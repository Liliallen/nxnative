// Probes DM_PROBE (taken from d2r-mobile dm/host/diag.c, keeping only the probe itself): when the debugger needs a system authorization prompt on the Mac, use this to print registers and a backtrace at a guest address.
#include "dm.h"
#include <TargetConditionals.h>
#include <signal.h>
#include <dlfcn.h>
#include <sys/ucontext.h>
#include <sys/mman.h>
#include <libkern/OSCacheControl.h>
#include <mach/mach.h>
#include <string.h>
#include <stdatomic.h>
#include <stdlib.h>
#include <stdio.h>
void crash_set_trap_hook(int (*fn)(ucontext_t *uc));
#if !TARGET_OS_IPHONE
// Syntax module:offset[@x0 offset]. Put a brk at the guest address; on hit print x0..x3 (and the readable strings they point to) and a backtrace, then execute the original instruction from a trampoline slot and jump back.
// The trampoline borrows x16: place probes only at function entries or at points where x16 is dead; the original instruction must not be PC-relative (adr/adrp/b/bl/ldr literal/cbz...).
#define MAX_PROBE 16
typedef void (*probe_fn)(ucontext_t *uc);
static struct { uint64_t at; uint32_t *slot; unsigned hits; char name[40]; long dump; probe_fn fn; int freg; long foff; uint64_t fval; int hreg; } g_probe[MAX_PROBE];

// !xN: treat xN as a sead::ExpHeap and print its free and used blocks (SMBW layout: free list +0xb0, node offset +0xc4; used list +0xc8, node offset +0xdc; block size at block +0x18)
static int rd64(uint64_t a, uint64_t *v) { vm_size_t g = 0; return !vm_read_overwrite(mach_task_self(), a, 8, (vm_address_t)v, &g) && g == 8; }
static void probe_heapwalk(uint64_t h) {
    uint64_t start = 0, size = 0; rd64(h + 0x28, &start); rd64(h + 0x30, &size);
    fprintf(stderr, "[dm]   ExpHeap %#llx 起 %#llx 大小 %#llx\n", (unsigned long long)h, (unsigned long long)start, (unsigned long long)size);
    static const struct { int list, off; const char *nm; } L[2] = { { 0xb0, 0xc4, "空闲/free" }, { 0xc8, 0xdc, "已用/used" } };
    for (int k = 0; k < 2; k++) {
        uint64_t offw = 0, node = 0, sum = 0; int n = 0; rd64(h + L[k].off, &offw); int32_t off = (int32_t)offw;
        rd64(h + L[k].list + 8, &node);
        fprintf(stderr, "[dm]   %s:", L[k].nm);
        while (node && node != h + L[k].list && n < 2000) {
            uint64_t blk = node - off, bsz = 0, w2 = 0; rd64(blk + 0x18, &bsz); rd64(blk + 0x10, &w2);
            fprintf(stderr, "%s%llx+%llx", n % 8 ? " " : "\n[dm]     ", (unsigned long long)(blk - start), (unsigned long long)bsz);
            sum += bsz; n++;
            if (!rd64(node + 8, &node)) break;
        }
        fprintf(stderr, "\n[dm]   %s 共 %d 块 %#llx 字节\n", L[k].nm, n, (unsigned long long)sum);
    }
}   // dump: on hit print 16 bytes at [x0+dump] (-1 = do not print); fn: dedicated handler (replaces the default print)
static int g_nprobe;
static void probe_str(uint64_t p) {
    char buf[80]; vm_size_t got = 0;
    if (p < 0x1000 || vm_read_overwrite(mach_task_self(), p, sizeof buf - 1, (vm_address_t)buf, &got) || !got) return;
    buf[got] = 0; int n = 0; while (buf[n] >= 0x20 && buf[n] < 0x7f) n++;
    if (n >= 3 && (buf[n] == 0 || n == (int)got)) { fprintf(stderr, " \"%.*s\"", n, buf); return; }
    // Game string object {char* pointer, u64 length, u64 capacity|top bit} (the path argument of 0xdf67f0 FJSONUtils has exactly this layout)
    if (got >= 24) {
        uint64_t ptr, len; memcpy(&ptr, buf, 8); memcpy(&len, buf + 8, 8);
        char t[96]; got = 0;
        if (len >= 3 && len < sizeof t && !vm_read_overwrite(mach_task_self(), ptr, len, (vm_address_t)t, &got) && got == len) {
            int k = 0; while (k < (int)len && t[k] >= 0x20 && t[k] < 0x7f) k++;
            if (k == (int)len) fprintf(stderr, " S\"%.*s\"", (int)len, t);
        }
    }
}
// DM_PROBE_DUMP=module:offset:length[:file]: on the first hit of any probe, write that range of guest memory to a file (default run/platform/probe_dump.bin)
static void probe_dump_once(void) {
    static int done; const char *e = getenv("DM_PROBE_DUMP"); if (done || !e) return; done = 1;
    char spec[512]; strlcpy(spec, e, sizeof spec);
    char *mod = strtok(spec, ":"), *o = strtok(NULL, ":"), *n = strtok(NULL, ":"), *f = strtok(NULL, ":");
    module_t *m = NULL; for (int i = 0; i < g_nmod; i++) if (mod && !strcmp(g_mod[i].name, mod)) m = &g_mod[i];
    if (!m || !o || !n) { LOG("DM_PROBE_DUMP 格式：模块:偏移:长度[:文件]"); return; }
    char def[512]; snprintf(def, sizeof def, "%s%s/run/platform/probe_dump.bin", getenv("DM_ROOT") ?: getenv("HOME"), getenv("DM_ROOT") ? "" : "/dm-work");
    FILE *fp = fopen(f ? f : def, "wb"); if (!fp) return;
    fwrite(m->base + strtoull(o, 0, 16), 1, strtoull(n, 0, 16), fp); fclose(fp);
    LOG("探针转储 %s+%s 长 %s → %s", mod, o, n, f ? f : def);
}
static int wp_hit(ucontext_t *uc);
static int probe_hit(ucontext_t *uc) {   // Registered by probe_install with the SIGTRAP branch of crash.c
    uint64_t pc = uc->uc_mcontext->__ss.__pc;
    if (wp_hit(uc)) return 1;
    for (int i = 0; i < g_nprobe; i++) if (g_probe[i].at == pc) {
        probe_dump_once();
        if (g_probe[i].fn) { g_probe[i].hits++; g_probe[i].fn(uc); uc->uc_mcontext->__ss.__pc = (uint64_t)g_probe[i].slot; return 1; }
        if (g_probe[i].freg >= 0) {   // ?xN=value / ?[xN+offset]=value: pass through silently when it does not match
            uint64_t v = uc->uc_mcontext->__ss.__x[g_probe[i].freg]; vm_size_t g = 0;
            if (g_probe[i].foff >= 0 && vm_read_overwrite(mach_task_self(), v + g_probe[i].foff, 8, (vm_address_t)&v, &g)) v = ~g_probe[i].fval;
            if (v != g_probe[i].fval) { uc->uc_mcontext->__ss.__pc = (uint64_t)g_probe[i].slot; return 1; }
        }
        { extern uint64_t g_t0_ns; uint64_t now_ns(void); uint32_t thr_cur_handle(void); fprintf(stderr, "[dm] PROBE %s #%u [%.4fs] T=%x", g_probe[i].name, ++g_probe[i].hits, (now_ns() - g_t0_ns) / 1e9, thr_cur_handle()); }
        for (int r = 0; r < 8; r++) { uint64_t v = uc->uc_mcontext->__ss.__x[r]; fprintf(stderr, " x%d=%#llx", r, v); probe_str(v); }
        for (int r = 19; r < 24; r++) fprintf(stderr, " x%d=%#llx", r, uc->uc_mcontext->__ss.__x[r]);
        if (getenv("DM_PROBE_ALL")) for (int r = 9; r < 19; r++) fprintf(stderr, " x%d=%#llx", r, uc->uc_mcontext->__ss.__x[r]);   // also print x9–x18
        fprintf(stderr, " lr=%#llx", uc->uc_mcontext->__ss.__lr);
        { uint64_t x8 = uc->uc_mcontext->__ss.__x[8]; Dl_info di; fprintf(stderr, " x8=%#llx", x8);   // x8: indirect call targets are often here (probe placed before blr x8)
          if (dladdr((void *)x8, &di) && di.dli_sname) fprintf(stderr, "（%s+%#lx）", di.dli_sname, (unsigned long)(x8 - (uint64_t)di.dli_saddr)); }
        if (g_probe[i].dump >= 0) {
            uint8_t b[16]; vm_size_t got = 0;
            int dr = (g_probe[i].dump >> 25) & 31;                                    // @xN+offset: based on xN
            uint64_t at = uc->uc_mcontext->__ss.__x[dr] + (g_probe[i].dump & 0xffffff);
            if (g_probe[i].dump & 0x1000000) { uint64_t p = 0; vm_size_t g = 0; if (!vm_read_overwrite(mach_task_self(), at, 8, (vm_address_t)&p, &g)) at = p; else at = 0; }   // @*offset: dereference first, then dump
            if (at && !vm_read_overwrite(mach_task_self(), at, 16, (vm_address_t)b, &got) && got == 16) {
                fprintf(stderr, " [%sx%d+%#lx]=", (g_probe[i].dump & 0x1000000) ? "*" : "", dr, g_probe[i].dump & 0xffffff); for (int k = 0; k < 16; k++) fprintf(stderr, "%02x", b[k]); }
        }
        fputc('\n', stderr);
        { static long xd = -2; if (xd == -2) { const char *e = getenv("DM_PROBE_X2"); xd = e ? strtol(e, 0, 16) : -1; }   // DM_PROBE_X2=bytes: also print the memory x2 points to (to read object fields)
          if (xd > 0) { uint64_t at = uc->uc_mcontext->__ss.__x[2]; uint8_t b[512]; vm_size_t got = 0; long n = xd > 512 ? 512 : xd;
            if (!vm_read_overwrite(mach_task_self(), at, n, (vm_address_t)b, &got)) { fprintf(stderr, "[dm]   [x2]:"); for (long k = 0; k < (long)got; k += 8) { uint64_t v; memcpy(&v, b + k, 8); fprintf(stderr, "%s%llx", k % 32 ? " " : "\n[dm]   ", (unsigned long long)v); } fputc('\n', stderr); } } }
        if (g_probe[i].hreg >= 0) probe_heapwalk(uc->uc_mcontext->__ss.__x[g_probe[i].hreg]);
        dm_backtrace(uc->uc_mcontext->__ss.__fp);
        uc->uc_mcontext->__ss.__pc = (uint64_t)g_probe[i].slot;
        return 1;
    }
    return 0;
}
static uint32_t *g_slots; static int g_slots_sealed;
static void probe_add(module_t *m, uint64_t off, long dump, probe_fn fn) {
    if (g_nprobe >= MAX_PROBE) die("探针过多");
    if (!g_slots) g_slots = mmap(NULL, 0x4000, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANON, -1, 0);
    uint64_t at = (uint64_t)m->base + off;
    uint32_t *w = (uint32_t *)at, *sl = g_slots + g_nprobe * 8;
    sl[0] = *w;                                  // Original instruction
    sl[1] = 0x58000050;                          // ldr x16, #8
    sl[2] = 0xD61F0200;                          // br x16
    *(uint64_t *)(sl + 3) = at + 4;
    uint64_t pg = at & ~0x3FFFull;
    if (mprotect((void *)pg, 0x4000, PROT_READ | PROT_WRITE)) die("probe mprotect");
    *w = 0xD43E0000;                             // brk #0xf000
    mprotect((void *)pg, 0x4000, PROT_READ | PROT_EXEC);
    sys_icache_invalidate(w, 4);
    g_probe[g_nprobe].at = at; g_probe[g_nprobe].slot = sl; g_probe[g_nprobe].dump = dump; g_probe[g_nprobe].fn = fn; g_probe[g_nprobe].freg = -1; g_probe[g_nprobe].hreg = -1;
    snprintf(g_probe[g_nprobe].name, sizeof g_probe[0].name, "%s+%#llx", m->name, off);
    LOG("探针 %s（原指令 %08x）", g_probe[g_nprobe].name, sl[0]);
    g_nprobe++;
}

// DM_PROBE_UBLIST=1 (Breath of the Wild 1.6.0 only, main 8e9978d5…): checks the uniform block list the crashing walk at main+0x14ef440 follows, at every call. A shader
// variation struct (x9 = [x0+0x30] + 0xa0 * [x1+0x20], or the first one) with bit 1 of +0x98 has a list at +0x88 (count +0x80) of 0x18-byte entries {block*, mask, ...};
// otherwise x0+0x10 (count +0x1c) holds descriptors whose +0x20 is the block. A live block's first word is its vtable in main. Each object's last good list is kept, so
// on the first bad one the dump says whether the owner, its list pointer or the list contents changed since
static uint64_t ub_main_lo, ub_main_hi;
static int ub_vt_ok(uint64_t o) { uint64_t v = 0; return o && rd64(o, &v) && v >= ub_main_lo && v < ub_main_hi; }
static void ub_dump(const char *nm, uint64_t a, int words) {
    fprintf(stderr, "[dm]   %s %#llx:", nm, (unsigned long long)a);
    for (int k = 0; k < words; k++) { uint64_t v = 0; rd64(a + 8 * k, &v);
        if (v >= ub_main_lo && v < ub_main_hi) fprintf(stderr, "%smain+%llx", k % 6 ? " " : "\n[dm]     ", (unsigned long long)(v - ub_main_lo));
        else fprintf(stderr, "%s%llx", k % 6 ? " " : "\n[dm]     ", (unsigned long long)v); }
    fputc('\n', stderr);
}
// Hardware write watchpoints on this task's threads (Mac diagnostics): ARM_DEBUG_STATE64 per thread, a watchpoint hit arrives as SIGTRAP before the store executes
enum { WP_N = 4 };
static uint64_t g_wp[WP_N]; static int g_wp_live[WP_N];
static void wp_apply(void) {
    thread_act_array_t th; mach_msg_type_number_t n = 0;
    if (task_threads(mach_task_self(), &th, &n)) return;
    for (mach_msg_type_number_t i = 0; i < n; i++) {
        arm_debug_state64_t ds; mach_msg_type_number_t c = ARM_DEBUG_STATE64_COUNT;
        if (thread_get_state(th[i], ARM_DEBUG_STATE64, (thread_state_t)&ds, &c)) memset(&ds, 0, sizeof ds);
        for (int k = 0; k < WP_N; k++) { ds.__wvr[k] = g_wp[k] & ~7ull; ds.__wcr[k] = g_wp_live[k] ? (1u | 2u << 1 | 2u << 3 | 0xFFu << 5) : 0; }
        thread_set_state(th[i], ARM_DEBUG_STATE64, (thread_state_t)&ds, ARM_DEBUG_STATE64_COUNT);
        mach_port_deallocate(mach_task_self(), th[i]);
    }
    vm_deallocate(mach_task_self(), (vm_address_t)th, n * sizeof *th);
}
static int wp_arm(uint64_t a) { for (int k = 0; k < WP_N; k++) if (!g_wp_live[k] && !g_wp[k]) { g_wp[k] = a; g_wp_live[k] = 1; wp_apply(); return 1; } return 0; }
static int wp_hit(ucontext_t *uc) {
    uint64_t far = uc->uc_mcontext->__es.__far; uint32_t ec = uc->uc_mcontext->__es.__esr >> 26;
    for (int k = 0; k < WP_N; k++) if (g_wp_live[k] && (far & ~7ull) == g_wp[k]) {
        uint64_t pc = uc->uc_mcontext->__ss.__pc; module_t *m = module_of((void *)pc); uint32_t thr_cur_handle(void); uint64_t old = 0; rd64(g_wp[k], &old);
        fprintf(stderr, "[dm] WATCH 写 | write %#llx（槽 %d，EC %#x）帧 %llu T=%x pc=%s+%#llx 旧值 %#llx x0=%#llx x1=%#llx x2=%#llx x8=%#llx x19=%#llx x20=%#llx\n", (unsigned long long)far, k, ec,
                (unsigned long long)dm_nvn_frame_count(), thr_cur_handle(), m ? m->name : "?", (unsigned long long)(m ? pc - (uint64_t)m->base : pc), (unsigned long long)old,
                uc->uc_mcontext->__ss.__x[0], uc->uc_mcontext->__ss.__x[1], uc->uc_mcontext->__ss.__x[2], uc->uc_mcontext->__ss.__x[8], uc->uc_mcontext->__ss.__x[19], uc->uc_mcontext->__ss.__x[20]);
        dm_backtrace(uc->uc_mcontext->__ss.__fp);
        g_wp_live[k] = 0; wp_apply();   // one shot: the store runs when the handler returns
        return 1;
    }
    return 0;
}
// Event ring (lock-free): rebuilds (W, the writer after it published the new list) and reads (R, the walk) per variation, dumped for the variation of the first bad read
typedef struct { uint64_t ns, var, arr; uint32_t thr, frame, cnt; char kind; } ub_ev;
enum { UB_RING = 1 << 18 };
static ub_ev g_ring[UB_RING]; static _Atomic uint64_t g_ring_n;
static void ub_note(char kind, uint64_t var, uint64_t arr, uint32_t cnt) {
    uint64_t now_ns(void); uint32_t thr_cur_handle(void);
    uint64_t i = atomic_fetch_add(&g_ring_n, 1) & (UB_RING - 1);
    g_ring[i] = (ub_ev){now_ns(), var, arr, thr_cur_handle(), (uint32_t)dm_nvn_frame_count(), cnt, kind};
}
static void ub_history(uint64_t var) {
    extern uint64_t g_t0_ns; uint64_t n = atomic_load(&g_ring_n), lo = n > UB_RING ? n - UB_RING : 0; int shown = 0;
    for (uint64_t i = n; i-- > lo && shown < 40;) { ub_ev *e = &g_ring[i & (UB_RING - 1)]; if (e->var != var) continue; shown++;
        fprintf(stderr, "[dm]   %c %.6fs T=%x 帧 %u arr=%#llx n=%u\n", e->kind, (e->ns - g_t0_ns) / 1e9, e->thr, e->frame, (unsigned long long)e->arr, e->cnt); }
}
static void ubf_probe(ucontext_t *uc) {   // job body F(x0 self, w1 phase, w2 partition, w3 start, w4 end) at main+0x139e530: var = self, arr = phase << 32 | partition, cnt = start << 16 | end
    uint64_t *x = uc->uc_mcontext->__ss.__x; ub_note('F', x[0], (uint64_t)(uint32_t)x[1] << 32 | (uint32_t)x[2], (uint32_t)(x[3] << 16 | (x[4] & 0xffff)));
}
static void ub_jobs(void) {
    extern uint64_t g_t0_ns; uint64_t n = atomic_load(&g_ring_n), lo = n > UB_RING ? n - UB_RING : 0; int shown = 0;
    for (uint64_t i = n; i-- > lo && shown < 60;) { ub_ev *e = &g_ring[i & (UB_RING - 1)]; if (e->kind != 'H' && e->kind != 'W') continue; shown++;
        if (e->kind == 'H') fprintf(stderr, "[dm]   H %.6fs T=%x 帧 %u head=%#llx unit=%#llx idx=%u\n", (e->ns - g_t0_ns) / 1e9, e->thr, e->frame, (unsigned long long)e->var, (unsigned long long)e->arr, e->cnt);
        else if (e->kind == 'F') fprintf(stderr, "[dm]   F %.6fs T=%x 帧 %u self=%#llx phase=%d part=%d range=%u..%u\n", (e->ns - g_t0_ns) / 1e9, e->thr, e->frame, (unsigned long long)e->var, (int)(e->arr >> 32), (int)(int32_t)e->arr, e->cnt >> 16, e->cnt & 0xffff);
        else fprintf(stderr, "[dm]   W %.6fs T=%x 帧 %u var=%#llx arr=%#llx\n", (e->ns - g_t0_ns) / 1e9, e->thr, e->frame, (unsigned long long)e->var, (unsigned long long)e->arr); }
}
static void ubh_probe(ucontext_t *uc) {   // phase 1 per head at main+0x139e834: var = head x27, arr = [head] (the unit passed on)
    uint64_t *x = uc->uc_mcontext->__ss.__x, u = 0; rd64(x[27], &u); ub_note('H', x[27], u, (uint32_t)x[26]);
}
static void uba_probe(ucontext_t *uc) {   // phase 0 add at main+0x139e67c: var = head x11, arr = outer item x22, cnt = list index
    uint64_t *x = uc->uc_mcontext->__ss.__x; ub_note('A', x[11], x[22], (uint32_t)(x[10] >> 3));
}
static void ub_adds(uint64_t head) {
    extern uint64_t g_t0_ns; uint64_t n = atomic_load(&g_ring_n), lo = n > UB_RING ? n - UB_RING : 0; int k = 0;
    for (uint64_t i = n; i-- > lo && k < 6;) { ub_ev *e = &g_ring[i & (UB_RING - 1)]; if (e->kind != 'A' || e->var != head) continue; k++;
        fprintf(stderr, "[dm]     A %.6fs T=%x 帧 %u head=%#llx outer=%#llx idx=%u\n", (e->ns - g_t0_ns) / 1e9, e->thr, e->frame, (unsigned long long)e->var, (unsigned long long)e->arr, e->cnt); }
}
static void ub_heads(uint64_t var) {   // for each rebuild of var in the ring: the heads the same thread took just before it
    extern uint64_t g_t0_ns; uint64_t n = atomic_load(&g_ring_n), lo = n > UB_RING ? n - UB_RING : 0; int ws = 0;
    for (uint64_t i = n; i-- > lo && ws < 3;) { ub_ev *w = &g_ring[i & (UB_RING - 1)]; if (w->kind != 'W' || w->var != var) continue; ws++;
        fprintf(stderr, "[dm]   W %.6fs T=%x 帧 %u 之前该线程的头 | heads before:\n", (w->ns - g_t0_ns) / 1e9, w->thr, w->frame); int hs = 0;
        for (uint64_t j = i; j-- > lo && hs < 3;) { ub_ev *e = &g_ring[j & (UB_RING - 1)]; if (e->thr != w->thr || e->kind != 'H') continue; hs++;
            fprintf(stderr, "[dm]     H %.6fs head=%#llx unit=%#llx idx=%u\n", (e->ns - g_t0_ns) / 1e9, (unsigned long long)e->var, (unsigned long long)e->arr, e->cnt);
            if (hs == 1) ub_adds(e->var); } }
}
static void ubw_probe(ucontext_t *uc) { ub_note('W', uc->uc_mcontext->__ss.__x[23], uc->uc_mcontext->__ss.__x[8], 0); }
enum { UB_H = 1 << 16 };
static struct { uint64_t obj, var, arr, first, frame; } g_ub[UB_H];
static void ub_probe(ucontext_t *uc) {
    uint64_t x0 = uc->uc_mcontext->__ss.__x[0], x1 = uc->uc_mcontext->__ss.__x[1], arr = 0, base = 0, n = 0, cnt = 0, var = 0;
    uint8_t idx = 0; uint32_t nv = 0; uint64_t t = 0;
    if (!rd64(x1 + 0x20, &t)) return; idx = (uint8_t)t;
    if (!rd64(x0 + 0x30, &base) || !rd64(x0 + 0x28, &t)) return; nv = (uint32_t)t;
    var = nv > idx ? base + 0xa0ull * idx : base;
    if (!rd64(var + 0x98, &t)) return;
    int listed = (t & 0xff) >> 1 & 1;
    if (listed) { rd64(var + 0x80, &cnt); cnt = (uint32_t)cnt; rd64(var + 0x88, &arr); }
    else { rd64(x0 + 0x18, &cnt); cnt >>= 32; rd64(x0 + 0x10, &arr); }
    int bad = -1; uint64_t blk = 0;
    for (n = 0; n < cnt && n < 64; n++) {
        if (listed) rd64(arr + 0x18 * n, &blk); else { uint64_t d = 0; rd64(arr + 8 * n, &d); rd64(d + 0x20, &blk); }
        if (!ub_vt_ok(blk)) { bad = (int)n; break; }
    }
    ub_note(bad < 0 ? 'R' : 'X', var, arr, (uint32_t)cnt);
    unsigned h = (unsigned)((x0 >> 4) * 0x9E3779B97F4A7C15ull >> 48);
    if (g_ub[h].obj == x0 && g_ub[h].var == var && g_ub[h].arr != arr) {   // the list was rebuilt
        static _Atomic int nch; if (atomic_fetch_add(&nch, 1) < 200) { uint64_t w0 = 0, wm = 0; rd64(arr, &w0); rd64(arr - 8, &wm);
            fprintf(stderr, "[dm] UBLIST 换表 | rebuilt 帧 %llu obj=%#llx var=%#llx %#llx→%#llx n=%llu %s [arr]=%#llx [arr-8]=%#llx\n", (unsigned long long)dm_nvn_frame_count(), (unsigned long long)x0,
                    (unsigned long long)var, (unsigned long long)g_ub[h].arr, (unsigned long long)arr, (unsigned long long)cnt, bad < 0 ? "好" : "坏", (unsigned long long)w0, (unsigned long long)wm); } }
    if (bad < 0 && cnt && dm_nvn_frame_count() > 600 && getenv("DM_PROBE_UBWATCH")) {
        static _Atomic int armed; if (atomic_load(&armed) < WP_N && g_ub[h].obj != x0 && wp_arm(var + 0x88)) {
            atomic_fetch_add(&armed, 1); fprintf(stderr, "[dm] WATCH 布防 | armed var+0x88=%#llx obj=%#llx arr=%#llx n=%llu 帧 %llu\n", (unsigned long long)(var + 0x88), (unsigned long long)x0, (unsigned long long)arr, (unsigned long long)cnt, (unsigned long long)dm_nvn_frame_count()); } }
    if (bad < 0) { uint64_t f = 0; if (cnt) { if (listed) rd64(arr, &f); else rd64(arr, &f); }
        g_ub[h].obj = x0; g_ub[h].var = var; g_ub[h].arr = arr; g_ub[h].first = f; g_ub[h].frame = dm_nvn_frame_count(); return; }
    static _Atomic int shown; if (atomic_fetch_add(&shown, 1) >= 3) return;
    fprintf(stderr, "[dm] UBLIST 坏条目 | bad entry %d/%llu 帧 %llu obj=%#llx ctx=%#llx var=%#llx（第 %u 个，共 %u）%s arr=%#llx blk=%#llx\n", bad, (unsigned long long)cnt,
            (unsigned long long)dm_nvn_frame_count(), (unsigned long long)x0, (unsigned long long)x1, (unsigned long long)var, idx, nv, listed ? "列表" : "描述符", (unsigned long long)arr, (unsigned long long)blk);
    if (g_ub[h].obj == x0) fprintf(stderr, "[dm]   上次正常 | last good: 帧 %llu var=%#llx arr=%#llx first=%#llx\n", (unsigned long long)g_ub[h].frame, (unsigned long long)g_ub[h].var, (unsigned long long)g_ub[h].arr, (unsigned long long)g_ub[h].first);
    else fprintf(stderr, "[dm]   此前未见过正常的该对象 | never seen good\n");
    ub_dump("obj", x0, 24); ub_dump("var", var, 20); ub_dump("arr-0x30", arr - 0x30, 30); ub_dump("ctx", x1, 12);
    if (g_ub[h].obj == x0) ub_dump("old arr", g_ub[h].arr, 12);
    fprintf(stderr, "[dm]   该 var 的事件（新→旧）| history:\n"); ub_history(var);
    ub_heads(var);
    dm_backtrace(uc->uc_mcontext->__ss.__fp);
}
// DM_PROBE_CORE=1 (BotW 1.6.0): which thread takes which bump-arena index at main+0x139e794 (TLS worker index - 1, or the current core number when the thread has none)
static void core_probe(ucontext_t *uc) {
    static _Atomic uint64_t seen[64]; uint32_t thr_cur_handle(void); void thr_cur_info(int *, int *, uint64_t *);
    uint32_t h = thr_cur_handle(); int idx = (int)uc->uc_mcontext->__ss.__x[0], core, prio; uint64_t mask; thr_cur_info(&core, &prio, &mask);
    uint64_t key = (uint64_t)h << 8 | (uint8_t)idx;
    for (int i = 0; i < 64; i++) { uint64_t e = 0; if (atomic_compare_exchange_strong(&seen[i], &e, key)) { fprintf(stderr, "[dm] CORE 索引 | index %d T=%x core=%d mask=%#llx prio=%d 帧 %llu\n", idx, h, core, (unsigned long long)mask, prio, (unsigned long long)dm_nvn_frame_count()); return; } if (e == key) return; }
}
static void ub_install(void) {
    if (!getenv("DM_PROBE_UBLIST") && !getenv("DM_PROBE_CORE")) return;
    for (int i = 0; i < g_nmod; i++) if (!strcmp(g_mod[i].name, "main")) {
        if (strcmp(g_mod[i].build_id, "8e9978d50bdd20b4c8395a106c27ffde")) { LOG("DM_PROBE_UBLIST：只认 BotW 1.6.0 main"); return; }
        ub_main_lo = (uint64_t)g_mod[i].base; ub_main_hi = ub_main_lo + g_mod[i].size;
        if (getenv("DM_PROBE_UBLIST")) { probe_add(&g_mod[i], 0x14ef440, -1, ub_probe); probe_add(&g_mod[i], 0x14e88a8, -1, ubw_probe); probe_add(&g_mod[i], 0x139e834, -1, ubh_probe); probe_add(&g_mod[i], 0x139e67c, -1, uba_probe); }
        if (getenv("DM_PROBE_CORE")) probe_add(&g_mod[i], 0x139e794, -1, core_probe);
    }
}

#endif

void probe_install(void) {
#if !TARGET_OS_IPHONE
    crash_set_trap_hook(probe_hit);
    ub_install();
    const char *e = getenv("DM_PROBE");
    if (e) {
        char spec[512]; strlcpy(spec, e, sizeof spec);
        for (char *t = strtok(spec, ","); t; t = strtok(NULL, ",")) {
            char *c = strchr(t, ':'); if (!c) die("DM_PROBE 格式：模块:偏移");
            *c = 0; module_t *m = NULL;
            for (int i = 0; i < g_nmod; i++) if (!strcmp(g_mod[i].name, t)) m = &g_mod[i];
            if (!m) die("DM_PROBE 无此模块 %s", t);
            char *at_ = strchr(c + 1, '@');
            long dump = -1;
            if (at_) {   // @offset / @*offset / @xN+offset / @*xN+offset
                const char *q = at_ + 1; long deref = 0, reg = 0;
                if (*q == '*') { deref = 0x1000000; q++; }
                if (*q == 'x') { char *e2; reg = strtol(q + 1, &e2, 10) & 31; q = *e2 == '+' ? e2 + 1 : e2; }
                dump = deref | (reg << 25) | (strtol(q, 0, 16) & 0xffffff);
            }
            char *qm = strchr(c + 1, '?'), *bang = strchr(c + 1, '!');
            probe_add(m, strtoull(c + 1, 0, 16), dump, NULL);
            if (bang && bang[1] == 'x') g_probe[g_nprobe - 1].hreg = (int)strtol(bang + 2, 0, 10) & 31;
            if (qm) {   // Filter: ?x0=706c400000 or ?[x0+38]=781548 (hex)
                const char *q = qm + 1; int br = *q == '[';
                if (br) q++;
                if (*q != 'x') die("DM_PROBE 过滤格式：?xN=值 或 ?[xN+偏移]=值");
                char *e2; g_probe[g_nprobe - 1].freg = (int)strtol(q + 1, &e2, 10) & 31; g_probe[g_nprobe - 1].foff = -1;
                if (br) { g_probe[g_nprobe - 1].foff = *e2 == '+' ? strtol(e2 + 1, &e2, 16) : 0; if (*e2 == ']') e2++; }
                if (*e2 != '=') die("DM_PROBE 过滤缺 =");
                g_probe[g_nprobe - 1].fval = strtoull(e2 + 1, 0, 16);
            }
        }
    }
    if (g_slots && !g_slots_sealed) { mprotect(g_slots, 0x4000, PROT_READ | PROT_EXEC); sys_icache_invalidate(g_slots, 0x4000); g_slots_sealed = 1; }
#endif
}
