// Detect the linked unwinder's GetCFA convention using a compiler-described
// native frame. This works with either libgcc or LLVM libunwind on either OS.
#include <stdint.h>
#include <unwind.h>
struct Probe { uintptr_t fp, sp, cfa; int recipe; };
static _Unwind_Reason_Code inspect(struct _Unwind_Context *context, void *data) {
    struct Probe *probe = data;
#if defined(__aarch64__)
    const int fp_register = 29;
#else
    const int fp_register = 6;
#endif
    if (_Unwind_GetGR(context, fp_register) != probe->fp) return _URC_NO_REASON;
    uintptr_t observed = _Unwind_GetCFA(context);
    if (observed == probe->sp && probe->sp != probe->cfa) probe->recipe = 1;
    else if (observed == probe->cfa && probe->sp != probe->cfa) probe->recipe = 2;
    return _URC_END_OF_STACK;
}
__attribute__((noinline)) int __rt_probe_unwinder_sp(void) {
    struct Probe probe = {0};
    // frame_address plus the compiler flag establishes an actual FP frame;
    // dwarf_cfa lets the compiler supply its true CFA even on AArch64 GCC,
    // whose frame record need not sit immediately below the entry SP.
    probe.fp = (uintptr_t)__builtin_frame_address(0);
    probe.cfa = (uintptr_t)__builtin_dwarf_cfa();
#if defined(__aarch64__)
    __asm__ volatile("mov %0, sp" : "=r"(probe.sp));
#else
    __asm__ volatile("mov %%rsp, %0" : "=r"(probe.sp));
#endif
    _Unwind_Backtrace(inspect, &probe);
    return probe.recipe;
}
