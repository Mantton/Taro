// macOS server counters, sampled outside the load generator. CPU times are
// Mach absolute ticks, not nanoseconds; convert with the host timebase.
#include <libproc.h>
#include <sys/resource.h>
#include <mach/mach_time.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

static uint64_t nanoseconds(uint64_t ticks) {
    mach_timebase_info_data_t base;
    mach_timebase_info(&base);
    return (uint64_t)((__uint128_t)ticks * base.numer / base.denom);
}
int main(int argc, char **argv) {
    if (argc != 2) return 2;
    if (strcmp(argv[1], "--self-test") == 0) {
        // Verify the platform units against an independent process CPU clock.
        // The volatile workload makes clock/counter sampling overhead negligible.
        volatile uint64_t value = 1;
        for (uint64_t i = 0; i < 50000000; ++i) value = value * 33 + i;
        struct rusage_info_v4 info = {0};
        if (proc_pid_rusage(getpid(), RUSAGE_INFO_V4, (rusage_info_t *)&info)) return 1;
        struct timespec cpu;
        clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &cpu);
        uint64_t expected = (uint64_t)cpu.tv_sec * 1000000000 + cpu.tv_nsec;
        uint64_t actual = nanoseconds(info.ri_user_time + info.ri_system_time);
        if (actual < expected * 0.95 || actual > expected * 1.05) return 1;
        puts("process CPU counter timebase verified");
        return 0;
    }
    struct rusage_info_v4 info = {0};
    if (proc_pid_rusage(atoi(argv[1]), RUSAGE_INFO_V4, (rusage_info_t *)&info)) return 1;
    printf("{\"user_ns\":%llu,\"system_ns\":%llu,\"instructions\":%llu,\"cycles\":%llu,\"rss\":%llu,\"footprint\":%llu,\"peak_footprint\":%llu}\n",
        (unsigned long long)nanoseconds(info.ri_user_time), (unsigned long long)nanoseconds(info.ri_system_time),
        (unsigned long long)info.ri_instructions, (unsigned long long)info.ri_cycles,
        (unsigned long long)info.ri_resident_size, (unsigned long long)info.ri_phys_footprint,
        (unsigned long long)info.ri_lifetime_max_phys_footprint);
    return 0;
}
