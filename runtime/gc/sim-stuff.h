
#ifndef SIM_STUFF_H_
#define SIM_STUFF_H_

unsigned long long rdtsc(void);

#define L1_LINE_SZ_PATH "/sys/devices/system/cpu/cpu0/cache/index0/coherency_line_size"

size_t get_l1_line_sz(void);

#endif
