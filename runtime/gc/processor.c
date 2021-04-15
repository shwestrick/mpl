#include "processor.h"

#include <pthread.h>

/***************************/
/* Static Global Variables */
/***************************/
/* variables used in processor initialization */
static volatile bool Proc_beginInit = FALSE;
static volatile uint32_t Proc_initializedCount = 0;

/************************/
/* Function definitions */
/************************/

int32_t Proc_processorNumber (GC_state s) {
  return s->procNumber;
}

void Proc_waitForInitialization (GC_state s) {
  SimResetHopCount();

  size_t pcounter = 0;
  while (!Proc_beginInit) {
    GC_MayTerminateThreadRarely(s, &pcounter);
  }

  __sync_add_and_fetch (&Proc_initializedCount, 1);

  while (!Proc_isInitialized (s)) {
    GC_MayTerminateThreadRarely(s, &pcounter);
  }

  SimRoiStart();
  s->cumulativeStatistics->tsc_start = rdtsc();
}

void Proc_signalInitialization (GC_state s) {
  SimResetHopCount();

  Proc_initializedCount = 1;
  Proc_beginInit = TRUE;

  while (!Proc_isInitialized (s)) { }

  SimRoiStart();
  s->cumulativeStatistics->tsc_start = rdtsc();
}

bool Proc_isInitialized (GC_state s) {
  return Proc_initializedCount == s->numberOfProcs;
}
