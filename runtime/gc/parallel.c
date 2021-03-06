#include <pthread.h>
#include <time.h>
#include "platform.h"

void Parallel_init (void) {
  GC_state s = pthread_getspecific (gcstate_key);

  if (!Proc_isInitialized (s)) {
    /* Now wake them up! */
    Proc_signalInitialization (s);
  }
}

/* lock = int* >= 0 if held or -1 if no one */

void Parallel_lockInit (Pointer arg) {
  spinlock_t* lock = ((spinlock_t*)(arg));
  spinlock_init(lock);
}

void Parallel_lockTake (Pointer arg) {
  spinlock_t* lock = ((spinlock_t*)(arg));
  uint32_t lockValue = Proc_processorNumber(pthread_getspecific(gcstate_key));
  GC_state s = pthread_getspecific (gcstate_key);
  size_t cpoll = 0;

  LOG(LM_PARALLEL, LL_DEBUG,
      "trying to lock %p to %u",
      ((volatile void*)(lock)),
      lockValue);

  if (!spinlock_trylock(lock, lockValue)) {
      Trace1(EVENT_LOCK_TAKE_ENTER, (EventInt)lock);

      do {
          if (GC_CheckForTerminationRequestRarely(s, &cpoll)) {
              Trace1(EVENT_LOCK_TAKE_LEAVE, (EventInt)lock);
              GC_TerminateThread(s);
          }
      } while (!spinlock_trylock(lock, lockValue));
      Trace1(EVENT_LOCK_TAKE_LEAVE, (EventInt)lock);
  }

  LOG(LM_PARALLEL, LL_DEBUG,
      "locked");
}

void Parallel_lockRelease (Pointer arg) {
  spinlock_t* lock = ((spinlock_t*)(arg));

  LOG(LM_PARALLEL, LL_DEBUG,
      "releasing %p",
      ((volatile void*)(lock)));

  spinlock_unlock(lock);
}

bool Parallel_alreadyLockedByMe (Pointer arg) {
  spinlock_t* lock = ((spinlock_t*)(arg));
  uint32_t lockValue = Proc_processorNumber(pthread_getspecific(gcstate_key));

  return (lockValue == spinlock_value(lock));
}

void Parallel_dekkerTake (Bool amLeft, Pointer left, Pointer right, Pointer leftsTurn_)
{
  Bool *mine, *other, *leftsTurn;
  GC_state s = pthread_getspecific (gcstate_key);
  size_t cpoll = 0;

  if (amLeft) {
    mine = (Bool *)left;
    other = (Bool *)right;
  }
  else {
    mine = (Bool *)right;
    other = (Bool *)left;
  }
  leftsTurn = (Bool *)leftsTurn_;

  //__sync_synchronize ();
  //*mine = 1;
  ////__sync_synchronize ();
  //if (__sync_lock_test_and_set (mine, 1)) {
  if (!__sync_bool_compare_and_swap (mine, 0, 1)) {
    fprintf (stderr, "failed lock!\n");
  }
  while (*other) {
    GC_MayTerminateThreadRarely(s, &cpoll);

    //__sync_synchronize ();
    if (amLeft != *leftsTurn) {
      //__sync_synchronize ();
      //*mine = 0;
      ////__sync_synchronize ();
      //__sync_lock_release (mine);
      __sync_bool_compare_and_swap (mine, 1, 0);
      while (amLeft != *leftsTurn) {
        //__sync_synchronize ();
      }
      //*mine = 1;
      //if (__sync_lock_test_and_set (mine, 1)) {
      if (!__sync_bool_compare_and_swap (mine, 0, 1)) {
        fprintf (stderr, "failed lock!\n");
      }
    }
    //__sync_synchronize ();
  }
}

void Parallel_dekkerRelease (Bool amLeft, Pointer left, Pointer right, Pointer leftsTurn_)
{
  Bool *mine, *leftsTurn;
  if (amLeft) {
    mine = (Bool *)left;
  }
  else {
    mine = (Bool *)right;
  }
  leftsTurn = (Bool *)leftsTurn_;

  //__sync_synchronize ();
  *leftsTurn = amLeft ? 0 : 1;
  //__sync_synchronize ();
  //*mine = 0;
  ////__sync_synchronize ();
  //__sync_lock_release (mine);
  __sync_bool_compare_and_swap (mine, 1, 0);
}

Word32 Parallel_processorNumber (void) {
  GC_state s = pthread_getspecific (gcstate_key);
  return Proc_processorNumber (s);
}

Word32 Parallel_numberOfProcessors (void) {
  GC_state s = pthread_getspecific (gcstate_key);
  return s->numberOfProcs;
}


Word64 Parallel_maxBytesLive (void) {
  GC_state s = pthread_getspecific (gcstate_key);
  return (uint64_t)s->cumulativeStatistics->maxBytesLiveSinceReset;
}

void Parallel_resetBytesLive (void) {
  GC_state s = pthread_getspecific (gcstate_key);
  s->cumulativeStatistics->maxBytesLiveSinceReset = 0;
}

uint64_t Parallel_getTimeInGC (void) {
  GC_state s = pthread_getspecific (gcstate_key);
  uint64_t gcTime = rusageTime (&s->cumulativeStatistics->ru_gc);
  return gcTime;
}

// fetchAndAdd implementations

Int8 Parallel_fetchAndAdd8 (pointer p, Int8 v) {
  return __sync_fetch_and_add ((Int8 *)p, v);
}

Int16 Parallel_fetchAndAdd16 (pointer p, Int16 v) {
  return __sync_fetch_and_add ((Int16 *)p, v);
}

Int32 Parallel_fetchAndAdd32 (pointer p, Int32 v) {
  return __sync_fetch_and_add ((Int32 *)p, v);
}

Int64 Parallel_fetchAndAdd64 (pointer p, Int64 v) {
  return __sync_fetch_and_add ((Int64 *)p, v);
}

// arrayFetchAndAdd implementations

Int8 Parallel_arrayFetchAndAdd8 (Pointer p, GC_sequenceLength i, Int8 v) {
  return __sync_fetch_and_add (((Int8*)p)+i, v);
}

Int16 Parallel_arrayFetchAndAdd16 (Pointer p, GC_sequenceLength i, Int16 v) {
  return __sync_fetch_and_add (((Int16*)p)+i, v);
}

Int32 Parallel_arrayFetchAndAdd32 (Pointer p, GC_sequenceLength i, Int32 v) {
  return __sync_fetch_and_add (((Int32*)p)+i, v);
}

Int64 Parallel_arrayFetchAndAdd64 (Pointer p, GC_sequenceLength i, Int64 v) {
  return __sync_fetch_and_add (((Int64*)p)+i, v);
}
