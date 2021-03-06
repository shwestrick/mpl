
#if (defined (MLTON_GC_INTERNAL_BASIS))

PRIVATE void Parallel_init (void);

PRIVATE void Parallel_lockInit (Pointer);
PRIVATE void Parallel_lockTake (Pointer);
PRIVATE void Parallel_lockRelease (Pointer);
PRIVATE bool Parallel_alreadyLockedByMe (Pointer);
PRIVATE void Parallel_dekkerTake (Bool, Pointer, Pointer, Pointer);
PRIVATE void Parallel_dekkerRelease (Bool, Pointer, Pointer, Pointer);

PRIVATE Word32 Parallel_processorNumber (void);
PRIVATE Word32 Parallel_numberOfProcessors (void);
PRIVATE Word64 Parallel_maxBytesLive (void);
PRIVATE void Parallel_resetBytesLive (void);
PRIVATE Word64 Parallel_getTimeInGC (void);

PRIVATE Int8 Parallel_fetchAndAdd8 (pointer p, Int8 v);
PRIVATE Int16 Parallel_fetchAndAdd16 (pointer p, Int16 v);
PRIVATE Int32 Parallel_fetchAndAdd32 (pointer p, Int32 v);
PRIVATE Int64 Parallel_fetchAndAdd64 (pointer p, Int64 v);

PRIVATE Int8 Parallel_arrayFetchAndAdd8 (pointer p, GC_sequenceLength i, Int8 v);
PRIVATE Int16 Parallel_arrayFetchAndAdd16 (pointer p, GC_sequenceLength i, Int16 v);
PRIVATE Int32 Parallel_arrayFetchAndAdd32 (pointer p, GC_sequenceLength i, Int32 v);
PRIVATE Int64 Parallel_arrayFetchAndAdd64 (pointer p, GC_sequenceLength i, Int64 v);

#endif /* (defined (MLTON_GC_INTERNAL_BASIS)) */
