/* Copyright (C) 2014,2020 Matthew Fluet.
 * Copyright (C) 1999-2006 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-2000 NEC Research Institute.
 *
 * MLton is released under a HPND-style license.
 * See the file MLton-LICENSE for details.
 */

#if (defined (MLTON_GC_INTERNAL_FUNCS))

static inline size_t sizeofInitialBytesLive (GC_state s);
static void initDynHeap (GC_state s, GC_thread thread);
static GC_thread initThreadAndHeap (GC_state s, uint32_t depth);
static void initWorld (GC_state s);
static void duplicateWorld (GC_state d, GC_state s);

#endif /* (defined (MLTON_GC_INTERNAL_FUNCS)) */
