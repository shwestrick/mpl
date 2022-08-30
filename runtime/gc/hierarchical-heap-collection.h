/* Copyright (C) 2019-2020 Sam Westrick
 * Copyright (C) 2015 Ram Raghunathan.
 *
 * MLton is released under a HPND-style license.
 * See the file MLton-LICENSE for details.
 */

/**
 * @file hierarchical-heap-collection.h
 *
 * @author Ram Raghunathan
 *
 * @brief
 * Definition of the HierarchicalHeap collection interface
 */


#ifndef HIERARCHICAL_HEAP_COLLECTION_H_
#define HIERARCHICAL_HEAP_COLLECTION_H_

#include "chunk.h"

#if (defined (MLTON_GC_INTERNAL_TYPES))
struct ForwardHHObjptrArgs {
  struct HM_HierarchicalHeap* hh;
  uint32_t minDepth;
  uint32_t maxDepth;
  uint32_t toDepth; /* if == HM_HH_INVALID_DEPTH, preserve level of the forwarded object */

  /* arrays of HH objects, e.g. HM_HH_getDepth(toSpace[i]) == i */
  HM_HierarchicalHeap* fromSpace;
  HM_HierarchicalHeap* toSpace;
  /* an array of pinned chunklists */
  struct HM_chunkList *pinned;

  /* a hack to keep track of which object is currently being traced */
  objptr containingObject;

  size_t bytesCopied;
  uint64_t objectsCopied;
  uint64_t stacksCopied;

  /* large objects are "moved" (rather than copied). */
  size_t bytesMoved;
  uint64_t objectsMoved;
};

struct checkDEDepthsArgs {
  int32_t minDisentangledDepth;
  HM_HierarchicalHeap* fromSpace;
  HM_HierarchicalHeap* toSpace;
  uint32_t maxDepth;
};

#define MAX_NUM_HOLES 512

#endif /* MLTON_GC_INTERNAL_TYPES */

#if (defined (MLTON_GC_INTERNAL_BASIS))
#endif /* MLTON_GC_INTERNAL_BASIS */

#if (defined (MLTON_GC_INTERNAL_FUNCS))
/**
 * This function performs a local collection on the current hierarchical heap
 */
void HM_HHC_collectLocal(uint32_t desiredScope);

/**
 * Forwards the object pointed to by 'opp' into 'destinationLevelList' starting
 * in its last chunk.
 *
 * @param s The GC_state to use
 * @param opp The objptr to forward
 * @param args The struct ForwardHHObjptrArgs* for this call, cast as a void*
 */
void forwardHHObjptr(GC_state s, objptr* opp, objptr op, void* rawArgs);

/* check if `op` is in args->toSpace[depth(op)] */
bool isObjptrInToSpace(objptr op, struct ForwardHHObjptrArgs *args);

objptr relocateObject(GC_state s, objptr obj, HM_HierarchicalHeap tgtHeap, struct ForwardHHObjptrArgs *args);


/**
 * Compute the size of the object, how much of it has to be copied, as well as
 * how much metadata it has.
 *
 * @param s GC state
 * @param p The pointer to copy
 * @param objectSize Where to store the size of the object (in bytes)
 * @param copySize Where to store the number of bytes to copy
 * @param metaDataSize Where to store the metadata size (in bytes)
 *
 * @return the tag of the object
 */
GC_objectTypeTag computeObjectCopyParameters(
  GC_state s,
  pointer p,
  size_t *objectSize,
  size_t *copySize,
  size_t *metaDataSize);

// NOTE: p should point to front of object metadata. copySize is how much
// data should be copied, including metadata. objectSize is the total size
// of the object, including metadata. Usually, copySize == objectSize. But
// it's possible copySize < objectSize, for stack objects.
pointer copyObject(
  pointer p,
  size_t objectSize,
  size_t copySize,
  HM_HierarchicalHeap tgtHeap);

#endif /* MLTON_GC_INTERNAL_FUNCS */

#endif /* HIERARCHICAL_HEAP_H_ */
