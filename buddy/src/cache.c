/*========================================================================
               Copyright (C) 1996-2002 by Jorn Lind-Nielsen
                            All rights reserved

    Permission is hereby granted, without written agreement and without
    license or royalty fees, to use, reproduce, prepare derivative
    works, distribute, and display this software and its documentation
    for any purpose, provided that (1) the above copyright notice and
    the following two paragraphs appear in all copies of the source code
    and (2) redistributions, including without limitation binaries,
    reproduce these notices in the supporting documentation. Substantial
    modifications to this software may be copyrighted by their authors
    and need not follow the licensing terms described here, provided
    that the new terms are clearly indicated in all files where they apply.

    IN NO EVENT SHALL JORN LIND-NIELSEN, OR DISTRIBUTORS OF THIS
    SOFTWARE BE LIABLE TO ANY PARTY FOR DIRECT, INDIRECT, SPECIAL,
    INCIDENTAL, OR CONSEQUENTIAL DAMAGES ARISING OUT OF THE USE OF THIS
    SOFTWARE AND ITS DOCUMENTATION, EVEN IF THE AUTHORS OR ANY OF THE
    ABOVE PARTIES HAVE BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

    JORN LIND-NIELSEN SPECIFICALLY DISCLAIM ANY WARRANTIES, INCLUDING,
    BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND
    FITNESS FOR A PARTICULAR PURPOSE. THE SOFTWARE PROVIDED HEREUNDER IS
    ON AN "AS IS" BASIS, AND THE AUTHORS AND DISTRIBUTORS HAVE NO
    OBLIGATION TO PROVIDE MAINTENANCE, SUPPORT, UPDATES, ENHANCEMENTS, OR
    MODIFICATIONS.
========================================================================*/

/*************************************************************************
  $Header: /Volumes/CVS/repository/spot/spot/buddy/src/cache.c,v 1.2 2003/05/05 13:45:05 aduret Exp $
  FILE:  cache.c
  DESCR: Cache class for caching apply/exist etc. results in BDD package
  AUTH:  Jorn Lind
  DATE:  (C) june 1997
*************************************************************************/
#include <stdlib.h>
#include <string.h>
#include <limits.h>
#include "kernel.h"
#include "cache.h"
#include "prime.h"


// This is the root of the circular list of external caches.
// It is declared as an external cache itself, but is only used
// for the next/prev pointers.
bddExtCache external_caches = { NULL, 0, &external_caches, &external_caches };


/*************************************************************************
*************************************************************************/

void BddCache_reset(BddCache *cache)
{
  for (int n = 0; n < cache->tablesize; n++)
    cache->table[n].i.a = -1;
}


int BddCache_init(BddCache *cache, int size)
{
   size = bdd_nextpower(size);

   if ((cache->table=NEW(BddCacheData,size)) == NULL)
      return bdd_error(BDD_MEMORY);

   cache->tablesize = size;
   BddCache_reset(cache);
   return 0;
}


void BddCache_done(BddCache *cache)
{
   free(cache->table);
   cache->table = NULL;
   cache->tablesize = 0;
}


int BddCache_resize(BddCache *cache, int newsize)
{
   free(cache->table);
   return BddCache_init(cache, newsize);
}


void bdd_extcache_init(bddExtCache* cache, int size)
{
  if (size <= 0)
    size = bddcachesize;

  size = bdd_nextpower(size);
  if ((cache->table=NEW(bddExtCacheEntry, size)) == NULL)
    bdd_error(BDD_MEMORY);
  cache->tablesize = size;
  bdd_extcache_reset(cache);

  // register the new cache in the circular list
  cache->next_ext_cache = external_caches.next_ext_cache;
  cache->prev_ext_cache = &external_caches;
  external_caches.next_ext_cache->prev_ext_cache = cache;
  external_caches.next_ext_cache = cache;
}

void bdd_extcache_done(bddExtCache* cache)
{
  free(cache->table);
  cache->table = NULL;
  cache->tablesize = 0;

  // remove the cache from the circular list
  cache->next_ext_cache->prev_ext_cache = cache->prev_ext_cache;
  cache->prev_ext_cache->next_ext_cache = cache->next_ext_cache;
}

void bdd_extcache_reset(bddExtCache* cache)
{
  for (int n = 0; n < cache->tablesize; n++)
    cache->table[n].arg1 = -1;
}

/* EOF */
