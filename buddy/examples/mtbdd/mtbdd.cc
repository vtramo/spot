#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include "bddx.h"
#include <iostream>


void ap_printer(FILE* f, int v)
{
  if (v < 3)
    fprintf(f, "%c", "abc"[v]);
  else
    fprintf(f, "%d", v);
}


int main(int argc, char** argv)
{
   bdd_init(500000, 50000);
   bdd_setvarnum(3);
   bdd_file_hook(ap_printer);

   bdd a = bdd_ithvar(0);
   bdd b = bdd_ithvar(1);
   bdd c = bdd_ithvar(2);
   bdd t0 = bdd_terminal(0);
   bdd t1 = bdd_terminal(1);
   bdd t2 = bdd_terminal(2);

   {
     bdd t3 = bdd_terminal(3);
     bdd t4 = bdd_terminal(0);
     bdd x = bdd_ite(a,
                     bdd_ite(b, t1, t3),
                     bdd_ite(b,
                             bdd_ite(c, t4, t3),
                             bdd_ite(c, t0, t2)));

     bdd y = bdd_ite(b,
                     bdd_ite(b, t1, t3),
                     bdd_ite(b,
                             bdd_ite(a, t4, t3),
                             bdd_ite(a, t0, t2)));

     // bdd_printset(x);
     // puts("");
     // bdd_printall();
     // bdd_gbc();
     // bdd_printall();
     bdd arr[4] = {x, y};

     bddExtCache mt_cache;
     bdd_extcache_init(&mt_cache, 100);
     arr[2] = bdd_mt_apply2(x, y,
                            [](int a , int b) { return a + b; },
                            &mt_cache, 1);
     /* this will use the cache */
     arr[2] = bdd_mt_apply2(x, y,
                            [](int a , int b) { return a + b; },
                            &mt_cache, 1);
     /* this resets the cache as a side effect */
     bdd_gbc();
     /* this recomputes everything */
     arr[2] = bdd_mt_apply2(x, y,
                            [](int a , int b) { return a + b; },
                            &mt_cache, 1);
     arr[3] = bdd_mt_apply1(arr[2],
                            [](int a) { return a + 1; },
                            bddfalse, bddtrue,
                            &mt_cache, 2);
     bdd_extcache_done(&mt_cache);
     bdd_printdot_array(arr, 4);
     fflush(stdout);
   }

   bdd_printall();

   return 0;
}
