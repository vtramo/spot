#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include "bddx.h"
#include <iostream>
#include <cassert>


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

     bdd sup = bdd_support(arr[2]);
     assert(sup == (a & b & c));

     for (auto [minterm, term]: minterms_mt_of(arr[2], sup))
       std::cout << minterm << " -> " << term << '\n';
     std::cout << "--\n";
     for (auto [path, term]: paths_mt_of(arr[2]))
       std::cout << path << " -> " << term << '\n';
     std::cout << "--\n";
     for (int term: terminals_of(arr[2]))
       std::cout << "terminal " << term << '\n';

     std::cout << "--\n";
     for (bdd sat: paths_of(sup))
       std::cout << sat << '\n';
     std::cout << "--\n";
     for (bdd sat: paths_of(bddtrue))
       std::cout << sat << '\n';
     std::cout << "--\n";
     for (bdd sat: paths_of(bddfalse))
       std::cout << sat << '\n';
     std::cout << "--\n";

     arr[0] = !a & !b & t0;
     bdd_printdot_array(arr, 1);
     for (auto [path, term]: paths_mt_of(arr[0]))
       std::cout << path << " -> " << term << '\n';
     std::cout << "--\n";

     arr[0] = !a & !b & t0;
     bdd_printdot_array(arr, 1);
     std::cerr << "leaves of arr[0]\n";
     for (bdd b: leaves_of(arr[0]))
       {
         if (b == bddtrue)
           std::cerr << "  true";
         else if (b == bddfalse)
           std::cerr << "  false";
         else
           std::cerr << "  " << bdd_get_terminal(b);
       }
     std::cout << '\n';

     std::cerr << "leaves of arr[0..3]\n";
     std::vector<bdd> varr(arr, arr + 4);
     for (bdd b: leaves_of(varr))
       {
         if (b == bddtrue)
           std::cerr << "  true";
         else if (b == bddfalse)
           std::cerr << "  false";
         else
           std::cerr << "  " << bdd_get_terminal(b);
       }
     std::cout << '\n';

     fflush(stdout);
   }

   bdd_printall();

   return 0;
}
