#include "config.h"

#include <fstream>

#include <spot/tl/formula.hh>
#include <spot/tl/parse.hh>
#include <spot/twaalgos/hoa.hh>
#include <spot/twaalgos/translate_aa.hh>

int main(int argc, char * argv[])
{
  if (argc < 3)
    return 1;

  spot::formula f = spot::parse_formula(argv[1]);
  spot::bdd_dict_ptr d = spot::make_bdd_dict();
  auto aut = ltl_to_aa(f, d, true);

  std::ofstream out(argv[2]);
  spot::print_hoa(out, aut);
  return 0;
}
