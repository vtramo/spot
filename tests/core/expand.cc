#include "config.h"

#include <spot/tl/expansions.hh>
#include <spot/tl/parse.hh>
#include <spot/twa/formula2bdd.hh>
#include <iostream>

int main(int argc, char** argv)
{
  if (argc != 2)
    return 1;

  spot::formula f = spot::parse_infix_sere(argv[1]).f;
  auto d = spot::make_bdd_dict();

  auto m = spot::expansion(f, d, nullptr);

  for (const auto& [bdd_l, form] : m)
    std::cout << '[' << bdd_to_formula(bdd_l, d) << ']' << ": " << form << std::endl;
  std::cout << "formula: " << expansion_to_formula(m, d) << std::endl;

  d->unregister_all_my_variables(nullptr);

  return 0;
}
