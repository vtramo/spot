// -*- coding: utf-8 -*-
// Copyright (C) 2017-2021 Laboratoire de Recherche et Développement
// de l'Epita.
//
// This file is part of Spot, a model checking library.
//
// Spot is free software; you can redistribute it and/or modify it
// under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 3 of the License, or
// (at your option) any later version.
//
// Spot is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
// or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
// License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#include "config.h"
#include <spot/twaalgos/split.hh>
#include <spot/misc/minato.hh>
#include <spot/misc/bddlt.hh>
#include <spot/priv/robin_hood.hh>

#include <algorithm>
#include <map>
#include <unordered_set>

namespace std 
{
	template<>
	struct hash<::bdd> 
	{
		size_t operator()(::bdd const& instance) const noexcept
    {
			return ::spot::bdd_hash{}(instance);
		}
	};

  template<>
	struct hash<pair<bdd, bdd>> 
	{
		size_t operator()(pair<bdd, bdd> const& x) const noexcept
        {
			size_t first_hash = std::hash<bdd>()(x.first);
			size_t second_hash = std::hash<bdd>()(x.second);
			first_hash ^= second_hash + 0x9e3779b9 + (first_hash << 6) + (first_hash >> 2);
            return  first_hash;
		}
	};
}

namespace spot 
{
    // Checks if the lhs is a subset of rhs, lhs <= rhs
    static bool bdd_is_subset(bdd lhs, bdd rhs) 
    {
        return (lhs & rhs) == rhs;
    }

  // We attempt to add a potentially new set of symbols defined as "value" to our current set of edge partitions, "current_set". 
  // We also specify a set of valid symbols considered
	static void add_to_lower_bound_set_helper(
        std::unordered_set<bdd>& current_set, 
        bdd valid_symbol_set, 
        bdd value
  ) 
	{
    // This function's correctness is defined by the invariant, that we never add a bdd to our
    // current set unless the bdd is disjoint from every other element in the current_set. In other words,
    // we will only reach the final set.insert(value), if we can iterate over the whole of current_set without 
    // finding some set intersections
		if(value == bddfalse) return; // Don't add empty sets, as they subsume everything
		for(auto sym : current_set) 
		{
      // If a sym is a subset of value, recursively add the set of symbols defined
      // in value, but not in sym. This ensures the two elements are disjoint.
			if(bdd_is_subset(sym, value)) 
			{
				add_to_lower_bound_set_helper(current_set, valid_symbol_set, (value & !sym) & valid_symbol_set);
				return;
			}
      // If a sym is a subset of the value we're trying to add, then we remove the symbol and add
      // the two symbols created by partitioning the sym with value. 
			else if (bdd_is_subset(value, sym)) 
			{
				current_set.erase(sym);
				add_to_lower_bound_set_helper(current_set, valid_symbol_set, sym & value);
				add_to_lower_bound_set_helper(current_set, valid_symbol_set, sym & !value);
				return;
			}
		}
    // This line is only reachable if value is not a subset and doesn't subsume any element currently in our set
		current_set.insert(value);
	}

  static std::array<bdd, 4> create_possible_intersections(
      bdd valid_symbol_set,
      std::pair<bdd, bdd> const& first, 
      std::pair<bdd, bdd> const& second
  ) 
  {
    return {
      first.first & second.first & valid_symbol_set,
      first.second & second.first & valid_symbol_set,
      first.first & second.second & valid_symbol_set,
      first.second & second.second & valid_symbol_set,
    };
  }

  // Transforms each element of the basis into a complement pair, with a valid symbol set specified
  static std::unordered_set<std::pair<bdd, bdd>> create_complement_pairs(std::vector<bdd> const& basis, bdd valid_symbol_set) 
  {
    std::unordered_set<std::pair<bdd, bdd>> intersections;
    for(auto& sym : basis) 
    {
      if(auto intersection = sym & valid_symbol_set; intersection != bddfalse) 
      {
        intersections.insert(std::make_pair(intersection, valid_symbol_set & !intersection));
      }
    }
    return intersections;
  }

  // Compute the lower set bound of a set. A valid symbol set is also provided to make sure that
  // no symbol exists in the output if it is not also included in the valid symbol set
	static std::unordered_set<bdd> lower_set_bound(std::vector<bdd> const& basis, bdd valid_symbol_set) 
	{
    auto complement_pairs = create_complement_pairs(basis, valid_symbol_set);
		if(complement_pairs.size() == 1) 
		{
      std::unordered_set<bdd> lower_bound;
			auto& pair = *complement_pairs.begin();
			if(pair.first != bddfalse && bdd_is_subset(pair.first, valid_symbol_set)) 
				lower_bound.insert(pair.first);
			if(pair.second != bddfalse && bdd_is_subset(pair.second, valid_symbol_set)) 
				lower_bound.insert(pair.second);
            return lower_bound; 
		}
    else
    {
      std::unordered_set<bdd> lower_bound;
      for(auto it = complement_pairs.begin(); it != complement_pairs.end(); it++)
      {
        for(auto it2 = std::next(it); it2 != complement_pairs.end(); it2++) 
        {
          for(auto& intersection : create_possible_intersections(valid_symbol_set, *it, *it2)) 
          {
            add_to_lower_bound_set_helper(lower_bound, valid_symbol_set, intersection);
          }
        }
      }
      return lower_bound;
    }
	}

  // Partitions a symbol based on a list of other bdds called the basis. The resulting partition will have the property that
  // for any paritioned element and any element element in the basis, the partitioned element will either by completely contained
  // by that element of the basis, or completely disjoint.
	static std::unordered_set<bdd> generate_contained_or_disjoint_symbols(bdd sym, std::vector<bdd> const& basis) 
	{
		auto lower_bound = lower_set_bound(basis, sym);
    // If the sym was disjoint from everything in the basis, we'll be left with an empty lower_bound.
    // To fix this, we will simply return a singleton, with sym as the only element.
    // Notice, this singleton will satisfy the requirements of a return value from this function.
    // Additionally, if the sym is false, that means nothing can traverse it, so we simply are left with no edges.
		if(lower_bound.empty() && sym != bddfalse)
    {
      lower_bound.insert(sym);
    }
		return lower_bound;
	}

  twa_graph_ptr split_edges(const const_twa_graph_ptr& aut)
  {
    twa_graph_ptr out = make_twa_graph(aut->get_dict());
    out->copy_acceptance_of(aut);
    out->copy_ap_of(aut);
    out->prop_copy(aut, twa::prop_set::all());
    out->new_states(aut->num_states());
    out->set_init_state(aut->get_init_state_number());

    // We use a cache to avoid the costly loop around minterms_of().
    // Cache entries have the form (id, [begin, end]) where id is the
    // number of a BDD that as been (or will be) split, and begin/end
    // denotes a range of existing transition numbers that cover the
    // split.
    typedef std::pair<unsigned, unsigned> cached_t;
    robin_hood::unordered_map<unsigned, cached_t> split_cond;

    bdd all = aut->ap_vars();
    internal::univ_dest_mapper<twa_graph::graph_t> uniq(out->get_graph());

    for (auto& e: aut->edges())
      {
        bdd cond = e.cond;
        if (cond == bddfalse)
          continue;
        unsigned dst = e.dst;
        if (aut->is_univ_dest(dst))
          {
            auto d = aut->univ_dests(dst);
            dst = uniq.new_univ_dests(d.begin(), d.end());
          }

        auto& [begin, end] = split_cond[cond.id()];
        if (begin == end)
          {
            begin = out->num_edges() + 1;
            for (bdd minterm: minterms_of(cond, all))
              out->new_edge(e.src, dst, minterm, e.acc);
            end = out->num_edges() + 1;
          }
        else
          {
            auto& g = out->get_graph();
            for (unsigned i = begin; i < end; ++i)
              out->new_edge(e.src, dst, g.edge_storage(i).cond, e.acc);
          }
      }
    return out;
  }
  
  twa_graph_ptr split_edges(const const_twa_graph_ptr& aut, std::vector<bdd> const& basis) 
  {
      twa_graph_ptr out = make_twa_graph(aut->get_dict());
      out->copy_acceptance_of(aut);
      out->copy_ap_of(aut);
      out->prop_copy(aut, twa::prop_set::all());
      out->new_states(aut->num_states());
      out->set_init_state(aut->get_init_state_number());

      // We use a cache to avoid the costly loop around minterms_of().
      // Cache entries have the form (id, [begin, end]) where id is the
      // number of a BDD that as been (or will be) split, and begin/end
      // denotes a range of existing transition numbers that cover the
      // split.
      using cached_t = std::pair<unsigned, unsigned>;
      std::unordered_map<unsigned, cached_t> split_cond;
      internal::univ_dest_mapper<twa_graph::graph_t> uniq(out->get_graph());

      for (auto& e: aut->edges())
      {
          bdd const& cond = e.cond;
          unsigned dst = e.dst;

          if (cond == bddfalse) continue;

          if (aut->is_univ_dest(dst))
          {
              auto d = aut->univ_dests(dst);
              dst = uniq.new_univ_dests(d.begin(), d.end());
          }

          auto& [begin, end] = split_cond[cond.id()];
          if (begin == end)
          {
              begin = out->num_edges() + 1;
              for (bdd minterm : generate_contained_or_disjoint_symbols(cond, basis)) 
              {
                  out->new_edge(e.src, dst, minterm, e.acc);
              }
              end = out->num_edges() + 1;
          }
          else
          {
              auto& g = out->get_graph();
              for (unsigned i = begin; i < end; ++i) 
              {
                  out->new_edge(e.src, dst, g.edge_storage(i).cond, e.acc);
              }
          }
      }
      return out;
  }
}
