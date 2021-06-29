
/*  template <typename ConstAutPtr, bool Cosimulation, bool Sba>
  class data_acc
  {
  };

  template <typename ConstAutPtr>
  class data_acc<ConstAutPtr, true, true>
  {
  public:
    std::vector<acc_cond::mark_t> acc_;
  };

  template <typename ConstAutPtr, bool Cosimulation, bool Sba>
  class cond_proxy;

  template <bool Cosimulation, bool Sba>
  class cond_proxy<const_twa_graph_ptr, Cosimulation, Sba>
  {
    typedef twa_graph_edge_data edge;

  public:
    cond_proxy(const const_twa_graph_ptr&)
    {}

    inline bool cond_implies(const twa_graph_edge_data& lhs,
                              const twa_graph_edge_data& rhs) const
    {
      return bdd_implies(lhs.cond, rhs.cond);
    }

    inline bdd new_cond_from(const edge& e) const
    {
      return e.cond;
    }
  };

  template <bool Cosimulation, bool Sba>
  class cond_proxy<const_twacube_ptr, Cosimulation, Sba>
  {
  public:
    cond_proxy(const const_twacube_ptr& a)
      : cs_(a->get_cubeset())
    {
    }

    inline bool cond_implies(const transition& lhs,
                              const transition& rhs) const
    {
      return cs_.implies(lhs.cube_, rhs.cube_);
    }

    inline cube new_cond_from(const transition& e) const
    {
      return cs_.copy(e.cube_);
    }

    const cubeset& cs_;
  };

  template <typename ConstAutPtr, bool Cosimulation, bool Sba>
  class reduce_sim : public data_acc<ConstAutPtr, Cosimulation, Sba>
                     , public cond_proxy<ConstAutPtr, Cosimulation, Sba>
  {
  public:
    typedef std::shared_ptr<
      typename std::remove_const<
        typename ConstAutPtr::element_type>::type> aut_ptr_t;

    reduce_sim(const ConstAutPtr& aut, unsigned nb_thread=0);

    auto run();

  //private:
    // If aut_ is deterministic, only the lower left triangle is set.
    std::vector<char> compute_simulation();
    std::vector<char> compute_simulation_scc();
    std::vector<char> compute_simulation_par1();
    std::vector<char> compute_simulation_par2();
    std::vector<char> compute_simulation_par2_1();
    std::vector<char> compute_simulation_par3();

    static constexpr bool is_twa_graph =
                        std::is_same<ConstAutPtr, const_twa_graph_ptr>::value;

    ConstAutPtr aut_;
    ConstAutPtr original_;
    unsigned nb_thread_;
  };

  template <typename ConstAutPtr, bool Cosimulation, bool Sba>
  reduce_sim<ConstAutPtr, Cosimulation, Sba>
  ::reduce_sim(const ConstAutPtr& aut, unsigned nb_thread)
    : cond_proxy<ConstAutPtr, Cosimulation, Sba>(aut)
    , original_(aut)
    , nb_thread_(nb_thread)
  {
    unsigned n = aut->num_states();

    aut_ptr_t a = create_twa_from(aut);
    for (unsigned i = 0; i < n; ++i)
      a->new_state();
    a->set_init_state(aut->get_init_state_number());

    // Whether we simulate or cosimulate, we transform the acceptance into all
    // fin. If we cosimulate, we also reverse all the edges.
    const auto all_inf = aut->acc().get_acceptance().used_inf_fin_sets().first;

    const auto& ga = aut->get_graph();
    auto& gr = a->get_graph();

    for (unsigned s = 0; s < n; ++s)
      for (const auto& e : ga.out(s))
        if constexpr(Cosimulation)
          gr.new_edge(e.dst, e.src, this->new_cond_from(e), e.acc ^ all_inf);
        else
          gr.new_edge(e.src, e.dst, this->new_cond_from(e), e.acc ^ all_inf);

    if constexpr(!Sba)
      {
        bool state_acc = true;

        // common_out[i] is the set of acceptance set numbers common to
        // all outgoing edges of state i.
        std::vector<acc_cond::mark_t> common_out(n);
        for (unsigned s = 0; s < n; ++s)
          {
            bool first = true;
            for (auto& e : gr.out(s))
              if (first)
                {
                  common_out[s] = e.acc;
                  first = false;
                }
              else if (common_out[s] != e.acc)
                {
                  state_acc = false;
                  break;
                }

            if (!state_acc)
              break;
          }

      // Pull the common outgoing sets to the incoming
      // edges.  Doing so seems to favor cases where states
      // can be merged.
      if (state_acc)
        for (auto& e : gr.edges())
          e.acc = (e.acc - common_out[e.src]) | common_out[e.dst];
      }

    if constexpr(Sba && Cosimulation)
      {
        this->acc_.reserve(n);
        for (unsigned s = 0; s < n; ++s)
          this->acc_.push_back(original_->state_acc_sets(s) ^ all_inf);
      }

    aut_ = std::move(a);
  }
*/
  template <typename ConstAutPtr, bool Cosimulation, bool Sba>
  std::vector<char>
  reduce_sim<ConstAutPtr, Cosimulation, Sba>::compute_simulation_scc()
  {
    // At the start, we consider that all the pairs of vertices are simulating
    // each other. At each iteration we detect which ones are not simulating
    // and we remove them from the set. This information propagate backwards,
    // so we only need to check the peers whose successors were updated in the
    // previous iteration. To limit the number of iterations, we update them in
    // reverse topological order.

    const size_t n = aut_->num_states();
    bool only_bisimu = false;
    if constexpr(is_twa_graph)
      only_bisimu = is_deterministic(aut_);

    const auto& ga = aut_->get_graph();

    // We need to have the predecessors of a state for the backward propagation.
    digraph<void, void> reverse(n, aut_->num_edges());
    reverse.new_states(n);

    for (unsigned s = 0; s < n; ++s)
      for (const auto& e : ga.out(s))
        reverse.new_edge(e.dst, e.src);

    reverse.sort_edges_([](const auto& e1, const auto& e2)
        {
          if (e1.src != e2.src)
            return e1.src < e2.src;
          return e1.dst < e2.dst;
        });

    // Remove all duplicates.
    auto& edges = reverse.edge_vector();
    edges.erase(std::unique(edges.begin() + 1, edges.end()), edges.end());
    reverse.chain_edges_();

    // Compute a reverse topological order for all the states. So that the
    // algorithm iterates as few times as possible, we must update all the
    // successors of a state before updating it.

    scc_info si(aut_, spot::scc_info_options::NONE);
    unsigned init = aut_->get_init_state_number();

    auto compute_order_in_scc = [&](unsigned scc, unsigned& begin, unsigned& end)
    {
      std::vector<unsigned> todo;
      todo.reserve(n);

      std::vector<unsigned> order(n, 0);
      const auto& go = original_->get_graph();

      unsigned i = Cosimulation ? 0 : n - 1;
      std::vector<bool> seen(n, false);

      todo.push_back(si.one_state_of(scc));
      seen[todo.back()] = true;
      while (!todo.empty())
        {
          unsigned cur = todo.back();
          todo.pop_back();
          std::cerr << "i: " << i << '\n';
          order[i] = cur;
          i += Cosimulation ? 1 : -1;

          for (const auto& e : go.out(cur))
            {
              if (!seen[e.dst] && si.scc_of(e.dst) == scc)
                {
                  seen[e.dst] = true;
                  todo.push_back(e.dst);
                }
            }
          }

      if (Cosimulation)
      {
        throw std::runtime_error("Not done yet l 1204");
        begin = 0;//i - 1;
        end = n;// + 2;
      }
      else
      {
        begin = i + 1;
        end = n;
      }
      return order;
    };

    std::vector<char> can_sim(n * n, true);

    // Test if s1 simulates s2.
    const auto test_sim = [&](size_t s1, size_t s2) -> bool
      {
        auto s_edges = ga.out(s1);
        auto d_edges = ga.out(s2);

        // s1 simulates s2 only if for all the edges of s2 there is an edges s1
        // with compatible condition, acceptance and the destinations simulate
        // each other.
        return std::all_of(s_edges.begin(), s_edges.end(),
          [&](const auto& s_edge) -> bool
            {
              size_t i = static_cast<size_t>(s_edge.dst) * n;

              return std::find_if(d_edges.begin(), d_edges.end(),
                [&](const auto& d_edge) -> bool
                  {
                    // Checks if the destinations of the spoiler simulates the
                    // duplicator.
                    if (!can_sim[i + static_cast<size_t>(d_edge.dst)])
                      return false;

                    if constexpr(Sba && Cosimulation)
                      {
                        if (!(this->acc_[d_edge.src])
                            .subset(this->acc_[s_edge.src]))
                          return false;
                      }
                    else
                      {
                        if (!d_edge.acc.subset(s_edge.acc))
                          return false;
                      }

                    if constexpr(Cosimulation)
                      {
                        if (s_edge.dst == init && d_edge.dst != init)
                          return false;
                      }

                    return this->cond_implies(s_edge, d_edge);
                  });
            });
      };

    std::vector<unsigned> todo(n, true);

    auto compute_sim_in_scc = [&](unsigned scc)
    {
      //TODO order has too much zero
      unsigned begin;
      unsigned end;
      auto order = compute_order_in_scc(scc, begin, end);

      bool has_changed;
      do
        {
          has_changed = false;
          std::cerr << begin << ' ' << end << '\n';
          for (unsigned ii = begin; ii < end; ++ii)
            {
              unsigned i = order[ii];
              if (!todo[i])
                continue;

              todo[i] = false;

              // Update all the predecessors that changed on last turn.
              for (const auto& re : reverse.out(i))
                {
                  size_t u = re.dst;
                  size_t idx = u * n;

                  if (only_bisimu)
                    {
                      // If the automaton is deterministic, compute only the
                      // bisimulation.
                      for (size_t v = 0; v < u; ++v)
                        {
                          // u doesn't simulate v
                          if (!can_sim[idx + v])
                            continue;

                          if (!test_sim(u, v) || !test_sim(v, u))
                            {
                              can_sim[u * n + v] = false;
                              has_changed = true;
                              todo[u] = true;
                              todo[v] = true;
                            }
                        }
                    }
                  else
                    {
                      for (unsigned v = 0; v < n; ++v)
                        {
                          // u doesn't simulate v
                          if (!can_sim[idx + v])
                            continue;

                          if (!test_sim(u, v))
                            {
                              can_sim[idx + v] = false;
                              has_changed = true;
                              todo[u] = true;
                            }
                        }
                    }
                }
            }
        }
      while (has_changed);
    };

    for (unsigned scc = 0; scc < si.scc_count(); ++scc)
      compute_sim_in_scc(scc);

    if constexpr(Cosimulation)
      {
        if (!ga.out(init).begin())
          {
            for (unsigned i = 0; i < n; ++i)
              {
                can_sim[i * n + init] = i == init;
                can_sim[init * n + i] = false;
              }
          }
        else
          for (unsigned i = 0; i < n; ++i)
            {
              // i doesn't simulate init
              can_sim[i * n + init] = i == init;
            }
      }

    return can_sim;
  }

  template <typename ConstAutPtr, bool Cosimulation, bool Sba>
  std::vector<char>
  reduce_sim<ConstAutPtr, Cosimulation, Sba>::compute_simulation()
  {
    // At the start, we consider that all the pairs of vertices are simulating
    // each other. At each iteration we detect which ones are not simulating
    // and we remove them from the set. This information propagate backwards,
    // so we only need to check the peers whose successors were updated in the
    // previous iteration. To limit the number of iterations, we update them in
    // reverse topological order.

    const size_t n = aut_->num_states();
    bool only_bisimu = false;
    if constexpr(is_twa_graph)
      only_bisimu = is_deterministic(aut_);

    const auto& ga = aut_->get_graph();

    // We need to have the predecessors of a state for the backward propagation.
    digraph<void, void> reverse(n, aut_->num_edges());
    reverse.new_states(n);

    for (unsigned s = 0; s < n; ++s)
      for (const auto& e : ga.out(s))
        reverse.new_edge(e.dst, e.src);

    reverse.sort_edges_([](const auto& e1, const auto& e2)
        {
          if (e1.src != e2.src)
            return e1.src < e2.src;
          return e1.dst < e2.dst;
        });

    // Remove all duplicates.
    auto& edges = reverse.edge_vector();
    edges.erase(std::unique(edges.begin() + 1, edges.end()), edges.end());
    reverse.chain_edges_();

    // Compute a reverse topological order for all the states. So that the
    // algorithm iterates as few times as possible, we must update all the
    // successors of a state before updating it.
    std::vector<unsigned> order(n, 0);
    std::vector<unsigned> todo;
    todo.reserve(n);

    unsigned init = aut_->get_init_state_number();

    {
      const auto& go = original_->get_graph();

      unsigned i = Cosimulation ? 0 : n - 1;
      std::vector<bool> seen(n, false);
      todo.push_back(init);
      seen[init] = true;
      while (!todo.empty())
        {
          unsigned cur = todo.back();
          todo.pop_back();
          order[i] = cur;
          i += Cosimulation ? 1 : -1;

          for (const auto& e : go.out(cur))
            {
              if (!seen[e.dst])
                {
                  seen[e.dst] = true;
                  todo.push_back(e.dst);
                }
            }
          }
    }

    std::vector<char> can_sim(n * n, true);

    // Test if s1 simulates s2.
    const auto test_sim = [&](size_t s1, size_t s2) -> bool
      {
        auto s_edges = ga.out(s1);
        auto d_edges = ga.out(s2);

        // s1 simulates s2 only if for all the edges of s2 there is an edges s1
        // with compatible condition, acceptance and the destinations simulate
        // each other.
        return std::all_of(s_edges.begin(), s_edges.end(),
          [&](const auto& s_edge) -> bool
            {
              size_t i = static_cast<size_t>(s_edge.dst) * n;

              return std::find_if(d_edges.begin(), d_edges.end(),
                [&](const auto& d_edge) -> bool
                  {
                    // Checks if the destinations of the spoiler simulates the
                    // duplicator.
                    if (!can_sim[i + static_cast<size_t>(d_edge.dst)])
                      return false;

                    if constexpr(Sba && Cosimulation)
                      {
                        if (!(this->acc_[d_edge.src])
                            .subset(this->acc_[s_edge.src]))
                          return false;
                      }
                    else
                      {
                        if (!d_edge.acc.subset(s_edge.acc))
                          return false;
                      }

                    if constexpr(Cosimulation)
                      {
                        if (s_edge.dst == init && d_edge.dst != init)
                          return false;
                      }

                    return this->cond_implies(s_edge, d_edge);
                  });
            });
      };

    todo.resize(n, true);

    bool has_changed;
    do
      {
        has_changed = false;
        for (unsigned i : order)
          {
            if (!todo[i])
              continue;

            todo[i] = false;

            // Update all the predecessors that changed on last turn.
            for (const auto& re : reverse.out(i))
              {
                size_t u = re.dst;
                size_t idx = u * n;

                if (only_bisimu)
                  {
                    // If the automaton is deterministic, compute only the
                    // bisimulation.
                    for (size_t v = 0; v < u; ++v)
                      {
                        // u doesn't simulate v
                        if (!can_sim[idx + v])
                          continue;

                        if (!test_sim(u, v) || !test_sim(v, u))
                          {
                            can_sim[u * n + v] = false;
                            has_changed = true;
                            todo[u] = true;
                            todo[v] = true;
                          }
                      }
                  }
                else
                  {
                    for (unsigned v = 0; v < n; ++v)
                      {
                        // u doesn't simulate v
                        if (!can_sim[idx + v])
                          continue;

                        if (!test_sim(u, v))
                          {
                            can_sim[idx + v] = false;
                            has_changed = true;
                            todo[u] = true;
                          }
                      }
                  }
              }
          }
      }
    while (has_changed);

    if constexpr(Cosimulation)
      {
        if (!ga.out(init).begin())
          {
            for (unsigned i = 0; i < n; ++i)
              {
                can_sim[i * n + init] = i == init;
                can_sim[init * n + i] = false;
              }
          }
        else
          for (unsigned i = 0; i < n; ++i)
            {
              // i doesn't simulate init
              can_sim[i * n + init] = i == init;
            }
      }

    return can_sim;
  }


  template <typename ConstAutPtr, bool Cosimulation, bool Sba>
  std::vector<char>
  reduce_sim<ConstAutPtr, Cosimulation, Sba>::compute_simulation_par1()
  {
    if (SPOT_UNLIKELY(is_twa_graph))
      throw std::runtime_error("compute_simulation_par(): does not support twa_graph");

    // At the start, we consider that all the pairs of vertices are simulating
    // each other. At each iteration we detect which ones are not simulating
    // and we remove them from the set. This information propagate backwards,
    // so we only need to check the peers whose successors were updated in the
    // previous iteration. To limit the number of iterations, we update them in
    // reverse topological order.

    const size_t n = aut_->num_states();
    const auto& ga = aut_->get_graph();

    // We need to have the predecessors of a state for the backward propagation.
    digraph<void, void> reverse(n, aut_->num_edges());
    reverse.new_states(n);

    for (unsigned s = 0; s < n; ++s)
      for (const auto& e : ga.out(s))
        reverse.new_edge(e.dst, e.src);

    reverse.sort_edges_([](const auto& e1, const auto& e2)
        {
          if (e1.src != e2.src)
            return e1.src < e2.src;
          return e1.dst < e2.dst;
        });

    // Remove all duplicates.
    auto& edges = reverse.edge_vector();
    edges.erase(std::unique(edges.begin() + 1, edges.end()), edges.end());
    reverse.chain_edges_();

    // Compute a reverse topological order for all the states. So that the
    // algorithm iterates as few times as possible, we must update all the
    // successors of a state before updating it.
    std::vector<unsigned> order(n, 0);

    unsigned init = aut_->get_init_state_number();

    {
      const auto& go = original_->get_graph();

      std::vector<unsigned> todo;
      todo.reserve(n);

      unsigned i = Cosimulation ? 0 : n - 1;
      std::vector<bool> seen(n, false);
      todo.push_back(init);
      seen[init] = true;
      while (!todo.empty())
        {
          unsigned cur = todo.back();
          todo.pop_back();
          order[i] = cur;
          i += Cosimulation ? 1 : -1;

          for (const auto& e : go.out(cur))
            {
              if (!seen[e.dst])
                {
                  seen[e.dst] = true;
                  todo.push_back(e.dst);
                }
            }
          }
    }

    std::vector<char> can_sim(n * n, true);

    // Test if s1 simulates s2.
    const auto test_sim = [&](size_t s1, size_t s2) -> bool
      {
        auto s_edges = ga.out(s1);
        auto d_edges = ga.out(s2);

        // s1 simulates s2 only if for all the edges of s2 there is an edges s1
        // with compatible condition, acceptance and the destinations simulate
        // each other.
        return std::all_of(s_edges.begin(), s_edges.end(),
          [&](const auto& s_edge) -> bool
            {
              size_t i = static_cast<size_t>(s_edge.dst) * n;

              return std::find_if(d_edges.begin(), d_edges.end(),
                [&](const auto& d_edge) -> bool
                  {
                    // Checks if the destinations of the spoiler simulates the
                    // duplicator.
                    if (!can_sim[i + static_cast<size_t>(d_edge.dst)])
                      return false;

                    if constexpr(Sba && Cosimulation)
                      {
                        if (!(this->acc_[d_edge.src])
                            .subset(this->acc_[s_edge.src]))
                          return false;
                      }
                    else
                      {
                        if (!d_edge.acc.subset(s_edge.acc))
                          return false;
                      }

                    if constexpr(Cosimulation)
                      {
                        if (s_edge.dst == init && d_edge.dst != init)
                          return false;
                      }

                    return this->cond_implies(s_edge, d_edge);
                  });
            });
      };

    moodycamel::ConcurrentQueue<unsigned> todo(n);
    for (unsigned i : order)
      todo.enqueue(i);

    auto loop = [&](unsigned id)
    {
      unsigned i;
      while (todo.try_dequeue(i))
      {
        // Update all the predecessors that changed on last turn.
        for (const auto& re : reverse.out(i))
        {
          size_t u = re.dst;
          size_t idx = u * n;

          bool has_changed = false;
          for (unsigned v = 0; v < n; ++v)
          {
            // u doesn't simulate v
            if (!can_sim[idx + v])
              continue;

            if (!test_sim(u, v))
            {
              can_sim[idx + v] = false;
              has_changed = true;
            }
          }
          if (has_changed)
            todo.enqueue(u);
        }
      }
    };

    std::vector<std::thread> ts;
    ts.reserve(nb_thread_ - 1);

    for (unsigned i = 0; i < nb_thread_ - 1; ++i)
      ts.emplace_back(std::thread(loop, i));

    loop(nb_thread_ - 1);

    for (unsigned i = 0; i < nb_thread_ - 1; ++i)
      ts[i].join();

    if constexpr(Cosimulation)
      {
        if (!ga.out(init).begin())
          {
            for (unsigned i = 0; i < n; ++i)
              {
                can_sim[i * n + init] = i == init;
                can_sim[init * n + i] = false;
              }
          }
        else
          for (unsigned i = 0; i < n; ++i)
            {
              // i doesn't simulate init
              can_sim[i * n + init] = i == init;
            }
      }

    return can_sim;
  }

  template <typename ConstAutPtr, bool Cosimulation, bool Sba>
  std::vector<char>
  reduce_sim<ConstAutPtr, Cosimulation, Sba>::compute_simulation_par2_1()
  {
    if (SPOT_UNLIKELY(is_twa_graph))
      throw std::runtime_error("compute_simulation_par(): does not support twa_graph");

    // At the start, we consider that all the pairs of vertices are simulating
    // each other. At each iteration we detect which ones are not simulating
    // and we remove them from the set. This information propagate backwards,
    // so we only need to check the peers whose successors were updated in the
    // previous iteration. To limit the number of iterations, we update them in
    // reverse topological order.

    const size_t n = aut_->num_states();
    const auto& ga = aut_->get_graph();

    // We need to have the predecessors of a state for the backward propagation.
    digraph<void, void> reverse(n, aut_->num_edges());
    reverse.new_states(n);

    for (unsigned s = 0; s < n; ++s)
      for (const auto& e : ga.out(s))
        reverse.new_edge(e.dst, e.src);

    reverse.sort_edges_([](const auto& e1, const auto& e2)
        {
          if (e1.src != e2.src)
            return e1.src < e2.src;
          return e1.dst < e2.dst;
        });

    // Remove all duplicates.
    auto& edges = reverse.edge_vector();
    edges.erase(std::unique(edges.begin() + 1, edges.end()), edges.end());
    reverse.chain_edges_();

    // Compute a reverse topological order for all the states. So that the
    // algorithm iterates as few times as possible, we must update all the
    // successors of a state before updating it.
    std::vector<unsigned> order(n, 0);
    std::vector<unsigned> rev_order(n, 0);

    unsigned init = aut_->get_init_state_number();

    {
      const auto& go = original_->get_graph();

      std::vector<unsigned> todo;
      todo.reserve(n);

      unsigned i = Cosimulation ? 0 : n - 1;
      std::vector<bool> seen(n, false);
      todo.push_back(init);
      seen[init] = true;
      while (!todo.empty())
        {
          unsigned cur = todo.back();
          todo.pop_back();
          order[i] = cur;
          rev_order[cur] = i;
          i += Cosimulation ? 1 : -1;

          for (const auto& e : go.out(cur))
            {
              if (!seen[e.dst])
                {
                  seen[e.dst] = true;
                  todo.push_back(e.dst);
                }
            }
          }
    }

    std::vector<char> can_sim(n * n, true);

    // Test if s1 simulates s2.
    const auto test_sim = [&](size_t s1, size_t s2) -> bool
      {
        auto s_edges = ga.out(s1);
        auto d_edges = ga.out(s2);

        // s1 simulates s2 only if for all the edges of s2 there is an edges s1
        // with compatible condition, acceptance and the destinations simulate
        // each other.
        return std::all_of(s_edges.begin(), s_edges.end(),
          [&](const auto& s_edge) -> bool
            {
              size_t i = static_cast<size_t>(s_edge.dst) * n;

              return std::find_if(d_edges.begin(), d_edges.end(),
                [&](const auto& d_edge) -> bool
                  {
                    // Checks if the destinations of the spoiler simulates the
                    // duplicator.
                    if (!can_sim[i + static_cast<size_t>(d_edge.dst)])
                      return false;

                    if constexpr(Sba && Cosimulation)
                      {
                        if (!(this->acc_[d_edge.src])
                            .subset(this->acc_[s_edge.src]))
                          return false;
                      }
                    else
                      {
                        if (!d_edge.acc.subset(s_edge.acc))
                          return false;
                      }

                    if constexpr(Cosimulation)
                      {
                        if (s_edge.dst == init && d_edge.dst != init)
                          return false;
                      }

                    return this->cond_implies(s_edge, d_edge);
                  });
            });
      };

    unsigned size = (n + nb_thread_ - 1) / nb_thread_;

    auto loop = [&](unsigned id)
    {
      // FIXME last thread may not have the same size
      const unsigned begin = size * id;
      const unsigned end = (begin + size < n) ? begin + size : n;
      std::vector<char> local_todo(n, false);
      for (unsigned i = begin; i < end; ++i)
        local_todo[order[i]] = true;

      bool has_changed;
      bool has_changed_prev = true;

      do
      {
        has_changed = false;

        for (unsigned k = 0; k < n; ++k)
        {
          unsigned i = order[k];

          if (!local_todo[i])
            continue;
          local_todo[i] = false;

          // Update all the predecessors that changed on last turn.
          for (const auto& re : reverse.out(i))
          {
            size_t u = re.dst;
            size_t idx = u * n;

            for (unsigned v = 0; v < n; ++v)
            {
              // u doesn't simulate v
              if (!can_sim[idx + v])
                continue;

              if (!test_sim(u, v))
              {
                can_sim[idx + v] = false;
                has_changed = true;
                local_todo[u] = true;
              }
            }
          }
        }
      } while (has_changed);
    };

    std::vector<std::thread> ts;
    ts.reserve(nb_thread_ - 1);

    for (unsigned i = 0; i < nb_thread_ - 1; ++i)
      ts.emplace_back(std::thread(loop, i));

    loop(nb_thread_ - 1);

    for (unsigned i = 0; i < nb_thread_ - 1; ++i)
      ts[i].join();

    if constexpr(Cosimulation)
      {
        if (!ga.out(init).begin())
          {
            for (unsigned i = 0; i < n; ++i)
              {
                can_sim[i * n + init] = i == init;
                can_sim[init * n + i] = false;
              }
          }
        else
          for (unsigned i = 0; i < n; ++i)
            {
              // i doesn't simulate init
              can_sim[i * n + init] = i == init;
            }
      }

    return can_sim;
  }

  template <typename ConstAutPtr, bool Cosimulation, bool Sba>
  std::vector<char>
  reduce_sim<ConstAutPtr, Cosimulation, Sba>::compute_simulation_par2()
  {
    if (SPOT_UNLIKELY(is_twa_graph))
      throw std::runtime_error("compute_simulation_par(): does not support twa_graph");

    // At the start, we consider that all the pairs of vertices are simulating
    // each other. At each iteration we detect which ones are not simulating
    // and we remove them from the set. This information propagate backwards,
    // so we only need to check the peers whose successors were updated in the
    // previous iteration. To limit the number of iterations, we update them in
    // reverse topological order.

    const size_t n = aut_->num_states();
    const auto& ga = aut_->get_graph();

    // We need to have the predecessors of a state for the backward propagation.
    digraph<void, void> reverse(n, aut_->num_edges());
    reverse.new_states(n);

    for (unsigned s = 0; s < n; ++s)
      for (const auto& e : ga.out(s))
        reverse.new_edge(e.dst, e.src);

    reverse.sort_edges_([](const auto& e1, const auto& e2)
        {
          if (e1.src != e2.src)
            return e1.src < e2.src;
          return e1.dst < e2.dst;
        });

    // Remove all duplicates.
    auto& edges = reverse.edge_vector();
    edges.erase(std::unique(edges.begin() + 1, edges.end()), edges.end());
    reverse.chain_edges_();

    // Compute a reverse topological order for all the states. So that the
    // algorithm iterates as few times as possible, we must update all the
    // successors of a state before updating it.
    std::vector<unsigned> order(n, 0);
    std::vector<unsigned> rev_order(n, 0);

    unsigned init = aut_->get_init_state_number();

    {
      const auto& go = original_->get_graph();

      std::vector<unsigned> todo;
      todo.reserve(n);

      unsigned i = Cosimulation ? 0 : n - 1;
      std::vector<bool> seen(n, false);
      todo.push_back(init);
      seen[init] = true;
      while (!todo.empty())
        {
          unsigned cur = todo.back();
          todo.pop_back();
          order[i] = cur;
          rev_order[cur] = i;
          i += Cosimulation ? 1 : -1;

          for (const auto& e : go.out(cur))
            {
              if (!seen[e.dst])
                {
                  seen[e.dst] = true;
                  todo.push_back(e.dst);
                }
            }
          }
    }

    std::vector<char> can_sim(n * n, true);

    // Test if s1 simulates s2.
    const auto test_sim = [&](size_t s1, size_t s2) -> bool
      {
        auto s_edges = ga.out(s1);
        auto d_edges = ga.out(s2);

        // s1 simulates s2 only if for all the edges of s2 there is an edges s1
        // with compatible condition, acceptance and the destinations simulate
        // each other.
        return std::all_of(s_edges.begin(), s_edges.end(),
          [&](const auto& s_edge) -> bool
            {
              size_t i = static_cast<size_t>(s_edge.dst) * n;

              return std::find_if(d_edges.begin(), d_edges.end(),
                [&](const auto& d_edge) -> bool
                  {
                    // Checks if the destinations of the spoiler simulates the
                    // duplicator.
                    if (!can_sim[i + static_cast<size_t>(d_edge.dst)])
                      return false;

                    if constexpr(Sba && Cosimulation)
                      {
                        if (!(this->acc_[d_edge.src])
                            .subset(this->acc_[s_edge.src]))
                          return false;
                      }
                    else
                      {
                        if (!d_edge.acc.subset(s_edge.acc))
                          return false;
                      }

                    if constexpr(Cosimulation)
                      {
                        if (s_edge.dst == init && d_edge.dst != init)
                          return false;
                      }

                    return this->cond_implies(s_edge, d_edge);
                  });
            });
      };

    std::vector<std::atomic<char>> todo(n);
    std::fill(todo.begin(), todo.end(), false);

    unsigned size = (n + nb_thread_ - 1) / nb_thread_;

    std::atomic<unsigned> has_changed_all = 0;
    for (unsigned i = 0; i < nb_thread_; ++i)
      has_changed_all |= 1U << i;

    auto loop = [&](unsigned id)
    {
      std::vector<char> local_todo(n, true);

      // FIXME last thread may not have the same size
      const unsigned begin = size * id;
      const unsigned end = (begin + size < n) ? begin + size : n;
      const unsigned mask = 1U << id;

      bool has_changed;
      bool has_changed_prev = true;

      do
      {
        has_changed = false;

        for (unsigned k = begin; k < end; ++k)
        {
          unsigned i = order[k];
          if (!local_todo[i])
          {
            if (!todo[i].exchange(false, std::memory_order_relaxed))
              continue;
          }
          else
            local_todo[i] = false;

          // Update all the predecessors that changed on last turn.
          for (const auto& re : reverse.out(i))
          {
            size_t u = re.dst;
            size_t idx = u * n;

            for (unsigned v = 0; v < n; ++v)
            {
              // u doesn't simulate v
              if (!can_sim[idx + v])
                continue;

              if (!test_sim(u, v))
              {
                can_sim[idx + v] = false;

                has_changed = true;
                if (!has_changed_prev)
                {
                  has_changed_prev = true;
                  has_changed_all |= mask;
                }

                if (rev_order[u] >= begin && rev_order[u] < end)
                  local_todo[u] = true;
                else
                  todo[u].store(true, std::memory_order_relaxed);
              }
            }
          }
        }
        if (!has_changed && has_changed_prev)
        {
          has_changed_all &= ~mask;
          has_changed_prev = false;
        }

      } while (has_changed || has_changed_all);
    };

    std::vector<std::thread> ts;
    ts.reserve(nb_thread_ - 1);

    for (unsigned i = 0; i < nb_thread_ - 1; ++i)
      ts.emplace_back(std::thread(loop, i));

    loop(nb_thread_ - 1);

    for (unsigned i = 0; i < nb_thread_ - 1; ++i)
      ts[i].join();

    if constexpr(Cosimulation)
      {
        if (!ga.out(init).begin())
          {
            for (unsigned i = 0; i < n; ++i)
              {
                can_sim[i * n + init] = i == init;
                can_sim[init * n + i] = false;
              }
          }
        else
          for (unsigned i = 0; i < n; ++i)
            {
              // i doesn't simulate init
              can_sim[i * n + init] = i == init;
            }
      }

    return can_sim;
  }

  template <typename ConstAutPtr, bool Cosimulation, bool Sba>
  std::vector<char>
  reduce_sim<ConstAutPtr, Cosimulation, Sba>::compute_simulation_par3()
  {
    if (SPOT_UNLIKELY(is_twa_graph))
      throw std::runtime_error("compute_simulation_par(): does not support twa_graph");

    // At the start, we consider that all the pairs of vertices are simulating
    // each other. At each iteration we detect which ones are not simulating
    // and we remove them from the set. This information propagate backwards,
    // so we only need to check the peers whose successors were updated in the
    // previous iteration. To limit the number of iterations, we update them in
    // reverse topological order.

    const size_t n = aut_->num_states();
    const auto& ga = aut_->get_graph();

    // We need to have the predecessors of a state for the backward propagation.
    digraph<void, void> reverse(n, aut_->num_edges());
    reverse.new_states(n);

    for (unsigned s = 0; s < n; ++s)
      for (const auto& e : ga.out(s))
        reverse.new_edge(e.dst, e.src);

    reverse.sort_edges_([](const auto& e1, const auto& e2)
        {
          if (e1.src != e2.src)
            return e1.src < e2.src;
          return e1.dst < e2.dst;
        });

    // Remove all duplicates.
    auto& edges = reverse.edge_vector();
    edges.erase(std::unique(edges.begin() + 1, edges.end()), edges.end());
    reverse.chain_edges_();

    // Compute a reverse topological order for all the states. So that the
    // algorithm iterates as few times as possible, we must update all the
    // successors of a state before updating it.
    

    unsigned init = aut_->get_init_state_number();

    std::vector<std::atomic<char>> can_sim(n * n);
    for (unsigned i = 0; i < n; ++i)
      can_sim[i] = true;

    // Test if s1 simulates s2.
    const auto test_sim = [&](size_t s1, size_t s2) -> bool
      {
        auto s_edges = ga.out(s1);
        auto d_edges = ga.out(s2);

        // s1 simulates s2 only if for all the edges of s2 there is an edges s1
        // with compatible condition, acceptance and the destinations simulate
        // each other.
        return std::all_of(s_edges.begin(), s_edges.end(),
          [&](const auto& s_edge) -> bool
            {
              size_t i = static_cast<size_t>(s_edge.dst) * n;

              return std::find_if(d_edges.begin(), d_edges.end(),
                [&](const auto& d_edge) -> bool
                  {
                    // Checks if the destinations of the spoiler simulates the
                    // duplicator.
                    if (!can_sim[i + static_cast<size_t>(d_edge.dst)])
                      return false;

                    if constexpr(Sba && Cosimulation)
                      {
                        if (!(this->acc_[d_edge.src])
                            .subset(this->acc_[s_edge.src]))
                          return false;
                      }
                    else
                      {
                        if (!d_edge.acc.subset(s_edge.acc))
                          return false;
                      }

                    if constexpr(Cosimulation)
                      {
                        if (s_edge.dst == init && d_edge.dst != init)
                          return false;
                      }

                    return this->cond_implies(s_edge, d_edge);
                  });
            });
      };

    auto loop = [&](unsigned id)
    {
      std::vector<unsigned> order(n, 0);
      std::iota(order.begin(), order.end(), 0);
      std::random_shuffle(order.begin(), order.end());

      std::vector<char> todo(n, true);
      bool has_changed;

      do
      {
        has_changed = false;

        for (unsigned k = 0; k < n; ++k)
        {
          unsigned i = order[k];
          if (!todo[i])
            continue;

          todo[i] = false;

          // Update all the predecessors that changed on last turn.
          for (const auto& re : reverse.out(i))
          {
            size_t u = re.dst;
            size_t idx = u * n;

            for (unsigned v = 0; v < n; ++v)
            {
              // u doesn't simulate v
              if (!can_sim[idx + v])
                continue;

              if (!test_sim(u, v))
              {
                can_sim[idx + v] = false;
                todo[u] = true;
                has_changed = true;
              }
            }
          }
        }
      } while (has_changed);
    };

    std::vector<std::thread> ts;
    ts.reserve(nb_thread_ - 1);

    for (unsigned i = 0; i < nb_thread_ - 1; ++i)
      ts.emplace_back(std::thread(loop, i));

    loop(nb_thread_ - 1);

    for (unsigned i = 0; i < nb_thread_ - 1; ++i)
      ts[i].join();

    if constexpr(Cosimulation)
      {
        if (!ga.out(init).begin())
          {
            for (unsigned i = 0; i < n; ++i)
              {
                can_sim[i * n + init] = i == init;
                can_sim[init * n + i] = false;
              }
          }
        else
          for (unsigned i = 0; i < n; ++i)
            {
              // i doesn't simulate init
              can_sim[i * n + init] = i == init;
            }
      }

    std::vector<char> can_sim2(can_sim.begin(), can_sim.end());
    return can_sim2;
  }

  
/*

  template <typename ConstAutPtr, bool Cosimulation, bool Sba>
  auto reduce_sim<ConstAutPtr, Cosimulation, Sba>::run()
  {
    aut_ptr_t res = create_twa_from(original_);
    aut_ptr_t no_mark = create_twa_from(original_);
    unsigned init = original_->get_init_state_number();

    std::vector<char> can_sim;
    if constexpr(is_twa_graph)
      can_sim = compute_simulation_scc();
    else
      throw std::runtime_error("la calotte de tes morts");
    //can_sim = nb_thread_ ? compute_simulation_par2_1()
    //                                       : compute_simulation();

    size_t n = original_->num_states();
    std::vector<unsigned> equiv_states(n);

    // If the automaton is deterministic, there is no simple simulation only
    // bisimulation.
    bool is_deter = false;
    //TODO
    if constexpr(is_twa_graph)
      is_deter = is_deterministic(original_);

    // The number of states in the reduced automaton.
    // There is at least an initial state.
    equiv_states[0] = res->new_state();
    no_mark->new_state();

    std::vector<unsigned> old;
    old.reserve(n);
    old.push_back(0);

    // If two states bisimulate each other, they will be the same state in the
    // reduced automaton.
    for (size_t i = 1; i < n; ++i)
      {
        bool found = false;

        size_t j = 0;
        for (; j < i; ++j)
          {
            if (can_sim[i * n + j] && (is_deter || can_sim[j * n + i]))
              {
                equiv_states[i] = equiv_states[j];
                found = true;
                break;
              }
          }

        if (!found)
          {
            equiv_states[i] = res->new_state();
            no_mark->new_state();
            old.push_back(i);
          }
      }
    unsigned nr = res->num_states();

    const auto& ga = aut_->get_graph();

    // Test if the language recognized by taking e1 is included in e2 (in this
    // case e2 dominates e1).
    const auto dominates_edge = [&](const auto& e2)
      {
        return [&](const auto& e1) -> bool
          {
            if (Cosimulation && e2.dst == init && e1.dst != init)
              return false;

            if constexpr(Sba && Cosimulation)
              {
                if (!(this->acc_[e1.src]).subset(this->acc_[e2.src]))
                  return false;
              }
            else
              {
                if (!e1.acc.subset(e2.acc))
                  return false;
              }

            // e1.dst simulates e2.dst
            return can_sim[e2.dst * n + e1.dst]
              // if e2.dst also simulates e1.dst, the edge with the higher
              // index is the dominator (this is arbitrary, but without that
              // we would remove both edges)
              && (!can_sim[e1.dst * n + e2.dst]
                  || ga.index_of_edge(e1) > ga.index_of_edge(e2))
              // of course the condition of e2 should implies that of e1, but
              // this we test this last because it is slow.
              && this->cond_implies(e2, e1);
          };
      };

    const auto all_inf = original_->acc().get_acceptance()
      .used_inf_fin_sets().first;
    auto& gr = res->get_graph();
    auto& g_no_mark = no_mark->get_graph();

    for (unsigned i = 0; i < nr; ++i)
      {
        auto out = ga.out(old[i]);

        for (const auto& e : out)
          {
            // If the language recognized by taking e is include in the
            // language of an other edge, we don't want to add it.
            // If the automaton is deterministic, this cannot happen since no
            // simple simulation are possible.
            if (is_deter
                || std::none_of(out.begin(), out.end(), dominates_edge(e)))
              {
                if (Cosimulation)
                  gr.new_edge(equiv_states[e.dst],
                      i,
                      this->new_cond_from(e),
                      e.acc ^ all_inf);
                else
                  gr.new_edge(i,
                      equiv_states[e.dst],
                      this->new_cond_from(e),
                      e.acc ^ all_inf);

                g_no_mark.new_edge(i, 
                    equiv_states[e.dst],
                    this->new_cond_from(e),
                    acc_cond::mark_t());
              }
          }
      }

    res->set_init_state(equiv_states[init]);
    no_mark->set_init_state(equiv_states[init]);
    no_mark->merge_edges();

    //TODO adapt for twacube (need scc_info)
    if constexpr(is_twa_graph)
      {
        std::vector<unsigned> redirect(no_mark->num_states());
        std::iota(redirect.begin(), redirect.end(), 0);

        scc_info si_no_mark(no_mark, scc_info_options::NONE);
        unsigned nscc = si_no_mark.scc_count();

        // Same as in compute_simulation(), but since we are between two sccs, we
        // can ignore the colors.
        const auto test_sim = [&](size_t s1, size_t s2) -> bool
          {
            auto s_edges = no_mark->out(s1);
            auto d_edges = no_mark->out(s2);

            return std::all_of(s_edges.begin(), s_edges.end(),
              [&](const auto& s_edge) -> bool
                {
                  size_t idx = static_cast<size_t>(old[s_edge.dst]) * n;

                  return std::find_if(d_edges.begin(), d_edges.end(),
                    [&](const auto& d_edge) -> bool
                      {
                        if (!can_sim[idx + static_cast<size_t>(old[d_edge.dst])])
                          return false;
                      return this->cond_implies(s_edge, d_edge);
                      });
                });
          };

        // Attempt to merge trivial sccs.
        for (unsigned scc = 0; scc < nscc; ++scc)
          {
            if (!si_no_mark.is_trivial(scc))
              continue;

            unsigned s = si_no_mark.one_state_of(scc);

            for (unsigned i = 0; i < nr; ++i)
              {
                if (si_no_mark.reachable_state(i)
                    && !si_no_mark.is_trivial(si_no_mark.scc_of(i)))
                  {
                    if (test_sim(i, s) && test_sim(s, i))
                      {
                        can_sim[old[i] * n + old[s]] = true;
                        can_sim[old[s] * n + old[i]] = true;

                        if (Cosimulation)
                          redirect[i] = s;
                        else
                          redirect[s] = i;
                        break;
                      }
                  }
              }
          }

        for (auto& e: res->edges())
          e.dst = redirect[e.dst];
        res->set_init_state(redirect[res->get_init_state_number()]);
      }

    //TODO no prop yet for cube
    if constexpr(is_twa_graph)
    {
      if (!Sba && !Cosimulation && original_->prop_state_acc())
        {
          // common_in[i] is the set of acceptance set numbers
          // common to all incoming edges of state i.  Only edges
          // inside one SCC matter.
          //
          // ns = nr
          std::vector<acc_cond::mark_t> common_in(nr);
          scc_info si(res, scc_info_options::NONE);

          for (unsigned s = 0; s < nr; ++s)
            {
              unsigned s_scc = si.scc_of(s);
              bool first = true;
              for (auto& e: res->out(s))
                {
                  if (si.scc_of(e.dst) != s_scc)
                    continue;
                  if (first)
                    {
                      common_in[s] = e.acc;
                      first = false;
                    }
                  else
                    {
                      common_in[s] &= e.acc;
                    }
                }
            }
          for (auto& e : res->edges())
            e.acc = (e.acc - common_in[e.dst]) | common_in[e.src];
        }
    }

    res->merge_edges();

    if constexpr(is_twa_graph)
    {
      res->purge_unreachable_states();

      // FIXME if no change keep all original_ prop
      res->prop_copy(original_,
          { Sba,          // state-based acc
            true,         // weakness preserved,
            false, true,  // determinism improved
            true,         // completeness preserved
            true,         // stutter inv.
          });
    }

    return res;
  }

  twa_graph_ptr reduce_direct_sim(const const_twa_graph_ptr& aut)
  {
    // The automaton must not have dead or unreachable states.
    reduce_sim<const_twa_graph_ptr, false, false> r(scc_filter(aut));
    return r.run();
  }

  twacube_ptr reduce_direct_sim(const const_twacube_ptr& aut, unsigned nb_thread)
  {
    // The automaton must not have dead or unreachable states.
    // FIXME
    reduce_sim<const_twacube_ptr, false, false> r(aut, nb_thread);
    return r.run();
  }

  twa_graph_ptr reduce_direct_sim_sba(const const_twa_graph_ptr& aut)
  {
    // The automaton must not have dead or unreachable states.
    reduce_sim<const_twa_graph_ptr, false, true> r(scc_filter_states(aut));
    return r.run();
  }

  twa_graph_ptr reduce_direct_cosim(const const_twa_graph_ptr& aut)
  {
    // The automaton must not have dead or unreachable states.
    reduce_sim<const_twa_graph_ptr, true, false> r(scc_filter(aut));
    return r.run();
  }

  twacube_ptr reduce_direct_cosim(const const_twacube_ptr& aut)
  {
    // The automaton must not have dead or unreachable states.
    // FIXME
    reduce_sim<const_twacube_ptr, true, false> r(aut);
    return r.run();
  }

  twa_graph_ptr reduce_direct_cosim_sba(const const_twa_graph_ptr& aut)
  {
    // The automaton must not have dead or unreachable states.
    reduce_sim<const_twa_graph_ptr, true, true> r(scc_filter_states(aut));
    return r.run();
  }

  template <typename ConstAutPtr, bool Sba>
  auto reduce_iterated_(const ConstAutPtr& aut)
  {
    unsigned last_states = aut->num_states();
    unsigned last_edges = aut->num_edges();

    ConstAutPtr a;
    //FIXME
    if constexpr(std::is_same<ConstAutPtr, const_twa_graph_ptr>::value)
      a = Sba ? scc_filter_states(aut) : scc_filter(aut);
    else
      a = aut;

    reduce_sim<ConstAutPtr, false, Sba> r(a);
    auto res = r.run();

    bool cosim = true;
    do
      {
        if constexpr(std::is_same<ConstAutPtr, const_twa_graph_ptr>::value)
          if (is_deterministic(res))
            break;

        last_states = res->num_states();
        last_edges = res->num_edges();

        if (cosim)
          {
            reduce_sim<ConstAutPtr, true, Sba> r(res);
            res = r.run();
          }
        else
          {
            reduce_sim<ConstAutPtr, false, Sba> r(res);
            res = r.run();
          }

        cosim = !cosim;

      }
    while (last_states > res->num_states() || last_edges > res->num_edges());

    return res;
  }

  twa_graph_ptr reduce_iterated(const const_twa_graph_ptr& aut)
  {
    return reduce_iterated_<const_twa_graph_ptr, false>(aut);
  }

  twacube_ptr reduce_iterated(const const_twacube_ptr& aut)
  {
    // The automaton must not have dead or unreachable states.
    // FIXME
    return reduce_iterated_<const_twacube_ptr, false>(aut);
  }

  twa_graph_ptr reduce_iterated_sba(const const_twa_graph_ptr& aut)
  {
    return reduce_iterated_<const_twa_graph_ptr, true>(aut);
  }
} // End namespace spot.
*/
