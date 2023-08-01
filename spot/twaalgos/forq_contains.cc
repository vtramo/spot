
#include "config.h"
#include <spot/twaalgos/split.hh>
#include "forq_contains.hh"

#include <spot/twaalgos/complement.hh>
#include <spot/twaalgos/contains.hh>
#include <spot/twaalgos/contains.hh>
#include <spot/twaalgos/product.hh>
#include <spot/twaalgos/product.hh>
#include <spot/twaalgos/word.hh>
#include <spot/twaalgos/hoa.hh>
#include <spot/misc/bddlt.hh>
#include <spot/twa/twagraph.hh>
#include <spot/twa/bddprint.hh>
#include <spot/twa/bdddict.hh>
#include <spot/misc/bddlt.hh>
#include <spot/twa/twa.hh>
#include <spot/twa/acc.hh>
#include <unordered_map>
#include <unordered_set>
#include <type_traits>
#include <iterator>
#include <optional>
#include <vector>
#include <string>
#include <memory>
#include <array>

namespace spot::forq
{
	// Wrapper to represent the edges along a given edge in our automaton.
	// As a result, we can abstract the bdds usually used to represent the edges as a set of symbols.
	class symbol_set
	{
		friend class ::std::hash<symbol_set>;
	public:
		symbol_set(bdd symbols);
		static symbol_set empty();

		bool operator==(symbol_set const& other) const;
		bool operator!=(symbol_set const& other) const;
		symbol_set operator&(symbol_set const& other) const;
		symbol_set operator|(symbol_set const& other) const;
		symbol_set operator!() const;

		bool contains(symbol_set const& other) const;
		bdd const& data() const;	
		size_t size() const;
	
		std::string to_string(spot::bdd_dict_ptr const& dict) const; 
		
	private:
		symbol_set() = default;
		bdd symbols;
	};
}

namespace std 
{
	template<>
	struct hash<::spot::forq::symbol_set> 
	{
		size_t operator()(::spot::forq::symbol_set const& instance) const noexcept {
			return ::spot::bdd_hash{}(instance.symbols);
		}
	};
	
	template <>
    class hash<std::pair<::spot::forq::symbol_set, ::spot::forq::symbol_set>>{
    public :
        size_t operator()(pair<::spot::forq::symbol_set, ::spot::forq::symbol_set> const& x) const noexcept
        {
            size_t first_hash = std::hash<::spot::forq::symbol_set>()(x.first);
			size_t second_hash = std::hash<::spot::forq::symbol_set>()(x.second);
			first_hash ^= second_hash + 0x9e3779b9 + (first_hash << 6) + (first_hash >> 2);
            return  first_hash;
        }
    };
}

namespace spot::forq 
{
	class word 
	{
		friend class ::std::hash<word>;
	public:
		word(symbol_set sym);
		static word empty();

		word operator+(symbol_set const& other) const;
		bool operator==(word const& other) const;

		auto begin() const { return symbols.begin(); }
		auto end() const { return symbols.end(); }

		std::string to_string(spot::bdd_dict_ptr const& dict) const; 

	private:
		word() = default;
		std::vector<symbol_set> symbols;
	};
}


namespace std 
{
	template<>
	struct hash<::spot::forq::word> 
	{
		size_t operator()(::spot::forq::word const& instance) const noexcept {
			std::size_t seed = instance.symbols.size();
			for(auto const& sym : instance.symbols) {
				size_t x = std::hash<::spot::forq::symbol_set>{}(sym);
				x = ((x >> 16) ^ x) * 0x45d9f3b;
				x = ((x >> 16) ^ x) * 0x45d9f3b;
				x = (x >> 16) ^ x;
				seed ^= x + 0x9e3779b9 + (seed << 6) + (seed >> 2);
			}
			return seed;
		}
	};
}

namespace spot::forq 
{
    using state = size_t;
    using edge = std::pair<state, state>;
    using const_graph = ::spot::const_twa_graph_ptr;

    struct final_edge 
    {
        symbol_set acc;
        state src, dst;
        bool operator==(final_edge const& other) const {
            return acc == other.acc && src == other.src && dst == other.dst;
        }
        struct hash 
        {
            size_t operator()(::spot::forq::final_edge const& other) const noexcept {
                size_t lhs = std::hash<size_t>{}(other.src);
                lhs ^= std::hash<size_t>{}(other.dst) + 0x9e3779b9 + (lhs << 6) + (lhs >> 2);
                return lhs;
            }
        };
    };
    
	struct forq_context 
    {
        using ipost_calculations = std::vector<std::unordered_map<symbol_set, std::optional<std::set<state>>>>;
    public:
		struct {
			const_graph aut;
            std::unordered_set<final_edge, final_edge::hash> final_edges;
            std::vector<std::vector<std::pair<symbol_set, state>>> outgoing;
		} A, B;

        struct {
            ipost_calculations precomputed_ipost;
        } mutable cache;
	};

    namespace util 
    {
        std::vector<state> get_final_states(const_graph const& automata);
        forq_context create_forq_context(const_graph const& A, const_graph const& B);
        ::spot::twa_word_ptr as_twa_word_ptr(
            ::spot::bdd_dict_ptr const&, 
            ::spot::forq::word const& stem, 
            ::spot::forq::word const& cycle
        );
    }

// concepts would be nice 
#define TEMPLATE_QUASI_TYPE(x) typename x, typename = std::enable_if_t<std::is_base_of_v<quasi_order<x>, x>>

	template<typename T>
	struct quasi_order 
	{
		virtual bool operator<=(T const&) const = 0;
	};

	// State_entry's hash and equality operator should only depend on the actual word, since the 
	// actual set is what's used to compare it, and is auxillary. Improvement on original?
	template<typename T>
	struct state_entry {
		T set;
		word w; 
		bool operator==(state_entry<T> const& other) const { return w == other.w; }
	};
}

namespace std 
{
	template<typename T>
	struct hash<::spot::forq::state_entry<T>> 
	{
		size_t operator()(::spot::forq::state_entry<T> const& other) const noexcept {
			return std::hash<::spot::forq::word>{}(other.w); 
		}
	};	
}

namespace spot::forq 
{
	template<TEMPLATE_QUASI_TYPE(quasi_type)> 
	class post_variable 
	{
		using state_entry_t = state_entry<quasi_type>;
		using state_set_t = std::unordered_set<std::shared_ptr<const state_entry_t>>;
	public:
		bool empty() const { return state_vector.empty(); }
		//state_set_t& operator[](state s) { return state_vector[s]; }
		state_set_t const& operator[](state s) const { return state_vector[s]; }

		void add(state s, std::shared_ptr<const state_entry_t> entry) {
			state_vector[s].insert(std::move(entry));
		}

		bool add_if_min(state s, std::shared_ptr<const state_entry_t> const& entry) {
			state_set_t& old_state_set = state_vector[s];
			for(auto it = old_state_set.begin(); it != old_state_set.end();) {
				if((*it)->set <= entry->set) return false;
				if(entry->set <= (*it)->set) it = old_state_set.erase(it);
				else it++;
			}
			old_state_set.insert(entry);
			return true;
		}

		bool add_if_max(state s, std::shared_ptr<const state_entry_t> const& entry) {
			state_set_t& old_state_set = state_vector[s];
			for(auto it = old_state_set.begin(); it != old_state_set.end();) {
				if(entry->set <= (*it)->set) return false;
				if((*it)->set <= entry->set) it = old_state_set.erase(it);
				else it++;
			}
			old_state_set.insert(entry);
			return true;
		}

		auto begin() { return state_vector.begin(); }
		auto begin() const { return state_vector.begin(); }
		auto end() { return state_vector.end(); }
		auto end() const { return state_vector.end(); }

		std::string to_string(spot::bdd_dict_ptr const& dict) const {
			std::stringstream ss;
			ss << "basis: {\n";
			for(auto& [s, set] : state_vector) {
				ss << "(state:" << s << "={\n";
				for(auto& entry : set) {
					ss << "( word:";
					if(entry->w.size() == 0) {ss<<"EMPTY";}
					else {
						ss << entry->w.to_string(dict);
					}
					ss << ", set: " << entry->set << "),\n";
				}
				ss << "}),\n";
			}
			ss << "}\n";
			return ss.str();
		}
	private:
		mutable std::unordered_map<state, state_set_t> state_vector;
	};

	struct state_set : quasi_order<state_set> 
	{
	public:
		
		state_set(bool reversed);
		state_set(state single_state, bool reversed);

		void insert(state s);
		size_t size() const;
		state_set& operator+=(std::set<state> const& other);
		bool operator<=(state_set const& other) const override;

		auto begin() { return set.begin(); }
		auto begin() const { return set.begin(); }
		auto end() { return set.end(); }
		auto end() const { return set.end(); }

		std::string to_string() const;

	private:
		std::set<state> set;
		bool reversed;
	};

	template<TEMPLATE_QUASI_TYPE(quasi_type)> class post_base 
	{
		using state_entry_t = state_entry<quasi_type>;
		using state_set_t = std::unordered_set<std::shared_ptr<const state_entry_t>>;
	public:
		post_base(forq_context const& context) : context(context) {}
		state_set_t const& operator[](state s) const { return basis[s]; }
		std::string to_string(spot::bdd_dict_ptr dict) const { return basis.to_string(dict); }

	protected:
		forq_context const& context;
		post_variable<quasi_type> basis;
		void evaluate(post_variable<quasi_type> initial_updates);

	private:
	 	// gets new cxt or tgt based on current state
		virtual quasi_type post(quasi_type const& current_state, symbol_set const& edge_expr) const = 0;

		// adds or removes elements from basis, in order to form a proper basis
		virtual bool add_extreme(state current_state, std::shared_ptr<const state_entry_t> const& entry) = 0;

		// Uses updates in order to iteratively construct the basis
		bool apply_step(post_variable<quasi_type>& updates);
	};

    template<typename quasi_type, typename _>
    void post_base<quasi_type, _>::evaluate(post_variable<quasi_type> initial_updates) {
        while(apply_step(initial_updates));
    }

    template<typename quasi_type, typename _>
    bool post_base<quasi_type, _>::apply_step(post_variable<quasi_type>& updates) 
    {
        post_variable<quasi_type> buffer;

        // Each state has a set of words, where each word has associated cxt or tgt in order to compare, so
        // state_set is { <cxt, word>, <cxt, word>, <cxt, word> } 
        for (auto& [from_a, word_set] : updates) 
        {
            // Look at all the successors for a given state (.p), in the form (symbol, successors)
            for (auto& word_pair : word_set) 
            {   
                auto& [quazi_b_set, current_word] = *word_pair;
                
                for (auto& [sym_a, succ_a] : context.A.outgoing[from_a])  
                {
                    {
                        auto new_entry = std::make_shared<const state_entry_t>(state_entry_t{ 
                            post(quazi_b_set, sym_a), current_word + sym_a 
                        });
                        if (add_extreme(succ_a, new_entry)) {
                            buffer.add(succ_a, new_entry);
                        }
                    }
                }
            }
        }

        updates = std::move(buffer);
        return !updates.empty();
    }

	class post_i : public post_base<state_set> 
	{
		using entry_ptr = std::shared_ptr<const state_entry<state_set>>;
	public:
		static post_i create(forq_context const& context, state A_initial, state B_initial);
		static post_i create_reversed(forq_context const& context, state A_initial, state B_initial);
		using post_base<state_set>::operator[];
	private:
		post_i(forq_context const& context, state A_initial, state B_initial, bool reversed);

		state_set post(state_set const& current, symbol_set const& sym) const override;
		bool add_extreme(state A_initial, entry_ptr const& entry) override;

		bool is_reversed;
	};

	class context_set : quasi_order<context_set>
	{
	public:
		context_set() = default;

		context_set& operator+=(context_set const& other);
		bool operator<=(context_set const& other) const override;

		void add(state initial, std::set<std::pair<state, bool>> const& other);
		bool relevance_test(state_set const& set) const;
		std::string to_string() const;

		template<typename Callable>
		void iterate(Callable callable) const {
			for(auto& [state1, set] : states) {
				for(auto [state2, flag] : set)
					callable(state1, state2, flag);
			} 
		}

	private:
		mutable std::map<state, std::set<std::pair<state, bool>>> states;
	};

	class post_f : public post_base<context_set> 
	{
		using entry_ptr = std::shared_ptr<const state_entry<context_set>>;
	public:
		static post_f create(forq_context const& context, state A_initial, state_set const& b_tgt);
		using post_base<context_set>::operator[];

	private:
		post_f(forq_context const& context, state A_initial, state_set const& B_initial);

		context_set post(context_set const& current, symbol_set const& sym) const override;
		bool add_extreme(state A_initial, entry_ptr const& entry) override;

		context_set compute_cxt_b(state_set const& b_tgt, symbol_set const& sym) const;
		bool is_final_edge(symbol_set const& sym, state src, state dst) const;

		std::set<std::pair<state, bool>>const get_post_set(bool already_accepting, symbol_set const& a_sym, state from_b) const;
	};

	static forq_status valid_automata(const_graph const& A, const_graph const& B, ::spot::forq_result* result) 
	{
		if(!result) {
			return forq_status::FORQ_INVALID_RESULT_PTR;
		}
		if(!A || !B) {
			return forq_status::FORQ_INVALID_INPUT_BA;
		}

		const auto buchi_acceptance = spot::acc_cond::acc_code::buchi();
		auto accept_A = A->get_acceptance();
		auto accept_B = B->get_acceptance();
			  
		if (accept_A != buchi_acceptance || accept_B != buchi_acceptance) {
			return forq_status::FORQ_INVALID_AC_COND;
		}
		if (A->get_dict() != B->get_dict()) {
			return forq_status::FORQ_INCOMPATIBLE_DICTS;
		}
		if (A->ap() != B->ap()) {
			return forq_status::FORQ_INCOMPATIBLE_AP;
		}
		return forq_status::FORQ_OKAY;
	}

	static ::spot::forq_status create_result(::spot::forq_result* result, bool included, ::spot::twa_word_ptr counter_example = {}) 
	{
		result->included 		= included;
		result->counter_example = std::move(counter_example); 
		return forq_status::FORQ_OKAY;
	}

	struct forq_setup 
	{
		forq::forq_context context;
		forq::post_i post_i_forward;
		forq::post_i post_i_reverse;
	};

	static forq_setup create_forq_setup(forq::const_graph A, forq::const_graph B) 
	{
		auto context = forq::util::create_forq_context(A, B);
		auto A_initial = A->get_init_state_number(),
			 B_initial = B->get_init_state_number();

		auto post_i_forward = forq::post_i::create(context, A_initial, B_initial);
		auto post_i_reverse = forq::post_i::create_reversed(context, A_initial, B_initial);

		return forq_setup{
			context, post_i_forward, post_i_reverse
		};
	}

	class final_state_result 
	{
	public:
		static final_state_result failure(spot::twa_word_ptr counter_example) {
			return final_state_result(std::move(counter_example));
		}
		static final_state_result success() { return final_state_result(nullptr); }

		bool should_continue() const {
			return counter_example == nullptr;
		}
		spot::twa_word_ptr const& get_counter_example() const {
			return counter_example;
		}
	private:
		final_state_result(spot::twa_word_ptr counter_example) 
			: counter_example(std::move(counter_example)) {}
		spot::twa_word_ptr counter_example = nullptr;
	};

	static final_state_result run_from_final_state(forq::state src, forq_setup const& setup) 
	{		
		auto& context = setup.context;
		auto shared_dict = context.A.aut->get_dict();
		for (auto& w_ptr : setup.post_i_reverse[src]) 
		{	
			auto& [W, word_of_w] = *w_ptr;
			auto new_post_f = forq::post_f::create(context, src, W);

			for (auto& v_ptr : new_post_f[src]) 
			{	
				auto& [V, word_of_v] = *v_ptr;
				if (!V.relevance_test(W)) continue;
				for (auto& u_ptr : setup.post_i_forward[src]) 
				{
					auto& [U, word_of_u] = *u_ptr;
					if (U <= W)
					{
						auto current_word = forq::util::as_twa_word_ptr(shared_dict, word_of_u, word_of_v);
						if(!context.B.aut->intersects(current_word->as_automaton())) 
							return final_state_result::failure(std::move(current_word));
					}
				}
			}
		}
		return final_state_result::success();
	}
}

namespace spot 
{
	forq_status contains_forq(forq::const_graph const& A, forq::const_graph const& B, forq_result* result)
	{
		if (auto rc = forq::valid_automata(A, B, result); rc != forq_status::FORQ_OKAY) return rc;
		forq::forq_setup setup = forq::create_forq_setup(A, B);

		for (auto src : forq::util::get_final_states(A)) 
		{
			auto final_state_result = forq::run_from_final_state(src, setup);
			if(!final_state_result.should_continue()){
				return forq::create_result(result, false, final_state_result.get_counter_example());
			}
		}
		return forq::create_result(result, true);
	}

	bool contains_forq(forq::const_graph const& A, forq::const_graph const& B) 
	{
		forq_result result;
		if(auto rc = contains_forq(A, B, &result); rc != forq_status::FORQ_OKAY) {
			throw std::runtime_error(forq_status_message(rc));
		}
		return result.included;
	}

	const char* forq_status_message(forq_status status) {
		switch(status) {
			case forq_status::FORQ_OKAY:
				return "Forq was able to properly run on the two buchi automata.";
			case forq_status::FORQ_INVALID_AC_COND:
				return "Forq only operates on automata with buchi acceptance conditions.";
			case forq_status::FORQ_INCOMPATIBLE_DICTS:
				return "The two input graphs must utilize the same twa_dict.";
			case forq_status::FORQ_INCOMPATIBLE_AP:
				return "The two input graphs must utilize the same set of atomic propositions defined in their shared twa_dict.";
			case forq_status::FORQ_INVALID_INPUT_BA:
				return "One of the two buchi automata passed in was a nullptr.";
			case forq_status::FORQ_INVALID_RESULT_PTR:
				return "The result pointer passed in was a nullptr.";
			default:
				return "Unknown Forq Status Code.";
		}
	}
}

namespace spot::forq::util 
{
	// In spot, there exists acceptance sets and an edge can be part of any number of them.
	// However, forq only operates on automata with a single acceptance set i.e {0}. 
	static bool is_final_edge(::spot::twa_graph::edge_storage_t const& edge) 
	{
		return edge.acc == ::spot::acc_cond::mark_t({0,});
	}

	// We consider any state as final if it's the source of an edge that's considered accepting
	std::vector<state> get_final_states(const_graph const& automata) 
	{
		std::unordered_set<state> states;
		for(auto& edge_storage : automata->edges())
		{
			if (is_final_edge(edge_storage)) 
			{
				states.insert(edge_storage.src); 
			}
		}
		return std::vector<state>(states.begin(), states.end());
	}

	static std::unordered_set<final_edge, final_edge::hash> get_final_edges(const_graph const& automata) 
	{
		std::unordered_set<final_edge, final_edge::hash> edges;
		for(auto& edge_storage : automata->edges())
		{
			if (is_final_edge(edge_storage)) 
			{
				edges.insert(final_edge{symbol_set(edge_storage.cond), edge_storage.src, edge_storage.dst});
			}
		}
		return edges;
	}

	// Create a fast query structure for determining the outgoing states of a given state.
	// This structure is indexed by the source node, which returns a list of outgoing edges represented
	// as a pair: [set of symbols that allow the transition, the destination state]
	static std::vector<std::vector<std::pair<symbol_set, state>>> generate_outgoing_states(const_graph const& A) 
	{
		std::vector<std::vector<std::pair<symbol_set, state>>> all_states; 
		all_states.resize(A->num_states());
		for(auto& edge_storage : A->edges()) 
		{
			all_states[edge_storage.src].emplace_back(symbol_set(edge_storage.cond), edge_storage.dst);
		}
		return all_states;
	}

	// Create a list of bdds, where each corresponds to an edge in B
	static std::vector<bdd> create_edge_splitting_basis(const_graph const& B) 
	{
		auto edges = B->edges();
		std::unordered_set<bdd, ::spot::bdd_hash> out;
		std::transform(edges.begin(), edges.end(), std::inserter(out, out.begin()), 
			[](auto& edge){ return edge.cond; }
		);
		return std::vector<bdd>(out.begin(), out.end());
	}

	forq_context create_forq_context(const_graph const& A, const_graph const& B) 
	{
		forq_context retval;
		retval.B.aut = B;
		retval.B.outgoing = util::generate_outgoing_states(B);
		retval.B.final_edges = get_final_edges(B);

		retval.A.aut = split_edges(A, create_edge_splitting_basis(B));
		retval.A.outgoing = util::generate_outgoing_states(retval.A.aut);
		retval.A.final_edges = get_final_edges(retval.A.aut);
		retval.cache.precomputed_ipost.resize(B->num_states());
		return retval;
	}

	::spot::twa_word_ptr as_twa_word_ptr(spot::bdd_dict_ptr const& dict, ::spot::forq::word const& stem, ::spot::forq::word const& cycle) 
	{
		auto new_word = ::spot::make_twa_word(dict);
		for(auto& symbol : stem) new_word->prefix.push_back(symbol.data());
		for(auto& symbol : cycle) new_word->cycle.push_back(symbol.data());
		return new_word;
	}
}


namespace spot::forq
{    
	namespace detail 
	{
		static size_t bdd_size;
		static void calculate_number_of_symbols_in_bdd_handler([[maybe_unused]] char* varset, [[maybe_unused]] int size) {
			bdd_size++;
		}
        static size_t calculate_number_of_symbols_in_bdd(bdd b) 
        {
            detail::bdd_size = 0;
            bdd_allsat(b, detail::calculate_number_of_symbols_in_bdd_handler);
            return detail::bdd_size;
        }
	}

    symbol_set symbol_set::empty() { return symbol_set(); }
    symbol_set::symbol_set(bdd symbols) : symbols(symbols) {}

    bool symbol_set::operator==(symbol_set const& other) const { return other.symbols == symbols; }
    bool symbol_set::operator!=(symbol_set const& other) const { return other.symbols != symbols; }
    symbol_set symbol_set::operator&(symbol_set const& other) const { return symbol_set(other.symbols & symbols); }
    symbol_set symbol_set::operator|(symbol_set const& other) const { return symbol_set(other.symbols | symbols); }
    symbol_set symbol_set::operator!() const { return symbol_set(!symbols); }

    bool symbol_set::contains(symbol_set const& other) const { 
        //return !bdd_have_common_assignment(!other.symbols, symbols);
        return other.symbols == (other.symbols & symbols); 
    }
    bdd const& symbol_set::data() const { return symbols; }
    size_t symbol_set::size() const { return detail::calculate_number_of_symbols_in_bdd(symbols); }

    std::string symbol_set::to_string(spot::bdd_dict_ptr const& dict) const {
        std::stringstream ss;
        spot::bdd_print_formula(ss, dict, symbols);
        return ss.str();
    }

    word::word(symbol_set sym) { 
        symbols.emplace_back(std::move(sym)); 
    }

    word word::empty() { return word(); }

    word word::operator+(symbol_set const& other) const 
    { 
        auto temp = *this;
        if(temp.symbols.size() == 1 && temp.symbols.front() == symbol_set::empty()) {
            temp.symbols.front() = other;
        }
        else {
            temp.symbols.push_back(other);
        }
        return temp;
    }
    std::string word::to_string(spot::bdd_dict_ptr const& dict) const
    {
        std::string retval;
        for(size_t i = 0; i < symbols.size(); i++) { 
            retval += symbols[i].to_string(dict);
            if(i != symbols.size() - 1) retval.push_back(';');
        }
        return retval;
    }
    bool word::operator==(word const& other) const { 
        return symbols == other.symbols; 
    }
	
	post_f post_f::create(forq_context const& context, state a_initial, state_set const& b_tgt) {
		return post_f(context, a_initial, b_tgt);
	}

	post_f::post_f(forq_context const& context, state a_initial, state_set const& b_tgt)
		: post_base(context)
	{
		// This is different from post_i initialization, as we have a lot more starting states
		// to check (all states of b_tgt), and additionally, we're looking at the successors of
		// these nodes, as we want to determine the period and not include any of the stem.
		post_variable<context_set> updates;
		for (auto& [sym_a, dst] : context.A.outgoing[a_initial]) 
		{
			auto it = std::find_if(context.A.final_edges.begin(), context.A.final_edges.end(), 
			[&sym_a = sym_a, a_initial, dst=dst](auto& other) {
				return other.acc.contains(sym_a) && other.src == a_initial && other.dst == dst;
			});
			
			if(it != context.A.final_edges.end())
			{
				auto initial = std::make_shared<const state_entry<context_set>>(
					state_entry<context_set>{compute_cxt_b(b_tgt, sym_a), word(sym_a)}
				);
				updates.add_if_min(dst, initial);
				basis  .add_if_min(dst, initial);
			}
		}
		evaluate(std::move(updates));
	}
	
	std::set<std::pair<state, bool>>const post_f::get_post_set(bool already_accepting, symbol_set const& a_sym, state from_b) const 
	{
		auto new_set = std::set<std::pair<state, bool>>{};
		for(auto& [sym, dst] : context.B.outgoing[from_b]) {
			if(sym.contains(a_sym))
			{
				new_set.emplace(std::make_pair(dst, false));
				if(already_accepting || is_final_edge(sym, from_b, dst))
					new_set.emplace(std::make_pair(dst, true));
			}
		}
		return new_set;	
	}

	bool post_f::is_final_edge(symbol_set const& sym, state src, state dst) const {
		return context.B.final_edges.find(final_edge{sym, src, dst}) != context.B.final_edges.end();
	}
	
	context_set post_f::compute_cxt_b(state_set const& b_tgt, symbol_set const& a_sym) const 
	{
		// Algorithm deviation
		context_set context_b;
		for (auto from_b : b_tgt) 
		{
			auto post_set = get_post_set(false, a_sym, from_b);
			context_b.add(from_b, std::move(post_set));
		}
		return context_b;
	}

	context_set post_f::post(context_set const& current, symbol_set const& a_sym) const
	{
		context_set post_b;
		current.iterate([&](state init_b, state from_b, bool already_accepting) 
		{
			auto post_set = get_post_set(already_accepting, a_sym, from_b);
			post_b.add(init_b, std::move(post_set));
		});
		return post_b;
	}

	bool post_f::add_extreme(state a_initial, entry_ptr const& entry)
	{
		return basis.add_if_min(a_initial, entry);
	}

	post_i post_i::create(forq_context const& context, state A_initial, state B_initial)
	{
		return post_i(context, std::move(A_initial), B_initial, false);
	}

	post_i post_i::create_reversed(forq_context const&  context, state A_initial, state B_initial)
	{
		return post_i(context, std::move(A_initial), B_initial, true);
	}

	post_i::post_i(forq_context const& context, state A_initial, state B_initial, bool reversed)
		: post_base(context), is_reversed(reversed)
	{	
		post_variable<state_set> updates;
		auto initial = std::make_shared<const state_entry<state_set>>(
			state_entry<state_set>{ 
				state_set{B_initial, reversed}, 
				word::empty() 
			}
		);
		updates.add(A_initial, initial);
		basis  .add(A_initial, initial);
		evaluate(std::move(updates));
	}

	state_set post_i::post(state_set const& current, symbol_set const& a_sym) const
	{
		// Algorithm deviation
		// Take current Tgt_B(w) and return Tgt_B(w + sym)
		state_set post_b{is_reversed};
		for (state from_b : current) {
			auto& precomputed = context.cache.precomputed_ipost[from_b][a_sym];
			if(!precomputed.has_value()){
				std::set<state> temp;
				for(auto& [sym, dst] : context.B.outgoing[from_b]) {
					// If there exists overlap between the two, then there exists some symbols
					// within a_sym that can bring us to the new state dst
					if(sym.contains(a_sym)) 
					{
						temp.insert(dst);
					}
				}
				precomputed = std::move(temp);
			}
			post_b += precomputed.value();
		}
		return post_b;
	}

	bool post_i::add_extreme(state A_initial, entry_ptr const& entry)
	{
		if (is_reversed) {
			return basis.add_if_max(A_initial, entry);
		}
		else {
			return basis.add_if_min(A_initial, entry);
		}
	}

	static bool operator<=(std::set<std::pair<state, bool>> const& f, std::set<std::pair<state, bool>> const& s) 
	{
		return std::includes(s.begin(), s.end(), f.begin(), f.end());
	}

	static bool operator<=(std::set<std::pair<state, bool>> const& f, state_set const& set) 
	{
		if (set.size() < f.size()) return false;
		auto first1 = set.begin(), last1 = set.end();
		auto first2 = f.begin(), last2 = f.begin();

		for (; first2 != last2; ++first1)
    	{
        	if (first1 == last1 || first2->first < *first1)
            	return false;
        	if (first2->first == *first1) {
            	++first2;
			}
		}
		return true;
	}
	
	void context_set::add(state initial, std::set<std::pair<state, bool>> const& other)
	{
		states[initial].insert(other.begin(), other.end());
	}
	
	context_set& context_set::operator+=(context_set const& other) 
	{
		for(auto& [state1, set] : other.states) {
			states[state1].insert(set.begin(), set.end());
		} 
		return *this;
	}

	bool context_set::relevance_test(state_set const& W) const 
	{
		for(auto& [s1, quazi] : states) {
			if(!(quazi <= W)) return false;
		}
		return true;
	}

	bool context_set::operator<=(context_set const& other) const 
	{
		for(auto& [s, set] : states) {
			if(!(set <= other.states[s])) return false;
		}
		return true;

		if (other.states.size() != states.size()) return false;
		auto first1 = other.states.begin(), last1 = other.states.end();
		auto first2 = states.begin(), last2 = states.begin();

		for (; first2 != last2; ++first1)
    	{
        	if (first1 == last1 || first2->first < first1->first)
            	return false;
        	if (first2->first == first1->first) {
				if(!(first2->second <= first1->second)) 
					return false;
            	++first2;
			}
		}
		return true;
	}

	std::string context_set::to_string() const 
	{
		std::string retval = "{";
		iterate([&](auto s1,auto s2,auto f) {
			retval.push_back('(');
			retval.append(std::to_string(s1));
			retval.push_back(',');
			retval.append(std::to_string(s2));
			retval.push_back(',');
			retval.append(f ? "true" : "false");
			retval.append("), ");
		}); 
		retval.pop_back();
		retval.pop_back();
		retval += '}';
		return retval;
	}

	state_set::state_set(state single_state, bool reversed) : set(std::set<state>{single_state}), reversed(reversed) {}
	state_set::state_set(bool reversed) : reversed(reversed) {}

	void state_set::insert(state s)
	{
		set.insert(s);
	}

	size_t state_set::size() const {
		return set.size();
	}

	state_set& state_set::operator+=(std::set<state> const& other) 
	{
		set.insert(other.begin(), other.end());
		return *this;
	}

	std::string state_set::to_string() const 
	{
		std::string retval = "{";
		for(auto s : set) {
			retval.append(std::to_string(s));
			retval.append(", ");
		}
		retval.pop_back(); retval.pop_back();
		return retval;
	}

	bool state_set::operator<=(state_set const& other) const 
	{
		// determines if the "this" set is a subset of "other" set
		if(other.set.size() < this->set.size()) return false;
		if(reversed) {
			return std::includes(other.set.rbegin(), other.set.rend(), this->set.rbegin(), this->set.rend(), std::greater{});
		}
		else{
			return std::includes(other.begin(), other.end(), this->begin(), this->end());
		}
	}
}
