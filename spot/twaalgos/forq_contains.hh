
#pragma once
#include <spot/twaalgos/hoa.hh>
#include <spot/twaalgos/word.hh>

namespace spot
{	
	enum class forq_status {
		FORQ_OKAY, 					// The forq works as expected
		FORQ_INVALID_AC_COND, 		// The automata passed do not use buchi acceptance conditions
		FORQ_INCOMPATIBLE_DICTS,	// The two automata are using different bdd_dict objects
		FORQ_INCOMPATIBLE_AP,		// The two automata are using different atomic propositions
		FORQ_INVALID_INPUT_BA,		// The two automata passed are nullptrs and are invalid
		FORQ_INVALID_RESULT_PTR		// The pointer forq_result, that was passed into function contains_forq, cannot be nullptr
	};

	struct forq_result 
	{
		bool included;						// Whether language of graph A is included in B
		spot::twa_word_ptr counter_example; // If the language of graph A is not included in B, a counter example is provided
	};

	// Return the status of language containment algorithm. 
	//If FORQ_OKAY is returned, the result is properly updated in forq_result* result.
	// forq_result::included is true, if the left argument is within that of the right argument
	forq_status contains_forq(spot::const_twa_graph_ptr, spot::const_twa_graph_ptr, forq_result* result);

	// Returns a human-readable string given a forq_status, which can be aquired through a call to contains_forq
	const char* forq_status_message(forq_status status);
}