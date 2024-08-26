#ifndef SEARCH_ALGORITHMS_EAGER_SEARCH_H
#define SEARCH_ALGORITHMS_EAGER_SEARCH_H

#include "../search_algorithm.h"

#include <memory>
#include <vector>


namespace plugins {
class Feature;
}

struct sat_capsule;

namespace sat_search {

struct AxiomSCC{
	std::vector<int> variables;
	bool sizeOne = false;
	bool isOfImplicationType = false;
	bool isDependentOnOneVariableInternally = false;
	int dependingVariable = false;


	bool fullComputationRequired = false;
	int numberOfAxiomLayers;

	// preprocessing information implications
	std::vector<std::vector<int>> directTransitiveImplications;
	std::vector<std::vector<int>> directTransitiveCauses;

	// preprocessing information guarded implications (i.e. ones that depend on a variable value)
	std::vector<std::vector<std::vector<int>>> guardedTransitiveImplications;
	std::vector<std::vector<std::vector<int>>> guardedTransitiveCauses;
};

class SATSearch : public SearchAlgorithm {
	int planLength;
	int currentLength;

	// index: timestep -> variable -> value
	std::vector<std::vector<std::vector<int>>> fact_variables;
	// index: timestep -> operator 
	std::vector<std::vector<int>> operator_variables;
	int get_fact_var(int time, FactProxy fact);
	
	// index: timestep -> variable
	std::vector<std::vector<std::vector<int>>> axiom_variables;
	int get_axiom_var(int time, int layer, FactProxy fact);
	int get_last_axiom_var(int time, FactProxy fact);

	// variable -> value -> list of actions
	std::vector<std::vector<std::vector<int>>> achiever;
	std::vector<std::vector<std::vector<int>>> deleter;

	// axiom SCCs
	std::vector<AxiomSCC> axiomSCCsInTopOrder;
	std::vector<std::vector<OperatorProxy>> achievers_per_derived;
	
	void printVariableTruth(void* solver, sat_capsule & capsule);
protected:
    virtual void initialize() override;
    virtual SearchStatus step() override;

public:
    explicit SATSearch(const plugins::Options &opts);
    virtual ~SATSearch() = default;

    virtual void print_statistics() const override;
};

extern void add_options_to_feature(plugins::Feature &feature);
}

#endif
