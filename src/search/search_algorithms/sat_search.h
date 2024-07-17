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

	// variable -> value -> list of actions
	std::vector<std::vector<std::vector<int>>> achiever;
	std::vector<std::vector<std::vector<int>>> deleter;

	
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
