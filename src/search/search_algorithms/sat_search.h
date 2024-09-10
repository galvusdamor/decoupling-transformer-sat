#ifndef SEARCH_ALGORITHMS_EAGER_SEARCH_H
#define SEARCH_ALGORITHMS_EAGER_SEARCH_H

#include "../search_algorithm.h"
#include "sat_encoder.h"

#include <memory>
#include <vector>
#include <map>
#include <set>


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
	int lengthIteration;
	int startLength;
	double multiplier;
	bool existsStep = true;

	bool forceAtLeastOneAction;

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

	// axiom structure graph
	std::vector<std::vector<int>> derived_implication;
	std::map<FactPair, std::vector<int>> derived_entry_edges;
	void axiom_dfs(int var, std::set<int> & allReachable);
	// axiom SCCs
	std::vector<AxiomSCC> axiomSCCsInTopOrder;
	std::vector<std::vector<OperatorProxy>> achievers_per_derived;
	
	void printVariableTruth(void* solver, sat_capsule & capsule);

	// exists step
    std::vector<std::vector<FactPair>> sorted_op_preconditions;
	bool can_be_executed_in_same_state(int op1_no, int op2_no);
	std::vector<int> global_action_ordering;
	// generate Erasing and Requiring list
	// per fact, per SCC, gives a list of all E/R as a pair: <operator,position_in_scc>
	std::map<FactPair,std::vector< std::vector<std::pair<int,int>>  >> erasingList;
	std::map<FactPair,std::vector< std::vector<std::pair<int,int>>  >> requiringList;
	
	void exists_step_restriction(void* solver,sat_capsule & capsule, std::vector<int> & operator_variables);
	void generateChain(void* solver,sat_capsule & capsule, std::vector<int> & operator_variables,
		    const std::vector<std::pair<int, int>>& E, const std::vector<std::pair<int, int>>& R);

	
	std::map<std::string,int> clauseCounter;
	std::map<std::string,int> variableCounter;
	
	void set_up_exists_step();
	void set_up_single_step();
	
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
