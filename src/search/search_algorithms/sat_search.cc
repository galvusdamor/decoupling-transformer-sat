#include "sat_search.h"

#include "../plugins/options.h"

#include "../utils/logging.h"

#include "../tasks/root_task.h"
#include "../tasks/decoupled_root_task.h"
#include "../task_utils/task_properties.h"

#include "sat_encoder.h"
#include "ipasir.h"

using namespace std;

namespace sat_search {
SATSearch::SATSearch(const plugins::Options &opts)
    : SearchAlgorithm(opts),
	planLength(opts.get<int>("plan_length")){
	
	currentLength = 1;
	if (planLength != -1) currentLength = planLength;
}

void SATSearch::initialize() {
    log << "conducting SAT search"
		<< " for plan length: " << (planLength==-1?"all":to_string(planLength))
        << endl;
}

void SATSearch::print_statistics() const {
    statistics.print_detailed_statistics();
}

SearchStatus SATSearch::step() {
	sat_capsule capsule;
	reset_number_of_clauses();
	void* solver = ipasir_init();

	log << "Building SAT formula for plan length " << currentLength << endl;



	// index: timestep -> variable -> value
	vector<vector<vector<int>>> fact_variables(currentLength + 1);
	// index: timestep -> operator 
	vector<vector<int>> operator_variables(currentLength);


	for (int time = 0; time < currentLength; time++){
		for (size_t op = 0; op < task_proxy.get_operators().size(); op ++){
			int opvar = capsule.new_variable();
			operator_variables[time].push_back(opvar);
			DEBUG(capsule.registerVariable(opvar,"op " + pad_int(op) + " @ " + pad_int(time) + " " + task_proxy.get_operators()[op].get_name()));
		}
	}

	for (int time = 0; time <= currentLength; time++){
		fact_variables[time].resize(task_proxy.get_variables().size());
		for (size_t var = 0; var < task_proxy.get_variables().size(); var++){
			VariableProxy varProxy = task_proxy.get_variables()[var];
			for (size_t val = 0; val < varProxy.get_domain_size(); val++){
				int factVar = capsule.new_variable();
				fact_variables[time][var].push_back(factVar);
				DEBUG(capsule.registerVariable(factVar,"fa " + pad_int(var) + "=" + pad_int(val) + " @ " + pad_int(time) + " " + varProxy.get_name() + "=" + varProxy.get_fact(val).get_name()));
			}
		}
	}


	DEBUG(capsule.printVariables());


	int solverState = ipasir_solve(solver);
	log << "SAT solver state: " << solverState << endl;
	if (solverState == 10){
		//for (int v = 1; v <= 3; v++)
		//	log << "V " << v << ": " << ipasir_val(solver,v) << endl; 

		// if solver has success, we have solved the problem!
		return SOLVED; 
	}

	if (planLength == currentLength) {
		log << "Reached length limit" << endl;
		return FAILED;
	}
	// increase length limit on the plan
	// TODO add better strategies according to Rintanen
	currentLength++;
    return IN_PROGRESS;
}

void add_options_to_feature(plugins::Feature &feature) {
    SearchAlgorithm::add_pruning_option(feature);
    SearchAlgorithm::add_options_to_feature(feature);
}
}
