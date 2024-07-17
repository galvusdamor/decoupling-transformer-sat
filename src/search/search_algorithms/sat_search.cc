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
   	log << "Step" << endl;

	sat_capsule capsule;
	reset_number_of_clauses();
	void* solver = ipasir_init();

	ipasir_add(solver,-1);
	ipasir_add(solver,-2);
	ipasir_add(solver,0);
	
	ipasir_add(solver,-3);
	ipasir_add(solver,2);
	ipasir_add(solver,0);
	
	ipasir_add(solver,3);
	ipasir_add(solver,0);

	int state = ipasir_solve(solver);
	log << "SAT solver state: " << state << endl;
	if (state == 10){
		for (int v = 1; v <= 3; v++)
			log << "V " << v << ": " << ipasir_val(solver,v) << endl; 

		// if solver has success, we have solved the problem!
		return SOLVED; 
	}

	if (planLength == currentLength) {
		log << "Reached length limit" << endl;
		return FAILED;
	}
    return IN_PROGRESS;
}

void add_options_to_feature(plugins::Feature &feature) {
    SearchAlgorithm::add_pruning_option(feature);
    SearchAlgorithm::add_options_to_feature(feature);
}
}
