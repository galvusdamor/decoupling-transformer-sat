#include "sat_search.h"

#include "../plugins/options.h"

#include "../utils/logging.h"

#include "../tasks/root_task.h"
#include "../tasks/decoupled_root_task.h"
#include "../task_utils/task_properties.h"


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
