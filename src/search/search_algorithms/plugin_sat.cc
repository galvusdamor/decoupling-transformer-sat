#include "sat_search.h"
#include "search_common.h"

#include "../plugins/plugin.h"

using namespace std;

namespace plugin_sat {
class SATSearchFeature : public plugins::TypedFeature<SearchAlgorithm, sat_search::SATSearch> {
public:
    SATSearchFeature() : TypedFeature("sat") {
        document_title("SAT search");
        document_synopsis("");
		
		add_option<int>(
            "plan_length",
            "run the search for a single plan length only. -1 if length should not be fixed.",
            "-1");
		add_option<int>(
            "encoding",
            "set the encoding. Currently supported are OneStep: 0 and ExistsStep: 2",
            "2");
		add_option<int>(
            "length_iteration",
            "run the search for a single plan length only. -1 if length should not be fixed. This options run's Rintanen's algorithm C in the round specified by length_iteration",
            "-1");
   		add_option<int>(
            "start_length",
            "only if length_iteration != -1. Start value for C.",
            "5");
   		add_option<int>(
            "disabling_threshold",
            "threshold for the size of the disabling graph. If graph becomes larger than this, make simplifying assumptions.",
            "5000000");
   		add_option<bool>(
            "join_groups_above_threshold",
            "join all groups of operators above the exists-step threshold into a single big group",
            "true");
   		add_option<double>(
            "multiplier",
            "only if length_iteration != -1. Multiplier for C.",
            "1.41");
     sat_search::add_options_to_feature(*this);
    }
};

static plugins::FeaturePlugin<SATSearchFeature> _plugin;
}
