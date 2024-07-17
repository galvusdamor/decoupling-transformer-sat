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
        sat_search::add_options_to_feature(*this);
    }
};

static plugins::FeaturePlugin<SATSearchFeature> _plugin;
}
