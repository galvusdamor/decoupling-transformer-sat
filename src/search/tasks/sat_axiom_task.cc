#include "sat_axiom_task.h"

#include "../operator_cost.h"

#include "../plugins/plugin.h"
#include "../task_utils/task_properties.h"
#include "../tasks/root_task.h"
#include "../utils/system.h"

#include <fstream>
#include <iostream>
#include "../task_utils/dump_sas_task.h"

#include <iostream>
#include <memory>

using namespace std;
using utils::ExitCode;

namespace tasks {
SatAxiomTask::SatAxiomTask(
    const shared_ptr<AbstractTask> &parent)
    : DelegatingTask(parent),
      new_initial_state(parent->get_initial_state_values()) {
    TaskProxy parent_proxy(*parent);
    for (const auto &var : parent_proxy.get_variables()) {
        if (var.is_derived() && var.get_default_axiom_value() == 1) {
            affected_variables.insert(var.get_id());
            new_initial_state[var.get_id()] = 0;
        }
    }

    TaskProxy task_proxy(*this);
    AxiomEvaluator &axiom_evaluator = g_axiom_evaluators[task_proxy];
    axiom_evaluator.evaluate(new_initial_state);
}

FactPair SatAxiomTask::get_adjusted_fact(const FactPair &fact) const {
    int var = fact.var;
    int value = fact.value;
    if (affected_variables.contains(fact.var)) {
        value = fact.value ^ 1;
    }
    return FactPair(var, value);
}


int SatAxiomTask::get_variable_default_axiom_value(int /*var*/) const {
    return 0;
}
string SatAxiomTask::get_fact_name(const FactPair &fact) const {
    return parent->get_fact_name(get_adjusted_fact(fact));
}

bool SatAxiomTask::are_facts_mutex(const FactPair &fact1, const FactPair &fact2) const {
    return parent->are_facts_mutex(get_adjusted_fact(fact1), get_adjusted_fact(fact2));
}

FactPair SatAxiomTask::get_operator_precondition(int op_index, int fact_index, bool is_axiom) const {
    FactPair fact = parent->get_operator_precondition(op_index, fact_index, is_axiom);
    return get_adjusted_fact(fact);
}

FactPair SatAxiomTask::get_operator_effect_condition(int op_index, int eff_index, int cond_index, bool is_axiom) const {
    FactPair fact = parent->get_operator_effect_condition(op_index, eff_index, cond_index, is_axiom);
    return get_adjusted_fact(fact);
}

FactPair SatAxiomTask::get_operator_effect(int op_index, int eff_index, bool is_axiom) const {
     FactPair fact = parent->get_operator_effect(op_index, eff_index, is_axiom);
     return get_adjusted_fact(fact);
}

FactPair SatAxiomTask::get_goal_fact(int index) const {
    FactPair fact = parent->get_goal_fact(index);
    return get_adjusted_fact(fact);
}

vector<int> SatAxiomTask::get_initial_state_values() const {
    return new_initial_state;
}

class SatAxiomTaskFeature : public plugins::TypedFeature<AbstractTask, SatAxiomTask> {
public:
    SatAxiomTaskFeature() : TypedFeature("sat_axiom") {
        document_title("Sat-axiom task");
        document_synopsis(
            "A task that sets the default value of axioms to false (0) such that the sat engine supports it.");

        add_cost_type_option_to_feature(*this);
    }

    shared_ptr<SatAxiomTask> create_component(const plugins::Options &, const utils::Context &) const override {
        return make_shared<SatAxiomTask>(g_root_task);
    }
};

static plugins::FeaturePlugin<SatAxiomTaskFeature> _plugin;
}
