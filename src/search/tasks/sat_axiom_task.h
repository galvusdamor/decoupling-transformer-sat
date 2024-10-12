#ifndef TASKS_COST_SAT_AXIOM_TASK_H
#define TASKS_COST_SAT_AXIOM_TASK_H

#include "delegating_task.h"

#include "../axioms.h"

#include <unordered_set>

namespace plugins {
class Options;
}

namespace tasks {
class SatAxiomTask : public DelegatingTask {
    std::unordered_set<int> affected_variables;
    std::vector<int> new_initial_state;

    FactPair get_adjusted_fact(const FactPair &fact) const;
public:
    SatAxiomTask(
        const std::shared_ptr<AbstractTask> &parent);
    virtual ~SatAxiomTask() override = default;

    virtual int get_variable_default_axiom_value(int var) const override;
    virtual std::string get_fact_name(const FactPair &fact) const override;

    virtual bool are_facts_mutex(
        const FactPair &fact1, const FactPair &fact2) const override;

    virtual FactPair get_operator_precondition(
        int op_index, int fact_index, bool is_axiom) const override;

    virtual FactPair get_operator_effect_condition(
        int op_index, int eff_index, int cond_index, bool is_axiom) const override;

    virtual FactPair get_operator_effect(
        int op_index, int eff_index, bool is_axiom) const override;

    virtual FactPair get_goal_fact(int index) const override;

    virtual std::vector<int> get_initial_state_values() const override;
};
}

#endif
