#include "decoupled_plan_reconstruction_task.h"

#include "../task_utils/task_properties.h"
#include "../plugins/plugin.h"
#include "../decoupling/manual_factoring.h"

#include <iostream>
#include <fstream>
#include <regex>
#include <string>

using namespace std;

namespace tasks {
static vector<string> read_file_to_string(const string &filename) {
    ifstream file(filename);
    vector<string> lines;
    string line;

    if (file.is_open()) {
        while (std::getline(file, line)) {
            lines.push_back(line);
        }
        file.close();
    } else {
        cerr << "Unable to open file: " << filename << endl;
    }

    return lines;
}


DecoupledPlanReconstructionTask::DecoupledPlanReconstructionTask(const plugins::Options & /*options*/)
    : RootTask(), factoring(nullptr) {
    TaskProxy original_task_proxy(*tasks::g_root_task);
    task_properties::verify_no_axioms(original_task_proxy);
    task_properties::verify_no_conditional_effects(original_task_proxy);

    // Factoring file to leave vector
    vector<vector<int>> leaves;
    string leave_str = read_file_to_string("factoring.txt")[0];
    assert(leave_str.size() > 2);
    leave_str = leave_str.substr(1, leave_str.length() - 2);
    leave_str = regex_replace(leave_str, regex("\\],"), "];");
    for (auto leaf_str : utils::split(leave_str, ";")) {
        leaves.push_back(vector<int>());
        leaf_str = leaf_str.substr(1, leaf_str.length() - 2);
        for (auto var_str : utils::split(leaf_str, ",")) {
            leaves.back().push_back(stoi(var_str));
        }
    }

    // Plan file to vector of operator ids
    vector<OperatorID> plan;
    vector<string> plan_steps = read_file_to_string("decoupled_plan");
    plan_steps.erase(std::remove_if(plan_steps.begin(), plan_steps.end(),
                                    [](const std::string &s) {return !s.empty() && s[0] == ';';}), plan_steps.end());
    for (string &op_name : plan_steps) {
        op_name = op_name.substr(1, op_name.length() - 2);
        for (auto const &op : original_task_proxy.get_operators()) {
            if (op_name == op.get_name()) {
                plan.push_back(OperatorID(op.get_id()));
                break;
            }
        }
    }

    if (plan.size() != plan_steps.size()) {
        cerr << "Can not align plan file to planning task!" << endl;
        utils::exit_with(utils::ExitCode::SEARCH_CRITICAL_ERROR);
    }

    plugins::Options opts;
    opts.set("verbosity", utils::Verbosity::NORMAL);
    opts.set("min_number_leaves", 1);
    opts.set("max_leaf_size", numeric_limits<int>::max());
    opts.set("factoring_time_limit", numeric_limits<int>::max());
    opts.set("prune_fork_leaf_state_spaces", false);
    opts.set("leaves", leaves);

    factoring = make_shared<decoupling::ManualFactoring>(opts);

    factoring->compute_factoring();

    cout << "TODO!!!" << endl;
    exit(0);
}

class DecoupledPlanReconstructionTaskFeature : public plugins::TypedFeature<AbstractTask, DecoupledPlanReconstructionTask> {
public:
    DecoupledPlanReconstructionTaskFeature() : TypedFeature("decoupled_plan_reconstruction") {
        document_title("Decoupled plan reconstruction task");
        document_synopsis("Task transformation that reconstructs a plan (decoupled_plan) for a given problem (output.sas) and factoring (factoring.txt)");
    }

    virtual shared_ptr<DecoupledPlanReconstructionTask> create_component(const plugins::Options &options, const utils::Context &) const override {
        return make_shared<DecoupledPlanReconstructionTask>(options);
    }
};

static plugins::FeaturePlugin<DecoupledPlanReconstructionTaskFeature> _plugin;
}