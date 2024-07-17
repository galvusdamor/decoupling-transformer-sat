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

	achiever.resize(task_proxy.get_variables().size());
	deleter.resize(task_proxy.get_variables().size());
	for (size_t var = 0; var < task_proxy.get_variables().size(); var++){
		VariableProxy varProxy = task_proxy.get_variables()[var];
		achiever[var].resize(varProxy.get_domain_size());
		deleter[var].resize(varProxy.get_domain_size());
	}

	for (size_t op = 0; op < task_proxy.get_operators().size(); op ++){
		OperatorProxy opProxy = task_proxy.get_operators()[op];

		// Effect
		EffectsProxy effs = opProxy.get_effects();
		for (size_t eff = 0; eff < effs.size(); eff++){
			EffectProxy thisEff = effs[eff];

			achiever[thisEff.get_fact().get_variable().get_id()][thisEff.get_fact().get_value()].push_back(op);

			// implicit deleting effects, i.e. delete any value of the variable that is set
			for (int val = 0; val < thisEff.get_fact().get_variable().get_domain_size(); val++){
				if (val == thisEff.get_fact().get_value()) continue;
		
				deleter[thisEff.get_fact().get_variable().get_id()][val].push_back(op);
			}
		}
	}
}

void SATSearch::print_statistics() const {
    statistics.print_detailed_statistics();
}

int SATSearch::get_fact_var(int time, FactProxy fact){
	return fact_variables[time][fact.get_variable().get_id()][fact.get_value()];
}


void SATSearch::printVariableTruth(void* solver, sat_capsule & capsule){
	for (int v = 1; v <= capsule.number_of_variables; v++){
		int val = ipasir_val(solver,v);
	
		std::string s = std::to_string(v);
		int x = 4 - s.size();
		while (x-- && x > 0) std::cout << " ";
		std::cout << v << ": ";
		if (val > 0) std::cout << "    ";
		else         std::cout << "not ";
#ifndef NDEBUG
		std::cout << capsule.variableNames[v] << endl; 
#else
		std::cout << v << endl;
#endif
	}
}



SearchStatus SATSearch::step() {
	sat_capsule capsule;
	reset_number_of_clauses();
	void* solver = ipasir_init();

	log << "Building SAT formula for plan length " << currentLength << endl;


	////////////// 1. Generate all base variables (actions and facts)
	fact_variables.clear();
	fact_variables.resize(currentLength+1);
	operator_variables.clear();
	operator_variables.resize(currentLength);



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
			for (int val = 0; val < varProxy.get_domain_size(); val++){
				int factVar = capsule.new_variable();
				fact_variables[time][var].push_back(factVar);
				DEBUG(capsule.registerVariable(factVar,"fa " + pad_int(var) + "=" + pad_int(val) + " @ " + pad_int(time) + " " + varProxy.get_name() + "=" + varProxy.get_fact(val).get_name()));
			}
		}
	}

	// 2. action effects / preconditions
	for (int time = 0; time < currentLength; time++){
		for (size_t op = 0; op < task_proxy.get_operators().size(); op ++){
			int opvar = operator_variables[time][op];
			OperatorProxy opProxy = task_proxy.get_operators()[op];

			// Preconditions
			PreconditionsProxy precs = opProxy.get_preconditions();
			for (size_t pre = 0; pre < precs.size(); pre++){
				FactProxy fact = precs[pre];
				int fact_var = get_fact_var(time,fact);
				
				implies(solver,opvar,fact_var);
			}

			// Effect
			EffectsProxy effs = opProxy.get_effects();
			for (size_t eff = 0; eff < effs.size(); eff++){
				EffectProxy thisEff = effs[eff];
				int eff_fact_var = get_fact_var(time+1,thisEff.get_fact());

				// gather the conditions of the conditional effect in a set (could be a vector ...)
				set<int> conditions;
				conditions.insert(opvar);
				EffectConditionsProxy cond = thisEff.get_conditions();
				for (size_t i = 0; i < cond.size(); i++)
					conditions.insert(get_fact_var(time, cond[i]));
			
				// adding effect	
				andImplies(solver,conditions,eff_fact_var);

				// implicit deleting effects, i.e. delete any value of the variable that is set
				for (int val = 0; val < thisEff.get_fact().get_variable().get_domain_size(); val++){
					if (val == thisEff.get_fact().get_value()) continue;
			
					int deletedFact = fact_variables[time+1][thisEff.get_fact().get_variable().get_id()][val];
					andImplies(solver,conditions,-deletedFact);
				}

			}
		}
	}

	// 3. Frame axioms
	for (int time = 0; time < currentLength; time++){
		for (size_t var = 0; var < task_proxy.get_variables().size(); var++){
			VariableProxy varProxy = task_proxy.get_variables()[var];
			// derived predicates don't have frame axioms
			if (varProxy.is_derived()) continue;				
			for (int val = 0; val < varProxy.get_domain_size(); val++){
				int thisTime = fact_variables[time][var][val];
				int nextTime = fact_variables[time+1][var][val];

				vector<int> achieverVars;
				for (int a : achiever[var][val])
					achieverVars.push_back(operator_variables[time][a]);

				impliesPosAndNegImpliesOr(solver,nextTime,thisTime,achieverVars);

				vector<int> deleterVars;
				for (int d : deleter[var][val])
					deleterVars.push_back(operator_variables[time][d]);

				impliesPosAndNegImpliesOr(solver,thisTime,nextTime,deleterVars);
			}
		}
	}



	// 4. Init and Goal
	State init = task_proxy.get_initial_state();
	init.unpack();
	for (size_t i = 0; i < init.size(); i++){
		assertYes(solver,get_fact_var(0,init[i]));
	}

	GoalsProxy goals = task_proxy.get_goals();
	for (size_t i = 0; i < goals.size(); i++){
		log << goals[i].get_variable().get_id() << " " << goals[i].get_value() << endl;
		assertYes(solver,get_fact_var(currentLength,goals[i]));
	}

	
	// 5. State Mutexes
	for (int time = 0; time <= currentLength; time++){
		for (size_t var = 0; var < task_proxy.get_variables().size(); var++){
			atMostOne(solver,capsule,fact_variables[time][var]);
			atLeastOne(solver,capsule,fact_variables[time][var]);
		}
	}
	
	// 6. Action Control
	// currently the most simple encoding: only one action at a time
	for (int time = 0; time < currentLength; time++){
		atMostOne(solver,capsule,operator_variables[time]);
		atLeastOne(solver,capsule,operator_variables[time]);
	}


	//DEBUG(capsule.printVariables());


	int solverState = ipasir_solve(solver);
	log << "SAT solver state: " << solverState << endl;
	if (solverState == 10){
		//printVariableTruth(solver,capsule);


		Plan plan;
		// plan extraction
		for (int time = 0; time < currentLength; time++){
			for (size_t op = 0; op < task_proxy.get_operators().size(); op++){
				int opvar = operator_variables[time][op];
				int val = ipasir_val(solver,opvar);
				if (val > 0)
					plan.push_back(OperatorID(op));
			}
		}
        
		set_plan(plan);
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
