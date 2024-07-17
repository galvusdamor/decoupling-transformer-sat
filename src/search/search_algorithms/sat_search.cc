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

int SATSearch::get_axiom_var(int time, int layer, FactProxy fact){
	assert(fact.get_value() == 1);
	return axiom_variables[time][layer][fact.get_variable().get_id()];
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


	int numberOfAxiomLayers = 10;

	////////////// 1. Generate all base variables (actions and facts)
	fact_variables.clear();
	fact_variables.resize(currentLength+1);
	axiom_variables.clear();
	axiom_variables.resize(currentLength+1);
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

	for (int time = 0; time <= currentLength; time++){
		axiom_variables[time].resize(numberOfAxiomLayers+1);
		for (int layer = 0; layer <= numberOfAxiomLayers; layer++){
			axiom_variables[time][layer].resize(task_proxy.get_variables().size());
			for (size_t var = 0; var < task_proxy.get_variables().size(); var++){
				VariableProxy varProxy = task_proxy.get_variables()[var];
				if (!varProxy.is_derived()) continue;
				// variables from axioms must be "boolean"
				assert(varProxy.get_domain_size() == 2);
				
				int factVar = capsule.new_variable();
				axiom_variables[time][layer][var] = factVar;
				DEBUG(capsule.registerVariable(factVar,"ax " + pad_int(var)+ " @ " + pad_int(time) + " / " + pad_int(layer) + " " + varProxy.get_name() + "=" + varProxy.get_fact(1).get_name()));
				//DEBUG(capsule.registerVariable(factVar,"ax " + pad_int(var)+ " @ " + pad_int(time) + " / " + pad_int(layer)));
			}
		}
	}

	// 2. action effects / preconditions
	vector<vector<vector<vector<int>>>> achieverVars(currentLength);
	vector<vector<vector<vector<int>>>> deleterVars(currentLength);
	for (int time = 0; time < currentLength; time++){
		achieverVars[time].resize(task_proxy.get_variables().size());
		deleterVars[time].resize(task_proxy.get_variables().size());
		for (size_t var = 0; var < task_proxy.get_variables().size(); var++){
			VariableProxy varProxy = task_proxy.get_variables()[var];
			// derived predicates don't have frame axioms
			if (varProxy.is_derived()) continue;				
			achieverVars[time][var].resize(varProxy.get_domain_size());
			deleterVars[time][var].resize(varProxy.get_domain_size());
		}
	}



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

				int thisCausation;

				if (conditions.size() == 1){
					thisCausation = opvar;
				} else {
					thisCausation = capsule.new_variable();
					DEBUG(capsule.registerVariable(thisCausation,"ce " + pad_int(op) + " " + pad_int(eff) +" @ " + pad_int(time)));
					
					for (int required : conditions)
						implies(solver,thisCausation,required);
	
				}

				// adding effect	
				andImplies(solver,conditions,eff_fact_var);
				achieverVars[time][thisEff.get_fact().get_variable().get_id()]
					[thisEff.get_fact().get_value()].push_back(thisCausation);

				// implicit deleting effects, i.e. delete any value of the variable that is set
				for (int val = 0; val < thisEff.get_fact().get_variable().get_domain_size(); val++){
					if (val == thisEff.get_fact().get_value()) continue;
			
					int deletedFact = fact_variables[time+1][thisEff.get_fact().get_variable().get_id()][val];
					andImplies(solver,conditions,-deletedFact);
					deleterVars[time][thisEff.get_fact().get_variable().get_id()]
						[val].push_back(thisCausation);
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

				//vector<int> achieverVars;
				//for (int a : achiever[var][val])
				//	achieverVars.push_back(operator_variables[time][a]);

				impliesPosAndNegImpliesOr(solver,nextTime,thisTime,achieverVars[time][var][val]);

				//vector<int> deleterVars;
				//for (int d : deleter[var][val])
				//	deleterVars.push_back(operator_variables[time][d]);

				impliesPosAndNegImpliesOr(solver,thisTime,nextTime,deleterVars[time][var][val]);
			}
		}
	}

	// 4. Evaluation of axioms
	// assumption here is: the variables in fact_variables are the ones
	// that are supposed to be used for preconditions
	AxiomsProxy axioms = task_proxy.get_axioms();
	for (int time = 0; time <= currentLength; time++){
		// initially all axioms are false
		for (size_t var = 0; var < task_proxy.get_variables().size(); var++)
			if (task_proxy.get_variables()[var].is_derived()){
				assertNot(solver,axiom_variables[time][0][var]);
			}

		// final value of the axioms implies their value for the next layer
		for (size_t var = 0; var < task_proxy.get_variables().size(); var++){
			if (task_proxy.get_variables()[var].is_derived()){
				// if axiom evaluates to true, its value 1 is the correct one
				implies(solver,axiom_variables[time][numberOfAxiomLayers][var],fact_variables[time][var][1]);
				// if axiom evaluates to false, its value 0 is the correct one
				implies(solver,-axiom_variables[time][numberOfAxiomLayers][var],fact_variables[time][var][0]);
			}
		}
		
		for (int layer = 0; layer < numberOfAxiomLayers; layer++){
			vector<vector<int>> causeVariables (task_proxy.get_variables().size());
			for (size_t ax = 0; ax < axioms.size(); ax++){
				OperatorProxy opProxy = axioms[ax];

				// Effect
				EffectsProxy effs = opProxy.get_effects();
				assert(effs.size() == 1);
				EffectProxy thisEff = effs[0];
				assert(thisEff.get_fact().get_value() == 1);
				assert(thisEff.get_fact().get_variable().is_derived());
				int eff_var = thisEff.get_fact().get_variable().get_id();
				int eff_fact_var = get_axiom_var(time,layer+1,thisEff.get_fact());

				set<int> conditions;
				// Preconditions
				PreconditionsProxy precs = opProxy.get_preconditions();
				vector<FactProxy> conds;
			
				for (size_t pre = 0; pre < precs.size(); pre++)
					conds.push_back(precs[pre]);
				
				EffectConditionsProxy cond = thisEff.get_conditions();
				for (size_t i = 0; i < cond.size(); i++)
					conds.push_back(cond[i]);

				for (FactProxy & fact : conds){
					// TODO stratification!
					if (fact.get_variable().is_derived()){
						// the variables that is changed will require value 0
						if (fact.get_variable().get_id() == eff_var){
							assert(fact.get_value() == 0);
							continue;	
						}

						assert(fact.get_value() == 1);
						int fact_var = get_axiom_var(time,layer,fact);
						conditions.insert(fact_var);
					} else {
						int fact_var = get_fact_var(time,fact);
						conditions.insert(fact_var);
					}
				}
				
				
				andImplies(solver,conditions,eff_fact_var);

				assert(conditions.size() > 0);
				if (conditions.size() == 1){
					causeVariables[eff_var].push_back(*conditions.begin());
				} else {
					int intermediateCausation = capsule.new_variable();
					causeVariables[eff_var].push_back(intermediateCausation);
					DEBUG(capsule.registerVariable(intermediateCausation,"ca " + pad_int(ax) + " @ " + pad_int(time) + " " + pad_int(layer)));
					for (int required : conditions)
						implies(solver, intermediateCausation, required);
				}
			}

			for (size_t var = 0; var < task_proxy.get_variables().size(); var++)
				if (task_proxy.get_variables()[var].is_derived()){
					int eff_var = axiom_variables[time][layer+1][var];
					impliesOr(solver,eff_var,causeVariables[var]);
				}
		}
	}


	// 5. Init and Goal
	State init = task_proxy.get_initial_state();
	init.unpack();
	for (size_t i = 0; i < init.size(); i++){
		//if (init[i].get_variable().is_derived()) continue;
		assertYes(solver,get_fact_var(0,init[i]));
	}

	GoalsProxy goals = task_proxy.get_goals();
	for (size_t i = 0; i < goals.size(); i++){
		log << "GOAL " << goals[i].get_variable().get_id() << " " << goals[i].get_value() << " " << get_fact_var(currentLength,goals[i]) << endl;
		assertYes(solver,get_fact_var(currentLength,goals[i]));
	}
	
	// 6. State Mutexes
	for (int time = 0; time <= currentLength; time++){
		for (size_t var = 0; var < task_proxy.get_variables().size(); var++){
			atMostOne(solver,capsule,fact_variables[time][var]);
			atLeastOne(solver,capsule,fact_variables[time][var]);
		}
	}
	
	// 7. Action Control
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
				if (val > 0){
					plan.push_back(OperatorID(op));
					log << "ACTION " << task_proxy.get_operators()[op].get_name() << endl;
				}
			}
		}
    
		for (int time = 0; time <= currentLength; time++){
			for (size_t var = 0; var < task_proxy.get_variables().size(); var++){
				if (var >= 2) continue;
				VariableProxy varProxy = task_proxy.get_variables()[var];
				for (int val = 0; val < varProxy.get_domain_size(); val++){
					int factVar = fact_variables[time][var][val];
					if (ipasir_val(solver,factVar) > 0){
						log << "time " << time << " " <<varProxy.get_name() << "=" <<  varProxy.get_fact(val).get_name() << endl;
					}
				}
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
