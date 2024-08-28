#include <cmath>
#include <iomanip>
#include "sat_search.h"

#include "../plugins/options.h"

#include "../algorithms/sccs.h"

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
	planLength(opts.get<int>("plan_length")),
	lengthIteration(opts.get<int>("length_iteration")),
	startLength(opts.get<int>("start_length")),
	multiplier(opts.get<double>("multiplier"))
	{

	forceAtLeastOneAction = true;
	
	currentLength = 1;
	if (planLength != -1) currentLength = planLength;

	if (lengthIteration != -1){
		currentLength = planLength = int(0.5 + startLength * pow(multiplier, lengthIteration));
		forceAtLeastOneAction = false;
	}
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


	for (size_t var = 0; var < task_proxy.get_variables().size(); var++){
		VariableProxy varProxy = task_proxy.get_variables()[var];
		if (!varProxy.is_derived()) continue;
	}

	vector<vector<int>> derived_implication(task_proxy.get_variables().size());
	achievers_per_derived.resize(task_proxy.get_variables().size());

	// building the derived predicate dependency graph
	AxiomsProxy axioms = task_proxy.get_axioms();
	for (size_t ax = 0; ax < axioms.size(); ax++){
		OperatorProxy opProxy = axioms[ax];

		// Effect
		EffectsProxy effs = opProxy.get_effects();
		assert(effs.size() == 1);
		EffectProxy thisEff = effs[0];
		assert(thisEff.get_fact().get_value() == 1);
		assert(thisEff.get_fact().get_variable().is_derived());
		int eff_var = thisEff.get_fact().get_variable().get_id();
		achievers_per_derived[eff_var].push_back(opProxy);

		// Preconditions
		PreconditionsProxy precs = opProxy.get_preconditions();
		vector<FactProxy> conds;
	
		for (size_t pre = 0; pre < precs.size(); pre++)
			conds.push_back(precs[pre]);
		
		EffectConditionsProxy cond = thisEff.get_conditions();
		for (size_t i = 0; i < cond.size(); i++)
			conds.push_back(cond[i]);

		for (FactProxy & fact : conds){
			if (fact.get_variable().is_derived()){
				// the variables that is changed will require value 0
				if (fact.get_variable().get_id() == eff_var){
					assert(fact.get_value() == 0);
					continue;	
				}

				assert(fact.get_value() == 1);
				int fact_var = fact.get_variable().get_id();
				derived_implication[fact_var].push_back(eff_var);
			}
		}
	}
	vector<vector<int>> initial_derived_sccs = sccs::compute_maximal_sccs(derived_implication);
	vector<vector<int>> derived_sccs;
	for (vector<int> s : initial_derived_sccs){
		if (s.size() == 1 && !task_proxy.get_variables()[s[0]].is_derived()) continue;
		derived_sccs.push_back(s);
		//log << "SCC of size " << s.size() << endl;
	}
	log << "Number of SCCs " << derived_sccs.size() << endl;


	int sizeOneSCCs = 0;
	int impliationSCCS = 0;
	int oneFactSCCS = 0;
	int oneVarSCCS = 0;
	int oneFactSCCSInternal = 0;
	int oneVarSCCSInternal = 0;
	int problematicSCCS = 0;
	for (vector<int> s : derived_sccs){
		AxiomSCC thisSCC;
		thisSCC.variables = s;
		if (s.size() == 1){
			sizeOneSCCs++;
			thisSCC.sizeOne = true;
			axiomSCCsInTopOrder.push_back(thisSCC);
			continue;
		}
		set<int> sset(s.begin(), s.end());

		// check if all internal edges are implications only
		bool implicationOnly = true;
		bool twoAntecedants = false;
		FactProxy actualDependency(*task,0,0);
		bool oneActualDependency = true;
		int varDependency = -1;

		FactProxy actualDependencyInternal(*task,0,0);
		bool oneActualDependencyInternal = true;
		int varDependencyInternal = -1;
		for (int dp : s){
			for (OperatorProxy opProxy : achievers_per_derived[dp]){
				// effect
				EffectsProxy effs = opProxy.get_effects();
				assert(effs.size() == 1);
				EffectProxy thisEff = effs[0];
				assert(thisEff.get_fact().get_value() == 1);
				assert(thisEff.get_fact().get_variable().is_derived());
				int eff_var = thisEff.get_fact().get_variable().get_id();
				// Preconditions
				PreconditionsProxy precs = opProxy.get_preconditions();
				vector<FactProxy> conds;
	
				for (size_t pre = 0; pre < precs.size(); pre++)
					conds.push_back(precs[pre]);
				
				EffectConditionsProxy cond = thisEff.get_conditions();
				for (size_t i = 0; i < cond.size(); i++)
					conds.push_back(cond[i]);

				int numDerived = 0;
				bool hasActual = false;
				FactProxy myActualDependency(*task,0,0);
				bool myOneActualDependency = true;
				int myVarDependency = -1;
				for (FactProxy & fact : conds){
					if (fact.get_variable().get_id() == eff_var) continue;
					if (fact.get_variable().is_derived() &&
							sset.count(fact.get_variable().get_id())){
						numDerived++;
					} else {
						// condition outside of this SCC or non-derived
						hasActual = true;
						if (myVarDependency == -1){
							myVarDependency = fact.get_variable().get_id();
							myActualDependency = fact;
						} if (myVarDependency != fact.get_variable().get_id()){
							myVarDependency = -2; // dependent on multiple variables
						} else if (myActualDependency != fact){
							myOneActualDependency = false;
						}
					}
					if (!hasActual && numDerived == 1) continue;
					if (hasActual && numDerived == 0) continue;
					//log << "FAIL SCC with " << fact.get_variable().get_id() << " -> " << eff_var << endl;
					implicationOnly = false;
				}
				if (myVarDependency != -1){
					if (myVarDependency == -2){
						varDependency = -2;
						oneActualDependency = false;
					} else if (myVarDependency != varDependency){
						// no dependency known before
						if (varDependency == -1){
							varDependency = myVarDependency;
							actualDependency = myActualDependency;
						} else {
							varDependency = -2;
							oneActualDependency = false;
						}
					} else if (!myOneActualDependency || myActualDependency != actualDependency){
						oneActualDependency = false;
					}

					if (numDerived){
						if (myVarDependency == -2){
							varDependencyInternal = -2;
							oneActualDependencyInternal = false;
						} else if (myVarDependency != varDependencyInternal){
							// no dependency known before
							if (varDependencyInternal == -1){
								varDependencyInternal = myVarDependency;
								actualDependencyInternal = myActualDependency;
							} else {
								varDependencyInternal = -2;
								oneActualDependencyInternal = false;
							}
						} else if (!myOneActualDependency || myActualDependency != actualDependencyInternal){
							oneActualDependencyInternal = false;
						}
					}
				}
				if (numDerived >= 2) twoAntecedants = true;
			}
		}

		if (twoAntecedants){
			log << "Problematic (2 antecedants) SCC of size " << s.size() << endl;
			problematicSCCS++;
			thisSCC.fullComputationRequired = true;
			thisSCC.numberOfAxiomLayers = thisSCC.variables.size();
			axiomSCCsInTopOrder.push_back(thisSCC);
			continue;
		}

		if (implicationOnly){
			log << "Implication SCC of size " << s.size() << endl;
			impliationSCCS++;
			thisSCC.isOfImplicationType = true;
			axiomSCCsInTopOrder.push_back(thisSCC);
			continue;
		}

		if (oneActualDependency){
			log << "One fact dependency SCC of size " << s.size() << endl;
			oneFactSCCS++;
			thisSCC.isDependentOnOneVariableInternally = true;
			thisSCC.dependingVariable = varDependencyInternal;
			axiomSCCsInTopOrder.push_back(thisSCC);
			continue;
		}

		if (oneActualDependencyInternal){
			log << "One fact dependency internal SCC of size " << s.size() << endl;
			oneFactSCCSInternal++;
			thisSCC.isDependentOnOneVariableInternally = true;
			thisSCC.dependingVariable = varDependencyInternal;
			axiomSCCsInTopOrder.push_back(thisSCC);
			continue;
		}

		if (varDependency != -2){
			log << "One var dependency SCC of size " << s.size() << endl;
			oneVarSCCS++;
			thisSCC.isDependentOnOneVariableInternally = true;
			thisSCC.dependingVariable = varDependencyInternal;
			axiomSCCsInTopOrder.push_back(thisSCC);
			continue;
		}

		if (varDependencyInternal != -2){
			log << "One var dependency internal SCC of size " << s.size() << endl;
			oneVarSCCSInternal++;
			thisSCC.isDependentOnOneVariableInternally = true;
			thisSCC.dependingVariable = varDependencyInternal;
			axiomSCCsInTopOrder.push_back(thisSCC);
			continue;
		}

		log << "Problematic SCC of size " << s.size() << endl;
		log << "members:";
		for (int d : sset) log << d << " ";
		log << endl;
		problematicSCCS++;
		
		thisSCC.fullComputationRequired = true;
		thisSCC.numberOfAxiomLayers = thisSCC.variables.size();
		axiomSCCsInTopOrder.push_back(thisSCC);
	}
	log << "Size 1 SCCS: " << sizeOneSCCs << endl;
	log << "Implication SCCS: " << impliationSCCS << endl;
	log << "OneFact SCCS: " << oneFactSCCS << endl;
	log << "OneVar SCCS: " << oneVarSCCS << endl;
	log << "OneFact internal SCCS: " << oneFactSCCSInternal << endl;
	log << "OneVar internal SCCS: " << oneVarSCCSInternal << endl;
	log << "Other SCCS: " << problematicSCCS << endl;



	// pre-process the axiom SCCs that can be handled specially
	for (AxiomSCC &scc : axiomSCCsInTopOrder){
		map<int,int> varsToOffset;
		for (size_t varOffset = 0; varOffset < scc.variables.size(); varOffset++)
			varsToOffset[scc.variables[varOffset]] = varOffset;

		if (scc.isOfImplicationType){
			log << "Pre Processing Implication Type SCC" << endl;

			// run Floyd Warshall on the implications
			vector<vector<bool>> reach (scc.variables.size());
			for (size_t varOffset = 0; varOffset < scc.variables.size(); varOffset++){
				reach[varOffset].resize(scc.variables.size());
				reach[varOffset][varOffset] = true;
				for (int implicated : derived_implication[scc.variables[varOffset]]){
					if (varsToOffset.count(implicated))
						reach[varOffset][varsToOffset[implicated]] = true;
				}
			}
			
			// compute transitive closure 
			for (size_t k = 0; k < reach.size(); k++)
				for (size_t i = 0; i < reach.size(); i++)
					for (size_t j = 0; j < reach.size(); j++)
						if (reach[i][k] && reach[k][j]) reach[i][j] = true;


			scc.directTransitiveImplications.resize(scc.variables.size());
			scc.directTransitiveCauses.resize(scc.variables.size());
			for (size_t varOffset = 0; varOffset < reach.size(); varOffset++)
				for (size_t varOffsetTo = 0; varOffsetTo < reach.size(); varOffsetTo++)
					if (reach[varOffset][varOffsetTo]){
						scc.directTransitiveImplications[varOffset].push_back(varOffsetTo);
						scc.directTransitiveCauses[varOffsetTo].push_back(varOffset);
					}
			
			//for (size_t varOffset = 0; varOffset < reach.size(); varOffset++){
			//	log << "Variable " << scc.variables[varOffset] << " reaches:";
			//	for (int offset : scc.directTransitiveImplications[varOffset])
			//		log << " " << scc.variables[offset];
			//	log << endl;
			//}

		} else if (scc.isDependentOnOneVariableInternally){
			log << "Pre Processing One Variable Dependent SCC" << endl;
			
			VariableProxy varProxy = task_proxy.get_variables()[scc.dependingVariable];
			scc.guardedTransitiveImplications.resize(varProxy.get_domain_size());
			scc.guardedTransitiveCauses.resize(varProxy.get_domain_size());

			for (int value = 0; value < varProxy.get_domain_size(); value++){
				// run Floyd Warshall on the implications
				vector<vector<bool>> reach (scc.variables.size());
				for (size_t varOffset = 0; varOffset < scc.variables.size(); varOffset++){
					reach[varOffset].resize(scc.variables.size());
					reach[varOffset][varOffset] = true;
				}
				
				for (size_t varOffsetTo = 0; varOffsetTo < scc.variables.size(); varOffsetTo++){
					int variableTo = scc.variables[varOffsetTo];
					for (OperatorProxy opProxy : achievers_per_derived[variableTo]){
						// effect
						EffectsProxy effs = opProxy.get_effects();
						assert(effs.size() == 1);
						EffectProxy thisEff = effs[0];
						assert(thisEff.get_fact().get_value() == 1);
						assert(thisEff.get_fact().get_variable().is_derived());
						int eff_var = thisEff.get_fact().get_variable().get_id();
						// Preconditions
						PreconditionsProxy precs = opProxy.get_preconditions();
						vector<FactProxy> conds;
		
						for (size_t pre = 0; pre < precs.size(); pre++)
							conds.push_back(precs[pre]);
						
						EffectConditionsProxy cond = thisEff.get_conditions();
						for (size_t i = 0; i < cond.size(); i++)
							conds.push_back(cond[i]);
	
						int numDerived = 0;
						FactProxy myActualDependency(*task,0,0);
						int myVarDependency = -1;
						int derivedDependency = -1;
						for (FactProxy & fact : conds){
							if (fact.get_variable().get_id() == eff_var) continue;
							if (fact.get_variable().is_derived() &&
									varsToOffset.count(fact.get_variable().get_id())){
								numDerived++;
								derivedDependency = fact.get_variable().get_id();
							} else {
								// condition outside of this SCC or non-derived
								if (myVarDependency == -1){
									myVarDependency = fact.get_variable().get_id();
									myActualDependency = fact;
								} if (myVarDependency != fact.get_variable().get_id()){
									myVarDependency = -2; // dependent on multiple variables
								} else if (myActualDependency != fact){
									assert(false); // this cannot happen
								}
							}
						}

						// axiom that is not internal to the SCC, will be handled separately
						if (numDerived == 0) continue; 
						assert(myVarDependency != -2);
						if (myVarDependency == -1){
							// this is a simple implication without condition, so it is always reached
							reach[varsToOffset[derivedDependency]][varOffsetTo] = true;
						} else {
							assert(myVarDependency == scc.dependingVariable);
							// not the current value
							if (value != myActualDependency.get_value()) continue;
							reach[varsToOffset[derivedDependency]][varOffsetTo] = true;
						}
					}
				}

				
				// compute transitive closure 
				for (size_t k = 0; k < reach.size(); k++)
					for (size_t i = 0; i < reach.size(); i++)
						for (size_t j = 0; j < reach.size(); j++)
							if (reach[i][k] && reach[k][j]) reach[i][j] = true;


				scc.guardedTransitiveImplications[value].resize(scc.variables.size());
				scc.guardedTransitiveCauses[value].resize(scc.variables.size());
				for (size_t varOffset = 0; varOffset < reach.size(); varOffset++)
					for (size_t varOffsetTo = 0; varOffsetTo < reach.size(); varOffsetTo++)
						if (reach[varOffset][varOffsetTo]){
							scc.guardedTransitiveImplications[value][varOffset].push_back(varOffsetTo);
							scc.guardedTransitiveCauses[value][varOffsetTo].push_back(varOffset);
						}
				
				//for (size_t varOffset = 0; varOffset < reach.size(); varOffset++){
				//	log << "Variable " << scc.variables[varOffset] << " reaches with value " << value << ":";
				//	for (int offset : scc.guardedTransitiveImplications[value][varOffset])
				//		log << " " << scc.variables[offset];
				//	log << endl;
				//}
			}
		}
	
	}


	//// We are trying to find variables that
	//// 1) Occur in all (or a lot of?) operators as effects
	//// 2) have only 2 values (true/false)
	//// 3) have an unconditional effect on them or a condition only on another variable that has only two values

	//set<int> nogoodVariables;

	//vector<map<pair<int,bool>, set<int>>> makingTrueOperators(task_proxy.get_variables().size());
	//vector<map<pair<int,bool>, set<int>>> makingFalseOperators(task_proxy.get_variables().size());

	//////// check for special types of conditional effects
	//for (size_t op = 0; op < task_proxy.get_operators().size(); op ++){
	//	OperatorProxy opProxy = task_proxy.get_operators()[op];

	//	// Effect
	//	EffectsProxy effs = opProxy.get_effects();
	//	for (size_t eff = 0; eff < effs.size(); eff++){
	//		EffectProxy thisEff = effs[eff];
	//		int effVar = thisEff.get_fact().get_variable().get_id();
	//		if (thisEff.get_fact().get_variable().get_domain_size() > 2) {
	//			nogoodVariables.insert(effVar);
	//			continue; // not a good variable
	//		}

	//		// gather the conditions of the conditional effect 
	//		EffectConditionsProxy cond = thisEff.get_conditions();
	//		if (cond.size() > 1) {
	//			nogoodVariables.insert(effVar);
	//			continue; // not a good effect
	//		}

	//		int conditionVariable = -1; // no condition 
	//		bool conditionState = true;
	//		for (size_t i = 0; i < cond.size(); i++){
	//			FactProxy condition = cond[i];
	//			if (condition.get_variable().get_domain_size() > 2) {
	//				nogoodVariables.insert(effVar);
	//				continue; // not a good variable
	//			}
	//			conditionState = condition.get_value() == 1;
	//			conditionVariable = condition.get_variable().get_id();
	//		}

	//		bool effectState = thisEff.get_fact().get_value() == 1;

	//		if (effectState)
	//			makingTrueOperators[effVar][{conditionVariable,conditionState}].insert(op);
	//		else
	//			makingFalseOperators[effVar][{conditionVariable,conditionState}].insert(op);
	//	}
	//}

	//for (size_t var = 0; var < task_proxy.get_variables().size(); var++){
	//	VariableProxy varProxy = task_proxy.get_variables()[var];
	//	if (varProxy.is_derived()) continue;
	//	if (nogoodVariables.count(var)) continue;
	//	log << "Good variable: " << var << endl;
	//	log << "+:" << endl;
	//	for (auto [a,b] : makingTrueOperators[var]){
	//		log << "\t" << a.first << " " << a.second << ":";
	//		for (int i : b) log << " " << i;
	//		log << endl;
	//	}
	//	log << "-:" << endl;
	//	for (auto [a,b] : makingFalseOperators[var]){
	//		log << "\t" << a.first << " " << a.second << ":";
	//		for (int i : b) log << " " << i;
	//		log << endl;
	//	}
	//}
}

void SATSearch::print_statistics() const {
    statistics.print_detailed_statistics();
}

int SATSearch::get_fact_var(int time, FactProxy fact){
	return fact_variables[time][fact.get_variable().get_id()][fact.get_value()];
}

int SATSearch::get_axiom_var(int time, int layer, FactProxy fact){
	assert(fact.get_value() == 1);
	return axiom_variables[time][fact.get_variable().get_id()][layer];
}

int SATSearch::get_last_axiom_var(int time, FactProxy fact){
	assert(fact.get_value() == 1);
	return axiom_variables[time][fact.get_variable().get_id()].back();
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
	reset_number_of_clauses();
	void* solver = ipasir_init();

	log << "Building SAT formula for plan length " << currentLength << endl;

	map<string,int> clauseCounter;
	map<string,int> variableCounter;
	int curClauseNumber = 0;
#define registerClauses(NAME) clauseCounter[NAME] += get_number_of_clauses() - curClauseNumber; curClauseNumber = get_number_of_clauses();


	map<int,int> numberOfAxiomLayerVariablesPerDerived;
	for (AxiomSCC & scc : axiomSCCsInTopOrder){
		if (scc.sizeOne) scc.numberOfAxiomLayers = 1;

		// nasty case. We can't optimise here
		if (scc.sizeOne || scc.fullComputationRequired){
			for (int v : scc.variables){
				numberOfAxiomLayerVariablesPerDerived[v] = scc.numberOfAxiomLayers;
			}
		} else {
			for (int v : scc.variables)
				numberOfAxiomLayerVariablesPerDerived[v] = 1;
		}
	}



	//int numberOfAxiomLayers = 30;

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
			variableCounter["operator"]++;
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
				variableCounter["facts"]++;
				DEBUG(capsule.registerVariable(factVar,"fa " + pad_int(var) + "=" + pad_int(val) + " @ " + pad_int(time) + " " + varProxy.get_name() + "=" + varProxy.get_fact(val).get_name()));
			}
		}
	}

	for (int time = 0; time <= currentLength; time++){
		axiom_variables[time].resize(task_proxy.get_variables().size());
		for (size_t var = 0; var < task_proxy.get_variables().size(); var++){
			VariableProxy varProxy = task_proxy.get_variables()[var];
			if (!varProxy.is_derived()) continue;

			axiom_variables[time][var].resize(numberOfAxiomLayerVariablesPerDerived[var] + 1);
			for (int layer = 0; layer <= numberOfAxiomLayerVariablesPerDerived[var]; layer++){
				// variables from axioms must be "boolean"
				assert(varProxy.get_domain_size() == 2);
				
				int factVar = capsule.new_variable();
				variableCounter["axioms"]++;
				axiom_variables[time][var][layer] = factVar;
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
		map<FactPair, map<set<int>,vector<int>>> conditionBuffer;
		map<FactPair, map<set<int>, int>> conditionVariable;
		for (size_t op = 0; op < task_proxy.get_operators().size(); op ++){
			int opvar = operator_variables[time][op];
			OperatorProxy opProxy = task_proxy.get_operators()[op];

			map<int,int> preMap;

			// Preconditions
			PreconditionsProxy precs = opProxy.get_preconditions();
			for (size_t pre = 0; pre < precs.size(); pre++){
				FactProxy fact = precs[pre];
				int fact_var = get_fact_var(time,fact);
				preMap[fact.get_variable().get_id()] = fact.get_value();
				
				implies(solver,opvar,fact_var);
			}
			registerClauses("preconditions");

			// Effect
			EffectsProxy effs = opProxy.get_effects();
			for (size_t eff = 0; eff < effs.size(); eff++){
				EffectProxy thisEff = effs[eff];
				int eff_fact_var = get_fact_var(time+1,thisEff.get_fact());

				// gather the conditions of the conditional effect in a set (could be a vector ...)
				set<int> conditions;
				EffectConditionsProxy cond = thisEff.get_conditions();
				for (size_t i = 0; i < cond.size(); i++)
					conditions.insert(get_fact_var(time, cond[i]));

				int thisCausation;

				if (conditions.size() == 0){
					thisCausation = opvar;
				} else {
					// operator that has exactly the same condition for the same effect
					if (conditionBuffer[thisEff.get_fact().get_pair()].count(conditions)){
						// reuse the causation variable
						thisCausation = conditionVariable[thisEff.get_fact().get_pair()][conditions];
						conditionBuffer[thisEff.get_fact().get_pair()][conditions].push_back(opvar);
					} else { 
						thisCausation = capsule.new_variable();
						conditionVariable[thisEff.get_fact().get_pair()][conditions] = thisCausation;
						conditionBuffer[thisEff.get_fact().get_pair()][conditions].push_back(opvar);
						
						variableCounter["facts"]++;
						DEBUG(capsule.registerVariable(thisCausation,"ce " + pad_int(op) + " " + pad_int(eff) +" @ " + pad_int(time)));
						
						for (int required : conditions)
							implies(solver,thisCausation,required);
						registerClauses("frame axioms effect causation");
					}
				}

				// adding effect	
				conditions.insert(opvar);
				andImplies(solver,conditions,eff_fact_var);
				achieverVars[time][thisEff.get_fact().get_variable().get_id()]
					[thisEff.get_fact().get_value()].push_back(thisCausation);

				// implicit deleting effects, i.e. delete any value of the variable that is set
				for (int val = 0; val < thisEff.get_fact().get_variable().get_domain_size(); val++){
					if (val == thisEff.get_fact().get_value()) continue;
					if (preMap.count(thisEff.get_fact().get_variable().get_id()) &&
						preMap[thisEff.get_fact().get_variable().get_id()] != val)
						continue;
			
					int deletedFact = fact_variables[time+1][thisEff.get_fact().get_variable().get_id()][val];
					andImplies(solver,conditions,-deletedFact);
					deleterVars[time][thisEff.get_fact().get_variable().get_id()]
						[val].push_back(thisCausation);
				}
				registerClauses("effects");
			}
			
		}
		// selectable operators for frame axioms
		for (auto [fp, m] : conditionBuffer){
			for (auto [con, opVars] : m){
				int conditionVar = conditionVariable[fp][con];
				impliesOr(solver,conditionVar,opVars);
			}
		}
		registerClauses("frame axioms effect causation");
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
	registerClauses("frame axioms");

	// 4. Evaluation of axioms
	// assumption here is: the variables in fact_variables are the ones
	// that are supposed to be used for preconditions
	AxiomsProxy axioms = task_proxy.get_axioms();
	for (int time = 0; time <= currentLength; time++){

		// final value of the axioms implies their value for the next layer
		for (size_t var = 0; var < task_proxy.get_variables().size(); var++){
			if (task_proxy.get_variables()[var].is_derived()){
				// if axiom evaluates to true, its value 1 is the correct one
				implies(solver,axiom_variables[time][var].back(),fact_variables[time][var][1]);
				// if axiom evaluates to false, its value 0 is the correct one
				implies(solver,-axiom_variables[time][var].back(),fact_variables[time][var][0]);
			}
		}
		registerClauses("axioms finalisation");


		// actual evaluation of axioms

		for (AxiomSCC & scc : axiomSCCsInTopOrder){
			set<int> sset(scc.variables.begin(), scc.variables.end());
			if (scc.sizeOne) scc.numberOfAxiomLayers = 1;

			// nasty case. We can't optimise here
			if (scc.sizeOne || scc.fullComputationRequired){
				// initially all axioms are false
				for (int var : scc.variables)
					if (task_proxy.get_variables()[var].is_derived()){
						assertNot(solver,axiom_variables[time][var][0]);
					}
				registerClauses("axioms initialisation");

				for (int layer = 0; layer < scc.numberOfAxiomLayers; layer++){
					vector<vector<int>> causeVariables (task_proxy.get_variables().size());
					for (int sccvar : scc.variables){
						for (OperatorProxy opProxy : achievers_per_derived[sccvar]){

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
								if (fact.get_variable().is_derived()){
									// the variables that is changed will require value 0
									if (fact.get_variable().get_id() == eff_var){
										assert(fact.get_value() == 0);
										continue;	
									}

									assert(fact.get_value() == 1);
									int fact_var;
									if (sset.count(fact.get_variable().get_id()))
										fact_var = get_axiom_var(time,layer,fact);
									else
										fact_var = get_last_axiom_var(time,fact);
									conditions.insert(fact_var);
								} else {
									int fact_var = get_fact_var(time,fact);
									conditions.insert(fact_var);
								}
							}
							
							
							andImplies(solver,conditions,eff_fact_var);
							registerClauses("axioms evaluation");


							assert(conditions.size() > 0);
							if (conditions.size() == 1){
								causeVariables[eff_var].push_back(*conditions.begin());
							} else {
								int intermediateCausation = capsule.new_variable();
								variableCounter["axiom causation"]++;
								causeVariables[eff_var].push_back(intermediateCausation);
								DEBUG(capsule.registerVariable(intermediateCausation,"ca " + pad_int(opProxy.get_id()) + " @ " + pad_int(time) + " " + pad_int(layer)));
								for (int required : conditions)
									implies(solver, intermediateCausation, required);
								registerClauses("axioms intermediate causation");
							}
						}
					}

					for (int var : scc.variables){
						assert(task_proxy.get_variables()[var].is_derived());
						assert(axiom_variables[time][var].size() > layer+1);
						int eff_var = axiom_variables[time][var][layer+1];
						impliesOr(solver,eff_var,causeVariables[var]);
						assert(causeVariables[var].size());
					}
					registerClauses("axioms causation");
				}
			} else if (scc.isOfImplicationType || scc.isDependentOnOneVariableInternally){
				// implication type or one-dependent SCCs can be evaluated in two steps
				// 1. We need to correctly determine the values coming into the SCC
				
				vector<vector<int>> causeVariablesLayer0 (task_proxy.get_variables().size());
				for (int sccvar : scc.variables){
					for (OperatorProxy opProxy : achievers_per_derived[sccvar]){

						// Effect
						EffectsProxy effs = opProxy.get_effects();
						assert(effs.size() == 1);
						EffectProxy thisEff = effs[0];
						assert(thisEff.get_fact().get_value() == 1);
						assert(thisEff.get_fact().get_variable().is_derived());
						int eff_var = thisEff.get_fact().get_variable().get_id();
						int eff_fact_var = get_axiom_var(time,0,thisEff.get_fact());

						set<int> conditions;
						// Preconditions
						PreconditionsProxy precs = opProxy.get_preconditions();
						vector<FactProxy> conds;
					
						for (size_t pre = 0; pre < precs.size(); pre++)
							conds.push_back(precs[pre]);
						
						EffectConditionsProxy cond = thisEff.get_conditions();
						for (size_t i = 0; i < cond.size(); i++)
							conds.push_back(cond[i]);

						// check whether the axiom is internal to the SCC
						bool internalAxiom = false;
						for (FactProxy & fact : conds){
							if (fact.get_variable().is_derived()){
								// the variables that is changed will require value 0
								if (fact.get_variable().get_id() == eff_var){
									assert(fact.get_value() == 0);
									continue;	
								}

								assert(fact.get_value() == 1);
								int fact_var;
								if (sset.count(fact.get_variable().get_id()))
									internalAxiom = true;
								else
									fact_var = get_last_axiom_var(time,fact);
								conditions.insert(fact_var);
							} else {
								int fact_var = get_fact_var(time,fact);
								conditions.insert(fact_var);
							}
						}

						// internal axioms cannot make facts at layer 0 true.
						if (internalAxiom) continue;
						
						andImplies(solver,conditions,eff_fact_var);
						registerClauses("axioms evaluation");

						assert(conditions.size() > 0);
						if (conditions.size() == 1){
							causeVariablesLayer0[eff_var].push_back(*conditions.begin());
						} else {
							int intermediateCausation = capsule.new_variable();
							variableCounter["axiom causation"]++;
							causeVariablesLayer0[eff_var].push_back(intermediateCausation);
							DEBUG(capsule.registerVariable(intermediateCausation,"ca " + pad_int(opProxy.get_id()) + " @ " + pad_int(time) + " " + pad_int(0)));
							for (int required : conditions)
								implies(solver, intermediateCausation, required);
							registerClauses("axioms intermediate causation");
						}
					}
				}

				for (int var : scc.variables)
					if (task_proxy.get_variables()[var].is_derived()){
						int eff_var = axiom_variables[time][var][0];
						impliesOr(solver,eff_var,causeVariablesLayer0[var]);
					}
				registerClauses("axioms causation");


				// 2. Internal work
				if (scc.isOfImplicationType) {
					for (size_t varOffset = 0; varOffset < scc.variables.size(); varOffset++){
						int var = scc.variables[varOffset];
						for (size_t varOffsetTo : scc.directTransitiveImplications[varOffset]){
							int varTo = scc.variables[varOffsetTo];
							implies(solver,axiom_variables[time][var][0], axiom_variables[time][varTo][1]);
						}
					}
					registerClauses("axioms evaluation");

					for (size_t varOffsetTo = 0; varOffsetTo < scc.variables.size(); varOffsetTo++){
						int varTo = scc.variables[varOffsetTo];
						vector<int> causeVariables;
						for (size_t varOffset : scc.directTransitiveCauses[varOffsetTo]){
							int var = scc.variables[varOffset];
							causeVariables.push_back(axiom_variables[time][var][0]);
						}
						impliesOr(solver,axiom_variables[time][varTo][1], causeVariables);
					}
					registerClauses("axioms causation");


				} else if (scc.isDependentOnOneVariableInternally){
					VariableProxy varProxy = task_proxy.get_variables()[scc.dependingVariable];
					// iterate over the possible values of the variable and implement the pattern for each one
					for (int value = 0; value < varProxy.get_domain_size(); value++){
						for (size_t varOffset = 0; varOffset < scc.variables.size(); varOffset++){
							int var = scc.variables[varOffset];
							for (size_t varOffsetTo : scc.guardedTransitiveImplications[value][varOffset]){
								int varTo = scc.variables[varOffsetTo];
								// if initial value and dependent one -> final value
								impliesAnd(solver,axiom_variables[time][var][0],
											fact_variables[time][scc.dependingVariable][value],
											axiom_variables[time][varTo][1]);
							}
						}
						registerClauses("axioms evaluation");

						for (size_t varOffsetTo = 0; varOffsetTo < scc.variables.size(); varOffsetTo++){
							int varTo = scc.variables[varOffsetTo];
							vector<int> causeVariables;
							for (size_t varOffset : scc.guardedTransitiveCauses[value][varOffsetTo]){
								int var = scc.variables[varOffset];
								causeVariables.push_back(axiom_variables[time][var][0]);
							}
							andImpliesOr(solver,axiom_variables[time][varTo][1],
									fact_variables[time][scc.dependingVariable][value],
									causeVariables);
						}
						registerClauses("axioms causation");

					}
				}	
			} else {
				assert(false); // the SCC must have *some* type
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
	registerClauses("init");

	GoalsProxy goals = task_proxy.get_goals();
	for (size_t i = 0; i < goals.size(); i++){
		if (goals[i].get_variable().is_derived()){
			log << "Derived GOAL " << goals[i].get_variable().get_id() << " " << goals[i].get_value() << " " << get_last_axiom_var(currentLength,goals[i]) << endl;
			assertYes(solver,get_last_axiom_var(currentLength,goals[i]));
		
		} else {
			log << "Regular GOAL " << goals[i].get_variable().get_id() << " " << goals[i].get_value() << " " << get_fact_var(currentLength,goals[i]) << endl;
			assertYes(solver,get_fact_var(currentLength,goals[i]));
		}
	}
	registerClauses("goal");
	
	// 6. State Mutexes
	for (int time = 0; time <= currentLength; time++){
		for (size_t var = 0; var < task_proxy.get_variables().size(); var++){
			atMostOne(solver,capsule,fact_variables[time][var]);
			if (forceAtLeastOneAction) atLeastOne(solver,capsule,fact_variables[time][var]);
		}
	}
	registerClauses("state mutexes");
	
	// 7. Action Control
	// currently the most simple encoding: only one action at a time
	for (int time = 0; time < currentLength; time++){
		atMostOne(solver,capsule,operator_variables[time]);
		atLeastOne(solver,capsule,operator_variables[time]);
	}
	registerClauses("action control");


	//DEBUG(capsule.printVariables());


	// print variable and clause statistics
	log << "Variables" << setw(23) << setfill(' ') << "total: " << setw(8) << setfill(' ') << capsule.number_of_variables << endl;
	for (auto [a,b] : variableCounter)
		log << setw(30) << setfill(' ') << a << ": " << setw(8) << setfill(' ') << b << endl;
	log << "Clauses" << setw(25) << setfill(' ') << "total: " << setw(8) << setfill(' ') << get_number_of_clauses() << endl;
	for (auto [a,b] : clauseCounter)
		log << setw(30) << setfill(' ') << a << ": " << setw(8) << setfill(' ') << b << endl;



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
    
		//for(int time = 0; time <= currentLength; time++){
		//	for (size_t var = 0; var < task_proxy.get_variables().size(); var++){
		//		if (var >= 2) continue;
		//		VariableProxy varProxy = task_proxy.get_variables()[var];
		//		for (int val = 0; val < varProxy.get_domain_size(); val++){
		//			int factVar = fact_variables[time][var][val];
		//			if (ipasir_val(solver,factVar) > 0){
		//				log << "time " << time << " " <<varProxy.get_name() << "=" <<  varProxy.get_fact(val).get_name() << endl;
		//			}
		//		}
		//	}
		//}

	    OperatorsProxy operators = task_proxy.get_operators();
	    State cur = state_registry.get_initial_state();
	    vector<State> visited_states;
		visited_states.push_back(cur);
	
	    for (size_t i = 0; i < plan.size(); ++i) {
	        cur = state_registry.get_successor_state(cur, operators[plan[i]]);
	        visited_states.push_back(cur);
	    }

		//AxiomEvaluator &axiom_evaluator = g_axiom_evaluators[task_proxy];
		for (size_t i = 0; i < visited_states.size(); ++i){
			State & s = visited_states[i];
			// TODO it seems that the state registry evaluates axioms for us
    		//s.unpack();
			//vector<int> upack = s.get_unpacked_values();
			//axiom_evaluator.evaluate(upack);
			//s = State(*task,move(upack));
			s.unpack();

			for (size_t j = 0; j < s.size(); ++j){
				int var = get_fact_var(i,s[j]);
				assert(ipasir_val(solver,var));
			}
		}
    	
		reverse(plan.begin(), plan.end());
		reverse(visited_states.begin(), visited_states.end());
		task->reconstruct_plan_if_necessary(plan,visited_states);
		reverse(plan.begin(), plan.end());
    
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
