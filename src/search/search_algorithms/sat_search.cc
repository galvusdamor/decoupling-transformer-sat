#include <cmath>
#include <iomanip>
#include <fstream>
#include <sstream>
#include <queue>
#include <stack>

#include "sat_search.h"

#include "../plugins/options.h"

#include "../algorithms/sccs.h"

#include "../utils/logging.h"
#include "../utils/markup.h"
#include "../utils/rng.h"

#include "../tasks/root_task.h"
#include "../tasks/decoupled_root_task.h"
#include "../task_utils/task_properties.h"

#include "../decoupling/factoring.h"

#include "sat_encoder.h"
#include "ipasir.h"

using namespace std;


sat_search::SATSearch* kissatSearch;
int kissatCurrentLength;
utils::RandomNumberGenerator rng;

struct sat_fact {
	int sat_var;
	int time;
	FactPair fact;
	int priorityTime;

	sat_fact(FactPair p) : fact(p){}

	bool operator<(const sat_fact& a) const {
		if (priorityTime > a.priorityTime) return true;
		if (priorityTime < a.priorityTime) return false;
		return fact < a.fact;
		//return sat_var > a.sat_var;
	}

};

extern "C" {

typedef struct kissat kissat;
unsigned kissat_import_literal (kissat * solver, int elit);
int kissat_set_option (kissat * solver, const char *name, int new_value);


void kissat_set_external_decision_function(unsigned (*function) (struct kissat *, int * ));
int kissat_get_truth_of_external_var(kissat * solver, int external_var);


sat_fact get_sat_fact_for(struct kissat * solver,FactPair fact, int time, bool &isStaticallyTrue, bool &isStaticallyFalse){
	assert(time >= 0); // only facts after the initial state can be branched on.
	isStaticallyTrue = false;
	isStaticallyFalse = false;
	sat_fact f(fact);
	f.time = time;
	
	// statically true check
	if (kissatSearch->statically_true_derived_predicates.count(fact.var) == 1){
		if (fact.value == 1){
			isStaticallyTrue = true;
		} else {
			isStaticallyFalse = true;
		}
		return f;
	}

	
	if (kissatSearch->task_proxy.get_variables()[fact.var].is_derived()){
		f.sat_var = kissatSearch->get_last_axiom_var(time,fact);
	} else {
		f.sat_var = kissatSearch->get_fact_var(time,fact);
	}

	// compute the priority time for this fact
	f.priorityTime = time - 1;
	while (f.priorityTime > 0){
		int prev_time_var = 0;
		if (kissatSearch->task_proxy.get_variables()[fact.var].is_derived()){
			prev_time_var = kissatSearch->get_last_axiom_var(f.priorityTime-1,fact);
		} else {
			prev_time_var = kissatSearch->get_fact_var(f.priorityTime-1,fact);
		}
	
		int var_truth = kissat_get_truth_of_external_var(solver,prev_time_var);
		if (var_truth == 2) {
			cout << "kissat_error on var " << prev_time_var << " is " << var_truth << endl;
			exit(-1);
		}

		if (var_truth != 1) break;

		f.priorityTime--;
	}


	return f;
}



unsigned rintanens_p(struct kissat * solver, int * made_decision){
	//cout << "========================================" << endl << "I am in FD" << endl;

	set<sat_fact> inQueue;
	priority_queue<sat_fact> q;
	//stack<sat_fact> q;

	GoalsProxy goals = kissatSearch->task_proxy.get_goals();
	for (size_t i = 0; i < goals.size(); i++){
		bool isTrue, isFalse;
		sat_fact f = get_sat_fact_for(solver,goals[i].get_pair(),kissatCurrentLength,isTrue,isFalse);
		if (isTrue) continue;
		if (isFalse) assert(false);

		q.push(f);
		inQueue.insert(f);
	}

	unordered_set<int> X;

	int first_found_action = -1;

	while (q.size() && X.size() < 1){
		//cout << "Taking one Fact" << endl;
		sat_fact f = q.top();
		q.pop();

		// DFS style search for a supporter
		int t = f.time - 1;
		bool found = false;
		do {
			//cout << "LOOP START FOR " << t << endl;
			for (const auto & [op, conditions] : kissatSearch->addingActions[f.fact]){
				//cout << "ACC " << t << " (" << kissatSearch->operator_variables.size() << ")" << endl;
				//cout << "\t " << op << " (" << kissatSearch->operator_variables[t].size() << ")" << endl;
				int op_var = kissatSearch->operator_variables[t][op];
				int op_truth = kissat_get_truth_of_external_var(solver,op_var);
				if (op_truth == 2) {
					cout << "kissat_error on op " << op << " -> " << op_var << " is " << op_truth << endl;
					exit(-1);
				}

				// treat eliminated variables as if they would be true.
				if (op_truth == 1 || op_truth == -2){
					// this action is to be chosen, so all of its preconditions must be true
					// first check if one of them is known to be false -> this can happen for conditions of conditional effects
					
					if (first_found_action == -1){
						first_found_action = t;
					} else if (t >= first_found_action){
						// abort there and exit the loop (we'll drain the queue)
						found = true;
						break;
					}
					vector<sat_fact> pre_facts;
					bool oneFalse = false;
					for (const FactPair & f : conditions){
						bool isTrue, isFalse;
						sat_fact sf = get_sat_fact_for(solver,f,t,isTrue,isFalse);
						if (isFalse){ oneFalse = true; break; }
						if (isTrue) continue;
						pre_facts.push_back(sf);
					}
					if (oneFalse) continue; // this is not the right operator
					
					if (t > 0)
						for (const sat_fact & sf : pre_facts){
							if (inQueue.count(sf)) continue;
							q.push(sf);
							inQueue.insert(sf);
						}
					found = true;
					break;
				}
			}
			// we found the achiever
			if (found) break;
			
			// no achiever found at time t
			bool isTrue, isFalse;
			sat_fact sf = get_sat_fact_for(solver,f.fact,t,isTrue,isFalse);
			assert(isFalse == false);
			assert(isTrue == false);
			
			int f_truth = kissat_get_truth_of_external_var(solver,sf.sat_var);
			if (f_truth == 2) {
				cout << "kissat_error on " << sf.fact.var << "=" << sf.fact.value << " -> " << sf.sat_var << " is " << f_truth << endl;
				exit(-1);
			}

			//cout << "Truth status of this fact: " << sf.sat_var << " is " << f_truth << endl; 

			// fact is true, we don't have to do anything.
			if (f_truth == 1){
				break;
			}


			if (f_truth == -1){
				// try to make this fact true here
				for (const auto & [op, conditions] : kissatSearch->addingActions[f.fact]){
					int op_var = kissatSearch->operator_variables[t][op];
					int op_truth = kissat_get_truth_of_external_var(solver,op_var);
					if (op_truth == 2) {
						cout << "kissat_error on op " << op << " -> " << op_var << " is " << op_truth << endl;
						exit(-1);
					}

					//cout << "Achiever " << op << " Truth " << op_truth << endl;
					// operator cannot be true, otherwise we would have found it before
					if (op_truth == -1 || op_truth == -2) continue; // either false or eliminated

					// this action is to be chosen, so all of its preconditions must be true
					// first check if one of them is known to be false -> this can happen for conditions of conditional effects
					vector<sat_fact> pre_facts;
					bool oneFalse = false;
					for (const FactPair & f : conditions){
						bool isTrue, isFalse;
						sat_fact sf = get_sat_fact_for(solver,f,t,isTrue,isFalse);
						if (isFalse){ oneFalse = true; break; }
						if (isTrue) continue;
						pre_facts.push_back(sf);
					}
					if (oneFalse) continue; // this is not the right operator
					
					X.insert(op_var); // try to apply this operator
				
					// searching below the precondition is only possible if this is not an action at time 0	
					if (t > 0)
						for (const sat_fact & sf : pre_facts){
							if (inQueue.count(sf)) continue;
							q.push(sf);
							inQueue.insert(sf);
						}
					found = true;
				}
			}

			// look for the previous time step
			t--;
			//cout << "END OF LOOP " << t << " cond " << (found == false) << " and " << (t >= 0) << endl; 
		} while (found == false && t >= 0);
	}

	//cout << "Found " << X.size() << " facts to branch on:";
	//for (const int & x : X) cout << " " << x;
	//cout << endl;

	if (X.size() == 0){
		// advice is to keep truth values
		//cout << "No more advice" << endl;
		// no decision was made
		*made_decision = 0;
		return 0;
	}
	int random = rng.random(X.size());
	vector<int> XX(X.begin(),X.end());

	//exit(0);
	*made_decision = 1;
	return XX[random];
}



};

namespace sat_search {
SATSearch::SATSearch(const plugins::Options &opts)
    : SearchAlgorithm(opts),
	planLength(opts.get<int>("plan_length")),
	lengthIteration(opts.get<int>("length_iteration")),
	startLength(opts.get<int>("start_length")),
	multiplier(opts.get<double>("multiplier")),
	disablingThreshold(opts.get<int>("disabling_threshold")),
	aboveThresholdGroupJoining(opts.get<bool>("join_groups_above_threshold")),
	useRintanensP(opts.get<bool>("use_p"))
	{

	switch (opts.get<int>("encoding")){
		case 0: existsStep = false; break;
		case 2: existsStep = true; agressiveDecoupledExistsStep = false; break;
		case 3: existsStep = true; agressiveDecoupledExistsStep = true; break;
		default:
			log << "Error: encoding No " << opts.get<int>("encoding") << " is not supported" << endl;
			exit(-1);
	}

	forceAtLeastOneAction = true;
	
	currentLength = 1;
	if (planLength != -1) currentLength = planLength;

	if (lengthIteration != -1){
		currentLength = planLength = int(0.5 + startLength * pow(multiplier, lengthIteration));
		forceAtLeastOneAction = false;
	}

	// check if this a decoupled root task

	if (dynamic_pointer_cast<tasks::DecoupledRootTask>(task)){
		log << "SAT encoding a decoupled root task" << endl;
		decouplingMode = true;
		decoupledTask = dynamic_pointer_cast<tasks::DecoupledRootTask>(task);
	}
}

// TODO copied from pruning/stubborn_sets_action_centric.h
// Relies on both fact sets being sorted by variable.
static bool contain_conflicting_fact(const vector<FactPair> &facts1,
                                     const vector<FactPair> &facts2) {
    auto facts1_it = facts1.begin();
    auto facts2_it = facts2.begin();
    while (facts1_it != facts1.end() && facts2_it != facts2.end()) {
        if (facts1_it->var < facts2_it->var) {
            ++facts1_it;
        } else if (facts1_it->var > facts2_it->var) {
            ++facts2_it;
        } else {
            if (facts1_it->value != facts2_it->value)
                return true;
            ++facts1_it;
            ++facts2_it;
        }
    }
    return false;
}

bool SATSearch::can_be_executed_in_same_state(int op1_no, int op2_no){
    return !contain_conflicting_fact(sorted_op_preconditions[op1_no],
                                    			   sorted_op_preconditions[op2_no]);
}

bool SATSearch::have_actions_unconflicting_effects(int op1_no, int op2_no){
    return !contain_conflicting_fact(sorted_op_effects[op1_no],
                                    			   sorted_op_effects[op2_no]);
}


void SATSearch::initialize() {
	log << "conducting SAT search"
		<< " for plan length: " << (planLength==-1?"all":to_string(planLength))
        << endl;

	// detect leaf operators
	is_leaf_operator.resize(task_proxy.get_operators().size());
	size_t number_of_non_leaf_operators = task_proxy.get_operators().size();

	if (decouplingMode){
		for (size_t leaf_op_id = 0; leaf_op_id < decoupledTask->get_separate_leaf_effect_operators().size(); leaf_op_id++){
			OperatorID op_id = decoupledTask->get_separate_leaf_effect_operators()[leaf_op_id];
			// this is a leaf operator
			is_leaf_operator[op_id.get_index()] = true;
			number_of_non_leaf_operators--;
		}
	}
	
	//for (size_t op = 0; op < task_proxy.get_operators().size(); op ++){
	//	log << is_leaf_operator[op] << " " << task_proxy.get_operators()[op].get_name() << endl;
	//}


	//achiever.resize(task_proxy.get_variables().size());
	//deleter.resize(task_proxy.get_variables().size());
	//for (size_t var = 0; var < task_proxy.get_variables().size(); var++){
	//	VariableProxy varProxy = task_proxy.get_variables()[var];
	//	achiever[var].resize(varProxy.get_domain_size());
	//	deleter[var].resize(varProxy.get_domain_size());
	//}

	//for (size_t op = 0; op < task_proxy.get_operators().size(); op ++){
	//	OperatorProxy opProxy = task_proxy.get_operators()[op];
	//	if (is_leaf_operator[op]) continue;

	//	// Effect
	//	EffectsProxy effs = opProxy.get_effects();
	//	for (size_t eff = 0; eff < effs.size(); eff++){
	//		EffectProxy thisEff = effs[eff];

	//		achiever[thisEff.get_fact().get_variable().get_id()][thisEff.get_fact().get_value()].push_back(op);

	//		// implicit deleting effects, i.e. delete any value of the variable that is set
	//		for (int val = 0; val < thisEff.get_fact().get_variable().get_domain_size(); val++){
	//			if (val == thisEff.get_fact().get_value()) continue;
	//	
	//			deleter[thisEff.get_fact().get_variable().get_id()][val].push_back(op);
	//		}
	//	}
	//}


	derived_implication.clear();
	derived_implication.resize(task_proxy.get_variables().size());
	pos_derived_implication.clear();
	pos_derived_implication.resize(task_proxy.get_variables().size());
	neg_derived_implication.clear();
	neg_derived_implication.resize(task_proxy.get_variables().size());
	achievers_per_derived.resize(task_proxy.get_variables().size());
	derived_entry_edges.clear();

	// find statically true DPs
	AxiomsProxy axioms = task_proxy.get_axioms();
	bool newTrueFound = true;
	while (newTrueFound){
		newTrueFound = false;
		for (size_t ax = 0; ax < axioms.size(); ax++){
			OperatorProxy opProxy = axioms[ax];

			// Effect
			EffectsProxy effs = opProxy.get_effects();
			assert(effs.size() == 1);
			EffectProxy thisEff = effs[0];
			assert(thisEff.get_fact().get_variable().is_derived());
			int eff_var = thisEff.get_fact().get_variable().get_id();
			if (statically_true_derived_predicates.count(eff_var)) continue;
			assert(thisEff.get_fact().get_value() == 1);
			
			// Preconditions
			PreconditionsProxy precs = opProxy.get_preconditions();
			vector<FactProxy> conds;
		
			for (size_t pre = 0; pre < precs.size(); pre++)
				conds.push_back(precs[pre]);
			
			EffectConditionsProxy cond = thisEff.get_conditions();
			for (size_t i = 0; i < cond.size(); i++)
				conds.push_back(cond[i]);

			int number_of_true_conditions = 0;
			bool inApplicable = false;
			for (FactProxy & fact : conds){
				if (fact.get_variable().is_derived() && fact.get_variable().get_id() == eff_var){
					assert(fact.get_value() == 0);
					continue;	
				}
				if (statically_true_derived_predicates.count(fact.get_variable().get_id())){
					if (fact.get_value()) continue;	// condition is always true
					inApplicable = true;
					break;
				}
				
				number_of_true_conditions++;
			}
			if (inApplicable) continue;

			if (number_of_true_conditions == 0){
				DEBUG(log << "Found statically true derived predicate: " << task_proxy.get_variables()[eff_var].get_name() << endl);
				statically_true_derived_predicates.insert(eff_var);
				newTrueFound = true;
			}
		}
	}
	log << "Found statically true derived predicates: " << statically_true_derived_predicates.size() << endl;

	// building the derived predicate dependency graph
	for (size_t ax = 0; ax < axioms.size(); ax++){
		OperatorProxy opProxy = axioms[ax];

		// Effect
		EffectsProxy effs = opProxy.get_effects();
		assert(effs.size() == 1);
		EffectProxy thisEff = effs[0];
		assert(thisEff.get_fact().get_variable().is_derived());
		
		int eff_var = thisEff.get_fact().get_variable().get_id();
		assert(thisEff.get_fact().get_value() == 1);
		achievers_per_derived[eff_var].push_back(opProxy);

		// statically true DP, it does not depend on anything even if there are axioms.
		if (statically_true_derived_predicates.count(eff_var)) continue;

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

				//assert(fact.get_value() == 1);
				int fact_var = fact.get_variable().get_id();
				derived_implication[fact_var].push_back(eff_var);

				if (fact.get_value() == 1)
					pos_derived_implication[fact_var].push_back(eff_var);
				else
					neg_derived_implication[fact_var].push_back(eff_var);
			} else {
				derived_entry_edges[fact.get_pair()].push_back(eff_var);
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
	log << "Number of SCCs " << derived_sccs.size() - statically_true_derived_predicates.size() << endl;


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
			// this will include statically true DPs.
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
				EffectProxy thisEff = effs[0];
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
		//log << "members:";
		//for (int d : sset) log << d << " ";
		//log << endl;
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


	if (existsStep)
		set_up_exists_step();
	else
		set_up_single_step();

	assert(global_action_ordering.size() == number_of_non_leaf_operators);
}

void SATSearch::set_up_single_step() {
	for (size_t op = 0; op < task_proxy.get_operators().size(); op++)
		if (!is_leaf_operator[op])
			global_action_ordering.push_back(op);
}


// mode = true: causing fact has become *true*
// mode = false: causing fact has become *false*
void SATSearch::axiom_dfs(int var, set<int> & posReachable, set<int> & negReachable, bool mode){
	if (mode){
		// causing fact has become true, this means the DP could turn true
		if (posReachable.count(var)) return;
		posReachable.insert(var);

		// search for all axioms in which this var is contained positively. They could also turn true
		for(int & succ : pos_derived_implication[var])
			axiom_dfs(succ,posReachable, negReachable, true);
		
		// search for all axioms in which this var is contained negatively. They could turn false
		for(int & succ : neg_derived_implication[var])
			axiom_dfs(succ,posReachable, negReachable, false);

	} else {
		// causing fact has become false, this means the DP could turn false
		if (negReachable.count(var)) return;
		negReachable.insert(var);

		// search for all axioms in which this var is contained positively. They could also turn false
		for(int & succ : pos_derived_implication[var])
			axiom_dfs(succ,posReachable, negReachable, false);
		
		// search for all axioms in which this var is contained negatively. They could turn true
		for(int & succ : neg_derived_implication[var])
			axiom_dfs(succ,posReachable, negReachable, true);
	}
}

void SATSearch::set_up_exists_step() {
	
	/////////// Exists step encoding
	// compute the disabling graph
	map<FactPair,set<int>> needingActions;
	map<FactPair,set<int>> deletingActions;
	map<int,vector<int>> affectingLeaf;
	for(size_t op = 0; op < task_proxy.get_operators().size(); op ++){
		if (op % 1000 == 0)
			log << "Disabling Graph Operator " << op << " of " << task_proxy.get_operators().size() << endl;
		// leaf operators are handled differently
		if (is_leaf_operator[op]) continue;


		if (!agressiveDecoupledExistsStep){
			OperatorProxy opProxy = task_proxy.get_operators()[op];
			PreconditionsProxy precs = opProxy.get_preconditions();
			map<int,int> preMap;
			vector<FactPair> fullPreConditions;
			for (size_t pre = 0; pre < precs.size(); pre++){
				FactProxy fact = precs[pre];
				needingActions[fact.get_pair()].insert(op);
				preMap[fact.get_variable().get_id()] = fact.get_value();
				fullPreConditions.push_back(fact.get_pair());
			}

			EffectsProxy effs = opProxy.get_effects();
			for (size_t eff = 0; eff < effs.size(); eff++){
				EffectProxy thisEff = effs[eff];
				// gather the conditions of the conditional effect 
				EffectConditionsProxy cond = thisEff.get_conditions();
				vector<FactPair> conditions;
				vector<FactPair> fullConditions = fullPreConditions;
				for (size_t i = 0; i < cond.size(); i++){
					FactProxy condition = cond[i];
					needingActions[condition.get_pair()].insert(op);
					conditions.push_back(condition.get_pair());
					fullConditions.push_back(condition.get_pair());
				}
				
				addingActions[thisEff.get_fact().get_pair()].push_back({op,fullConditions});

				// setting a fact to true can cause a DP to become true, which in turn means we make a precondition that it has to be false false
				for (int & start : derived_entry_edges[thisEff.get_fact().get_pair()]){
					set<int> posReachable, negReachable;
					axiom_dfs(start,posReachable, negReachable, true); // fact has become true
					// if derived is maintained, it cannot be deleted.
					//if (maintainedFactsByOperator[op].count(FactPair(reach,1)) &&
					//	maintainedFactsByOperator[op].count(FactPair(reach,0))
					//		) continue;
					// if we make the entry point true, any of the connected axioms might become true, so we might delete any negative precondition on it
					for (const int & reach : posReachable){
						deletingActions[FactPair(reach,0)].insert(op);
						addingActions[FactPair(reach,1)].push_back({op,fullConditions});
					}
					for (const int & reach : negReachable){
						deletingActions[FactPair(reach,1)].insert(op);
						addingActions[FactPair(reach,0)].push_back({op,fullConditions});
					}
				}



				// implicit deleting effects, i.e. delete any value of the variable that is set
				for (int val = 0; val < thisEff.get_fact().get_variable().get_domain_size(); val++){
					if (val == thisEff.get_fact().get_value()) continue;
					if (preMap.count(thisEff.get_fact().get_variable().get_id()) &&
						preMap[thisEff.get_fact().get_variable().get_id()] != val)
						continue;
			
					FactPair deletedFact(thisEff.get_fact().get_variable().get_id(),val);
					deletingActions[deletedFact].insert(op);

					if (decouplingMode) continue; // we determine the effects on derived predicates differently

					// treat operators that have an effect that can make a derived fact false as if they were deletes of that fact
					for (int & start : derived_entry_edges[deletedFact]){
						set<int> posReachable, negReachable;
						axiom_dfs(start,posReachable, negReachable, false); // fact has become true
						// if derived is maintained, it cannot be deleted.
						//if (maintainedFactsByOperator[op].count(FactPair(reach,1)) &&
						//	maintainedFactsByOperator[op].count(FactPair(reach,0))
						//		) continue;
						// if we make the entry point true, any of the connected axioms might become true, so we might delete any negative precondition on it
						for (const int & reach : posReachable)
							deletingActions[FactPair(reach,0)].insert(op);
						for (const int & reach : negReachable)
							deletingActions[FactPair(reach,1)].insert(op);
					}
				}
			}



			if (decouplingMode){
				std::shared_ptr<decoupling::Factoring> factoring = decoupledTask->get_factoring();
				int factoring_op_id = decoupledTask->get_original_operator_id(op);
				vector<int> affectedLeafs = factoring->get_operator_pre_and_eff_leaves(OperatorID(factoring_op_id));

				for (int l : affectedLeafs)
					affectingLeaf[l].push_back(op);
			}
		} else {
			assert(decouplingMode);
			assert(agressiveDecoupledExistsStep);
			//log << "Computing Aggressive Disabling in Decoupling Mode." << endl;

			std::shared_ptr<decoupling::Factoring> factoring = decoupledTask->get_factoring();
			TaskProxy originalTask = decoupledTask->get_task_proxy_for_plan_saving();
			int original_op_id = decoupledTask->get_original_operator_id(op);
			//log << "Op " << op << " is originally " << original_op_id << endl;


			OperatorProxy opProxy = originalTask.get_operators()[original_op_id];
			PreconditionsProxy precs = opProxy.get_preconditions();
			map<int,int> preMap;
			for (size_t pre = 0; pre < precs.size(); pre++){
				FactProxy fact = precs[pre];
				needingActions[fact.get_pair()].insert(op);
				//log << "Op " << task_proxy.get_operators()[op].get_name() << " needs " <<
				//	originalTask.get_variables()[fact.get_pair().var].get_name() << " " <<
				//	originalTask.get_variables()[fact.get_pair().var].get_fact(fact.get_pair().value).get_name() << endl;
				preMap[fact.get_variable().get_id()] = fact.get_value();
			}

			// preconditions are potentially also effects as they reduce reachability in the leaf state space.
			map<int,int> effMap;
			for (const auto & [var, val] : preMap)
				// but only leaf preconditions do
				if (factoring->is_leaf_variable(var))
					effMap[var] = val;


			EffectsProxy effs = opProxy.get_effects();
			for (size_t eff = 0; eff < effs.size(); eff++){
				EffectProxy thisEff = effs[eff];
				// gather the conditions of the conditional effect 
				EffectConditionsProxy cond = thisEff.get_conditions();
				for (size_t i = 0; i < cond.size(); i++){
					FactProxy condition = cond[i];
					needingActions[condition.get_pair()].insert(op);
					//log << "Op " << task_proxy.get_operators()[op].get_name() << " needs " <<
					//	originalTask.get_variables()[condition.get_pair().var].get_name() << " " <<
					//	originalTask.get_variables()[condition.get_pair().var].get_fact(condition.get_pair().value).get_name() << endl;
				}
				effMap[thisEff.get_fact().get_variable().get_id()] = thisEff.get_fact().get_value();
			}

			// Any effect that is a leaf variable can potentially make all other leaf variables false.
			// This is due to: the leaf state is not a single state, but a set of reachable states!
			// An effect (or implicit effect due to a precondition!) will cause 

			for (const auto & [var, effVal] : effMap){			
				// implicit deleting effects, i.e. delete any value of the variable that is set
				for (int val = 0; val < originalTask.get_variables()[var].get_domain_size(); val++){
					if (val == effVal) continue;
					// if this variable has a different value in the precondition, it does not delete
					// but this is only true for centre variables
					if (factoring->is_center_variable(var) && preMap.count(var) && preMap[var] != val)
						continue;
			
					FactPair deletedFact(var,val);
					deletingActions[deletedFact].insert(op);
					//log << "Op " << task_proxy.get_operators()[op].get_name() << " deletes " <<
					//	originalTask.get_variables()[deletedFact.var].get_name() << " " <<
					//	originalTask.get_variables()[deletedFact.var].get_fact(deletedFact.value).get_name() << endl;
				}

				if (factoring->is_center_variable(var)) continue;

				// leaf variables also delete all independent variables in the same leaf
				int factor_id = factoring->get_factor(var);

				bool foundMyself = false;
				for (const int & leaf_var : factoring->get_leaf(factor_id)){
					if (leaf_var == var) { foundMyself = true; continue; }
					// if this variable has a defined value by either preconditions or effects, we don't have to generate any extra deleting effects
					if (effMap.count(leaf_var)) continue;
					
					// otherwise all its values might be deleted
					for (int val = 0; val < originalTask.get_variables()[leaf_var].get_domain_size(); val++){
						FactPair deletedFact(leaf_var,val);
						deletingActions[deletedFact].insert(op);
						//log << "Op " << task_proxy.get_operators()[op].get_name() << " deletes " <<
						//	originalTask.get_variables()[deletedFact.var].get_name() << " " <<
						//	originalTask.get_variables()[deletedFact.var].get_fact(deletedFact.value).get_name() << endl;
					}
				}
				assert(foundMyself);
			}
		}
	}



	if (agressiveDecoupledExistsStep == false)
		for (const auto & [_leaf, operators] : affectingLeaf)
			decoupling_at_most_one_groups.insert(operators);

	// prepare data structures needed for compatibility checking
	// TODO: copied from pruning/stubborn_sets.cc maybe create common super class
    sorted_op_preconditions = utils::map_vector<vector<FactPair>>(
        task_proxy.get_operators(), [](const OperatorProxy &op) {
            return utils::sorted<FactPair>(
                task_properties::get_fact_pairs(op.get_preconditions()));
        });

    sorted_op_effects = utils::map_vector<vector<FactPair>>(
        task_proxy.get_operators(), [](const OperatorProxy &op) {
			EffectsProxy effProx = op.get_effects();
			vector<EffectProxy> unconditionalEffects;
			for (EffectProxy eff : effProx)
				if (eff.get_conditions().size() == 0)
					unconditionalEffects.push_back(eff);

            return utils::sorted<FactPair>(
                utils::map_vector<FactPair>(
                    unconditionalEffects,
                    [](const EffectProxy &eff) {return eff.get_fact().get_pair();}));
        });


	// actually compute the edges of the graph
	vector<set<int>> disabling_graph(task_proxy.get_operators().size());
	int number_of_edges_in_disabling_graph = 0;
	int number_refuted_edges_in_disabling_graph = 0;
	unordered_set<int> sequentialOperators;
	set<FactPair> thresholdFacts;
	for (auto [fact, deleters] : deletingActions){
		if (needingActions[fact].size() == 0) {
			thresholdFacts.insert(fact);
			continue;
		}
		int checkSize = deleters.size() * needingActions[fact].size();
		//log << "DG " << fact << " deleter " << deleters.size() << " needers " << needingActions[fact].size() << " checks " << checkSize << endl;
		if (checkSize > disablingThreshold){
			thresholdFacts.insert(fact);
			unordered_set<int> thisSequentialOperators;
			for (int deleter : deleters){
				sequentialOperators.insert(deleter);
				thisSequentialOperators.insert(deleter);
			}
			for (int needer : needingActions[fact]){
				sequentialOperators.insert(needer);
				thisSequentialOperators.insert(needer);
			}

			if (aboveThresholdGroupJoining) continue;

			vector<int> atMostOneGroup;
			for (const int & op : thisSequentialOperators)
				atMostOneGroup.push_back(op);
			// strong constraint - at most one of these can be executed at any time.
			decoupling_at_most_one_groups.insert(atMostOneGroup);

			continue;
		}
		for (int deleter : deleters){
			for (int needer : needingActions[fact]){
				if (deleter == needer) continue;
				// if preconditions are incompatible, action's don't disable each other
				if (!can_be_executed_in_same_state(deleter,needer)) {
					number_refuted_edges_in_disabling_graph++;
					continue;	
				}
				if (!have_actions_unconflicting_effects(deleter,needer)) {
					number_refuted_edges_in_disabling_graph++;
					continue;	
				}

				// deleter disables needer
				if (disabling_graph[deleter].count(needer)) continue; // only count inserted edges once

				disabling_graph[deleter].insert(needer);
				//log << task_proxy.get_operators()[deleter].get_name() << " dis " << task_proxy.get_operators()[needer].get_name() << endl;
				//TaskProxy originalTask = decoupledTask->get_task_proxy_for_plan_saving();
				//log << "\tvia " << originalTask.get_variables()[fact.var].get_name() << " " << originalTask.get_variables()[fact.var].get_fact(fact.value).get_name() << endl;
				number_of_edges_in_disabling_graph++;
			}
		}
	}

	log << "Generated Disabling Graph with " << number_of_edges_in_disabling_graph << " edges." << std::endl;
	double refute_quota = double(number_refuted_edges_in_disabling_graph) / (number_of_edges_in_disabling_graph + number_refuted_edges_in_disabling_graph);
	log << "Refuted " << number_refuted_edges_in_disabling_graph << " edges. Quota: " << fixed << setprecision(5) << refute_quota << std::endl;

	log << "Due to threshold, treating " << sequentialOperators.size() << " of " << task_proxy.get_operators().size() << " operators as sequential." << endl; 
	if (aboveThresholdGroupJoining && sequentialOperators.size()){
		vector<int> atMostOneGroup;
		for (const int & op : sequentialOperators)
			atMostOneGroup.push_back(op);
		// strong constraint - at most one of these can be executed at any time.
		decoupling_at_most_one_groups.insert(atMostOneGroup);
	}


	vector<vector<int>> disabling_graph_vector(task_proxy.get_operators().size());
	for(size_t op = 0; op < task_proxy.get_operators().size(); op++){
		for (const int & op2 : disabling_graph[op]){
			disabling_graph_vector[op].push_back(op2);
		}
	}

	// print to file
	//graph_to_dot(disabling_graph_vector,"disabling.graph");

	vector<vector<int>> disabling_sccs = sccs::compute_maximal_sccs(disabling_graph_vector);
	log << "Disabling Graph contains " << disabling_sccs.size() << " SCCS." << std::endl;
	
	// go backwards though the SCCs
	for (int scc = disabling_sccs.size() - 1; scc >= 0; scc--){
		// artificial leaf operator action
		if (disabling_sccs[scc].size() == 1 && is_leaf_operator[disabling_sccs[scc][0]]) continue;

		//log << "\t SCC No " << scc << endl;
		for (size_t i = 0; i < disabling_sccs[scc].size(); i++){
		//for (int i = disabling_sccs[scc].size() - 1; i >= 0; i--){
			const int & opID = disabling_sccs[scc][i];
			global_action_ordering.push_back(opID);
			//log << "\t\t Operator " << opID << " " << task_proxy.get_operators()[opID].get_name() << endl;
		}
	}

	for (auto & [factPair, _ignore] : deletingActions){
		if (thresholdFacts.count(factPair)) continue; // don't need to generate anything for these
		erasingList[factPair].resize(disabling_sccs.size());
		requiringList[factPair].resize(disabling_sccs.size());
		for (size_t scc = 0; scc < disabling_sccs.size(); scc++){
			if (disabling_sccs[scc].size() == 1) continue; // no disabling possible.
			for (size_t sccOp = 0; sccOp < disabling_sccs[scc].size(); sccOp++){
				int op = disabling_sccs[scc][sccOp];
				// check if this operator has this fact as a precondition
				if (needingActions[factPair].count(op))
					requiringList[factPair][scc].push_back({op, sccOp});

				// check if this operator has this fact as an effect
				if (deletingActions[factPair].count(op))
					erasingList[factPair][scc].push_back({op, sccOp});
			}
		}
	}
	log << "Build enabling disabling lists." << std::endl;
}


void SATSearch::generateChain(void* solver,sat_capsule & capsule,vector<int> & operator_variables,
	const std::vector<std::pair<int, int>>& E,
	const std::vector<std::pair<int, int>>& R){

	// generate chain variables
	map<int,int> chainVars; // we only need them for every R.second value
	for (const auto& [_ignore, i] : R) {
		int chainVar = capsule.new_variable();
		chainVars[i] = chainVar;
		variableCounter["chain"]++;
		// TODO don't have enough information to generate nice names here
		// need: timestep, scc number, fact pair
		DEBUG(capsule.registerVariable(chainVar,"chain R " + to_string(i)));
	}

	// Generate chain restriction for every SCC (f1 in Scala code)
	size_t rpos = 0;
	for (const auto& [opID, i] : E) {
		// search for the position in the R list with the next higher i value
		while (rpos < R.size() && R[rpos].second <= i)
			rpos++;

		if (rpos < R.size())
			implies(solver, operator_variables[opID], chainVars[R[rpos].second]);
	}


	// Process R and generate additional clauses (f2 in Scala code)
	if (R.size() >= 2){
		for (size_t i = 0; i < R.size() - 1; i++) {
			implies(solver, chainVars[R[i].second], chainVars[R[i+1].second]);
		}
	}

	for (const auto& [opID, i] : R) {
		impliesNot(solver,chainVars[i], operator_variables[opID]);
	}
}

void SATSearch::exists_step_restriction(void* solver,sat_capsule & capsule,vector<int> & operator_variables){
	// loop over all fact pairs
	for (auto & [factPair, requiringLists] : requiringList){
		for (size_t scc = 0; scc < requiringLists.size(); scc++){
			assert(erasingList.count(factPair));
			const std::vector<std::pair<int,int>> & E = erasingList[factPair][scc];
			const std::vector<std::pair<int,int>> & R = requiringLists[scc];

			// no chain to be generated
			if (E.size() == 0 || R.size() == 0) continue;
			generateChain(solver,capsule,operator_variables,E,R);
		}
	}

	// decouplings generate at most one constraints on their leafs
	for (const vector<int> & amogroup : decoupling_at_most_one_groups){
		vector<int> amo_operators;
		for (const int & op : amogroup)
			amo_operators.push_back(operator_variables[op]);

		atMostOne(solver,capsule,amo_operators);
	}
}


void SATSearch::print_statistics() const {
    statistics.print_detailed_statistics();
}

int SATSearch::get_fact_var(int time, FactProxy fact){
	assert(statically_true_derived_predicates.count(fact.get_variable().get_id()) == 0);
	return fact_variables[time][fact.get_variable().get_id()][fact.get_value()];
}

int SATSearch::get_axiom_var(int time, int layer, FactProxy fact){
	assert(statically_true_derived_predicates.count(fact.get_variable().get_id()) == 0);
	assert(fact.get_value() == 1);
	return axiom_variables[time][fact.get_variable().get_id()][layer];
}

int SATSearch::get_last_axiom_var(int time, FactProxy fact){
	assert(statically_true_derived_predicates.count(fact.get_variable().get_id()) == 0);
	if (fact.get_value() == 1)
		return axiom_variables[time][fact.get_variable().get_id()].back();
	else
		return -axiom_variables[time][fact.get_variable().get_id()].back();
}


int SATSearch::get_last_axiom_var(int time, FactPair fact){
	if (fact.value == 1)
		return axiom_variables[time][fact.var].back();
	else
		return -axiom_variables[time][fact.var].back();
}

int SATSearch::get_fact_var(int time, FactPair fact){
	return fact_variables[time][fact.var][fact.value];
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

	kissatSearch = this;
	if (useRintanensP)
		kissat_set_external_decision_function(rintanens_p);
	//kissat_set_option((kissat*)solver,"autarky",0);
	//kissat_set_option((kissat*)solver,"xors",0);
	//kissat_set_option((kissat*)solver,"ands",0);
	//kissat_set_option((kissat*)solver,"forward",0);
	//kissat_set_option((kissat*)solver,"eliminate",0);

	log << "Building SAT formula for plan length " << currentLength << endl;

	clauseCounter.clear();
	variableCounter.clear();
	int curClauseNumber = 0;
#define registerClauses(NAME) clauseCounter[NAME] += get_number_of_clauses() - curClauseNumber; curClauseNumber = get_number_of_clauses();


	map<int,int> numberOfAxiomLayerVariablesPerDerived;
	for (AxiomSCC & scc : axiomSCCsInTopOrder){
		if (scc.sizeOne) scc.numberOfAxiomLayers = 1;

		// nasty case. We can't optimise here
		if (scc.fullComputationRequired){
			for (int v : scc.variables){
				numberOfAxiomLayerVariablesPerDerived[v] = scc.numberOfAxiomLayers;
			}
		} else {
			for (int v : scc.variables)
				numberOfAxiomLayerVariablesPerDerived[v] = 1;
		}
	}
	
	DEBUG(log << "Axiom SCC number calculated" << endl);


	////////////// 1. Generate all base variables (actions and facts)
	fact_variables.clear();
	fact_variables.resize(currentLength+1);
	axiom_variables.clear();
	axiom_variables.resize(currentLength+1);
	operator_variables.clear();
	operator_variables.resize(currentLength);
	real_operator_variables.clear();
	real_operator_variables.resize(currentLength);

	for (int time = 0; time < currentLength; time++){
		for (size_t op = 0; op < task_proxy.get_operators().size(); op ++){
			int opvar = capsule.new_variable();
			operator_variables[time].push_back(opvar);
			if (!is_leaf_operator[op]) real_operator_variables[time].push_back(opvar);
			variableCounter["operator"]++;
			DEBUG(capsule.registerVariable(opvar,"op " + pad_int(op) + " @ " + pad_int(time) + " " + task_proxy.get_operators()[op].get_name()));
		}
	}
	DEBUG(log << "Operator Variables Generated " << capsule.number_of_variables<< endl);

	for (int time = 0; time <= currentLength; time++){
		fact_variables[time].resize(task_proxy.get_variables().size());
		for (size_t var = 0; var < task_proxy.get_variables().size(); var++){
			// don't need to generate anything for statically true facts.
			if (statically_true_derived_predicates.count(var)) continue;
			VariableProxy varProxy = task_proxy.get_variables()[var];
			for (int val = 0; val < varProxy.get_domain_size(); val++){
				int factVar = capsule.new_variable();
				fact_variables[time][var].push_back(factVar);
				variableCounter["facts"]++;
				DEBUG(capsule.registerVariable(factVar,"fa " + pad_int(var) + "=" + pad_int(val) + " @ " + pad_int(time) + " " + varProxy.get_name() + "=" + varProxy.get_fact(val).get_name()));
			}
		}
	}
	DEBUG(log << "State Variables Generated " << capsule.number_of_variables<< endl);

	for (int time = 0; time <= currentLength; time++){
		axiom_variables[time].resize(task_proxy.get_variables().size());
		for (size_t var = 0; var < task_proxy.get_variables().size(); var++){
			VariableProxy varProxy = task_proxy.get_variables()[var];
			if (!varProxy.is_derived()) continue;
			// don't need to generate anything for statically true facts.
			if (statically_true_derived_predicates.count(var)) continue;

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

	DEBUG(log << "Axiom Variables generated " << capsule.number_of_variables << endl);

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
		DEBUG(log << "=> Generating timestep " << time << " of " << currentLength << endl);
		map<FactPair, map<set<int>,vector<int>>> conditionBuffer;
		map<FactPair, map<set<int>, int>> conditionVariable;
		for (size_t op = 0; op < task_proxy.get_operators().size(); op ++){
			DEBUG(if (op && op % 100 == 0){
				log << "Generated Operator " << op << " of " << task_proxy.get_operators().size() << endl;		
			});
			int opvar = operator_variables[time][op];
			OperatorProxy opProxy = task_proxy.get_operators()[op];

			map<int,int> preMap;
			bool inapplicableOperator = false;

			// Preconditions
			PreconditionsProxy precs = opProxy.get_preconditions();
			for (size_t pre = 0; pre < precs.size(); pre++){
				FactProxy fact = precs[pre];

				if (statically_true_derived_predicates.count(fact.get_variable().get_id())){
					// this precondition is always true, ignore it.
					if (fact.get_value()) continue;
					// precondition is always false, to disable action
					assertNot(solver,opvar);
					DEBUG(log << "Disabling operator " << opProxy.get_name() << endl);
					inapplicableOperator = true;
					break;
				}

				int fact_var = get_fact_var(time,fact);
				preMap[fact.get_variable().get_id()] = fact.get_value();
				
				implies(solver,opvar,fact_var);
			}
			registerClauses("preconditions");
			
			if (inapplicableOperator) continue;

			// Effect
			EffectsProxy effs = opProxy.get_effects();
			for (size_t eff = 0; eff < effs.size(); eff++){
				EffectProxy thisEff = effs[eff];
				int eff_fact_var = get_fact_var(time+1,thisEff.get_fact());
				//int eff_fact_var_before = get_fact_var(time,thisEff.get_fact());

				// gather the conditions of the conditional effect in a set (could be a vector ...)
				set<int> conditions;
				bool inApplicableEffect = false;
				EffectConditionsProxy cond = thisEff.get_conditions();
				for (size_t i = 0; i < cond.size(); i++){
					if (statically_true_derived_predicates.count(cond[i].get_variable().get_id())){
						// this precondition is always true, ignore it.
						if (cond[i].get_value()) continue;
						// precondition is always false, to disable action
						inApplicableEffect = true;
						break;
					}
					conditions.insert(get_fact_var(time, cond[i]));
				}

				if (inApplicableEffect) continue;

				int thisCausation;

				if (conditions.size() == 0){
					thisCausation = opvar;
				} else {
					// for conditional effects we add that the effect is not yet true
					//conditions.insert(-eff_fact_var_before);

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
	DEBUG(log << "Frame axioms." << endl);
	registerClauses("frame axioms");

	// 4. Evaluation of axioms
	// assumption here is: the variables in fact_variables are the ones
	// that are supposed to be used for preconditions
	AxiomsProxy axioms = task_proxy.get_axioms();
	for (int time = 0; time <= currentLength; time++){
		DEBUG(log << "=> Generating axioms for timestep " << time << " of " << currentLength << endl);

		// final value of the axioms implies their value for the next layer
		for (size_t var = 0; var < task_proxy.get_variables().size(); var++){
			if (task_proxy.get_variables()[var].is_derived() && statically_true_derived_predicates.count(var) == 0){
				// if axiom evaluates to true, its value 1 is the correct one
				implies(solver,axiom_variables[time][var].back(),fact_variables[time][var][1]);
				// if axiom evaluates to false, its value 0 is the correct one
				implies(solver,-axiom_variables[time][var].back(),fact_variables[time][var][0]);
			}
		}
		registerClauses("axioms finalisation");


		// actual evaluation of axioms

		int sccCount = 0;
		for (AxiomSCC & scc : axiomSCCsInTopOrder){
			DEBUG(if (sccCount && sccCount % 1000 == 0){
				log << "Generated Axiom SCC " << sccCount << " of " << axiomSCCsInTopOrder.size() << endl;
			});
			sccCount++;
			set<int> sset(scc.variables.begin(), scc.variables.end());
			if (scc.sizeOne) {
				scc.numberOfAxiomLayers = 1;
				if (statically_true_derived_predicates.count(scc.variables[0])){
					continue; // don't need to generate anything for this variable
				}
			}

			// nasty case. We can't optimise here
			if (scc.sizeOne || scc.fullComputationRequired){
				// initially all axioms are false
				for (int var : scc.variables){
					if (task_proxy.get_variables()[var].is_derived()){
						if (statically_true_derived_predicates.count(var))
							assertYes(solver,axiom_variables[time][var][0]);
						else
							assertNot(solver,axiom_variables[time][var][0]);
					}
				}
				registerClauses("axioms initialisation");

				for (int layer = 0; layer < scc.numberOfAxiomLayers; layer++){
					vector<vector<int>> causeVariables (task_proxy.get_variables().size());
					for (int sccvar : scc.variables){
						//if (statically_true_derived_predicates.count(sccvar)) {
						//	assertYes(solver,axiom_variables[time][sccvar][layer+1]);
						//	continue;
						//}

						// positive maintenance, if DP was true, it must remain true.
						int scc_var_fact = axiom_variables[time][sccvar][layer+1]; 
						int scc_var_fact_cur = axiom_variables[time][sccvar][layer]; 
						implies(solver,scc_var_fact_cur,scc_var_fact);
						causeVariables[sccvar].push_back(scc_var_fact_cur);
						registerClauses("axioms evaluation");

						for (OperatorProxy opProxy : achievers_per_derived[sccvar]){
							// Effect
							EffectsProxy effs = opProxy.get_effects();
							assert(effs.size() == 1);
							EffectProxy thisEff = effs[0];
							assert(thisEff.get_fact().get_value() == 1);
							assert(thisEff.get_fact().get_variable().is_derived());
							int eff_var = thisEff.get_fact().get_variable().get_id();
							assert(eff_var == sccvar);
							assert(statically_true_derived_predicates.count(eff_var) == 0);
							int eff_fact_var = get_axiom_var(time,layer+1,thisEff.get_fact());
							assert(eff_fact_var == scc_var_fact);

							set<int> conditions;
							// Preconditions
							PreconditionsProxy precs = opProxy.get_preconditions();
							vector<FactProxy> conds;
						
							for (size_t pre = 0; pre < precs.size(); pre++)
								conds.push_back(precs[pre]);
							
							EffectConditionsProxy cond = thisEff.get_conditions();
							for (size_t i = 0; i < cond.size(); i++)
								conds.push_back(cond[i]);

							bool inApplicable = false;
							for (FactProxy & fact : conds){
								if (fact.get_variable().is_derived()){
									// the variables that is changed will require value 0
									if (fact.get_variable().get_id() == eff_var){
										assert(fact.get_value() == 0);
										continue;	
									}

									if (statically_true_derived_predicates.count(fact.get_variable().get_id())){
										if (fact.get_value()) continue;	// condition is always true
										inApplicable = true;
										break;
									}

									//assert(fact.get_value() == 1);
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

							if (inApplicable) continue;
							
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
						assert(axiom_variables[time][var].size() > size_t(layer)+1);
						if (statically_true_derived_predicates.count(var)) continue;
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
					assert(statically_true_derived_predicates.count(sccvar) == 0);
					//if (statically_true_derived_predicates.count(sccvar)) {
					//	assertYes(solver,axiom_variables[time][sccvar][0]);
					//	continue;
					//}
					for (OperatorProxy opProxy : achievers_per_derived[sccvar]){

						// Effect
						EffectsProxy effs = opProxy.get_effects();
						assert(effs.size() == 1);
						EffectProxy thisEff = effs[0];
						assert(thisEff.get_fact().get_value() == 1);
						assert(thisEff.get_fact().get_variable().is_derived());
						int eff_var = thisEff.get_fact().get_variable().get_id();
						assert(statically_true_derived_predicates.count(eff_var) == 0);
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
						bool inApplicable = false;
						for (FactProxy & fact : conds){
							if (fact.get_variable().is_derived()){
								// the variables that is changed will require value 0
								if (fact.get_variable().get_id() == eff_var){
									assert(fact.get_value() == 0);
									continue;	
								}
								
								if (statically_true_derived_predicates.count(fact.get_variable().get_id())){
									if (fact.get_value()) continue;	// condition is always true
									inApplicable = true;
									break;
								}

								int fact_var;
								if (sset.count(fact.get_variable().get_id())){
									assert(fact.get_value() == 1);
									internalAxiom = true;
									break;
								}

								fact_var = get_last_axiom_var(time,fact);
								conditions.insert(fact_var);
							} else {
								int fact_var = get_fact_var(time,fact);
								conditions.insert(fact_var);
							}
						}

						// internal axioms cannot make facts at layer 0 true.
						if (internalAxiom) continue;
						if (inApplicable) continue;
						
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

				for (int var : scc.variables){
					if (statically_true_derived_predicates.count(var)) continue;
					if (task_proxy.get_variables()[var].is_derived()){
						int eff_var = axiom_variables[time][var][0];
						impliesOr(solver,eff_var,causeVariablesLayer0[var]);
					}
				}
				registerClauses("axioms causation");


				// 2. Internal work
				if (scc.isOfImplicationType) {
					for (size_t varOffset = 0; varOffset < scc.variables.size(); varOffset++){
						int var = scc.variables[varOffset];
						//if (statically_true_derived_predicates.count(var)) {
						//	assertYes(solver,axiom_variables[time][var][1]);
						//	continue;
						//}
						for (size_t varOffsetTo : scc.directTransitiveImplications[varOffset]){
							int varTo = scc.variables[varOffsetTo];
							implies(solver,axiom_variables[time][var][0], axiom_variables[time][varTo][1]);
						}
					}
					registerClauses("axioms evaluation");

					for (size_t varOffsetTo = 0; varOffsetTo < scc.variables.size(); varOffsetTo++){
						int varTo = scc.variables[varOffsetTo];
						if (statically_true_derived_predicates.count(varTo)) continue;
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
							//if (statically_true_derived_predicates.count(var)) {
							//	assertYes(solver,axiom_variables[time][var][1]);
							//	continue;
							//}
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
							if (statically_true_derived_predicates.count(varTo)) continue;
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
	DEBUG(log << "Axioms done. Generating init and goal." << endl);


	// 5. Init and Goal
	State init = task_proxy.get_initial_state();
	init.unpack();
	for (size_t i = 0; i < init.size(); i++){
		//if (init[i].get_variable().is_derived()) continue;
		if (statically_true_derived_predicates.count(init[i].get_variable().get_id())) continue;
		assertYes(solver,get_fact_var(0,init[i]));
	}
	registerClauses("init");

	GoalsProxy goals = task_proxy.get_goals();
	for (size_t i = 0; i < goals.size(); i++){
		if (statically_true_derived_predicates.count(goals[i].get_variable().get_id()) == 1){
			assert(goals[i].get_value() == 1);
			// statically true goals do not have to be satisfied.
			continue;
		}

		if (goals[i].get_variable().is_derived()){
			DEBUG(log << "Derived GOAL " << goals[i].get_variable().get_id() << " " << goals[i].get_value() << " " << get_last_axiom_var(currentLength,goals[i]) << endl);
			assertYes(solver,get_last_axiom_var(currentLength,goals[i]));
		} else {
			DEBUG(log << "Regular GOAL " << goals[i].get_variable().get_id() << " " << goals[i].get_value() << " " << get_fact_var(currentLength,goals[i]) << endl);
			assertYes(solver,get_fact_var(currentLength,goals[i]));
		}
	}
	registerClauses("goal");
	
	// 6. State Mutexes
	for (int time = 0; time <= currentLength; time++){
		for (size_t var = 0; var < task_proxy.get_variables().size(); var++){
			if (statically_true_derived_predicates.count(var)) continue;
			atMostOne(solver,capsule,fact_variables[time][var]);
			atLeastOne(solver,capsule,fact_variables[time][var]);
		}
	}
	registerClauses("state mutexes");
	
	// 7. Action Control
	for (int time = 0; time < currentLength; time++){
		if (real_operator_variables[time].size() == 0) continue;
			
		if (existsStep)
			// exists-step gets all operator variables -- otherwise indexing is too difficult
			exists_step_restriction(solver,capsule,operator_variables[time]);
		else
			atMostOne(solver,capsule,real_operator_variables[time]);

		if (forceAtLeastOneAction) atLeastOne(solver,capsule,real_operator_variables[time]);
	
		registerClauses("action control");

		// if we have leaf operators, we have to ensure that they are called whenever the main operator is called and vice versa
		if (decouplingMode){
			for (size_t leaf_internal_op_id = 0; leaf_internal_op_id < decoupledTask->get_separate_leaf_effect_operators().size(); leaf_internal_op_id++){
				OperatorID leaf_op_id = decoupledTask->get_separate_leaf_effect_operators()[leaf_internal_op_id];
				assert(is_leaf_operator[leaf_op_id.get_index()]);

				int leaf_var = operator_variables[time][leaf_op_id.get_index()];
				vector<int> realOpVars;
				for (const OperatorID & real_op : decoupledTask->get_global_operators_for_separate_leaf_effect_operator(leaf_internal_op_id)){
					assert(!is_leaf_operator[real_op.get_index()]);
					
					int real_var = operator_variables[time][real_op.get_index()];
					implies(solver,real_var,leaf_var);
					// the real operator forces the leaf operator to be present
					realOpVars.push_back(real_var);
				}
				// if the leaf operator is present, one the real operators that cause it have to be present
				impliesOr(solver,leaf_var,realOpVars);
			}	
			registerClauses("action control leaf");
		}
	}

	//assertYes(solver, 137);

	DEBUG(capsule.printVariables());


	// print variable and clause statistics
	log << "Variables" << setw(23) << setfill(' ') << "total: " << setw(8) << setfill(' ') << capsule.number_of_variables << endl;
	for (auto [a,b] : variableCounter)
		log << setw(30) << setfill(' ') << a << ": " << setw(8) << setfill(' ') << b << endl;
	log << "Clauses" << setw(25) << setfill(' ') << "total: " << setw(8) << setfill(' ') << get_number_of_clauses() << endl;
	for (auto [a,b] : clauseCounter)
		log << setw(30) << setfill(' ') << a << ": " << setw(8) << setfill(' ') << b << endl;



	kissatCurrentLength = currentLength;
	int solverState = ipasir_solve(solver);
	log << "SAT solver state: " << solverState << endl;
	if (solverState == 10){
		//printVariableTruth(solver,capsule);

		// maps operator to their index in the global ordering
		std::vector<int> global_action_indexing(task_proxy.get_operators().size());
		for(size_t i = 0; i < global_action_ordering.size(); i++)
			global_action_indexing[global_action_ordering[i]] = i;

		map<int,int> planPositionsToSATStates;
		planPositionsToSATStates[0] = 0;
		Plan plan;
		// plan extraction
		for (int time = 0; time < currentLength; time++){
			map<int,int> operatorsThisTime;
			for (size_t op = 0; op < task_proxy.get_operators().size(); op++){
				// the leaf operators don't have to be inserted into the plan
				if (is_leaf_operator[op]) continue;
				int opvar = operator_variables[time][op];
				int val = ipasir_val(solver,opvar);
				if (val > 0){
					operatorsThisTime[global_action_indexing[op]] = op;
					DEBUG(log << "time " << time << " operator " << task_proxy.get_operators()[op].get_name() << endl);
					//log << "kisvar " << opvar << " " << kissat_import_literal((kissat*)solver,opvar) << endl;
				}
			}

			// sort the operators according to their global sorting
			for (auto & [_sortkey, op] : operatorsThisTime){
				log << "time " << time << " sorted operator " << task_proxy.get_operators()[op].get_name() << endl;
				plan.push_back(OperatorID(op));
			}

			planPositionsToSATStates[plan.size()] = time + 1;
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

		AxiomEvaluator &axiom_evaluator = g_axiom_evaluators[task_proxy];
		for (size_t i = 0; i < visited_states.size(); ++i){
			State & s = visited_states[i];
			// TODO it seems that the state registry evaluates axioms for us
    		s.unpack();
			vector<int> upack = s.get_unpacked_values();
			axiom_evaluator.evaluate(upack);
			s = State(*task,move(upack));
			s.unpack();
			//task_properties::dump_fdr(s);

			if (!existsStep || planPositionsToSATStates.count(i)){
				for (size_t j = 0; j < s.size(); ++j){
					if (statically_true_derived_predicates.count(s[j].get_variable().get_id())) continue;
					//log << "State " << j << " " << s[j].get_value() << " " << get_fact_var(planPositionsToSATStates[i],s[j]) << " sat: " << 
					//	ipasir_val(solver,get_fact_var(planPositionsToSATStates[i],s[j])) << endl;
					assert(ipasir_val(solver,get_fact_var(planPositionsToSATStates[i],s[j])) > 0);
				}
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