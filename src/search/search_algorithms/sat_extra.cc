set<int> activeAxioms;
for (size_t var = 0; var < task_proxy.get_variables().size(); var++){
	VariableProxy varProxy = task_proxy.get_variables()[var];
	if (!varProxy.is_derived()) continue; // those are determined above

	// positive maintenance - i.e. if the fact was true, we try to keep it true
	FactPair derivedTarget(var,1);


	set<FactPair> guaranteedEffects; // contains all facts that *must* be true after the action
	// try to do this with out any inference

	// get the definitive effects of this action
	for (size_t eff = 0; eff < effs.size(); eff++){
		EffectProxy thisEff = effs[eff];
		// gather the conditions of the conditional effect 
		EffectConditionsProxy cond = thisEff.get_conditions();

		// check if conditions is satisfied. This can only stem from the assumed axiom
		bool allConditionsTrue = true;
		for (size_t i = 0; i < cond.size(); i++){
			FactProxy condition = cond[i];
			if (derivedTarget == condition.get_pair()) continue;
			// if this condition is not known to be true, we don't know whether the effect will fire 
			allConditionsTrue = false;
			break;
		}
		if (!allConditionsTrue) continue;
		guaranteedEffects.insert(thisEff.get_fact().get_pair());
	}
	// if I can satisfy with this minimal amount of information, then fine
	if (try_to_satisfy(activeAxioms, guaranteedEffects, derivedTarget)) continue;
				
	if (false){
		// reset and try to perform better inference
		guaranteedEffects.clear();

		// does this cause any effects to fire?
		set<FactPair> _unused1;
		set<FactPair> _unused2;
		compute_necessary_effects(op,derivedTarget,_unused1,_unused2,guaranteedEffects, false); // don't evaluate the axioms, I'll do that myself
		if (logInference)
			for (const FactPair & pair : guaranteedEffects){
				log << "State After: " << pair << endl;
			}

		// now try to get the fact to be true
		if (try_to_satisfy(activeAxioms, guaranteedEffects, derivedTarget)) continue;
	}
	// we could not ensure that this fact remains true to it might get deleted
	deletingActions[derivedTarget].insert(op);
	if (logInference) log << "Op " << op << " deleting " << derivedTarget.var << "=" << derivedTarget.value << endl;
}




	//invertedDerived.resize(task_proxy.get_variables().size());
	//for (size_t var = 0; var < task_proxy.get_variables().size(); var++){
	//	VariableProxy varProxy = task_proxy.get_variables()[var];
	//	if (!varProxy.is_derived()) continue;
	//	if (varProxy.get_default_axiom_value() == 0) continue;
	//	log << "Derived predicated with wrong monotonicity: " << varProxy.get_name() << endl;
	//	invertedDerived[var] = true;
	//}




// gather facts that could potentially become true
// gather fact that must be true afterwards
void  SATSearch::compute_necessary_effects(int op, FactPair assumedFact,
		set<FactPair> & maintainedFacts,
		set<FactPair> & potentialEffects,
		set<FactPair> & definitiveEffects,
		bool evaluateAxiomsAfter){
	OperatorProxy opProxy = task_proxy.get_operators()[op];
	EffectsProxy effs = opProxy.get_effects();
	set<FactPair> priorState = compute_known_prior_state(op, assumedFact);

	map<int,int> preMap;
	for (const FactPair & fact : priorState)
		preMap[fact.var] = fact.value;


	
	// 1. Any non-derived that is not changed will remain true 
	for (const FactPair & fact : priorState)
		if (!task_proxy.get_variables()[fact.var].is_derived())
			definitiveEffects.insert(fact);

	for (size_t eff = 0; eff < effs.size(); eff++){
		EffectProxy thisEff = effs[eff];
		// gather the conditions of the conditional effect 
		EffectConditionsProxy cond = thisEff.get_conditions();
		// check if conditions are potentially satisfied
		bool allConditionsPotentiallyTrue = true;
		for (size_t i = 0; i < cond.size(); i++){
			FactProxy condition = cond[i];
			// we don't know anything about the truth of this variable
			if (preMap.count(condition.get_variable().get_id()) == 0) continue;
			// we know this condition is true
			if (preMap[condition.get_variable().get_id()] == condition.get_pair().value) continue;
			// if we get here, the conditions variable has a different value than we know it must have
			allConditionsPotentiallyTrue = false;
			break;
		}
		if (!allConditionsPotentiallyTrue) continue;
		// if this was true before, it is not potentially new
		if (priorState.count(thisEff.get_fact().get_pair()) == 0)
			potentialEffects.insert(thisEff.get_fact().get_pair());
		
		// try to erase if this fact might become false
		if (thisEff.get_fact().get_variable().is_derived()) continue;
		if (preMap.count(thisEff.get_fact().get_variable().get_id()) == 0) continue;
		int thisEffectVariable = thisEff.get_fact().get_variable().get_id(); 
		// potential effect might generate the same value that it had before
		if (preMap[thisEffectVariable] == thisEff.get_fact().get_value()) continue;

		definitiveEffects.erase(FactPair(thisEffectVariable,preMap[thisEffectVariable]));
	}
	
	if (logInference){
		for (const FactPair & pair : definitiveEffects){
			log << "Definitive surviving preconditions: " << pair << endl;
		}
	}


	// get the definitive effects of this action
	for (size_t eff = 0; eff < effs.size(); eff++){
		EffectProxy thisEff = effs[eff];
		// gather the conditions of the conditional effect 
		EffectConditionsProxy cond = thisEff.get_conditions();

		// check if conditions is satisfied. This can only stem from the assumed axiom
		bool allConditionsTrue = true;
		for (size_t i = 0; i < cond.size(); i++){
			FactProxy condition = cond[i];
			if (priorState.count(condition.get_pair())) continue;
			// if this condition is not known to be true, we don't know whether the effect will fire 
			allConditionsTrue = false;
			break;
		}
		if (!allConditionsTrue) continue;
		definitiveEffects.insert(thisEff.get_fact().get_pair());
	}
	if (logInference){
		for (const FactPair & pair : definitiveEffects){
			log << "Definitive Effects: " << pair << endl;
		}
	}
	
	if (!evaluateAxiomsAfter) return;
	
	// run speculative execution to see which facts might be come true
	speculative_evaluate_axioms_on_partial_state(maintainedFacts,potentialEffects,definitiveEffects);
	if (logInference){
		for (const FactPair & pair : potentialEffects){
			log << "Potential effects: " << pair << endl;
		}
	}

	// all derived predicates that were false before and cannot potentially become true remain false
	for (const FactPair & fact : priorState) {
		if (!task_proxy.get_variables()[fact.var].is_derived()) continue;
		if (fact.value == 1) continue; // we can't say anything about these
		FactPair inverse (fact.var,1);
		// check if this derived can become true
		if (potentialEffects.count(inverse)) continue;
		definitiveEffects.insert(fact);
		if (logInference) log << "Definitive Effects due to speculative execution: " << fact << endl;
	}
	
	evaluate_axioms_on_partial_state(definitiveEffects);
}

set<FactPair> SATSearch::evaluate_axioms_on_partial_state(set<FactPair> & definitiveEffects){
	map<int,int> stateMap;
	for (const FactPair & pair : definitiveEffects){
		stateMap[pair.var] = pair.value;
	}

	// evaluate all axioms on the partial state that we got ...
	set<FactPair> newEffects; 
	for (AxiomSCC & scc : axiomSCCsInTopOrder){
		bool somethingAdded = true;
		set<int> thisSCCVars(scc.variables.begin(), scc.variables.end());
		set<int> allAchieversInapplicable(scc.variables.begin(), scc.variables.end());

		bool allEnteringAreInapplicable = true;
		while (somethingAdded){
			somethingAdded = false;
			for (int & dp : scc.variables){
				// try to apply the axioms in this SCC
				bool allInapplicable = true;
				for (OperatorProxy opProxy : achievers_per_derived[dp]){
					//if (dp == 65) log << "Operator for DP 65" << endl;
					// effect
					EffectsProxy effs = opProxy.get_effects();
					assert(effs.size() == 1);
					EffectProxy thisEff = effs[0];
					assert(thisEff.get_fact().get_value() == 1);
					assert(thisEff.get_fact().get_variable().is_derived());
					// Preconditions
					PreconditionsProxy precs = opProxy.get_preconditions();
					vector<FactPair> conds;
	
					for (size_t pre = 0; pre < precs.size(); pre++)
						conds.push_back(precs[pre].get_pair());
					
					EffectConditionsProxy cond = thisEff.get_conditions();
					for (size_t i = 0; i < cond.size(); i++)
						conds.push_back(cond[i].get_pair());
				

					bool cyclicOperator = false;
					bool inApplicable = false;	
					bool applicable = true;
					for (FactPair & pre : conds){
						// this is just that the DP has to be false before we apply this rule.
						if (pre.var == thisEff.get_fact().get_variable().get_id()) continue;

						if (thisSCCVars.count(pre.var))
							cyclicOperator = true;

						if (stateMap.count(pre.var)){
							// condition is incompatible with known true state 
							if (stateMap[pre.var] != pre.value)
								inApplicable = true;
						}

						if (definitiveEffects.count(pre) == 0){
							applicable = false;
							break;
						}
					}

					// non-cyclic, i.e., entering this SCC
					// not inapplicable, i.e., could potentially be applicable
					if (!cyclicOperator && !inApplicable)
						allEnteringAreInapplicable = false;

					if (!inApplicable)
						allInapplicable = false;

					if (!applicable) continue;
					if (definitiveEffects.count(thisEff.get_fact().get_pair())) continue;
					somethingAdded = true;
					definitiveEffects.insert(thisEff.get_fact().get_pair());
					newEffects.insert(thisEff.get_fact().get_pair());
					stateMap[thisEff.get_fact().get_pair().var] = thisEff.get_fact().get_pair().value;
				}
				if (!allInapplicable)
					allAchieversInapplicable.erase(dp);
			}
		}
		
		for (const int & dp : allAchieversInapplicable){
			//log << "All achievers are definitely inapplicable for " << dp << endl;
			definitiveEffects.insert(FactPair(dp,0));
			newEffects.insert(FactPair(dp,0));
			stateMap[dp] = 0;
		}

		if (allEnteringAreInapplicable){
			//log << "All Entering are definitely inapplicable" << endl;
			for (int & dp : scc.variables){
				definitiveEffects.insert(FactPair(dp,0));
				newEffects.insert(FactPair(dp,0));
				stateMap[dp] = 0;
			}
		}
	}
	if (logInference){
		for (const FactPair & pair : newEffects){
			log << "Effects After Propagation: " << pair << endl;
		}
	}

	return definitiveEffects;
}


bool SATSearch::try_to_satisfy(set<int> & activeAxtioms, set<FactPair> & currentState, FactPair goal){
	if (currentState.count(goal)) return true; // true and nothing to do.

	// try to search for an axiom that will make the goal fact true
	int unusedAxiom = -1;
	for (OperatorProxy opProxy : achievers_per_derived[goal.var]){
		EffectsProxy effs = opProxy.get_effects();
		EffectProxy thisEff = effs[0];
		
		// Preconditions
		PreconditionsProxy precs = opProxy.get_preconditions();
		vector<FactPair> conds;

		for (size_t pre = 0; pre < precs.size(); pre++)
			conds.push_back(precs[pre].get_pair());
		
		EffectConditionsProxy cond = thisEff.get_conditions();
		for (size_t i = 0; i < cond.size(); i++)
			conds.push_back(cond[i].get_pair());
	

		bool allConditionsSatisfied = true;
		for (FactPair & pre : conds){
			// this is just that the DP has to be false before we apply this rule.
			if (pre.var == thisEff.get_fact().get_variable().get_id()) continue;
			if (currentState.count(pre)) continue;

			allConditionsSatisfied = false;
			break;
		}
		if (!allConditionsSatisfied) continue;

		if (activeAxtioms.count(opProxy.get_id())) return true; // nothing to do
		unusedAxiom = opProxy.get_id();
	}

	// we have an axiom for this, just use it!
	if (unusedAxiom != -1){
		activeAxtioms.insert(unusedAxiom);
		return true;	
	}

	// no axiom that could satisfy my result
	return false;
}

void SATSearch::speculative_evaluate_axioms_on_partial_state(set<FactPair> & maintainedFacts, set<FactPair> & possibleEffects, set<FactPair> & definitiveEffects){
	map<int,int> stateMap;
	for (const FactPair & pair : definitiveEffects){
		stateMap[pair.var] = pair.value;
	}
	
	// evaluate all axioms on the partial state that we got ...
	set<FactPair> newEffects; 
	for (AxiomSCC & scc : axiomSCCsInTopOrder){
		bool somethingAdded = true;
		set<int> thisSCCVars(scc.variables.begin(), scc.variables.end());
		set<int> allAchieversInapplicable(scc.variables.begin(), scc.variables.end());

		while (somethingAdded){
			somethingAdded = false;
			for (int & dp : scc.variables){
				// try to apply the axioms in this SCC
				for (OperatorProxy opProxy : achievers_per_derived[dp]){
					EffectsProxy effs = opProxy.get_effects();
					assert(effs.size() == 1);
					EffectProxy thisEff = effs[0];
					assert(thisEff.get_fact().get_value() == 1);
					assert(thisEff.get_fact().get_variable().is_derived());
					
					// we have already proven that if the value remains 0 if it was,
					// this derived predicate cannot become newly 1
					FactPair inverted(thisEff.get_fact().get_variable().get_id(), 0);
					if (maintainedFacts.count(inverted))
						continue;
						
					// Preconditions
					PreconditionsProxy precs = opProxy.get_preconditions();
					vector<FactPair> conds;
	
					for (size_t pre = 0; pre < precs.size(); pre++)
						conds.push_back(precs[pre].get_pair());
					
					EffectConditionsProxy cond = thisEff.get_conditions();
					for (size_t i = 0; i < cond.size(); i++)
						conds.push_back(cond[i].get_pair());
				
					bool inApplicable = false;
					bool potentiallyNewlyApplicable = false;
					for (FactPair & pre : conds){
						// this is just that the DP has to be false before we apply this rule.
						if (pre.var == thisEff.get_fact().get_variable().get_id()) continue;

						if (stateMap.count(pre.var)){
							// condition is incompatible with known true state 
							if (stateMap[pre.var] != pre.value){
								inApplicable = true;
								break;
							}
						}

						if (possibleEffects.count(pre) > 0)
							potentiallyNewlyApplicable = true;
					}

					if (inApplicable) continue;
					if (!potentiallyNewlyApplicable) continue; // execution will remain the same
					possibleEffects.insert(thisEff.get_fact().get_pair());

				}
			}
		}
	}
	if (logInference) {
		for (const FactPair & pair : possibleEffects){
			log << "Possible Effects After Propagation: " << pair << endl;
		}
	}
}

set<FactPair> SATSearch::compute_known_prior_state(int op, FactPair assumedFact){
	OperatorProxy opProxy = task_proxy.get_operators()[op];
	EffectsProxy effs = opProxy.get_effects();
	set<FactPair> definitiveBefore;

	// get all preconditions
	PreconditionsProxy precs = opProxy.get_preconditions();
	set<FactPair> definitiveDerivedBefore;

	if (assumedFact.var != -1){
		definitiveBefore.insert(assumedFact);
	}

	for (size_t pre = 0; pre < precs.size(); pre++){
		FactProxy fact = precs[pre];
		definitiveBefore.insert(fact.get_pair());
	}

	bool newInference = true;
	while (newInference){
		newInference = false;
		// Derived predicates can imply further facts, if they only have one achiever
		set<FactPair> loopCopy = definitiveBefore;
		for (const FactPair & derived : loopCopy){
			if (!task_proxy.get_variables()[derived.var].is_derived()) continue;
			//log << "\tKnow that " << derived << " before action" << endl;
			if (derived.value == 1){
				if (achievers_per_derived[derived.var].size() == 1){
					for (OperatorProxy opProxy : achievers_per_derived[derived.var]){
						PreconditionsProxy precs = opProxy.get_preconditions();
						vector<FactPair> conds;
		
						for (size_t pre = 0; pre < precs.size(); pre++)
							conds.push_back(precs[pre].get_pair());
						
						EffectProxy thisEff = opProxy.get_effects()[0];
						EffectConditionsProxy cond = thisEff.get_conditions();
						for (size_t i = 0; i < cond.size(); i++)
							conds.push_back(cond[i].get_pair());

						for (FactPair & pre : conds){
							// this is just that the DP has to be false before we apply this rule.
							if (pre.var == thisEff.get_fact().get_variable().get_id()) continue;
							if (definitiveBefore.count(pre)) continue;
							newInference = true;
							definitiveBefore.insert(pre);
						}
					}
				}
			} else {
				// we know that Derived Predicate is false
				for (OperatorProxy opProxy : achievers_per_derived[derived.var]){
					//log << "\tCausing operator" << endl;
					PreconditionsProxy precs = opProxy.get_preconditions();
					vector<FactPair> conds;
		
					for (size_t pre = 0; pre < precs.size(); pre++)
						conds.push_back(precs[pre].get_pair());
					
					EffectProxy thisEff = opProxy.get_effects()[0];
					EffectConditionsProxy cond = thisEff.get_conditions();
					for (size_t i = 0; i < cond.size(); i++)
						conds.push_back(cond[i].get_pair());

					int unknownConditions = 0;
					FactPair unknownCondition (-1,-1);
					for (FactPair & pre : conds){
						//log << "\t\t\t" << pre.var << "=" << pre.value << endl;
						// this is just that the DP has to be false before we apply this rule.
						if (pre.var == thisEff.get_fact().get_variable().get_id()) continue;
						if (definitiveBefore.count(pre)) continue;
						unknownConditions++;
						unknownCondition = pre;
					}

					if (unknownConditions == 1){
						int variable = unknownCondition.var;
						if (task_proxy.get_variables()[variable].get_domain_size() == 2){
							int value = 1 - unknownCondition.value; // it must be the other value

							if (definitiveBefore.count(FactPair(variable, value)) == 0){
								definitiveBefore.insert(FactPair(variable, value));
								newInference = true;
							}
						}
					}
				}
			}
		}
	}
	
	//for (const FactPair & pair : definitiveBefore){
	//	log << "Definitive Before: " << pair << endl;
	//}
	return definitiveBefore;
}



void SATSearch::set_up_exists_step() {

	//log << "Computing maintainance effects of actions" << endl;
	//vector<set<FactPair>> maintainedFactsByOperator(task_proxy.get_operators().size());
	//for(size_t op = 0; op < task_proxy.get_operators().size(); op++){
	//	continue;
	//	//if (op != 39) continue;
	//	log << "\t Operator " << op << endl;
	//	set<FactPair> & maintainedFacts = maintainedFactsByOperator[op];
	//	OperatorProxy opProxy = task_proxy.get_operators()[op];
	//	EffectsProxy effs = opProxy.get_effects();
	//
	//
	//	bool newMaintained = true;
	//	while (newMaintained){
	//		newMaintained = false;
	//
	//		// first true than false	
	//		for (int value = 1; value >= 0; value --){
	//			if (value == 1){
	//				for (size_t var = 0; var < task_proxy.get_variables().size(); var++){
	//					//if (var != 10) continue;
	//					// result already known
	//					if (maintainedFacts.count(FactPair(var,value))) continue;
	//					
	//					VariableProxy varProxy = task_proxy.get_variables()[var];
	//	
	//					if (logInference)
	//						log << "POS Considering derived variable " << var << " " << varProxy.get_name() << endl;
	//					//assert(varProxy.get_domain_size() == 2);
	//	
	//					FactPair derivedPair(var,value);
	//					set<FactPair> potentialEffects;
	//					set<FactPair> definitiveEffects;
	//					compute_necessary_effects(op, derivedPair, maintainedFacts, potentialEffects, definitiveEffects, true);
	//					FactPair derivedInverted(var,1-value);
	//	
	//					if (definitiveEffects.count(derivedPair)){
	//							//potentialEffects.count(derivedInverted) == 0){
	//						if (logInference) log << "Maintain as Effect " << var << "=" << value << endl;
	//						maintainedFacts.insert(FactPair(var,value));
	//						newMaintained = true;
	//						continue;
	//					}
	//					
	//					// special case: disjunctions but this only works for derived predicates
	//					if (!varProxy.is_derived()) continue;

	//					bool allCausesMaintained = true;
	//					for (OperatorProxy opProxy : achievers_per_derived[var]){
	//						EffectsProxy effs = opProxy.get_effects();
	//						assert(effs.size() == 1);
	//						EffectProxy thisEff = effs[0];
	//						assert(thisEff.get_fact().get_value() == 1);
	//						assert(thisEff.get_fact().get_variable().is_derived());
	//						// Preconditions
	//						PreconditionsProxy precs = opProxy.get_preconditions();
	//						vector<FactPair> conds;
	//						
	//						for (size_t pre = 0; pre < precs.size(); pre++)
	//							conds.push_back(precs[pre].get_pair());
	//						
	//						EffectConditionsProxy cond = thisEff.get_conditions();
	//						for (size_t i = 0; i < cond.size(); i++)
	//							conds.push_back(cond[i].get_pair());
	//						
	//						bool maintained = true;
	//						for (FactPair & pre : conds){
	//							// this is just that the DP has to be false before we apply this rule.
	//							if (pre.var == thisEff.get_fact().get_variable().get_id()) continue;
	//							if (definitiveEffects.count(pre)) continue;
	//							if (maintainedFacts.count(pre)) continue;

	//							// this could be the cause and it might not be true any more
	//							maintained = false;
	//						}
	//						if (!maintained){
	//							allCausesMaintained = false;
	//							break;
	//						}
	//					}
	//					if (allCausesMaintained){
	//						if (logInference) log << "Maintain Disjunct " << var << "=" << value << endl;
	//						maintainedFacts.insert(FactPair(var,value));
	//						newMaintained = true;
	//					}
	//				}
	//			} else {
	//				// value = false
	//				for (size_t var = 0; var < task_proxy.get_variables().size(); var++){
	//					//if (var != 10) continue;
	//					// result already known
	//					if (maintainedFacts.count(FactPair(var,value))) continue;
	//					
	//					VariableProxy varProxy = task_proxy.get_variables()[var];
	//					if (logInference)
	//						log << "NEG Considering derived variable " << var << " " << varProxy.get_name() << endl;
	//					FactPair derivedPair(var,value);
	//					
	//					// compute all effects of this action
	//					set<FactPair> potentialEffects;
	//					set<FactPair> definitiveEffects;
	//					compute_necessary_effects(op, derivedPair, maintainedFacts, potentialEffects, definitiveEffects, true);


	//					if (logInference){
	//						for (const FactPair & pair : definitiveEffects){
	//							log << "State after: " << pair << endl;
	//						}
	//					}
	//					if (definitiveEffects.count(derivedPair)){
	//							//potentialEffects.count(derivedInverted) == 0){
	//						if (logInference) log << "Maintain as Effect " << var << "=" << value << endl;
	//						maintainedFacts.insert(FactPair(var,value));
	//						newMaintained = true;
	//						continue;
	//					}
	//					
	//					// special case: disjunctions but this only works for derived predicates
	//					if (!varProxy.is_derived()) continue;


	//					// convert to map so that we can test for contradictions more easily	
	//					map<int,int> stateMap;
	//					for (const FactPair & pair : definitiveEffects){
	//						stateMap[pair.var] = pair.value;
	//					}
	//	
	//					bool couldBecomeTrue = false;
	//					for (OperatorProxy opProxy : achievers_per_derived[var]){
	//						//log << "Operator could make it true. " << endl;
	//						EffectsProxy effs = opProxy.get_effects();
	//						assert(effs.size() == 1);
	//						EffectProxy thisEff = effs[0];
	//						assert(thisEff.get_fact().get_value() == 1);
	//						assert(thisEff.get_fact().get_variable().is_derived());
	//						// Preconditions
	//						PreconditionsProxy precs = opProxy.get_preconditions();
	//						vector<FactPair> conds;
	//						
	//						for (size_t pre = 0; pre < precs.size(); pre++)
	//							conds.push_back(precs[pre].get_pair());
	//						
	//						EffectConditionsProxy cond = thisEff.get_conditions();
	//						for (size_t i = 0; i < cond.size(); i++)
	//							conds.push_back(cond[i].get_pair());
	//						
	//						bool applicable = true;
	//						bool onePotentiallyNewCondition = false;
	//						for (FactPair & pre : conds){
	//							// this is just that the DP has to be false before we apply this rule.
	//							if (pre.var == thisEff.get_fact().get_variable().get_id()) continue;
	//							//log << "\tCondition " << pre << endl;
	//					
	//							if (potentialEffects.count(pre))
	//								onePotentiallyNewCondition = true;
	//	
	//							if (stateMap.count(pre.var)){
	//								if (stateMap[pre.var] != pre.value){
	//									//log << "\t\tAction has contradicting effect" << endl;
	//									applicable = false;
	//									break;
	//								}
	//								// condition is definitely true
	//								//log << "\t\tAction has supporting effect" << endl;
	//								continue;
	//							}
	//	
	//							
	//							//log << "\t\tdon't know anything about this fact" << endl;
	//							// we can only assume it could be true
	//						}
	//						//log << "\tOperator: " << applicable << " " << onePotentiallyNewCondition << endl;
	//						if (applicable && onePotentiallyNewCondition) couldBecomeTrue = true;
	//					}
	//	
	//					if (couldBecomeTrue) continue;
	//					if (logInference) log << "Maintain Causes " << var << "=" << value << endl;
	//					maintainedFacts.insert(FactPair(var,value));
	//					newMaintained = true;
	//				}
	//			}
	//		}
	//	}
	//
	//
	//	if (op == 0){
	//		for (int value = 1; value >= 0; value --){
	//			for (size_t var = 0; var < task_proxy.get_variables().size(); var++){
	//				FactPair derivedPair(var,value);
	//				if (maintainedFacts.count(derivedPair)) continue;
	//				log << "Not Maintained " << var << "=" << value << endl;
	//			}
	//			//exit(0);
	//		}
	//		//for (const FactPair & maintained : maintainedFacts)
	//		//	log << "Maintain " << maintained.var << "=" << maintained.value << endl;
	//	}
	//
	//}



