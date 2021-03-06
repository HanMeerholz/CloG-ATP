module ATP::RuleApplications
/*
 * Module providing the functions for each of the rule applications.
 */

import CloG_Base::GLASTs;
import ATP::ATP_Base;
import ATP::ProofSearch;
import Map;
import List;

/* 
 * A function applying the "ax1" axiom to a term
 * 
 * Input:  the sequent to which the "ax1" axiom is applied
 * Output: the sequent resulting from applying the "ax1" axiom
 *
 * For the axiom to be applied, there must be exactly two sequents of the forms
 * "p^[]" and "~p^[]".
 * 
 * If these condition are met, an empty sequent (the result of applying the ax1
 * axiom is returned. Otherwise, noSeq() is returned.
 */
MaybeSequent applyAx1(CloGSequent seq) {
	if (size(seq) != 2) return noSeq();
	
	if (term(atomP(Prop p), [], _) := seq[0] && term(neg(atomP(p)), [], _) := seq[1]) {
		return sequent([]);
	}
	
	if (term(atomP(Prop p), [], _) := seq[1] && term(neg(atomP(p)), [], _) := seq[0]) {
		return sequent([]);
	}
	
	return noSeq();
}

/*
 * A function applying the "ax1" axiom after some potential weakening and
 * expanding of the terms in the sequent.
 * 
 * Input:  the sequent to which the rule is applied
 * Output: either the CloGProof found after applying weakening/expanding,
 *         and the ax1() axiom to the sequent, or noProof() if no such
 *         proof could be found
 *
 * If there are two terms "p^a", and "~p^a" in the input sequent, the weak
 * rule is applied to the remaining terms, and the exp rule is used to obtain
 * "p^[]" and "~p^[]". At this point, we can call the applyAx1() function,
 * which will return a leaf. 
 * 
 * We return the proof that applies weakening and expanding rules, ending in
 * a ax1 application resulting in a CloGLeaf.
 * 
 * If no such terms exist, noProof() is returned.
 */
MaybeProof tryApplyAx1(CloGSequent seq) {
	for (int termIdx <- [0 .. size(seq)]) {
		if (term(atomP(Prop p), _, _) := seq[termIdx]) {
			for (int termIdx2 <- [0 .. size(seq)]) {
				if (term(neg(atomP(p)), _, _) := seq[termIdx2]) {
					
					CloGSequent weakenTo = termIdx < termIdx2
									     ? [term(atomP(p), [], true), term(neg(atomP(p)), [], true)]
									     : [term(neg(atomP(p)), [], true), term(atomP(p), [], true)];
					
					resSeq = applyAx1(weakenTo);
					if (resSeq != noSeq()) {
						weakenTo[0].active = true;
						weakenTo[1].active = true;
						
						resProof = proofSearchWeakExp(seq, weakenTo);
			 	
					 	return visit(resProof) {
					 		case CloGUnaryInf(_, weak(), CloGLeaf()) => CloGUnaryInf(weakenTo, ax1(), CloGLeaf())
					 	};
					}
				}
			}
		}
	}
	
	return cantApply();
}


 
/* A function applying the "modm" rule to a term
 * 
 * Input:  the sequent to apply the "modm" rule to
 * Output: the sequent resulting from applying the "modm" rule
 *
 * For the rule to be applied, there must be two terms in the sequent, of forms "<g>phi^a" and
 * "<g^d>psi^b"
 * 
 * If these conditions are met, a sequent containing "phi^a" and "psi^b" is returned. Otherwise,
 * noSeq() is returned.
 */
MaybeSequent applyModm(CloGSequent seq) {

	if (size(seq) != 2)
		return noSeq();
		
	if (term(\mod(Game g, GameLog phi), list[CloGName] a, _) := seq[0] && term(\mod(dual(g), GameLog psi), list[CloGName] b, _) := seq[1]) {
		return sequent([term(phi, a, false), term(psi, b, false)]);
	}
	if (term(\mod(Game g, GameLog phi), list[CloGName] a, _) := seq[1] && term(\mod(dual(g), GameLog psi), list[CloGName] b, _) := seq[0]) {
		return sequent([term(psi, b, false), term(phi, a, false)]);
	}
	
	return noSeq();
}

/*
 * All of the remaining tryApply<rulename>() functions defined in here have the
 * following inputs' and outputs: 
 *
 * Input:  the sequent to which the rule is applied, the map of closure
 *         sequents, the list of fixpoint sequents, and the current depth
 * Output: either the CloGProof found after applying the rule to the sequent,
 *         or noProof() if no such proof could be found
 */

/*
 * A function applying the "modm" rule to a sequent, after some potential 
 * weakening of the terms in the given sequent. The main proofSearch()
 * algorithm is called on the sequent resulting from applying this "modm" rule.
 * 
 * For the rule to be applied, there must be 2 terms in the sequent of the
 * form "<g>phi^[a]", and "~<g^d>psi^[b]". The remaining terms are removed by
 * weakening, and a proof search is done on the resulting sequent.
 *
 * If a subproof is found for this resulting sequent, we return the proof
 * that includes the weakening rule applications and ends in this subproof.
 *
 * The rule application is tried for any 2 terms of the form. If none of these 
 * return a proof, or there are no 2 terms of the appropriate form, noProof()
 * is returned.
 */
MaybeProof tryApplyModm(CloGSequent seq, CloSeqs cloSeqs, list[CloGSequent] fpSeqs, int depth) {
	for (int termIdx <- [0 .. size(seq)]) {
		if (term(\mod(Game g, GameLog phi), list[CloGName] a, _) := seq[termIdx]) {
			for (int termIdx2 <- [0 .. size(seq)]) {
				if (term(\mod(dual(g), GameLog psi), list[CloGName] b, _) := seq[termIdx2]) {
				
					CloGSequent weakenTo = termIdx < termIdx2
									     ? [term(\mod(g, phi), a, false), term(\mod(dual(g), psi), b, false)]
									     : [term(\mod(dual(g), psi), b, false), term(\mod(g, phi), a, false)];
									     
					MaybeSequent resSeq = applyModm(weakenTo);
					
					if (resSeq != noSeq()) {
						subProof = proofSearch(resSeq.seq, cloSeqs, fpSeqs, depth - 1);
						if (subProof != noProof() && subProof != cantApply()) {
							weakenTo[0].active = true;
							weakenTo[1].active = true;
							
							resProof = proofSearchWeakExp(seq, weakenTo);
			 	
						 	return visit(resProof) {
						 		case CloGUnaryInf(_, weak(), CloGLeaf()) => CloGUnaryInf(weakenTo, modm(), subProof.p)
						 	};
						}
					}
				}
			}
		}
	}
	
	return noProof();
}

/* 
 * A function applying the "and" rule to a term
 * 
 * Input:  the sequent and the index of the term therein to which to apply the "and" rule
 * Output: the pair of sequents resulting from applying the "and" rule
 *
 * For the rule to be applied, the term at the specified index must be of
 * the form "(phi & psi)^a".
 * 
 * If this condition is met, a pair of sequents is returned, such that for one of
 * them, the specified term is replaced by "phi^a", and for the other, it is
 * replaced by "psi^a". Otherwise, noSeqs() is returned.
 */
MaybeSequents applyAnd(CloGSequent seq, int termIdx) {
	if (term(and(GameLog phi, GameLog psi), list[CloGName] a, _) := seq[termIdx]) {
		copySeq = seq;
		seq[termIdx] = term(phi, a, false);
		copySeq[termIdx] = term(psi, a, false);
		
		return sequents(seq, copySeq);
	}
	return noSeqs();
}

/*
 * A function applying the "and" rule to a sequent and calling the main proof search
 * algorithm on the resulting sequents.
 *
 * For any of the terms in the sequent, the algorithm checks tries to apply the "and"
 * rule. For the first successful application, a proof search is done on the resulting sequent.
 * If either of these proof searches returns a noProof() or cantApply(), that return value
 * is propagated. If two subproofs are found, A CloGBinaryInf with the resulting subproofs,
 * is returned.
 * 
 * If the "and" rule could not be applied to any term in the sequent, cantApply() is returned.
 */
MaybeProof tryApplyAnd(CloGSequent seq, CloSeqs cloSeqs, list[CloGSequent] fpSeqs, int depth) {		
	for (int termIdx <- [0 .. size(seq)]) {
		MaybeSequents resSeqs = applyAnd(seq, termIdx);
		if (resSeqs != noSeqs()) {
			MaybeProof subProofL = proofSearch(resSeqs.left, cloSeqs, fpSeqs, depth - 1);
			
			if (subProofL == noProof() ||subProofL == cantApply())
				return subProofL;
			
			MaybeProof subProofR = proofSearch(resSeqs.right, cloSeqs, fpSeqs, depth - 1);
			
			if (subProofR == noProof() ||subProofR == cantApply())
				return subProofR;
			
			seq[termIdx].active = true;
			return proof(CloGBinaryInf(seq, subProofL.p, subProofR.p));
		}
	}
	
	return cantApply();
}

/* 
 * A function applying the "or" rule to a term
 * 
 * Input:  the sequent and the index of the term therein to which to apply the "or" rule
 * Output: the sequent resulting from applying the "or" rule
 *
 * For the rule to be applied, the term at the specified index must be of
 * the form "(phi | psi)^a".
 * 
 * If this condition is met, the specified term in the given sequent is replaced by two
 * terms "phi^a", and "psi^a" and the sequent is returned. Otherwise, noSeq() is returned.
 */
MaybeSequent applyOr(CloGSequent seq, int termIdx) {
	if (term(or(GameLog phi, GameLog psi), list[CloGName] a, _) := seq[termIdx]) {
		return sequent(seq[0 .. termIdx] + term(phi, a, false) + term(psi, a, false) + seq[termIdx+1 .. size(seq)]);
	}
	return noSeq();
}

/*
 * A function applying the "or" rule to a sequent and calling the main
 * proof search algorithm on the resulting sequent.
 * 
 * For any of the terms in the sequent, the algorithm checks tries to apply the "or"
 * rule. For the first successful application, a proof search is done on the resulting sequent.
 * If a subproof is found, A CloGUnaryInf with the resulting subproof, and the applied orR()
 * rule is returned. Otherwise, the subProof itself is returned, which can be noProof()
 * or cantApply().
 * If the "or" rule could not be applied to any term in the sequent, cantApply() is returned.
 */
MaybeProof tryApplyOr(CloGSequent seq, CloSeqs cloSeqs, list[CloGSequent] fpSeqs, int depth) {	
	for (int termIdx <- [0 .. size(seq)]) {
		MaybeSequent resSeq = applyOr(seq, termIdx);
		if (resSeq != noSeq()) {			
			subProof = proofSearch(resSeq.seq, cloSeqs, fpSeqs, depth - 1);
			if (subProof != noProof() && subProof != cantApply()) {
				seq[termIdx].active = true;
				return proof(CloGUnaryInf(seq, orR(), subProof.p));		
			}
			return subProof;
		}
	}
	
	return cantApply();
}

/* 
 * A function applying the "choice" rule to a term
 * 
 * Input:  the sequent and the index of the term therein to which to apply the "choice" rule
 * Output: the sequent resulting from applying the "choice" rule
 *
 * For the rule to be applied, the term at the specified index must be of
 * the form "(<gamma || delta>phi)^a".
 * 
 * If this condition is met, the specified term in the given sequent is replaced by
 * the term "(<gamma>phi | <delta> phi)^a" and the sequent is returned. Otherwise,
 * noSeq() is returned.
 */
MaybeSequent applyChoice(CloGSequent seq, int termIdx) {
	if (term(\mod(choice(Game gamma, Game delta), GameLog phi), list[CloGName] a, _) := seq[termIdx]) {
		seq[termIdx] = term(or(\mod(gamma, phi), \mod(delta, phi)), a, false);
		return sequent(seq);
	}
	return noSeq();
}

/* 
 * A function applying the "choice" rule to a sequent and calling the main
 * proof search algorithm on the resulting sequent.
 *
 * For any of the terms in the sequent, the algorithm tries to apply the "choice"
 * rule. For the first successful application, a proof search is done on the resulting sequent.
 * If a subproof is found, A CloGUnaryInf with the resulting subproof, and the applied choiceR()
 * rule is returned. Otherwise, the subProof itself is returned, which can be noProof()
 * or cantApply().
 * If the "choice" rule could not be applied to any term in the sequent, cantApply() is returned.
 */
MaybeProof tryApplyChoice(CloGSequent seq, CloSeqs cloSeqs, list[CloGSequent] fpSeqs, int depth) {
	for (int termIdx <- [0 .. size(seq)]) {
		MaybeSequent resSeq = applyChoice(seq, termIdx);
		if (resSeq != noSeq()) {
			MaybeProof subProof = proofSearch(resSeq.seq, cloSeqs, fpSeqs, depth - 1);
			if (subProof != noProof() && subProof != cantApply()) {
				seq[termIdx].active = true;
				return proof(CloGUnaryInf(seq, choiceR(), subProof.p));
			}
			return subProof;
		}
	}

	return cantApply();
}

/* 
 * A function applying the "dChoice" rule to a term
 * 
 * Input:  the sequent and the index of the term therein to which to apply the "dChoice" rule
 * Output: the sequent resulting from applying the "dChoice" rule
 *
 * For the rule to be applied, the term at the specified index must be of
 * the form "(<gamma && delta>phi)^a".
 * 
 * If this condition is met, the specified term in the given sequent is replaced by
 * the term "(<gamma>phi & <delta> phi)^a" and the sequent is returned. Otherwise,
 * noSeq() is returned.
 */
MaybeSequent applyDChoice(CloGSequent seq, int termIdx) {
	if (term(\mod(dChoice(Game gamma, Game delta), GameLog phi), list[CloGName] a, _) := seq[termIdx]) {
		seq[termIdx] = term(and(\mod(gamma, phi), \mod(delta, phi)), a, false);
		return sequent(seq);
	}
	return noSeq();
}

/* 
 * A function applying the "dChoice" rule to a sequent and calling the main
 * proof search algorithm on the resulting sequent.
 *
 * For any of the terms in the sequent, the algorithm tries to apply the "dChoice"
 * rule. For the first successful application, a proof search is done on the resulting sequent.
 * If a subproof is found, A CloGUnaryInf with the resulting subproof, and the applied dChoiceR()
 * rule is returned. Otherwise, the subProof itself is returned, which can be noProof()
 * or cantApply().
 * If the "dChoice" rule could not be applied to any term in the sequent, cantApply() is returned.
 */
MaybeProof tryApplyDChoice(CloGSequent seq, CloSeqs cloSeqs, list[CloGSequent] fpSeqs, int depth) {
	for (int termIdx <- [0 .. size(seq)]) {
		MaybeSequent resSeq = applyDChoice(seq, termIdx);
		if (resSeq != noSeq()) {
			MaybeProof subProof = proofSearch(resSeq.seq, cloSeqs, fpSeqs, depth - 1);
			if (subProof != noProof() && subProof != cantApply()) {
				seq[termIdx].active = true;
				return proof(CloGUnaryInf(seq, dChoiceR(), subProof.p));
			}
			return subProof;
		}
	}
		
	return cantApply();
}


/* 
 * A function applying the "concat" rule to a term
 * 
 * Input:  the sequent and the index of the term therein to which to apply the "concat" rule
 * Output: the sequent resulting from applying the "concat" rule
 *
 * For the rule to be applied, the term at the specified index must be of
 * the form "(<gamma; delta>phi)^a".
 * 
 * If this condition is met, the specified term in the given sequent is replaced by
 * the term "(<gamma><delta>phi)^a" and the sequent is returned. Otherwise, noSeq()
 * is returned.
 */
MaybeSequent applyConcat(CloGSequent seq, int termIdx) {
	if (term(\mod(concat(Game gamma, Game delta), GameLog phi), list[CloGName] a, _) := seq[termIdx]) {
		seq[termIdx] = term(\mod(gamma, \mod(delta, phi)), a, false);
		return sequent(seq);
	}
	return noSeq();
}

/* 
 * A function applying the "concat" rule to a sequent and calling the main
 * proof search algorithm on the resulting sequent.
 * 
 * For any of the terms in the sequent, the algorithm tries to apply the "concat"
 * rule. For the first successful application, a proof search is done on the resulting sequent.
 * If a subproof is found, A CloGUnaryInf with the resulting subproof, and the applied concatR()
 * rule is returned. Otherwise, the subProof itself is returned, which can be noProof()
 * or cantApply().
 * If the "concat" rule could not be applied to any term in the sequent, cantApply() is returned.
 */
MaybeProof tryApplyConcat(CloGSequent seq, CloSeqs cloSeqs, list[CloGSequent] fpSeqs, int depth) {
	for (int termIdx <- [0 .. size(seq)]) {
		MaybeSequent resSeq = applyConcat(seq, termIdx);
		if (resSeq != noSeq()) {
			MaybeProof subProof = proofSearch(resSeq.seq, cloSeqs, fpSeqs, depth - 1);
			if (subProof != noProof() && subProof != cantApply()) {
				seq[termIdx].active = true;
				return proof(CloGUnaryInf(seq, concatR(), subProof.p));
			}
			return subProof;
		}
	}
		
	return cantApply();
}

/* 
 * A function applying the "test" rule to a term
 * 
 * Input:  the sequent and the index of the term therein to which to apply the "test" rule
 * Output: the sequent resulting from applying the "test" rule
 *
 * For the rule to be applied, the term at the specified index must be of
 * the form "(<psi?>phi)^a".
 * 
 * If this condition is met, the specified term in the given sequent is replaced by
 * the term "(psi & phi)^a" and the sequent is returned. Otherwise, noSeq() is returned.
 */
MaybeSequent applyTest(CloGSequent seq, int termIdx) {
	if (term(\mod(\test(GameLog psi), GameLog phi), list[CloGName] a, _) := seq[termIdx]) {
		seq[termIdx] = term(and(psi, phi), a, false);
		return sequent(seq);
	}
	return noSeq();
}

/* 
 * A function applying the "test" rule to a sequent and calling the main
 * proof search algorithm on the resulting sequent.
 *
 * For any of the terms in the sequent, the algorithm tries to apply the "test"
 * rule. For the first successful application, a proof search is done on the resulting sequent.
 * If a subproof is found, A CloGUnaryInf with the resulting subproof, and the applied testR()
 * rule is returned. Otherwise, the subProof itself is returned, which can be noProof()
 * or cantApply().
 * If the "test" rule could not be applied to any term in the sequent, cantApply() is returned.
 */
MaybeProof tryApplyTest(CloGSequent seq, CloSeqs cloSeqs, list[CloGSequent] fpSeqs, int depth) {
	for (int termIdx <- [0 .. size(seq)]) {
	
		MaybeSequent resSeq = applyTest(seq, termIdx);
		if (resSeq != noSeq()) {
			MaybeProof subProof = proofSearch(resSeq.seq, cloSeqs, fpSeqs, depth - 1);
			if (subProof != noProof() && subProof != cantApply()) {
				seq[termIdx].active = true;
				return proof(CloGUnaryInf(seq, testR(), subProof.p));
			}
			return subProof;
		}
	}
		
	return cantApply();
}


/* 
 * A function applying the "dTest" rule to a term
 * 
 * Input:  the sequent and the index of the term therein to which to apply the "dTest" rule
 * Output: the sequent resulting from applying the "dTest" rule
 *
 * For the rule to be applied, the term at the specified index must be of
 * the form "(<psi!>phi)^a".
 * 
 * If this condition is met, the specified term in the given sequent is replaced by
 * the term "(psi | phi)^a" and the sequent is returned. Otherwise, noSeq() is returned.
 */
MaybeSequent applyDTest(CloGSequent seq, int termIdx) {
	if (term(\mod(dTest(GameLog psi), GameLog phi), list[CloGName] a, _) := seq[termIdx]) {
		seq[termIdx] = term(or(psi, phi), a, false);
		return sequent(seq);
	}
	return noSeq();
}

/* 
 * A function applying the "dTest" rule to a sequent and calling the main
 * proof search algorithm on the resulting sequent.
 *
 * For any of the terms in the sequent, the algorithm tries to apply the "dTest"
 * rule. For the first successful application, a proof search is done on the resulting sequent.
 * If a subproof is found, A CloGUnaryInf with the resulting subproof, and the applied dTestR()
 * rule is returned. Otherwise, the subProof itself is returned, which can be noProof()
 * or cantApply().
 * If the "dTest" rule could not be applied to any term in the sequent, cantApply() is returned
 */
MaybeProof tryApplyDTest(CloGSequent seq, CloSeqs cloSeqs, list[CloGSequent] fpSeqs, int depth) {
	for (int termIdx <- [0 .. size(seq)]) {
	
		MaybeSequent resSeq = applyDTest(seq, termIdx);
		if (resSeq != noSeq()) {
			MaybeProof subProof = proofSearch(resSeq.seq, cloSeqs, fpSeqs, depth - 1);
			if (subProof != noProof() && subProof != cantApply()) {
				seq[termIdx].active = true;
				return proof(CloGUnaryInf(seq, dTestR(), subProof.p));
			}
			return subProof;
		}
	}
		
	return cantApply();
}

/* 
 * A function applying the "iter" rule to a term
 * 
 * Input:  the sequent and the index of the term therein to which to apply the "iter" rule,
 *         and the list of closure sequents
 * Output: the sequent resulting from applying the "iter" rule
 *
 * For the rule to be applied, the term at the specified index must be of
 * the form "(<gamma*>phi)^a".
 * Each of the names in the label "a" must be smaller than or equal to this
 * "<gamma*>phi" fixpoint formula, according to the order on fixpoint formulae
 * defined in the literature.
 * 
 * If these conditions are met, the specified term in the given sequent is replaced by
 * the term "(phi | <gamma><gamma*>phi)^a" and the sequent is returned. Otherwise,
 * noSeq() is returned.
 */
MaybeSequent applyIter(CloGSequent seq, int termIdx, CloSeqs cloSeqs) {
	if (term(\mod(iter(Game gamma), GameLog phi), list[CloGName] a, _) := seq[termIdx]) {
		for (CloGName x <- a)
			if (!fpLessThanOrEqualTo(cloSeqs[x].contextSeq[cloSeqs[x].fpFormulaIdx].s, \mod(iter(gamma), phi)))
				return noSeq();
				
		seq[termIdx] = term(or(phi, \mod(gamma, \mod(iter(gamma), phi))), a, false);
		return sequent(seq);
	}
	return noSeq();
}

/* 
 * A function applying the "iter" rule to a sequent and calling the main
 * proof search algorithm on the resulting sequent.
 *
 * For any of the terms in the sequent, the algorithm tries to apply the "iter"
 * rule. For the first successful application, a proof search is done on the resulting sequent.
 * If a subproof is found, the current sequent is added to the list of fixpoint sequents,
 * and a CloGUnaryInf with the resulting subproof, and the applied iterR() rule is returned.
 * Otherwise, the subProof itself is returned, which can be noProof() or cantApply().
 * If the "iter" rule could not be applied to any term in the sequent, cantApply() is returned.
 */
MaybeProof tryApplyIter(CloGSequent seq, CloSeqs cloSeqs, list[CloGSequent] fpSeqs, int depth) {
	for (int termIdx <- [0 .. size(seq)]) {
	
		MaybeSequent resSeq = applyIter(seq, termIdx, cloSeqs);
		
		if (resSeq != noSeq()) {
			fpSeqs += [seq];
			MaybeProof subProof = proofSearch(resSeq.seq, cloSeqs, fpSeqs, depth - 1);
			if (subProof != noProof() && subProof != cantApply()) {
				seq[termIdx].active = true;
				return proof(CloGUnaryInf(seq, iterR(), subProof.p));
			}
			return subProof;
		}
	}	
	return cantApply();	
}

/* 
 * A function applying the "clo" rule to a term
 * 
 * Input:  the sequent and the index of the term therein to which to apply the "clo" rule,
 *         and the list of closure sequents
 * Output: a tuple containing the sequent resulting from applying the clo rule, and
 *         the new name associated with the fixpoint formula of the term that the rule
 *         was applied to
 *
 * For the rule to be applied, the term at the specified index must be of
 * the form "(<gamma^x>phi)^a".
 * Each of the names in the label "a" must be smaller than or equal to this
 * "(<gamma^x>phi)^a" fixpoint formula, according to the order on fixpoint formulae
 * defined in the literature.
 *
 * If these conditions are met, a new name is created, x_n, where n is the
 * number of closure sequents (or closure sequents names, named x_0 to x_{n-1})
 * currently in the list of closure sequents, and the specified term in the given
 * sequent is replaced by the term "(phi & <gamma><gamma^x>phi)^{a + x_n}" and a
 * tuple of this sequent and the new associated name is returned. Otherwise, a tuple
 * of noSeq() and an empty name is returned.
 */
tuple[MaybeSequent, CloGName] applyClo(CloGSequent seq, int termIdx, CloSeqs cloSeqs) {
	if (term(\mod(dIter(Game gamma), GameLog phi), list[CloGName] a, _) := seq[termIdx]) {
	
		for (CloGName x <- a) {
			GameLog cloForm = cloSeqs[x].contextSeq[cloSeqs[x].fpFormulaIdx].s;
			if (!fpLessThanOrEqualTo(cloForm, \mod(dIter(gamma), phi)))
				return <noSeq(), name("")>;
		}
		
		CloGName newName = nameS("x", size(cloSeqs));
	
		seq[termIdx] = term(and(phi, \mod(gamma, \mod(dIter(gamma), phi))), a + newName, false);
		return <sequent(seq), newName>;
	}
	return <noSeq(), name("")>;
}

/* 
 * A function applying the "clo" rule to a sequent and calling the main
 * proof search algorithm on the resulting sequent.
 *
 * For any of the terms in the sequent, the algorithm tries to apply the "clo"
 * rule. For all successful applications, a proof search is done on the resulting sequent.
 * If a subproof is found, the current sequent is added to the list of fixpoint sequents,
 * and the new name associated with the closure rule application is added to the closure
 * sequents as the key to the associated context sequence and the index of the term in the
 * sequent that contains the relevant fixpoint formula.
 * 
 * If a subproof is found, a CloGUnaryInf with the resulting subproof, and the applied clo()
 * rule (with the new name) is returned. 
 * If the "clo" rule could not be applied to any term in the sequent, cantApply() is returned.
 * If the "clo" rule could be applied to a term in the sequent, but no subproof was found,
 * noProof() is returned.
 */
MaybeProof tryApplyClo(CloGSequent seq, CloSeqs cloSeqs, list[CloGSequent] fpSeqs, int depth) {
	bool canApply = false;

	for (int termIdx <- [0 .. size(seq)]) {
	
		tuple[MaybeSequent resSeq, CloGName newName] res = applyClo(seq, termIdx, cloSeqs);
		if (res.resSeq != noSeq()) {
			canApply = true;
		
			cloSeqs += (res.newName: <seq, termIdx>);
			fpSeqs += [seq];
			MaybeProof subProof = proofSearch(res.resSeq.seq, cloSeqs, fpSeqs, depth - 1);
			if (subProof != noProof() && subProof != cantApply()) {
				seq[termIdx].active = true;
				return proof(CloGUnaryInf(seq, clo(res.newName), subProof.p));
			}
		}
	}
	return canApply ? noProof() : cantApply();
}