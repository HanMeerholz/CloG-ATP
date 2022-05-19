module RuleApplications
/*
 * Module providing the functions for each of the rule applications.
 */

import ATP_Base;
import GLASTs;
import Map;
import List;
import ProofSearch;
//import Exception;

import IO;

/* 
 * A function applying the ax1 axiom to a term
 * 
 * Input:  the sequent
 * Output: the sequent resulting from applying the ax1 axiom
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
		println("applied ax1");
		return sequent([]);
	}
	
	if (term(atomP(Prop p), [], _) := seq[1] && term(neg(atomP(p)), [], _) := seq[0]) {
		println("applied ax1");
		return sequent([]);
	}
	
	return noSeq();
}

/*
 * A function applying the ax1 rule after some potential weakening and
 * expanding of the terms in the sequent.
 * 
 * Input:  the sequent to which the rule is applied
 * Output: either the CloGProof found after applying weakening/expanding,
 *         and the ax1() axiom to the sequent, or noProof() if no such
 *         proof could be found
 *
 * If there are two terms "p^a", and "~p^a", the weak rule is applied
 * to the remaining terms, and the exp rule is used to obtain "p^[]" and
 * "~p^[]". At this point, the ax1 rule can be applied, and the complete
 * proof is returned.
 * 
 * If no such terms exist, noProof() is returned.
 */
MaybeProof tryApplyAx1(CloGSequent seq, int depth) {
	for (int termIdx <- [0 .. size(seq)]) {
		if (term(atomP(Prop p), _, _) := seq[termIdx]) {
			for (int termIdx2 <- [0 .. size(seq)]) {
				if (term(neg(atomP(p)), _, _) := seq[termIdx2]) {
					
					CloGSequent weakenTo = [term(atomP(p), [], true), term(neg(atomP(p)), [], true)];
					
					resSeq = applyAx1(weakenTo);
					if (resSeq != noSeq())
						return proofSearchWeakExp(seq, weakenTo, CloGUnaryInf(weakenTo, ax1(), CloGLeaf()), depth - 1);
				}
			}
		}
	}
	
	return noProof();
}

/*
 * All of the remaining tryApply<rulename> functions defined in here have the
 * following inputs' and outputs: 
 *
 * Input:  the sequent to which the rule is applied, the map of closure
 *         sequents, the list of fixpoint sequents, and the current depth
 * Output: either the CloGProof found after applying the rule to the sequent,
 *         or noProof() if no such proof could be found
 */
 
/* A function applying the modm rule to a term
 * 
 * Input:  the sequent to apply the modm rule to
 * Output: the sequent resulting from applying the modm rule
 *
 * For the rule to be applied, there must be two terms in the sequent, of forms "<g>phi^a" and
 * "<g^d>psi^b"
 * 
 * If these conditions are met, a sequent containing "phi^a" and "psi^b" is returned.
 */
MaybeSequent applyModm(CloGSequent seq) {

	if (size(seq) != 2)
		return noSeq();
		
	if (term(\mod(Game g, GameLog phi), list[CloGName] a, _) := seq[0] && term(\mod(dual(g), GameLog psi), list[CloGName] b, _) := seq[1]) {
		println("applied modm");
		return sequent([term(phi, a, false), term(psi, b, false)]);
	}
	if (term(\mod(Game g, GameLog phi), list[CloGName] a, _) := seq[1] && term(\mod(dual(g), GameLog psi), list[CloGName] b, _) := seq[0]) {
		println("applied modm");
		return sequent([term(psi, b, false), term(phi, a, false)]);
	}
	
	return noSeq();
}

/*
 * A function applying the modm rule to a sequent, after some potential 
 * weakening of the terms in the given sequent. The main proofSearch()
 * algorithm is called on the sequent resulting from applying this modm rule.
 *
 * For the rule to be applied, there must be 2 terms in the sequent of the
 * form "<g>phi^[a]", and "~<g^d>psi^[b]". The remaining terms are removed by
 * weakening rules, and a proof search is done on the resulting sequent.
 * 
 * If no proof could be found in this proof search, or there are no 2 terms
 * of the appropriate form, noSeq() is returned.
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
						if (subProof != noProof()) {
							resSeq.seq[0].active = true;
							resSeq.seq[1].active = true;
							subProof2 = CloGUnaryInf(weakenTo, modm(), subProof.p);
							return proofSearchWeakExp(seq, weakenTo, subProof2, depth);
						}
					}
				}
			}
		}
	}
	
	return noProof();
}

/* 
 * A function applying the and rule to a term
 * 
 * Input:  the sequent and the index of the term therein to apply the and rule to
 * Output: the sequent resulting from applying the and rule
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
		println("applied and");
		
		copySeq = seq;
		seq[termIdx] = term(phi, a, false);
		copySeq[termIdx] = term(psi, a, false);
		
		return sequents(seq, copySeq);
	}
	return noSeqs();
}

/*
 * A function applying the "and" rule to a sequent and calling the main
 * proof search algorithm on the resulting sequents.
 *
 * For any of the terms in the sequent, the algorithm checks tries to apply the and
 * rule. For all successful applications, a proof search is done on the resulting sequent.
 * If a subproof is found, A CloGBinaryInf with the resulting subproofs, is returned.
 * Otherwise, noProof() is returned.
 */
MaybeProof tryApplyAnd(CloGSequent seq, CloSeqs cloSeqs, list[CloGSequent] fpSeqs, int depth) {		
	for (int termIdx <- [0 .. size(seq)]) {
		MaybeSequents resSeqs = applyAnd(seq, termIdx);
		if (resSeqs != noSeqs()) {
			MaybeProof subProofL = proofSearch(resSeqs.left, cloSeqs, fpSeqs, depth - 1);
			MaybeProof subProofR = proofSearch(resSeqs.right, cloSeqs, fpSeqs, depth - 1);
			if (subProofL != noProof() && subProofR != noProof()) {
				seq[termIdx].active = true;
				return proof(CloGBinaryInf(seq, subProofL.p, subProofR.p));
			}
		}
	}
	
	return noProof();
}

/* 
 * A function applying the or rule to a term
 * 
 * Input:  the sequent and the index of the term therein to apply the or rule to
 * Output: the sequent resulting from applying the or rule
 *
 * For the rule to be applied, the term at the specified index must be of
 * the form "(phi | psi)^a".
 * 
 * If this condition is met, the specified term in the given sequent is replaced by two
 * terms "phi^a", and "psi^a" and the sequent is returned. Otherwise, noSeq() is returned.
 */
MaybeSequent applyOr(CloGSequent seq, int termIdx) {
	if (term(or(GameLog phi, GameLog psi), list[CloGName] a, _) := seq[termIdx]) {
		println("applied or");
		return sequent(seq[0 .. termIdx] + term(phi, a, false) + term(psi, a, false) + seq[termIdx+1 .. size(seq)]);
	}
	return noSeq();
}

/*
 * A function applying the "or" rule to a sequent and calling the main
 * proof search algorithm on the resulting sequent.
 * 
 * For any of the terms in the sequent, the algorithm checks tries to apply the or
 * rule. For all successful applications, a proof search is done on the resulting sequent.
 * If a subproof is found, A CloGUnaryInf with the resulting subproof, and the applied orR()
 * rule is returned. Otherwise, noProof() is returned.
 */
MaybeProof tryApplyOr(CloGSequent seq, CloSeqs cloSeqs, list[CloGSequent] fpSeqs, int depth) {	
	for (int termIdx <- [0 .. size(seq)]) {
		MaybeSequent resSeq = applyOr(seq, termIdx);
		if (resSeq != noSeq()) {
			MaybeProof subProof = proofSearch(resSeq.seq, cloSeqs, fpSeqs, depth - 1);
			if (subProof != noProof()) {
				seq[termIdx].active = true;
				return proof(CloGUnaryInf(seq, orR(), subProof.p));		
			}
		}
	}
	
	return noProof();
}

/* 
 * A function applying the or rule to a term
 * 
 * Input:  the sequent and the index of the term therein to apply the choice rule to
 * Output: the sequent resulting from applying the choice rule
 *
 * For the rule to be applied, the term at the specified index must be of
 * the form "(<gamma || delta>phi)^a".
 * 
 * If this condition is met, the specified term in the given sequent is replaced by
 * two term "(<gamma>phi | <delta> phi)^a" and the sequent is returned. Otherwise,
 * noSeq() is returned.
 */
MaybeSequent applyChoice(CloGSequent seq, int termIdx) {
	if (term(\mod(choice(Game gamma, Game delta), GameLog phi), list[CloGName] a, _) := seq[termIdx]) {
		println("applied choice");
		seq[termIdx] = term(or(\mod(gamma, phi), \mod(delta, phi)), a, false);
		return sequent(seq);
	}
	return noSeq();
}

/* 
 * A function applying the choice rule to a sequent and calling the main
 * proof search algorithm on the resulting sequent.
 *
 * For any of the terms in the sequent, the algorithm checks tries to apply the choice
 * rule. For all successful applications, a proof search is done on the resulting sequent.
 * If a subproof is found, A CloGUnaryInf with the resulting subproof, and the applied
 * choiceR() rule is returned. Otherwise, noProof() is returned.
 */
MaybeProof tryApplyChoice(CloGSequent seq, CloSeqs cloSeqs, list[CloGSequent] fpSeqs, int depth) {
	for (int termIdx <- [0 .. size(seq)]) {
		MaybeSequent resSeq = applyChoice(seq, termIdx);
		if (resSeq != noSeq()) {
			MaybeProof subProof = proofSearch(resSeq.seq, cloSeqs, fpSeqs, depth - 1);
			if (subProof != noProof()) {
				seq[termIdx].active = true;
				return proof(CloGUnaryInf(seq, choiceR(), subProof.p));
			}
		}
	}

	return noProof();
}

/* 
 * A function applying the dChoice rule to a term
 * 
 * Input:  the sequent and the index of the term therein to apply the dChoice rule to
 * Output: the sequent resulting from applying the dChoice rule
 *
 * For the rule to be applied, the term at the specified index must be of
 * the form "(<gamma && delta>phi)^a".
 * 
 * If this condition is met, the specified term in the given sequent is replaced by
 * two term "(<gamma>phi & <delta> phi)^a" and the sequent is returned. Otherwise,
 * noSeq() is returned.
 */
MaybeSequent applyDChoice(CloGSequent seq, int termIdx) {
	if (term(\mod(dChoice(Game gamma, Game delta), GameLog phi), list[CloGName] a, _) := seq[termIdx]) {
		println("applied dChoice");
		seq[termIdx] = term(and(\mod(gamma, phi), \mod(delta, phi)), a, false);
		return sequent(seq);
	}
	return noSeq();
}

/* 
 * A function applying the dChoice rule to a sequent and calling the main
 * proof search algorithm on the resulting sequent.
 *
 * For any of the terms in the sequent, the algorithm checks tries to apply the dChoice
 * rule. For all successful applications, a proof search is done on the resulting sequent.
 * If a subproof is found, A CloGUnaryInf with the resulting subproof, and the applied
 * dChoiceR() rule is returned. Otherwise, noProof() is returned.
 */
MaybeProof tryApplyDChoice(CloGSequent seq, CloSeqs cloSeqs, list[CloGSequent] fpSeqs, int depth) {
	for (int termIdx <- [0 .. size(seq)]) {
		MaybeSequent resSeq = applyDChoice(seq, termIdx);
		if (resSeq != noSeq()) {
			MaybeProof subProof = proofSearch(resSeq.seq, cloSeqs, fpSeqs, depth - 1);
			if (subProof != noProof()) {
				seq[termIdx].active = true;
				return proof(CloGUnaryInf(seq, dChoiceR(), subProof.p));
			}
		}
	}
		
	return noProof();
}


/* 
 * A function applying the concat rule to a term
 * 
 * Input:  the sequent and the index of the term therein to apply the concat rule to
 * Output: the sequent resulting from applying the concat rule
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
		println("applied concat");
		seq[termIdx] = term(\mod(gamma, \mod(delta, phi)), a, false);
		return sequent(seq);
	}
	return noSeq();
}

/* 
 * A function applying the concat rule to a sequent and calling the main
 * proof search algorithm on the resulting sequent.
 * 
 * For any of the terms in the sequent, the algorithm checks tries to apply the concat
 * rule. For all successful applications, a proof search is done on the resulting sequent.
 * If a subproof is found, A CloGUnaryInf with the resulting subproof, and the applied
 * concatR() rule is returned. Otherwise, noProof() is returned.
 */
MaybeProof tryApplyConcat(CloGSequent seq, CloSeqs cloSeqs, list[CloGSequent] fpSeqs, int depth) {
	for (int termIdx <- [0 .. size(seq)]) {
		MaybeSequent resSeq = applyConcat(seq, termIdx);
		if (resSeq != noSeq()) {
			MaybeProof subProof = proofSearch(resSeq.seq, cloSeqs, fpSeqs, depth - 1);
			if (subProof != noProof()) {
				seq[termIdx].active = true;
				return proof(CloGUnaryInf(seq, concatR(), subProof.p));
			}
		}
	}
		
	return noProof();
}

///* 
// * 
// */
//MaybeSequent applyWeak(CloGSequent seq, int termIdx) {
//	println("applied weak");
//	return sequent(seq - seq[termIdx]);
//}
//
///* 
// * 
// */
//MaybeProof tryApplyWeak(CloGSequent seq, CloSeqs cloSeqs, list[CloGTerm] fpAppl, int depth) {
//	for (int termIdx <- [0 .. size(seq)]) {
//		MaybeSequent resSeq = applyWeak(seq, termIdx);
//		if (resSeq != noSeq()) {
//			MaybeProof subProof = proofSearch(resSeq.seq, cloSeqs, fpAppl, depth - 1);
//			if (subProof != noProof()) {
//				seq[termIdx].active = true;
//				return proof(CloGUnaryInf(seq, weak(), subProof.p));
//			}
//		}
//	}
//		
//	return noProof();
//}

///* 
// * 
// */
//MaybeSequent applyExp(CloGSequent seq, int termIdx, int nameIdx) {
//	if (term(GameLog phi, list[CloGName] a, _) := seq[termIdx]) {
//		println("applied exp");
//		seq[termIdx] = term(phi, a - a[nameIdx], false);
//		return sequent(seq);
//	}
//	return noSeq();
//}
//
///* 
// * 
// */
//MaybeProof tryApplyExp(CloGSequent seq, CloSeqs cloSeqs, list[CloGTerm] fpAppl, int depth) {
//	for (int termIdx <- [0 .. size(seq)]) {
//		for (int nameIdx <- [0 .. size(seq[termIdx].label)]) {
//			MaybeSequent resSeq = applyExp(seq, termIdx, nameIdx);
//			if (resSeq != noSeq()) {
//				MaybeProof subProof = proofSearch(resSeq.seq, cloSeqs, fpAppl, depth - 1);
//				if (subProof != noProof()) {
//					seq[termIdx].active = true;
//					return proof(CloGUnaryInf(seq, exp(), subProof.p));
//				}
//			}
//		}
//	}
//		
//	return noProof();
//}

/* 
 * A function applying the iter rule to a term
 * 
 * Input:  the sequent and the index of the term therein to apply the iter rule to,
 *         and the list of closure sequents
 * Output: the sequent resulting from applying the iter rule
 *
 * For the rule to be applied, the term at the specified index must be of
 * the form "(<gamma*>phi)^a".
 * Each of the names in the label a must be smaller than or equal to this
 * "<gamma*>phi" fixpoint formula, according to the order on fixpoint formulae
 * defined in the literature.
 * 
 * If these conditions is met, the specified term in the given sequent is replaced by
 * the term "(phi | <gamma><gamma*>phi)^a" and the sequent is returned. Otherwise,
 * noSeq() is returned.
 */
MaybeSequent applyIter(CloGSequent seq, int termIdx, CloSeqs cloSeqs) {
	if (term(\mod(iter(Game gamma), GameLog phi), list[CloGName] a, _) := seq[termIdx]) {
	
		for (CloGName x <- a)
			if (!fpLessThanOrEqualTo(cloSeqs[x].contextSeq[cloSeqs[x].fpFormulaIdx].s, \mod(iter(gamma), phi)))
				return noSeq();
				
		println("applied iter");
		seq[termIdx] = term(or(phi, \mod(gamma, \mod(iter(gamma), phi))), a, false);
		return sequent(seq);
	}
	return noSeq();
}

/* 
 * A function applying the iter rule to a sequent and calling the main
 * proof search algorithm on the resulting sequent.
 *
 * For any of the terms in the sequent, the algorithm checks tries to apply the iter
 * rule. For all successful applications, a proof search is done on the resulting sequent.
 * If a subproof is found, the current sequent is added to the list of fixpoint sequents,
 * and a CloGUnaryInf with the resulting subproof, and the applied iterR() rule is returned.
 * Otherwise, noProof() is returned.
 */
MaybeProof tryApplyIter(CloGSequent seq, CloSeqs cloSeqs, list[CloGSequent] fpSeqs, int depth) {
	for (int termIdx <- [0 .. size(seq)]) {
	
		MaybeSequent resSeq = applyIter(seq, termIdx, cloSeqs);
		
		if (resSeq != noSeq()) {
			fpSeqs += [seq];
			MaybeProof subProof = proofSearch(resSeq.seq, cloSeqs, fpSeqs, depth - 1);
			if (subProof != noProof()) {
				seq[termIdx].active = true;
				return proof(CloGUnaryInf(seq, iterR(), subProof.p));
			}
		}
	}	
	return noProof();	
}

/* 
 * A function applying the test rule to a term
 * 
 * Input:  the sequent and the index of the term therein to apply the test rule to
 * Output: the sequent resulting from applying the test rule
 *
 * For the rule to be applied, the term at the specified index must be of
 * the form "(<psi?>phi)^a".
 * 
 * If this condition is met, the specified term in the given sequent is replaced by
 * the term "(phi & psi)^a" and the sequent is returned. Otherwise, noSeq() is returned.
 */
MaybeSequent applyTest(CloGSequent seq, int termIdx) {
	if (term(\mod(\test(GameLog psi), GameLog phi), list[CloGName] a, _) := seq[termIdx]) {
		println("applied test");
		seq[termIdx] = term(and(psi, phi), a, false);
		return sequent(seq);
	}
	return noSeq();
}

/* 
 * A function applying the test rule to a sequent and calling the main
 * proof search algorithm on the resulting sequent.
 *
 * For any of the terms in the sequent, the algorithm checks tries to apply the test
 * rule. For all successful applications, a proof search is done on the resulting sequent.
 * If a subproof is found, A CloGUnaryInf with the resulting subproof, and the applied
 * testR() rule is returned. Otherwise, noProof() is returned.
 */
MaybeProof tryApplyTest(CloGSequent seq, CloSeqs cloSeqs, list[CloGSequent] fpSeqs, int depth) {
	for (int termIdx <- [0 .. size(seq)]) {
	
		MaybeSequent resSeq = applyTest(seq, termIdx);
		if (resSeq != noSeq()) {
			MaybeProof subProof = proofSearch(resSeq.seq, cloSeqs, fpSeqs, depth - 1);
			if (subProof != noProof()) {
				seq[termIdx].active = true;
				return proof(CloGUnaryInf(seq, testR(), subProof.p));
			}
		}
	}
		
	return noProof();
}

/* 
 * A function applying the dIter rule to a term
 * 
 * Input:  the sequent and the index of the term therein to apply the dIter rule to,
 *         and the list of closure sequents
 * Output: the sequent resulting from applying the dIter rule
 *
 * For the rule to be applied, the term at the specified index must be of
 * the form "(<gamma^x>phi)^a".
 * Each of the names in the label a must be smaller than or equal to this
 * "(<gamma^x>phi)^a" fixpoint formula, according to the order on fixpoint formulae
 * defined in the literature.
 * 
 * If these conditions is met, the specified term in the given sequent is replaced by
 * the term "(phi & <gamma><gamma^x>phi)^a" and the sequent is returned. Otherwise,
 * noSeq() is returned.
 */
MaybeSequent applyDIter(CloGSequent seq, int termIdx, CloSeqs cloSeqs) {
	if (term(\mod(dIter(Game gamma), GameLog phi), list[CloGName] a, _) := seq[termIdx]) {
	
		for (CloGName x <- a)
			if (!fpLessThanOrEqualTo(cloSeqs[x].contextSeq[cloSeqs[x].fpFormulaIdx].s, \mod(dIter(gamma), phi)))
				return noSeq();
	
		println("applied dIter");
		seq[termIdx] = term(and(phi, \mod(gamma, \mod(dIter(gamma), phi))), a, false);
		return sequent(seq);
	}
	return noSeq();
}

/* 
 * A function applying the dIter rule to a sequent and calling the main
 * proof search algorithm on the resulting sequent.
 *
 * For any of the terms in the sequent, the algorithm checks tries to apply the dIter
 * rule. For all successful applications, a proof search is done on the resulting sequent.
 * If a subproof is found, the current sequent is added to the list of fixpoint sequents,
 * and a CloGUnaryInf with the resulting subproof, and the applied dIterR() rule is returned.
 * Otherwise, noProof() is returned.
 */
MaybeProof tryApplyDIter(CloGSequent seq, CloSeqs cloSeqs, list[CloGSequent] fpSeqs, int depth) {
	for (int termIdx <- [0 .. size(seq)]) {
	
		MaybeSequent resSeq = applyDIter(seq, termIdx, cloSeqs);
		if (resSeq != noSeq()) {
			fpSeqs += [seq];
			MaybeProof subProof = proofSearch(resSeq.seq, cloSeqs, fpAppl, depth - 1);
			if (subProof != noProof()) {
				seq[termIdx].active = true;
				return proof(CloGUnaryInf(seq, dIterR(), subProof.p));
			}
		}
	}	
	return noProof();
}

/* 
 * A function applying the dTest rule to a term
 * 
 * Input:  the sequent and the index of the term therein to apply the dTest rule to
 * Output: the sequent resulting from applying the dTest rule
 *
 * For the rule to be applied, the term at the specified index must be of
 * the form "(<psi!>phi)^a".
 * 
 * If this condition is met, the specified term in the given sequent is replaced by
 * the term "(phi | psi)^a" and the sequent is returned. Otherwise, noSeq() is returned.
 */
MaybeSequent applyDTest(CloGSequent seq, int termIdx) {
	if (term(\mod(dTest(GameLog psi), GameLog phi), list[CloGName] a, _) := seq[termIdx]) {
		println("applied dTest");
		seq[termIdx] = term(or(psi, phi), a, false);
		return sequent(seq);
	}
	return noSeq();
}

/* 
 * A function applying the test rule to a sequent and calling the main
 * proof search algorithm on the resulting sequent.
 *
 * For any of the terms in the sequent, the algorithm checks tries to apply the dTest
 * rule. For all successful applications, a proof search is done on the resulting sequent,
 * If a subproof is found, A CloGUnaryInf with the resulting subproof, and the applied
 * dTestR() rule is returned. Otherwise, noProof() is returned.
 */
MaybeProof tryApplyDTest(CloGSequent seq, CloSeqs cloSeqs, list[CloGSequent] fpSeqs, int depth) {
	for (int termIdx <- [0 .. size(seq)]) {
	
		MaybeSequent resSeq = applyDTest(seq, termIdx);
		if (resSeq != noSeq()) {
			MaybeProof subProof = proofSearch(resSeq.seq, cloSeqs, fpSeqs, depth - 1);
			if (subProof != noProof()) {
				seq[termIdx].active = true;
				return proof(CloGUnaryInf(seq, dTestR(), subProof.p));
			}
		}
	}
		
	return noProof();
}

/* 
 * A function applying the clo rule to a term
 * 
 * Input:  the sequent and the index of the term therein to apply the clo rule to,
 *         and the list of closure sequents
 * Output: a tuple containing the sequent resulting from applying the clo rule, and
 *         the new name associated with the sequent
 *
 * For the rule to be applied, the term at the specified index must be of
 * the form "(<gamma^x>phi)^a".
 * Each of the names in the label a must be smaller than or equal to this
 * "(<gamma^x>phi)^a" fixpoint formula, according to the order on fixpoint formulae
 * defined in the literature.
 *
 * If these conditions are met, a new name is created, x_n, where n is the
 * number of closure sequents (or closure sequents names, named x_0 to x_{n-1}),
 * and the specified term in the given sequent is replaced by the term
 * "(phi & <gamma><gamma^x>phi)^{a + x_n}" and a pair of this sequent, and the
 * new associated name is returned. Otherwise, a pair of noSeq() and an empty name
 * is returned.
 */
tuple[MaybeSequent, CloGName] applyClo(CloGSequent seq, int termIdx, CloSeqs cloSeqs) {
	if (term(\mod(dIter(Game gamma), GameLog phi), list[CloGName] a, _) := seq[termIdx]) {
	
		for (CloGName x <- a)
			if (!fpLessThanOrEqualTo(cloSeqs[x].contextSeq[cloSeqs[x].fpFormulaIdx].s, \mod(dIter(gamma), phi)))
				return <noSeq(), name("")>;

		CloGName newName = nameS("x", size(cloSeqs));
	
		println("applied clo");
		seq[termIdx] = term(and(phi, \mod(gamma, \mod(dIter(gamma), phi))), a + newName, false);
		return <sequent(seq), newName>;
	}
	return <noSeq(), name("")>;
}

/* 
 * A function applying the clo rule to a sequent and calling the main
 * proof search algorithm on the resulting sequent.
 *
 * For any of the terms in the sequent, the algorithm checks tries to apply the clo
 * rule. For all successful applications, a proof search is done on the resulting sequent.
 * If a subproof is found, the current sequent is added to the list of fixpoint sequents,
 * and the new name associated with the closure rule application is added to the closure
 * sequents as the key to the associated context sequence and the index of the term in the
 * sequent that contains the relevant fixpoint formula.
 * 
 * A CloGUnaryInf with the resulting subproof, and the applied clo() rule (with the new name)
 * is returned. Otherwise, noProof() is returned.
 */
MaybeProof tryApplyClo(CloGSequent seq, CloSeqs cloSeqs, list[CloGSequent] fpSeqs, int depth) {

	for (int termIdx <- [0 .. size(seq)]) {
	
		tuple[MaybeSequent resSeq, CloGName newName] res = applyClo(seq, termIdx, cloSeqs);
	
		if (res.resSeq != noSeq()) {
			cloSeqs += (res.newName: <seq, termIdx>);
			fpSeqs += [seq];
			MaybeProof subProof = proofSearch(res.resSeq.seq, cloSeqs, fpSeqs, depth - 1);
			if (subProof != noProof()) {
				seq[termIdx].active = true;
				return proof(CloGUnaryInf(seq, clo(res.newName), subProof.p));
			}
		}
	}
		
	return noProof();	
}