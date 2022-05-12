module RuleApplications
/*
 * Module providing the functions for each of the rule applications.
 */

import ATP_Base;
import GLASTs;
import Map;
import List;
import ProofSearch;
import Exception;

import IO;

//CloGSequent applyAx1(CloGSequent seq) {
//	if (size(seq) != 2) throw IllegalArgument("Error: incorrect number of terms for ax1 application");
//	
//	if (term(atomP(Prop p), []) := seq[0] && term(neg(atomP(p)), []) := seq[1]) return [];
//	if (term(atomP(Prop p), []) := seq[1] && term(neg(atomP(p)), []) := seq[0]) return [];
//	
//	throw IllegalArgument("Error: incorrect form of terms for ax1 application");
//}

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
MaybeProof tryApplyAx1(CloGSequent seq) {
	for (int termIdx <- [0 .. size(seq)]) {
		if (term(atomP(Prop p), _, _) := seq[termIdx]) {
			for (int termIdx2 <- [0 .. size(seq)]) {
				if (term(neg(atomP(p)), _, _) := seq[termIdx2]) {
					println("applied ax1");
					CloGSequent weakenTo = [term(atomP(p), [], true), term(neg(atomP(p)), [], true)];
					
					return proofSearchWeakExp(seq, weakenTo, CloGUnaryInf(weakenTo, ax1(), CloGLeaf()));
				}
			}
		}
	}
	
	return noProof();
}

/*
 * All of the remaining functions defined in here have the following inputs'
 * and outputs: 
 *
 * Input:  the sequent to which the rule is applied, the map of closure
 *         sequents, the list of fixpoint sequents, and the current depth
 * Output: either the CloGProof found after applying the rule to the sequent,
 *         or noProof() if no such proof could be found
 */

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
					CloGSequent resSeq = [term(phi, a, false), term(psi, b, false)];
					subProof = proofSearch(resSeq, cloSeqs, fpSeqs, depth - 1);
					if (subProof != noProof()) {
						CloGSequent weakenTo = [term(\mod(g, phi), a, true), term(\mod(dual(g), psi), b, true)];
						subProof2 = proofSearchWeakExp(seq, weakenTo, CloGUnaryInf(weakenTo, modm(), subProof.p));
						return subProof2;
					}
				}
			}
		}
	}
	
	return noProof();
}

/*
 * A function applying the and rule to a sequent.
 *
 * For the rule to be applied, the term at the specified index must be of
 * the form "(phi & psi)^a".
 * 
 * If this condition is met, a pair of sequents, such that for one of them, the
 * specified term is replaced by "phi^a", and for the other, it is replaced by
 * "psi^a", is returned. Otherwise, noSeqs() is returned.
 */
MaybeProof tryApplyAnd(CloGSequent seq, CloSeqs cloSeqs, list[CloGSequent] fpSeqs, int depth) {	
	for (int termIdx <- [0 .. size(seq)]) {
	    if (term(and(GameLog phi, GameLog psi), list[CloGName] a, _) := seq[termIdx]) {
			println("applied and");
			CloGSequent resSeqL = seq - seq[termIdx] + term(phi, a, false); 
			CloGSequent resSeqR = seq - seq[termIdx] + term(psi, a, false); 
			
			MaybeProof subProofL = proofSearch(resSeqL, cloSeqs, fpSeqs, depth - 1);
			MaybeProof subProofR = proofSearch(resSeqR, cloSeqs, fpSeqs, depth - 1);
			if (subProofL != noProof() && subProofR != noProof()) {
				seq[termIdx].active = true;
				return proof(CloGBinaryInf(seq, subProofL.p, subProofR.p));
			}
		}
	}
	
	return noProof();
}

/* A function applying the or rule to a term
 * 
 * Input:  the sequent and the index of the term therein to apply the or rule to
 * Output: the sequent resulting from applying the or rule
 */
MaybeSequent applyOr(CloGSequent seq, int termIdx) {
	if (term(or(GameLog phi, GameLog psi), list[CloGName] a, _) := seq[termIdx]) {
		println("applied or");
		return sequent(seq - seq[termIdx] + term(phi, a, false) + term(psi, a, false));
	}
	return noSeq();
}

/*
 * A function applying the or rule to a sequent and calling the main
 * proof search algorithm on the resulting sequent.
 *
 * For the rule to be applied, the term at the specified index must be of
 * the form "(phi | psi)^a".
 * 
 * If this condition is met, a proof search is done on the resulting sequent,
 * which is the given sequent, where the specified term is replaced by two terms
 * "phi^a", and "psi^a". If a subproof is found, A CloGUnaryInf with the resulting
 * subproof, and the applied orR() rule is returned. Otherwise, noProof() is returned.
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
 * A function applying the choice rule to a sequent and calling the main
 * proof search algorithm on the resulting sequent.
 *
 * For the rule to be applied, the term at the specified index must be of
 * the form "(<gamma || delta>phi)^a".
 * 
 * If this condition is met, a proof search is done on the resulting sequent,
 * which is the given sequent, where the specified term is replaced by
 * "(<gamma>phi | <delta> phi)^a". If a subproof is found, A CloGUnaryInf with
 * the resulting subproof, and the applied choiceR() rule is returned. Otherwise,
 * noProof() is returned.
 */
MaybeProof tryApplyChoice(CloGSequent seq, CloSeqs cloSeqs, list[CloGSequent] fpSeqs, int depth) {
	for (int termIdx <- [0 .. size(seq)]) {
		    if (term(\mod(choice(Game gamma, Game delta), GameLog phi), list[CloGName] a, _) := seq[termIdx]) {
				println("applied choice");
				CloGSequent resSeq = seq - seq[termIdx] + term(or(\mod(gamma, phi), \mod(delta, phi)), a, false);
				MaybeProof subProof = proofSearch(resSeq, cloSeqs, fpSeqs, depth - 1);
				if (subProof != noProof()) {
					seq[termIdx].active = true;
					return proof(CloGUnaryInf(seq, choiceR(), subProof.p));
				}
			}
		}
		
	return noProof();
}

/* 
 * A function applying the dChoice rule to a sequent and calling the main
 * proof search algorithm on the resulting sequent.
 *
 * For the rule to be applied, the term at the specified index must be of
 * the form "(<gamma && delta>phi)^a".
 * 
 * If this condition is met, a proof search is done on the resulting sequent,
 * which is the given sequent, where the specified term is replaced by
 * "(<gamma>phi & <delta> phi)^a". If a subproof is found, A CloGUnaryInf with
 * the resulting subproof, and the applied dChoiceR() rule is returned. Otherwise,
 * noProof() is returned.
 */
MaybeProof tryApplyDChoice(CloGSequent seq, CloSeqs cloSeqs, list[CloGSequent] fpSeqs, int depth) {
	for (int termIdx <- [0 .. size(seq)]) {
		    if (term(\mod(dChoice(Game gamma, Game delta), GameLog phi), list[CloGName] a, _) := seq[termIdx]) {
				println("applied dChoice");
				CloGSequent resSeq = seq - seq[termIdx] + term(and(\mod(gamma, phi), \mod(delta, phi)), a, false);
				MaybeProof subProof = proofSearch(resSeq, cloSeqs, fpSeqs, depth - 1);
				if (subProof != noProof()) {
					seq[termIdx].active = true;
					return proof(CloGUnaryInf(seq, dChoiceR(), subProof.p));
				}
			}
		}
		
	return noProof();
}

/* 
 * A function applying the concat rule to a sequent and calling the main
 * proof search algorithm on the resulting sequent.
 *
 * For the rule to be applied, the term at the specified index must be of
 * the form "(<gamma; delta>phi)^a".
 * 
 * If this condition is met, a proof search is done on the resulting sequent,
 * which is the given sequent, where the specified term is replaced by
 * "(<gamma><delta>phi)^a". If a subproof is found, A CloGUnaryInf with the
 * resulting subproof, and the applied concatR() rule is returned. Otherwise,
 * noProof() is returned.
 */
MaybeProof tryApplyConcat(CloGSequent seq, CloSeqs cloSeqs, list[CloGSequent] fpSeqs, int depth) {
	for (int termIdx <- [0 .. size(seq)]) {
		    if (term(\mod(concat(Game gamma, Game delta), GameLog phi), list[CloGName] a, _) := seq[termIdx]) {
				println("applied concat");
				CloGSequent resSeq = seq - seq[termIdx] + term(\mod(gamma, \mod(delta, phi)), a, false);
				MaybeProof subProof = proofSearch(resSeq, cloSeqs, fpSeqs, depth - 1);
				if (subProof != noProof()) {
					seq[termIdx].active = true;
					return proof(CloGUnaryInf(seq, concatR(), subProof.p));
				}
			}
		}
		
	return noProof();
}

/* 
 * A function applying the iter rule to a sequent and calling the main
 * proof search algorithm on the resulting sequent.
 *
 * For the rule to be applied, the term at the specified index must be of
 * the form "(<gamma*>phi)^a".
 * Each of the names in the label a must be smaller than or equal to this
 * "<gamma*>phi" fixpoint formula, according to the order on fixpoint formulae
 * defined in the literature.
 * 
 * If these conditions are met, a proof search is done on the resulting sequent,
 * which is the given sequent, where the specified term is replaced by
 * "(phi | <gamma><gamma*>phi)^a". If a subproof is found, A CloGUnaryInf with
 * the resulting subproof, and the applied iterR() rule is returned. Otherwise,
 * noProof() is returned.
 */
MaybeProof tryApplyIter(CloGSequent seq, CloSeqs cloSeqs, list[CloGSequent] fpSeqs, int depth) {
	for (int termIdx <- [0 .. size(seq)]) {
		if (term(\mod(iter(Game gamma), GameLog phi), list[CloGName] a, _) := seq[termIdx]) {	
			
		
			bool nextTerm = false;
				
			for (CloGName x <- a)
				if (!fpLessThanOrEqualTo(cloSeqs[x].contextSeq[cloSeqs[x].fpFormulaIdx].s, \mod(iter(gamma), phi)))
					nextTerm = true;
			
			if (nextTerm) continue;
			
			fpSeqs += [seq];
			
			println("applied iter");
			CloGSequent resSeq =  seq - seq[termIdx] + term(or(phi, \mod(gamma, \mod(iter(gamma), phi))), a, false);
			
			MaybeProof subProof = proofSearch(resSeq, cloSeqs, fpSeqs, depth - 1);
			if (subProof != noProof()) {
				seq[termIdx].active = true;
				return proof(CloGUnaryInf(seq, iterR(), subProof.p));
			}
		}
	}	
	return noProof();	
}

/* 
 * A function applying the test rule to a sequent and calling the main
 * proof search algorithm on the resulting sequent.
 *
 * For the rule to be applied, the term at the specified index must be of
 * the form "(<psi?>phi)^a".
 * 
 * If this condition is met, a proof search is done on the resulting sequent,
 * which is the given sequent, where the specified term is replaced by
 * "(phi & psi)^a". If a subproof is found, A CloGUnaryInf with the resulting
 * subproof, and the applied testR() rule is returned. Otherwise, noProof()
 * is returned.
 */
MaybeProof tryApplyTest(CloGSequent seq, CloSeqs cloSeqs, list[CloGSequent] fpSeqs, int depth) {
	for (int termIdx <- [0 .. size(seq)]) {
		    if (term(\mod(\test(GameLog psi), GameLog phi), list[CloGName] a, _) := seq[termIdx]) {
				println("applied test");
				CloGSequent resSeq = seq - seq[termIdx] + term(and(psi, phi), a, false);
				MaybeProof subProof = proofSearch(resSeq, cloSeqs, fpSeqs, depth - 1);
				if (subProof != noProof()) {
					seq[termIdx].active = true;
					return proof(CloGUnaryInf(seq, testR(), subProof.p));
				}
			}
		}
		
	return noProof();
}

/* 
 * A function applying the dIter rule to a sequent and calling the main
 * proof search algorithm on the resulting sequent.
 *
 * For the rule to be applied, the term at the specified index must be of
 * the form "(<gamma^x>phi)^a".
 * Each of the names in the label a must be smaller than or equal to this
 * "<gamma^x>phi" fixpoint formula, according to the order on fixpoint formulae
 * defined in the literature.
 * 
 * If these conditions are met, a proof search is done on the resulting sequent,
 * which is the given sequent, where the specified term is replaced by
 * "(phi & <gamma><gamma^x>phi)^a". If a subproof is found, A CloGUnaryInf with
 * the resulting subproof, and the applied dIterR() rule is returned. Otherwise,
 * noProof() is returned.
 */
MaybeProof tryApplyDIter(CloGSequent seq, CloSeqs cloSeqs, list[CloGSequent] fpSeqs, int depth) {
	for (int termIdx <- [0 .. size(seq)]) {
		if (term(\mod(dIter(Game gamma), GameLog phi), list[CloGName] a, _) := seq[termIdx]) {	
			bool nextTerm = false;
				
			for (CloGName x <- a)
				if (!fpLessThanOrEqualTo(cloSeqs[x].contextSeq[cloSeqs[x].fpFormulaIdx].s, \mod(dIter(gamma), phi)))
					nextTerm = true;
			
			if (nextTerm) continue;
			
			fpSeqs += [seq];
			
			println("applied dIter");
			CloGSequent resSeq =  seq - seq[termIdx] + term(and(phi, \mod(gamma, \mod(dIter(gamma), phi))), a, false);
			
			MaybeProof subProof = proofSearch(resSeq, cloSeqs, fpSeqs, depth - 1);
			if (subProof != noProof()) {
				seq[termIdx].active = true;
				return proof(CloGUnaryInf(seq, dIterR(), subProof.p));
			}
		}				
	}	
	return noProof();	
}


/* 
 * A function applying the test rule to a sequent and calling the main
 * proof search algorithm on the resulting sequent.
 *
 * For the rule to be applied, the term at the specified index must be of
 * the form "(<psi!>phi)^a".
 * 
 * If this condition is met, a proof search is done on the resulting sequent,
 * which is the given sequent, where the specified term is replaced by
 * "(phi | psi)^a". If a subproof is found, A CloGUnaryInf with the resulting
 * subproof, and the applied dTestR() rule is returned. Otherwise, noProof()
 * is returned.
 */
MaybeProof tryApplyDTest(CloGSequent seq, CloSeqs cloSeqs, list[CloGSequent] fpSeqs, int depth) {
	for (int termIdx <- [0 .. size(seq)]) {
		    if (term(\mod(dTest(GameLog psi), GameLog phi), list[CloGName] a, _) := seq[termIdx]) {
				println("applied dTest");
				CloGSequent resSeq = seq - seq[termIdx] + term(or(psi, phi), a, false);
				MaybeProof subProof = proofSearch(resSeq, cloSeqs, fpSeqs, depth - 1);
				if (subProof != noProof()) {
					seq[termIdx].active = true;
					return proof(CloGUnaryInf(seq, dTestR(), subProof.p));
				}
			}
		}
		
	return noProof();
}

/* 
 * A function applying the clo rule to a sequent and calling the main
 * proof search algorithm on the resulting sequent.
 *
 * For the rule to be applied, the term at the specified index must be of
 * the form "(<gamma^x>phi)^a".
 * Each of the names in the label a must be smaller than or equal to this
 * "<gamma^x>phi" fixpoint formula, according to the order on fixpoint formulae
 * defined in the literature.
 *  
 * If these conditions are met, a new label is created, x_n, where n is the
 * number of closure sequents (or closure sequents names, named x_0 to x_{n-1}).
 * This label is added to the closure sequents as the key to the associated context
 * sequence and the index of the term in the sequent that contains the relevant
 * fixpoint formula.
 *
 * Then, a proof search is done on the resulting sequent, which is the given
 * sequent, where the specified term is replaced by "(phi & <gamma><gamma^x>phi)^a".
 * If a subproof is found, A CloGUnaryInf with the resulting subproof, and the
 * applied clo() rule is returned. Otherwise, noProof() is returned.
 */
MaybeProof tryApplyClo(CloGSequent seq, CloSeqs cloSeqs, list[CloGSequent] fpSeqs, int depth) {
	for (int termIdx <- [0 .. size(seq)]) {
		if (term(\mod(dIter(Game gamma), GameLog phi), list[CloGName] a, _) := seq[termIdx]) {	
			bool nextTerm = false;
				
			for (CloGName x <- a)
				if (!fpLessThanOrEqualTo(cloSeqs[x].contextSeq[cloSeqs[x].fpFormulaIdx].s, \mod(dIter(gamma), phi)))
					nextTerm = true;
			
			if (nextTerm) continue;
			
			CloGName newName = nameS("x", size(cloSeqs));
			cloSeqs += (newName: <seq, termIdx>);
			
			fpSeqs += [seq];
			
			println("applied clo");
			CloGSequent resSeq =  seq - seq[termIdx] + term(and(phi, \mod(gamma, \mod(dIter(gamma), phi))), a + newName, false);
			
			MaybeProof subProof = proofSearch(resSeq, cloSeqs, fpSeqs, depth - 1);
			if (subProof != noProof()) {
				seq[termIdx].active = true;
				return proof(CloGUnaryInf(seq, clo(newName), subProof.p));
			}
		}				
	}	
	return noProof();	
}