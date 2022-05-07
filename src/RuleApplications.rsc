module RuleApplications
/*
 * Module providing the functions for each of the rule applications.
 */

import ATP_Base;
import GLASTs;
import Map;
import List;
import ProofSearch;

import IO;

/*
 * All of the functions defined in here have the following inputs and
 * outputs: 
 *
 * Input:  the sequent to which the rule is applied, the map of closure
 *         sequents, and the current depth
 * Output: either the CloGProof found after applying weakening to one of
 *         the terms in the sequent, or noProof() if no such proof could
 *         be found
 */

/*
 * A function applying the ax1 axiom to a sequent, and calling the main
 * proof search algorithm on the resulting (empty) sequent.
 *
 * For the rule to be applied, there must be exactly 2 terms in the sequent.
 * These terms must be of the form "p^[]", and "~p^[]".
 * 
 * If these conditions are met, a proof search is done on an empty sequent
 * (resulting in a leaf), and a CloGUnaryInf with the resulting leaf, and
 * the applied ax1() rule is returned. Otherwise, noProof() is returned.
 */
MaybeProof tryApplyAx1(CloGSequent seq, CloSeqs cloSeqs, int depth) {
	if (size(seq) != 2) return noProof();
	
	if (
		   (term(atomP(Prop p), []) := seq[0] && term(neg(atomP(p)), []) := seq[1])
	    || (term(atomP(Prop q), []) := seq[1] && term(neg(atomP(q)), []) := seq[0])
	) {
		println("applied ax1");
		CloGSequent resSeq = [];
		
		MaybeProof subProof = proofSearch(resSeq, cloSeqs, depth - 1);
		return subProof != noProof()
			? proof(CloGUnaryInf(seq, ax1(), subProof.p))
			: noProof()
			;
	}

	return noProof();	
}

/*
 * A function applying the modm rule to a sequent, and calling the main
 * proof search algorithm on the resulting sequent.
 *
 * For the rule to be applied, there must be exactly 2 terms in the sequent.
 * These terms must be of the form "<g>phi^[a]", and "~<g^d>psi^[b]".
 * 
 * If these conditions are met, a proof search is done on the sequent with
 * the terms "phi^a" and "psi^a". If a subproof is found, a CloGUnaryInf with
 * the resulting subproof, and the applied modm() rule is returned. Otherwise,
 * noSeq() is returned.
 */
MaybeProof tryApplyModm(CloGSequent seq, CloSeqs cloSeqs, int depth) {
	if (size(seq) != 2) return noProof();
	
	if (
	     term(\mod(Game g, GameLog phi), list[CloGName] a) := seq[0]
	  && term(\mod(dual(g), GameLog psi), list[CloGName] b) := seq[1]
	) {
		println("applied modm");
		CloGSequent resSeq = [term(phi, a), term(psi, b)];
		
		MaybeProof subProof = proofSearch(resSeq, cloSeqs, depth - 1);
		if (subProof != noProof())
			return proof(CloGUnaryInf(seq, modm(), subProof.p));
	}
	
	if (
	     term(\mod(Game g, GameLog phi), list[CloGName] a) := seq[1]
	  && term(\mod(dual(g), GameLog psi), list[CloGName] b) := seq[0]
	) {
		println("applied modm");
		CloGSequent resSeq = [term(phi, a), term(psi, b)];
		
		MaybeProof subProof = proofSearch(resSeq, cloSeqs, depth - 1);
		if (subProof != noProof())
			return proof(CloGUnaryInf(seq, modm(), subProof.p));
	}

	return noProof();
}

/*
 * A function applying the and rule to a sequent.
 *
 * Input:  the sequent to which the rule is applied, and an integer indicating
 *         which term in the sequent to apply the rule to
 * Output: if the rule can be applied, the resulting pair of sequents;
 *         otherwise, noSeqs(), indicating the rule application failed
 *
 * For the rule to be applied, the term at the specified index must be of
 * the form "(phi & psi)^a".
 * 
 * If this condition is met, a pair of sequents, such that for one of them, the
 * specified term is replaced by "phi^a", and for the other, it is replaced by
 * "psi^a", is returned. Otherwise, noSeqs() is returned.
 */
MaybeProof tryApplyAnd(CloGSequent seq, CloSeqs cloSeqs, int depth) {	
	for (int termIdx <- [0 .. size(seq)]) {
	    if (term(and(GameLog phi, GameLog psi), list[CloGName] a) := seq[termIdx]) {
			println("applied and");
			CloGSequent resSeqL = seq - seq[termIdx] + term(phi, a); 
			CloGSequent resSeqR = seq - seq[termIdx] + term(psi, a); 
			
			MaybeProof subProofL = proofSearch(resSeqL, cloSeqs, depth - 1);
			MaybeProof subProofR = proofSearch(resSeqR, cloSeqs, depth - 1);
			if (subProofL != noProof() && subProofR != noProof())
				return proof(CloGBinaryInf(seq, subProofL.p, subProofR.p));
		}
	}
	
	return noProof();
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
MaybeProof tryApplyOr(CloGSequent seq, CloSeqs cloSeqs, int depth) {	
	for (int termIdx <- [0 .. size(seq)]) {
	    if (term(or(GameLog phi, GameLog psi), list[CloGName] a) := seq[termIdx]) {
			println("applied or");
			CloGSequent resSeq = seq - seq[termIdx] + term(phi, a) + term(psi, a); 
			MaybeProof subProof = proofSearch(resSeq, cloSeqs, depth - 1);
			if (subProof != noProof())
				return proof(CloGUnaryInf(seq, orR(), subProof.p));
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
MaybeProof tryApplyChoice(CloGSequent seq, CloSeqs cloSeqs, int depth) {
	for (int termIdx <- [0 .. size(seq)]) {
		    if (term(\mod(choice(Game gamma, Game delta), GameLog phi), list[CloGName] a) := seq[termIdx]) {
				println("applied choice");
				CloGSequent resSeq = seq - seq[termIdx] + term(or(\mod(gamma, phi), \mod(delta, phi)), a);
				MaybeProof subProof = proofSearch(resSeq, cloSeqs, depth - 1);
				if (subProof != noProof())
					return proof(CloGUnaryInf(seq, choiceR(), subProof.p));
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
MaybeProof tryApplyDChoice(CloGSequent seq, CloSeqs cloSeqs, int depth) {
	for (int termIdx <- [0 .. size(seq)]) {
		    if (term(\mod(dChoice(Game gamma, Game delta), GameLog phi), list[CloGName] a) := seq[termIdx]) {
				println("applied dChoice");
				CloGSequent resSeq = seq - seq[termIdx] + term(and(\mod(gamma, phi), \mod(delta, phi)), a);
				MaybeProof subProof = proofSearch(resSeq, cloSeqs, depth - 1);
				if (subProof != noProof())
					return proof(CloGUnaryInf(seq, dChoiceR(), subProof.p));
			}
		}
		
	return noProof();
}

/*
 * A function applying the weak rule to a sequent, and calling the main
 * proof search algorithm on the resulting sequent.
 *
 * For the rule to be applied, there must be more than 1 term present in the
 * sequent.
 * 
 * If this condition is met, we loop through all the terms in the sequent,
 * and for each of the terms, we remove it, and try to find a proof with the
 * resulting sequents. Whenever the specified term is removed from the sequent,
 * and this removes the occurrence of certain names from the sequent entirely,
 * their associated entries are removed from the closure sequent map as well,
 * which is passed to the proofSearch() call.
 *
 * If a subproof is found, we return a CloGUnaryInf with the subproof, and the
 * applied weak() rule.
 */
MaybeProof tryApplyWeak(CloGSequent seq, CloSeqs cloSeqs, int depth) {
	if (size(seq) <= 1) return noProof();

	for (int termIdx <- [0 .. size(seq)]) {
	
		CloGSequent resSeq = seq - seq[termIdx];
		
		CloSeqs resCloSeqs = cloSeqs;
		
		for (CloGName csName <- cloSeqs) {
			bool present = false;
			for (term(_, list[CloGName] label) <- resSeq) {
				if (present) break;
				for (CloGName sName <- label)
					if (sName == csName) {
						present = true;
						break;
					}
			}
			if (!present)
				resCloSeqs = delete(resCloSeqs, csName);
		}
		println("applied weak");
	
		MaybeProof subProof = proofSearch(resSeq, resCloSeqs, depth - 1);
		if (subProof != noProof())
			return proof(CloGUnaryInf(seq, weak(), subProof.p));
	}	
	return noProof();	
}

/*
 * A function applying the exp rule to a sequent, and calling the main
 * proof search algorithm on the resulting sequent.
 *
 *
 * We loop through all the terms in the sequent, and if a term is of the form
 * phi^a (which is always the case), we loop through all the names in the term's
 * label, and for each name, we remove it from the term, and try to find a proof
 * with the resulting sequent. Whenever the specified term is removed from the
 * sequent, and this removes the occurrence of certain names from the sequent
 * entirely, their associated entries are removed from the closure sequent map
 * as well, which is passed to the proofSearch() call.
 *
 * If a subproof is found, we return a CloGUnaryInf with the subproof, and the
 * applied exp() rule.
 */
MaybeProof tryApplyExp(CloGSequent seq, CloSeqs cloSeqs, int depth) {
	
	for (int termIdx <- [0 .. size(seq)])
		if (term(GameLog phi, list[CloGName] a) := seq[termIdx])
			for (int nameIdx <- [0 .. size(a)]) {
				CloGSequent resSeq = seq - seq[termIdx] + term(phi, a - a[nameIdx]);
			
				CloSeqs resCloSeqs = cloSeqs;
				
				for (CloGName csName <- cloSeqs) {
					bool present = false;
					for (term(_, list[CloGName] label) <- resSeq) {
						if (present) break;
						for (CloGName sName <- label)
							if (sName == csName) {
								present = true;
								break;
							}
					}
					if (!present)
						resCloSeqs = delete(resCloSeqs, csName);
				}
			
				println("applied exp");
				
				MaybeProof subProof = proofSearch(resSeq, resCloSeqs, depth - 1);
				if (subProof != noProof())
					return proof(CloGUnaryInf(seq, exp(), subProof.p));
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
MaybeProof tryApplyConcat(CloGSequent seq, CloSeqs cloSeqs, int depth) {
	for (int termIdx <- [0 .. size(seq)]) {
		    if (term(\mod(concat(Game gamma, Game delta), GameLog phi), list[CloGName] a) := seq[termIdx]) {
				println("applied concat");
				CloGSequent resSeq = seq - seq[termIdx] + term(\mod(gamma, \mod(delta, phi)), a);
				MaybeProof subProof = proofSearch(resSeq, cloSeqs, depth - 1);
				if (subProof != noProof())
					return proof(CloGUnaryInf(seq, concatR(), subProof.p));
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
MaybeProof tryApplyIter(CloGSequent seq, CloSeqs cloSeqs, int depth) {
	for (int termIdx <- [0 .. size(seq)]) {
		if (term(\mod(iter(Game gamma), GameLog phi), list[CloGName] a) := seq[termIdx]) {	
			
		
			bool nextTerm = false;
				
			for (CloGName x <- a)
				if (!fpLessThanOrEqualTo(cloSeqs[x].contextSeq[cloSeqs[x].fpFormulaIdx].s, \mod(iter(gamma), phi)))
					nextTerm = true;
			
			if (nextTerm) continue;
			
			println("applied iter");
			CloGSequent resSeq =  seq - seq[termIdx] + term(or(phi, \mod(gamma, \mod(iter(gamma), phi))), a);
			
			MaybeProof subProof = proofSearch(resSeq, cloSeqs, depth - 1);
			if (subProof != noProof())
				return proof(CloGUnaryInf(seq, iterR(), subProof.p));
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
MaybeProof tryApplyTest(CloGSequent seq, CloSeqs cloSeqs, int depth) {
	for (int termIdx <- [0 .. size(seq)]) {
		    if (term(\mod(\test(GameLog psi), GameLog phi), list[CloGName] a) := seq[termIdx]) {
				println("applied test");
				CloGSequent resSeq = seq - seq[termIdx] + term(and(psi, phi), a);
				MaybeProof subProof = proofSearch(resSeq, cloSeqs, depth - 1);
				if (subProof != noProof())
					return proof(CloGUnaryInf(seq, testR(), subProof.p));
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
MaybeProof tryApplyDIter(CloGSequent seq, CloSeqs cloSeqs, int depth) {
	for (int termIdx <- [0 .. size(seq)]) {
		if (term(\mod(dIter(Game gamma), GameLog phi), list[CloGName] a) := seq[termIdx]) {	
			bool nextTerm = false;
				
			for (CloGName x <- a)
				if (!fpLessThanOrEqualTo(cloSeqs[x].contextSeq[cloSeqs[x].fpFormulaIdx].s, \mod(dIter(gamma), phi)))
					nextTerm = true;
			
			if (nextTerm) continue;
			
			println("applied dIter");
			CloGSequent resSeq =  seq - seq[termIdx] + term(and(phi, \mod(gamma, \mod(dIter(gamma), phi))), a);
			
			MaybeProof subProof = proofSearch(resSeq, cloSeqs, depth - 1);
			if (subProof != noProof())
				return proof(CloGUnaryInf(seq, dIterR(), subProof.p));
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
MaybeProof tryApplyDTest(CloGSequent seq, CloSeqs cloSeqs, int depth) {
	for (int termIdx <- [0 .. size(seq)]) {
		    if (term(\mod(dTest(GameLog psi), GameLog phi), list[CloGName] a) := seq[termIdx]) {
				println("applied dTest");
				CloGSequent resSeq = seq - seq[termIdx] + term(or(psi, phi), a);
				MaybeProof subProof = proofSearch(resSeq, cloSeqs, depth - 1);
				if (subProof != noProof())
					return proof(CloGUnaryInf(seq, dTestR(), subProof.p));
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
MaybeProof tryApplyClo(CloGSequent seq, CloSeqs cloSeqs, int depth) {
	for (int termIdx <- [0 .. size(seq)]) {
		if (term(\mod(dIter(Game gamma), GameLog phi), list[CloGName] a) := seq[termIdx]) {	
			bool nextTerm = false;
				
			for (CloGName x <- a)
				if (!fpLessThanOrEqualTo(cloSeqs[x].contextSeq[cloSeqs[x].fpFormulaIdx].s, \mod(dIter(gamma), phi)))
					nextTerm = true;
			
			if (nextTerm) continue;
			
			CloGName newName = nameS("x", size(cloSeqs));
			cloSeqs += (newName: <seq, termIdx>);
			
			println("applied clo");
			CloGSequent resSeq =  seq - seq[termIdx] + term(and(phi, \mod(gamma, \mod(dIter(gamma), phi))), a + newName);
			
			MaybeProof subProof = proofSearch(resSeq, cloSeqs, depth - 1);
			if (subProof != noProof())
				return proof(CloGUnaryInf(seq, clo(nameS("x", size(cloSeqs))), subProof.p));
		}				
	}	
	return noProof();	
}