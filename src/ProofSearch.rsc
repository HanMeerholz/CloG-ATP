module ProofSearch
/*
 * Module defining the basic proof search algorithm:
 * A basic depth-first search, applying a rule (possibly on a specific formula)
 * at every step.
 */

import List;
import Map;
import ATP_Base;
import GLASTs;
import RuleApplications;
import IO;

/*
 * Initially, the map keeping track of names and fixpoint formulae is empty.
 */
MaybeProof proofSearch(CloGSequent seq) {
	return proofSearch(seq, ());
}

/*
 * A depth-first proof search algorithm.
 * 
 * Input:  a sequent to be proven, and a map which maps the names present in the sequent to the
 *         associated fixpoint formulae.
 * Output: a MaybeProof, which is either a CloGProof, or a noProof(), which essentially acts as
 *         a null value, indicating no proof could be found.
 *
 * When there are no sequents, a leaf is returned.
 * 
 * If the current sequent to be proven already appears as the context for a fixpoint formula
 * associated with one of the names in the cloSeqs map, a closure discharge is returned, which
 * also closes the branch.
 *
 * Otherwise, we try applying one of the rules. If a rule can be applied, a sequent is returned, 
 * for which we again call the proofSearch algorithm. If this results in a proof, we return the
 * CloGUnaryInf with the sequent, rule applied, and the subproof.
 *
 * For the ax1 and modm rule application, we merely pass along the sequent itself, for the
 * remaining rules, we loop through all the formulae in the sequent and pass them along as
 * indices, such that the rule can be tried for each of the formulae in the sequent.
 *
 * For the exp rule, we not only need to specify the formula to apply it to, but also which name
 * in the formula to apply it too, thus we have a double loop.
 *
 * The and rule can return a pair of sequents, and upon finding subproofs for both of them, a
 * CloGBinaryInf is returned with the current sequent and these two subproofs associated.
 *
 * For the iter and dIter, and clo rules, we need to check a soundness condition related to the
 * closure sequents map, thus we pass that map along.
 *
 * The clo rule can also add a closure sequent to the map, thus it returns a pair containing the
 * resulting sequent, and the updated map of closure sequents. The weak and exp rules work
 * similarly, since they can remove a name from a sequent, which means the associated entry in
 * the closure sequents map can be removed.
 */
MaybeProof proofSearch(CloGSequent seq, CloSeqs cloSeqs) {
	//println("seq=<seq>");
	//println("cloSeqs=<cloSeqs>");

	if (size(seq) == 0) return proof(CloGLeaf());
	
	for (CloGName cn <- cloSeqs) {
		FpSeq fs = cloSeqs[cn];
		
		if (size(seq) == size(fs.contextSeq)) {
			CloGTerm fpForm = term(fs.contextSeq[fs.fpFormulaIdx].s,
			                       fs.contextSeq[fs.fpFormulaIdx].label + cn);
			                   
			    
			if (fpForm in seq) {
				if (toSet(seq) - fpForm == toSet(fs.contextSeq) - fs.contextSeq[fs.fpFormulaIdx])
					return proof(disClo(seq, cn));
			}
			
	    }
	}
	
	// ax1	
	resSeq = applyAx1(seq);
	if (resSeq != noSeq()) {
		MaybeProof subProof = proofSearch(resSeq.seq, cloSeqs);
		if (subProof != noProof())
			return proof(CloGUnaryInf(seq, ax1(), subProof.p));
	}
	
	// modm	
	resSeq = applyModm(seq);
	if (resSeq != noSeq()) {
		MaybeProof subProof = proofSearch(resSeq.seq, cloSeqs);
		if (subProof != noProof())
			return proof(CloGUnaryInf(seq, modm(), subProof.p));
	}
	
	// andR
	for (int i <- [0 .. size(seq)]) {
	    resSeqs = applyAndR(seq, i);
		if (resSeqs != noSeqs()) {
			MaybeProof subProofL = proofSearch(resSeqs.left, cloSeqs);
			MaybeProof subProofR = proofSearch(resSeqs.right, cloSeqs);
			if (subProofL != noProof() && subProofR != noProof())
				return proof(CloGBinaryInf(seq, subProofL.p, subProofR.p));
		}
	}
	
	// orR
	for (int i <- [0 .. size(seq)]) {
	    resSeq = applyOrR(seq, i);
		if (resSeq != noSeq()) {
			MaybeProof subProof = proofSearch(resSeq.seq, cloSeqs);
			if (subProof != noProof())
				return proof(CloGUnaryInf(seq, orR(), subProof.p));
		}
	}
	
	// choiceR
	for (int i <- [0 .. size(seq)]) {
	    resSeq = applyChoiceR(seq, i);
		if (resSeq != noSeq()) {
			MaybeProof subProof = proofSearch(resSeq.seq, cloSeqs);
			if (subProof != noProof())
				return proof(CloGUnaryInf(seq, choiceR(), subProof.p));
		}
	}
	
	// dChoiceR
	for (int i <- [0 .. size(seq)]) {
	    resSeq = applyDChoiceR(seq, i);
		if (resSeq != noSeq()) {
			MaybeProof subProof = proofSearch(resSeq.seq, cloSeqs);
			if (subProof != noProof())
				return proof(CloGUnaryInf(seq, dChoiceR(), subProof.p));
		}
	}
	
	// concatR
	for (int i <- [0 .. size(seq)]) {
	    resSeq = applyConcatR(seq, i);
		if (resSeq != noSeq()) {
			MaybeProof subProof = proofSearch(resSeq.seq, cloSeqs);
			if (subProof != noProof())
				return proof(CloGUnaryInf(seq, concatR(), subProof.p));
		}
	}
	
	// testR
	for (int i <- [0 .. size(seq)]) {
	    resSeq = applyTestR(seq, i);
		if (resSeq != noSeq()) {
			MaybeProof subProof = proofSearch(resSeq.seq, cloSeqs);
			if (subProof != noProof())
				return proof(CloGUnaryInf(seq, testR(), subProof.p));
		}
	}
	
	// dTestR
	for (int i <- [0 .. size(seq)]) {
	    resSeq = applyDTestR(seq, i);
		if (resSeq != noSeq()) {
			MaybeProof subProof = proofSearch(resSeq.seq, cloSeqs);
			if (subProof != noProof())
				return proof(CloGUnaryInf(seq, dTestR(), subProof.p));
		}
	}
	
	// iterR
	for (int i <- [0 .. size(seq)]) {
	    resSeq = applyIterR(seq, i, cloSeqs);
		if (resSeq != noSeq()) {
			MaybeProof subProof = proofSearch(resSeq.seq, cloSeqs);
			if (subProof != noProof())
				return proof(CloGUnaryInf(seq, iterR(), subProof.p));
		}
	}
	
	// clo
	for (int i <- [0 .. size(seq)]) {
	    <resSeq, cloSeqs> = applyClo(seq, i, cloSeqs);
		if (resSeq != noSeq()) {
			MaybeProof subProof = proofSearch(resSeq.seq, cloSeqs);
			if (subProof != noProof())
				return proof(CloGUnaryInf(seq, clo(nameS("x", size(cloSeqs))), subProof.p));
		}
	}
	
	// dIterR
	for (int i <- [0 .. size(seq)]) {
	    resSeq = applyDIterR(seq, i, cloSeqs);
		if (resSeq != noSeq()) {
			MaybeProof subProof = proofSearch(resSeq.seq, cloSeqs);
			if (subProof != noProof())
				return proof(CloGUnaryInf(seq, dIterR(), subProof.p));
		}
	}
	
	// exp
	for (int i <- [0 .. size(seq)])
		for (int j <- [0 .. size(seq[i].label)])
		    <resSeq, cloSeqs> = applyExp(seq, i, j, cloSeqs);
			if (resSeq != noSeq()) {
				MaybeProof subProof = proofSearch(resSeq.seq, cloSeqs);
				if (subProof != noProof())
					return proof(CloGUnaryInf(seq, exp(), subProof.p));
			}
	
	// weak
	for (int i <- [0 .. size(seq)]) {
	    <resSeq, cloSeqs> = applyWeak(seq, i, cloSeqs);
		if (resSeq != noSeq()) {
			MaybeProof subProof = proofSearch(resSeq.seq, cloSeqs);
			if (subProof != noProof())
				return proof(CloGUnaryInf(seq, weak(), subProof.p));
		}
	}
	
	return noProof();
}