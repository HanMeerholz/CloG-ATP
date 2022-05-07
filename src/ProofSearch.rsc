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
	return proofSearch(seq, (), -1);
}

/*
 * Initially, the map keeping track of names and fixpoint formulae is empty.
 */
MaybeProof proofSearch(CloGSequent seq, CloSeqs cloSeqs) {
	return proofSearch(seq, cloSeqs, -1);
}

/*
 * Initially, the map keeping track of names and fixpoint formulae is empty.
 */
MaybeProof proofSearch(CloGSequent seq, int maxRecursionDepth) {
	return proofSearch(seq, (), maxRecursionDepth);
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
 * Otherwise, we try applying one of the rules. Each successful rule application recursively calls
 * again for the sequent resulting from the rule application. Thus, the rule application formulae
 * return a MaybeProof themselves. If all the rule applications return noProof(), no proof could
 * be found and a noProof() is returned.
 */
MaybeProof proofSearch(CloGSequent seq, CloSeqs cloSeqs, int depth) {
	//println("seq=<seq>");
	//println("cloSeqs=<cloSeqs>");
	
	if (depth == 0) return noProof();

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
		
	resProof = tryApplyAx1(seq, cloSeqs, depth);
	if (resProof != noProof()) return resProof;
	
	resProof = tryApplyModm(seq, cloSeqs, depth);
	if (resProof != noProof()) return resProof;
	
	resProof = tryApplyWeak(seq, cloSeqs, depth);
	if (resProof != noProof()) return resProof;
	
	resProof = tryApplyExp(seq, cloSeqs, depth);
	if (resProof != noProof()) return resProof;
	
	resProof = tryApplyOrR(seq, cloSeqs, depth);
	if (resProof != noProof()) return resProof;
	
	resProof = tryApplyChoiceR(seq, cloSeqs, depth);
	if (resProof != noProof()) return resProof;
	
	resProof = tryApplyDChoiceR(seq, cloSeqs, depth);
	if (resProof != noProof()) return resProof;
	
	resProof = tryApplyConcatR(seq, cloSeqs, depth);
	if (resProof != noProof()) return resProof;
	
	resProof = tryApplyTestR(seq, cloSeqs, depth);
	if (resProof != noProof()) return resProof;
	
	resProof = tryApplyDTestR(seq, cloSeqs, depth);
	if (resProof != noProof()) return resProof;
	
	resProof = tryApplyIterR(seq, cloSeqs, depth);
	if (resProof != noProof()) return resProof;
	
	resProof = tryApplyClo(seq, cloSeqs, depth);
	if (resProof != noProof()) return resProof;
	
	resProof = tryApplyDIterR(seq, cloSeqs, depth);
	if (resProof != noProof()) return resProof;
	
	resProof = tryApplyAndR(seq, cloSeqs, depth);
	if (resProof != noProof()) return resProof;
	
	return noProof();
}