module ProofSearch
/*
 * Module defining the basic proof search algorithm, and some helper functions:
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
 * Calls the main proof search algorithm without a maximum recursion depth, and with an
 * initially empty map of closure sequents and list of fixpoint sequents. 
 */
MaybeProof proofSearch(CloGSequent seq) {
	return proofSearch(seq, (), [], -1);
}

/*
 * Calls the main proof search algorithm without a maximum recursion depth.
 */
MaybeProof proofSearch(CloGSequent seq, CloSeqs cloSeqs, list[CloGSequent] fpSeqs) {
	return proofSearch(seq, cloSeqs, fpSeqs, -1);
}

/*
 * Calls the main proof search algorithm with an initially empty map of closure sequents and
 * list of fixpoint sequents. 
 */
MaybeProof proofSearch(CloGSequent seq, int maxRecursionDepth) {
	return proofSearch(seq, (), [], maxRecursionDepth);
}

/*
 * A depth-first proof search algorithm.
 * 
 * Input:  a sequent to be proven, a map which maps the names present in the sequent to the
 *         associated fixpoint formulae, a list of sequents associated with earlier applications
 *         of iter, dIter, and clo rules, and an integer representing how deep in the proof tree
 *         we are.
 * Output: a MaybeProof, which is either a CloGProof, or a noProof(), which essentially acts as
 *         a null value, indicating no proof could be found.
 *
 * When the depth reaches 0, we do not recurse any further, and noProof() is returned.
 *
 * First, we try discharging a closure sequent if possible.
 *
 * If this is not possible, we try to detect cycles. If we find that by applying weakening
 * and expanding rules, we can reach one of the earlier fpSeqs, that means there is a cycle, and
 * we return noProof().
 * We do this after trying to discharge closure sequents, because if we can discharge a closure
 * sequent, that also means that there is a cycle, only this cycle is desired.
 *
 * After this, we try applying the ax1 and modm rules, which implicitly also try to apply
 * weakening and expanding rules to reach just 2 terms upon which the rule can be applied.
 *
 * If no proof can be found by applying those rules, we try applying the remaining rules, in the
 * order and, or, choice, dChoice, concat, test, dTest, clo, iter, dIter.
 *
 * Each rule application returns a MaybePoof, since they recursively call the proofSearch()
 * algorithm again (except for the tryDisClo() and tryApplyAx1() rules, which call the
 * proofSearchWeakExp() algorithm instead) on the resulting sequent of the application of the
 * corresponding rule.
 *
 * If all the rule applications return noProof(), no proof could be found and a noProof() is
 * returned.
 */
MaybeProof proofSearch(CloGSequent seq, CloSeqs cloSeqs, list[CloGSequent] fpSeqs, int depth) {	
	
	//println("seq    = <seq>");
	//println("fpSeqs = <fpSeqs>");
	
	if (depth == 0) return proof(CloGLeaf());
	
	//if (isEmpty(seq)) return proof(CloGLeaf());
	
	resProof = tryDisClo(seq, cloSeqs);
	if (resProof != noProof()) return resProof;
	
	if (detectCycles(seq, fpSeqs)) return noProof();	
	
	resProof = tryApplyAx1(seq);
	if (resProof != noProof()) return resProof;
	
	resProof = tryApplyModm(seq, cloSeqs, fpSeqs, depth);
	if (resProof != noProof()) return resProof;
	
	resProof = tryApplyChoice(seq, cloSeqs, fpSeqs, depth);
	if (resProof != noProof()) return resProof;
	
	resProof = tryApplyDChoice(seq, cloSeqs, fpSeqs, depth);
	if (resProof != noProof()) return resProof;
	
	resProof = tryApplyTest(seq, cloSeqs, fpSeqs, depth);
	if (resProof != noProof()) return resProof;
	
	resProof = tryApplyDTest(seq, cloSeqs, fpSeqs, depth);
	if (resProof != noProof()) return resProof;
	
	resProof = tryApplyClo(seq, cloSeqs, fpSeqs, depth);
	if (resProof != noProof()) return resProof;
	
	resProof = tryApplyOr(seq, cloSeqs, fpSeqs, depth);
	if (resProof != noProof()) return resProof;
	
	resProof = tryApplyAnd(seq, cloSeqs, fpSeqs, depth);
	if (resProof != noProof()) return resProof;
	
	resProof = tryApplyIter(seq, cloSeqs, fpSeqs, depth);
	if (resProof != noProof()) return resProof;
		
	resProof = tryApplyDIter(seq, cloSeqs, fpSeqs, depth);
	if (resProof != noProof()) return resProof;
	
	resProof = tryApplyConcat(seq, cloSeqs, fpSeqs, depth);
	if (resProof != noProof()) return resProof;
		
	return noProof();
}

/* 
 * A function that tries discharging a closure sequent on the current sequent.
 *
 * Input:  a sequent for which to try to discharge a closure sequent, and the list of currently
 *         active closure sequents
 * Output: the proof consisting of possible applications of the weak and exp rules, and the
 *         eventual closure sequent discharge, or noProof() if no such proof could be found
 *
 * The algorithm iterates over all the active closure sequents, and for each of them, it checks
 * whether the current sequent has a fixpoint formula corresponding to the closure sequent's
 * fixpoint formula. If so, and the closure sequent can be reached from the current sequent by
 * applying exp and weak rules, a proof is returned, consisting of these weak and exp
 * applications, and a closure sequent discharge.
 *
 * If for none of the closure sequents, such a fixpoint formula exists, or it can be reached by
 * weak and exp rules applications, noProof() is returned.
 */
MaybeProof tryDisClo(CloGSequent seq, CloSeqs cloSeqs) {
	for (CloGName cn <- cloSeqs) {
		fpTerm = cloSeqs[cn].contextSeq[cloSeqs[cn].fpFormulaIdx];
		for (int termIdx <- [0 .. size(seq)]) {
			if (
				term(\mod(dIter(Game gamma), GameLog phi), list[CloGName] a, _) := seq[termIdx]
			 && term(\mod(dIter(gamma), phi), list[CloGName] b, _) := fpTerm
			 && b + cn <= a) {
			    resSeq = cloSeqs[cn].contextSeq - fpTerm + term(\mod(dIter(gamma), phi), b + cn, false);
			    return proofSearchWeakExp(seq, resSeq, disClo(resSeq, cn));
			}
		}
	}
	return noProof();
}

/*
 * A function that returns whether cycles are detected between the current sequent and the list
 * of saved fixpoint sequents.
 *
 * Input:  a current sequent, and a list of fixpoint sequents
 * Output: true, if a cycle is detected, false, otherwise
 *
 * The algorithm loops through all the fixpoint sequents, and if for any of them, a cycle is
 * detected, true is returned. Otherwise, false is returned.
 * A cycle is detected for a fixpoint sequent, if this sequent can be reached from the current
 * sequent merely by applying weak and exp rules. This is the case, if each term in the fixpoint
 * sequent can be reduced from a term of the current sequent.
 */
bool detectCycles(CloGSequent seq, list[CloGSequent] fpSeqs) {
	for (CloGSequent fpSeq <- fpSeqs) {	
	 	// seq is found if all its terms are found
		bool foundSeq = true;
		
		for (int i <- [0 .. size(fpSeq)]) {
			// term is found if any of the terms in seq correspond to the current term in fpSeq
		    bool foundTerm = false;
		    
		    for (int j <- [0 .. size(seq)]) {		    
		    	if (term(GameLog phi, list[CloGName] a, _) := fpSeq[i] && term(phi, list[CloGName] b, _) := seq[j] && a <= b) {
		    		foundTerm = true;
		    		break;
		    	}
		    }
		    // if one of the terms isn't found, the whole sequent is not found
		    if (!foundTerm) foundSeq = false;
		}
		if (foundSeq) return true;
	}
	return false;
}

/*
 * A function that searches for a proof from one sequent to another, using only the exp and weak
 * rules of CloG. The proof ends in the provided tail of the proof.
 *
 * Input:  the sequent to start from, the sequent to end up on, and the proof for the sequent to
 *         end up on
 * Output: the proof of the first sequent, which applies exp and weak rules to reach the second
 *         sequent, and uses the provided proof of the second sequent for the rest
 *
 * For each of terms in the first sequent, if it corresponds to a term in the second term,
 * we apply the exp rule until it has the same label. If this term does not correspond to a
 * term in the second sequent, we apply weakening to the starting term, and move to the next
 * term. We either end up with the second sequent, in which case a proof is found, or we end up
 * with an empty sequent, when all terms have been removed by weakening, in which case noProof()
 * is returned.
 */
MaybeProof proofSearchWeakExp(CloGSequent seqFrom, CloGSequent seqTo, CloGProof tail) {
	if (isEmpty(seqFrom))
		return noProof();
		
	
	if (toSet([<termFrom.s, termFrom.label> | termFrom <- seqFrom]) == toSet([<termTo.s, termTo.label> | termTo <- seqTo])) {
		return proof(tail);
	}
	
	for (int i <- [0 .. size(seqFrom)]) {
		termFrom = seqFrom[i];
		for (int j <- [0 .. size(seqTo)]) {
			termTo = seqTo[j];
			if (termFrom.s == termTo.s) {
				for (CloGName n <- termFrom.label - termTo.label) {
					println("applied exp");
				
					newSeq = delete(seqFrom, i) + term(termFrom.s, termFrom.label - n, false);
					subProof = proofSearchWeakExp(newSeq, seqTo, tail);
					if (subProof != noProof()) {
						seqFrom[i].active = true;
						return proof(CloGUnaryInf(seqFrom, exp(), subProof.p));
					}
				}
			}
		}
		println("applied weak");
		
		newSeq = delete(seqFrom, i);
		subProof = proofSearchWeakExp(newSeq, seqTo, tail);
		if (subProof != noProof()) {
			seqFrom[i].active = true;
			return proof(CloGUnaryInf(seqFrom, weak(), subProof.p));
		}
	}
	
	return noProof();
}