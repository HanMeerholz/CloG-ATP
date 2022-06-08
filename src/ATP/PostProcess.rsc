module ATP::PostProcess
/*
 * A module that deals with the post-processing of proofs
 * obtained from the Automated Theorem Prover
 */

import CloG_Base::GLASTs;
import ATP::ATP_Base;

/*
 * A function that replaces closure rules that no not have
 * a discharged assumption by a dIter rule instead.
 *
 * Input:  A CloGProof that may contain closure rule applications
 *         without a discharged assumption appearing somewhere above
 *         the proof node at which the closure rule was applied
 * Output: A CloGProof with its closure rule applications replaced
 *         by dIter applications
 *
 * For each of the nodes at which a closure rule was applied, and
 * above which no discharged assumption appears, the replaceCloAt()
 * function is called, which handles the actual replacement.
 */
CloGProof replaceUnusedClos(CloGProof proof) {
	return visit(proof) {
		case subProof:CloGUnaryInf(_, clo(CloGName n), CloGProof inf): {
			if (/disClo(_, n) !:= inf) {
				insert replaceCloAt(subProof, n);
			}
		}
	}
}

/*
 * A function that replaces a specific closure rule application
 * in a proof by a dIter rule application, and updates the rest
 * of the proof accordingly
 *
 * Input:  A CloGProof with a closure rule application at the root,
 *         and the name associated with this closure rule application
 * Output: A CloGProof with the closure rule application at the root
 *         replaced by a dIter rule application, and no more closure
 *         rule name appearing in sequents above this proof node
 *
 * Replaces the rule at the root by a dIter rule, then visits the
 * rest of the proof, and for all sequents above the starting node,
 * the name associated with the original closure rule application
 * is removed.
 */ 
CloGProof replaceCloAt(CloGProof proof, CloGName name) {
	proof.rule = dIterR();

	return visit(proof) {
		case subP:CloGUnaryInf(CloGSequent seq, _, _): {
			CloGSequent newSeq = [];
			for (term <- seq) {
				if (t:term(_, list[CloGName] label, _) := term) {
					t.label = label - name;
					newSeq += t;
				}
			}
			subP.seq = newSeq;
			insert subP;
		}
		case subP:CloGBinaryInf(CloGSequent seq, _, _): {
			CloGSequent newSeq = [];
			for (term <- seq) {
				if (t:term(_, list[CloGName] label, _) := term) {
					t.label = label - name;
					newSeq += t;
				}
			}
			subP.seq = newSeq;
			insert subP;
		}
		case subP:disClo(CloGSequent seq, _): {
			CloGSequent newSeq = [];
			for (term <- seq) {
				if (t:term(_, list[CloGName] label, _) := term) {
					t.label = label - name;
					newSeq += t;
				}
			}
			subP.seq = newSeq;
			insert subP;
		}
	}
}