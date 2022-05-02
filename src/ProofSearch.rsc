module ProofSearch

import List;
import ATP_Data;
import GLASTs;
import RuleApplications;

MaybeProof proofSearch(CloGSequent seq) {
	return proofSearch(seq, []);
}

MaybeProof proofSearch(CloGSequent seq, list[CloSeq] cloSeqs) {
	if (size(seq) == 0) return proof(CloGLeaf());
	
	for (CloSeq cs <- cloSeqs) {
		FpSeq fs = cs.fpSeq;
	
		CloGTerm ogFpFormula = seq[fs.fpFormulaIdx];
		CloGTerm newFpFormula = fs.contextSeq[fs.fpFormulaIdx];
		
		if (
		    ogFpFormula.s == newFpFormula.s
		 && ogFpFormula.label + cs.name == newFpFormula.label
		 && delete(seq, fs.fpFormulaIdx) == delete(fs.contextSeq, fs.fpFormulaIdx) 
		)
		    return proof(disClo(seq, cs.name));
	}
	
	// ax1	
	resSeq = applyAx1(seq);
	if (resSeq != noSeq()) {
		MaybeProof subProof = proofSearch(resSeq.seq, cloSeqs);
		if (subProof != noProof()) {
			return proof(CloGUnaryInf(seq, ax1(), subProof.p));
		}
	}
	
	// modm	
	resSeq = applyModm(seq);
	if (resSeq != noSeq()) {
		MaybeProof subProof = proofSearch(resSeq.seq, cloSeqs);
		if (subProof != noProof()) {
			return proof(CloGUnaryInf(seq, modm(), subProof.p));
		}
	}
	
	// andR
	for (int i <- [1 .. size(seq)]) {
	    resSeqs = applyAndR(seq, i);
		if (resSeqs != noSeqs()) {
			MaybeProof subProofL = proofSearch(resSeqs.left, cloSeqs);
			MaybeProof subProofR = proofSearch(resSeqs.right, cloSeqs);
			if (subProofL != noProof() && subProofR != noProof()) {
				return proof(CloGBinaryInf(seq, subProofL.p, subProofR.p));
			}
		}
	}
	
	// orR
	for (int i <- [1 .. size(seq)]) {
	    resSeq = applyOrR(seq, i);
		if (resSeq != noSeq()) {
			MaybeProof subProof = proofSearch(resSeq.seq, cloSeqs);
			if (subProof != noProof()) {
				return proof(CloGUnaryInf(seq, orR(), subProof.p));
			}
		}
	}
	
	// choiceR
	for (int i <- [1 .. size(seq)]) {
	    resSeq = applyChoiceR(seq, i);
		if (resSeq != noSeq()) {
			MaybeProof subProof = proofSearch(resSeq.seq, cloSeqs);
			if (subProof != noProof()) {
				return proof(CloGUnaryInf(seq, choiceR(), subProof.p));
			}
		}
	}
	
	// dChoiceR
	for (int i <- [1 .. size(seq)]) {
	    resSeq = applyDChoiceR(seq, i);
		if (resSeq != noSeq()) {
			MaybeProof subProof = proofSearch(resSeq.seq, cloSeqs);
			if (subProof != noProof()) {
				return proof(CloGUnaryInf(seq, dChoiceR(), subProof.p));
			}
		}
	}
	
	// concatR
	for (int i <- [1 .. size(seq)]) {
	    resSeq = applyConcatR(seq, i);
		if (resSeq != noSeq()) {
			MaybeProof subProof = proofSearch(resSeq.seq, cloSeqs);
			if (subProof != noProof()) {
				return proof(CloGUnaryInf(seq, concatR(), subProof.p));
			}
		}
	}
	
	// testR
	for (int i <- [1 .. size(seq)]) {
	    resSeq = applyTestR(seq, i);
		if (resSeq != noSeq()) {
			MaybeProof subProof = proofSearch(resSeq.seq, cloSeqs);
			if (subProof != noProof()) {
				return proof(CloGUnaryInf(seq, testR(), subProof.p));
			}
		}
	}
	
	// dTestR
	for (int i <- [1 .. size(seq)]) {
	    resSeq = applyDTestR(seq, i);
		if (resSeq != noSeq()) {
			MaybeProof subProof = proofSearch(resSeq.seq, cloSeqs);
			if (subProof != noProof()) {
				return proof(CloGUnaryInf(seq, dTestR(), subProof.p));
			}
		}
	}
	
	// iterR
	for (int i <- [1 .. size(seq)]) {
	    resSeq = applyIterR(seq, i, cloSeqs);
		if (resSeq != noSeq()) {
			MaybeProof subProof = proofSearch(resSeq.seq, cloSeqs);
			if (subProof != noProof()) {
				return proof(CloGUnaryInf(seq, iterR(), subProof.p));
			}
		}
	}
	
	// clo
	for (int i <- [1 .. size(seq)]) {
	    resSeq = applyClo(seq, i, cloSeqs);
		if (resSeq != noSeq()) {
			MaybeProof subProof = proofSearch(resSeq.seq, cloSeqs);
			if (subProof != noProof()) {
				return proof(CloGUnaryInf(seq, clo(nameS(x, size(cloSeqs)-1)), subProof.p));
			}
		}
	}
	
	// dIterR
	for (int i <- [1 .. size(seq)]) {
	    resSeq = applyClo(seq, i, cloSeqs);
		if (resSeq != noSeq()) {
			MaybeProof subProof = proofSearch(resSeq.seq, cloSeqs);
			if (subProof != noProof()) {
				return proof(CloGUnaryInf(seq, dIterR(), subProof.p));
			}
		}
	}
	
	// exp
	for (int i <- [1 .. size(seq)]) {
	    resSeq = applyExp(seq, i);
		if (resSeq != noSeq()) {
			MaybeProof subProof = proofSearch(resSeq.seq, cloSeqs);
			if (subProof != noProof()) {
				return proof(CloGUnaryInf(seq, exp(), subProof.p));
			}
		}
	}
	
	// weak
	for (int i <- [1 .. size(seq)]) {
	    resSeq = applyWeak(seq, i);
		if (resSeq != noSeq()) {
			MaybeProof subProof = proofSearch(resSeq.seq, cloSeqs);
			if (subProof != noProof()) {
				return proof(CloGUnaryInf(seq, weak(), subProof.p));
			}
		}
	}
	
	return noProof();
}