module ProofSearch

import List;
import ATP_Base;
import GLASTs;
import RuleApplications;
import IO;

MaybeProof proofSearch(CloGSequent seq) {
	return proofSearch(seq, []);
}

MaybeProof proofSearch(CloGSequent seq, list[CloSeq] cloSeqs) {
	//println(seq);

	if (size(seq) == 0) return proof(CloGLeaf());
	
	for (CloSeq cs <- cloSeqs) {
		FpSeq fs = cs.fpSeq;
		
		if (size(seq) == size(fs.contextSeq)) {
			CloGTerm toFind = term(fs.contextSeq[fs.fpFormulaIdx].s,
			                       fs.contextSeq[fs.fpFormulaIdx].label + cs.name);
			                       
			//println("To find = <toFind>");
			
			int curIdx = indexOf(seq, toFind);
			
			//println("Form<curIdx == -1 ? "not" : ""> found");
			
			if (curIdx != -1) {
				//println(delete(seq, curIdx));
				//println(delete(fs.contextSeq, fs.fpFormulaIdx));
				if (delete(seq, curIdx) == delete(fs.contextSeq, fs.fpFormulaIdx))
					return proof(disClo(seq, cs.name));
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
	
	//// clo
	//for (int i <- [0 .. size(seq)]) {
	//    resSeq = applyClo(seq, i, cloSeqs);
	//	if (resSeq != noSeq()) {
	//		MaybeProof subProof = proofSearch(resSeq.seq, cloSeqs);
	//		if (subProof != noProof())
	//			return proof(CloGUnaryInf(seq, clo(nameS("x", size(cloSeqs))), subProof.p));
	//	}
	//}
	
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
	for (int i <- [0 .. size(seq)]) {
		for (int j <- [0 .. size(seq[i].label)]) {
		    resSeq = applyExp(seq, i, j);
			if (resSeq != noSeq()) {
				MaybeProof subProof = proofSearch(resSeq.seq, cloSeqs);
				if (subProof != noProof())
					return proof(CloGUnaryInf(seq, exp(), subProof.p));
			}
		}
	}
	
	// weak
	if (size(seq) > 1)
		for (int i <- [0 .. size(seq)]) {
		    resSeq = applyWeak(seq, i);
			if (resSeq != noSeq()) {
				MaybeProof subProof = proofSearch(resSeq.seq, cloSeqs);
				if (subProof != noProof())
					return proof(CloGUnaryInf(seq, weak(), subProof.p));
			}
		}
	
	return noProof();
}