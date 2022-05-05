module ProofSearch

import List;
import Map;
import ATP_Base;
import GLASTs;
import RuleApplications;
import IO;

MaybeProof proofSearch(CloGSequent seq) {
	return proofSearch(seq, ());
}

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