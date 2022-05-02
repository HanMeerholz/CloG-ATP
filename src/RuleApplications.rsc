module RuleApplications

import ATP_Data;
import GLASTs;
import List;

MaybeSequent applyAx1(CloGSequent seq) {
	if (size(seq) != 2) return noSeq();
	
	if (term(atomP(Prop p), []) := seq[0]) {
		if (term(neg(atomP(p)), []) := seq[1]) {
			return sequent([]);
		}
	}
	
	if (term(atomP(Prop p), []) := seq[1]) {
		if (term(neg(atomP(p)), []) := seq[0]) {
			return sequent([]);
		}
	}
	
	return noSeq();
}

MaybeSequent applyModm(CloGSequent seq) {
	if (size(seq) != 2) return noSeq();
	
	if (term(\mod(Game g, GameLog phi), list[CloGName] a) := seq[0]) {
		if (term(\mod(dual(g), GameLog psi), list[CloGName] b) := seq[1]) {
			return sequent([term(phi, a), term(psi, b)]);
		}
	}
	
	if (term(\mod(Game g, GameLog phi), list[CloGName] a) := seq[1]) {
		if (term(\mod(dual(g), GameLog psi), list[CloGName] b) := seq[0]) {
			return sequent([term(phi, a), term(psi, b)]);
		}
	}

	return noSeq();
}

MaybeSequents applyAndR(CloGSequent seq, int formIdx) {
	if (term(and(GameLog phi, GameLog psi), list[CloGName] a) := seq[formIdx]) {
		return sequents(
			seq - seq[formIdx] + sequent([term(phi, a)]),
			seq - seq[formIdx] + sequent([term(psi, a)])
		);
	}

	return noSeqs();
}

MaybeSequent applyOrR(CloGSequent seq, int formIdx) {
	return noSeq();
}

MaybeSequent applyChoiceR(CloGSequent seq, int formIdx) {
	return noSeq();
}

MaybeSequent applyDChoiceR(CloGSequent seq, int formIdx) {
	return noSeq();
}

MaybeSequent applyWeak(CloGSequent seq, int formIdx) {
	return noSeq();
}

MaybeSequent applyExp(CloGSequent seq, int formIdx) {
	return noSeq();
}

MaybeSequent applyConcatR(CloGSequent seq, int formIdx) {
	return noSeq();
}

MaybeSequent applyConcatR(CloGSequent seq, int formIdx) {
	return noSeq();
}

MaybeSequent applyIterR(CloGSequent seq, int formIdx, list[CloSeq] cloSeqs) {
	return noSeq();
}

MaybeSequent applyTestR(CloGSequent seq, int formIdx) {
	return noSeq();
}

MaybeSequent applyDIterR(CloGSequent seq, int formIdx, list[CloSeq] cloSeqs) {
	return noSeq();
}

MaybeSequent applyDTestR(CloGSequent seq, int formIdx) {
	return noSeq();
}

MaybeSequent applyClo(CloGSequent seq, int formIdx, list[CloSeq] cloSeqs) {
	return noSeq();
}