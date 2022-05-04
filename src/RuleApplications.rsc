module RuleApplications

import ATP_Base;
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
	if (term(and(GameLog phi, GameLog psi), list[CloGName] a) := seq[formIdx])
		return sequents(
			seq - seq[formIdx] + term(phi, a),
			seq - seq[formIdx] + term(psi, a)
		);

	return noSeqs();
}

MaybeSequent applyOrR(CloGSequent seq, int formIdx) {
	if (term(or(GameLog phi, GameLog psi), list[CloGName] a) := seq[formIdx])
		return sequent(seq - seq[formIdx] + term(phi, a) + term(psi, a));
	
	return noSeq();
}

MaybeSequent applyChoiceR(CloGSequent seq, int formIdx) {
	if (term(\mod(choice(Game gamma, Game delta), GameLog phi), list[CloGName] a) := seq[formIdx])
		return sequent(seq - seq[formIdx] + term(or(\mod(gamma, phi), \mod(delta, phi)), a));

	return noSeq();
}

MaybeSequent applyDChoiceR(CloGSequent seq, int formIdx) {
	if (term(\mod(dChoice(Game gamma, Game delta), GameLog phi), list[CloGName] a) := seq[formIdx])
		return sequent(seq - seq[formIdx] + term(and(\mod(gamma, phi), \mod(delta, phi)), a));

	return noSeq();
}

MaybeSequent applyWeak(CloGSequent seq, int formIdx) {
	return sequent(seq - seq[formIdx]);
}

MaybeSequent applyExp(CloGSequent seq, int formIdx, int nameIdx) {
	if (term(GameLog phi, list[CloGName] a) := seq[formIdx])
		return sequent(seq - seq[formIdx] + term(phi, a - a[nameIdx]));
		
	return noSeq();
}

MaybeSequent applyConcatR(CloGSequent seq, int formIdx) {
	if (term(\mod(concat(Game gamma, Game delta), GameLog phi), list[CloGName] a) := seq[formIdx])
		return sequent(seq - seq[formIdx] + term(\mod(gamma, \mod(delta, phi)), a));
		
	return noSeq();
}

MaybeSequent applyIterR(CloGSequent seq, int formIdx, list[CloSeq] cloSeqs) {
	if (term(\mod(iter(Game gamma), GameLog phi), list[CloGName] a) := seq[formIdx]) {
		for (CloGName x <- a)
			if (fpGreaterThan(cloSeqs[x][0].contextSeq[cloSeqs[x][0].fpFormulaIdx].s, \mod(iter(gamma), phi)))
				return noSeq();
		return sequent(seq - seq[formIdx] + term(or(phi, \mod(gamma, \mod(iter(gamma), phi))), a));
	}
	
	return noSeq();
}

MaybeSequent applyTestR(CloGSequent seq, int formIdx) {
	if (term(\mod(\test(GameLog psi), GameLog phi), list[CloGName] a) := seq[formIdx])
		return sequent(seq - seq[formIdx] + term(and(psi, phi), a));

	return noSeq();
}

MaybeSequent applyDIterR(CloGSequent seq, int formIdx, list[CloSeq] cloSeqs) {
	if (term(\mod(dIter(Game gamma), GameLog phi), list[CloGName] a) := seq[formIdx]) {
		for (CloGName x <- a)
			if (fpGreaterThan(cloSeqs[x][0].contextSeq[cloSeqs[x][0].fpFormulaIdx].s, \mod(dIter(gamma), phi)))
				return noSeq();
		return sequent(seq - seq[formIdx] + term(and(phi, \mod(gamma, \mod(dIter(gamma), phi))), a));
	}
	
	return noSeq();
}

MaybeSequent applyDTestR(CloGSequent seq, int formIdx) {
	if (term(\mod(dTest(GameLog psi), GameLog phi), list[CloGName] a) := seq[formIdx])
		return sequent(seq - seq[formIdx] + term(or(psi, phi), a));

	return noSeq();
}

MaybeSequent applyClo(CloGSequent seq, int formIdx, list[CloSeq] cloSeqs) {
	if (term(\mod(dIter(Game gamma), GameLog phi), list[CloGName] a) := seq[formIdx]) {
		for (CloGName x <- a)
			if (fpGreaterThan(cloSeqs[x][0].contextSeq[cloSeqs[x][0].fpFormulaIdx].s, \mod(dIter(gamma), phi)))
				return noSeq();
		CloGName newName = nameS("x", size(cloSeqs));
		cloSeqs += <a + newName, <seq, formIdx>>;
		return sequent(seq - seq[formIdx] + term(and(phi, \mod(gamma, \mod(dIter(gamma), phi))), a + newName));
	}
	
	return noSeq();
}

