module RuleApplications
/*
 * Module providing the functions for each of the rule applications.
 */

import ATP_Base;
import GLASTs;
import Map;
import List;

import IO;

/*
 * A function applying the ax1 rule to a sequent.
 *
 * Input:  the sequent to which the rule is applied
 * Output: if the rule can be applied, the resulting (empty) sequent;
 *         otherwise, noSeq(), indicating the rule application failed
 *
 * For the rule to be applied, there must be exactly 2 terms in the sequent.
 * These terms must be of the form "p^[]", and "~p^[]".
 * 
 * If these conditions are met, an empty sequent is returned.
 * Otherwise, noSeq() is returned.
 */
MaybeSequent applyAx1(CloGSequent seq) {
	if (size(seq) != 2) return noSeq();
	
	if (term(atomP(Prop p), []) := seq[0]) {
		if (term(neg(atomP(p)), []) := seq[1]) {
			println("applied ax1");
			return sequent([]);
		}
	}
	
	if (term(atomP(Prop p), []) := seq[1]) {
		if (term(neg(atomP(p)), []) := seq[0]) {
			println("applied ax1");
			return sequent([]);
		}
	}
	
	return noSeq();
}

/*
 * A function applying the modm rule to a sequent.
 *
 * Input:  the sequent to which the rule is applied
 * Output: if the rule can be applied, the resulting sequent;
 * otherwise, noSeq(), indicating the rule application failed
 *
 * For the rule to be applied, there must be exactly 2 terms in the sequent.
 * These terms must be of the form "<g>phi^[a]", and "~<g^d>psi^[b]".
 * 
 * If these conditions are met, a sequent with the terms "phi^a" and "psi^a"
 * is returned. Otherwise, noSeq() is returned.
 */
MaybeSequent applyModm(CloGSequent seq) {
	if (size(seq) != 2) return noSeq();
	
	if (term(\mod(Game g, GameLog phi), list[CloGName] a) := seq[0]) {
		if (term(\mod(dual(g), GameLog psi), list[CloGName] b) := seq[1]) {
			println("applied modm");
			return sequent([term(phi, a), term(psi, b)]);
		}
	}
	
	if (term(\mod(Game g, GameLog phi), list[CloGName] a) := seq[1]) {
		if (term(\mod(dual(g), GameLog psi), list[CloGName] b) := seq[0]) {
			println("applied modm");
			return sequent([term(phi, a), term(psi, b)]);
		}
	}

	return noSeq();
}

/*
 * A function applying the andR rule to a sequent.
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
MaybeSequents applyAndR(CloGSequent seq, int termIdx) {
	if (term(and(GameLog phi, GameLog psi), list[CloGName] a) := seq[termIdx]) {
		println("applied and");
		return sequents(
			seq - seq[termIdx] + term(phi, a),
			seq - seq[termIdx] + term(psi, a)
		);
	}
	
	return noSeqs();
}

/*
 * A function applying the orR rule to a sequent.
 *
 * Input:  the sequent to which the rule is applied, and an integer indicating
 *         which term in the sequent to apply the rule to
 * Output: if the rule can be applied, the resulting sequent;
 *         otherwise, noSeq(), indicating the rule application failed
 *
 * For the rule to be applied, the term at the specified index must be of
 * the form "(phi | psi)^a".
 * 
 * If this condition is met, a sequent, where the specified term is replaced by
 * two terms "phi^a", and "psi^a", is returned. Otherwise, noSeq() is returned.
 */
MaybeSequent applyOrR(CloGSequent seq, int termIdx) {
	if (term(or(GameLog phi, GameLog psi), list[CloGName] a) := seq[termIdx]) {
		println("applied or");
		return sequent(seq - seq[termIdx] + term(phi, a) + term(psi, a)); 
	}
	
	return noSeq();
}

/*
 * A function applying the choiceR rule to a sequent.
 *
 * Input:  the sequent to which the rule is applied, and an integer indicating
 *         which term in the sequent to apply the rule to
 * Output: if the rule can be applied, the resulting sequent;
 *         otherwise, noSeq(), indicating the rule application failed
 *
 * For the rule to be applied, the term at the specified index must be of
 * the form "(<gamma || delta>phi)^a".
 * 
 * If this condition is met, a sequent, where the specified term is replaced by
 * "(<gamma>phi | <delta> phi)^a" is returned. Otherwise, noSeq() is returned.
 */
MaybeSequent applyChoiceR(CloGSequent seq, int termIdx) {
	if (term(\mod(choice(Game gamma, Game delta), GameLog phi), list[CloGName] a) := seq[termIdx]) {
		println("applied choice");
		return sequent(seq - seq[termIdx] + term(or(\mod(gamma, phi), \mod(delta, phi)), a));
	}

	return noSeq();
}

/*
 * A function applying the dChoiceR rule to a sequent.
 *
 * Input:  the sequent to which the rule is applied, and an integer indicating
 *         which term in the sequent to apply the rule to
 * Output: if the rule can be applied, the resulting sequent;
 *         otherwise, noSeq(), indicating the rule application failed
 *
 * For the rule to be applied, the term at the specified index must be of
 * the form "(<gamma && delta>phi)^a".
 * 
 * If this condition is met, a sequent, where the specified term is replaced by
 * "(<gamma>phi & <delta> phi)^a" is returned. Otherwise, noSeq() is returned.
 */
MaybeSequent applyDChoiceR(CloGSequent seq, int termIdx) {
	if (term(\mod(dChoice(Game gamma, Game delta), GameLog phi), list[CloGName] a) := seq[termIdx]) {
		println("applied dChoice");
		return sequent(seq - seq[termIdx] + term(and(\mod(gamma, phi), \mod(delta, phi)), a));
	}
	
	return noSeq();
}

/*
 * A function applying the weak rule to a sequent.
 *
 * Input:  the sequent to which the rule is applied, an integer indicating
 *         which term in the sequent to apply the rule to, and the map of
 *         closure sequents
 * Output: a pair of, if the rule can be applied, the resulting sequent,
 *         otherwise, noSeq(), indicating the rule application failed, and
 *         the potentially updated map of closure sequents
 *
 * For the rule to be applied, there must be more than 1 term present in the
 * sequent.
 * 
 * If this condition is met, the specified term is removed from the sequent,
 * and if this removes the occurrence of certain names from the sequent entirely,
 * their associated entries are removed from the closure sequent map as well. The\
 * sequent with the specified term removed, is returned, along with the potentially
 * updated list of closure sequents.
 *
 * Otherwise, a pair with a noSeq(), and the non-updated list of closure sequents
 * is returned.
 */
tuple[MaybeSequent, CloSeqs] applyWeak(CloGSequent seq, int termIdx, CloSeqs cloSeqs) {
	if (size(seq) <= 1) return <noSeq(), cloSeqs>;
	
	CloGSequent newSeq = seq - seq[termIdx];
	
	for (CloGName csName <- cloSeqs) {
		bool present = false;
		for (term(_, list[CloGName] label) <- newSeq) {
			if (present) break;
			for (CloGName sName <- label)
				if (sName == csName) {
					present = true;
					break;
				}
		}
		if (!present)
			cloSeqs = delete(cloSeqs, csName);
	}
	
	println("applied weak");
	return <sequent(newSeq), cloSeqs>;
}

/*
 * A function applying the exp rule to a sequent.
 *
 * Input:  the sequent to which the rule is applied, an integer indicating
 *         which term in the sequent to apply the rule to, and integer
 *         indicating which name in the term's label to apply the rule to,
 *         and the map of closure sequents
 * Output: a pair of, if the rule can be applied, the resulting sequent,
 *         otherwise, noSeq(), indicating the rule application failed, and
 *         the potentially updated map of closure sequents
 *
 * For the rule to be applied, there must be more than 1 term present in the
 * sequent.
 *
 * For the rule to be applied, the term at the specified index must be of
 * the form "phi^a" (which is always the case). 
 *
 * If this condition is met, the specified term is replaced by the same term,
 * where its label has the specified name removed, and if this removes the
 * occurrence of certain names in the sequent entirely, their associated entries
 * are removed from the closure sequent map as well. The sequent with the
 * specified term replaced, is returned, along with the potentially updated list
 * of closure sequents.
 *
 * Otherwise, a pair with a noSeq(), and the non-updated list of closure sequents
 * is returned (this cannot happen).
 */
tuple[MaybeSequent, CloSeqs] applyExp(CloGSequent seq, int termIdx, int nameIdx, CloSeqs cloSeqs) {
	if (term(GameLog phi, list[CloGName] a) := seq[termIdx]) {
		
		CloGSequent newSeq = seq - seq[termIdx] + term(phi, a - a[nameIdx]);
	
		for (CloGName csName <- cloSeqs) {
			bool present = false;
			for (term(_, list[CloGName] label) <- newSeq) {
				if (present) break;
				for (CloGName sName <- label)
					if (sName == csName) {
						present = true;
						break;
					}
			}
			if (!present)
				cloSeqs = delete(cloSeqs, csName);
		}
	
		println("applied exp");
		return <sequent(newSeq), cloSeqs>;
	}
		
	return <noSeq(), cloSeqs>;
}

/*
 * A function applying the concat rule to a sequent.
 *
 * Input:  the sequent to which the rule is applied, and an integer indicating
 *         which term in the sequent to apply the rule to
 * Output: if the rule can be applied, the resulting sequent;
 *         otherwise, noSeq(), indicating the rule application failed
 *
 * For the rule to be applied, the term at the specified index must be of
 * the form "(<gamma; delta>phi)^a".
 * 
 * If this condition is met, a sequent, where the specified term is replaced by
 * "(<gamma><delta>phi)^a" is returned. Otherwise, noSeq() is returned.
 */
MaybeSequent applyConcatR(CloGSequent seq, int termIdx) {
	if (term(\mod(concat(Game gamma, Game delta), GameLog phi), list[CloGName] a) := seq[termIdx]) {
		println("applied concat");
		return sequent(seq - seq[termIdx] + term(\mod(gamma, \mod(delta, phi)), a));
	}	
	return noSeq();
}

/*
 * A function applying the iterR rule to a sequent.
 *
 * Input:  the sequent to which the rule is applied, an integer indicating
 *         which term in the sequent to apply the rule to, and the map of
 *         closure sequents
 * Output: if the rule can be applied, the resulting sequent;
 *         otherwise, noSeq(), indicating the rule application failed
 *
 * For the rule to be applied, the term at the specified index must be of
 * the form "(<gamma*>phi)^a".
 * Each of the names in the label a must be smaller than this "<gamma*>phi"
 * fixpoint formula, according to the order on fixpoint formulae defined in the
 * literature.
 *
 * If these conditions are met, a sequent, where the specified term is replaced
 * by "(phi | <gamma><gamma*>phi)^a" is returned. Otherwise, noSeq() is returned.
 */
MaybeSequent applyIterR(CloGSequent seq, int termIdx, CloSeqs cloSeqs) {
	if (term(\mod(iter(Game gamma), GameLog phi), list[CloGName] a) := seq[termIdx]) {
		for (CloGName x <- a) {
			if (fpGreaterThan(cloSeqs[x].contextSeq[cloSeqs[x].fpFormulaIdx].s, \mod(iter(gamma), phi)))
				return noSeq();
			}
		println("applied iter");
		return sequent(seq - seq[termIdx] + term(or(phi, \mod(gamma, \mod(iter(gamma), phi))), a));
	}
	
	return noSeq();
}

/*
 * A function applying the testR rule to a sequent.
 *
 * Input:  the sequent to which the rule is applied, and an integer indicating
 *         which term in the sequent to apply the rule to
 * Output: if the rule can be applied, the resulting sequent;
 *         otherwise, noSeq(), indicating the rule application failed
 *
 * For the rule to be applied, the term at the specified index must be of
 * the form "(<psi?>phi)^a".
 * 
 * If this condition is met, a sequent, where the specified term is replaced by
 * "(phi & psi)^a" is returned. Otherwise, noSeq() is returned.
 */
MaybeSequent applyTestR(CloGSequent seq, int termIdx) {
	if (term(\mod(\test(GameLog psi), GameLog phi), list[CloGName] a) := seq[termIdx]) {
		println("applied test");
		return sequent(seq - seq[termIdx] + term(and(psi, phi), a));
	}
	
	return noSeq();
}

/*
 * A function applying the dIterR rule to a sequent.
 *
 * Input:  the sequent to which the rule is applied, an integer indicating
 *         which term in the sequent to apply the rule to, and the map of
 *         closure sequents
 * Output: if the rule can be applied, the resulting sequent;
 *         otherwise, noSeq(), indicating the rule application failed
 *
 * For the rule to be applied, the term at the specified index must be of
 * the form "(<gamma^x>phi)^a".
 * Each of the names in the label a must be smaller than this "<gamma^x>phi"
 * fixpoint formula, according to the order on fixpoint formulae defined in the
 * literature.
 *
 * If these conditions are met, a sequent, where the specified term is replaced
 * by "(phi & <gamma><gamma^x>phi)^a" is returned. Otherwise, noSeq() is returned.
 */
MaybeSequent applyDIterR(CloGSequent seq, int termIdx, CloSeqs cloSeqs) {
	if (term(\mod(dIter(Game gamma), GameLog phi), list[CloGName] a) := seq[termIdx]) {
		for (CloGName x <- a)
			if (fpGreaterThan(cloSeqs[x].contextSeq[cloSeqs[x].fpFormulaIdx].s, \mod(dIter(gamma), phi)))
				return noSeq();
		println("applied dIter");
		return sequent(seq - seq[termIdx] + term(and(phi, \mod(gamma, \mod(dIter(gamma), phi))), a));
	}
	
	return noSeq();
}

/*
 * A function applying the testR rule to a sequent.
 *
 * Input:  the sequent to which the rule is applied, and an integer indicating
 *         which term in the sequent to apply the rule to
 * Output: if the rule can be applied, the resulting sequent;
 *         otherwise, noSeq(), indicating the rule application failed
 *
 * For the rule to be applied, the termm at the specified index must be of
 * the form "(<psi!>phi)^a".
 * 
 * If this condition is met, a sequent, where the specified term is replaced by
 * "(phi | psi)^a" is returned. Otherwise, noSeq() is returned.
 */
MaybeSequent applyDTestR(CloGSequent seq, int termIdx) {
	if (term(\mod(dTest(GameLog psi), GameLog phi), list[CloGName] a) := seq[termIdx]) {
		println("applied dTest");
		return sequent(seq - seq[termIdx] + term(or(psi, phi), a));
	}
	
	return noSeq();
}

/*
 * A function applying the clo rule to a sequent.
 *
 * Input:  the sequent to which the rule is applied, an integer indicating
 *         which term in the sequent to apply the rule to, and the map of
 *         closure sequents
 * Output: a pair of, if the rule can be applied, the resulting sequent,
 *         otherwise, noSeq(), indicating the rule application failed, and
 *         the potentially updated map of closure sequents
 *
 * For the rule to be applied, the term at the specified index must be of
 * the form "(<gamma^x>phi)^a".
 * Each of the names in the label a must be smaller than this "<gamma^x>phi"
 * fixpoint formula, according to the order on fixpoint formulae defined in the
 * literature.
 * 
 * If these conditions are met, a new label is created, x_n, where n is the
 * number of closure sequents (or closure sequents labels, labeled x_0 to x_{n-1}.
 * This label is added to the closure sequents as the key to the associated context
 * sequence and the index of the term in the sequent that contains the relevant
 * fixpoint formula. Then, a sequent, where the specified term is replaced
 * by "(phi & <gamma><gamma^x>phi)^[a x_n]" is returned.
 * 
 * Otherwise, a pair with a noSeq(), and the non-updated list of closure sequents
 * is returned.
 */
tuple[MaybeSequent, CloSeqs] applyClo(CloGSequent seq, int termIdx, CloSeqs cloSeqs) {
	if (term(\mod(dIter(Game gamma), GameLog phi), list[CloGName] a) := seq[termIdx]) {
		for (CloGName x <- a)
			if (fpGreaterThan(cloSeqs[x].contextSeq[cloSeqs[x].fpFormulaIdx].s, \mod(dIter(gamma), phi)))
				return <noSeq(), cloSeqs>;
		CloGName newName = nameS("x", size(cloSeqs));
		cloSeqs += (newName: <seq, termIdx>);
		
		println("applied clo");
		return <sequent(seq - seq[termIdx] + term(and(phi, \mod(gamma, \mod(dIter(gamma), phi))), a + newName)), cloSeqs>;
	}
	
	return <noSeq(), cloSeqs>;
}
