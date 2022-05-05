module ATP_Base
/*
 * Module defining data types relevant for the Automated Theorem Prover, and
 * some helper functions.
 */

import GLASTs;
import Map;

/* 
 * A FpSeq, or fixpoint sequent is a tuple containing a sequent that contains
 * a specific fixpoint formula, and the index of the term in that sequent which
 * contains the fixpoint formula.
 */
alias FpSeq = tuple[CloGSequent contextSeq, int fpFormulaIdx];

/* 
 * A CloSeqs is a map, mapping each name associated with a fixpoint formula to the
 * FpSeq containing that formula at the specified index.
 */
alias CloSeqs = map[CloGName name, FpSeq fpSeq];

/*
 * MaybeProof is either a CloGProof, or noProof(), which indicates no proof could be
 * found.
 */
data MaybeProof
	= proof(CloGProof p)
	| noProof();
	
/*
 * MaybeSequent is either a CloGSequent, or noSeq(), which indicates no sequent could
 * be derived.
 */
data MaybeSequent
	= sequent(CloGSequent seq)
	| noSeq();

/*
 * MaybeSequents is either a pair of CloGSequents, or noSeqs(), which indicates no
 * sequents could be derived.
 */
data MaybeSequents
    = sequents(CloGSequent left, CloGSequent right)
    | noSeqs();
    
/*
 * An algorithm returning whether one fixpoint formula is bigger than the other,
 * according to the fixpoint ordering defined in the literature.
 *
 * Input:  two GameLog formulae
 * Output: a bool, true if the left GameLog formula is greater than the right
 *         GameLog formula according to the fixpoint ordering, and false otherwise.
 *
 * One fixpoint formula is considered greater than another fixpoint formula, if
 * the game in the other fixpoint formula is a subterm of the game in the one
 * fixpoint formula.
 */
bool fpGreaterThan(GameLog left, GameLog right) {
	if (\mod(Game fp0, GameLog _) := left && \mod(Game fp1, GameLog _) := right)
		if (
	    	(iter(Game _) := fp0 || dIter(Game _) := fp0)
         && (iter(Game _) := fp1 || dIter(Game _) := fp1)
		)
			return subTerm(fp1, fp0);
	return false;
}

/*
 * An algorithm returning whether one game formula is a subterm of the other.
 *
 * Input:  two Game formulae
 * Output: a bool, true if the left Game formula is a subterm of the right, and
 * false otherwise.
 *
 * One Game formula is a subterm of the other, if it appears in the other
 * formula, which is the same as saying the one Game formula is a descendant of
 * the other.
 */
bool subTerm(Game g, Game h) {
	if (/g := h)
		return true;
	return false;
}