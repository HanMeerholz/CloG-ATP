module ATP_Base

import GLASTs;

alias FpSeq = tuple[CloGSequent contextSeq, int fpFormulaIdx];
alias CloSeq = tuple[CloGName name, FpSeq fpSeq];

/*
 * Define MaybeProof as either a proof, or null, if no proof could be found.
 */
data MaybeProof
	= proof(CloGProof p)
	| noProof();
	
data MaybeSequent
	= sequent(CloGSequent seq)
	| noSeq();
	
data MaybeSequents
    = sequents(CloGSequent left, CloGSequent right)
    | noSeqs();
    
bool fpGreaterThan(GameLog left, GameLog right) {
	if (\mod(Game fp0, GameLog _) := left && \mod(Game fp1, GameLog _) := right)
		if (
	    	(iter(Game _) := fp0 || dIter(Game _) := fp0)
         && (iter(Game _) := fp1 || dIter(Game _) := fp1)
		)
			return subTerm(fp1, fp0);
	return false;
}

bool subTerm(Game g, Game h) {
	for (/g := h)
		return true;
	return false;
}