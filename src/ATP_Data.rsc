module ATP_Data

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