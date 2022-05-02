module GLASTs
/*
 * Module defining all Abstract Syntax Types for the Game logic proof transformations
 */
 
/*
 * Abstract Syntax for a CloG Proof
 */

data CloGProof(loc src = |tmp:///|)
	= CloGLeaf()
	| disClo(list[CloGTerm] seq, CloGName n)
	| CloGUnaryInf(list[CloGTerm] seq, CloGRule rule, CloGProof inf)
	| CloGBinaryInf(list[CloGTerm] seq, CloGProof infL, CloGProof infR);
	
data CloGSequent(loc src = |tmp:///|)
    = CloGSequent(list[CloGTerm] seq);

data CloGTerm(loc src = |tmp:///|)
	= term(GameLog s, list[CloGName] label);

data CloGRule(loc src = |tmp:///|)
	= ax1()
	| modm()
	| andR()
	| orR()
	| choiceR()
	| dChoiceR()
	| weak()
	| exp()
	| concatR()
	| iterR()
	| testR()
	| dIterR()
	| dTestR()
	| clo(CloGName n);

data CloGName(loc src = |tmp:///|)
	= name(str l)
	| nameS(str l, int sub);
	
/*
 * Abstract Syntax for a Game Logic Formula
 */
	
data GameLog(loc src = |tmp:///|)
	= top()
	| bot()
	| atomP(Prop p)
	| neg(GameLog pr)
	| \mod(Game g, GameLog pr)
	| modExp(Game g, GameLog pr, int n) // fp annotation for expansion rule
	| dMod(Game g, GameLog pr)
	| and(GameLog pL, GameLog pR)
	| or(GameLog pL, GameLog pR)
	| cond(GameLog pL, GameLog pR)
	| biCond(GameLog pL, GameLog pR);
	
data Game(loc src = |tmp:///|)
	= atomG(AGame g) 
	| dual(Game ga) 
	| \test(GameLog p) 
	| dTest(GameLog p)
	| iter(Game ga)
	| dIter(Game ga)
	| dIterExp(Game ga, int n) // fp annotation for expansion rule
	| concat(Game gL, Game gR)
	| choice(Game gL, Game gR)
	| dChoice(Game gL, Game gR);

/*
 * Abstract syntax for atomic games and propositions
 */

data AGame(loc src = |tmp:///|)
	= agame(str l)
	| agameS(str l, int sub);

data Prop(loc src = |tmp:///|)
	= prop(str l)
	| propS(str l, int sub);