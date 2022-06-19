module unitTests::ProofSearch_test

import CloG_Base::GLASTs;
import ATP::ATP_Base;
import ATP::ProofSearch;


// Try Closure Discharge

// seq:     [ p^[] ]
// cloSeqs: empty
test bool tryDisClo_test_1() {
	CloGSequent input = [term(atomP(prop("p")), [], false)];	
	CloSeqs cloSeqs = ();
	MaybeProof output = noProof();
	
	return tryDisClo(input, cloSeqs) == output;
}

// seq:     [ p^[] ]
// cloSeqs: ( x: <[ <a^x>p^[] ], 0> )
test bool tryDisClo_test_2() {
	CloGSequent input = [term(atomP(prop("p")), [], false)];	
	CloSeqs cloSeqs = (
		name("x"): <[term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [], false)], 0>
	);
	MaybeProof output = noProof();
	
	return tryDisClo(input, cloSeqs) == output;
}

// seq:     [ <a^x>p^x ]
// cloSeqs: empty
test bool tryDisClo_test_3() {
	CloGSequent input = [term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [name("x")], false)];
	CloSeqs cloSeqs = ();
	MaybeProof output = noProof();
	
	return tryDisClo(input, cloSeqs) == output;
}

// seq:     [ <a^x>p^x ]
// cloSeqs: ( x: <[ <a^x>p^[] ], 0> )
test bool tryDisClo_test_4() {
	CloGSequent input = [term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [name("x")], false)];
	CloSeqs cloSeqs = (
		name("x"): <[term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [], false)], 0>
	);
	MaybeProof output = proof(disClo(input, name("x")));
	
	return tryDisClo(input, cloSeqs) == output;
}

// seq:     [ <a^x>p^[] ]
// cloSeqs: ( x: <[ <a^x>p^[] ], 0> )
test bool tryDisClo_test_5() {
	CloGSequent input = [term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [], false)];
	CloSeqs cloSeqs = (
		name("x"): <[term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [], false)], 0>
	);
	MaybeProof output = noProof();
	
	return tryDisClo(input, cloSeqs) == output;
}

// seq:     [ <a^x>p^y ]
// cloSeqs: ( x: <[ <a^x>p^[] ], 0> )
test bool tryDisClo_test_6() {
	CloGSequent input = [term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [name("y")], false)];
	CloSeqs cloSeqs = (
		name("x"): <[term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [], false)], 0>
	);
	MaybeProof output = noProof();
	
	return tryDisClo(input, cloSeqs) == output;
}

// seq:     [ <b^x>p^x ]
// cloSeqs: ( x: <[ <a^x>p^[] ], 0> )
test bool tryDisClo_test_7() {
	CloGSequent input = [term(\mod(dIter(atomG(agame("b"))), atomP(prop("p"))), [name("x")], false)];
	CloSeqs cloSeqs = (
		name("x"): <[term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [], false)], 0>
	);
	MaybeProof output = noProof();
	
	return tryDisClo(input, cloSeqs) == output;
}

// seq:     [ <(a||b)^x>p^x ]
// cloSeqs: ( x: <[ <a^x>p^[] ], 0> )
test bool tryDisClo_test_8() {
	CloGSequent input = [term(\mod(dIter(choice(atomG(agame("a")), atomG(agame("b")))), atomP(prop("p"))), [name("x")], false)];
	CloSeqs cloSeqs = (
		name("x"): <[term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [], false)], 0>
	);
	MaybeProof output = noProof();
	
	return tryDisClo(input, cloSeqs) == output;
}

// seq:     [ <(a)^x>p^x ]
// cloSeqs: ( x: <[ <(a||b)^x>p^[] ], 0> )
test bool tryDisClo_test_9() {
	CloGSequent input = [term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [name("x")], false)];
	CloSeqs cloSeqs = (
		name("x"): <[term(\mod(dIter(choice(atomG(agame("a")), atomG(agame("b")))), atomP(prop("p"))), [], false)], 0>
	);
	MaybeProof output = noProof();
	
	return tryDisClo(input, cloSeqs) == output;
}


// seq:     [ <a^x>p^x ]
// cloSeqs: ( x: <[ q^[] <a^x>p^[] ], 1> )
test bool tryDisClo_test_10() {
	CloGSequent input = [term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [name("x")], false)];
	CloSeqs cloSeqs = (
		name("x"): <[term(atomP(prop("q")), [], false), term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [], false)], 1>
	);
	MaybeProof output = noProof();
	
	return tryDisClo(input, cloSeqs) == output;
}

// seq:     [ q^[] <a^x>p^x ]
// cloSeqs: ( x: <[ q^[] <a^x>p^[] ], 1> )
test bool tryDisClo_test_11() {
	CloGSequent input = [term(atomP(prop("q")), [], false), term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [name("x")], false)];
	CloSeqs cloSeqs = (
		name("x"): <[term(atomP(prop("q")), [], false), term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [], false)], 1>
	);
	MaybeProof output = proof(disClo(input, name("x")));
	
	return tryDisClo(input, cloSeqs) == output;
}

// seq:     [ q^[] <a^x>p^x ]
// cloSeqs: ( x: <[ <a^x>p^[] q^[] ], 0> )
test bool tryDisClo_test_12() {
	CloGSequent input = [term(atomP(prop("q")), [], false), term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [name("x")], false)];
	CloSeqs cloSeqs = (
		name("x"): <[term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [], false), term(atomP(prop("q")), [], false)], 0>
	);
	MaybeProof output = proof(disClo(input, name("x")));
	
	return tryDisClo(input, cloSeqs) == output;
}

// seq:     [ q^[] <a^x>p^x ]
// cloSeqs: ( x: <[ <a^x>p^[] ], 0> )
test bool tryDisClo_test_13() {
	CloGSequent input = [term(atomP(prop("q")), [], false), term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [name("x")], false)];
	CloSeqs cloSeqs = (
		name("x"): <[term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [], false)], 0>
	);
	CloGSequent seq1 = [term(atomP(prop("q")), [], true), term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [name("x")], false)];
	CloGSequent seq2 = [term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [name("x")], false)];
	
	MaybeProof output = proof(CloGUnaryInf(seq1, weak(), disClo(seq2, name("x"))));
	
	return tryDisClo(input, cloSeqs) == output;
}

// seq:     [ <a^y>p^y ]
// cloSeqs: ( x: <[ <b^x>q^[] ], 0>, y: <[ <a^x>p^[] ], 0> )
test bool tryDisClo_test_14() {
	CloGSequent input = [term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [name("y")], false)];
	CloSeqs cloSeqs = (
		name("x"): <[term(\mod(dIter(atomG(agame("b"))), atomP(prop("q"))), [], false)], 0>,
		name("y"): <[term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [], false)], 0>
	);
	MaybeProof output = proof(disClo(input, name("y")));
	
	return tryDisClo(input, cloSeqs) == output;
}

// seq:     [ <a^y>p^[x, y] ]
// cloSeqs: ( x: <[ <b^x>q^[] ], 0>, y: <[ <a^x>p^x ], 0> )
test bool tryDisClo_test_15() {
	CloGSequent input = [term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [name("x"), name("y")], false)];
	CloSeqs cloSeqs = (
		name("x"): <[term(\mod(dIter(atomG(agame("b"))), atomP(prop("q"))), [], false)], 0>,
		name("y"): <[term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [name("x")], false)], 0>
	);
	MaybeProof output = proof(disClo(input, name("y")));
	
	return tryDisClo(input, cloSeqs) == output;
}


// Detect Cycles

// from: [ ]
// to:   [ p^[] ]
test bool detectCycles_test_1() {
	CloGSequent input = [term(atomP(prop("p")), [], false)];
	list[CloGSequent] fpSeqs = [];

	return detectCycles(input, fpSeqs) == false;
}

// from: [ [ p^[] ] ]
// to:   [ p^[] ]
test bool detectCycles_test_2() {
	CloGSequent input = [term(atomP(prop("p")), [], false)];
	list[CloGSequent] fpSeqs = [ [term(atomP(prop("p")), [], false)] ];

	return detectCycles(input, fpSeqs) == true;
}

// from: [ [ p^[] ] ]
// to:   [ q^[] ]
test bool detectCycles_test_3() {
	CloGSequent input = [term(atomP(prop("q")), [], false)];
	list[CloGSequent] fpSeqs = [ [term(atomP(prop("p")), [], false)] ];

	return detectCycles(input, fpSeqs) == false;
}

// from: [ [ p^[] ] ]
// to:   [ p^[] q^[] ]
test bool detectCycles_test_4() {
	CloGSequent input = [term(atomP(prop("p")), [], false), term(atomP(prop("q")), [], false)];
	list[CloGSequent] fpSeqs = [ [term(atomP(prop("p")), [], false)] ];

	return detectCycles(input, fpSeqs) == false;
}

// from: [ [ p^[] q^[] ] ]
// to:   [ p^[] ]
test bool detectCycles_test_5() {
	CloGSequent input = [term(atomP(prop("p")), [], false)];
	list[CloGSequent] fpSeqs = [ [term(atomP(prop("p")), [], false), term(atomP(prop("q")), [], false)] ];

	return detectCycles(input, fpSeqs) == false;
}

// from: [ [ p^[] q^[] ] ]
// to:   [ q^[] p^[] ]
test bool detectCycles_test_6() {
	CloGSequent input = [term(atomP(prop("q")), [], false), term(atomP(prop("p")), [], false)];
	list[CloGSequent] fpSeqs = [ [term(atomP(prop("p")), [], false), term(atomP(prop("q")), [], false)] ];

	return detectCycles(input, fpSeqs) == true;
}

// from: [ [ p^[] ] ]
// to:   [ p^x ]
test bool detectCycles_test_7() {
	CloGSequent input = [term(atomP(prop("p")), [name("x")], false)];
	list[CloGSequent] fpSeqs = [ [term(atomP(prop("p")), [], false)] ];

	return detectCycles(input, fpSeqs) == false;
}

// from: [ [ p^x ] ]
// to:   [ p^[] ]
test bool detectCycles_test_8() {
	CloGSequent input = [term(atomP(prop("p")), [], false)];
	list[CloGSequent] fpSeqs = [ [term(atomP(prop("p")), [name("x")], false)] ];

	return detectCycles(input, fpSeqs) == false;
}

// from: [ [ p^y ] ]
// to:   [ p^[x y] ]
test bool detectCycles_test_9() {
	CloGSequent input = [term(atomP(prop("p")), [name("x"), name("y")], false)];
	list[CloGSequent] fpSeqs = [ [term(atomP(prop("p")), [name("y")], false)] ];

	return detectCycles(input, fpSeqs) == false;
}

// from: [ [ p^[x y] ] ]
// to:   [ p^y ]
test bool detectCycles_test_10() {
	CloGSequent input = [term(atomP(prop("p")), [ name("y")], false)];
	list[CloGSequent] fpSeqs = [ [term(atomP(prop("p")), [name("y"), name("x")], false)] ];

	return detectCycles(input, fpSeqs) == false;
}

// from: [ [ p^[y x] ] ]
// to:   [ p^[x y] ]
test bool detectCycles_test_11() {
	CloGSequent input = [term(atomP(prop("p")), [ name("x"), name("y")], false)];
	list[CloGSequent] fpSeqs = [ [term(atomP(prop("p")), [name("y"), name("x")], false)] ];

	return detectCycles(input, fpSeqs) == true;
}

// from: [ [ p^[] p^y ] ]
// to:   [ p^x p^y ]
test bool detectCycles_test_12() {
	CloGSequent input = [term(atomP(prop("p")), [name("x")], false), term(atomP(prop("p")), [ name("y") ], false)];
	list[CloGSequent] fpSeqs = [ [term(atomP(prop("p")), [], false), term(atomP(prop("p")), [name("y")], false)] ];

	return detectCycles(input, fpSeqs) == false;
}

// from: [ [ p^[] p^x ] ]
// to:   [ p^x p^y ]
test bool detectCycles_test_13() {
	CloGSequent input = [term(atomP(prop("p")), [name("x")], false), term(atomP(prop("p")), [ name("x") ], false)];
	list[CloGSequent] fpSeqs = [ [term(atomP(prop("p")), [], false), term(atomP(prop("p")), [name("x")], false)] ];

	return detectCycles(input, fpSeqs) == false;
}

// from: [ [ p^x p^y ] ]
// to:   [ p^[] p^[x y] ]
test bool detectCycles_test_14() {
	CloGSequent input = [term(atomP(prop("p")), [ ], false), term(atomP(prop("p")), [ name("x"), name("y") ], false)];
	list[CloGSequent] fpSeqs = [ [term(atomP(prop("p")), [ name("x") ], false), term(atomP(prop("p")), [ name("y") ], false)] ];

	return detectCycles(input, fpSeqs) == false;
}

// from: [ [ p^[] p^x q^[] ]
// to:   [ p^x q^[] q^y ]
test bool detectCycles_test_15() {
	CloGSequent input = [term(atomP(prop("p")), [name("x")], false), term(atomP(prop("q")), [], false), term(atomP(prop("q")), [ name ("y") ], false)];
	list[CloGSequent] fpSeqs = [ [term(atomP(prop("p")), [], false), term(atomP(prop("p")), [ name("x") ], false), term(atomP(prop("q")), [], false)] ];

	return detectCycles(input, fpSeqs) == false;
}

// from: [ [ p^[] ] [ q^[] ] ]
// to:   [ p^[] ]
test bool detectCycles_test_16() {
	CloGSequent input = [term(atomP(prop("p")), [], false)];
	list[CloGSequent] fpSeqs = [ [term(atomP(prop("p")), [], false)], [term(atomP(prop("q")), [], false)] ];

	return detectCycles(input, fpSeqs) == true;
}

// from: [ [ p^[] ] [ q^[] ] [ r^[] ] ]
// to:   [ q^[] ]
test bool detectCycles_test_17() {
	CloGSequent input = [term(atomP(prop("q")), [], false)];
	list[CloGSequent] fpSeqs = [ [term(atomP(prop("p")), [], false)], [term(atomP(prop("q")), [], false)], [term(atomP(prop("r")), [], false)] ];

	return detectCycles(input, fpSeqs) == true;
}

// from: [ [ p^[] ] [ q^[x y] r^[] ] [ s^[] ] ]
// to:   [ r^[] q^[y x] ]
test bool detectCycles_test_18() {
	CloGSequent input = [term(atomP(prop("r")), [], false), term(atomP(prop("q")), [name("y"), name("x")], false)];
	list[CloGSequent] fpSeqs = [ [term(atomP(prop("p")), [], false)], [term(atomP(prop("q")), [name("x"), name("y")], false), term(atomP(prop("r")), [], false)], [term(atomP(prop("s")), [], false)] ];

	return detectCycles(input, fpSeqs) == true;
}


// Proof Search with Weakening/Expanding

// from: [ p^[] ]
// to :  [ p^[] ]
test bool proofSearchWeakExp_test_1() {
	CloGSequent from = [term(atomP(prop("p")), [], false)];
	CloGSequent to = [term(atomP(prop("p")), [], false)];
	MaybeProof output = proof(CloGUnaryInf(to, weak(), CloGLeaf()));
	
	return proofSearchWeakExp(from, to) == output;
}

// from: [ p^[] ]
// to :  [ q^[] ]
test bool proofSearchWeakExp_test_2() {
	CloGSequent from = [term(atomP(prop("p")), [], false)];
	CloGSequent to = [term(atomP(prop("q")), [], false)];
	MaybeProof output = noProof();
	
	return proofSearchWeakExp(from, to) == output;
}

// from: [ p^[] q^[] ]
// to :  [ p^[] ]
test bool proofSearchWeakExp_test_3() {
	CloGSequent from = [term(atomP(prop("p")), [], false), term(atomP(prop("q")), [], false)];
	CloGSequent seq1 = [term(atomP(prop("p")), [], false), term(atomP(prop("q")), [], true)];
	CloGSequent to = [term(atomP(prop("p")), [], false)];
	MaybeProof output = proof(CloGUnaryInf(seq1, weak(), CloGUnaryInf(to, weak(), CloGLeaf())));
	
	return proofSearchWeakExp(from, to) == output;
}

// from: [ p^[] ]
// to :  [ p^[] q^[] ]
test bool proofSearchWeakExp_test_4() {
	CloGSequent from = [term(atomP(prop("p")), [], false)];
	CloGSequent to = [term(atomP(prop("p")), [], false), term(atomP(prop("q")), [], false)];
	MaybeProof output = noProof();
	
	return proofSearchWeakExp(from, to) == output;
}

// from: [ p^[] q^[] r^[] ]
// to :  [ q^[] ]
test bool proofSearchWeakExp_test_5() {
	CloGSequent from = [term(atomP(prop("p")), [], false), term(atomP(prop("q")), [], false), term(atomP(prop("r")), [], false)];
	CloGSequent seq1 = [term(atomP(prop("p")), [], true), term(atomP(prop("q")), [], false), term(atomP(prop("r")), [], false)];
	CloGSequent seq2 = [term(atomP(prop("q")), [], false), term(atomP(prop("r")), [], true)];
	CloGSequent to = [term(atomP(prop("q")), [], false)];
	MaybeProof output = proof(CloGUnaryInf(seq1, weak(), CloGUnaryInf(seq2, weak(), CloGUnaryInf(to, weak(), CloGLeaf()))));
	
	return proofSearchWeakExp(from, to) == output;
}

// from: [ p^[] q^[] r^[] ]
// to :  [ p^[] r^[] ]
test bool proofSearchWeakExp_test_6() {
	CloGSequent from = [term(atomP(prop("p")), [], false), term(atomP(prop("q")), [], false), term(atomP(prop("r")), [], false)];
	CloGSequent seq1 = [term(atomP(prop("p")), [], false), term(atomP(prop("q")), [], true), term(atomP(prop("r")), [], false)];
	CloGSequent to = [term(atomP(prop("p")), [], false), term(atomP(prop("r")), [], false)];
	MaybeProof output = proof(CloGUnaryInf(seq1, weak(), CloGUnaryInf(to, weak(), CloGLeaf())));
	
	return proofSearchWeakExp(from, to) == output;
}

// from: [ p^[] q^[] r^[] ]
// to :  [ r^[] p^[] ]
test bool proofSearchWeakExp_test_7() {
	CloGSequent from = [term(atomP(prop("p")), [], false), term(atomP(prop("q")), [], false), term(atomP(prop("r")), [], false)];
	CloGSequent seq1 = [term(atomP(prop("p")), [], false), term(atomP(prop("q")), [], true), term(atomP(prop("r")), [], false)];
	CloGSequent seq2 = [term(atomP(prop("p")), [], false), term(atomP(prop("r")), [], false)];
	CloGSequent to = [term(atomP(prop("r")), [], false), term(atomP(prop("p")), [], false)];
	MaybeProof output = proof(CloGUnaryInf(seq1, weak(), CloGUnaryInf(seq2, weak(), CloGLeaf())));
	
	return proofSearchWeakExp(from, to) == output;
}

// from: [ p^[x] ]
// to :  [ p^[] ]
test bool proofSearchWeakExp_test_8() {
	CloGSequent from = [term(atomP(prop("p")), [name("x")], false)];
	CloGSequent seq1 = [term(atomP(prop("p")), [name("x")], true)];
	CloGSequent to = [term(atomP(prop("p")), [], false)];
	MaybeProof output = proof(CloGUnaryInf(seq1, exp(), CloGUnaryInf(to, weak(), CloGLeaf())));
	
	return proofSearchWeakExp(from, to) == output;
}

// from: [ p^[] ]
// to :  [ p^[x] ]
test bool proofSearchWeakExp_test_9() {
	CloGSequent from = [term(atomP(prop("p")), [], false)];
	CloGSequent to = [term(atomP(prop("p")), [name("x")], false)];
	MaybeProof output = noProof();
	
	return proofSearchWeakExp(from, to) == output;
}

// from: [ p^[x y] ]
// to :  [ p^[] ]
test bool proofSearchWeakExp_test_10() {
	CloGSequent from = [term(atomP(prop("p")), [name("x"), name("y")], false)];
	CloGSequent seq1 = [term(atomP(prop("p")), [name("x"), name("y")], true)];
	CloGSequent seq2 = [term(atomP(prop("p")), [name("y")], true)];
	CloGSequent to = [term(atomP(prop("p")), [], false)];
	MaybeProof output = proof(CloGUnaryInf(seq1, exp(), CloGUnaryInf(seq2, exp(), CloGUnaryInf(to, weak(), CloGLeaf()))));
	
	return proofSearchWeakExp(from, to) == output;
}

// from: [ p^[x y] ]
// to :  [ p^[x] ]
test bool proofSearchWeakExp_test_11() {
	CloGSequent from = [term(atomP(prop("p")), [name("x"), name("y")], false)];
	CloGSequent seq1 = [term(atomP(prop("p")), [name("x"), name("y")], true)];
	CloGSequent to = [term(atomP(prop("p")), [name("x")], false)];
	MaybeProof output = proof(CloGUnaryInf(seq1, exp(), CloGUnaryInf(to, weak(), CloGLeaf())));
	
	return proofSearchWeakExp(from, to) == output;
}

// from: [ p^[x y z] ]
// to :  [ p^[y] ]
test bool proofSearchWeakExp_test_12() {
	CloGSequent from = [term(atomP(prop("p")), [name("x"), name("y"), name("z")], false)];
	CloGSequent seq1 = [term(atomP(prop("p")), [name("x"), name("y"), name("z")], true)];
	CloGSequent seq2 = [term(atomP(prop("p")), [name("y"), name("z")], true)];
	CloGSequent to = [term(atomP(prop("p")), [name("y")], false)];
	MaybeProof output = proof(CloGUnaryInf(seq1, exp(), CloGUnaryInf(seq2, exp(), CloGUnaryInf(to, weak(), CloGLeaf()))));
	
	return proofSearchWeakExp(from, to) == output;
}

// from: [ p^[x y z] ]
// to :  [ p^[x z] ]
test bool proofSearchWeakExp_test_13() {
	CloGSequent from = [term(atomP(prop("p")), [name("x"), name("y"), name("z")], false)];
	CloGSequent seq1 = [term(atomP(prop("p")), [name("x"), name("y"), name("z")], true)];
	CloGSequent to = [term(atomP(prop("p")), [name("x"), name("z")], false)];
	MaybeProof output = proof(CloGUnaryInf(seq1, exp(), CloGUnaryInf(to, weak(), CloGLeaf())));
	
	return proofSearchWeakExp(from, to) == output;
}

// from: [ p^[x y z] ]
// to :  [ p^[z x] ]
test bool proofSearchWeakExp_test_14() {
	CloGSequent from = [term(atomP(prop("p")), [name("x"), name("y"), name("z")], false)];
	CloGSequent seq1 = [term(atomP(prop("p")), [name("x"), name("y"), name("z")], true)];
	CloGSequent seq2 = [term(atomP(prop("p")), [name("x"), name("z")], false)];
	CloGSequent to = [term(atomP(prop("p")), [name("z"), name("x")], false)];
	MaybeProof output = proof(CloGUnaryInf(seq1, exp(), CloGUnaryInf(seq2, weak(), CloGLeaf())));
	
	return proofSearchWeakExp(from, to) == output;
}

// from: [ p^[x] q^[] ]
// to :  [ p^[] ]
test bool proofSearchWeakExp_test_15() {
	CloGSequent from = [term(atomP(prop("p")), [name("x")], false), term(atomP(prop("q")), [], false)];
	CloGSequent seq1 = [term(atomP(prop("p")), [name("x")], true), term(atomP(prop("q")), [], false)];
	CloGSequent seq2 = [term(atomP(prop("p")), [], false), term(atomP(prop("q")), [], true)];
	CloGSequent to = [term(atomP(prop("p")), [], false)];
	MaybeProof output = proof(CloGUnaryInf(seq1, exp(), CloGUnaryInf(seq2, weak(), CloGUnaryInf(to, weak(), CloGLeaf()))));
	
	return proofSearchWeakExp(from, to) == output;
}

// from: [ p^[] q^[x] ]
// to :  [ p^[] ]
test bool proofSearchWeakExp_test_16() {
	CloGSequent from = [term(atomP(prop("p")), [], false), term(atomP(prop("q")), [name("x")], false)];
	CloGSequent seq1 = [term(atomP(prop("p")), [], false), term(atomP(prop("q")), [name("x")], true)];
	CloGSequent to = [term(atomP(prop("p")), [], false)];
	MaybeProof output = proof(CloGUnaryInf(seq1, weak(), CloGUnaryInf(to, weak(), CloGLeaf())));
	
	return proofSearchWeakExp(from, to) == output;
}

// from: [ p^[] q^[x] ]
// to :  [ q^[] ]
test bool proofSearchWeakExp_test_17() {
	CloGSequent from = [term(atomP(prop("p")), [], false), term(atomP(prop("q")), [name("x")], false)];
	CloGSequent seq1 = [term(atomP(prop("p")), [], true), term(atomP(prop("q")), [name("x")], false)];
	CloGSequent seq2 = [term(atomP(prop("q")), [name("x")], true)];
	CloGSequent to = [term(atomP(prop("q")), [], false)];
	MaybeProof output = proof(CloGUnaryInf(seq1, weak(), CloGUnaryInf(seq2, exp(), CloGUnaryInf(to, weak(), CloGLeaf()))));
	
	return proofSearchWeakExp(from, to) == output;
}

// from: [ p^[] q^[x y z] r^[] ]
// to :  [ q^[y] ]
test bool proofSearchWeakExp_test_18() {
	CloGSequent from = [term(atomP(prop("p")), [], false), term(atomP(prop("q")), [name("x"), name("y"), name("z")], false), term(atomP(prop("r")), [], false)];
	CloGSequent seq1 = [term(atomP(prop("p")), [], true), term(atomP(prop("q")), [name("x"), name("y"), name("z")], false), term(atomP(prop("r")), [], false)];
	CloGSequent seq2 = [term(atomP(prop("q")), [name("x"), name("y"), name("z")], true), term(atomP(prop("r")), [], false)];
	CloGSequent seq3 = [term(atomP(prop("q")), [name("y"), name("z")], true), term(atomP(prop("r")), [], false)];
	CloGSequent seq4 = [term(atomP(prop("q")), [name("y")], false), term(atomP(prop("r")), [], true)];
	CloGSequent to = [term(atomP(prop("q")), [name("y")], false)];
	MaybeProof output = proof(CloGUnaryInf(seq1, weak(), CloGUnaryInf(seq2, exp(), CloGUnaryInf(seq3, exp(), CloGUnaryInf(seq4, weak(), CloGUnaryInf(to, weak(), CloGLeaf()))))));
	
	return proofSearchWeakExp(from, to) == output;
}