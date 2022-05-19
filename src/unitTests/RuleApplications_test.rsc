module unitTests::RuleApplications_test

import RuleApplications;
import GLASTs;
import ATP_Base;
import IO;

// Apply Ax1

// p^[]
test bool applyAx1_test_1() {
	CloGSequent input = [term(atomP(prop("p")), [], false)];	
	return applyAx1(input) == noSeq();
}
// p^[] ~p^[]
test bool applyAx1_test_2() {
	CloGSequent input = [term(atomP(prop("p")), [], false), term(neg(atomP(prop("p"))), [], false)];
	return applyAx1(input) == sequent([]);
}
// ~p^[] p^[]
test bool applyAx1_test_3() {
	CloGSequent input = [term(neg(atomP(prop("p"))), [], false), term(atomP(prop("p")), [], false)];
	return applyAx1(input) == sequent([]);
}
// p^[] ~q^[]
test bool applyAx1_test_4() {
	CloGSequent input = [term(atomP(prop("p")), [], false), term(neg(atomP(prop("q"))), [], false)];
	return applyAx1(input) == noSeq();
}
// p^[] ~p^[] q^[]
test bool applyAx1_test_5() {
	CloGSequent input = [term(atomP(prop("p")), [], false), term(neg(atomP(prop("p"))), [], false), term(atomP(prop("q")), [], false)];
	return applyAx1(input) == noSeq();
}
// p^[] ~p^x
test bool applyAx1_test_6() {
	CloGSequent input = [term(atomP(prop("p")), [], false), term(neg(atomP(prop("p"))), [name("x")], false)];
	return applyAx1(input) == noSeq();
}
// ~p^[] ~(~p)^[]
test bool applyAx1_test_7() {
	CloGSequent input = [term(neg(atomP(prop("p"))), [], false), term(neg(neg(atomP(prop("p")))), [], false)];
	return applyAx1(input) == noSeq();
}
// (p|~p)^[]
test bool applyAx1_test_8() {
	CloGSequent input = [term(or(atomP(prop("p")), neg(atomP(prop("p")))), [], false)];
	return applyAx1(input) == noSeq();
}


// Apply Modm

// p^[]
test bool applyModm_test_1() {
	CloGSequent input = [term(atomP(prop("p")), [], false)];
	MaybeSequent output = noSeq();
	
	return applyModm(input) == output;
}
// <a>p^[]
test bool applyModm_test_2() {
	CloGSequent input = [term(\mod(atomG(agame("a")), atomP(prop("p"))), [], false)];
	MaybeSequent output = noSeq();
	
	return applyModm(input) == output;
}
// <a>p^x <a>q^y
test bool applyModm_test_3() {
	CloGSequent input = [term(\mod(atomG(agame("a")), atomP(prop("p"))), [name("x")], false), term(\mod(atomG(agame("a")), atomP(prop("q"))), [name("y")], false)];
	MaybeSequent output = noSeq();
	
	return applyModm(input) == output;
}
// <a>p^x <a^d>q^y
test bool applyModm_test_4() {
	CloGSequent input = [term(\mod(atomG(agame("a")), atomP(prop("p"))), [name("x")], false), term(\mod(dual(atomG(agame("a"))), atomP(prop("q"))), [name("y")], false)];
	MaybeSequent output = sequent([term(atomP(prop("p")), [name("x")], false), term(atomP(prop("q")), [name("y")], false)]);
	
	return applyModm(input) == output;
}
// <a^d>p^x <a>q^y
test bool applyModm_test_5() {
	CloGSequent input = [term(\mod(dual(atomG(agame("a"))), atomP(prop("p"))), [name("x")], false), term(\mod(atomG(agame("a")), atomP(prop("q"))), [name("y")], false)];
	MaybeSequent output = sequent([term(atomP(prop("p")), [name("x")], false), term(atomP(prop("q")), [name("y")], false)]);
	
	return applyModm(input) == output;
}
// <a>p^x <b^d>q^y
test bool applyModm_test_6() {
	CloGSequent input = [term(\mod(atomG(agame("a")), atomP(prop("p"))), [name("x")], false), term(\mod(dual(atomG(agame("b"))), atomP(prop("q"))), [name("y")], false)];
	MaybeSequent output = noSeq();
	
	return applyModm(input) == output;
}
// <a>p^x <a^d>q^y r^[]
test bool applyModm_test_7() {
	CloGSequent input = [term(\mod(atomG(agame("a")), atomP(prop("p"))), [name("x")], false), term(\mod(dual(atomG(agame("a"))), atomP(prop("q"))), [name("y")], false), term(atomP(prop("r")), [], false)];
	MaybeSequent output = noSeq();
	
	return applyModm(input) == output;
}
// (<a>p | <a^d>q)^x
test bool applyModm_test_8() {
	CloGSequent input = [term(or(\mod(atomG(agame("a")), atomP(prop("p"))), \mod(dual(atomG(agame("a"))), atomP(prop("q")))), [name("x")], false)];
	MaybeSequent output = noSeq();
	
	return applyModm(input) == output;
}

// Apply Or

// p^[]
test bool applyOr_test_1() {
	CloGSequent input = [term(atomP(prop("p")), [], false)];
	MaybeSequent output = noSeq();
	
	return applyOr(input, 0) == output;
}
// (p|q)^[]
test bool applyOr_test_2() {
	CloGSequent input = [term(or(atomP(prop("p")), atomP(prop("q"))), [], false)];
	MaybeSequent output = sequent([term(atomP(prop("p")), [], false), term(atomP(prop("q")), [], false)]);
	
	return applyOr(input, 0) == output;
}
// (p|~p)^[]
test bool applyOr_test_3() {
	CloGSequent input = [term(or(atomP(prop("p")), neg(atomP(prop("p")))), [], false)];
	MaybeSequent output = sequent([term(atomP(prop("p")), [], false), term(neg(atomP(prop("p"))), [], false)]);
	
	return applyOr(input, 0) == output;
}
// (p|q)^x
test bool applyOr_test_4() {
	CloGSequent input = [term(or(atomP(prop("p")), atomP(prop("q"))), [name("x")], false)];
	MaybeSequent output = sequent([term(atomP(prop("p")), [name("x")], false), term(atomP(prop("q")), [name("x")], false)]);
	
	return applyOr(input, 0) == output;
}
// [(p|q)^[] r^[]] (apply to first term)
test bool applyOr_test_5() {
	CloGSequent input = [term(or(atomP(prop("p")), atomP(prop("q"))), [], false), term(atomP(prop("r")), [], false)];
	MaybeSequent output = sequent([term(atomP(prop("p")), [], false), term(atomP(prop("q")), [], false), term(atomP(prop("r")), [], false)]);
	
	return applyOr(input, 0) == output;
}
// [(p|q)^[] r^[]] (apply to second term)
test bool applyOr_test_6() {
	CloGSequent input = [term(or(atomP(prop("p")), atomP(prop("q"))), [], false), term(atomP(prop("r")), [], false)];
	MaybeSequent output = noSeq();
	
	return applyOr(input, 1) == output;
}
// [p^[] (q|r)^[]] (apply to second term)
test bool applyOr_test_7() {
	CloGSequent input = [term(atomP(prop("p")), [], false), term(or(atomP(prop("q")), atomP(prop("r"))), [], false)];
	MaybeSequent output = sequent([term(atomP(prop("p")), [], false), term(atomP(prop("q")), [], false), term(atomP(prop("r")), [], false)]);
	
	return applyOr(input, 1) == output;
}
// [p^[] (q|r)^[] s^[]] (apply to second term)
test bool applyOr_test_8() {
	CloGSequent input = [term(atomP(prop("p")), [], false), term(or(atomP(prop("q")), atomP(prop("r"))), [], false), term(atomP(prop("s")), [], false)];
	MaybeSequent output = sequent([term(atomP(prop("p")), [], false), term(atomP(prop("q")), [], false), term(atomP(prop("r")), [], false), term(atomP(prop("s")), [], false)]);
	
	return applyOr(input, 1) == output;
}
// [(p|q)^[] (r|s)^[]] (apply to first term)
test bool applyOr_test_9() {
	CloGSequent input = [term(or(atomP(prop("p")), atomP(prop("q"))), [], false), term(or(atomP(prop("r")), atomP(prop("s"))), [], false)];
	MaybeSequent output = sequent([term(atomP(prop("p")), [], false), term(atomP(prop("q")), [], false), term(or(atomP(prop("r")), atomP(prop("s"))), [], false)]);
	
	return applyOr(input, 0) == output;
}
// [(p|q)^[] (r|s)^[]] (apply to second term)
test bool applyOr_test_10() {
	CloGSequent input = [term(or(atomP(prop("p")), atomP(prop("q"))), [], false), term(or(atomP(prop("r")), atomP(prop("s"))), [], false)];
	MaybeSequent output = sequent([term(or(atomP(prop("p")), atomP(prop("q"))), [], false), term(atomP(prop("r")), [], false), term(atomP(prop("s")), [], false)]);
	
	return applyOr(input, 1) == output;
}
// [(p|q)^[] (r|s)^[]] (apply to both terms)
test bool applyOr_test_11() {
	CloGSequent input = [term(or(atomP(prop("p")), atomP(prop("q"))), [], false), term(or(atomP(prop("r")), atomP(prop("s"))), [], false)];
	MaybeSequent output = sequent([term(atomP(prop("p")), [], false), term(atomP(prop("q")), [], false), term(atomP(prop("r")), [], false), term(atomP(prop("s")), [], false)]);
	
	return applyOr(applyOr(input, 0).seq, 2) == output;
}
// [<a>(p|q)^[]]
test bool applyOr_test_12() {
	CloGSequent input = [term(\mod(atomG(agame("a")), or(atomP(prop("p")), atomP(prop("q")))), [], false)];
	MaybeSequent output = noSeq();
	
	return applyOr(input, 0) == output;
}


// Apply And

// p^[]
test bool applyAnd_test_1() {
	CloGSequent input = [term(atomP(prop("p")), [], false)];
	MaybeSequents output = noSeqs();
	
	return applyAnd(input, 0) == output;
}
// (p&q)^[]
test bool applyAnd_test_2() {
	CloGSequent input = [term(and(atomP(prop("p")), atomP(prop("q"))), [], false)];
	MaybeSequents output = sequents([term(atomP(prop("p")), [], false)], [term(atomP(prop("q")), [], false)]);
	
	return applyAnd(input, 0) == output;
}
// (p&~p)^[]
test bool applyAnd_test_3() {
	CloGSequent input = [term(and(atomP(prop("p")), neg(atomP(prop("p")))), [], false)];
	MaybeSequents output = sequents([term(atomP(prop("p")), [], false)], [term(neg(atomP(prop("p"))), [], false)]);
	
	return applyAnd(input, 0) == output;
}
// (p&q)^x
test bool applyAnd_test_4() {
	CloGSequent input = [term(and(atomP(prop("p")), atomP(prop("q"))), [name("x")], false)];
	MaybeSequents output = sequents([term(atomP(prop("p")), [name("x")], false)], [term(atomP(prop("q")), [name("x")], false)]);
	
	return applyAnd(input, 0) == output;
}
// [(p&q)^[] r^[]] (apply to first term)
test bool applyAnd_test_5() {
	CloGSequent input = [term(and(atomP(prop("p")), atomP(prop("q"))), [], false), term(atomP(prop("r")), [], false)];
	MaybeSequents output = sequents([term(atomP(prop("p")), [], false), term(atomP(prop("r")), [], false)], [term(atomP(prop("q")), [], false), term(atomP(prop("r")), [], false)]);
	
	return applyAnd(input, 0) == output;
}
// [(p&q)^[] r^[]] (apply to second term)
test bool applyAnd_test_6() {
	CloGSequent input = [term(and(atomP(prop("p")), atomP(prop("q"))), [], false), term(atomP(prop("r")), [], false)];
	MaybeSequents output = noSeqs();
	
	return applyAnd(input, 1) == output;
}
// [p^[] (q&r)^[]] (apply to second term)
test bool applyAnd_test_7() {
	CloGSequent input = [term(atomP(prop("p")), [], false), term(and(atomP(prop("q")), atomP(prop("r"))), [], false)];
	MaybeSequents output = sequents([term(atomP(prop("p")), [], false), term(atomP(prop("q")), [], false)], [term(atomP(prop("p")), [], false), term(atomP(prop("r")), [], false)]);
	
	return applyAnd(input, 1) == output;
}
// [p^[] (q&r)^[] s^[]] (apply to second term)
test bool applyAnd_test_8() {
	CloGSequent input = [term(atomP(prop("p")), [], false), term(and(atomP(prop("q")), atomP(prop("r"))), [], false), term(atomP(prop("s")), [], false)];
	MaybeSequents output = sequents([term(atomP(prop("p")), [], false), term(atomP(prop("q")), [], false), term(atomP(prop("s")), [], false)], [term(atomP(prop("p")), [], false), term(atomP(prop("r")), [], false), term(atomP(prop("s")), [], false)]);
	
	return applyAnd(input, 1) == output;
}
// [(p&q)^[] (r&s)^[]] (apply to first term)
test bool applyAnd_test_9() {
	CloGSequent input = [term(and(atomP(prop("p")), atomP(prop("q"))), [], false), term(and(atomP(prop("r")), atomP(prop("s"))), [], false)];
	MaybeSequents output = sequents([term(atomP(prop("p")), [], false), term(and(atomP(prop("r")), atomP(prop("s"))), [], false)], [term(atomP(prop("q")), [], false), term(and(atomP(prop("r")), atomP(prop("s"))), [], false)]);
	
	return applyAnd(input, 0) == output;
}
// [(p&q)^[] (r&s)^[]] (apply to second term)
test bool applyAnd_test_10() {
	CloGSequent input = [term(and(atomP(prop("p")), atomP(prop("q"))), [], false), term(and(atomP(prop("r")), atomP(prop("s"))), [], false)];
	MaybeSequents output = sequents([term(and(atomP(prop("p")), atomP(prop("q"))), [], false), term(atomP(prop("r")), [], false)], [term(and(atomP(prop("p")), atomP(prop("q"))), [], false), term(atomP(prop("s")), [], false)]);
	
	return applyAnd(input, 1) == output;
}
// [(p&q)^[] (r&s)^[]] (apply to both terms)
test bool applyAnd_test_11() {
	CloGSequent input = [term(and(atomP(prop("p")), atomP(prop("q"))), [], false), term(and(atomP(prop("r")), atomP(prop("s"))), [], false)];
	MaybeSequents output1 = sequents([term(atomP(prop("p")), [], false), term(atomP(prop("r")), [], false)], [term(atomP(prop("p")), [], false), term(atomP(prop("s")), [], false)]);
	MaybeSequents output2 = sequents([term(atomP(prop("q")), [], false), term(atomP(prop("r")), [], false)], [term(atomP(prop("q")), [], false), term(atomP(prop("s")), [], false)]);
	
	initResult = applyAnd(input, 0);
	return applyAnd(initResult.left, 1) == output1 && applyAnd(initResult.right, 1) == output2;
}
// [<a>(p&q)^[]]
test bool applyAnd_test_12() {
	CloGSequent input = [term(\mod(atomG(agame("a")), and(atomP(prop("p")), atomP(prop("q")))), [], false)];
	MaybeSequents output = noSeqs();
	
	return applyAnd(input, 0) == output;
}


// Apply Choice

// p^[]
test bool applyChoice_test_1() {
	CloGSequent input = [term(atomP(prop("p")), [], false)];
	MaybeSequent output = noSeq();
	
	return applyChoice(input, 0) == output;
}
// <a>p^[]
test bool applyChoice_test_2() {
	CloGSequent input = [term(\mod(atomG(agame("a")), atomP(prop("p"))), [], false)];
	MaybeSequent output = noSeq();
	
	return applyChoice(input, 0) == output;
}
// <a||b>p^[]
test bool applyChoice_test_3() {
	CloGSequent input = [term(\mod(choice(atomG(agame("a")), atomG(agame("b"))), atomP(prop("p"))), [], false)];
	MaybeSequent output = sequent([term(or(\mod(atomG(agame("a")), atomP(prop("p"))), \mod(atomG(agame("b")), atomP(prop("p")))), [], false)]);
	
	return applyChoice(input, 0) == output;
}
// <a||b>~p^[]
test bool applyChoice_test_4() {
	CloGSequent input = [term(\mod(choice(atomG(agame("a")), atomG(agame("b"))), neg(atomP(prop("p")))), [], false)];
	MaybeSequent output = sequent([term(or(\mod(atomG(agame("a")), neg(atomP(prop("p")))), \mod(atomG(agame("b")), neg(atomP(prop("p"))))), [], false)]);
	
	return applyChoice(input, 0) == output;
}
// <a||a^d>p^[]
test bool applyChoice_test_5() {
	CloGSequent input = [term(\mod(choice(atomG(agame("a")), dual(atomG(agame("a")))), atomP(prop("p"))), [], false)];
	MaybeSequent output = sequent([term(or(\mod(atomG(agame("a")), atomP(prop("p"))), \mod(dual(atomG(agame("a"))), atomP(prop("p")))), [], false)]);
	
	return applyChoice(input, 0) == output;
}
// <a||b>p^x
test bool applyChoice_test_6() {
	CloGSequent input = [term(\mod(choice(atomG(agame("a")), atomG(agame("b"))), atomP(prop("p"))), [name("x")], false)];
	MaybeSequent output = sequent([term(or(\mod(atomG(agame("a")), atomP(prop("p"))), \mod(atomG(agame("b")), atomP(prop("p")))), [name("x")], false)]);
	
	return applyChoice(input, 0) == output;
}
// [<a||b>p^[] q^[]] (apply to first term)
test bool applyChoice_test_7() {	
	CloGSequent input = [term(\mod(choice(atomG(agame("a")), atomG(agame("b"))), atomP(prop("p"))), [], false), term(atomP(prop("q")), [], false)];
	MaybeSequent output = sequent([term(or(\mod(atomG(agame("a")), atomP(prop("p"))), \mod(atomG(agame("b")), atomP(prop("p")))), [], false), term(atomP(prop("q")), [], false)]);
	
	return applyChoice(input, 0) == output;
}
// [<a||b>p^[] q^[]] (apply to second term)
test bool applyChoice_test_8() {	
	CloGSequent input = [term(\mod(choice(atomG(agame("a")), atomG(agame("b"))), atomP(prop("p"))), [], false), term(atomP(prop("q")), [], false)];
	MaybeSequent output = noSeq();
	
	return applyChoice(input, 1) == output;
}
// [p^[] <a||b>q^[]] (apply to second term)
test bool applyChoice_test_9() {
	CloGSequent input = [term(atomP(prop("p")), [], false), term(\mod(choice(atomG(agame("a")), atomG(agame("b"))), atomP(prop("q"))), [], false)];
	MaybeSequent output = sequent([term(atomP(prop("p")), [], false), term(or(\mod(atomG(agame("a")), atomP(prop("q"))), \mod(atomG(agame("b")), atomP(prop("q")))), [], false)]);
	
	return applyChoice(input, 1) == output;
}
// [p^[] <a||b>q^[] r^[]] (apply to second term)
test bool applyChoice_test_10() {
	CloGSequent input = [term(atomP(prop("p")), [], false), term(\mod(choice(atomG(agame("a")), atomG(agame("b"))), atomP(prop("q"))), [], false), term(atomP(prop("r")), [], false)];
	MaybeSequent output = sequent([term(atomP(prop("p")), [], false), term(or(\mod(atomG(agame("a")), atomP(prop("q"))), \mod(atomG(agame("b")), atomP(prop("q")))), [], false), term(atomP(prop("r")), [], false)]);
	
	return applyChoice(input, 1) == output;
}
// [(<a||b>p^[] <c||d>q^[]] (apply to first term)
test bool applyChoice_test_11() {
	CloGSequent input = [term(\mod(choice(atomG(agame("a")), atomG(agame("b"))), atomP(prop("p"))), [], false), term(\mod(choice(atomG(agame("c")), atomG(agame("d"))), atomP(prop("q"))), [], false)];
	MaybeSequent output = sequent([term(or(\mod(atomG(agame("a")), atomP(prop("p"))), \mod(atomG(agame("b")), atomP(prop("p")))), [], false), term(\mod(choice(atomG(agame("c")), atomG(agame("d"))), atomP(prop("q"))), [], false)]);
	
	return applyChoice(input, 0) == output;
}
// [(<a||b>p^[] <c||d>q^[]] (apply to second term)
test bool applyChoice_test_12() {
	CloGSequent input = [term(\mod(choice(atomG(agame("a")), atomG(agame("b"))), atomP(prop("p"))), [], false), term(\mod(choice(atomG(agame("c")), atomG(agame("d"))), atomP(prop("q"))), [], false)];
	MaybeSequent output = sequent([term(\mod(choice(atomG(agame("a")), atomG(agame("b"))), atomP(prop("p"))), [], false), term(or(\mod(atomG(agame("c")), atomP(prop("q"))), \mod(atomG(agame("d")), atomP(prop("q")))), [], false)]);
	
	return applyChoice(input, 1) == output;
}

// [(<a||b>p^[] <c||d>q^[]] (apply to both terms)
test bool applyChoice_test_13() {
	CloGSequent input = [term(\mod(choice(atomG(agame("a")), atomG(agame("b"))), atomP(prop("p"))), [], false), term(\mod(choice(atomG(agame("c")), atomG(agame("d"))), atomP(prop("q"))), [], false)];
	MaybeSequent output = sequent([term(or(\mod(atomG(agame("a")), atomP(prop("p"))), \mod(atomG(agame("b")), atomP(prop("p")))), [], false), term(or(\mod(atomG(agame("c")), atomP(prop("q"))), \mod(atomG(agame("d")), atomP(prop("q")))), [], false)]);
	
	return applyChoice(applyChoice(input, 0).seq, 1) == output;
}
// <a&&b>p^[]
test bool applyChoice_test_14() {
	CloGSequent input = [term(\mod(dChoice(atomG(agame("a")), atomG(agame("b"))), atomP(prop("p"))), [], false)];
	MaybeSequent output = noSeq();
	
	return applyChoice(input, 0) == output;
}
// <(a||b)*>p^[]
test bool applyChoice_test_15() {
	CloGSequent input = [term(\mod(iter(choice(atomG(agame("a")), atomG(agame("b")))), atomP(prop("p"))), [], false)];
	MaybeSequent output = noSeq();
	
	return applyChoice(input, 0) == output;
}


// Apply dChoice

// p^[]
test bool applyDChoice_test_1() {
	CloGSequent input = [term(atomP(prop("p")), [], false)];
	MaybeSequent output = noSeq();
	
	return applyDChoice(input, 0) == output;
}
// <a>p^[]
test bool applyDChoice_test_2() {
	CloGSequent input = [term(\mod(atomG(agame("a")), atomP(prop("p"))), [], false)];
	MaybeSequent output = noSeq();
	
	return applyDChoice(input, 0) == output;
}
// <a&&b>p^[]
test bool applyDChoice_test_3() {
	CloGSequent input = [term(\mod(dChoice(atomG(agame("a")), atomG(agame("b"))), atomP(prop("p"))), [], false)];
	MaybeSequent output = sequent([term(and(\mod(atomG(agame("a")), atomP(prop("p"))), \mod(atomG(agame("b")), atomP(prop("p")))), [], false)]);
	
	return applyDChoice(input, 0) == output;
}
// <a&&b>~p^[]
test bool applyDChoice_test_4() {
	CloGSequent input = [term(\mod(dChoice(atomG(agame("a")), atomG(agame("b"))), neg(atomP(prop("p")))), [], false)];
	MaybeSequent output = sequent([term(and(\mod(atomG(agame("a")), neg(atomP(prop("p")))), \mod(atomG(agame("b")), neg(atomP(prop("p"))))), [], false)]);
	
	return applyDChoice(input, 0) == output;
}
// <a&&a^d>p^[]
test bool applyDChoice_test_5() {
	CloGSequent input = [term(\mod(dChoice(atomG(agame("a")), dual(atomG(agame("a")))), atomP(prop("p"))), [], false)];
	MaybeSequent output = sequent([term(and(\mod(atomG(agame("a")), atomP(prop("p"))), \mod(dual(atomG(agame("a"))), atomP(prop("p")))), [], false)]);
	
	return applyDChoice(input, 0) == output;
}
// <a&&b>p^x
test bool applyDChoice_test_6() {
	CloGSequent input = [term(\mod(dChoice(atomG(agame("a")), atomG(agame("b"))), atomP(prop("p"))), [name("x")], false)];
	MaybeSequent output = sequent([term(and(\mod(atomG(agame("a")), atomP(prop("p"))), \mod(atomG(agame("b")), atomP(prop("p")))), [name("x")], false)]);
	
	return applyDChoice(input, 0) == output;
}
// [<a&&b>p^[] q^[]] (apply to first term)
test bool applyDChoice_test_7() {	
	CloGSequent input = [term(\mod(dChoice(atomG(agame("a")), atomG(agame("b"))), atomP(prop("p"))), [], false), term(atomP(prop("q")), [], false)];
	MaybeSequent output = sequent([term(and(\mod(atomG(agame("a")), atomP(prop("p"))), \mod(atomG(agame("b")), atomP(prop("p")))), [], false), term(atomP(prop("q")), [], false)]);
	
	return applyDChoice(input, 0) == output;
}
// [<a&&b>p^[] q^[]] (apply to second term)
test bool applyDChoice_test_8() {	
	CloGSequent input = [term(\mod(dChoice(atomG(agame("a")), atomG(agame("b"))), atomP(prop("p"))), [], false), term(atomP(prop("q")), [], false)];
	MaybeSequent output = noSeq();
	
	return applyDChoice(input, 1) == output;
}
// [p^[] <a&&b>q^[]] (apply to second term)
test bool applyDChoice_test_9() {
	CloGSequent input = [term(atomP(prop("p")), [], false), term(\mod(dChoice(atomG(agame("a")), atomG(agame("b"))), atomP(prop("q"))), [], false)];
	MaybeSequent output = sequent([term(atomP(prop("p")), [], false), term(and(\mod(atomG(agame("a")), atomP(prop("q"))), \mod(atomG(agame("b")), atomP(prop("q")))), [], false)]);
	
	return applyDChoice(input, 1) == output;
}
// [p^[] <a&&b>q^[] r^[]] (apply to second term)
test bool applyDChoice_test_10() {
	CloGSequent input = [term(atomP(prop("p")), [], false), term(\mod(dChoice(atomG(agame("a")), atomG(agame("b"))), atomP(prop("q"))), [], false), term(atomP(prop("r")), [], false)];
	MaybeSequent output = sequent([term(atomP(prop("p")), [], false), term(and(\mod(atomG(agame("a")), atomP(prop("q"))), \mod(atomG(agame("b")), atomP(prop("q")))), [], false), term(atomP(prop("r")), [], false)]);
	
	return applyDChoice(input, 1) == output;
}
// [(<a&&b>p^[] <c&&d>q^[]] (apply to first term)
test bool applyDChoice_test_11() {
	CloGSequent input = [term(\mod(dChoice(atomG(agame("a")), atomG(agame("b"))), atomP(prop("p"))), [], false), term(\mod(dChoice(atomG(agame("c")), atomG(agame("d"))), atomP(prop("q"))), [], false)];
	MaybeSequent output = sequent([term(and(\mod(atomG(agame("a")), atomP(prop("p"))), \mod(atomG(agame("b")), atomP(prop("p")))), [], false), term(\mod(dChoice(atomG(agame("c")), atomG(agame("d"))), atomP(prop("q"))), [], false)]);
	
	return applyDChoice(input, 0) == output;
}
// [(<a&&b>p^[] <c&&d>q^[]] (apply to second term)
test bool applyDChoice_test_12() {
	CloGSequent input = [term(\mod(dChoice(atomG(agame("a")), atomG(agame("b"))), atomP(prop("p"))), [], false), term(\mod(dChoice(atomG(agame("c")), atomG(agame("d"))), atomP(prop("q"))), [], false)];
	MaybeSequent output = sequent([term(\mod(dChoice(atomG(agame("a")), atomG(agame("b"))), atomP(prop("p"))), [], false), term(and(\mod(atomG(agame("c")), atomP(prop("q"))), \mod(atomG(agame("d")), atomP(prop("q")))), [], false)]);
	
	return applyDChoice(input, 1) == output;
}
// [(<a&&b>p^[] <c&&d>q^[]] (apply to both terms)
test bool applyDChoice_test_13() {
	CloGSequent input = [term(\mod(dChoice(atomG(agame("a")), atomG(agame("b"))), atomP(prop("p"))), [], false), term(\mod(dChoice(atomG(agame("c")), atomG(agame("d"))), atomP(prop("q"))), [], false)];
	MaybeSequent output = sequent([term(and(\mod(atomG(agame("a")), atomP(prop("p"))), \mod(atomG(agame("b")), atomP(prop("p")))), [], false), term(and(\mod(atomG(agame("c")), atomP(prop("q"))), \mod(atomG(agame("d")), atomP(prop("q")))), [], false)]);
	
	return applyDChoice(applyDChoice(input, 0).seq, 1) == output;
}
// <a||b>p^[]
test bool applyDChoice_test_14() {
	CloGSequent input = [term(\mod(choice(atomG(agame("a")), atomG(agame("b"))), atomP(prop("p"))), [], false)];
	MaybeSequent output = noSeq();
	
	return applyDChoice(input, 0) == output;
}
// <(a&&b)*>p^[]
test bool applyDChoice_test_15() {
	CloGSequent input = [term(\mod(iter(dChoice(atomG(agame("a")), atomG(agame("b")))), atomP(prop("p"))), [], false)];
	MaybeSequent output = noSeq();
	
	return applyDChoice(input, 0) == output;
}

// Apply concat

// p^[]
test bool applyConcat_test_1() {
	CloGSequent input = [term(atomP(prop("p")), [], false)];
	MaybeSequent output = noSeq();
	
	return applyConcat(input, 0) == output;
}
// <a>p^[]
test bool applyConcat_test_2() {
	CloGSequent input = [term(\mod(atomG(agame("a")), atomP(prop("p"))), [], false)];
	MaybeSequent output = noSeq();
	
	return applyConcat(input, 0) == output;
}
// <a;b>p^[]
test bool applyConcat_test_3() {
	CloGSequent input = [term(\mod(concat(atomG(agame("a")), atomG(agame("b"))), atomP(prop("p"))), [], false)];
	MaybeSequent output = sequent([term(\mod(atomG(agame("a")), \mod(atomG(agame("b")), atomP(prop("p")))), [], false)]);
	
	return applyConcat(input, 0) == output;
}
// <a;b>~p^[]
test bool applyConcat_test_4() {
	CloGSequent input = [term(\mod(concat(atomG(agame("a")), atomG(agame("b"))), neg(atomP(prop("p")))), [], false)];
	MaybeSequent output = sequent([term(\mod(atomG(agame("a")), \mod(atomG(agame("b")), neg(atomP(prop("p"))))), [], false)]);
	
	return applyConcat(input, 0) == output;
}
// <a;a^d>p^[]
test bool applyConcat_test_5() {
	CloGSequent input = [term(\mod(concat(atomG(agame("a")), dual(atomG(agame("a")))), atomP(prop("p"))), [], false)];
	MaybeSequent output = sequent([term(\mod(atomG(agame("a")), \mod(dual(atomG(agame("a"))), atomP(prop("p")))), [], false)]);
	
	return applyConcat(input, 0) == output;
}
// <a;b>p^x
test bool applyConcat_test_6() {
	CloGSequent input = [term(\mod(concat(atomG(agame("a")), atomG(agame("b"))), atomP(prop("p"))), [name("x")], false)];
	MaybeSequent output = sequent([term(\mod(atomG(agame("a")), \mod(atomG(agame("b")), atomP(prop("p")))), [name("x")], false)]);
	
	return applyConcat(input, 0) == output;
}
// [<a;b>p^[] q^[]] (apply to first term)
test bool applyConcat_test_7() {
	CloGSequent input = [term(\mod(concat(atomG(agame("a")), atomG(agame("b"))), atomP(prop("p"))), [], false), term(atomP(prop("q")), [], false)];
	MaybeSequent output = sequent([term(\mod(atomG(agame("a")), \mod(atomG(agame("b")), atomP(prop("p")))), [], false), term(atomP(prop("q")), [], false)]);
	
	return applyConcat(input, 0) == output;
}
// [<a;b>p^[] q^[]] (apply to second term)
test bool applyConcat_test_8() {
	CloGSequent input = [term(\mod(concat(atomG(agame("a")), atomG(agame("b"))), atomP(prop("p"))), [], false), term(atomP(prop("q")), [], false)];
	MaybeSequent output = noSeq();
	
	return applyConcat(input, 1) == output;
}
// [p^[] <a;b>q^[]] (apply to second term)
test bool applyConcat_test_9() {
	CloGSequent input = [term(atomP(prop("p")), [], false), term(\mod(concat(atomG(agame("a")), atomG(agame("b"))), atomP(prop("q"))), [], false)];
	MaybeSequent output = sequent([term(atomP(prop("p")), [], false), term(\mod(atomG(agame("a")), \mod(atomG(agame("b")), atomP(prop("q")))), [], false)]);
	
	return applyConcat(input, 1) == output;
}
// [p^[] <a;b>q^[] r^[]] (apply to second term)
test bool applyConcat_test_10() {
	CloGSequent input = [term(atomP(prop("p")), [], false), term(\mod(concat(atomG(agame("a")), atomG(agame("b"))), atomP(prop("q"))), [], false), term(atomP(prop("r")), [], false)];
	MaybeSequent output = sequent([term(atomP(prop("p")), [], false), term(\mod(atomG(agame("a")), \mod(atomG(agame("b")), atomP(prop("q")))), [], false), term(atomP(prop("r")), [], false)]);
	
	return applyConcat(input, 1) == output;
}
// [<a;b>p^[] <c;d>q^[]] (apply to first term)
test bool applyConcat_test_11() {
	CloGSequent input = [term(\mod(concat(atomG(agame("a")), atomG(agame("b"))), atomP(prop("p"))), [], false), term(\mod(concat(atomG(agame("c")), atomG(agame("d"))), atomP(prop("q"))), [], false)];
	MaybeSequent output = sequent([term(\mod(atomG(agame("a")), \mod(atomG(agame("b")), atomP(prop("p")))), [], false), term(\mod(concat(atomG(agame("c")), atomG(agame("d"))), atomP(prop("q"))), [], false)]);
	
	return applyConcat(input, 0) == output;
}
// [<a;b>p^[] <c;d>q^[]] (apply to second term)
test bool applyConcat_test_12() {
	CloGSequent input = [term(\mod(concat(atomG(agame("a")), atomG(agame("b"))), atomP(prop("p"))), [], false), term(\mod(concat(atomG(agame("c")), atomG(agame("d"))), atomP(prop("q"))), [], false)];
	MaybeSequent output = sequent([term(\mod(concat(atomG(agame("a")), atomG(agame("b"))), atomP(prop("p"))), [], false), term(\mod(atomG(agame("c")), \mod(atomG(agame("d")), atomP(prop("q")))), [], false)]);
	
	return applyConcat(input, 1) == output;
}
// [<a;b>p^[] <c;d>q^[]] (apply to both terms)
test bool applyConcat_test_13() {
	CloGSequent input = [term(\mod(concat(atomG(agame("a")), atomG(agame("b"))), atomP(prop("p"))), [], false), term(\mod(concat(atomG(agame("c")), atomG(agame("d"))), atomP(prop("q"))), [], false)];
	MaybeSequent output = sequent([term(\mod(atomG(agame("a")), \mod(atomG(agame("b")), atomP(prop("p")))), [], false), term(\mod(atomG(agame("c")), \mod(atomG(agame("d")), atomP(prop("q")))), [], false)]);
	
	return applyConcat(applyConcat(input, 0).seq, 1) == output;
}
// <a||b>p^[]
test bool applyConcat_test_14() {
	CloGSequent input = [term(\mod(choice(atomG(agame("a")), atomG(agame("b"))), atomP(prop("p"))), [], false)];
	MaybeSequent output = noSeq();
	
	return applyConcat(input, 0) == output;
}
// <(a;b)*>p^[]
test bool applyConcat_test_15() {
	CloGSequent input = [term(\mod(iter(concat(atomG(agame("a")), atomG(agame("b")))), atomP(prop("p"))), [], false)];
	MaybeSequent output = noSeq();
	
	return applyConcat(input, 0) == output;
}


// Apply test

// p^[]
test bool applyTest_test_1() {
	CloGSequent input = [term(atomP(prop("p")), [], false)];
	MaybeSequent output = noSeq();
	
	return applyTest(input, 0) == output;
}
// <a>p^[]
test bool applyTest_test_2() {
	CloGSequent input = [term(\mod(atomG(agame("a")), atomP(prop("p"))), [], false)];
	MaybeSequent output = noSeq();
	
	return applyTest(input, 0) == output;
}
// <p?>q^[]
test bool applyTest_test_3() {
	CloGSequent input = [term(\mod(\test(atomP(prop("p"))), atomP(prop("q"))), [], false)];
	MaybeSequent output = sequent([term(and(atomP(prop("p")), atomP(prop("q"))), [], false)]);
	
	return applyTest(input, 0) == output;
}
// <p?>~q^[]
test bool applyTest_test_4() {
	CloGSequent input = [term(\mod(\test(atomP(prop("p"))), neg(atomP(prop("q")))), [], false)];
	MaybeSequent output = sequent([term(and(atomP(prop("p")), neg(atomP(prop("q")))), [], false)]);
	
	return applyTest(input, 0) == output;
}
// <~p?>q^[]
test bool applyTest_test_5() {
	CloGSequent input = [term(\mod(\test(neg(atomP(prop("p")))), atomP(prop("q"))), [], false)];
	MaybeSequent output = sequent([term(and(neg(atomP(prop("p"))), atomP(prop("q"))), [], false)]);
	
	return applyTest(input, 0) == output;
}
// <p?>q^x
test bool applyTest_test_6() {
	CloGSequent input = [term(\mod(\test(atomP(prop("p"))), atomP(prop("q"))), [name("x")], false)];
	MaybeSequent output = sequent([term(and(atomP(prop("p")), atomP(prop("q"))), [name("x")], false)]);
	
	return applyTest(input, 0) == output;
}
// [<p?>q^[] r^[]] (apply to first term)
test bool applyTest_test_7() {
	CloGSequent input = [term(\mod(\test(atomP(prop("p"))), atomP(prop("q"))), [], false), term(atomP(prop("r")), [], false)];
	MaybeSequent output = sequent([term(and(atomP(prop("p")), atomP(prop("q"))), [], false), term(atomP(prop("r")), [], false)]);
	
	return applyTest(input, 0) == output;
}
// [<p?>q^[] r^[]] (apply to second term)
test bool applyTest_test_8() {
	CloGSequent input = [term(\mod(\test(atomP(prop("p"))), atomP(prop("q"))), [], false), term(atomP(prop("r")), [], false)];
	MaybeSequent output = noSeq();
	
	return applyTest(input, 1) == output;
}
// [p^[] <q?>r^[]] (apply to second term)
test bool applyTest_test_9() {
	CloGSequent input = [term(atomP(prop("p")), [], false), term(\mod(\test(atomP(prop("q"))), atomP(prop("r"))), [], false)];
	MaybeSequent output = sequent([term(atomP(prop("p")), [], false), term(and(atomP(prop("q")), atomP(prop("r"))), [], false)]);
	
	return applyTest(input, 1) == output;
}
// [p^[] <q?>r^[] s^[]] (apply to second term)
test bool applyTest_test_10() {
	CloGSequent input = [term(atomP(prop("p")), [], false), term(\mod(\test(atomP(prop("q"))), atomP(prop("r"))), [], false), term(atomP(prop("s")), [], false)];
	MaybeSequent output = sequent([term(atomP(prop("p")), [], false), term(and(atomP(prop("q")), atomP(prop("r"))), [], false), term(atomP(prop("s")), [], false)]);
	
	return applyTest(input, 1) == output;
}
// [<p?>q^[] <r?>s^[]] (apply to first term)
test bool applyTest_test_11() {
	CloGSequent input = [term(\mod(\test(atomP(prop("p"))), atomP(prop("q"))), [], false), term(\mod(\test(atomP(prop("r"))), atomP(prop("s"))), [], false)];
	MaybeSequent output = sequent([term(and(atomP(prop("p")), atomP(prop("q"))), [], false), term(\mod(\test(atomP(prop("r"))), atomP(prop("s"))), [], false)]);
	
	return applyTest(input, 0) == output;
}
// [<p?>q^[] <r?>s^[]] (apply to second term)
test bool applyTest_test_12() {
	CloGSequent input = [term(\mod(\test(atomP(prop("p"))), atomP(prop("q"))), [], false), term(\mod(\test(atomP(prop("r"))), atomP(prop("s"))), [], false)];
	MaybeSequent output = sequent([term(\mod(\test(atomP(prop("p"))), atomP(prop("q"))), [], false), term(and(atomP(prop("r")), atomP(prop("s"))), [], false)]);
	
	return applyTest(input, 1) == output;
}
// [<p?>q^[] <r?>s^[]] (apply to both terms)
test bool applyTest_test_13() {
	CloGSequent input = [term(\mod(\test(atomP(prop("p"))), atomP(prop("q"))), [], false), term(\mod(\test(atomP(prop("r"))), atomP(prop("s"))), [], false)];
	MaybeSequent output = sequent([term(and(atomP(prop("p")), atomP(prop("q"))), [], false), term(and(atomP(prop("r")), atomP(prop("s"))), [], false)]);
	
	return applyTest(applyTest(input, 0).seq, 1) == output;
}
// <a||b>p^[]
test bool applyTest_test_14() {
	CloGSequent input = [term(\mod(choice(atomG(agame("a")), atomG(agame("b"))), atomP(prop("p"))), [], false)];
	MaybeSequent output = noSeq();
	
	return applyTest(input, 0) == output;
}
// <(p?)*>q^[]
test bool applyTest_test_15() {
	CloGSequent input = [term(\mod(iter(\test(atomP(prop("p")))), atomP(prop("q"))), [], false)];
	MaybeSequent output = noSeq();
	
	return applyTest(input, 0) == output;
}


// Apply dTest

// p^[]
test bool applyDTest_test_1() {
	CloGSequent input = [term(atomP(prop("p")), [], false)];
	MaybeSequent output = noSeq();
	
	return applyDTest(input, 0) == output;
}
// <a>p^[]
test bool applyDTest_test_2() {
	CloGSequent input = [term(\mod(atomG(agame("a")), atomP(prop("p"))), [], false)];
	MaybeSequent output = noSeq();
	
	return applyDTest(input, 0) == output;
}
// <p!>q^[]
test bool applyDTest_test_3() {
	CloGSequent input = [term(\mod(dTest(atomP(prop("p"))), atomP(prop("q"))), [], false)];
	MaybeSequent output = sequent([term(\or(atomP(prop("p")), atomP(prop("q"))), [], false)]);
	
	return applyDTest(input, 0) == output;
}
// <p!>~q^[]
test bool applyDTest_test_4() {
	CloGSequent input = [term(\mod(dTest(atomP(prop("p"))), neg(atomP(prop("q")))), [], false)];
	MaybeSequent output = sequent([term(\or(atomP(prop("p")), neg(atomP(prop("q")))), [], false)]);
	
	return applyDTest(input, 0) == output;
}
// <~p!>q^[]
test bool applyDTest_test_5() {
	CloGSequent input = [term(\mod(dTest(neg(atomP(prop("p")))), atomP(prop("q"))), [], false)];
	MaybeSequent output = sequent([term(or(neg(atomP(prop("p"))), atomP(prop("q"))), [], false)]);
	
	return applyDTest(input, 0) == output;
}
// <p!>q^x
test bool applyDTest_test_6() {
	CloGSequent input = [term(\mod(dTest(atomP(prop("p"))), atomP(prop("q"))), [name("x")], false)];
	MaybeSequent output = sequent([term(or(atomP(prop("p")), atomP(prop("q"))), [name("x")], false)]);
	
	return applyDTest(input, 0) == output;
}
// [<p!>q^[] r^[]] (apply to first term)
test bool applyDTest_test_7() {
	CloGSequent input = [term(\mod(dTest(atomP(prop("p"))), atomP(prop("q"))), [], false), term(atomP(prop("r")), [], false)];
	MaybeSequent output = sequent([term(or(atomP(prop("p")), atomP(prop("q"))), [], false), term(atomP(prop("r")), [], false)]);
	
	return applyDTest(input, 0) == output;
}
// [<p!>q^[] r^[]] (apply to second term)
test bool applyDTest_test_8() {
	CloGSequent input = [term(\mod(dTest(atomP(prop("p"))), atomP(prop("q"))), [], false), term(atomP(prop("r")), [], false)];
	MaybeSequent output = noSeq();
	
	return applyDTest(input, 1) == output;
}
// [p^[] <q!>r^[]] (apply to second term)
test bool applyDTest_test_9() {
	CloGSequent input = [term(atomP(prop("p")), [], false), term(\mod(dTest(atomP(prop("q"))), atomP(prop("r"))), [], false)];
	MaybeSequent output = sequent([term(atomP(prop("p")), [], false), term(\or(atomP(prop("q")), atomP(prop("r"))), [], false)]);
	
	return applyDTest(input, 1) == output;
}
// [p^[] <q!>r^[] s^[]] (apply to second term)
test bool applyDTest_test_10() {
	CloGSequent input = [term(atomP(prop("p")), [], false), term(\mod(dTest(atomP(prop("q"))), atomP(prop("r"))), [], false), term(atomP(prop("s")), [], false)];
	MaybeSequent output = sequent([term(atomP(prop("p")), [], false), term(\or(atomP(prop("q")), atomP(prop("r"))), [], false), term(atomP(prop("s")), [], false)]);
	
	return applyDTest(input, 1) == output;
}
// [<p!>q^[] <r!>s^[]] (apply to first term)
test bool applyDTest_test_11() {
	CloGSequent input = [term(\mod(dTest(atomP(prop("p"))), atomP(prop("q"))), [], false), term(\mod(dTest(atomP(prop("r"))), atomP(prop("s"))), [], false)];
	MaybeSequent output = sequent([term(or(atomP(prop("p")), atomP(prop("q"))), [], false), term(\mod(dTest(atomP(prop("r"))), atomP(prop("s"))), [], false)]);
	
	return applyDTest(input, 0) == output;
}
// [<p!>q^[] <r!>s^[]] (apply to second term)
test bool applyDTest_test_12() {
	CloGSequent input = [term(\mod(dTest(atomP(prop("p"))), atomP(prop("q"))), [], false), term(\mod(dTest(atomP(prop("r"))), atomP(prop("s"))), [], false)];
	MaybeSequent output = sequent([term(\mod(dTest(atomP(prop("p"))), atomP(prop("q"))), [], false), term(or(atomP(prop("r")), atomP(prop("s"))), [], false)]);
	
	return applyDTest(input, 1) == output;
}
// [<p!>q^[] <r!>s^[]] (apply to both terms)
test bool applyDTest_test_13() {
	CloGSequent input = [term(\mod(dTest(atomP(prop("p"))), atomP(prop("q"))), [], false), term(\mod(dTest(atomP(prop("r"))), atomP(prop("s"))), [], false)];
	MaybeSequent output = sequent([term(or(atomP(prop("p")), atomP(prop("q"))), [], false), term(or(atomP(prop("r")), atomP(prop("s"))), [], false)]);
	
	return applyDTest(applyDTest(input, 0).seq, 1) == output;
}
// <a||b>p^[]
test bool applyDTest_test_14() {
	CloGSequent input = [term(\mod(choice(atomG(agame("a")), atomG(agame("b"))), atomP(prop("p"))), [], false)];
	MaybeSequent output = noSeq();
	
	return applyDTest(input, 0) == output;
}
// <(p!)*>q^[]
test bool applyDTest_test_15() {
	CloGSequent input = [term(\mod(iter(dTest(atomP(prop("p")))), atomP(prop("q"))), [], false)];
	MaybeSequent output = noSeq();
	
	return applyDTest(input, 0) == output;
}


// Apply iter

// p^[] (empty closure map)
test bool applyIter_test_1() {
	CloGSequent input = [term(atomP(prop("p")), [], false)];
	MaybeSequent output = noSeq();
	
	return applyIter(input, 0, ()) == output;
}
// <a>p^[] (empty closure map)
test bool applyIter_test_2() {
	CloGSequent input = [term(\mod(atomG(agame("a")), atomP(prop("p"))), [], false)];
	MaybeSequent output = noSeq();
	
	return applyIter(input, 0, ()) == output;
}
// <a*>p^[] (empty closure map)
test bool applyIter_test_3() {
	CloGSequent input = [term(\mod(iter(atomG(agame("a"))), atomP(prop("p"))), [], false)];
	MaybeSequent output = sequent([term(or(atomP(prop("p")), \mod(atomG(agame("a")), \mod(iter(atomG(agame("a"))), atomP(prop("p"))))), [], false)]);
	
	return applyIter(input, 0, ()) == output;
}
// <a*>p^[] (closure map contains fp formula for x: <a*>p)
test bool applyIter_test_4() {
	CloGSequent input = [term(\mod(iter(atomG(agame("a"))), atomP(prop("p"))), [], false)];
	CloSeqs cloSeqs = (name("x"): <[term(\mod(iter(atomG(agame("a"))), atomP(prop("p"))), [], false)], 0>);
	MaybeSequent output = sequent([term(or(atomP(prop("p")), \mod(atomG(agame("a")), \mod(iter(atomG(agame("a"))), atomP(prop("p"))))), [], false)]);
	
	return applyIter(input, 0, cloSeqs) == output;
}
// <a*>~p^[] (empty closure map)
test bool applyIter_test_5() {
	CloGSequent input = [term(\mod(iter(atomG(agame("a"))), neg(atomP(prop("p")))), [], false)];
	MaybeSequent output = sequent([term(or(neg(atomP(prop("p"))), \mod(atomG(agame("a")), \mod(iter(atomG(agame("a"))), neg(atomP(prop("p")))))), [], false)]);
	
	return applyIter(input, 0, ()) == output;
}
// <(a^d)*>p^[] (empty closure map)
test bool applyIter_test_6() {
	CloGSequent input = [term(\mod(iter(dual(atomG(agame("a")))), atomP(prop("p"))), [], false)];
	MaybeSequent output = sequent([term(or(atomP(prop("p")), \mod(dual(atomG(agame("a"))), \mod(iter(dual(atomG(agame("a")))), atomP(prop("p"))))), [], false)]);
	
	return applyIter(input, 0, ()) == output;
}
// <a*>p^x (closure map contains fp formula for x: <a*>p == <a*>p)
test bool applyIter_test_7() {
	CloGSequent input = [term(\mod(iter(atomG(agame("a"))), atomP(prop("p"))), [name("x")], false)];
	CloSeqs cloSeqs = (name("x"): <[term(\mod(iter(atomG(agame("a"))), atomP(prop("p"))), [], false)], 0>);
	MaybeSequent output = sequent([term(or(atomP(prop("p")), \mod(atomG(agame("a")), \mod(iter(atomG(agame("a"))), atomP(prop("p"))))), [name("x")], false)]);
	
	return applyIter(input, 0, cloSeqs) == output;
}
// <a*>p^x (closure map contains fp formula for x: <a**>p < <a*>p)
test bool applyIter_test_8() {
	CloGSequent input = [term(\mod(iter(atomG(agame("a"))), atomP(prop("p"))), [name("x")], false)];
	CloSeqs cloSeqs = (name("x"): <[term(\mod(iter(iter(atomG(agame("a")))), atomP(prop("p"))), [], false)], 0>);
	MaybeSequent output = sequent([term(or(atomP(prop("p")), \mod(atomG(agame("a")), \mod(iter(atomG(agame("a"))), atomP(prop("p"))))), [name("x")], false)]);
	
	return applyIter(input, 0, cloSeqs) == output;
}
// <a*>p^x (closure map contains fp formula for x: <b*>p !<= <a*>p)
test bool applyIter_test_9() {
	CloGSequent input = [term(\mod(iter(atomG(agame("a"))), atomP(prop("p"))), [name("x")], false)];
	CloSeqs cloSeqs = (name("x"): <[term(\mod(iter(atomG(agame("b"))), atomP(prop("p"))), [], false)], 0>);
	MaybeSequent output = noSeq();
	
	return applyIter(input, 0, cloSeqs) == output;
}
// <a*>p^y (closure map contains fp formula for x: <b*>p !<= <a*>p and y: <a**>p < <a*>p)
test bool applyIter_test_10() {
	CloGSequent input = [term(\mod(iter(atomG(agame("a"))), atomP(prop("p"))), [name("y")], false)];
	CloSeqs cloSeqs = (
		name("x"): <[term(\mod(iter(atomG(agame("b"))), atomP(prop("p"))), [], false)], 0>,
		name("y"): <[term(\mod(iter(iter(atomG(agame("a")))), atomP(prop("p"))), [], false)], 0>
	);
	MaybeSequent output = sequent([term(or(atomP(prop("p")), \mod(atomG(agame("a")), \mod(iter(atomG(agame("a"))), atomP(prop("p"))))), [name("y")], false)]);
	
	return applyIter(input, 0, cloSeqs) == output;
}
// <a*>p^x (closure map contains fp formula for x: <a*>p = <a*>p and y: <b*>p !<= <a*>p)
test bool applyIter_test_11() {
	CloGSequent input = [term(\mod(iter(atomG(agame("a"))), atomP(prop("p"))), [name("x")], false)];
	CloSeqs cloSeqs = (
		name("x"): <[term(\mod(iter(atomG(agame("a"))), atomP(prop("p"))), [], false)], 0>,
		name("y"): <[term(\mod(iter(atomG(agame("b"))), atomP(prop("p"))), [], false)], 0>
	);
	MaybeSequent output = sequent([term(or(atomP(prop("p")), \mod(atomG(agame("a")), \mod(iter(atomG(agame("a"))), atomP(prop("p"))))), [name("x")], false)]);
	
	return applyIter(input, 0, cloSeqs) == output;
}
// <a*>p^{x, y} (closure map contains fp formula for x: <a*>p = <a*>p and y: <(a*;b)*>q < <a*>p)
test bool applyIter_test_12() {
	CloGSequent input = [term(\mod(iter(atomG(agame("a"))), atomP(prop("p"))), [name("x"), name("y")], false)];
	CloSeqs cloSeqs = (
		name("x"): <[term(\mod(iter(atomG(agame("a"))), atomP(prop("p"))), [], false)], 0>,
		name("y"): <[term(\mod(iter(concat(iter(atomG(agame("a"))), atomG(agame("b")))), atomP(prop("q"))), [name("x")], false)], 0>
	);
	MaybeSequent output = sequent([term(or(atomP(prop("p")), \mod(atomG(agame("a")), \mod(iter(atomG(agame("a"))), atomP(prop("p"))))), [name("x"), name("y")], false)]);
	
	return applyIter(input, 0, cloSeqs) == output;
}
// <a*>p^{x, y} (closure map contains fp formula for x: <a**>p < <a*>p and y: <b*>p !<= <a*>p)
test bool applyIter_test_13() {
	CloGSequent input = [term(\mod(iter(atomG(agame("a"))), atomP(prop("p"))), [name("x"), name("y")], false)];
	CloSeqs cloSeqs = (
		name("x"): <[term(\mod(iter(iter(atomG(agame("a")))), atomP(prop("p"))), [], false)], 0>,
		name("y"): <[term(\mod(iter(atomG(agame("b"))), atomP(prop("p"))), [name("x")], false)], 0>
	);
	MaybeSequent output = noSeq();
	
	return applyIter(input, 0, cloSeqs) == output;
}
// [<a*>p^[] q^[]] (apply to first term; empty closure map)
test bool applyIter_test_14() {
	CloGSequent input = [term(\mod(iter(atomG(agame("a"))), atomP(prop("p"))), [], false), term(atomP(prop("q")), [], false)];
	MaybeSequent output = sequent([term(or(atomP(prop("p")), \mod(atomG(agame("a")), \mod(iter(atomG(agame("a"))), atomP(prop("p"))))), [], false), term(atomP(prop("q")), [], false)]);
	
	return applyIter(input, 0, ()) == output;
}
// [<a*>p^[] q^[]] (apply to second term; empty closure map)
test bool applyIter_test_15() {
	CloGSequent input = [term(\mod(iter(atomG(agame("a"))), atomP(prop("p"))), [], false), term(atomP(prop("q")), [], false)];
	MaybeSequent output = noSeq();
	
	return applyIter(input, 1, ()) == output;
}
// [p^[] <a*>q^[]] (apply to second term; empty closure map)
test bool applyIter_test_16() {
	CloGSequent input = [term(atomP(prop("p")), [], false), term(\mod(iter(atomG(agame("a"))), atomP(prop("q"))), [], false)];
	MaybeSequent output = sequent([term(atomP(prop("p")), [], false), term(or(atomP(prop("q")), \mod(atomG(agame("a")), \mod(iter(atomG(agame("a"))), atomP(prop("q"))))), [], false)]);
	
	return applyIter(input, 1, ()) == output;
}
// [p^[] <a*>q^[] r^[]] (apply to second term; empty closure map)
test bool applyIter_test_17() {
	CloGSequent input = [term(atomP(prop("p")), [], false), term(\mod(iter(atomG(agame("a"))), atomP(prop("q"))), [], false), term(atomP(prop("r")), [], false)];
	MaybeSequent output = sequent([term(atomP(prop("p")), [], false), term(or(atomP(prop("q")), \mod(atomG(agame("a")), \mod(iter(atomG(agame("a"))), atomP(prop("q"))))), [], false), term(atomP(prop("r")), [], false)]);
	
	return applyIter(input, 1, ()) == output;
}
// [<a*>p^[] <b*>q^[]] (apply to first term; empty closure map)
test bool applyIter_test_18() {
	CloGSequent input = [term(\mod(iter(atomG(agame("a"))), atomP(prop("p"))), [], false), term(\mod(iter(atomG(agame("b"))), atomP(prop("q"))), [], false)];
	MaybeSequent output = sequent([term(or(atomP(prop("p")), \mod(atomG(agame("a")), \mod(iter(atomG(agame("a"))), atomP(prop("p"))))), [], false), term(\mod(iter(atomG(agame("b"))), atomP(prop("q"))), [], false)]);
	
	return applyIter(input, 0, ()) == output;
}
// [<a*>p^[] <b*>q^[]] (apply to second term; empty closure map)
test bool applyIter_test_19() {
	CloGSequent input = [term(\mod(iter(atomG(agame("a"))), atomP(prop("p"))), [], false), term(\mod(iter(atomG(agame("b"))), atomP(prop("q"))), [], false)];
	MaybeSequent output = sequent([term(\mod(iter(atomG(agame("a"))), atomP(prop("p"))), [], false), term(or(atomP(prop("q")), \mod(atomG(agame("b")), \mod(iter(atomG(agame("b"))), atomP(prop("q"))))), [], false)]);
	
	return applyIter(input, 1, ()) == output;
}
// [<a*>p^[] <b*>q^[]] (apply to both terms; empty closure map)
test bool applyIter_test_20() {
	CloGSequent input = [term(\mod(iter(atomG(agame("a"))), atomP(prop("p"))), [], false), term(\mod(iter(atomG(agame("b"))), atomP(prop("q"))), [], false)];
	MaybeSequent output = sequent([term(or(atomP(prop("p")), \mod(atomG(agame("a")), \mod(iter(atomG(agame("a"))), atomP(prop("p"))))), [], false), term(or(atomP(prop("q")), \mod(atomG(agame("b")), \mod(iter(atomG(agame("b"))), atomP(prop("q"))))), [], false)]);
	
	return applyIter(applyIter(input, 0, ()).seq, 1, ()) == output;
}
// <a||b>p^[]
test bool applyIter_test_21() {
	CloGSequent input = [term(\mod(choice(atomG(agame("a")), atomG(agame("b"))), atomP(prop("p"))), [], false)];
	MaybeSequent output = noSeq();
	
	return applyIter(input, 0, ()) == output;
}
// <(a*)^x>p^[]
test bool applyIter_test_22() {
	CloGSequent input = [term(\mod(dIter(iter(atomG(agame("a")))), atomP(prop("p"))), [], false)];
	MaybeSequent output = noSeq();
	
	return applyIter(input, 0, ()) == output;
}


// Apply dIter

// p^[] (empty closure map)
test bool applyDIter_test_1() {
	CloGSequent input = [term(atomP(prop("p")), [], false)];
	MaybeSequent output = noSeq();
	
	return applyDIter(input, 0, ()) == output;
}
// <a>p^[] (empty closure map)
test bool applyDIter_test_2() {
	CloGSequent input = [term(\mod(atomG(agame("a")), atomP(prop("p"))), [], false)];
	MaybeSequent output = noSeq();
	
	return applyDIter(input, 0, ()) == output;
}
// <a^x>p^[] (empty closure map)
test bool applyDIter_test_3() {
	CloGSequent input = [term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [], false)];
	MaybeSequent output = sequent([term(and(atomP(prop("p")), \mod(atomG(agame("a")), \mod(dIter(atomG(agame("a"))), atomP(prop("p"))))), [], false)]);
	
	return applyDIter(input, 0, ()) == output;
}
// <a^x>p^[] (closure map contains fp formula for x: <a^x>p)
test bool applyDIter_test_4() {
	CloGSequent input = [term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [], false)];
	CloSeqs cloSeqs = (name("x"): <[term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [], false)], 0>);
	MaybeSequent output = sequent([term(and(atomP(prop("p")), \mod(atomG(agame("a")), \mod(dIter(atomG(agame("a"))), atomP(prop("p"))))), [], false)]);
	
	return applyDIter(input, 0, cloSeqs) == output;
}
// <a^x>~p^[] (empty closure map)
test bool applyDIter_test_5() {
	CloGSequent input = [term(\mod(dIter(atomG(agame("a"))), neg(atomP(prop("p")))), [], false)];
	MaybeSequent output = sequent([term(and(neg(atomP(prop("p"))), \mod(atomG(agame("a")), \mod(dIter(atomG(agame("a"))), neg(atomP(prop("p")))))), [], false)]);
	
	return applyDIter(input, 0, ()) == output;
}
// <(a^d)^x>p^[] (empty closure map)
test bool applyDIter_test_6() {
	CloGSequent input = [term(\mod(dIter(dual(atomG(agame("a")))), atomP(prop("p"))), [], false)];
	MaybeSequent output = sequent([term(and(atomP(prop("p")), \mod(dual(atomG(agame("a"))), \mod(dIter(dual(atomG(agame("a")))), atomP(prop("p"))))), [], false)]);
	
	return applyDIter(input, 0, ()) == output;
}
// <a^x>p^x (closure map contains fp formula for x: <a^x>p == <a^x>p)
test bool applyDIter_test_7() {
	CloGSequent input = [term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [name("x")], false)];
	CloSeqs cloSeqs = (name("x"): <[term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [], false)], 0>);
	MaybeSequent output = sequent([term(and(atomP(prop("p")), \mod(atomG(agame("a")), \mod(dIter(atomG(agame("a"))), atomP(prop("p"))))), [name("x")], false)]);
	
	return applyDIter(input, 0, cloSeqs) == output;
}
// <a^x>p^x (closure map contains fp formula for x: <a^x*>p < <a^x>p)
test bool applyDIter_test_8() {
	CloGSequent input = [term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [name("x")], false)];
	CloSeqs cloSeqs = (name("x"): <[term(\mod(iter(dIter(atomG(agame("a")))), atomP(prop("p"))), [], false)], 0>);
	MaybeSequent output = sequent([term(and(atomP(prop("p")), \mod(atomG(agame("a")), \mod(dIter(atomG(agame("a"))), atomP(prop("p"))))), [name("x")], false)]);
	
	return applyDIter(input, 0, cloSeqs) == output;
}
// <a^x>p^x (closure map contains fp formula for x: <b*>p !<= <a^x>p)
test bool applyDIter_test_9() {
	CloGSequent input = [term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [name("x")], false)];
	CloSeqs cloSeqs = (name("x"): <[term(\mod(iter(atomG(agame("b"))), atomP(prop("p"))), [], false)], 0>);
	MaybeSequent output = noSeq();
	
	return applyDIter(input, 0, cloSeqs) == output;
}
// <a^x>p^y (closure map contains fp formula for x: <b*>p !<= <a^x>p and y: <a^x*>p < <a^x>p)
test bool applyDIter_test_10() {
	CloGSequent input = [term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [name("y")], false)];
	CloSeqs cloSeqs = (
		name("x"): <[term(\mod(iter(atomG(agame("b"))), atomP(prop("p"))), [], false)], 0>,
		name("y"): <[term(\mod(iter(dIter(atomG(agame("a")))), atomP(prop("p"))), [], false)], 0>
	);
	
	MaybeSequent output = sequent([term(and(atomP(prop("p")), \mod(atomG(agame("a")), \mod(dIter(atomG(agame("a"))), atomP(prop("p"))))), [name("y")], false)]);
	
	return applyDIter(input, 0, cloSeqs) == output;
}
// <a^x>p^x (closure map contains fp formula for x: <a^x>p = <a^x>p and y: <b*>p !<= <a^x>p)
test bool applyDIter_test_11() {
	CloGSequent input = [term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [name("x")], false)];
	CloSeqs cloSeqs = (
		name("x"): <[term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [], false)], 0>,
		name("y"): <[term(\mod(iter(atomG(agame("b"))), atomP(prop("p"))), [], false)], 0>
	);
	MaybeSequent output = sequent([term(and(atomP(prop("p")), \mod(atomG(agame("a")), \mod(dIter(atomG(agame("a"))), atomP(prop("p"))))), [name("x")], false)]);
	
	return applyDIter(input, 0, cloSeqs) == output;
}
// <a^x>p^{x, y} (closure map contains fp formula for x: <a^x>p = <a^x>p and y: <(a^x;b)*>q < <a^x>p)
test bool applyDIter_test_12() {
	CloGSequent input = [term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [name("x"), name("y")], false)];
	CloSeqs cloSeqs = (
		name("x"): <[term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [], false)], 0>,
		name("y"): <[term(\mod(iter(concat(dIter(atomG(agame("a"))), atomG(agame("b")))), atomP(prop("q"))), [name("x")], false)], 0>
	);
	MaybeSequent output = sequent([term(and(atomP(prop("p")), \mod(atomG(agame("a")), \mod(dIter(atomG(agame("a"))), atomP(prop("p"))))), [name("x"), name("y")], false)]);
	
	return applyDIter(input, 0, cloSeqs) == output;
}
// <a^x>p^{x, y} (closure map contains fp formula for x: <a^x*>p < <a^x>p and y: <b*>p !<= <a^x>p)
test bool applyDIter_test_13() {
	CloGSequent input = [term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [name("x"), name("y")], false)];
	CloSeqs cloSeqs = (
		name("x"): <[term(\mod(iter(dIter(atomG(agame("a")))), atomP(prop("p"))), [], false)], 0>,
		name("y"): <[term(\mod(iter(atomG(agame("b"))), atomP(prop("p"))), [name("x")], false)], 0>
	);
	MaybeSequent output = noSeq();
	
	return applyDIter(input, 0, cloSeqs) == output;
}
// [<a^x>p^[] q^[]] (apply to first term; empty closure map)
test bool applyDIter_test_14() {
	CloGSequent input = [term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [], false), term(atomP(prop("q")), [], false)];
	MaybeSequent output = sequent([term(and(atomP(prop("p")), \mod(atomG(agame("a")), \mod(dIter(atomG(agame("a"))), atomP(prop("p"))))), [], false), term(atomP(prop("q")), [], false)]);
	
	return applyDIter(input, 0, ()) == output;
}
// [<a^x>p^[] q^[]] (apply to second term; empty closure map)
test bool applyDIter_test_15() {
	CloGSequent input = [term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [], false), term(atomP(prop("q")), [], false)];
	MaybeSequent output = noSeq();
	
	return applyDIter(input, 1, ()) == output;
}
// [p^[] <a^x>q^[]] (apply to second term; empty closure map)
test bool applyDIter_test_16() {
	CloGSequent input = [term(atomP(prop("p")), [], false), term(\mod(dIter(atomG(agame("a"))), atomP(prop("q"))), [], false)];
	MaybeSequent output = sequent([term(atomP(prop("p")), [], false), term(and(atomP(prop("q")), \mod(atomG(agame("a")), \mod(dIter(atomG(agame("a"))), atomP(prop("q"))))), [], false)]);
	
	return applyDIter(input, 1, ()) == output;
}
// [p^[] <a^x>q^[] r^[]] (apply to second term; empty closure map)
test bool applyDIter_test_17() {
	CloGSequent input = [term(atomP(prop("p")), [], false), term(\mod(dIter(atomG(agame("a"))), atomP(prop("q"))), [], false), term(atomP(prop("r")), [], false)];
	MaybeSequent output = sequent([term(atomP(prop("p")), [], false), term(and(atomP(prop("q")), \mod(atomG(agame("a")), \mod(dIter(atomG(agame("a"))), atomP(prop("q"))))), [], false), term(atomP(prop("r")), [], false)]);
	
	return applyDIter(input, 1, ()) == output;
}
// [<a^x>p^[] <b^x>q^[]] (apply to first term; empty closure map)
test bool applyDIter_test_18() {
	CloGSequent input = [term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [], false), term(\mod(dIter(atomG(agame("b"))), atomP(prop("q"))), [], false)];
	MaybeSequent output = sequent([term(and(atomP(prop("p")), \mod(atomG(agame("a")), \mod(dIter(atomG(agame("a"))), atomP(prop("p"))))), [], false), term(\mod(dIter(atomG(agame("b"))), atomP(prop("q"))), [], false)]);
	
	return applyDIter(input, 0, ()) == output;
}
// [<a^x>p^[] <b^x>q^[]] (apply to second term; empty closure map)
test bool applyDIter_test_19() {
	CloGSequent input = [term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [], false), term(\mod(dIter(atomG(agame("b"))), atomP(prop("q"))), [], false)];
	MaybeSequent output = sequent([term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [], false), term(and(atomP(prop("q")), \mod(atomG(agame("b")), \mod(dIter(atomG(agame("b"))), atomP(prop("q"))))), [], false)]);
	
	return applyDIter(input, 1, ()) == output;
}
// [<a^x>p^[] <b^x>q^[]] (apply to both terms; empty closure map)
test bool applyDIter_test_20() {
	CloGSequent input = [term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [], false), term(\mod(dIter(atomG(agame("b"))), atomP(prop("q"))), [], false)];
	MaybeSequent output = sequent([term(and(atomP(prop("p")), \mod(atomG(agame("a")), \mod(dIter(atomG(agame("a"))), atomP(prop("p"))))), [], false), term(and(atomP(prop("q")), \mod(atomG(agame("b")), \mod(dIter(atomG(agame("b"))), atomP(prop("q"))))), [], false)]);
	
	return applyDIter(applyDIter(input, 0, ()).seq, 1, ()) == output;
}
// <a||b>p^[]
test bool applyDIter_test_21() {
	CloGSequent input = [term(\mod(choice(atomG(agame("a")), atomG(agame("b"))), atomP(prop("p"))), [], false)];
	MaybeSequent output = noSeq();
	
	return applyDIter(input, 0, ()) == output;
}
// <(a^x)*>p^[]
test bool applyDIter_test_22() {
	CloGSequent input = [term(\mod(iter(dIter(atomG(agame("a")))), atomP(prop("p"))), [], false)];
	MaybeSequent output = noSeq();
	
	return applyDIter(input, 0, ()) == output;
}



// Apply clo

// p^[] (empty closure map)
test bool applyClo_test_1() {
	CloGSequent input = [term(atomP(prop("p")), [], false)];
	tuple[MaybeSequent, CloGName] output = <noSeq(), name("")>;
	
	return applyClo(input, 0, ()) == output;
}
// <a>p^[] (empty closure map)
test bool applyClo_test_2() {
	CloGSequent input = [term(\mod(atomG(agame("a")), atomP(prop("p"))), [], false)];
	tuple[MaybeSequent, CloGName] output = <noSeq(), name("")>;
	
	return applyClo(input, 0, ()) == output;
}
// <a^x>p^[] (empty closure map)
test bool applyClo_test_3() {
	CloGSequent input = [term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [], false)];
	tuple[MaybeSequent, CloGName] output = <sequent([term(and(atomP(prop("p")), \mod(atomG(agame("a")), \mod(dIter(atomG(agame("a"))), atomP(prop("p"))))), [nameS("x",0)], false)]), nameS("x", 0)>;
	
	return applyClo(input, 0, ()) == output;
}
// <a^x>p^[] (closure map contains fp formula for x_0: <a^x>p)
test bool applyClo_test_4() {
	CloGSequent input = [term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [], false)];
	CloSeqs cloSeqs = (nameS("x", 0): <[term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [], false)], 0>);
	tuple[MaybeSequent, CloGName] output = <sequent([term(and(atomP(prop("p")), \mod(atomG(agame("a")), \mod(dIter(atomG(agame("a"))), atomP(prop("p"))))), [nameS("x", 1)], false)]), nameS("x", 1)>;
	
	return applyClo(input, 0, cloSeqs) == output;
}
// <a^x>~p^[] (empty closure map)
test bool applyClo_test_5() {
	CloGSequent input = [term(\mod(dIter(atomG(agame("a"))), neg(atomP(prop("p")))), [], false)];
	tuple[MaybeSequent, CloGName] output = <sequent([term(and(neg(atomP(prop("p"))), \mod(atomG(agame("a")), \mod(dIter(atomG(agame("a"))), neg(atomP(prop("p")))))), [nameS("x", 0)], false)]), nameS("x", 0)>;
	
	return applyClo(input, 0, ()) == output;
}
// <(a^d)^x>p^[] (empty closure map)
test bool applyClo_test_6() {
	CloGSequent input = [term(\mod(dIter(dual(atomG(agame("a")))), atomP(prop("p"))), [], false)];
	tuple[MaybeSequent, CloGName] output = <sequent([term(and(atomP(prop("p")), \mod(dual(atomG(agame("a"))), \mod(dIter(dual(atomG(agame("a")))), atomP(prop("p"))))), [nameS("x", 0)], false)]), nameS("x", 0)>;
	
	return applyClo(input, 0, ()) == output;
}
// <a^x>p^x_0 (closure map contains fp formula for x_0: <a^x>p == <a^x>p)
test bool applyClo_test_7() {
	CloGSequent input = [term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [nameS("x", 0)], false)];
	CloSeqs cloSeqs = (nameS("x", 0): <[term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [], false)], 0>);
	tuple[MaybeSequent, CloGName] output = <sequent([term(and(atomP(prop("p")), \mod(atomG(agame("a")), \mod(dIter(atomG(agame("a"))), atomP(prop("p"))))), [nameS("x", 0), nameS("x", 1)], false)]), nameS("x", 1)>;
	
	return applyClo(input, 0, cloSeqs) == output;
}
// <a^x>p^x_0 (closure map contains fp formula for x_0: <a^x*>p < <a^x>p)
test bool applyClo_test_8() {
	CloGSequent input = [term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [nameS("x", 0)], false)];
	CloSeqs cloSeqs = (nameS("x", 0): <[term(\mod(iter(dIter(atomG(agame("a")))), atomP(prop("p"))), [], false)], 0>);
	tuple[MaybeSequent, CloGName] output = <sequent([term(and(atomP(prop("p")), \mod(atomG(agame("a")), \mod(dIter(atomG(agame("a"))), atomP(prop("p"))))), [nameS("x", 0), nameS("x", 1)], false)]), nameS("x", 1)>;
	
	return applyClo(input, 0, cloSeqs) == output;
}
// <a^x>p^x_0 (closure map contains fp formula for x_0: <b*>p !<= <a^x>p)
test bool applyClo_test_9() {
	CloGSequent input = [term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [nameS("x", 0)], false)];
	CloSeqs cloSeqs = (nameS("x", 0): <[term(\mod(iter(atomG(agame("b"))), atomP(prop("p"))), [], false)], 0>);
	tuple[MaybeSequent, CloGName] output = <noSeq(), name("")>;
	
	return applyClo(input, 0, cloSeqs) == output;
}
// <a^x>p^x_1 (closure map contains fp formula for x_0: <b*>p !<= <a^x>p and x_1: <a^x*>p < <a^x>p)
test bool applyClo_test_10() {
	CloGSequent input = [term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [nameS("x", 1)], false)];
	CloSeqs cloSeqs = (
		nameS("x", 0): <[term(\mod(iter(atomG(agame("b"))), atomP(prop("p"))), [], false)], 0>,
		nameS("x", 1): <[term(\mod(iter(dIter(atomG(agame("a")))), atomP(prop("p"))), [], false)], 0>
	);
	
	tuple[MaybeSequent, CloGName] output = <sequent([term(and(atomP(prop("p")), \mod(atomG(agame("a")), \mod(dIter(atomG(agame("a"))), atomP(prop("p"))))), [nameS("x", 1), nameS("x", 2)], false)]), nameS("x", 2)>;

	return applyClo(input, 0, cloSeqs) == output;
}
// <a^x>p^x_0 (closure map contains fp formula for x_0: <a^x>p = <a^x>p and x_1: <b*>p !<= <a^x>p)
test bool applyClo_test_11() {
	CloGSequent input = [term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [nameS("x", 0)], false)];
	CloSeqs cloSeqs = (
		nameS("x", 0): <[term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [], false)], 0>,
		nameS("x", 1): <[term(\mod(iter(atomG(agame("b"))), atomP(prop("p"))), [], false)], 0>
	);
	tuple[MaybeSequent, CloGName] output = <sequent([term(and(atomP(prop("p")), \mod(atomG(agame("a")), \mod(dIter(atomG(agame("a"))), atomP(prop("p"))))), [nameS("x", 0), nameS("x", 2)], false)]), nameS("x", 2)>;
	
	return applyClo(input, 0, cloSeqs) == output;
}
// <a^x>p^{x_0, x_1} (closure map contains fp formula for x_0: <a^x>p = <a^x>p and x_1: <(a^x;b)*>q < <a^x>p)
test bool applyClo_test_12() {
	CloGSequent input = [term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [nameS("x", 0), nameS("x", 1)], false)];
	CloSeqs cloSeqs = (
		nameS("x", 0): <[term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [], false)], 0>,
		nameS("x", 1): <[term(\mod(iter(concat(dIter(atomG(agame("a"))), atomG(agame("b")))), atomP(prop("q"))), [nameS("x", 0)], false)], 0>
	);
	tuple[MaybeSequent, CloGName] output = <sequent([term(and(atomP(prop("p")), \mod(atomG(agame("a")), \mod(dIter(atomG(agame("a"))), atomP(prop("p"))))), [nameS("x", 0), nameS("x", 1), nameS("x", 2)], false)]), nameS("x", 2)>;
	
	return applyClo(input, 0, cloSeqs) == output;
}
// <a^x>p^{x_0, x_1} (closure map contains fp formula for x_0: <a^x*>p < <a^x>p and x_1: <b*>p !<= <a^x>p)
test bool applyClo_test_13() {
	CloGSequent input = [term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [nameS("x", 0), nameS("x", 1)], false)];
	CloSeqs cloSeqs = (
		nameS("x", 0): <[term(\mod(iter(dIter(atomG(agame("a")))), atomP(prop("p"))), [], false)], 0>,
		nameS("x", 1): <[term(\mod(iter(atomG(agame("b"))), atomP(prop("p"))), [nameS("x", 0)], false)], 0>
	);
	tuple[MaybeSequent, CloGName] output = <noSeq(), name("")>;
	
	return applyClo(input, 0, cloSeqs) == output;
}
// [<a^x>p^[] q^[]] (apply to first term; empty closure map)
test bool applyClo_test_14() {
	CloGSequent input = [term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [], false), term(atomP(prop("q")), [], false)];
	tuple[MaybeSequent, CloGName] output = <sequent([term(and(atomP(prop("p")), \mod(atomG(agame("a")), \mod(dIter(atomG(agame("a"))), atomP(prop("p"))))), [nameS("x", 0)], false), term(atomP(prop("q")), [], false)]), nameS("x", 0)>;
	
	return applyClo(input, 0, ()) == output;
}
// [<a^x>p^[] q^[]] (apply to second term; empty closure map)
test bool applyClo_test_15() {
	CloGSequent input = [term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [], false), term(atomP(prop("q")), [], false)];
	tuple[MaybeSequent, CloGName] output = <noSeq(), name("")>;
	
	return applyClo(input, 1, ()) == output;
}
// [p^[] <a^x>q^[]] (apply to second term; empty closure map)
test bool applyClo_test_16() {
	CloGSequent input = [term(atomP(prop("p")), [], false), term(\mod(dIter(atomG(agame("a"))), atomP(prop("q"))), [], false)];
	tuple[MaybeSequent, CloGName] output = <sequent([term(atomP(prop("p")), [], false), term(and(atomP(prop("q")), \mod(atomG(agame("a")), \mod(dIter(atomG(agame("a"))), atomP(prop("q"))))), [nameS("x", 0)], false)]), nameS("x", 0)>;
	
	return applyClo(input, 1, ()) == output;
}
// [p^[] <a^x>q^[] r^[]] (apply to second term; empty closure map)
test bool applyClo_test_17() {
	CloGSequent input = [term(atomP(prop("p")), [], false), term(\mod(dIter(atomG(agame("a"))), atomP(prop("q"))), [], false), term(atomP(prop("r")), [], false)];
	tuple[MaybeSequent, CloGName] output = <sequent([term(atomP(prop("p")), [], false), term(and(atomP(prop("q")), \mod(atomG(agame("a")), \mod(dIter(atomG(agame("a"))), atomP(prop("q"))))), [nameS("x", 0)], false), term(atomP(prop("r")), [], false)]), nameS("x", 0)>;
	
	return applyClo(input, 1, ()) == output;
}
// [<a^x>p^[] <b^x>q^[]] (apply to first term; empty closure map)
test bool applyClo_test_18() {
	CloGSequent input = [term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [], false), term(\mod(dIter(atomG(agame("b"))), atomP(prop("q"))), [], false)];
	tuple[MaybeSequent, CloGName] output = <sequent([term(and(atomP(prop("p")), \mod(atomG(agame("a")), \mod(dIter(atomG(agame("a"))), atomP(prop("p"))))), [nameS("x", 0)], false), term(\mod(dIter(atomG(agame("b"))), atomP(prop("q"))), [], false)]), nameS("x", 0)>;
	
	return applyClo(input, 0, ()) == output;
}
// [<a^x>p^[] <b^x>q^[]] (apply to second term; empty closure map)
test bool applyClo_test_19() {
	CloGSequent input = [term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [], false), term(\mod(dIter(atomG(agame("b"))), atomP(prop("q"))), [], false)];
	tuple[MaybeSequent, CloGName] output = <sequent([term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [], false), term(and(atomP(prop("q")), \mod(atomG(agame("b")), \mod(dIter(atomG(agame("b"))), atomP(prop("q"))))), [nameS("x", 0)], false)]), nameS("x", 0)>;
	
	return applyClo(input, 1, ()) == output;
}
// [<a^x>p^[] <b^x>q^[]] (apply to both terms; empty closure map)
test bool applyClo_test_20() {
	CloGSequent input = [term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [], false), term(\mod(dIter(atomG(agame("b"))), atomP(prop("q"))), [], false)];
	tuple[MaybeSequent, CloGName] output1 = <sequent([term(and(atomP(prop("p")), \mod(atomG(agame("a")), \mod(dIter(atomG(agame("a"))), atomP(prop("p"))))), [nameS("x", 0)], false), term(\mod(dIter(atomG(agame("b"))), atomP(prop("q"))), [], false)]), nameS("x", 0)>;
	CloSeqs cloSeqs = (nameS("x", 0): <[term(\mod(dIter(atomG(agame("a"))), atomP(prop("p"))), [], false), term(\mod(dIter(atomG(agame("b"))), atomP(prop("q"))), [], false)], 0>);
	tuple[MaybeSequent, CloGName] output2 = <sequent([term(and(atomP(prop("p")), \mod(atomG(agame("a")), \mod(dIter(atomG(agame("a"))), atomP(prop("p"))))), [nameS("x", 0)], false), term(and(atomP(prop("q")), \mod(atomG(agame("b")), \mod(dIter(atomG(agame("b"))), atomP(prop("q"))))), [nameS("x", 1)], false)]), nameS("x", 1)>;
	
	tuple[MaybeSequent, CloGName] result1 = applyClo(input, 0, ());
	tuple[MaybeSequent, CloGName] result2 = applyClo(result1[0].seq, 1, cloSeqs);
	
	return result1 == output1 && result2 == output2;
}
// [<a^x^x>p^[]] (apply twice (with an and application in between))
test bool applyClo_test_21() {
	CloGSequent input = [term(\mod(dIter(dIter(atomG(agame("a")))), atomP(prop("p"))), [], false)];
	tuple[MaybeSequent, CloGName] output1 = <sequent([term(and(atomP(prop("p")), \mod(dIter(atomG(agame("a"))), \mod(dIter(dIter(atomG(agame("a")))), atomP(prop("p"))))), [nameS("x", 0)], false)]), nameS("x", 0)>;
	CloSeqs cloSeqs = (nameS("x", 0): <[term(\mod(dIter(dIter(atomG(agame("a")))), atomP(prop("p"))), [], false)], 0>);
	tuple[MaybeSequent, CloGName] output2 = <sequent([term(and(\mod(dIter(dIter(atomG(agame("a")))), atomP(prop("p"))),\mod(atomG(agame("a")), \mod(dIter(atomG(agame("a"))), \mod(dIter(dIter(atomG(agame("a")))), atomP(prop("p")))))), [nameS("x", 0), nameS("x", 1)],false)]), nameS("x", 1)>;
	
	tuple[MaybeSequent, CloGName] result1 = applyClo(input, 0, ());
	MaybeSequents result2 = applyAnd(result1[0].seq, 0);
	tuple[MaybeSequent, CloGName] result3 = applyClo(result2.right, 0, cloSeqs);
	
	return result1 == output1 && result3 == output2;
}
// <a||b>p^[]
test bool applyClo_test_22() {
	CloGSequent input = [term(\mod(choice(atomG(agame("a")), atomG(agame("b"))), atomP(prop("p"))), [], false)];
	tuple[MaybeSequent, CloGName] output = <noSeq(), name("")>;
	
	return applyClo(input, 0, ()) == output;
}
// <(a^x)*>p^[]
test bool applyClo_test_23() {
	CloGSequent input = [term(\mod(iter(dIter(atomG(agame("a")))), atomP(prop("p"))), [], false)];
	tuple[MaybeSequent, CloGName] output = <noSeq(), name("")>;
	
	return applyClo(input, 0, ()) == output;
}