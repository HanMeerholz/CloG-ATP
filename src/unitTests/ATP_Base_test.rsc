module unitTests::ATP_Base_test

import ATP_Base;
import GLASTs;
import Exception;

// SubTerm

// A game should be a subterm of itself
// (a <= a)
test bool subTerm_test_1() =
	subTerm(atomG(agame("a")), atomG(agame("a"))) == true;
// A game should be a subterm of a unary operator applied to itself
// (a <= a^d)
test bool subTerm_test_2() =
	subTerm(atomG(agame("a")), dual(atomG(agame("a")))) == true;
// A game should be a subterm of a binary operator applied to itself and something else
// (a <= a && b)
test bool subTerm_test_3() =
	subTerm(atomG(agame("a")), dChoice(atomG(agame("a")), atomG(agame("b")))) == true;
// This should also work if the game appears not at the start of the other formula
// (a <= b && a)
test bool subTerm_test_4() =
	subTerm(atomG(agame("a")), dChoice(atomG(agame("b")), atomG(agame("a")))) == true;
// Further nesting
// (a <= (b && a)*)
test bool subTerm_test_5() =
	subTerm(atomG(agame("a")), iter(dChoice(atomG(agame("b")), atomG(agame("a"))))) == true;
// A game should be a subterm a test of a game logic formula containing that game
// (a <= <a>p?)
test bool subTerm_test_6() =
	subTerm(atomG(agame("a")), \test(\mod(atomG(agame("a")), atomP(prop("p"))))) == true;
// A composite game can also be a subterm of a bigger composite game
// ((a && b) <= (a && b)*)
test bool subTerm_test_7() =
	subTerm(dChoice(atomG(agame("a")), atomG(agame("b"))), iter(dChoice(atomG(agame("a")), atomG(agame("b"))))) == true;
// A simple game should not be a subterm of a different simple game
// (a !<= b)
test bool subTerm_test_8() =
	subTerm(atomG(agame("a")), atomG(agame("b"))) == false;
// A composite game should not be a subterm of a simple game
// (a^d !<= a)
test bool subTerm_test_9() =
	subTerm(dual(atomG(agame("a"))), atomG(agame("a"))) == false;
// A game should be fully contained to be a subterm of another game
// (a && a !<= a && b)
test bool subTerm_test_10() =
	subTerm(dChoice(atomG(agame("a")), atomG(agame("a"))), dChoice(atomG(agame("a")), atomG(agame("b")))) == false;
// Order matters
// (a && b !<= b && a)
test bool subTerm_test_11() =
	subTerm(dChoice(atomG(agame("a")), atomG(agame("b"))), dChoice(atomG(agame("b")), atomG(agame("a")))) == false;
// Order matters
// (a && b !<= a* && b)
test bool subTerm_test_12() =
	subTerm(dChoice(atomG(agame("a")), atomG(agame("b"))), dChoice(iter(atomG(agame("a"))), atomG(agame("b")))) == false;


// fpLessThanOrEqualTo

// <a*>p <= <a*>q
test bool fpLessThanOrEqualTo_test_1() = 
	fpLessThanOrEqualTo(\mod(iter(atomG(agame("a"))), atomP(prop("p"))),
	                    \mod(iter(atomG(agame("a"))), atomP(prop("q")))) == true;
// <(a* && b)^x>p <= <a*>q
test bool fpLessThanOrEqualTo_test_2() = 
	fpLessThanOrEqualTo(\mod(dIter(dChoice(iter(atomG(agame("a"))), atomG(agame("b")))), atomP(prop("p"))),
	                    \mod(iter(atomG(agame("a"))), atomP(prop("q")))) == true;
// <(a* && b)^x><a*>p <= <a*>q
test bool fpLessThanOrEqualTo_test_3() = 
	fpLessThanOrEqualTo(\mod(dIter(dChoice(iter(atomG(agame("a"))), atomG(agame("b")))),
	                         \mod(iter(atomG(agame("a"))), atomP(prop("p")))),
	                    \mod(iter(atomG(agame("a"))), atomP(prop("q")))) == true;
// <a*><(a* && b)^x>p <= <(a* && b)^x>q
test bool fpLessThanOrEqualTo_test_4() = 
	fpLessThanOrEqualTo(\mod(iter(atomG(agame("a"))),
	                         \mod(dIter(dChoice(iter(atomG(agame("a"))), atomG(agame("b")))), atomP(prop("p")))),
	                    \mod(dIter(dChoice(iter(atomG(agame("a"))), atomG(agame("b")))), atomP(prop("q")))) == false;
// <a*>p !<= <(a* && b)^x><a*>q
test bool fpLessThanOrEqualTo_test_5() = 
	fpLessThanOrEqualTo(\mod(iter(atomG(agame("a"))), atomP(prop("p"))),
	                    \mod(dIter(dChoice(iter(atomG(agame("a"))), atomG(agame("b")))),
	                         \mod(iter(atomG(agame("a"))), atomP(prop("q"))))) == false;
// <a*>p !<= <a^x>p
test bool fpLessThanOrEqualTo_test_6() = 
	fpLessThanOrEqualTo(\mod(iter(atomG(agame("a"))), atomP(prop("p"))),
	                    \mod(dIter(atomG(agame("a"))), atomP(prop("p")))) == false;
// <a*>p !<= <a^x>p
test bool fpLessThanOrEqualTo_test_7() = 
	fpLessThanOrEqualTo(\mod(iter(atomG(agame("a"))), atomP(prop("p"))),
	                    \mod(dIter(atomG(agame("a"))), atomP(prop("p")))) == false;
// <a*^x>p <= <a*>p
test bool fpLessThanOrEqualTo_test_8() = 
	fpLessThanOrEqualTo(\mod(dIter(iter(atomG(agame("a")))), atomP(prop("p"))),
	                    \mod(iter(atomG(agame("a"))), atomP(prop("p")))) == true;
// p <= q should throw an exception
test bool fpLessThanOrEqualTo_test_9() {
	try fpLessThanOrEqualTo(atomP(prop("p")), atomP(prop("q")));
	catch IllegalArgument("Error: cannot apply fixpoint ordering on non-fixpoint formulae!"): return true;
	return false;
}
// <a>p <= <b>q should throw an exception
test bool fpLessThanOrEqualTo_test_10() {
	try fpLessThanOrEqualTo(\mod(atomG(agame("a")), atomP(prop("p"))), \mod(atomG(agame("b")), atomP(prop("q"))));
	catch IllegalArgument("Error: cannot apply fixpoint ordering on non-fixpoint formulae!"): return true;
	return false;
}