module integrationTests::Proof_tests
/*
 * Module to execute the integration tests
 */

import ATP::CloG_ATP_Tool;

/*
 * A function that generates LaTeX proofs for each of the sequents in the input folder (manually)
 */
void executeTests() {
	proofSearch_Tool("01 (empty)");
	proofSearch_Tool("02 (single)");
	proofSearch_Tool("03 (single named)");
	proofSearch_Tool("04 (double)");
	proofSearch_Tool("05 (double named)");
	proofSearch_Tool("06 (ax1)");
	proofSearch_Tool("07 (ax1 with labels)");
	proofSearch_Tool("08 (ax1 with side formulae)");
	proofSearch_Tool("09 (ax1 with side formulae and labels)");
	
	proofSearch_Tool("10 (disClo)/seq", [<"10 (disClo)/cloSeq and fpSeq", 0>], ["10 (disClo)/cloSeq and fpSeq"]);
	
	proofSearch_Tool("11 (or)");
	proofSearch_Tool("12 (or with side formulae)");
	proofSearch_Tool("13 (and)");
	proofSearch_Tool("14 (modm)");
	proofSearch_Tool("15 (choice)");
	proofSearch_Tool("16 (dChoice)");
	proofSearch_Tool("17 (concat)");
	proofSearch_Tool("18 (dTest)");
	proofSearch_Tool("19 (test)");
	proofSearch_Tool("20 (monotonicity)");
	proofSearch_Tool("21 (iter 1)");
	proofSearch_Tool("22 (iter 2)");
	proofSearch_Tool("23 (iter 3)");
	proofSearch_Tool("24 (iter 4)");
	proofSearch_Tool("25 (dIter & iter)");
	proofSearch_Tool("26 (dIter & iter 2)");
	proofSearch_Tool("27 (double dIter & iter)");
	proofSearch_Tool("28 (multi iter)");
	proofSearch_Tool("29 (multi iter 2)");
	proofSearch_Tool("30 (multi dIter)");
	proofSearch_Tool("31 (double iter fail)");
	proofSearch_Tool("32 (double dIter fail)");
	proofSearch_Tool("33 (multi iter fail)");
	proofSearch_Tool("34 (multi dIter fail)");
	proofSearch_Tool("35 (iter dIter alternate fail)");
	proofSearch_Tool("36 (bigSeq1)");
	proofSearch_Tool("37 (bigSeq2)");
	proofSearch_Tool("38 (proof 1)");
	proofSearch_Tool("39 (proof 2)");
}