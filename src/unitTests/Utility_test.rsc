module unitTests::Utility_test

import utility::Utility;

import IO;
import Exception;

// set size 1, combinations of 1
test bool combinations_test_1() {
	return combinations(1, 1) == [[0]];
}
// set size 2, combinations of 1
test bool combinations_test_2() {
	return combinations(2, 1) == [[0], [1]];
}
// set size 2, combinations of 2
test bool combinations_test_3() {
	return combinations(2, 2) == [[0, 1]];
}
// set size 4, combinations of 2
test bool combinations_test_4() {
	return combinations(4, 2) == [[0, 1], [0, 2], [0, 3], [1, 2], [1, 3], [2, 3]];
}
// set size 4, combinations of 3
test bool combinations_test_5() {
	return combinations(4, 3) == [[0, 1, 2], [0, 1, 3], [0, 2, 3], [1, 2, 3]];
}
// set size 0, combinations of 1
test bool combinations_test_6() {
	try combinations(0, 1);
	catch IllegalArgument("Error: Empty starting sets not allowed!"): return true;
	return false;
}
// set size -1, combinations of 1
test bool combinations_test_7() {
	try combinations(-1, 1);
	catch IllegalArgument("Error: Cannot have a negative number of elements in the starting set!"): return true;
	return false;
}
// set size 1, combinations of 0
test bool combinations_test_8() {
	try combinations(1, 0);
	catch IllegalArgument("Error: Empty combinations not allowed!"): return true;
	return false;
}
// set size 1, combinations of -1
test bool combinations_test_9() {
	try combinations(1, -1);
	catch IllegalArgument("Error: Cannot have a negative number of elements in a combination!"): return true;
	return false;
}
// set size 1, combinations of 2
test bool combinations_test_10() {
	try combinations(1, 2);
	catch IllegalArgument("Error: Combination size cannot be larger than total size!"): return true;
	return false;
}

// set size 1, combinations of 1, include 0
test bool combinationsIncluding_test_1() {
	return combinationsIncluding(1, 1, 0) == [[0]];
}
// set size 2, combinations of 1, include 0
test bool combinationsIncluding_test_2() {
	return combinationsIncluding(2, 1, 0) == [[0]];
}
// set size 2, combinations of 2, include 0
test bool combinationsIncluding_test_3() {
	return combinationsIncluding(2, 2, 0) == [[0, 1]];
}
// set size 4, combinations of 2, include 0
test bool combinationsIncluding_test_4() {
	return combinationsIncluding(4, 2, 0) == [[0, 1], [0, 2], [0, 3]];
}
// set size 4, combinations of 2, include 2
test bool combinationsIncluding_test_5() {
	return combinationsIncluding(4, 2, 2) == [[0, 2], [1, 2], [2, 3]];
}
// set size 4, combinations of 3, include 2
test bool combinationsIncluding_test_6() {
	return combinationsIncluding(4, 3, 2) == [[0, 1, 2], [0, 2, 3], [1, 2, 3]];
}
// set size 1, combinations of 1, include -1
test bool combinationsIncluding_test_7() {
	try combinationsIncluding(1, 1, -1);
	catch IllegalArgument("Error: Index to include should be between 0 and the total size - 1!"): return true;
	return false;
}
// set size 1, combinations of 1, include 1
test bool combinationsIncluding_test_8() {
	try combinationsIncluding(1, 1, 1);
	catch IllegalArgument("Error: Index to include should be between 0 and the total size - 1!"): return true;
	return false;
}