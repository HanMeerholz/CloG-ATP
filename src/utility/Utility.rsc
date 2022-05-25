module utility::Utility

import List;

list[list[int]] combRec(list[int] indices, int len) {
	if (len == 1) return [ [idx] | idx <- indices ];
	
	list[list[int]] result = [];
	
	for (list[int] subComb <- combRec(indices, len-1)) {
		
		int startPos = subComb[size(subComb) - 1] + 1;
		
		if (size(indices) >= startPos)
			for (int i <- [startPos .. size(indices)]) {
				result += [(subComb + indices[i])];
			}
	}
	
	return result;
}

/*
 * Helper function returning a list of combinations of integers
 *
 * Input:  the number of items in the starting set, and the number of
 *         items in a combination
 * Output: a list of combinations, each combination being a list of integers
 *
 * Returns a list of all the lists of size combSize corresponding to a unique
 * combination of integers 0 to totalSize.
 * 
 * Example: combinations(5, 3) returns [[0,1,2], [0,1,3], [0,1,4], [1,2,4], [1,3,4], [2,3,4]]
 */
list[list[int]] combinations(int totalSize, int combSize) {
	return combRec([0 .. totalSize], combSize);
}