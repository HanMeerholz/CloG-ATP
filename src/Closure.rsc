module Closure

import ATP_Base;
import GLASTs;
import Map;

/*
 * A function that generates a map that gives a unique name for each fixpoint formula
 * that might occur in a proof starting with the input sequent
 *
 * Input:  the input sequent
 * Output: a map, mapping each possible fixpoint formula in the closures of the formulae
 *         present in the terms of the input sequent to a unique CloGName
 */
FpClosure generateFpClosure(CloGSequent input) {
	FpClosure fpMap = ();
	for (CloGTerm term <- input) {
		if (term(\mod(Game g, GameLog pr), _, _) := term) {
			top-down visit (g) {
				case Game iterGame:iter(_): {
					GameLog fpForm = \mod(iterGame, pr);
					if (!(fpForm in fpMap)) {
						newName = nameS("x", size(fpMap));
						fpMap += (fpForm: newName);
					}
				}
				case Game dIterGame:dIter(_): {
					GameLog fpForm = \mod(dIterGame, pr);
					if (!(fpForm in fpMap)) {
						newName = nameS("x", size(fpMap));
						fpMap += (\mod(dIterGame, pr): newName);
					}
				}
			}
		}
	}
	return fpMap;
}