module ATP::CloG_ATP_Tool
/*
 * Main module for the automated theorem prover tool
 */

import CloG_Base::CloGSyntax;
import CloG_Base::GLASTs;
import CloG_Base::CST2AST_CloG;
import CloG_Base::LaTeXOutput;
import ATP::ATP_Base;
import ATP::ProofSearch;
import ATP::PostProcess;
import ATP::Closure;

import util::IDE;
import ParseTree;
import IO;

// Call IDE() in terminal to activate parse checker and keyword hihlighting for .clog files in eclipse.
void IDE() {
	start[SCloGSequent] clogSeq(str src, loc l) {
		return parse(#start[SCloGSequent], src, l);
	}

	registerLanguage("CloGSeq", "seq", clogSeq);
}

// Main function is split up for modularity and to help with testing in the terminal.

// Get the location of an input .seq file.
loc inputLoc(str file) {
	return (|project://CloG-ATP/input| + file)[extension=".seq"];
}

// Form the location for an output .tex file
loc outputLoc(str file) {
	return (|project://CloG-ATP/output| + file)[extension=".tex"];
}

// Parse input .clog file and output abstract syntax tree for the CloG Proof
CloGSequent getCloGAST(str file){
	loc l = inputLoc(file);
	start[SCloGSequent] cst = parse(#start[SCloGSequent], l);
	return cst2astCloG(cst);
}

// Input abstract syntax tree for CloG proof and output .tex proof tree to the given output file
void CloG2LaTeX(CloGProof p, str out){
	loc l = outputLoc(out);
	LaTeXOutput(p, l);
}

// Displays the sequent at file location "in" as a CloG proof tree as a .tex proof tree displaying the
// sequent and a dummy "weak" rule application.
void input2latex(str \in,  str out){
	CloG2LaTeX(CloGUnaryInf(getCloGAST(\in), weak(), CloGLeaf()), out);
}

// Input .seq file name, do a default proof search on the sequent and display the result in LaTeX
// (or display "fail!" if no proof could be found).
void proofSearch_Tool(str file){
	CloGSequent seqAST = getCloGAST(file);
	
	fpClosure = generateFpClosure(seqAST);
	
	MaybeProof resProof = proofSearch(seqAST);
	if (resProof != noProof())
		LaTeXOutput(resProof.p, outputLoc(file));
	else
		println("fail!\n");
}

// Input .seq file name, do a default proof search on the sequent and display the result in LaTeX
// (or display "fail!" if no proof could be found).
void proofSearch_Tool(str file, int depth) {
	CloGSequent seqAST = getCloGAST(file);
	
	fpClosure = generateFpClosure(seqAST);
	
	MaybeProof resProof = proofSearch(seqAST, depth);
	if (resProof != noProof()) {
		CloGProof validProof = replaceUnusedClos(resProof.p);
		LaTeXOutput(validProof, outputLoc(file));
	} else
		println("fail!\n");
}


// Input .seq file name, do a proof search on the sequent with a given list of names to files with closure
// sequents and integers corresponding to the relevant fixpoint formula within those sequents, a given
// list of fixpoint sequents in a similar manner (but without the integer), and a maximum proof search depth.
// Display the result in LaTeX (or display "fail!" if no proof could be found).
void proofSearch_Tool(str file, list[tuple[str, int]] cloSeqFiles, list[str] fpSeqsFiles, int depth){
	CloGSequent seqAST = getCloGAST(file);
	
	fpClosure = generateFpClosure(seqAST);
	
	CloSeqs cloSeqs = ();
	for (int i <- [0 .. size(cloSeqFiles)])
		cloSeqs += (nameS("x", i): <getCloGAST(cloSeqFiles[i][0]), cloSeqFiles[i][1]>);
	
	list[CloGSequent] fpSeqs = [];
	for (str fpSeqFile <- fpSeqsFiles)
		fpSeqs += getCloGAST(fpSeqFile);
		
	MaybeProof resProof = proofSearch(seqAST, cloSeqs, fpSeqs, depth);
	if (resProof != noProof())
		LaTeXOutput(resProof.p, outputLoc(file));
	else
		println("fail!\n");
}

