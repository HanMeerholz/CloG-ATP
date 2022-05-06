module LaTeXOutput
/*
 * Module defining the transformation from abstract proof trees to LaTeX proof trees
 */

import GLASTs;

import IO;
import List;

// Functions takes a proof tree and file location as input then writes the LaTeX output to the file.
void LaTeXOutput(CloGProof p, loc out){
	writeFile(out, LaTeXOutput(p));
}

// Functions define the preamle and proof tree wrapper for LaTeX output
str LaTeXOutput(CloGProof p) = 
	"\\documentclass{article}
	'\\usepackage[utf8]{inputenc}
	'\\usepackage{prooftrees}
	'
	'\\begin{document}
	'
	'\\begin{prooftree}
	'<LaTeXCloGTree(p)>
	'\\end{prooftree}
	'
	'\\end{document}";

// Function to output the LaTeX proof tree part for each CloG sequent and assocated rule label
str LaTeXCloGTree(CloGLeaf()) =
	"\\AxiomC{}";
str LaTeXCloGTree(disClo(list[CloGTerm] seq, CloGName n)) =
	"\\AxiomC{$[<(LaTeXCloGTree(head(seq)) | it + ", " + LaTeXCloGTree(t) | CloGTerm t <- tail(seq))>]^{<LaTeXCloGTree(n)>}$}";
str LaTeXCloGTree(CloGUnaryInf(list[CloGTerm] seq, CloGRule rule, CloGProof inf)) =
	"<LaTeXCloGTree(inf)>
	'\\RightLabel{<LaTeXCloGTree(rule)>}
	'\\UnaryInfC{$<(LaTeXCloGTree(head(seq)) | it + ", " + LaTeXCloGTree(t) | CloGTerm t <- tail(seq))>$}";
str LaTeXCloGTree(CloGBinaryInf(list[CloGTerm] seq, CloGProof infL, CloGProof infR)) =
	"<LaTeXCloGTree(infL)>
	'<LaTeXCloGTree(infR)>
	'\\RightLabel{$\\wedge$}
	'\\BinaryInfC{$<(LaTeXCloGTree(head(seq)) | it + ", " + LaTeXCloGTree(t) | CloGTerm t <- tail(seq))>$}";
	
// Function to output the superscript label attached to each logic formula
str LaTeXCloGTree(term(GameLog s, [])) 
	= "(<LaTeXGameLog(s)>)^{\\varepsilon}";
str LaTeXCloGTree(term(GameLog s, list[CloGName] label)) 
	= "(<LaTeXGameLog(s)>)^{<(LaTeXCloGTree(head(label)) | it + ", " + LaTeXCloGTree(n) | CloGName n <- tail(label))>}";

// Function to output the CloG rule labels
str LaTeXCloGTree(ax1()) = "Ax1";
str LaTeXCloGTree(modm()) = "mod$_{m}$";
str LaTeXCloGTree(andR()) = "$\\wedge$"; 
str LaTeXCloGTree(orR()) =  "$\\vee$";
str LaTeXCloGTree(choiceR()) =  "$\\sqcup$";
str LaTeXCloGTree(dChoiceR()) =  "$\\sqcap$";
str LaTeXCloGTree(weak()) =  "weak";
str LaTeXCloGTree(exp()) =  "exp";
str LaTeXCloGTree(concatR()) =  "$;$";
str LaTeXCloGTree(iterR()) =  "$*$";
str LaTeXCloGTree(testR()) =  "$?$";
str LaTeXCloGTree(dIterR()) =  "$\\times$";
str LaTeXCloGTree(dTestR()) =  "$!$";
str LaTeXCloGTree(clo(CloGName n)) =  "clo$_{<LaTeXCloGTree(n)>}$";

// Function to output a CloG name which can have a subscript
str LaTeXCloGTree(name(str n)) = "<n>";
str LaTeXCloGTree(nameS(str n, int sub)) = "<n>_{<sub>}";

// Function to output the game logic formulae in LaTeX maths mode
str LaTeXGameLog(top()) = "(p\\vee\\neg p)";
str LaTeXGameLog(bot()) = "(p\\wedge\\neg p)";
str LaTeXGameLog(atomP(Prop p)) = "<LaTeXGameLog(p)>";
str LaTeXGameLog(neg(GameLog pr)) = "\\neg <hasPar(pr)>";
str LaTeXGameLog(\mod(Game g, GameLog pr)) = "\\langle <hasPar(g)>\\rangle <hasPar(pr)>";
str LaTeXGameLog(dMod(Game g, GameLog pr)) = "[<hasPar(g)>]<hasPar(pr)>";
str LaTeXGameLog(and(GameLog pL, GameLog pR)) = "<hasPar(pL)>\\wedge <hasPar(pR)>";
str LaTeXGameLog(or(GameLog pL, GameLog pR)) = "<hasPar(pL)>\\vee <hasPar(pR)>";
str LaTeXGameLog(cond(GameLog pL, GameLog pR)) = "<hasPar(pL)>\\rightarrow <hasPar(pR)>";
str LaTeXGameLog(biCond(GameLog pL, GameLog pR)) = "<hasPar(pL)>\\leftrightarrow <hasPar(pR)>";

// Function to output the game formulae in LaTeX maths mode
str LaTeXGameLog(atomG(AGame g)) = "<LaTeXGameLog(g)>";
str LaTeXGameLog(dual(Game ga)) = "{<hasPar(ga)>}^d";
str LaTeXGameLog(\test(GameLog g)) = "<hasPar(g)>?";
str LaTeXGameLog(dTest(GameLog g)) = "<hasPar(g)>!";
str LaTeXGameLog(iter(Game ga)) = "{<hasPar(ga)>}^{*}";
str LaTeXGameLog(dIter(Game ga)) = "{<hasPar(ga)>}^{\\times}";
str LaTeXGameLog(concat(Game gL, Game gR)) = "<hasPar(gL)>;<hasPar(gR)>";
str LaTeXGameLog(choice(Game gL, Game gR)) = "<hasPar(gL)>\\sqcup <hasPar(gR)>";
str LaTeXGameLog(dChoice(Game gL, Game gR)) = "<hasPar(gL)>\\sqcap <hasPar(gR)>";

// Function to put parentheses around only the binary connectives and not unary connectives or atomic formulae
str hasPar(top()) = "(p\\vee\\neg p)";
str hasPar(bot()) = "(p\\wedge\\neg p)";
str hasPar(atomP(Prop p)) = "<LaTeXGameLog(atomP(p))>";
str hasPar(neg(GameLog pr)) = "<LaTeXGameLog(neg(pr))>";
str hasPar(\mod(Game g, GameLog pr)) = "<LaTeXGameLog(\mod(g,pr))>";
str hasPar(dMod(Game g, GameLog pr)) = "<LaTeXGameLog(dMod(g,pr))>";
str hasPar(and(GameLog pL, GameLog pR)) = "(<LaTeXGameLog(and(pL,pR))>)";
str hasPar(or(GameLog pL, GameLog pR)) = "(<LaTeXGameLog(or(pL,pR))>)";
str hasPar(cond(GameLog pL, GameLog pR)) = "(<LaTeXGameLog(cond(pL,pR))>)";
str hasPar(biCond(GameLog pL, GameLog pR)) = "(<LaTeXGameLog(biCond(pL,pR))>)";
str hasPar(atomG(AGame g)) = "<LaTeXGameLog(atomG(g))>";
str hasPar(dual(Game ga)) = "<LaTeXGameLog(dual(ga))>";
str hasPar(\test(GameLog g)) = "<LaTeXGameLog(\test(g))>";
str hasPar(dTest(GameLog g)) = "<LaTeXGameLog(dTest(g))>";
str hasPar(iter(Game ga)) = "<LaTeXGameLog(iter(ga))>";
str hasPar(dIter(Game ga)) = "<LaTeXGameLog(dIter(ga))>";
str hasPar(concat(Game gL, Game gR)) = "(<LaTeXGameLog(concat(gL,gR))>)";
str hasPar(choice(Game gL, Game gR)) = "(<LaTeXGameLog(choice(gL,gR))>)";
str hasPar(dChoice(Game gL, Game gR)) = "(<LaTeXGameLog(dChoice(gL,gR))>)";

// Functions to output the atomic propositions and games which can have a subscript
str LaTeXGameLog(agame(str n)) = "<n>";
str LaTeXGameLog(agameS(str n, int sub)) = "<n>_{<sub>}";
str LaTeXGameLog(prop(str n)) = "<n>";
str LaTeXGameLog(propS(str n, int sub)) = "<n>_{<sub>}";