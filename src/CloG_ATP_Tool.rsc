module CloG_ATP_Tool
/*
 * Main module for the automated theorem prover tool
 */
 
import CloGSyntax;
import GLASTs;
import CST2AST_CloG;
import LaTeXOutput;

// Get the location of an input .seq file.
loc inputLoc(str file) {
	return (|project://CloG-ATP/input| + file)[extension=".seq"];
}

// Form the location for an output .tex file
loc outputLoc(str file) {
	return (|project://CloG-ATP/output| + file)[extension=".tex"];
}