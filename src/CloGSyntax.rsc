module CloGSyntax
/* 
 * Module defines the concrete syntax for the input of a CloG proof
 *
 * Converted to abstract syntax tree by CST2AST_CloG module
 */ 

extend lang::std::Layout;
extend lang::std::Id;
	
/*
 * A seq file starts with "Seq" and consists of a list of labeled formulae, represented as CloG terms wrapped by [].
 */
start syntax SCloGSequent
	= "Seq" "[" SCloGTerm* seq "]";

/*
 * Each CloG term is defined as a CloG expression (a game logic formula in normal form) with a superscript label
 *
 * The label is defined as a list of named Id's wrapped by [].
 */
syntax SCloGTerm
	= SCloGExpr ex "^" "[" SId* label "]";

// Syntax definition of normal form game logic expression used in CloG
syntax SCloGExpr
	= prop: SId p
	| not: "~" SId p
	> left par: "(" SCloGExpr ex ")"
	> right strat: "\<" SCloGGame g "\>" SCloGExpr ex
	> left and: SCloGExpr exL "&" SCloGExpr exR
	> left or: SCloGExpr exL "|" SCloGExpr exR;

// Syntax definition of normal form game expression used in CloG
syntax SCloGGame
	= agame: SId g
	| dual: SId g "^d"
	> left par: "(" SCloGGame ga ")"
	> left \test: SCloGExpr ga "?"
	> left dTest: SCloGExpr ga "!"
	> left iter: SCloGGame ga "*"
	> left dIter: SCloGGame ga "^x"
	> left con: SCloGGame gaL ";" SCloGGame gaR
	> left dChoice: SCloGGame gaL "&&" SCloGGame gaR
	> left choice: SCloGGame gaL "||" SCloGGame gaR;
	
// Syntax definition of a named ID which can have a subscript integer
// Used for atomic games, atomic propositions, and Clo rule names
syntax SId
	= Id n "_" Int sub
	| Id n;

// Regular Expression definition for an integer that can be used for an ID subscript
lexical Int
	= [1-9][0-9]*
	| [0];