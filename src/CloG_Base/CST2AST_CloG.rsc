module CloG_Base::CST2AST_CloG
/*
 * A module containing functions to transform the CloG input to an abstract syntax tree
 */

import String;

import CloG_Base::CloGSyntax;
import CloG_Base::GLASTs;

/* Main function for syntax conversion
 *
 * Input:  Parsed CloG input sequent syntax
 * Output: CloGSequent algebraic type for whole proof
 */
CloGSequent cst2astCloG(start[SCloGSequent] ss){
	SCloGSequent s = ss.top;
	
	return [ cst2astCloG(t) | SCloGTerm t <- s.seq ];
}

/* Function for syntax conversion of a CloG term. Conversion called on the proposition and list reduction used to convert label
 *
 * Input: Concrete syntax CloG term
 * Output: CloG term algebraic type
 */
CloGTerm cst2astCloG(SCloGTerm t){
	return term(cst2astCloG(t.ex), [id2name(n) | SId n <- t.label], false);
}

/* Function for syntax conversion of a normal form game logic propositional formula. Switch statement used to identify which
 * operator is used.
 *
 * Input: Concrete syntax game expression
 * Output: Game logic proposition algebraic type
 */
GameLog cst2astCloG(SCloGExpr exp){
	switch (exp){
		case(SCloGExpr)`~ <SId p>`: 
			return neg(atomP(id2prop(p)));
		case(SCloGExpr)`<SId p>`: 
			return atomP(id2prop(p));
		case(SCloGExpr)`( <SCloGExpr ex> )`: 
			return cst2astCloG(ex);
		case(SCloGExpr)`\< <SCloGGame g> \> <SCloGExpr ex>`: 
			return \mod(cst2astCloG(g), cst2astCloG(ex));
		case(SCloGExpr)`<SCloGExpr exL> & <SCloGExpr exR>`:
			return and(cst2astCloG(exL), cst2astCloG(exR));
		case(SCloGExpr)`<SCloGExpr exL> | <SCloGExpr exR>`:
			return or(cst2astCloG(exL), cst2astCloG(exR));
		default: throw "Unsupported Game Logic Formula";
	}
}

/* Function for syntax conversion of a normal form game formula. Switch statement used to identify which
 * operator is used.
 *
 * Input: Concrete syntax game expression
 * Output: Game algebraic type
 */
Game cst2astCloG(SCloGGame g){
	switch (g){
		case (SCloGGame)`<SId a> ^d`: 
			return dual(atomG(id2agame(a)));
		case (SCloGGame)`<SId a>`: 
			return atomG(id2agame(a));
		case (SCloGGame)`( <SCloGGame ga> )`: 
			return cst2astCloG(ga);
		case (SCloGGame)`<SCloGExpr ex> ?`: 
			return \test(cst2astCloG(ex));
		case (SCloGGame)`<SCloGExpr ex> !`: 
			return dTest(cst2astCloG(ex));
		case (SCloGGame)`<SCloGGame ga> *`: 
			return iter(cst2astCloG(ga));
		case (SCloGGame)`<SCloGGame ga> ^x`: 
			return dIter(cst2astCloG(ga));
		case (SCloGGame)`<SCloGGame gaL> ; <SCloGGame gaR>`: 
			return concat(cst2astCloG(gaL), cst2astCloG(gaR));
		case (SCloGGame)`<SCloGGame gaL> && <SCloGGame gaR>`: 
			return dChoice(cst2astCloG(gaL), cst2astCloG(gaR));
		case (SCloGGame)`<SCloGGame gaL> || <SCloGGame gaR>`: 
			return choice(cst2astCloG(gaL), cst2astCloG(gaR));
		default: throw "Unsupported Game Formula";
	}
}

/* ID conversion functions need different names as they use the same concrete syntax type. Is more modular
 * than a larger switch statement.
 *
 * Input: Concrete syntax for an identifier
 * Output: Algebraic the corresponding atom or name
 */

// Function for syntax conversion of a Clo rule name
CloGName id2name(SId n){
	switch (n) {
		case (SId)`<Id id> _ <Int sub>`:
			return nameS("<id>",toInt("<sub>"));
		case (SId)`<Id id>`:
			return name("<id>");
		default: throw "Unsupported Name";
	}
}

// Function for syntax conversion of an atomic proposition
Prop id2prop(SId p){
	switch (p){
		case (SId)`<Id id> _ <Int sub>`:
			return propS("<id>",toInt("<sub>"));
		case (SId)`<Id id>`:
			return prop("<id>");
		default: throw "Unsupported Proposition";
	}
}

// Function for syntax conversion of an atomic game
AGame id2agame(SId a){
	switch (a){
		case (SId)`<Id id> _ <Int sub>`:
			return agameS("<id>",toInt("<sub>"));
		case (SId)`<Id id>`:
			return agame("<id>");
		default: throw "Unsupported Proposition";
	}
}