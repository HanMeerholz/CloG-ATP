module ATP::PostProcess

import CloG_Base::GLASTs;
import ATP::ATP_Base;

CloGProof replaceUnusedClos(CloGProof proof) {
	return visit(proof) {
		case subProof:CloGUnaryInf(_, clo(CloGName n), CloGProof inf): {
			if (/disClo(_, n) !:= inf) {
				insert replaceCloAt(subProof, n);
			}
		}
	}
}

CloGProof replaceCloAt(CloGProof proof, CloGName name) {
	proof.rule = dIterR();

	return visit(proof) {
		case subP:CloGUnaryInf(CloGSequent seq, _, _): {
			CloGSequent newSeq = [];
			for (term <- seq) {
				if (t:term(_, list[CloGName] label, _) := term) {
					t.label = label - name;
					newSeq += t;
				}
			}
			subP.seq = newSeq;
			insert subP;
		}
		case subP:CloGBinaryInf(CloGSequent seq, _, _): {
			CloGSequent newSeq = [];
			for (term <- seq) {
				if (t:term(_, list[CloGName] label, _) := term) {
					t.label = label - name;
					newSeq += t;
				}
			}
			subP.seq = newSeq;
			insert subP;
		}
		case subP:disClo(CloGSequent seq, _): {
			CloGSequent newSeq = [];
			for (term <- seq) {
				if (t:term(_, list[CloGName] label, _) := term) {
					t.label = label - name;
					newSeq += t;
				}
			}
			subP.seq = newSeq;
			insert subP;
		}
	}
}