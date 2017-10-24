(* ::Package:: *)

<<FiniteFields`


AddElements[fld_,e1_,e2_]:=ReduceElement[PolynomialToElement[fld,ElementToPolynomial[e1,w]+ElementToPolynomial[e2,w]]]


AddPolynomials[fld_,p1_,p2_]:=ElementToPolynomial[ReduceElement[PolynomialToElement[fld,p1+p2]],w]
