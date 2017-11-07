(* ::Package:: *)

Needs["FiniteFields`"]


p=2
irred={1,1,0,0,1}
field=GF[p,irred]
m=2
d=Length[irred]-1

ipoly=FieldIrreducible[field,w]


AddElements[e1_,e2_]:=ReduceElement[PolynomialToElement[field,PolynomialMod[ElementToPolynomial[e1,w]+ElementToPolynomial[e2,w],ipoly]]]


AddFP[p1_,p2_]:=ElementToPolynomial[ReduceElement[PolynomialToElement[field,PolynomialMod[p1+p2,ipoly]]],w]


MultFP[p1_,p2_]:=ElementToPolynomial[ReduceElement[PolynomialToElement[field,PolynomialMod[p1*p2,ipoly]]],w]


ExpFP[p1_,exp_]:=ElementToPolynomial[ReduceElement[PolynomialToElement[field,PolynomialMod[p1^Mod[exp,p^d-1],ipoly]]],w]

InvFP


AddP[v1_,v2_]:=Map[Function[x,ElementToPolynomial[ReduceElement[PolynomialToElement[field,PolynomialMod[x,ipoly]]],w]],If[Length[v1]<Length[v2],Join[v1,Table[0,{i,Length[v2]-Length[v1]}]]+v2,v1+Join[v2,Table[0,{i,Length[v1]-Length[v2]}]]]]


MultP[v1_,v2_]:=Map[Function[x,PolynomialMod[x,ipoly]],If[Length[v1]<Length[v2],vect=KroneckerProduct[Join[v1,Table[0,{i,Length[v2]-Length[v1]}]],v2];For[i=0,i<Length[vect],i++,vect[[i+1]]=Join[Table[0,i],vect[[i+1]]]];vect,vect=KroneckerProduct[v1,Join[v2,Table[0,{i,Length[v1]-Length[v2]}]]];For[i=0,i<Length[vect],i++,vect[[i+1]]=Join[Table[0,i],vect[[i+1]]]];vect]]
