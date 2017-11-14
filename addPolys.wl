(* ::Package::*)

Needs["FiniteFields`"]


p=2;
irred={1,1,0,0,1};
field=GF[p,irred];
m=3;
d=Length[irred]-1;
ordertheta=d/GCD[d,m];

ipoly=FieldIrreducible[field,w];


AddElements[e1_,e2_]:=ReduceElement[PolynomialToElement[field,PolynomialMod[ElementToPolynomial[e1,w]+ElementToPolynomial[e2,w],ipoly]]]


AddFP[p1_,p2_]:=ElementToPolynomial[ReduceElement[PolynomialToElement[field,PolynomialMod[p1+p2,ipoly]]],w]


MultFP[p1_,p2_]:=ElementToPolynomial[ReduceElement[PolynomialToElement[field,PolynomialMod[p1*p2,ipoly]]],w]


ExpFP[p1_,exp_]:=ElementToPolynomial[ReduceElement[PolynomialToElement[field,PolynomialMod[p1^Mod[exp,p^d-1],ipoly]]],w]


AddP[v1_,v2_]:=Map[Function[x,ElementToPolynomial[ReduceElement[PolynomialToElement[field,PolynomialMod[x,ipoly]]],w]],If[Length[v1]<Length[v2],Join[v1,Table[0,{i,Length[v2]-Length[v1]}]]+v2,v1+Join[v2,Table[0,{i,Length[v1]-Length[v2]}]]]]


MultP[v1_,v2_]:=Map[Function[x,ele=ReduceElement[PolynomialToElement[field,PolynomialMod[x,ipoly]]];If[ele==0,0,"Error: Nonzero integer produced",ElementToPolynomial[ele,w]]],vector=Table[0,{i,Length[v1]+Length[v2]-1}];For[j=1,j<=Length[v2],j++,For[i=1,i<=Length[v1],i++,vector[[j+i-1]]=vector[[j+i-1]]+v1[[i]]*v2[[j]]]];vector]


InvFP[p1_]:=ExpFP[p1,-1]


FrobFP[p1_]:=ExpFP[p1,p]


ThetaFP[p1_]:=Nest[FrobFP,p1,m]


ThetanFP[p1_,n_]:=Nest[ThetaFP,p1,Mod[n,ordertheta]]


ThetaP[v1_]:=Map[ThetaFP,v1]


ThetanP[v1_,n_]:=Map[Function[x,ThetanFP[x,n]],v1]
