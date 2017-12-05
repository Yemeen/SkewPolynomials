(* ::Package:: *)

Needs["FiniteFields`"]


p=2;
irred={1,1,0,0,1};
field=GF[p,irred];
m=3;
d=Length[irred]-1;
ordertheta=d/GCD[d,m];

ipoly=FieldIrreducible[field,w];


SimplifyFP[p1_]:=(ele=ReduceElement[PolynomialToElement[field,PolynomialMod[p1,ipoly]]];Return[If[ele==0,0,"Error: Nonzero integer produced",ElementToPolynomial[ele,w]]])


DropExtra[v1_]:=(temp=v1;For[i=Length[v1],i>1,i--,If[Last[temp]==0,temp=Most[temp],Return[temp]]];Return[temp])


AddElements[e1_,e2_]:=ReduceElement[PolynomialToElement[field,PolynomialMod[ElementToPolynomial[e1,w]+ElementToPolynomial[e2,w],ipoly]]]


AddFP[p1_,p2_]:=SimplifyFP[p1+p2]


MultFP[p1_,p2_]:=SimplifyFP[p1*p2]


ExpFP[p1_,exp_]:=SimplifyFP[p1^Mod[exp,p^d-1]]


AddP[v1_,v2_]:=DropExtra[Map[Function[x,SimplifyFP[x]],If[Length[v1]<Length[v2],Join[v1,Table[0,{i,Length[v2]-Length[v1]}]]+v2,v1+Join[v2,Table[0,{i,Length[v1]-Length[v2]}]]]]]


SubP[v1_,v2_]:=AddP[v1,-1*v2]


MultP[v1_,v2_]:=Map[Function[x,SimplifyFP[x]],vector=Table[0,{i,Length[v1]+Length[v2]-1}];For[j=1,j<=Length[v2],j++,For[i=1,i<=Length[v1],i++,vector[[j+i-1]]=vector[[j+i-1]]+v1[[i]]*ThetanFP[v2[[j]],i-1]]];vector]


InvFP[p1_]:=ExpFP[p1,-1]


FrobFP[p1_]:=ExpFP[p1,p]


ThetaFP[p1_]:=Nest[FrobFP,p1,m]


ThetanFP[p1_,n_]:=If[n==0,SimplifyFP[p1],Nest[ThetaFP,p1,Mod[n,ordertheta]]]


ThetaP[v1_]:=DropExtra[Map[ThetaFP,v1]]


ThetanP[v1_,n_]:=DropExtra[Map[Function[x,ThetanFP[x,n]],v1]]


RightDivide[num_,den_]:=(temp=num;ret[[Length[temp]-Length[den]+1]]=ThetanFP[Last[temp]*InvFP[Last[den]],ordertheta-Length[den]+1];temp=SubP[temp,ret[[Length[temp]-Length[den]+1]]*den])
