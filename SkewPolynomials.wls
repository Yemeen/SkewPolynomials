#!/usr/bin/env wolframscript
(* ::Package:: *)

(* ::Input:: *)
(*<<FiniteFields`*)


(* ::Input:: *)
(*(* This package is terrible says the mathematica community. Try to use as little as possible??*)*)


(* ::Input:: *)
(*randpoly[x_,p_,deg_]:= Table[Random[Integer,{0,p-1}],{deg}].Table[x^j,{j,0,deg-1}]+x^deg*)


(* ::Input:: *)
(*getIrreducible[x_,p_,deg_]:= Catch[Module[{poly},While[True,poly=randpoly[x,p,deg];If[Length[FactorList[poly, Modulus -> p]] ==2, Throw[poly]];]]]*)


(* ::Input:: *)
(**)
(**)
(*(*Example*)*)


(* ::Input:: *)
(*p = 5;*)
(*deg = 3;*)
(*SeedRandom[1121]*)
(*irred=getIrreducible[x,p,deg]*)


(* ::Input:: *)
(*(*Zech logs representation or how mathematica described it*)*)


(* ::Input:: *)
(*isPrimitive[lin_, poly_, p_, deg_, facs_] := Catch[(For[j=1, j<= Length[facs], j++, If[PolynomialMod[lin^facs[[j]],{poly,p}]===1,Throw[False]];];True)]*)


(* ::Input:: *)
(*getPrimitivePolynomials[x_,p_,deg_] := Catch[Module[{j,irred,facs},facs = (p^deg-1)/Map[First, FactorInteger[p^deg-1]]];While[True, irred = getIrreducible[x,p,deg]; *)
(*If[isPrimitive[x,irred,p,deg,facs],*)
(*Throw[CoefficientList[irred, x]]]*)
(*];*)
(*]*)


(* ::Input:: *)
(**)


(* ::Input:: *)
(*defPoly = getPrimitivePolynomials[x,p,deg]*)
