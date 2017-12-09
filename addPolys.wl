(* ::Package::*)Needs["FiniteFields`"]

(*Characteristic of field*)
p = 2;
(*Irreducible polynomial*)
irred = {1, 1, 1};
(*Finite fields package field*)
field = GF[p, irred];
(*Extension of the field*)
m = 1;
(*Order of the multiplicative field*)
d = Length[irred] - 1;
(*Order of multiplicative field*)
ordertheta = d/GCD[d, m];
(**)
ipoly = FieldIrreducible[field, w];

(*Simplify polynomials under current field*)
SimplifyFP[
  p1_] := (ele = 
   ReduceElement[
    PolynomialToElement[field, PolynomialMod[p1, ipoly]]]; 
  Return[If[ele == 0, 0, "Error: Nonzero integer produced", 
    ElementToPolynomial[ele, w]]])

(*Removes leading zeros from vector inputs*)
DropExtra[v1_] := (temp = v1; 
  For[i = Length[v1], i > 1, i--, 
   If[Last[temp] == 0, temp = Most[temp], Return[temp]]]; Return[temp])

(*Add two field elements*)
AddElements[e1_, e2_] := 
 ReduceElement[
  PolynomialToElement[field, 
   PolynomialMod[
    ElementToPolynomial[e1, w] + ElementToPolynomial[e2, w], ipoly]]]

(*Add two polynomials under current field*)
AddFP[p1_, p2_] := SimplifyFP[p1 + p2]

(*Multiply two polynomials*)
MultFP[p1_, p2_] := SimplifyFP[p1*p2]

(*Raise a polynomial to power exp*)
ExpFP[p1_, exp_] := SimplifyFP[p1^Mod[exp, p^d - 1]]

(*Add two field elements represented by vectors*)
AddP[v1_, v2_] := 
 DropExtra[
  Map[Function[x, SimplifyFP[x]], 
   If[Length[v1] < Length[v2], 
    Join[v1, Table[0, {i, Length[v2] - Length[v1]}]] + v2, 
    v1 + Join[v2, Table[0, {i, Length[v1] - Length[v2]}]]]]]

(*Subtract two field elements represented by vectors*)
SubP[v1_, v2_] := AddP[v1, -1*v2]

(*Multiply two field elements*)
MultP[v1_, v2_] := 
 DropExtra[
  Map[Function[x, SimplifyFP[x]], 
   vector = Table[0, {i, Length[v1] + Length[v2] - 1}]; 
   For[j = 1, j <= Length[v2], j++, 
    For[i = 1, i <= Length[v1], i++, 
     vector[[j + i - 1]] = 
      vector[[j + i - 1]] + v1[[i]]*ThetanFP[v2[[j]], i - 1]]]; 
   vector]]

(*Returns inverse of field polynomial*)
InvFP[p1_] := ExpFP[p1, -1]

(*Returns frobenius automorphism of field polynomial*)
FrobFP[p1_] := ExpFP[p1, p]

(*Applies frobenius automorphism m times to polynomial*)
ThetaFP[p1_] := Nest[FrobFP, p1, m]

(*Applies frobenius automorphism n times to polynomial*)
ThetanFP[p1_, n_] := 
 If[n == 0, SimplifyFP[p1], Nest[ThetaFP, p1, Mod[n, ordertheta]]]

(*Applies frobenius automorphism to vector*)
ThetaP[v1_] := DropExtra[Map[ThetaFP, v1]]

(*Applies frobenius automorphism n times to vector*)
ThetanP[v1_, n_] := DropExtra[Map[Function[x, ThetanFP[x, n]], v1]]

(*Divides two polynomials on the right side*)
RightDivide[num_, den_] := (remainder = num; 
  ret = Table[0, {i, Length[num] - Length[den] + 1}]; 
  For[i = 1, i < Length[num] - Length[den] + 2, 
   i++, (check = i; 
    ret[[Length[remainder] - Length[den] + 1]] = 
     ThetanFP[Last[remainder]*InvFP[Last[den]], 
      ordertheta - Length[den] + 1]; 
    remainder = SubP[remainder, MultP[den, ret[[1 ;; -i]]]]; 
    i = check;)]; Return[{ret, remainder}])
