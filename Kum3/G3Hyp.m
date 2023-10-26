// Arithmetic of genus 3 hyperelliptic curves and their Kummer varieties
// M. Stoll
// Started 2011-12-10

// A hyperelliptic curve of genus 3 is given by an equation
//  y^2 = f(x) = f8*x^8 + f7*x^7 + ... + f1*x + f0

import "G3HypHelp.m": K3quartics, K3deltas, Xipolynomials, K3biquforms, K3xi2coeffs;

// We store the data with the curve

declare attributes CrvHyp:
 KummerEquations, KummerVariety, KummerDeltas, KummerXipols, KummerBQF, HeightTable;

declare verbose ReducedBasis, 2;

declare verbose FindPointsG3, 3;

intrinsic KummerVarietyG3(C::CrvHyp : Ambient := "") -> Sch
{Construct the Kummer variety associated to the genus 3 hyperelliptic curve C.}
  if assigned C`KummerVariety then
    return C`KummerVariety;
  elif assigned C`KummerEquations then
    if Ambient cmpeq "" then
      Ambient := ProjectiveSpace(Universe(C`KummerEquations));
    end if;
    K := Scheme(Ambient, C`KummerEquations);
    C`KummerVariety := K;
    return K;
  else
    if Ambient cmpeq "" then
      Ambient := ProjectiveSpace(BaseRing(C), 7);
    end if;
    require Genus(C) eq 3: "The curve must be of genus 3.";
    f, h := HyperellipticPolynomials(C);
    require h eq 0: "The curve must have the form y^2 = f(x).";
    fs := Coefficients(f);
    fs cat:= [0 : i in [#fs+1..9]];
    quartics := K3quartics(fs : Ring := CoordinateRing(Ambient));
    quad := P.1*P.8 - P.2*P.7 + P.3*P.6 - P.4*P.5 where P := Universe(quartics);
    C`KummerEquations := [quad] cat quartics;
    K := Scheme(Ambient, C`KummerEquations);
    C`KummerVariety := K;
    return K;
  end if;
end intrinsic;

intrinsic KummerOrigin(C::CrvHyp) -> Pt
{Return the origin on the Kummer variety of the curve C.}
  return KummerVarietyG3(C)![0,0,0,0,0,0,0,1];
end intrinsic;

intrinsic Double(C::CrvHyp, P::Pt) -> Pt
{Double the point P on the Kummer variety of C.}
  if assigned C`KummerDeltas then
    deltas := C`KummerDeltas;
    R := Universe(deltas);
  else
    require Genus(C) eq 3: "The curve must be of genus 3.";
    f, h := HyperellipticPolynomials(C);
    require h eq 0: "The curve must have the form y^2 = f(x).";
    fs := Coefficients(f);
    fs cat:= [0 : i in [#fs+1..9]];
    R := assigned C`KummerEquations
           select Universe(C`KummerEquations)
           else PolynomialRing(Universe(fs), 8);
    deltas := K3deltas(fs : Ring := R);
    C`KummerDeltas := deltas;
  end if;
  P2 := [Evaluate(d, s) : d in deltas] where s := Eltseq(P);
  K := KummerVarietyG3(C : Ambient := ProjectiveSpace(R));
  return K!P2;
end intrinsic;

intrinsic KummerXi(C::CrvHyp, P::Pt) -> RngElt
{Computes the value of Xi on the given coordinates of P.}
  if assigned C`KummerXipols then
    Xipols := C`KummerXipols;
  else
    require Genus(C) eq 3: "The curve must be of genus 3.";
    f, h := HyperellipticPolynomials(C);
    require h eq 0: "The curve must have the form y^2 = f(x).";
    fs := Coefficients(f);
    fs cat:= [0 : i in [#fs+1..9]];
    R := assigned C`KummerEquations
           select Universe(C`KummerEquations)
           else PolynomialRing(Universe(fs), 8);
    Xipols := Xipolynomials(fs : Ring := R);
    C`KummerXipols := Xipols;
  end if;
  i := 1; while P[i] eq 0 do i +:= 1; end while;
  return Evaluate(Xipols[i], Eltseq(P))/P[i];
end intrinsic;

intrinsic PseudoAdd(C::CrvHyp, P1::Pt, P2::Pt, P3::Pt) -> Pt
{Given the images on the Kummer variety of C of points P, Q, P-Q on the
Jacobian of C, returns the image of P+Q.}
  L12 := Eltseq(P1) cat Eltseq(P2);
  L3 := Eltseq(P3);
  // i := K`SelectCoordinate(L3);
  i := 1; while L3[i] eq 0 do i +:= 1; end while;
  if assigned C`KummerBQF then
    BB := C`KummerBQF;
  else
    require Genus(C) eq 3: "The curve must be of genus 3.";
    f, h := HyperellipticPolynomials(C);
    require h eq 0: "The curve must have the form y^2 = f(x).";
    fs := Coefficients(f);
    fs cat:= [0 : i in [#fs+1..9]];
    BB := K3biquforms(fs);
    C`KummerBQF := BB;
  end if;
  Xi := KummerXi(C, P1)*KummerXi(C, P2);
  signs := [1,-1,1,-1,-1,1,-1,1];
  c1 := 2*L3[i]; c2 := Evaluate(BB[i,i], L12);
  L := [ c1*(Evaluate(BB[i,j], L12) + (i+j eq 9 select signs[i]*Xi else 0))
          - L3[j]*c2 : j in [1..8] ];
  return KummerVarietyG3(C)!L;
  // Check if point really is on K here, since third argument might
  // not be image of P-Q.
end intrinsic;

intrinsic Multiple(C::CrvHyp, n::RngIntElt, P::Pt) -> Pt
{The n-th multiple of P on the Kummer variety of the curve C.}
  if n eq 0 then return KummerOrigin(C); end if;
  m := Abs(n);
  Px := KummerOrigin(C); Py := P; Pz := P;
  // invariants: Px = ax*P, Py = ay*P, Pz = az*P with
  //  ax + ay = az  and  ax + m*az = n .
  while true do
    if IsOdd(m) then
      Px := PseudoAdd(C, Px, Pz, Py);
    else
      Py := PseudoAdd(C, Py, Pz, Px);
    end if;
    m div:= 2;
    if m eq 0 then return Px; end if;
    Pz := Double(C, Pz);
  end while;
end intrinsic;

intrinsic PseudoAddMultiple(C::CrvHyp, P1::Pt, P2::Pt, P3::Pt, n::RngIntElt) -> Pt
{Given the images on the Kummer variety of the curve C of points P, Q, P-Q on the
Jacobian, returns the image of P+n*Q.}
  if n lt 0 then
    P3 := PseudoAdd(C, P1, P2, P3); n := -n;
  end if;
  while true do
    // This is a variant of the multiplication algorithm above.
    if IsOdd(n) then
      P1 := PseudoAdd(C, P1, P2, P3);
    else
      P3 := PseudoAdd(C, P3, P2, P1);
    end if;
    n div:= 2;
    if n eq 0 then return P1; end if;
    P2 := Double(P2);
  end while;
end intrinsic;

intrinsic ToKummerVariety(P::JacHypPt : twist := 1, Kum := "UNIQUE") -> Pt
{Returns the image of P on the Kummer variety of its parent (genus 3).}
  Ct := Curve(Parent(P));
  C := twist eq 1 select Ct else HyperellipticCurve(HyperellipticPolynomials(Ct)/twist);
  K := Kum cmpeq "UNIQUE" select KummerVarietyG3(C) else Kum;
  fpol := HyperellipticPolynomials(C);
  F := BaseRing(Parent(fpol));
  apol := P[1];
  bpol := P[2];
  deg := P[3];
  assert deg eq Degree(apol); // only odd degree genus 3 Jacobians are implemented
  cpol := ExactQuotient(bpol^2 - fpol*twist, apol);
  if deg eq 0 then
    return K![0,0,0,0,0,0,0,1];
  elif deg eq 1 then
    a0, a1 := Explode(Coefficients(apol));
    coords := [F| 0, 0, 0, 0, a1^2, a0*a1, a0^2];
    G := 2*Coefficient(fpol, 8)*a0^4 - a1*Coefficient(fpol, 7)*a0^3;
    Append(~coords, -G/a1^2);
    return K!coords;
  elif deg eq 2 then
    a0, a1, a2 := Explode(Coefficients(apol));
    b0, b1 := Explode([Coefficient(bpol, j) : j in [0..1]]);
    coords := [F| 0, a2^2, a1*a2, a0*a2, a1^2 - a0*a2, a0*a1, a0^2];
    if a1^2 ne 4*a0*a2 then
      // two distinct points
      G := 2*&+[Coefficient(fpol, 2*j)*a0^j*a2^(4-j) : j in [0..4]]
            - a1*&+[Coefficient(fpol, 2*j+1)*a0^j*a2^(3-j) : j in [0..3]];
      y1y2 := (b1^2*a0 - b0*b1*a1 + b0^2*a2)/twist;
      Append(~coords, (2*y1y2 - G)/(a1^2 - 4*a0*a2));
    else
      f0,f1,f2,f3,f4,f5,f6,f7,f8 := Explode([Coefficient(fpol, j) : j in [0..8]]);
      s0,s1,s2 := Explode([a2,a1,a0]);
      cof1 := 4*f0*s0^4 - 2*f1*s0^3*s1 + 4*f2*s0^3*s2 - 2*f3*s0^2*s1*s2
               + 4*f4*s0^2*s2^2 - 2*f5*s0*s1*s2^2 + 4*f6*s0*s2^3 - 2*f7*s1*s2^3
               + 4*f8*s2^4;
      assert cof1 ne 0;
      cof0 := (-4*f0*f2 + f1^2)*s0^6 + 4*f0*f3*s0^5*s1 - 2*f1*f3*s0^5*s2
               - 4*f0*f4*s0^4*s1^2 + (-4*f0*f5 + 4*f1*f4)*s0^4*s1*s2
               + (-4*f0*f6 + 2*f1*f5 - 4*f2*f4 + f3^2)*s0^4*s2^2 + 4*f0*f5*s0^3*s1^3
               + (8*f0*f6 - 4*f1*f5)*s0^3*s1^2*s2
               + (8*f0*f7 - 4*f1*f6 + 4*f2*f5)*s0^3*s1*s2^2
               + (-2*f1*f7 - 2*f3*f5)*s0^3*s2^3 - 4*f0*f6*s0^2*s1^4
               + (-12*f0*f7 + 4*f1*f6)*s0^2*s1^3*s2
               + (-16*f0*f8 + 8*f1*f7 - 4*f2*f6)*s0^2*s1^2*s2^2
               + (8*f1*f8 - 4*f2*f7 + 4*f3*f6)*s0^2*s1*s2^3
               + (-4*f2*f8 + 2*f3*f7 - 4*f4*f6 + f5^2)*s0^2*s2^4
               + 4*f0*f7*s0*s1^5 + (16*f0*f8 - 4*f1*f7)*s0*s1^4*s2
               + (-12*f1*f8 + 4*f2*f7)*s0*s1^3*s2^2 + (8*f2*f8 - 4*f3*f7)*s0*s1^2*s2^3
               + (-4*f3*f8 + 4*f4*f7)*s0*s1*s2^4 - 2*f5*f7*s0*s2^5 - 4*f0*f8*s1^6
               + 4*f1*f8*s1^5*s2 - 4*f2*f8*s1^4*s2^2 + 4*f3*f8*s1^3*s2^3
               - 4*f4*f8*s1^2*s2^4 + 4*f5*f8*s1*s2^5 + (-4*f6*f8 + f7^2)*s2^6;
      Append(~coords, -cof0/cof1);
    end if;
    return K!coords;
  else
    assert deg eq 3;
    a0,a1,a2,a3 := Explode(Coefficients(apol));
    b0 := Coefficient(bpol, 0);
    b1 := Coefficient(bpol, 1);
    b2 := Coefficient(bpol, 2);
    c0 := Coefficient(cpol, 0);
    c1 := Coefficient(cpol, 1);
    c2 := Coefficient(cpol, 2);
    c3 := Coefficient(cpol, 3);
    c4 := Coefficient(cpol, 4);
    coords := [F| twist, -a2*c4, -a1*c4, -a0*c4, -a0*c4 - a1*c3 - a3*c1,
                  -a0*c3 - a3*c0, 2*b0*b2 - a0*c2 - a2*c0];
    Append(~coords, (coords[2]*coords[7] - coords[3]*coords[6] + coords[4]*coords[5])/twist);
    return K!coords;
  end if;
end intrinsic;

function ToJacobian(J, Apol, Bpol, Cpol);
  // J = Jacobian of C : y^2 = f = Bpol^2 - Apol*Cpol
  // Apol, Bpol, Cpol polynomials of degree <= 4
  if Degree(Apol) eq 4 then
    // change divisor to get smaller degree
    if Degree(Cpol) lt 4 then
      Apol := Cpol;
      Bpol *:= -1;
    else
      cofs := [Coefficient(Apol, 4), Coefficient(Bpol, 4), Coefficient(Cpol, 4)];
      flag, sqrtdisc := IsSquare(cofs[2]^2 - cofs[1]*cofs[3]);
      assert flag;
      mu := (-cofs[2] + sqrtdisc)/cofs[3];
      Apol +:= 2*mu*Bpol + mu^2*Cpol;
      assert Degree(Apol) lt 4;
      Bpol +:= mu*Cpol;
    end if;
  end if;
  // now deg(Apol) le 3
  Apol *:= 1/LeadingCoefficient(Apol);
  Bpol := Bpol mod Apol;
  return elt<J | Apol, Bpol, Degree(Apol)>;
end function;

intrinsic Points(J::JacHyp, pol::RngUPolElt : d := Degree(pol)) -> SetIndx[JacHypPt]
{Returns as an indexed set all points on the hyperelliptic Jacobian J whose first component
is the given polynomial pol and whose last component is d.}
  require d le Dimension(J): "The degree cannot be larger than the genus.";
  fact := Factorization(pol);
  f, h := HyperellipticPolynomials(Curve(J));
  require h eq 0: "Need a curve of the form y^2 = f(x).";
  require d ge Degree(pol): "d must be >= deg(pol).";
  if d gt Degree(pol) then
    require IsEven(Degree(f)): "d > deg(pol) ==> no Weierstrass point at infinity.";
  end if;
  if IsOdd(d) then
    require IsOdd(Degree(f)): "odd d ==> need Weierstrass point at infinity.";
  end if;
  R := BaseRing(J);
  if IsOdd(Degree(f)) or forall{a : a in fact | IsEven(Degree(a[1]))} then
    ptsJ := [];
    for a in fact do
      if Degree(a[1]) eq 1 then
        flag, b := IsSquare(Evaluate(f, -Coefficient(a[1],0)/Coefficient(a[1],1)));
        if not flag then return {@ @}; end if; // no point possible
        Append(~ptsJ, a[2]*elt<J | a[1], Parent(a[1])![b], 1>);
      else
        K := ext<R | a[1]>;
        assert Evaluate(a[1], K.1) eq 0;
        flag, b := IsSquare(Evaluate(f, K.1));
        if not flag then return {@ @}; end if; // no point possible
        Append(~ptsJ, a[2]*elt<J | a[1], Parent(a[1])!Eltseq(b), Degree(a[1])>);
      end if;
    end for;
    if d gt Degree(pol) then
      ptsinf := PointsAtInfinity(Curve(J));
      if #ptsinf ne 2 then return {@ @}; end if;
      Append(~ptsJ, ExactQuotient(d - Degree(pol), 2)*(ptsinf[1] - ptsinf[2]));
    end if;
    // combine
    result := {@ J!0 @};
    for pt in ptsJ do
      result := {@ rpt + pt : rpt in result @} join {@ rpt - pt : rpt in result @};
    end for;
    return {@ pt : pt in result | pt[1] eq pol and pt[3] eq d @};
  else
    if Dimension(J) eq 2 then
      return Points(J, pol, d);
    end if;
    // should work in Pic/<m>
    require false: "This case is not yet implemented.";
  end if;
end intrinsic;

intrinsic LiftToJacobian(C::CrvHyp, P::Pt : twist := 1) -> SetIndx[JacHypPt]
{Given a point P on the Kummer variety associated to C, returns the rational points
on the Jacobian of C that map to P.}
  assert Parent(P) eq KummerVarietyG3(C)(BaseRing(C));
  Ct := twist eq 1 select C else QuadraticTwist(C, twist);
  xiseq := Eltseq(P);
  f := HyperellipticPolynomials(C);
  Pol := Parent(f);
  f0,f1,f2,f3,f4,f5,f6,f7,f8 := Explode([Coefficient(f, i) : i in [0..8]]);
  if xiseq[1] ne 0 then
    // normalize first coordinate to be 1
    x2,x3,x4,x5,x6,x7 := Explode([xi/xiseq[1] : xi in xiseq[2..7]]);
    // set up matrix
    mat := Matrix([[2*f0,        f1,        x7,        x6,   x4],
                   [  f1, 2*(f2-x7),     f3-x6,     x5-x4,   x3],
                   [  x7,     f3-x6, 2*(f4-x5),     f5-x3,   x2],
                   [  x6,     x5-x4,     f5-x3, 2*(f6-x2),   f7],
                   [  x4,        x3,        x2,        f7, 2*f8]]);
    // test minors
    for s in Subsets({1..5}, 3) do
      ss := Setseq(s);
      submat := Matrix([[mat[i,j] : j in ss] : i in ss]);
      minor := Determinant(submat);
      if minor ne 0 then
        flag, sqrtmin := IsSquare(-1/2*minor*twist);
        if flag then
          // point should lift
          // find kernel (dim = 2)
          kermat := KernelMatrix(mat);
          assert NumberOfRows(kermat) eq 2;
          trmat := Matrix([kermat[1], kermat[2]]
                           cat [Parent(kermat[1]) |
                                Vector([i eq j select 1 else 0 : i in [1..5]])
                                 : j in ss]);
          // parametrize the conic
          Con := Conic(submat);
          para := Parametrization(Con);
          pareqn := DefiningPolynomials(para);
          P2 := Universe(pareqn);
          mat1 := Matrix([[MonomialCoefficient(eqn, mon)
                            : mon in [P2.1^2, P2.1*P2.2, P2.2^2]]
                           : eqn in pareqn]);
          trmat := Matrix([[i le 2 or j le 2 select (i eq j select 1 else 0)
                                             else mat1[j-2,i-2]
                              : j in [1..5]] : i in [1..5]])
                    * trmat;
          // now trmat*mat*Transpose(trmat) has constant times antidiag(1,-2,1)
          // in its lower right 3x3 submatrix and zeros elsewhere
          // up to constant factor
          trmat := Transpose(trmat^-1)*sqrtmin;
          Apol := Pol!Eltseq(trmat[3]);
          Bpol := Pol!Eltseq(trmat[4]);
          Cpol := Pol!Eltseq(trmat[5]);
          flag, qu := IsDivisibleBy(f, Bpol^2 - Apol*Cpol);
          assert flag;
          flag, sqrtqu := IsSquare(qu*twist);
          assert flag;
          Apol *:= sqrtqu;
          Bpol *:= sqrtqu;
          Cpol *:= sqrtqu;
          // now normalize to have deg(Apol) le 3
          ptJ := ToJacobian(Jacobian(Ct), Apol, Bpol, Cpol);
          return {@ ptJ, -ptJ @};
        else
          // point does not lift
          return {@ @};
        end if;
      end if;
    end for;
    // all minors vanish ==> 2-torsion point
    // find kernel (dim = 3)
    for s in Subsets({1..5}, 2) do
      ss := Setseq(s);
      submat := Matrix([[mat[i,j] : j in ss] : i in ss]);
      minor := Determinant(submat);
      if minor ne 0 then
        kermat := KernelMatrix(mat);
        assert NumberOfRows(kermat) eq 3;
        trmat := Matrix([kermat[1], kermat[2], kermat[3]]
                          cat [Parent(kermat[1]) |
                                Vector([i eq j select 1 else 0 : i in [1..5]])
                                : j in ss]);
        pol := Pol![submat[2,2], 2*submat[1,2], submat[1,1]];
        mat1 := IdentityMatrix(BaseRing(trmat), 5);
        if Degree(pol) eq 1 then
          mat1[5,4] := -Coefficient(pol, 0);
          mat1[5,5] := Coefficient(pol, 1);
        else
          roots := [r[1] : r in Roots(pol)];
          assert #roots eq 2;
          mat1[4,4] := roots[1];
          mat1[4,5] := 1;
          mat1[5,4] := roots[2];
          mat1[5,5] := 1;
        end if;
        trmat := mat1*trmat;
        trmat := Transpose(trmat^-1);
        Apol := Pol!Eltseq(trmat[4]);
        Cpol := Pol!Eltseq(trmat[5]);
        flag, scal := IsDivisibleBy(f*twist, Apol*Cpol);
        assert flag;
        return {@ ToJacobian(Jacobian(Ct), scal*Apol, Pol!0, Cpol) @};
        end if;
    end for;
  elif xiseq[2] ne 0 then
    // xi1 = 0, xi2 /= 0 : degree 2 point
    // get polynomial A
    Apol := Pol![xiseq[4]/xiseq[2], xiseq[3]/xiseq[2], 1];
    cands := Points(Jacobian(Ct), Apol); // get possible points
    return {@ pt : pt in cands | ToKummerVariety(pt : twist := twist, Kum := Parent(P)) eq P @};
  else // degree 1 point (0 : 0 : 0 : 0 : 1 : -x0 : x0^2 : ...)
    assert xiseq[3] eq 0 and xiseq[4] eq 0;
    if xiseq[5] eq 0 then
      // origin
      assert xiseq[6] eq 0 and xiseq[7] eq 0;
      return {@ Jacobian(C)!0 @};
    else
      x0 := -xiseq[6]/xiseq[5];
      flag, y0 := IsSquare(Evaluate(f*twist, x0));
      if flag then
        ptJ := elt<Jacobian(Ct) | Pol.1 - x0, Pol!y0, 1>;
        return {@ ptJ, -ptJ @};
      else
        return {@ @};
      end if;
    end if;
  end if;
  return {@ @};
end intrinsic;

// Heights

function normalize(seq)
  seq := [Integers() | a*x : x in seq] where a := LCM([Denominator(x) : x in seq]);
  seq := [ExactQuotient(x,b) : x in seq] where b := GCD(seq);
  return seq;
end function;

intrinsic NaiveHeight(C::CrvHyp, P::Pt) -> FldReElt
{The naive height of the point P on the Kummer variety of C.}
  s := Eltseq(P);
  assert Universe(s) cmpeq Rationals();
  return Log(Max(normalize(s)));
end intrinsic;

intrinsic NaiveHeightG3(P:JacHypPt) -> FldReElt
{The naive height of the point P on a genus 3 hyperelliptic Jacobian.}
  return NaiveHeight(Curve(Parent(P)), ToKummerVariety(P));
end intrinsic;

intrinsic CanonicalHeightG3(P::JacHypPt : Precision := 0) -> FldReElt
{Computes the canonical height of P. The genus must be 3.}
  return CanonicalHeight(Curve(Parent(P)), ToKummerVariety(P) : Precision := Precision);
end intrinsic;

// The following is necessary so that the intrinsic Precision can be
// accessed inside some of the functions below that have an argument called "Precision"
MyPrec := func<R | Precision(R)>;

function kummerXi(C, P)
  if assigned C`KummerXipols then
    Xipols := C`KummerXipols;
  else
    f := HyperellipticPolynomials(C);
    fs := Coefficients(f);
    fs cat:= [0 : i in [#fs+1..9]];
    R := assigned C`KummerEquations
           select Universe(C`KummerEquations)
           else PolynomialRing(Universe(fs), 8);
    Xipols := Xipolynomials(fs : Ring := R);
    C`KummerXipols := Xipols;
  end if;
  v, i := Min([Valuation(s) : s in P]);
  return Evaluate(Xipols[i], Eltseq(P))/P[i];
end function;

function kummerBB(C)
  if assigned C`KummerBQF then
    BB := C`KummerBQF;
  else
    f := HyperellipticPolynomials(C);
    fs := Coefficients(f);
    fs cat:= [0 : i in [#fs+1..9]];
    BB := K3biquforms(fs);
    C`KummerBQF := BB;
  end if;
  return BB;
end function;

function kummerD(C)
  if assigned C`KummerDeltas then
    deltas := C`KummerDeltas;
    R := Universe(deltas);
  else
    f := HyperellipticPolynomials(C);
    fs := Coefficients(f);
    fs cat:= [0 : i in [#fs+1..9]];
    R := assigned C`KummerEquations
           select Universe(C`KummerEquations)
           else PolynomialRing(Universe(fs), 8);
    deltas := K3deltas(fs : Ring := R);
    C`KummerDeltas := deltas;
  end if;
  return deltas;
end function;

intrinsic HeightConstAtInfty(f::RngUPolElt : eps := 0.0001) -> FldReElt, SeqEnum
{}
  partitions := [<s, {1..7} diff s> : s in Subsets({1..7}, 3)];
  roots := [r[1] : r in Roots(f, ComplexField())];
  vprintf JacHypHeight, 2: " Roots of f:\n";
  if GetVerbose("JacHypHeight") ge 2 then
    Cprt<i> := ComplexField(15);
    for r in roots do printf "   %o\n", Cprt!r; end for;
    delete Cprt;
  end if;
  lcf := Abs(LeadingCoefficient(f));
  // Find a bound for the local height constant at infinity
  function step(ds)
    aseq := [0.0 : i in [1..8]];
    PC := PolynomialRing(ComplexField());
    X := PC.1;
    for pi in partitions do
      p1 := pi[1]; p2 := pi[2];
      spol := &*[X - roots[i] : i in p1];
      tpol := &*[X - roots[i] : i in p2];
      s4, s3, s2, s1 := Explode(Coefficients(spol)); s0 := 0;
      t4, t3, t2, t1, t0 := Explode(Coefficients(tpol));
      st02 := s2*t0 + s0*t2;
      st03 := s3*t0 + s0*t3;
      st04 := s4*t0 + s0*t4;
      st13 := s3*t1 + s1*t3;
      st14 := s4*t1 + s1*t4;
      st24 := s4*t2 + s2*t4;
      // find bound on absolute value of y_T, making use of the fact that delta(x) is real
      // and bounded in absolute value component-wise by ds
      cofs := [lcf*st02*ds[7], lcf*st03*ds[6], lcf*st04*ds[5],
               lcf*(st04+st13)*ds[4], lcf*st14*ds[3], lcf*st24*ds[2],
               lcf^2*(st02*st24 - st03*st14 + st04*(st04+st13))*ds[1]];
      b := Sqrt(Max([Modulus(ds[8] + e1*cofs[1] + e2*cofs[2] + e3*cofs[3] + e4*cofs[4]
                                         + e5*cofs[5] + e6*cofs[6] + e7*cofs[7])
                                        : e1,e2,e3,e4,e5,e6,e7 in [1,-1]]));
//       b := Sqrt(ds[8] + lcf*(Modulus(st02)*ds[7] + Modulus(st03)*ds[6] + Modulus(st04)*ds[5]
//                         + Modulus(st04 + st13)*ds[4] + Modulus(st14)*ds[3] + Modulus(st24)*ds[2])
//                   + lcf^2*Modulus(st02*st24 - st03*st14 + st04*(st04+st13))*ds[1]);
      res := lcf^4*&*[roots[i] - roots[j] : i in p1, j in p2];
      rr := Modulus(b/(8*res));
      // get coefficients \upsilon_j(T)
      xicof := K3xi2coeffs(spol, lcf*tpol);
      for j := 1 to 8 do
        aseq[j] +:= rr*Modulus(xicof[j]);
      end for;
    end for;
    return [Sqrt(a) : a in aseq];
  end function;
  ds := [1.0 : i in [1..8]];
  bsum := 0.0;
  n := 1;
  ds := step(ds);
  maxd := Max(ds);
  bsum +:= 4^n*Log(maxd);
  ds := [d/maxd : d in ds];
  bound := bsum/(4^n-1);
  vprintf JacHypHeight, 2: "  first bound: %o\n", ChangePrecision(bound, 6);
  repeat
    n +:= 1;
    ds := step(ds);
    maxd := Max(ds);
    bsum +:= 4^n*Log(maxd);
    ds := [d/maxd : d in ds];
    oldbound := bound;
    bound := bsum/(4^n-1);
    vprintf JacHypHeight, 2: "  new bound: %o\n", ChangePrecision(bound, 6);
    assert bound le oldbound;
  until oldbound - bound lt eps;
  return bound;
end intrinsic;

intrinsic HeightConstantG3(J::JacHyp) -> FldReElt, FldReElt
{If J is the Jacobian of a genus 3 curve defined over the rationals,
 of the form  y^2 = f(x)  with integral coefficients, this computes
 a real number c such that  h_K(P) le h(P) + c  for all P in J(Q),
 where h_K is the naive logarithmic height got from the Kummer surface
 and h is the canonical height on J.}
  C := Curve(J);
  require Genus(C) eq 3 and CoefficientRing(C) cmpeq Rationals():
          "HeightConstant is only implemented",
          "for Jacobians of genus 2 curves over the rationals.";
  f, h := HyperellipticPolynomials(C);
  require h eq 0 and &and[ Denominator(c) eq 1 : c in Coefficients(f)]:
          "HeightConstant needs a curve of the form  y^2 = f(x), ",
          "where f has integral coefficients.";
  if assigned J`HeightConst then
    return J`HeightConst[1], J`HeightConst[2];
  end if;
  assert Degree(f) eq 7;
  vprintf JacHypHeight, 1: "Find height constant for J =\n%o\n", J;
  hc_inf := HeightConstAtInfty(f);
  vprintf JacHypHeight, 1: " Bound for height constant at infinity:\n";
  vprintf JacHypHeight, 1: "   %o\n", hc_inf;
  // Now find a bound for the finite part
  disc := Integers()!Abs(Discriminant(C)/2^12); // this is |disc(F)|
  c := GCD(ChangeUniverse(Eltseq(f), Integers()));
  disc1 := ExactQuotient(64*disc, c^10);
  hc_finite := Log(disc1)/3;
  vprintf JacHypHeight, 1: " Bound for finite part of height constant:\n";
  vprintf JacHypHeight, 1: "   %o\n", hc_finite;
  vprintf JacHypHeight, 1: " Result infinite + finite is\n  %o\n\n",
          hc_inf + hc_finite;
  // Determine upper bound for |delta(P)|/|P|^4 at infinity
  deltas := kummerD(C);
  hc_inf_both := Max(hc_inf,
                     1/3*Log(Max([Abs(t) : t in &cat[Coefficients(d) : d in deltas]])));
  J`HeightConst := <hc_finite + hc_inf, hc_inf_both>;
  return hc_finite + hc_inf, hc_inf_both;
end intrinsic;

// The following does the "pseudo-addition" on a Kummer variety over a p-adic field
// directly on the coordinate sequences.
// This avoids error messages and should be more efficient, since no algebraic-geometric
// objects need to be constructed.
function MyPseudoAdd(C, P1, P2, P3)
  // C = genus 3 hyp. curve (over Q), P1, P2, P3 coordinate sequences in a p-adic field.
  // Returns normalized coordinates for P1+P2 (assuming P3 = P1-P2)
  // and the relative precision of the result.
  // (Compare $MAGMA_ROOT/package/Geometry/CrvG2/kummer.m)
  BB := kummerBB(C);
  Xi := kummerXi(C, P1)*kummerXi(C, P2);
  P12 := P1 cat P2;
  v, i := Min([Valuation(s) : s in P3]);
  signs := [1,-1,1,-1,-1,1,-1,1];
  c1 := 2*P3[i]; c2 := Evaluate(BB[i,i], P12);
  L := [ c1*(Evaluate(BB[i,j], P12) + (i+j eq 9 select signs[i]*Xi else 0))
           - P3[j]*c2 : j in [1..8] ];
  v := Min([Valuation(s) : s in L]);
  sh := UniformizingElement(Universe(P1))^-v;
  return [s * sh : s in L], Min([AbsolutePrecision(s) - v : s in L]);
end function;

intrinsic CanonicalHeight(C::CrvHyp, P::Pt : Precision := 0, Check := true) -> FldReElt
{Computes the canonical height of P on the Kummer variety of C.}
  // Some checks
  R := BaseRing(C);
  TR := Type(R);
  require TR eq FldRat:
          "CanonicalHeight for genus 3 is only implemented for the rationals as base field.";
  f := HyperellipticPolynomials(C);
  require forall{c : c in Coefficients(f) | Denominator(c) eq 1}:
          "Defining polynomial of the curve must have integral coefficients.";
  if not assigned C`HeightTable then
    C`HeightTable := AssociativeArray(Parent(P));
  end if;
  if Precision le 0 then
    Precision := MyPrec(RealField()); // use default precision
  end if;
  if IsDefined(C`HeightTable, P) then
    ht, prec := Explode(C`HeightTable[P]);
    if prec ge Precision then
      return ChangePrecision(ht, Precision);
    end if;
  end if;
  P1s := normalize(Eltseq(P));
  vprintf JacHypHeight: "CanonicalHeight: P = %o\n", P1s;
  K := KummerVarietyG3(C); // the Kummer variety on which P lies
  D := kummerD(C);   // the sequence consisting of the eight duplication polynomials
  Rs := RealField(Precision+5); // work with slightly higher precision
  if P eq KummerOrigin(C) then
    vprintf JacHypHeight: " P = 0, so height is zero.\n";
    return ChangePrecision(Rs!0, Precision);
  end if;
  // Find the mu_p(P) for the bad primes
  P2s := [ Integers() | Evaluate(D[j], P1s) : j in [1..8]]; // double of P
  g2 := GCD(P2s);
  P2s := [ExactQuotient(a, g2) : a in P2s];
  P4s := [Integers() | Evaluate(d, P2s) : d in D]; // twice double of P
  g4 := GCD(P4s);  // g2 and g4 contain exactly the bad primes for P
  bad := Set(PrimeDivisors(g2)) join Set(PrimeDivisors(g4));
  vprintf JacHypHeight: " Bad primes: %o\n", bad;
  // For each bad prime,
  // compute multiples m*P over Q_p until epsilon_p(m*P) = 0
  // and m*P is on the component of the origin.
  sum := 0; // this is used to accumulate the finite contribution of the correction
  safety := 5; // minimal relative p-adic precision during the computation
  for p in bad do
    function normp(seq)
      i := 0; repeat i +:= 1; until seq[i] ne 0;
      return [s/seq[i] : s in seq];
    end function;
    vprintf JacHypHeight, 2: "  computing contribution at p = %o...\n", p;
    fmodp := PolynomialRing(GF(p))!f;
    issq := fmodp ne 0 and IsSquare(fmodp);
    // default p-adic precision used is twice the following
    precp := Valuation(Discriminant(C), p) + (p eq 2 select 20 else 2);
    flag := false; // flag will be set if computation with given precision was successful
    Fp := GF(p);
    Dp := ChangeUniverse(D, PolynomialRing(Fp, 8)); // used for checking epsilon = 0
    repeat
      precp *:= 2; // double p-adic precision after each unsuccessful attempt
      vprintf JacHypHeight, 2: "    current %o-adic precision is %o\n", p, precp;
      // table will be [0, eps_p(P), eps_p(2*P), ..., eps_p((n-1)*P]
      // where eps_p(n*P) = 0 with n*P on component of origin and n is minimal with this property
      v := Valuation(g2, p);
      table := [0, v];
      Qp := pAdicField(p, precp);
      m := 1;
      Pp := ChangeUniverse(Eltseq(P), Qp);    // work with coordinate sequences in Qp
      mP := Pp;                               // m*P
      mP1 := [Qp | 0, 0, 0, 0, 0, 0, 0, 1];   // (m-1)*P
      mP2 := [Qp | s*p^-v : s in P2s];        // 2*m*P
      mP3, pr := MyPseudoAdd(C, mP2, Pp, Pp); // (2*m+1)*P
      if pr le safety then continue; end if;  // restart with higher precision
      repeat
        m +:= 1;
        Ptemp, pr := MyPseudoAdd(C, mP, Pp, mP1); // compute (m+1)*P
        if pr le safety then break; end if; // restart with higher precision
        mP1 := mP;                                  // new (m-1)*P
        mP := Ptemp;                                // new m*P
        P2ms := [Evaluate(D[j], mP) : j in [1..8]]; // double of m*P
        v := Min([Valuation(s) : s in P2ms]);       // this is eps_p(m*P)
        pr := Min([AbsolutePrecision(s) : s in P2ms]);
        if pr-v le safety then break; end if; // restart with higher precision
        mP2 := [a*p^-v : a in P2ms];             // normalize mP2
        mP3, pr := MyPseudoAdd(C, mP2, Pp, mP3); // new (2*m+1)*P
        if pr le safety then break; end if; // restart with higher precision
        if v eq 0 then
          vprintf JacHypHeight, 2: "    %o*P has epsilon_p = 0\n", m;
          if issq then
            // need to check if point is on irred. component of origin
            if exists{d : d in Dp | Evaluate(d, seq) ne 0}
                where seq := ChangeUniverse(mP2, Fp) then
              vprintf JacHypHeight, 2: "         and is on component of origin\n";
              if Check then
                // check that mu really is zero
                step := func<seq | normp([Evaluate(d, seq) : d in Dp])>;
                s1 := ChangeUniverse(mP2, Fp); s2 := step(s1);
                repeat s1 := step(s1); s2 := step(step(s2)); until s1 eq s2;
              end if;
              flag := true;
              break;
            else
              vprintf JacHypHeight, 2: "         but is not on component of origin\n";
            end if;
          else
            // table is complete (we can only get here when m <= 3)
            if Check then
              // check that mu really is zero
              step := func<seq | normp([Evaluate(d, seq) : d in Dp])>;
              s1 := ChangeUniverse(mP2, Fp); s2 := step(s1);
              repeat s1 := step(s1); s2 := step(step(s2)); until s1 eq s2;
            end if;
            flag := true;
            break;
          end if;
        end if;
        // Check if eps_p(2*m*P) = 0 or eps_p((2*m+1)*P) = 0
        // by computing delta(..*P) mod p.
        // If so (and the relevant multiple of P is on the component of the origin),
        // we can complete table by symmetry.
        if exists{d : d in Dp | Evaluate(d, seq) ne 0}
             where seq := ChangeUniverse(mP2, Fp) then
          vprintf JacHypHeight, 2:
                  "    %o*P has epsilon_p = 0 (found at m = %o)\n", 2*m, m;
          if issq then
            seq2 := [Evaluate(d, seq) : d in Dp] where seq := ChangeUniverse(mP2, Fp);
            if exists{d : d in Dp | Evaluate(d, seq2) ne 0} then
              vprintf JacHypHeight, 2: "         and is on component of origin\n";
              table := table cat [v] cat table[m..2 by -1];
              if Check then
                // check that mu really is zero
                step := func<seq | normp([Evaluate(d, seq) : d in Dp])>;
                s1 := ChangeUniverse(mP2, Fp); s2 := step(s1);
                repeat s1 := step(s1); s2 := step(step(s2)); until s1 eq s2;
              end if;
              flag := true;
              break;
            else
              vprintf JacHypHeight, 2: "         but is not on component of origin\n";
            end if;
          else
            table := table cat [v] cat table[m..2 by -1];
            if Check then
              // check that mu really is zero
              step := func<seq | normp([Evaluate(d, seq) : d in Dp])>;
              s1 := ChangeUniverse(mP2, Fp); s2 := step(s1);
              repeat s1 := step(s1); s2 := step(step(s2)); until s1 eq s2;
            end if;
            flag := true;
            break;
          end if;
        end if;
        if exists{d : d in Dp | Evaluate(d, seq) ne 0}
             where seq := ChangeUniverse(mP3, Fp) then
          vprintf JacHypHeight, 2:
                  "    %o*P has epsilon_p = 0 (found at m = %o)\n", 2*m+1, m;
          if issq then
            seq2 := [Evaluate(d, seq) : d in Dp] where seq := ChangeUniverse(mP3, Fp);
            if exists{d : d in Dp | Evaluate(d, seq2) ne 0} then
              vprintf JacHypHeight, 2: "         and is on component of origin\n";
              table := table cat [v, v] cat table[m..2 by -1];
              if Check then
                // check that mu really is zero
                step := func<seq | normp([Evaluate(d, seq) : d in Dp])>;
                s1 := ChangeUniverse(mP3, Fp); s2 := step(s1);
                repeat s1 := step(s1); s2 := step(step(s2)); until s1 eq s2;
              end if;
              flag := true;
              break;
            else
              vprintf JacHypHeight, 2: "         but is not on component of origin\n";
            end if;
          else
            table := table cat [v, v] cat table[m..2 by -1];
            if Check then
              // check that mu really is zero
              step := func<seq | normp([Evaluate(d, seq) : d in Dp])>;
              s1 := ChangeUniverse(mP3, Fp); s2 := step(s1);
              repeat s1 := step(s1); s2 := step(step(s2)); until s1 eq s2;
            end if;
            flag := true;
            break;
          end if;
        end if;
        // Otherwise we extend table.
        Append(~table, v);
      until flag;
    until flag;
    vprintf JacHypHeight, 2: "  p = %o: table is %o\n", p, table;
    // compute contribution and add it to sum
    sum_p := 0;
    m_p := #table;
    r := Valuation(m_p, 2); // length of pre-period
    for n := 0 to r-1 do
      sum_p +:= table[1 + (2^n mod m_p)]/4^(n+1);
    end for;
    // now find periodic part
    n2_start := 2^r mod m_p;
    n2 := n2_start;
    c := 0;
    sum1 := 0;
    repeat
      sum1 +:= table[1 + (n2 mod m_p)]/4^c;
      c +:= 1;
      n2 := (2*n2) mod m_p;
    until n2 eq n2_start;
    // now c is the length of the period (= multiplicative order of 2 mod m_p/2^r)
    sum_p +:= 4^(-r-1)/(1 - 4^(-c))*sum1;
    vprintf JacHypHeight: "  p = %o: contribution is %o*log(%o).\n", p, -sum_p, p;
    sum -:= sum_p*Log(Rs!p);
  end for;

  // compute infinite part
  prec := Precision;
  delta := Rs!1/10^Precision;
  Rs0 := Rs;
//   eqn := DefiningPolynomial(K);
  // Determine how many iterations are necessary
  _, hc_inf := HeightConstantG3(Jacobian(C));
  bound := Ceiling(((Precision+5)*Log(10) + Log(hc_inf))/Log(4));
  vprintf JacHypHeight, 2: " Current precision = %o decimal digits\n", Precision;
  vprintf JacHypHeight, 2: " Bound for mu_infty = %o\n", hc_inf;
  vprintf JacHypHeight, 2:
          "  ==> need %o iterations for infinite part.\n", bound;
  repeat
    flag := true;
    one := Rs0!1;
    Pol := PolynomialRing(Rs0);
    x := Pol.1;
    // Convert into (floating-point!) real numbers
    s := [one*t : t in P1s];
    // Normalize such that the sup-norm is 1
    norm := Max([Abs(t) : t in s]);
    for j := 1 to 8 do s[j] /:= norm; end for;
    // The following gives a slight speed improvement
    // but is bad for numerical stability! - MS
//       D := ChangeUniverse(D, ChangeRing(Parent(D[1]), Rs0));
//       D := [one*d : d in D];
    // The height (of P) is the naive height plus mu_infty(P) plus the finite
    // part,
    // where mu_infty(Q) = sum_{n ge 0} eps_infty(2^n*Q)/4^(n+1)
    // where eps_infty(Q) is the local height constant at infinity at Q.
    ht := Log(norm);
    vprintf JacHypHeight: " Naive height = %o\n",ht;
    sum_inf := 0;
    pow4 := one;
    for n := 1 to bound do
      // double the point
      s := [Evaluate(D[j], s) : j in [1..8]];
      vprintf JacHypHeight, 4: "  precision of s: %o\n", [MyPrec(a) : a in s];
      // Normalize such that the sup-norm is 1
      norm := Max([Abs(t) : t in s]);
      // A safety measure:
      if norm eq 0 then
        vprintf JacHypHeight, 2: "  Precision loss!\n";
        vprintf JacHypHeight, 2:
                "   ==> increase precision and restart computation of infinite part\n";
        prec +:= 5;
        Rs0 := RealField(prec+5);
        bound +:= 5;
        flag := false;
        break n;
      end if;
      for j := 1 to 8 do s[j] /:= norm; end for;
      // add eps_infty
      pow4 *:= 4;
      sum_inf +:= Log(norm) / pow4;
    end for;
  until flag;
  vprintf JacHypHeight: " infinite part = %o.\n", sum_inf;
  height := ht + sum_inf + sum;
  height := ((Precision gt 0) select RealField(Precision)
                              else RealField())!height;
  vprintf JacHypHeight: "height(P) = %o.\n", height;
  C`HeightTable[P] := <height, Precision>;
  return height;
end intrinsic;

intrinsic HeightPairingG3(P::JacHypPt, Q::JacHypPt : Precision := 0) -> FldReElt
{Computes the canonical height pairing of P and Q (on the same Jacobian),
 defined by  <P,Q> := (h(P+Q) - h(P) - h(Q))/2.
 The genus must be 3, and the base field must be the rationals. }
  require Parent(P) eq Parent(Q): "Points must be on the same Jacobian.";
  return (CanonicalHeightG3(P+Q : Precision := Precision)
           - CanonicalHeightG3(P : Precision := Precision)
           - CanonicalHeightG3(Q : Precision := Precision))/2;
end intrinsic;

intrinsic HeightPairingMatrixG3(S::[JacHypPt] : Precision := 0) -> AlgMat
{Given a sequence of points P_i on a Jacobian (of a curve of genus 3
 over the rationals), this returns the matrix  (<P_i, P_j>), where
 < , > is the canonical height pairing. }
  n := #S;
  hs1 := [ CanonicalHeightG3(P : Precision := Precision) : P in S ];
  hs2 := [ [ (CanonicalHeightG3(S[i]+S[j] : Precision := Precision)
                - hs1[i] - hs1[j])/2: i in [1..j-1] ]
           : j in [2..n] ];
  mat := [ (i eq j) select hs1[i] else
           (i lt j) select hs2[j-1,i] else hs2[i-1,j] : i,j in [1..n] ];
  // changed that to not set the coefficient field... MS 2004-10
  // return MatrixRing(RealField(), n)!mat;
  return Matrix(n, mat);
end intrinsic;

intrinsic RegulatorG3(S::[JacHypPt] : Precision := 0) -> FldReElt
{Given a sequence of points on the Jacobian of a genus 3 curve
 over the rationals), this computes the regulator, i.e. the determinant
 of the height pairing matrix. It is zero when the points are dependent
 in the Mordell-Weil group; otherwise it is the square of the volume
 of the parallelotope spanned by the points (in J(Q) tensor R, with the
 canonical height as metrics).}
  J := Universe(S);
  require Dimension(J) eq 3 : "Argument universe must have dimension3.";
  // changed the following -- MS, 2004-10
  R := CoefficientRing(J);
  TR := Type(R);
  require TR eq FldRat :
          "Regulator is only implemented for the rationals as base field.";
   // require Type(BaseField(J)) eq FldRat :
   //   "Argument universe must be defined over the rationals";
   return Determinant(HeightPairingMatrixG3(S : Precision := Precision));
end intrinsic;

intrinsic ReducedBasisG3(ps::[JacHypPt] : Precision := 0) -> SeqEnum, AlgMatElt
  {Computes a reduced basis (with respect to the height pairing) of the
  subgroup in J(Q)/torsion generated by the given points on J.}
  require Dimension(Universe(ps)) eq 3 :
      "Universe of argument must be the Jacobian of a genus 3 curve.";
  C := Curve(Universe(ps));
  if not IsSimplifiedModel(C) then
    C1, m := SimplifiedModel(C);
    ps := [ Evaluate(m,Q) : Q in ps ];
  else
    m := IdentityMap(C);
  end if;
  vprintf ReducedBasis: "ReducedBasis: %o points, prec = %o.\n", #ps, Precision;
  // First compute heights...
  prec := Precision eq 0 select MyPrec(RealField()) else Precision;
  vprintf ReducedBasis: " Computing heights...\n";
  ps := Setseq(Seqset(ps));
  psh := [<pt, CanonicalHeightG3(pt : Precision := prec)> : pt in ps];
  // Some initialisations
  vprintf ReducedBasis: " Initialising...\n";
  gens := [Universe(ps) | ];
  pairing := []; // [ ... [ ... pairing(gen[i],gen[j]) ... ] ... ]
  points := { pt[1] : pt in psh | pt[2] gt 0.5 or Order(pt[1]) eq 0 };
  // Now repeatedly take the point of smallest positive height,
  // adjoin it to the generators, update the pairing matrix,
  // and reduce the remaining points w.r.t. the lattice generated so far.
  mat0 := MatrixRing(RealField(), #gens)!0;
  while not IsEmpty(points) do
    // Find point of smallest height.
    cht := 0;
    for pt in points do
      ht := CanonicalHeightG3(pt : Precision := prec);
      if cht eq 0 or ht lt cht then
        cht := ht; cpt := pt;
      end if;
    end for;
    // Update gens and pairing.
    vprintf ReducedBasis: "  New possible generator %o of height %o\n", cpt, cht;
    Append(~gens, cpt);
    for i := 1 to #gens - 1 do
      val := HeightPairingG3(gens[i], cpt : Precision := prec);
      Append(~pairing[i], val);
    end for;
    Append(~pairing, [ pairing[i, #gens] : i in [1..#gens-1] ] cat [cht]);
    Mat := MatrixRing(RealField(), #gens);
    mat0 := Mat!&cat pairing;
    while not IsPositiveDefinite(mat0) do
      mat0 +:= 0.1^prec*(Mat!1);
    end while;
    // Generate the appropriate lattice.
    L := LatticeWithGram(mat0);
    L1 := LLL(L); B := Basis(L1);
    gens := [ &+[Round(b[i])*gens[i] : i in [1..#gens]] : b in B ];
    new_gens := [];
    for g in gens do
      ht := CanonicalHeightG3(g : Precision := prec);
      if ht gt 0.5 or Order(g) eq 0 then Append(~new_gens, g); end if;
    end for;
    gens := new_gens;
    vprintf ReducedBasis: "  Current generators:\n%o\n", gens;
    pairing := [];
    for i := 1 to #gens do
      for j := 1 to i-1 do
        val := HeightPairingG3(gens[j], gens[i] : Precision := prec);
        Append(~pairing[j], val);
      end for;
      ht := CanonicalHeightG3(gens[i] : Precision := prec);
      Append(~pairing, [ pairing[j, i] : j in [1..i-1] ] cat [ht]);
    end for;
    Mat := MatrixRing(RealField(), #gens);
    mat0 := Mat!&cat pairing;
    V := RSpace(RealField(), #gens);
    vprintf ReducedBasis: "  Current pairing matrix:\n%o\n",
            Matrix([[ChangePrecision(mat0[i,j], 5)
                     : j in [1..#gens]] : i in [1..#gens]]);
    mat := mat0^-1;
    // Project the points into the real space spanned by the lattice,
    // find a close vector and compute the difference.
    newPoints := { Universe(ps) | };
    for pt in points do
      proj := [];
      for i := 1 to #gens do
        proji := HeightPairingG3(gens[i], pt : Precision := prec);
        Append(~proj, proji);
      end for;
      w := (V!proj)*mat;
      v := [ Round(w[i]) : i in [1..#gens] ];
      npt := pt - &+[ Round(v[i])*gens[i] : i in [1..#gens] ];
      nht := CanonicalHeightG3(npt : Precision := prec);
      if nht gt 0.5 or Order(npt) eq 0 then Include(~newPoints, npt); end if;
    end for;
    points := newPoints;
    vprintf ReducedBasis: "  Number of remaining points: %o.\n", #points;
  end while;
  vprintf ReducedBasis: " Generators:\n%o\n", gens;
  return [ Pullback(m,Q) : Q in gens ], mat0;
end intrinsic;

intrinsic ReducedBasisG3(ps::{@JacHypPt@} : Precision := 0) -> SeqEnum, AlgMatElt
  {Computes a reduced basis (with respect to the height pairing) of the
  subgroup in J(Q)/torsion generated by the given points on J. }
  require Dimension(Universe(ps)) eq 3 :
      "Universe of argument must be the Jacobian of a genus 3 curve.";
  return ReducedBasisG3(IndexedSetToSequence(ps) : Precision := Precision);
end intrinsic;

intrinsic ReducedBasisG3(ps::{JacHypPt} : Precision := 0) -> SeqEnum, AlgMatElt
  {Computes a reduced basis (with respect to the height pairing) of the
  subgroup in J(Q)/torsion generated by the given points on J. }
  require Dimension(Universe(ps)) eq 3 :
      "Universe of argument must be the Jacobian of a genus 3 curve.";
  return ReducedBasisG3(SetToSequence(ps) : Precision := Precision);
end intrinsic;

// Point search

function projLattice(L, v)
  // L: lattice, v: primitive vector in L
  // returns the projected lattice L/<v> and a map that lifts to L
  qL, qmap := quo<L | v>;
  assert IsFree(qL); // qL is an abelian group
  bas := [qL.i @@ qmap : i in [1..Ngens(qL)]];
  // compute Gram matrix of quotient lattice
  baspr := [b - (b,v)/(v,v)*v : b in bas];
  L1 := LatticeWithGram(Matrix([[(b1,b2) : b2 in baspr] : b1 in baspr]));
  liftmap := map<L1 -> L | v1 :-> &+[v1[i]*bas[i] : i in [1..#bas]]>;
  return L1, liftmap;
end function;

function collect(L, H, test : primitive := true, factor := 100, count := 3)
  // L: lattice, H: height bound,
  // test: function that applied to lattice point returns an indexed set
  // returns the union of test applied to all primitive lattice points
  // of norm at most H
  result := {@ @};
  dim := Dimension(L);
  svheight := Ceiling(H^(1/dim)); // expected norm of shortest vector
//   vprintf FindPointsG3, 3: " successive minima: %o\n", SuccessiveMinima(L);
  vprintf FindPointsG3, 3: " finding shortest vectors...\n";
  sv := ShortestVectors(L)[1];
  if (sv,sv) lt factor*svheight and dim gt 1 and count gt 0 then
    vprintf FindPointsG3, 2: "  projecting lattice...\n";
    // fairly short shortest vector
    new := test(Eltseq(sv));
    if not IsEmpty(new) then
      vprintf FindPointsG3, 3: "   Found points %o\n", new;
    end if;
    result join:= new;
    // now search on projected lattice
    L1, lift := projLattice(L, sv);
    function newtest(v)
      v1 := lift(v);
      res := {@ @};
      pol := Polynomial(Rationals(), [(v1,v1) - H, 2*(v1,sv), (sv,sv)]);
      rts := [r[1] : r in Roots(pol, RealField())];
      if #rts eq 2 then
        for n := Ceiling(rts[1]) to Floor(rts[2]) do
          res join:= test(v1 + n*sv);
        end for;
      elif #rts eq 1 then
        flag, sqrt := IsSquare(1/LeadingCoefficient(pol)*pol);
        assert flag;
        if Coefficient(sqrt, 0) in Integers() then
          new := test(v1 - (Integers()!Coefficient(sqrt, 0))*sv);
          if not IsEmpty(new) then
            vprintf FindPointsG3, 3: "   Found points %o\n", new;
          end if;
          res join:= new;
        end if;
      end if;
      return res;
    end function;
    result join:= collect(L1, H, newtest : primitive := false, factor := factor, count := count-1);
    return result;
  else
    // lattice is not too skew
    vprintf FindPointsG3, 2: "  running ShortVectorsProcess...\n";
    svproc := ShortVectorsProcess(L, H);
    while not IsEmpty(svproc) do
      v := NextVector(svproc);
      if not primitive or GCD(ChangeUniverse(Eltseq(v), Integers())) eq 1 then
        new := test(v);
        if not IsEmpty(new) then
          vprintf FindPointsG3, 3: "   Found points %o\n", new;
        end if;
        result join:= new;
      end if;
    end while;
  end if;
  return result;
end function;

intrinsic FindRationalPoints(C::CrvHyp, P::Pt, H::RngIntElt : twist := 1, factor := 100, count := 3) -> SetIndx
{Find all rational points on the Jacobian of the Kummer Variety K of multiplicative naive height
at most H whose image on K reduces mod the prime p to P.}
  Ct := twist eq 1 select C else QuadraticTwist(C, twist);
  K := KummerVarietyG3(C);
  eqns := DefiningEquations(K);
  F := Universe(Eltseq(P));
  p := Characteristic(F);
  assert F eq GF(p);
  eqnsF := ChangeUniverse(eqns, PolynomialRing(F, 8));
  vprintf FindPointsG3, 2: "point: %o\n", P;
  vprintf FindPointsG3, 1: "Setting up Jacobian matrix...\n";
  jac := JacobianMatrix(eqnsF);
  vprintf FindPointsG3, 1: " and evaluating it at P...\n";
  jac := Matrix(F, [[Evaluate(jac[i,j], Eltseq(P)) : j in [1..NumberOfColumns(jac)]]
                      : i in [1..NumberOfRows(jac)]]);
  rank := Rank(jac);
  vprintf FindPointsG3, 1: "rank is %o\n", rank;
  Pint := ChangeUniverse(Eltseq(P), Integers());
  if rank lt 4 then
    printf "point is singular. Abort.\n";
//     vprintf FindPointsG3, 1: "point is singular. Abort.\n";
//     i := 1;
//     while P[i] ne 1 do i +:= 1; end while;
//     assert i le 8;
//     P8<[x]> := Universe(eqns);
//     evseq1 := [Pint[j] + p*(j lt i select x[j] else j gt i select x[j-1] else 0)
//                : j in [1..8]];
//     quad := 1/p*Evaluate(eqns[1], evseq1);
//     quadF := Universe(eqnsF)!quad;
//     assert TotalDegree(quadF) eq 1;
//     k := 1;
//     while MonomialCoefficient(quadF, Parent(quadF).k) eq 0 do k +:= 1; end while;
//     // solve for x[k]
//     solxk := &+[j eq k select 0
//                        else Integers()!MonomialCoefficient(quadF, Parent(quadF).j)*x[j]
//                  : j in [1..7]];
//     evseq2 := [j eq k select p*x[k] - solxk else x[j] : j in [1..8]];
//     evseq := [Evaluate(e, evseq2) : e in evseq1];
//     eqns1 := [Evaluate(e, evseq) : e in eqns];
//     eqns1 := [1/p^Min([Valuation(c, p) : c in Coefficients(e)])*e : e in eqns1];
//     PF7 := PolynomialRing(F, 7);
//     toPF7 := hom<Universe(eqnsF) -> PF7 | [PF7.i : i in [1..7]]  cat [0]>;
//     eqns1F := [toPF7(Universe(eqnsF)!e) : e in eqns1];
//     vprintf FindPointsG3, 1: "computing points on blow-up...\n";
//     var := Variety(ideal<PF7 | eqns1F>);
//     vprintf FindPointsG3, 1: " ...%o points\n", #var;
    result := {@ Jacobian(Ct) | @};
//     for pt in var do
//       P := [pt[i] : i in [1..7]];
//       jac := JacobianMatrix(eqns1F);
//       jac := Matrix(F, [[Evaluate(jac[i,j], P) : j in [1..NumberOfColumns(jac)]]
//                          : i in [1..NumberOfRows(jac)]]);
//       rank := Rank(jac);
//       if rank lt 4 then
//         vprintf FindPointsG3, 1: "new rank is %o -- too small. Skip.\n", rank;
//       else
//         Pint := ChangeUniverse(P, Integers());
//
//       end if;
//     end for;
    return result;
  end if;
  as := -Vector(F, [F| ExactQuotient(Evaluate(eqn, Pint), p) : eqn in eqns]);
  vprintf FindPointsG3, 1: "solving linear system...\n";
  sol, ker := Solution(Transpose(jac), as);
  vprintf FindPointsG3, 1: "...done\n";
  sol := ChangeRing(sol, Integers());
  Pint := Vector(Pint) + p*sol;
  vprintf FindPointsG3, 1: "setting up lattice...\n";
  L := Lattice(Matrix([Eltseq(Pint)]
                       cat [Eltseq(p*ChangeRing(b, Integers())) : b in Basis(ker)]
                       cat [[i eq j select p^2 else 0 : j in [1..8]] : i in [1..8]]));
  function test(v)
    if GCD(ChangeUniverse(Eltseq(v), Integers())) eq 1
        and forall{e : e in eqns | Evaluate(e, Eltseq(v)) eq 0} then
      return LiftToJacobian(C, K!Eltseq(v) : twist := twist);
    else
      return {@ Jacobian(Ct) | @};
    end if;
  end function;
  vprintf FindPointsG3, 1: "collecting points...\n";
  result := collect(L, 8*H^2, test : factor := factor, count := count);
  vprintf FindPointsG3, 1: "... found %o points on J\n", #result;
  return result;
end intrinsic;

