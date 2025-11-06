/*
	Stratification of mu-constant plane branch deformations by the poles of the complex zeta function
*/

//######################
//### Input/settings
//######################

quitWhenFinished           := true;
printDeformationProcess    := false;
printParameterOptions      := true;
printCandidatesLong        := false;
stratificationVerboseLevel := "default"; // "none" "default" "onlyStrata" "detailed"
printResultsAfterCompute   := false;
printApijInResults         := false;

curve                      := "deformation_restricted";
semigroupFromAbcd          := false; // Curves with coinciding candidates (2 characteristic exponents)
semigroup                  := [15,21,175];
abcd                       := [4,5,9,1]; // a>=2, b>=a+1, c>=2, d>=1, {a,b,c} pairwise coprime, {c,d} coprime
whichEquations             := [1, 1];
deformationParameters      := [];

useDefaultCandidates       := [true, true];
nusIfNotDefaultCandidates  := [[], []];
includeTopologicalRootsOfGeometricOriginInDefaultCandidates := false;
includeUndeterminedRootsInDefaultCandidates := true;

// OVERRIDE SETTINGS
predefinedSettings         := "5732";
case predefinedSettings:
	when "5732":
		curve                     := "deformation_restricted";
		semigroupFromAbcd         := true;
		abcd                      := [5,7,3,2];
		deformationParameters     := [2,62];
		useDefaultCandidates      := [false, false];
		nusIfNotDefaultCandidates := [[10,11],[4,9]];
	when "3871":
		curve                     := "deformation_restricted";
		semigroupFromAbcd         := true;
		abcd                      := [3,8,7,1];
		deformationParameters     := [0,126];
		useDefaultCandidates      := [false, false];
		nusIfNotDefaultCandidates := [[2,6], [3,35]];
	when "4571":
		curve                     := "deformation_restricted";
		semigroupFromAbcd         := true;
		abcd                      := [4,5,7,1];
		deformationParameters     := [0,97,98];
		useDefaultCandidates      := [false, false];
		nusIfNotDefaultCandidates := [[2,4], [5,21]];
	when "4591":
		curve                     := "deformation_restricted";
		semigroupFromAbcd         := true;
		abcd                      := [4,5,9,1];
		deformationParameters     := [0,129];
		useDefaultCandidates      := [false, false];
		nusIfNotDefaultCandidates := [[2,4],[9,29]];
end case;

// semigroup
// [15,21,175]
// [5,12]
// [15,21,175]
// [18,48,146,441]
// [36,96,292,881]
// [5,7]
// [6,17]
// [4,6,13]
// [4,10,21]
// [6,9,22]
// [6,14,43]
// [8,18,73]
// [10,15,36]
// [10,24,121]
// [36,96,292,881]
// [8,12,26,53] 2-3|2-3|2-3
// [12,16,50,101] 3-4|2-3|2-3
// [12,18,38,115] 2-3|3-4|2-3
// [12,18,39,79]  2-3|2-3|3-4
// [18,45,93,281] 2-5|3-4|3-5 t=[1,73,235] nus=[[], [1,3,4], [2,3,5]];

// abcd
// [5,7,3,2]
// [17,19,7,6]
// [7,9,4,3]

// deformationParameters
// [1,73,235] [2,62] [0,2,95,96,98] [95,96,98] [17] [4,5] [7] [32] [35,36,37,38] "all" []

//##########################
//### Basic requirements
//##########################
AttachSpec("../SingularitiesDim2/IntegralClosureDim2.spec");
AttachSpec("../ZetaFunction/ZetaFunction.spec");
Z := IntegerRing(); Q := RationalField();


//#########################
//### Curve/deformation
//#########################

originalCurveString := curve;
assumeNonzero := {};
if semigroupFromAbcd then
	a,b,c,d := Explode(abcd); semigroup := [a*c,b*c,a*b*(c+d)];
end if;
printf "\n";
// Definition of:
//   - R: the base ring
//   - P = R[x,y]
//   - f: a polynomial in P with a singularity at (0,0)
//   - gs: the sequence of polynomials which separate from f at the i-th rupture divisor
case curve:
	when "2_3":
		P<x,y> := LocalPolynomialRing(Q, 2);
		R := BaseRing(P);
		f := x^3 - y^2;
		gs := [f];
	when "3-7_testing":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 1), 2);
		R<t1> := BaseRing(P);
		f := -x^7 + t1*x^5*y + y^3;
		gs := [f];
	when "5-7": // 5-7 - deform 4
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 4), 2);
		R<t_1,t_4,t_6,'t_{11}'> := BaseRing(P);
		f := 1/7*x^7 + 1/5*y^5 - t_1*x^3*y^3-t_4*x^5*y^2-t_6*x^4*y^3-'t_{11}'*x^5*y^3;
		gs := [f];
	when "4-9": // 4-9 - deform 4
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 4), 2);
		R<t_1,t_2,t_6,'t_{10}'> := BaseRing(P);
		f := -(x^9/9+y^4/4) + t_1*x^7*y+t_2*x^5*y^2+t_6*x^6*y^2+'t_{10}'*x^7*y^2;
		gs := [f];
	when "6-7": // 6-7 - deform 6
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 6), 2);
		R<u_1,u_2,u_3,u_8,u_9,'u_{15}'> := BaseRing(P);
		f := x^6 + y^7 + u_1*x^2*y^5 + u_2*x^3*y^4 + u_3*x^4*y^3 + u_8*x^3*y^5 + u_9*x^4*y^4 + 'u_{15}'*x^4*y^5;
		gs := [f];
	when "n-m": // n-m - deform ? - Generic curve construction with 1 characteristic exponent
		n := 3;
		m := 7;
		//n := StringToInteger(n); //m := n+1;
		curve := Sprint(n)*"-"*Sprint(m);
		Deformation := DeformationCurve([n,m]);
		f := Deformation[1];
		PDeformation := Parent(f);
		totalDim := Rank(PDeformation);
		T := totalDim-2;
		if T gt 0 then
			P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, T), 2);
			R := BaseRing(P);
			tNames := ["t"*Sprint(i) : i in [1..T]];
			AssignNames(~R, tNames);
			ts := [P | R.i : i in [1..T]];
			f := Evaluate(f, ts cat [x,y]);
			gs := [f];
		else
			P<x,y> := LocalPolynomialRing(Q, 2);
			R := BaseRing(P);
			f := Evaluate(f, [x,y]);
			gs := [f];
		end if;
	when "4-6-13":
		R<t_0,t_1> := RationalFunctionField(Q, 3);
		P<x,y> := LocalPolynomialRing(R, 2);
		R<t_0,t_1> := BaseRing(P);
		f := (x^3-y^2)^2 - x^5*y*(t_0+t_1*x);
		gs := [x^3-y^2, f];
	when "4-6-13_moved":
		R<t_0,t_1> := RationalFunctionField(Q, 3);
		P<x,y> := LocalPolynomialRing(R, 2);
		R<t_0,t_1> := BaseRing(P);
		f := (x^3-(y-x)^2)^2 - x^5*(y-x)*(t_0+t_1*x);
		gs := [x^3-(y-x)^2, f];
	when "8-18-73_t_3":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 1), 2);
		R<t> := BaseRing(P);
		f := (x^9-y^4-t*x^3*y^3)^2 - x^16*y;
		gs := [x^9-y^4-t*x^3*y^3, f];
	when "8-18-73_t_1-2-6-10": // deform first divisor as with 1 exponent
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 4), 2);
		R<t_1,t_2,t_6,t_10> := BaseRing(P);
		f := (-(x^9+y^4) + t_1*x^7*y+t_2*x^5*y^2+t_6*x^6*y^2+t_10*x^7*y^2)^2 - x^16*y;
		gs := [-(x^9+y^4) + t_1*x^7*y+t_2*x^5*y^2+t_6*x^6*y^2+t_10*x^7*y^2, f];
	when "8-18-73_full":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 39), 2);
		R<t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33, t34, t35, t36, t37, t38> := BaseRing(P);
		f := (y^4 + t3*x^3*y^3 + t7*x^4*y^3 + t2*x^5*y^2 - x^9 + t11*x^5*y^3 + t6*x^6*y^2 + t1*x^7*y + t15*x^6*y^3 + t10*x^7*y^2 + t5*x^8*y  + t19*x^7*y^3 + t14*x^8*y^2)^2 + (t36*x^3*y^7 + t37*x^4*y^7 + t35*x^5*y^6 + t38*x^5*y^7 - x^16*y) * ( t0 + t9*y + t4*x + t18*y^2 + t13*x*y + t8*x^2 + t22*x*y^2 + t17*x^2*y + t12*x^3 + t25*x^2*y^2 + t21*x^3*y + t16*x^4 + t28*x^3*y^2 + t24*x^4*y + t20*x^5 + t30*x^4*y^2 + t27*x^5*y + t23*x^6 + t32*x^5*y^2 + t29*x^6*y + t26*x^7 + t33*x^6*y^2 + t31*x^7*y + t34*x^7*y^2 )^2;
		gs := [y^4 + t3*x^3*y^3 + t7*x^4*y^3 + t2*x^5*y^2 - x^9 + t11*x^5*y^3 + t6*x^6*y^2 + t1*x^7*y + t15*x^6*y^3 + t10*x^7*y^2 + t5*x^8*y  + t19*x^7*y^3 + t14*x^8*y^2, f];
	when "8-18-73_t_0":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 1), 2);
		R<t_0> := BaseRing(P);
		f := (y^4 - x^9)^2 + (- x^16*y) * ( t_0 )^2;
		gs := [y^4 - x^9, f];
	when "4-18-37":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 11), 2);
		R<t_0,t_1,t_2,t_3,t_4,t_5,t_6,t_7,t_8,t_9,t_10> := BaseRing(P);
		f := (y^2 + t_1*x^5*y + t_3*x^6*y - x^9 + t_5*x^7*y)^2 + (t_0 + t_2*x + t_4*x^2 + t_6*x^3 + t_7*x^4 + t_8*x^5 + t_9*x^6 + t_10*x^7)^2 * (- x^14*y);
		gs := [y^2 + t_1*x^5*y + t_3*x^6*y - x^9 + t_5*x^7*y, f];
	when "10-15-36":
		P<x,y> := LocalPolynomialRing(Q, 2);
		R := BaseRing(P);
		f := (x^3-y^2)^5 -x^18;
		gs := [x^3-y^2, f];
	when "9-21-67":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 1), 2);
		R<t_1> := BaseRing(P);
		f := (1/t_1*x^7 - 1/t_1*y^3)^3 - x^20*y;
		gs := [1/t_1*x^7 - 1/t_1*y^3, f];
	when "6-14-43":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 1), 2);
		R<t_1> := BaseRing(P);
		f := x^14 - 17/53*x^12*y + 324/2809*x^10*y^2 - 2*x^7*y^3 - 36/53*x^5*y^4 + y^6;
		gs := [-x^7 + (-18/53)*x^5*y + y^3, f];
	when "6-14-43_AM":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 1), 2);
		R<t> := BaseRing(P);
		f := (x^3-y^7)^2 + x*y^12 + t*x^2*y^10; // t = 174002425037731477/11477129801212247256
		gs := [x^3-y^7, f];
	when "4-9_example":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 1), 2);
		R<t> := BaseRing(P);
		f := y^4 - x^9 + t*x^5*y^2;
		gs := [f];
	when "6-14-43_Artal":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 1), 2);
		R<t> := BaseRing(P);
		f := (x^3-y^7)^2 + x^4*y^5 + t*x^2*y^10;
		// -23/86 not root for t = -21/1060 (Artal Singular)
	when "6-9-22_Artal_mod":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 1), 2);
		R<t> := BaseRing(P);
		f := (x^2-y^3)^3 + x^6*y^2 + t*y^8*(x^2-y^3);
		//                   ^   ^ exponentes cambiados (typo Artal supongo)
		// -23/66 not root for t = -7/10 (Artal Singular)
	when "6-9-22_Artal":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 1), 2);
		R<t> := BaseRing(P);
		f := (x^2-y^3)^3 + x^2*y^6 + t*y^8*(x^2-y^3);
		// Runtime error: Argument must be an irreducible series
		// -23/66 not root for t = -7/10 (Artal Singular)
		
	when "Maria_6-7_general":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 6), 2);
		R<A_43,A_34,A_44,A_52,A_53,A_54> := BaseRing(P);
		f := y^6 - x^7 + A_52*x^5*y^2 + A_43*x^4*y^3 + A_34*x^3*y^4 + A_44*x^4*y^4 + A_53*x^5*y^3 + A_54*x^5*y^4;
		
	when "Maria_6-7_w(5,2)":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 5), 2);
		R<A_43,A_34,A_44,A_53,A_54> := BaseRing(P);
		// w = (5,2)
		// f := y^6 - x^7 + x^5*y^2 + A_43*x^4*y^3 + A_34*x^3*y^4;
		// f := y^6 - x^7 + x^5*y^2 + A_43*x^4*y^3 + (63*A_43^2-20)/56*x^3*y^4 + A_44*x^4*y^4;
		f := y^6 - x^7 + x^5*y^2 + A_43*x^4*y^3 + A_34*x^3*y^4 + A_44*x^4*y^4;
		// f := y^6 - x^7 + x^5*y^2 + A_43*x^4*y^3 + A_34*x^3*y^4 + A_44*x^4*y^4 + A_53*x^5*y^3 + A_54*x^5*y^4; // irrellevants
		
	when "Maria_6-7_w(5,2)_extra1":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 5), 2);
		R<A_43,A_34,A_44,A_53,A_54> := BaseRing(P);
		// w = (5,2)
		f := y^6 - x^7 + x^5*y^2 + A_43*x^4*y^3 + A_34*x^3*y^4;
		
	when "Maria_6-7_w(5,2)_extra2":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 5), 2);
		R<A_43,A_34,A_44,A_53,A_54> := BaseRing(P);
		// w = (5,2)
		f := y^6 - x^7 + x^5*y^2 + A_43*x^4*y^3 + (63*A_43^2-20)/56*x^3*y^4 + A_44*x^4*y^4;
		
	when "Maria_6-7_w(4,3)":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 5), 2);
		R<A_43,A_34,A_44,A_53,A_54> := BaseRing(P);
		// w = (4,3)
		// f := y^6 - x^7 + x^4*y^3 + A_34*x^3*y^4 + A_44*x^4*y^4; // irrellevant
		f := y^6 - x^7 + x^4*y^3 + A_34*x^3*y^4;
		
	when "Maria_6-7_w(3,4)":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 5), 2);
		R<A_43,A_34,A_44,A_53,A_54> := BaseRing(P);
		// w = (3,4)
		f := y^6 - x^7 + x^3*y^4 + A_53*x^5*y^3;
		
	when "Maria_6-7_w(5,3)":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 5), 2);
		R<A_43,A_34,A_44,A_53,A_54> := BaseRing(P);
		// w = (5,3)
		f := y^6 - x^7 + x^5*y^3 + A_44*x^4*y^4;
		
	when "Maria_6-7_w(4,4)":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 5), 2);
		R<A_43,A_34,A_44,A_53,A_54> := BaseRing(P);
		// w = (4,4)
		f := y^6 - x^7 + x^4*y^4;
		
	when "Maria_6-7_w(5,4)":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 5), 2);
		R<A_43,A_34,A_44,A_53,A_54> := BaseRing(P);
		// w = (5,4)
		f := y^6 - x^7 + x^5*y^4;
		
	when "Maria_6-7_wInf":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 5), 2);
		R<A_43,A_34,A_44,A_53,A_54> := BaseRing(P);
		// w = Inf
		f := y^6 - x^7;
		
	when "Maria_17-6":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 12), 2);
		R<A_9_3, A_12_2, A_15_1, A_10_3, A_13_2, A_11_3, A_14_2, A_12_3, A_15_2, A_13_3, A_14_3, A_15_3> := BaseRing(P);
		// w = (6,4)
		f := y^6 - x^17 + x^6*y^4 + A_9_3*x^9*y^3 + A_12_2*x^12*y^2 + A_15_1*x^15*y + A_10_3*x^10*y^3 +
			A_13_2*x^13*y^2 + A_11_3*x^11*y^3 + A_14_2*x^14*y^2 + A_12_3*x^12*y^3 + A_15_2*x^15*y^2 +
			A_13_3*x^13*y^3 + A_14_3*x^14*y^3 + A_15_3*x^15*y^3;
		
	when "Maria_17-6_1.1":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 12), 2);
		R<A_9_3, A_12_2, A_15_1, A_10_3, A_13_2, A_11_3, A_14_2, A_12_3, A_15_2, A_13_3, A_14_3, A_15_3> := BaseRing(P);
		// w = (6,4)
		// 1.1
		f := y^6 - x^17 + x^6*y^4 + A_9_3*x^9*y^3 + A_12_2*x^12*y^2 + A_15_1*x^15*y + A_10_3*x^10*y^3 +
			A_13_2*x^13*y^2 + A_11_3*x^11*y^3 + A_14_2*x^14*y^2 + A_15_2*x^15*y^2;
		
	when "Maria_17-6_1.2.1.1":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 12), 2);
		R<A_9_3, A_12_2, A_15_1, A_10_3, A_13_2, A_11_3, A_14_2, A_12_3, A_15_2, A_13_3, A_14_3, A_15_3> := BaseRing(P);
		// w = (6,4)
		// 1.2.1.1
		f := y^6 - x^17 + x^6*y^4 + A_9_3*x^9*y^3 +
			(1/3 + 9/8*A_9_3^2)*x^12*y^2 +
			A_15_1*x^15*y +
			A_10_3*x^10*y^3 +
			A_13_2*x^13*y^2 +
			A_11_3*x^11*y^3 +
			A_14_2*x^14*y^2 +
			A_12_3*x^12*y^3 +
			A_13_3*x^13*y^3;
		
	when "Maria_17-6_1.2.1.2":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 12), 2);
		R<A_9_3, A_12_2, A_15_1, A_10_3, A_13_2, A_11_3, A_14_2, A_12_3, A_15_2, A_13_3, A_14_3, A_15_3> := BaseRing(P);
		// w = (6,4)
		// 1.2.1.2
		f := y^6 - x^17 + x^6*y^4 + A_9_3*x^9*y^3 +
			(1/3 + 9/8*A_9_3^2)*x^12*y^2 +
			A_15_1*x^15*y +
			A_10_3*x^10*y^3 +
			1/1020*(
				-450*A_15_1^2 + 275*A_10_3*A_9_3 + 540*A_15_1*A_9_3 - 162*A_9_3^2 +
				1215*A_15_1*A_9_3^3 - 729*A_9_3^4 - 6561/8*A_9_3^6)*x^13*y^2 +
			A_11_3*x^11*y^3 +
			A_14_2*x^14*y^2 +
			A_12_3*x^12*y^3 +
			A_13_3*x^13*y^3 +
			A_14_3*x^14*y^3;
	
	when "Maria_17-6_1.2.2.1":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 12), 2);
		R<A_9_3, A_12_2, A_15_1, A_10_3, A_13_2, A_11_3, A_14_2, A_12_3, A_15_2, A_13_3, A_14_3, A_15_3> := BaseRing(P);
		// w = (6,4)
		// 1.2.2.1
		f := y^6 - x^17 + x^6*y^4 + A_9_3*x^9*y^3 +
			(1/3 + 9/8*A_9_3^2)*x^12*y^2 +
			(27/20*A_9_3^3 + 3/5*A_9_3)*x^15*y +
			A_10_3*x^10*y^3 +
			A_13_2*x^13*y^2 +
			A_11_3*x^11*y^3 +
			A_14_2*x^14*y^2 +
			A_12_3*x^12*y^3 +
			A_15_2*x^15*y^2;
	
	when "Maria_17-6_1.2.2.2.1":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 12), 2);
		R<A_9_3, A_12_2, A_15_1, A_10_3, A_13_2, A_11_3, A_14_2, A_12_3, A_15_2, A_13_3, A_14_3, A_15_3> := BaseRing(P);
		// w = (6,4)
		// 1.2.2.2.1
		f := y^6 - x^17 + x^6*y^4 + A_9_3*x^9*y^3 +
			(1/3 + 9/8*A_9_3^2)*x^12*y^2 +
			(27/20*A_9_3^3 + 3/5*A_9_3)*x^15*y +
			A_10_3*x^10*y^3 +
			(27/20*A_9_3)*x^13*y^2 +
			A_11_3*x^11*y^3 +
			A_14_2*x^14*y^2 +
			A_12_3*x^12*y^3 +
			A_15_2*x^15*y^2 +
			A_13_3*x^13*y^3;
	
	when "Maria_17-6_1.2.2.2.2.1":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 12), 2);
		R<A_9_3, A_12_2, A_15_1, A_10_3, A_13_2, A_11_3, A_14_2, A_12_3, A_15_2, A_13_3, A_14_3, A_15_3> := BaseRing(P);
		// w = (6,4)
		// 1.2.2.2.2.1
		f := y^6 - x^17 + x^6*y^4 + A_9_3*x^9*y^3 +
			(1/3 + 9/8*A_9_3^2)*x^12*y^2 +
			(27/20*A_9_3^3 + 3/5*A_9_3)*x^15*y +
			A_10_3*x^10*y^3 +
			(27/20*A_9_3)*x^13*y^2 +
			A_11_3*x^11*y^3 +
			(45/32*A_9_3*A_11_3)*x^14*y^2 +
			A_12_3*x^12*y^3 +
			A_15_2*x^15*y^2 +
			A_13_3*x^13*y^3 +
			A_14_3*x^14*y^3;
	
	when "Maria_17-6_1.2.2.2.2.2":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 12), 2);
		R<A_9_3, A_12_2, A_15_1, A_10_3, A_13_2, A_11_3, A_14_2, A_12_3, A_15_2, A_13_3, A_14_3, A_15_3> := BaseRing(P);
		// w = (6,4)
		// 1.2.2.2.2.2
		f := y^6 - x^17 + x^6*y^4 + A_9_3*x^9*y^3 +
			(1/3 + 9/8*A_9_3^2)*x^12*y^2 +
			(27/20*A_9_3^3 + 3/5*A_9_3)*x^15*y +
			A_10_3*x^10*y^3 +
			(27/20*A_9_3)*x^13*y^2 +
			A_11_3*x^11*y^3 +
			(45/32*A_9_3*A_11_3)*x^14*y^2 +
			A_12_3*x^12*y^3 +
			(63/44*A_9_3*A_12_3)*x^15*y^2 +
			A_13_3*x^13*y^3 +
			A_14_3*x^14*y^3 +
			A_15_3*x^15*y^3;
	when "dos_monomis":
		// [6,14,43]
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 3), 2);
		R<t1,t2> := BaseRing(P);
		f := (-x^7+y^3)^2 + t1*x^5*y^4 + t2*x^12*y;
		// f := (-x^7+y^3)^2 + 1*x^5*y^4;
		// f := (-x^7+y^3)^2 + t2*x^12*y;
		
	when "set_monomis":
		// [10,15,36]
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 7), 2);
		R<t1,t2,t3,t4,t5,t6,t7> := BaseRing(P);
		// f := (-x^3 + y^2)^5 + t1*y^12 + t2*x^3*y^10 + t3*x^6*y^8 + t4*x^9*y^6 + t5*x^12*y^4 + t6*x^15*y^2 + t7*x^18;
		// f := (-x^3 + y^2)^5 + 1*y^12;
		// f := (-x^3 + y^2)^5 + 1*x^3*y^10;
		f := (-x^3 + y^2)^5 + t1*y^12 + t2*x^3*y^10;
		
	when "2_monomis":
		// [10,24,121]
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 3), 2);
		R<t1,t2> := BaseRing(P);
		
		f := (-x^12+y^5)^2 + t1*x^5*y^8 + t2*x^17*y^3;
		// f := (-x^12+y^5)^2 + 1*x^5*y^8 + 0*x^17*y^3;
		// f := (-x^12+y^5)^2 + 0*x^5*y^8 + 1*x^17*y^3;
		
	when "4_monomis":
		// [6,9,22]
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 4), 2);
		R<t1,t2,t3,t4> := BaseRing(P);
		
		f := (-x^3+y^2)^3 + t1*x^2*y^6 + t2*x^5*y^4 + t3*x^8*y^2 + t4*x^11;
		// f := (-x^3+y^2)^3 + x^11;
		// f := (-x^3+y^2)^3 + x^2*y^6;
		
	when "Maria_5-12_s1_general":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 4), 2);
		R<A_10_1, A_8_2, A_9_2, A_10_2> := BaseRing(P);
		f := y^5 - x^12 + x^5*y^3 + A_10_1*x^10*y + A_8_2*x^8*y^2 + A_9_2*x^9*y^2 + A_10_2*x^10*y^2;
		
	when "Maria_5-12_s1_subestrat1":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 4), 2);
		R<A_10_1, A_8_2, A_9_2, A_10_2> := BaseRing(P);
		f := y^5 - x^12 + x^5*y^3 + A_10_1*x^10*y + A_8_2*x^8*y^2 + A_9_2*x^9*y^2;
		
	when "Maria_5-12_s1_subestrat2":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 4), 2);
		R<A_10_1, A_8_2, A_9_2, A_10_2> := BaseRing(P);
		f := y^5 - x^12 + x^5*y^3 + 3/10*x^10*y + A_8_2*x^8*y^2 + A_9_2*x^9*y^2;
		
	when "Maria_5-12_s2_general":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 6), 2);
		R<A_8_2, A_6_3, A_9_2, A_7_3, A_8_3, A_9_3> := BaseRing(P);
		f := y^5 - x^12 + x^10*y + A_8_2*x^8*y^2 +A_6_3*x^6*y^3 + A_9_2*x^9*y^2 + A_7_3*x^7*y^3 + A_8_3*x^8*y^3 + A_9_3*x^9*y^3;
		
	when "Maria_5-12_s2_subestrat1":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 6), 2);
		R<A_8_2, A_6_3, A_9_2, A_7_3, A_8_3, A_9_3> := BaseRing(P);
		f := y^5 - x^12 + x^10*y + A_8_2*x^8*y^2 + A_6_3*x^6*y^3 + A_7_3*x^7*y^3;
		
	when "Maria_5-12_s2_subestrat2":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 6), 2);
		R<A_8_2, A_6_3, A_9_2, A_7_3, A_8_3, A_9_3> := BaseRing(P);
		f := y^5 - x^12 + x^10*y + A_8_2*x^8*y^2 + (4/3*A_8_2*A_8_2 + 1/3*A_8_2)*x^6*y^3 + A_7_3*x^7*y^3 + A_8_3*x^8*y^3;
		
	when "Maria_5-12_s2_subestrat3":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 6), 2);
		R<A_8_2, A_6_3, A_9_2, A_7_3, A_8_3, A_9_3> := BaseRing(P);
		f := y^5 - x^12 + x^10*y - 5/12*x^8*y^2 + A_6_3*x^6*y^3 + A_9_2*x^9*y^2;
		
	when "Maria_5-12_s2_subestrat4":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 6), 2);
		R<A_8_2, A_6_3, A_9_2, A_7_3, A_8_3, A_9_3> := BaseRing(P);
		f := y^5 - x^12 + x^10*y - 5/12*x^8*y^2 + 5/54*x^6*y^3 + A_9_2*x^9*y^2 + A_7_3*x^7*y^3;
		
	when "Maria_5-12_s2_subestrat5":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 6), 2);
		R<A_8_2, A_6_3, A_9_2, A_7_3, A_8_3, A_9_3> := BaseRing(P);
		f := y^5 - x^12 + x^10*y - 5/12*x^8*y^2 + 5/54*x^6*y^3 - 11/9*A_7_3*x^9*y^2 + A_7_3*x^7*y^3 + A_8_3*x^8*y^3;
		
	when "Maria_5-12_s2_subestrat6":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 6), 2);
		R<A_8_2, A_6_3, A_9_2, A_7_3, A_8_3, A_9_3> := BaseRing(P);
		f := y^5 - x^12 + x^10*y - 5/12*x^8*y^2 + 5/54*x^6*y^3 - 11/9*A_7_3*x^9*y^2 + A_7_3*x^7*y^3 + (121/32*A_7_3*A_7_3 + 5/93312)*x^8*y^3 + A_9_3*x^9*y^3;
		
	when "Maria_5-12_s4_general":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 3), 2);
		R<A_6_3, A_7_3> := BaseRing(P);
		f := y^5 - x^12 + x^8*y^2 + A_6_3*x^6*y^3 + A_7_3*x^7*y^3;
		
	when "Maria_5-12_s6_general":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 3), 2);
		R<A_9_2, A_10_2> := BaseRing(P);
		f := y^5 - x^12 + x^6*y^3 + A_9_2*x^9*y^2 + A_10_2*x^10*y^2;
		
	when "Maria_5-12_s9_general":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 3), 2);
		R<A_7_3, A_8_3> := BaseRing(P);
		f := y^5 - x^12 + x^9*y^2 + A_7_3*x^7*y^3 + A_8_3*x^8*y^3;
		
	when "Maria_5-12_s11_general":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 1), 2);
		R<A_10_2> := BaseRing(P);
		f := y^5 - x^12 + x^7*y^3 + A_10_2*x^10*y^2;
		
	when "Maria_5-12_s14_general":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 3), 2);
		R<A_8_3, A_9_3> := BaseRing(P);
		f := y^5 - x^12 + x^10*y^2 + A_8_3*x^8*y^3 + A_9_3*x^9*y^3;
		
	when "Maria_5-12_s14_subestrat1":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 3), 2);
		R<A_8_3, A_9_3> := BaseRing(P);
		f := y^5 - x^12 + x^10*y^2 + A_8_3*x^8*y^3;
		
	when "Maria_5-12_s14_subestrat2":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 3), 2);
		R<A_8_3, A_9_3> := BaseRing(P);
		f := y^5 - x^12 + x^10*y^2 + A_9_3*x^9*y^3;
		
	when "Maria_5-12_s16_general":
		P<x,y> := LocalPolynomialRing(Q, 2);
		R := BaseRing(P);
		f := y^5 - x^12 + x^8*y^3;
		
	when "Maria_5-12_s21_general":
		P<x,y> := LocalPolynomialRing(Q, 2);
		R := BaseRing(P);
		f := y^5 - x^12 + x^9*y^3;
		
	when "Maria_5-12_s26_general":
		P<x,y> := LocalPolynomialRing(Q, 2);
		R := BaseRing(P);
		f := y^5 - x^12 + x^10*y^3;
		
	when "Maria_5-12_sInf_general":
		P<x,y> := LocalPolynomialRing(Q, 2);
		R := BaseRing(P);
		f := y^5 - x^12;
	
	when "David_1":
		// Puiseux 6,14,43; Zariski
		P<x,y> := LocalPolynomialRing(Q, 2);
		R := BaseRing(P);
		f := -x^14 + 2*x^7*y^3 - y^6 + (-6)*x^12*y + 6*x^5*y^4 + (-9)*x^10*y^2 + (-2)*x^15 + 2*x^8*y^3 + (-6)*x^13*y - x^16 + 9*x^19*y^2 + (-6)*x^24 + 6*x^17*y^3 + 3*x^25 + 6*x^31*y + (-3)*x^34 + x^43;
	
	when "David_2":
		// Puiseux 6,14,43; Zarkski
		P<x,y> := LocalPolynomialRing(Q, 2);
		R := BaseRing(P);
		f := x^43 + 6*x^31*y + 9*x^19*y^2 - x^14 + 2*x^7*y^3 - y^6;
		
	when "David_3":
		// Puiseux 6,14,17; Zariski 17
		P<x,y> := LocalPolynomialRing(Q, 2);
		R := BaseRing(P);
		f := x^17 + (-3)*x^16 + 3*x^15 - x^14 + 6*x^8*y^3 + 2*x^7*y^3 - y^6;
		
	when "David_4":
		// Puiseux 6,14,17; Zariski 16
		P<x,y> := LocalPolynomialRing(Q, 2);
		R := BaseRing(P);
		f := x^17 + (-10)*x^16 + x^15 + 6*x^14*y - x^14 + (-6)*x^13*y + (-6)*x^12*y + 9*x^11*y^2 + (-9)*x^10*y^2 + 8*x^8*y^3 + 2*x^7*y^3 + 6*x^5*y^4 - y^6;
		
	when "David_5":
		// Puiseux ; Zariski
		P<x,y> := LocalPolynomialRing(Q, 2);
		R := BaseRing(P);
		f := x^59 - x^58 + 46*x^57*y + (-483)*x^56*y^2 + 552*x^55*y^3 + 115*x^53*y^4 + 22862*x^52*y^5 + 63204*x^51*y^6 + 46*x^50*y^7 + (-4715)*x^48*y^8 + 738484*x^47*y^9 + (-86434)*x^46*y^10 + 82708*x^43*y^12 + 2691552*x^42*y^13 + 713*x^41*y^14 + (-586661)*x^38*y^16 + 777630*x^37*y^17 + 1310333*x^33*y^20 + 4232*x^32*y^21 + 2*x^29*y^23 + (-514234)*x^28*y^24 + 414*x^24*y^27 + 7820*x^23*y^28 + 4186*x^19*y^31 + 1932*x^14*y^35 - y^46;
		
	when "David_6":
		// Puiseux 34,38,39; Zariski 39  -> raiz
		P<x,y> := LocalPolynomialRing(Q, 2);
		R := BaseRing(P);
		f := x^39 - x^38 + 34*x^37*y + (-425)*x^36*y^2 + 2380*x^35*y^3 + (-5780)*x^34*y^4 + 4862*x^33*y^5 + (-714)*x^32*y^6 + 170*x^28*y^9 + 11237*x^27*y^10 + 64736*x^26*y^11 + 40749*x^25*y^12 + 1190*x^24*y^13 + 2*x^19*y^17 + (-3213)*x^18*y^18 + 10540*x^17*y^19 + (-357)*x^16*y^20 + 119*x^9*y^26 + 34*x^8*y^27 - y^34;
		
	when "David_7":
		// t5, t11 + t12 +t13 +t14
		P<x,y> := LocalPolynomialRing(Q, 2);
		R := BaseRing(P);
		f := -x^14 - x^13 - x^12 + (-5)*x^11*y - x^11 + (-5)*x^10*y + (-5)*x^9*y + (-10)*x^8*y^2 + (-10)*x^7*y^2 + (-10)*x^5*y^3 + y^5;
		
	when "David_8":
		// t10, t22 + t24 + t26 + t28 + t29
		P<x,y> := LocalPolynomialRing(Q, 2);
		R := BaseRing(P);
		f := x^29 + (-111)*x^28 + 13*x^27 + 10*x^26*y + 27*x^26 + (-260)*x^25*y + x^25 + 20*x^24*y + 35*x^23*y^2 + (-3)*x^24 + (-385)*x^22*y^2 + (-2)*x^23 + (-100)*x^21*y^2 + 60*x^20*y^3 - x^22 + (-20)*x^21*y + (-25)*x^20*y^2 + (-420)*x^19*y^3 + (-10)*x^20*y + (-75)*x^19*y^2 + (-170)*x^18*y^3 + 75*x^17*y^4 + (-45)*x^18*y^2 + (-170)*x^17*y^3 + (-325)*x^16*y^4 + (-120)*x^16*y^3 + (-250)*x^15*y^4 + 72*x^14*y^5 + (-200)*x^14*y^4 + (-198)*x^13*y^5 + (-198)*x^12*y^5 + 55*x^11*y^6 + 2*x^11*y^5 + (-90)*x^10*y^6 + 10*x^9*y^6 + 30*x^8*y^7 + 20*x^7*y^7 + 20*x^5*y^8 - y^10;
	
	when "David_9":
		// 
		P<x,y> := LocalPolynomialRing(Q, 2);
		R := BaseRing(P);
		f := y^5 + x^11 + x^9*y + x^7*y^2;
		
	when "David_10":
		// Senovilla - Computing a Saito basis from a standard basis
		// 36x^3 * (...dx + ...dy) + ...dy
		P<x,y> := LocalPolynomialRing(Q, 2);
		R := BaseRing(P);
		f := (-13492928512/4782969)*x^196 + 3373232128/531441*x^168*y + (-120472576/19683)*x^140*y^2 + 70027/729*x^116 + 21512960/6561*x^112*y^3 + (-3325/27)*x^88*y + (-768320/729)*x^84*y^4 + 154/3*x^60*y^2 + 5488/27*x^56*y^5 - x^36 + (-7)*x^32*y^3 + (-196/9)*x^28*y^6 + y^7;
		
	when "David_11":
		// Senovilla - Computing a Saito basis from a standard basis
		// 36x^3 * (...dx + ...dy) - 560 * (...)dy
		P<x,y> := LocalPolynomialRing(Q, 2);
		R := BaseRing(P);
		f :=  (-1/45312452946136620155605528267853500261871027739095881489117719035904)*x^206 + 343/271528241623977695813092575157061124887565828096*x^201 + (-245794879917154064393063555374515405263311844076914202370828559/87129290721203997305816807972135970662895181076683240243200)*x^196 + 20451673422440139293408181412560468062336411497906072756623929058133753/234890366791563487037922346027981368794283361210411774913919414435840000*x^191 + 221754041601537809643664681057269657151/2571503244531850514797585121685129425584128000*x^186 + (-26783585667400094917893367360702411855667959261/3451941807891854008254640222408748650602154998890496000000)*x^181 + (-249396329542342047811544650270125615514459278087453661/7656465298097773472089846789363197172084763089257565367618764800000000)*x^176 + (-49/60339609249772821291798350034902472197236850688)*x^173*y + (-4420833100615571387829783048287022170586138004907/37836861548453837233406462641720395718196340471184187751137280000000000)*x^171 + 1720564159420078450751444882196089774757467869405342881066969359/271068904465967991618096735913311908729007230016347858534400*x^168*y + 555331877120179284141942568587494072490650079221269/1328329573524454469415020066199715835904000000000000*x^166 + (-873104732057045878344905493883737719/5199564505679064255712587591670824960)*x^163*y + (-174874299450794616513217176420230360523092276383332381169/46113564007278380979403365604980179984439485030400000000000000)*x^161 + (-52666584880365229790370361403355175594337/380011035025262353853420912426802459558543360000)*x^158*y + (-2785450316611869131519118425629054241705231135934014903/23833642694889289263851535607086422388840915783291135590400000000)*x^156 + 107134342669600379671573469443487793136449394141/10739374513441323581236658469716106912984482218770432000000*x^153*y + (-21215627408818582514184754631714653456740837979/18356337970939861839053896913942615262446489626094862336000000)*x^151 + 143073025381124410761708163211898307295203/3467483853506984463483186385822646747006938581565440000000*x^148*y + 7/53635208222020285592709644475468864175321645056*x^145*y^2 + 5716665465494668717257763/142398746381431762422080639389123188326400000000*x^146 + 1012987122942640639/5097649578358181361498998439885000000000*x^143*y + (-44589434805851330231518057557545/7285092378896021389523288064)*x^140*y^2 + 5184500086928378520012947305425655789980415531979/2430929938476125826380428879319741399040000000000*x^141 + (-3742133418513437863770900992848081081737825297190019/4132580895409413904846729094843560378368000000000000)*x^138*y + 1559115592959010497044474096247661141/11554587790397920568250194648157388800*x^135*y^2 + (-27044952903916951943666708443778840920964990299/144194695673847651689218657813495532451004416000000)*x^136 + 671755435260516482475337112300258448876307511/139475364634544367202265017531231636209795072000000*x^133*y + 210666339521460919161481444917927966419297/2364513106823854646199063455100104192808714240000*x^130*y^2 + (-7394275781792919866511011631045973433344919/8622025668942386095232311572674468788971723816960000)*x^131 + 2090218176457113212463672902551109840028937/16924763610823776991720052925279056389373857628160000*x^128*y + (-6095669251/1267348151121831900000)*x^125*y^2 + (-1059702799154979357391/31402379598148414546335654451200000)*x^126 + 3689121397848050791597/3297249857805583527365243717376000000*x^123*y + (-714672202003528007/36471058348451219645314821120000000)*x^120*y^2 + (-34832526140406649/29642865757657852411719768499200000000)*x^121 + 38191022268537167683/46100584826309492070706583969955840000000*x^118*y + (-371619836101979486167/4059994686407938222136091201899520000000000)*x^115*y^2 + 4223892125282113696875939957642606532457/43971858844883557556693278874664960000*x^116 + 15924798144946903654113591964751/4856728252597347593015525376*x^112*y^3 + (-33293255074105362919251886276845955051/5139567916934441792340772855480320000)*x^113*y + 9725511919476570861647637559465608097039/13280643497358597591408557058561146880000*x^110*y^2 + (-33688333/5940250668)*x^111 + (-6236462371836041988177896385044046421/107842819377047258637001816716135628800)*x^107*y^3 + 269793986647/1489814867534400*x^108*y + (-37630442591/16407566370082800)*x^105*y^2 + (-18483871481984363/1259195399558730469440000)*x^106 + (-30173269/1053621109134000)*x^102*y^3 + 312762712463/462939485131886202000*x^103*y + (-540079238557081/12510715582712547889920000)*x^100*y^2 + (-310558145063807/1252568055350526624864000000)*x^101 + 870809893/844898767414554600000*x^97*y^3 + 6007775656813457/294287568372881623862784000000*x^98*y + (-15926012781499/44143135255932243579417600000)*x^95*y^2 + (-38254157/913968350666539710474240000)*x^96 + 1407588573410403007/340396544585544716689604997120000000*x^92*y^3 + 48217/125344230948554017436467200*x^93*y + (-4023559/12824693945473105784025907200)*x^90*y^2 + 197809/15489565414662322570317004800*x^87*y^3 + (-3325/27)*x^88*y + (-9099884654255373516636338259833/8634183560173062387583156224)*x^84*y^4 + 23492/4617*x^85*y^2 + (-77371/1929906)*x^86 + (-7390376/26053731)*x^82*y^3 + 14752073/4125174075*x^83*y + 1372/98415*x^79*y^4 + (-241146811/4138374632040)*x^80*y^2 + (-221996689/1151408166321600)*x^81 + 10617179833/21876755160110400*x^77*y^3 + 3653312880439/387563988783850560000*x^78*y + 4310467/936552097008000*x^74*y^4 + (-2322365501/17616544944720480000)*x^75*y^2 + (-136267/178871592085401600)*x^76 + 5916036569/1183831820285216256000*x^72*y^3 + 419/6969023068262400*x^73*y + (-870809893/10514295772270012800000)*x^69*y^4 + (-479/155548594883616768)*x^70*y^2 + 7/180637077929361408*x^67*y^3 + (-7/21396753230858551296)*x^64*y^4 + 154/3*x^60*y^2 + (-28/171)*x^61 + 5488/27*x^56*y^5 + (-2380/1539)*x^57*y^3 + 1253/107217*x^58*y + 308861/5789718*x^54*y^4 + (-2863/5078700)*x^55*y^2 + (-1/419904)*x^56 + (-98/54675)*x^51*y^5 + 50269/8044660800*x^52*y^3 + 7/117153216*x^53*y + (-2357/61212555360)*x^49*y^4 + (-7/4625662464)*x^50*y^2 + (-615781/2081226882240000)*x^46*y^5 - x^36 + (-7)*x^32*y^3 + (-196/9)*x^28*y^6 + 28/171*x^29*y^4 + (-7/1782)*x^26*y^5 + 7/72900*x^23*y^6 + y^7;
		
	when "Example_pair_1":
		// Puiseux 6,7; Zariski 3
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 6), 2);
		R<A_4_3, A_3_4, A_4_4, A_5_2, A_5_3, A_5_4> := BaseRing(P);
		// R<A_5_2, A_4_3, A_3_4, A_4_4, A_5_3, A_5_4> := BaseRing(P);
		// Reorder parameters -> same ideals, different generators. Check with:
		//   RR<A_4_3, A_3_4, A_4_4, A_5_2, A_5_3, A_5_4> := PolynomialRing(Q,6);
		//   ideal<RR| A_5_2*A_3_4^2 - 420*A_4_4, 5*A_5_2^2 + 14*A_3_4 > eq ideal<RR| 14*A_3_4 + 5*A_5_2^2, 16464*A_4_4 - 5*A_5_2^5 >;
		
		f := y^6 - x^7 + A_5_2*x^5*y^2 + A_4_3*x^4*y^3 + A_3_4*x^3*y^4 + A_4_4*x^4*y^4 + A_5_3*x^5*y^3 + A_5_4*x^5*y^4;
		
		// f := y^6 - x^7 + x^4*y^3 + A_3_4*x^3*y^4;
		
	when "Example_pair_2":
		// Puiseux 12,14,85; Zariski ?
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 6), 2);
		R<A_4_3, A_3_4, A_4_4, A_5_2, A_5_3, A_5_4> := BaseRing(P);		
		f := (y^6 - x^7 + A_5_2*x^5*y^2 + A_4_3*x^4*y^3 + A_3_4*x^3*y^4 + A_4_4*x^4*y^4 + A_5_3*x^5*y^3 + A_5_4*x^5*y^4)^2 + x^6*y^7;
		
		// // Puiseux 12,14,17; Zariski
		// P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 1), 2);
		// R<t> := BaseRing(P);
		// f := (y^3 + x^7)^2 + x^17;
		
	when "Example_pair_3":
		// Puiseux ; Zariski
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 6), 2);
		R<t> := BaseRing(P);
		f := y^3 - x^7 + t*x^5*y;
		
	when "Example_pair_4":
		// Puiseux ; Zariski
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 6), 2);
		R<t> := BaseRing(P);
		f := (y^3 - x^7 + t*x^5*y)^2 + x^6*y^7;
		
	when "Maria_f1":
		P<x,y> := LocalPolynomialRing(Q, 2);
		R := BaseRing(P);
		f := y^5 - x^12 + x^5*y^3;
		
	when "Maria_f2":
		P<x,y> := LocalPolynomialRing(Q, 2);
		R := BaseRing(P);
		f := y^5 - x^12 + x^5*y^3 + (3/10)*x^10*y;
		
	when "18-45-93-281":
		P<x,y> := LocalPolynomialRing(Q, 2);
		R := BaseRing(P);
		t0 := 1;
		t72 := 1;
		f := x^45 - 9*x^40*y^2 + 36*x^35*y^4 - 3*t0^3*x^33*y^5 - 84*x^30*y^6 + 18*t0^3*x^28*y^7 + 126*x^25*y^8 + t0^4*t72^3*x^26*y^8 - 45*t0^3*x^23*y^9 - 126*x^20*y^10 + (3*t0^6 - 5*t0^4*t72^3)*x^21*y^10 + 60*t0^3*x^18*y^11 + 84*x^15*y^12 + (-9*t0^6 + 10*t0^4*t72^3)*x^16*y^12 - 45*t0^3*x^13*y^13 - 36*x^10*y^14 + (9*t0^6 - 10*t0^4*t72^3)*x^11*y^14 + 18*t0^3*x^8*y^15 - t0^9*x^9*y^15 + 9*x^5*y^16 + (-3*t0^6 + 5*t0^4*t72^3)*x^6*y^16 - 3*t0^3*x^3*y^17 - y^18 - t0^4*t72^3*x*y^18;


	when "deformation_restricted": // Generic curve construction
		// INPUT
		_betas := semigroup;
		error if (not IsPlaneCurveSemiGroup(_betas)), "Please define a valid plane branch semigroup. Given: ", _betas;
		
		// Name
		curve := &*[Sprint(_b)*"-" : _b in _betas];
		curve := curve[1..#curve-1];
		
		if printDeformationProcess or printParameterOptions then print "Semigroup:", _betas; end if;
		
		// Topological information
		//semiGroupInfo := SemiGroupInfo(_betas);
		//g, c, betas, es, ms, ns, qs, _ms := Explode(semiGroupInfo);
		planeBranchNumbers := PlaneBranchNumbers(_betas);
		g, c, betas, es, ms, ns, qs, _betas, _ms, Nps, kps, Ns, ks := Explode(planeBranchNumbers);
		
		// Choice of monomial curve equations and their deformations
		eqs := allMonomialCurves(_betas); // [ [i-th equation options] ]
		if printDeformationProcess then
			print "Possible undeformed equations in space:";
			for i in [1..#_betas-1] do
				printf "Equation %o options:\n", i;
				print eqs[i];
			end for;
		end if;
		// INPUT
		error if (ExtendedType(whichEquations) ne SeqEnum[RngIntElt]), "Please define a valid list of equation indexes";
		error if (#whichEquations lt (#_betas-1)), "Please define a valid list of equation indexes, # of indexes too small";
		whichEquations := whichEquations[1..g];
		error if (&or[ (eqIdx le 0) or (eqIdx gt #(eqs[i])) : i -> eqIdx in whichEquations ]), "Please define a valid list of equation indexes, index out of bounds";
		monomialCurve := [eqs[i, whichEquations[i]] : i in [1..#_betas-1]]; // Select the chosen equations
		if printDeformationProcess then print "Chosen equation indexes:", whichEquations; end if;
		if printDeformationProcess then print "Chosen equations:"; end if;
		if printDeformationProcess then print monomialCurve; end if;
		
		// Deform the chosen monomial curve equations
		Deformation := DeformationCurveSpecific(monomialCurve, _betas);
		
		PDeformation := Universe(Deformation); // Q[t_0, ..., t_{T-1}, u_0, ..., u_g] (localization)
		totalDim := Rank(PDeformation);
		g := #Deformation; // g = # of equations in space (H_1, ..., H_g), g+1 = # variables (u_0, ..., u_g)
		T := totalDim-(g+1); // # of parameters (t_0, ..., t_{T-1})
		
		// Restrict deformation such that it can be turned explicitly to plane curve (see TFG-Roger, p.21)
		completeDeformation := true;
		for i in [1..g-1] do
			Hi := Deformation[i];
			// Find and save disallowed terms
			termsToRemove := PDeformation!0;
			for term in Terms(Hi) do
				if &+( Exponents(term)[(T+i+2 +1)..(T+g +1)] ) gt 0 then // u_{i+2}, ..., u_g not allowed in Hi (see TFG-Roger, p.21)
					termsToRemove +:= term;
				elif Exponents(term)[T+i+1 +1] gt 1 then // Allowed degree of u_{i+1} in Hi at most 1 (see TFG-Roger, p.21)
					termsToRemove +:= term;
				end if;
			end for;
			// Remove disallowed terms
			Deformation[i] -:= termsToRemove;
			// Store whether any terms have been removed (in total)
			if termsToRemove ne 0 then
				completeDeformation := false;
			end if;
		end for;
		if printDeformationProcess or printParameterOptions then
			print "Can use complete deformation:", completeDeformation;
		end if;
		if printDeformationProcess then
			print "Usable deformation:";
			print Deformation;
		end if;
		
		// Determine, separate and show the needed and optional deformation parameters
		if printDeformationProcess or printParameterOptions then print "Parameters:"; end if;
		neededParams := []; // parameter needed at each Hi
		optionalParams := []; // [ [optional parameters for Hi] ]
		// Parameters of H_1, ..., H_{g-1}
		// H_i = h_i(u_0,...,u_i) - t_?*u_{i+1} + sum_r( t_?*phi_{r,i}(u_0,...,u_g) )
		for i in [1..g-1] do
			Hi := Deformation[i];
			ei := [ (j eq i+1) select 1 else 0 : j in [0..g] ]; // [0, ..., 0, 1, 0, ..., 0] at position corresponding to u_{i+1} among "u"s
			optionalParams[i] := [];
			for term in Terms(Hi) do
				exps := Exponents(term); // exponents of ts and us
				tExps := exps[1..T]; // exponents of (t_0, ..., t_{T-1})
				uExps := exps[T+1..T+g+1]; // exponents of (u_0, ..., u_g)
				if uExps eq ei then // Term t_?*u_{i+1} is necessarily nonzero, save t_? as needed parameter
					tIndex := Explode([j : j in [0..T-1] | tExps[j+1] gt 0]); // index of t_?
					Append(~neededParams, tIndex);
				else // Term is optional, save the new optional parameters of this divisor
					for j in [0..T-1] do
						if (tExps[j+1] gt 0) and (j notin neededParams) and (j notin &cat(optionalParams)) then
							Append(~optionalParams[i], j);
						end if;
					end for;
				end if;
			end for;
			Sort(~optionalParams[i]);
			if printDeformationProcess or printParameterOptions then printf "    Optional at E%o: %o\n", i, optionalParams[i]; end if;
		end for;
		// H_g treated separately, no neededParams
		// H_g = h_g(u_0,...,u_g) + sum_r( t_?*phi_{r,g}(u_0,...,u_g) )
		Hg := Deformation[g];
		optionalParams[g] := [];
		for term in Terms(Hg) do
			exps := Exponents(term); // exponents of ts and us
			tExps := exps[1..T]; // exponents of (t_0, ..., t_{T-1})
			uExps := exps[T+1..T+g+1]; // exponents of (u_0, ..., u_g)
			// Term is optional, save the new optional parameters of this divisor
			for j in [0..T-1] do
				if (tExps[j+1] gt 0) and (j notin neededParams) and (j notin &cat(optionalParams)) then
					Append(~optionalParams[g], j);
				end if;
			end for;
		end for;
		Sort(~optionalParams[g]);
		if printDeformationProcess or printParameterOptions then
			printf "    Optional at E%o: %o\n", g, optionalParams[g];
			for i in [1..g-1] do
				printf "    Needed at E%o: %o\n", i, neededParams[i];
			end for;
		end if;
		optionalParams := &cat(optionalParams); // optional parameters from any divisor -> [optional parameters]
		
		// Choose deformation parameters
		// INPUT
		parameters := deformationParameters;
		if Type(parameters) eq MonStgElt and parameters eq "all" then
			parameters := optionalParams;
		else
			error if ((ExtendedType(parameters) ne SeqEnum[RngIntElt]) and (parameters ne [])), "Please define a valid list of parameters. Given ", parameters;
			for p in parameters do
				error if ((p notin optionalParams) and (p notin neededParams)), "Please define a valid list of parameters. Given invalid parameter ", p;
			end for;
		end if;
		parameters cat:= neededParams; // neededParams always have to be included
		parameters := [p : p in Set(parameters)]; // remove duplicates
		Sort(~parameters);
		if printDeformationProcess or printParameterOptions then printf "Chosen parameters: %o\n", parameters; end if;
		// Create structures with the new number of parameters
		newT := #parameters; // (temp variable) updated # of parameters (t_0, ..., t_{newT-1})
		PDeformation := LocalPolynomialRing(Q, newT+(g+1)); // polynomial ring with updated # of parameters
		// Create vector "oldToNewParam" which for each old parameter contains the corresponding new parameter (as variable) or a 0
		
		oldToNewParam := [PDeformation| 0 : i in [1..T]];
		k := 1;
		for i in [0..T-1] do
			if (i in parameters) then
				oldToNewParam[i+1] := PDeformation.k; // t_i -> new k-th variable
				k +:= 1;
			end if;
		end for;
		// Update variables
		newUs := [ PDeformation.i : i in [newT+1..newT+(g+1)]]; // new u_0, ..., u_g
		Deformation := [Evaluate(pol, oldToNewParam cat newUs) : pol in Deformation]; // Update variables of Deformation
		T := newT; // Update # of parameters
		delete newT; // (delete temp variable)
		totalDim := T + g+1; // Update total dimension
		// Set parameter and variable names
		tNames := ["t"*Sprint(i) : i in parameters ];
		uNames := ["u"*Sprint(i) : i in [0..g] ];
		AssignNames(~PDeformation, tNames cat uNames);
		if printDeformationProcess then
			print "Chosen deformation:";
			print Deformation;
		end if;
		
		// Switch to rational fraction field
		PDefNoLocal := PolynomialRing(BaseRing(PDeformation), totalDim); // Q[t_0, ..., t_{T-1}, u_0, ..., u_g] but non-localized to enable division/fractions
		FP := FieldOfFractions(PDefNoLocal); // Q(t_0, ..., t_{T-1}, u_0, ..., u_g)
		ChangeUniverse(~Deformation, FP);
		
		// Elimination of the variables u_2, ..., u_g
		// Invariant property (as ensured before): u_{i+2}, ..., u_g not in Hi, u_{i+1} with exponent at most 1 in Hi
		gs := [FP| ]; // Parts of the equations Hi, relevant later for their proximity to the curve f
		for i in [1..g-1] do
			Hi := Numerator(Deformation[i]); // We are interested in Hi=0 -> denominators don't matter
			u_ip1 := PDefNoLocal.(T+1+ i+1); // u_{i+1} as polynomial
			// Define: Hi = gs[i] + u_{i+1}*uDenom
			gs[i]  := Coefficient(Hi, u_ip1, 0);
			uDenom := Coefficient(Hi, u_ip1, 1);
			// Solve for u_{i+1}:
			// Hi = gs[i] + u_{i+1}*uDenom = 0 <=> u_{i+1} = - gs[i] / uDenom
			u_ip1_value := - gs[i] / uDenom; // function of (u_0, u_1) because of the invariant property and the elimination of (u_2, ..., u_i) in previous iterations
			// Substitute value of u_{i+1} in the remaining equations, thus eliminating u_{i+1}
			// As the value of u_{i+1} is a function of (u_0, u_1), the invariant property is preserved
			for j in [i+1..g] do
				Deformation[j] := Evaluate(Deformation[j], (T+1+ i+1), u_ip1_value); // Substitute value of u_{i+1}
				Deformation[j] := Numerator(Deformation[j]); // Remove denominators
			end for;
		end for;
		f := Deformation[g]; // Resulting plane curve equation
		gs[g] := f;
		// Switch back to polynomial ring (no denominators)
		ChangeUniverse(~gs, PDefNoLocal);
		f := PDefNoLocal ! f;
		
		// Separate parameters into the coefficient ring
		// From: Q[t_0, ..., t_{T-1}, u_0, ..., u_g]
		// To:   Q(t_0, ..., t_{T-1})[x,y]
		// u_0=x, u_1=y, ( u_2, ..., u_g have already been eliminated from the polynomials, can be evaluated to 0 )
		if T eq 0 then
			P<x,y> := LocalPolynomialRing(Q, 2);
			R := BaseRing(P);
			ts := [P | ];
		else
			P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, T), 2);
			R := BaseRing(P);
			tNames := ["t"*Sprint(i) : i in parameters ]; // in [1..T]
			AssignNames(~R, tNames);
			ts := [P | R.i : i in [1..T]];
		end if;
		// gs := [Evaluate(pol, ts cat [x,y] cat [0 : i in [2..g]]) : pol in gs];
		//gUnits := [Evaluate(pol, ts cat [x,y] cat [0 : i in [2..g]]) : pol in gUnits];
		f := Evaluate(f, ts cat [x,y] cat [0 : i in [2..g]]);
		f /:= LeadingCoefficient(f);
		// printf "f = %o\n", f;
		// printf "MaxContactElements = %o\n", MaxContactElements(f);
		
		// Save needed non-zero parameters as variables
		for i in neededParams do
			j := Position(parameters, i);
			//Append(~invertibleVariables, j);
			Include(~assumeNonzero, R.j);
		end for;



	when "deformation_GroebnerElimination": // Generic curve construction
		// INPUT
		_betas := semigroup;
		error if (not IsPlaneCurveSemiGroup(_betas)), "Please define a valid plane branch semigroup. Given: ", _betas;
		
		// Name
		curve := &*[Sprint(_b)*"-" : _b in _betas];
		curve := curve[1..#curve-1];
		
		if printDeformationProcess or printParameterOptions then print "Semigroup:", _betas; end if;
		
		// Topological information
		//semiGroupInfo := SemiGroupInfo(_betas);
		//g, c, betas, es, ms, ns, qs, _ms := Explode(semiGroupInfo);
		planeBranchNumbers := PlaneBranchNumbers(_betas);
		g, c, betas, es, ms, ns, qs, _betas, _ms, Nps, kps, Ns, ks := Explode(planeBranchNumbers);
		
		// Choice of monomial curve equations and their deformations
		eqs := allMonomialCurves(_betas); // [ [i-th equation options] ]
		if printDeformationProcess then
			print "Possible undeformed equations in space:";
			for i in [1..#_betas-1] do
				printf "Equation %o options:\n", i;
				print eqs[i];
			end for;
		end if;
		// INPUT
		error if (ExtendedType(whichEquations) ne SeqEnum[RngIntElt]), "Please define a valid list of equation indexes";
		error if (#whichEquations lt (#_betas-1)), "Please define a valid list of equation indexes, # of indexes too small";
		whichEquations := whichEquations[1..g];
		error if (&or[ (eqIdx le 0) or (eqIdx gt #(eqs[i])) : i -> eqIdx in whichEquations ]), "Please define a valid list of equation indexes, index out of bounds";
		monomialCurve := [eqs[i, whichEquations[i]] : i in [1..#_betas-1]]; // Select the chosen equations
		if printDeformationProcess then print "Chosen equation indexes:", whichEquations; end if;
		if printDeformationProcess then print "Chosen equations:"; end if;
		if printDeformationProcess then print monomialCurve; end if;
		
		// Deform the chosen monomial curve equations
		Deformation := DeformationCurveSpecific(monomialCurve, _betas);
		
		PDeformation := Universe(Deformation); // Q[t_0, ..., t_{T-1}, u_0, ..., u_g] (localization)
		totalDim := Rank(PDeformation);
		g := #Deformation; // g = # of equations in space (H_1, ..., H_g), g+1 = # variables (u_0, ..., u_g)
		T := totalDim-(g+1); // # of parameters (t_0, ..., t_{T-1})
		
		// Determine, separate and show the needed and optional deformation parameters
		if printDeformationProcess or printParameterOptions then print "Parameters:"; end if;
		neededParams := []; // parameter needed at each Hi
		optionalParams := []; // [ [optional parameters for Hi] ]
		// Parameters of H_1, ..., H_{g-1}
		// H_i = h_i(u_0,...,u_i) - t_?*u_{i+1} + sum_r( t_?*phi_{r,i}(u_0,...,u_g) )
		for i in [1..g-1] do
			Hi := Deformation[i];
			ei := [ (j eq i+1) select 1 else 0 : j in [0..g] ]; // [0, ..., 0, 1, 0, ..., 0] at position corresponding to u_{i+1} among "u"s
			optionalParams[i] := [];
			for term in Terms(Hi) do
				exps := Exponents(term); // exponents of ts and us
				tExps := exps[1..T]; // exponents of (t_0, ..., t_{T-1})
				uExps := exps[T+1..T+g+1]; // exponents of (u_0, ..., u_g)
				if uExps eq ei then // Term t_?*u_{i+1} is necessarily nonzero, save t_? as needed parameter
					tIndex := Explode([j : j in [0..T-1] | tExps[j+1] gt 0]); // index of t_?
					Append(~neededParams, tIndex);
				else // Term is optional, save the new optional parameters of this divisor
					for j in [0..T-1] do
						if (tExps[j+1] gt 0) and (j notin neededParams) and (j notin &cat(optionalParams)) then
							Append(~optionalParams[i], j);
						end if;
					end for;
				end if;
			end for;
			Sort(~optionalParams[i]);
			if printDeformationProcess or printParameterOptions then printf "    Optional at E%o: %o\n", i, optionalParams[i]; end if;
		end for;
		// H_g treated separately, no neededParams
		// H_g = h_g(u_0,...,u_g) + sum_r( t_?*phi_{r,g}(u_0,...,u_g) )
		Hg := Deformation[g];
		optionalParams[g] := [];
		for term in Terms(Hg) do
			exps := Exponents(term); // exponents of ts and us
			tExps := exps[1..T]; // exponents of (t_0, ..., t_{T-1})
			uExps := exps[T+1..T+g+1]; // exponents of (u_0, ..., u_g)
			// Term is optional, save the new optional parameters of this divisor
			for j in [0..T-1] do
				if (tExps[j+1] gt 0) and (j notin neededParams) and (j notin &cat(optionalParams)) then
					Append(~optionalParams[g], j);
				end if;
			end for;
		end for;
		Sort(~optionalParams[g]);
		if printDeformationProcess or printParameterOptions then
			printf "    Optional at E%o: %o\n", g, optionalParams[g];
			for i in [1..g-1] do
				printf "    Needed at E%o: %o\n", i, neededParams[i];
			end for;
		end if;
		optionalParams := &cat(optionalParams); // optional parameters from any divisor -> [optional parameters]
		
		// Choose deformation parameters
		// INPUT
		parameters := deformationParameters;
		if Type(parameters) eq MonStgElt and parameters eq "all" then
			parameters := optionalParams;
		else
			error if ((ExtendedType(parameters) ne SeqEnum[RngIntElt]) and (parameters ne [])), "Please define a valid list of parameters. Given ", parameters;
			for p in parameters do
				error if ((p notin optionalParams) and (p notin neededParams)), "Please define a valid list of parameters. Given invalid parameter ", p;
			end for;
		end if;
		parameters cat:= neededParams; // neededParams always have to be included
		parameters := [p : p in Set(parameters)]; // remove duplicates
		Sort(~parameters);
		if printDeformationProcess or printParameterOptions then printf "Chosen parameters: %o\n", parameters; end if;
		// Create structures with the new number of parameters
		newT := #parameters; // (temp variable) updated # of parameters (t_0, ..., t_{newT-1})
		PDeformation := LocalPolynomialRing(Q, newT+(g+1)); // polynomial ring with updated # of parameters
		// Create vector "oldToNewParam" which for each old parameter contains the corresponding new parameter (as variable) or a 0
		
		oldToNewParam := [PDeformation| 0 : i in [1..T]];
		k := 1;
		for i in [0..T-1] do
			if (i in parameters) then
				oldToNewParam[i+1] := PDeformation.k; // t_i -> new k-th variable
				k +:= 1;
			end if;
		end for;
		// Update variables
		newUs := [ PDeformation.i : i in [newT+1..newT+(g+1)]]; // new u_0, ..., u_g
		Deformation := [Evaluate(pol, oldToNewParam cat newUs) : pol in Deformation]; // Update variables of Deformation
		T := newT; // Update # of parameters
		delete newT; // (delete temp variable)
		totalDim := T + g+1; // Update total dimension
		// Set parameter and variable names
		tNames := ["t"*Sprint(i) : i in parameters ];
		uNames := ["u"*Sprint(i) : i in [0..g] ];
		AssignNames(~PDeformation, tNames cat uNames);
		if printDeformationProcess then
			print "Chosen deformation:";
			print Deformation;
		end if;
		
		// Elimination of variables (using Groebner bases)
		PP := PolynomialRing(CoefficientRing(PDeformation),totalDim);
		AssignNames(~PP, Names(PDeformation));
		I := ideal<PP| Deformation>;
		// printf "I =\n"; IndentPush(); printf "%o\n", I; IndentPop();
		J := EliminationIdeal(I, {1..(T+2)});
		// printf "J =\n"; IndentPush(); printf "%o\n", J; IndentPop();
		ff := Basis(J)[1];
		// printf "ff = %o\n\n", ff;
		// PPP := PolynomialRing(CoefficientRing(PDeformation),T+2);
		// AssignNames(~PPP, Names(PDeformation)[1..T] cat ["x","y"]);
		// printf "PPP =\n"; IndentPush(); printf "%o\n", PPP; IndentPop();
		// ff := Evaluate(ff, [PPP.i : i in [1..(T+2)]] cat [0 : i in [3..(g+1)]]);
		// printf "ff = %o\n\n", ff;
		f := Normalize(ff);
		if printDeformationProcess then printf "\n"; end if;
		
		// Separate parameters into the coefficient ring
		// From: Q[t_0, ..., t_{T-1}, u_0, ..., u_g]
		// To:   Q(t_0, ..., t_{T-1})[x,y]
		// u_0=x, u_1=y, ( u_2, ..., u_g have already been eliminated from the polynomials, can be evaluated to 0 )
		if T eq 0 then
			P<x,y> := LocalPolynomialRing(Q, 2);
			R := BaseRing(P);
			ts := [P | ];
		else
			P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, T), 2);
			R := BaseRing(P);
			tNames := ["t"*Sprint(i) : i in parameters ]; // in [1..T]
			AssignNames(~R, tNames);
			ts := [P | R.i : i in [1..T]];
		end if;
		// gs := [Evaluate(pol, ts cat [x,y] cat [0 : i in [2..g]]) : pol in gs];
		//gUnits := [Evaluate(pol, ts cat [x,y] cat [0 : i in [2..g]]) : pol in gUnits];
		f := Evaluate(f, ts cat [x,y] cat [0 : i in [2..g]]);
		f /:= LeadingCoefficient(f);
		// printf "f = %o\n", f;
		// printf "MaxContactElements = %o\n", MaxContactElements(f);
		
		// Save needed non-zero parameters as variables
		for i in neededParams do
			j := Position(parameters, i);
			//Append(~invertibleVariables, j);
			Include(~assumeNonzero, R.j);
		end for;



	when "deformation_cassou": // Generic curve construction
		// INPUT
		_betas := semigroup;
		error if (not IsPlaneCurveSemiGroup(_betas)), "Please define a valid plane branch semigroup. Given: ", _betas;
		
		// Name
		curve := &*[Sprint(_b)*"-" : _b in _betas];
		curve := curve[1..#curve-1];
		
		if printDeformationProcess or printParameterOptions then print "Semigroup:", _betas; end if;
		
		// Topological information
		//semiGroupInfo := SemiGroupInfo(_betas);
		//g, c, betas, es, ms, ns, qs, _ms := Explode(semiGroupInfo);
		planeBranchNumbers := PlaneBranchNumbers(_betas);
		g, c, betas, es, ms, ns, qs, _betas, _ms, Nps, kps, Ns, ks := Explode(planeBranchNumbers);
		
		// // Choice of monomial curve equations and their deformations
		// eqs := allMonomialCurves(_betas); // [ [i-th equation options] ]
		// if (printDeformationProcess) then
		// 	print "Possible undeformed equations in space:";
		// 	for i in [1..#_betas-1] do
		// 		printf "Equation %o options:\n", i;
		// 		print eqs[i];
		// 	end for;
		// end if;
		// error if (ExtendedType(whichEquations) ne SeqEnum[RngIntElt]), "Please define a valid list of equation indexes";
		// error if (#whichEquations lt (#_betas-1)), "Please define a valid list of equation indexes, # of indexes too small";
		// whichEquations := whichEquations[1..g];
		// error if (&or[ (eqIdx le 0) or (eqIdx gt #(eqs[i])) : i -> eqIdx in whichEquations ]), "Please define a valid list of equation indexes, index out of bounds";
		// monomialCurve := [eqs[i, whichEquations[i]] : i in [1..#_betas-1]]; // Select the chosen equations
		// if (printDeformationProcess) then print "Chosen equation indexes:", whichEquations; end if;
		// if (printDeformationProcess) then print "Chosen equations:"; end if;
		// if (printDeformationProcess) then print monomialCurve; end if;
		
		// Deform the chosen monomial curve equations
		monomialCurve, Deformation := DeformationCurveCassou(_betas);
		// printf "Deformation =\n"; IndentPush(); printf "%o\n", Deformation; IndentPop();
		// printf "DeformationCurveSpecific\n%o\n", Deformation;
		
		PDeformation := Universe(Deformation); // Q[t_0, ..., t_{T-1}, u_0, ..., u_g] (localization)
		// printf "PDeformation =\n"; IndentPush(); printf "%o\n", PDeformation; IndentPop();
		totalDim := Rank(PDeformation);
		// g := #Deformation; // g = # of equations in space (F_1, ..., F_g), g+1 = # variables (u_0, ..., u_g)
		T := totalDim-(g+1); // # of parameters (t_0, ..., t_{T-1})
		
		// Determine, separate and show the needed and optional deformation parameters
		if printDeformationProcess or printParameterOptions then print "Parameters:"; end if;
		neededParams := []; // parameter needed at each Fi
		optionalParams := []; // [ [optional parameters for Fi] ]
		// Parameters of F_1, ..., F_{g-1}
		// F_i = f_i(u_0,...,u_i) - t_?*u_{i+1} + sum_r( t_?*phi_{r,i}(u_0,...,u_g) )
		for i in [1..g-1] do
			Fi := Deformation[i];
			ei := [ (j eq i+1) select 1 else 0 : j in [0..g] ]; // [0, ..., 0, 1, 0, ..., 0] at position corresponding to u_{i+1} among "u"s
			optionalParams[i] := [];
			for term in Terms(Fi) do
				exps := Exponents(term); // exponents of ts and us
				tExps := exps[1..T]; // exponents of (t_0, ..., t_{T-1})
				uExps := exps[T+1..T+g+1]; // exponents of (u_0, ..., u_g)
				if uExps eq ei then // Term t_?*u_{i+1} is necessarily nonzero, save t_? as needed parameter
					tIndex := Explode([j : j in [0..T-1] | tExps[j+1] gt 0]); // index of t_?
					Append(~neededParams, tIndex);
				else // Term is optional, save the new optional parameters of this divisor
					for j in [0..T-1] do
						if (tExps[j+1] gt 0) and (j notin neededParams) and (j notin &cat(optionalParams)) then
							Append(~optionalParams[i], j);
						end if;
					end for;
				end if;
			end for;
			Sort(~optionalParams[i]);
			if printDeformationProcess or printParameterOptions then printf "    Optional at E%o: %o\n", i, optionalParams[i]; end if;
		end for;
		// F_g treated separately, no neededParams
		// F_g = f_g(u_0,...,u_g) + sum_r( t_?*phi_{r,g}(u_0,...,u_g) )
		Fg := Deformation[g];
		optionalParams[g] := [];
		for term in Terms(Fg) do
			exps := Exponents(term); // exponents of ts and us
			tExps := exps[1..T]; // exponents of (t_0, ..., t_{T-1})
			uExps := exps[T+1..T+g+1]; // exponents of (u_0, ..., u_g)
			// Term is optional, save the new optional parameters of this divisor
			for j in [0..T-1] do
				if (tExps[j+1] gt 0) and (j notin neededParams) and (j notin &cat(optionalParams)) then
					Append(~optionalParams[g], j);
				end if;
			end for;
		end for;
		Sort(~optionalParams[g]);
		if printDeformationProcess or printParameterOptions then
			printf "    Optional at E%o: %o\n", g, optionalParams[g];
			for i in [1..g-1] do
				printf "    Needed at E%o: %o\n", i, neededParams[i];
			end for;
		end if;
		optionalParams := &cat(optionalParams); // optional parameters from any divisor -> [optional parameters]
		
		// Choose deformation parameters
		// INPUT
		parameters := deformationParameters;
		if Type(parameters) eq MonStgElt and parameters eq "all" then
			parameters := optionalParams;
		else
			error if ((ExtendedType(parameters) ne SeqEnum[RngIntElt]) and (parameters ne [])), "Please define a valid list of parameters. Given ", parameters;
			for p in parameters do
				error if ((p notin optionalParams) and (p notin neededParams)), "Please define a valid list of parameters. Given invalid parameter ", p;
			end for;
		end if;
		parameters cat:= neededParams; // neededParams always have to be included
		parameters := [p : p in Set(parameters)]; // remove duplicates
		Sort(~parameters);
		if printDeformationProcess or printParameterOptions then printf "Chosen parameters: %o\n", parameters; end if;
		// Create structures with the new number of parameters
		newT := #parameters; // (temp variable) updated # of parameters (t_0, ..., t_{newT-1})
		PDeformation := LocalPolynomialRing(Q, newT+(g+1)); // polynomial ring with updated # of parameters
		// Create vector "oldToNewParam" which for each old parameter contains the corresponding new parameter (as variable) or a 0
		
		oldToNewParam := [PDeformation| 0 : i in [1..T]];
		k := 1;
		for i in [0..T-1] do
			if (i in parameters) then
				oldToNewParam[i+1] := PDeformation.k; // t_i -> new k-th variable
				k +:= 1;
			end if;
		end for;
		// Update variables
		newUs := [ PDeformation.i : i in [newT+1..newT+(g+1)]]; // new u_0, ..., u_g
		monomialCurve := [Evaluate(pol, oldToNewParam cat newUs) : pol in monomialCurve]; // Update variables
		Deformation := [Evaluate(pol, oldToNewParam cat newUs) : pol in Deformation]; // Update variables
		T := newT; // Update # of parameters
		us := newUs;
		delete newT; // (delete temp variable)
		delete newUs; // (delete temp variable)
		totalDim := T + g+1; // Update total dimension
		// Set parameter and variable names
		tNames := ["t"*Sprint(i) : i in parameters ];
		uNames := ["u"*Sprint(i) : i in [0..g] ];
		AssignNames(~PDeformation, tNames cat uNames);
		if printDeformationProcess then
			print "Chosen deformation:";
			print Deformation;
		end if;
		
		
		// Elimination of variables (Cassou)
		
		C1 := [ (i lt g) select F + us[i+1 +1] else F : i->F in monomialCurve]; // Add plane curve monomials, to go from monomial curve C_Gamma to C_1
		Deformation := [ (i lt g) select F + us[i+1 +1] else F : i->F in Deformation]; // Add plane curve monomials, to go from deformation of monomial curve C_Gamma to deformation of C_1
		
		gammas := [ [Derivative(F, us[i+1]) : F in C1] : i in [0..g]];
		
		if printDeformationProcess then
			printf "monomialCurve =\n"; print monomialCurve;
			printf "C1 =\n"; print C1;
			printf "Deformation =\n"; print Deformation;
			printf "gammas =\n[\n"; IndentPush();
			for i in [0..g] do
				printf "[\n"; IndentPush();
				for j in [1..g] do
					printf "%o\n", gammas[i+1][j];
				end for;
				IndentPop(); printf "]\n";
			end for;
			IndentPop(); printf "]\n";
		end if;
		
		for i in [1..(g-1)] do
			termsToMove := PDeformation!0;
			for term in Terms(Deformation[i]) do
				exp := Exponents(term)[(T+1)..(T+g+1)];
				if &+(exp[(i+1 +1)..(g +1)]) ne 0 then
					if term ne us[i+1 +1] then
						termsToMove +:= term;
					end if;
				end if;
			end for;
			if printDeformationProcess then printf "termsToMove = %o\n", termsToMove; end if;
			Deformation := [pol - termsToMove * gammas[i+1 +1][j] : j->pol in Deformation];
		end for;
		
		if printDeformationProcess then printf "Deformation =\n"; print Deformation; end if;
		
		// Eliminate variables u2,...,ug
		for i in [1..(g-1)] do
			uip1 := us[i+1 +1] - Deformation[i]; // F=0 -> u2=u2-F
			Deformation[i] := PDeformation!0; // Avoid unnecessary calculations
			Deformation := [Evaluate(pol, T+i+1 +1, uip1) : pol in Deformation];
		end for;
		
		if printDeformationProcess then printf "Deformation =\n"; print Deformation; end if;
		
		f := Deformation[g];
		
		// printf "f =\n"; IndentPush(); printf "%o\n", f; IndentPop();
		
		// Separate parameters into the coefficient ring
		// From: Q[t_0, ..., t_{T-1}, u_0, ..., u_g]
		// To:   Q(t_0, ..., t_{T-1})[x,y]
		// u_0=x, u_1=y, ( u_2, ..., u_g have already been eliminated from the polynomials, can be evaluated to 0 )
		if T eq 0 then
			P<x,y> := LocalPolynomialRing(Q, 2);
			R := BaseRing(P);
			ts := [P | ];
		else
			P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, T), 2);
			R := BaseRing(P);
			tNames := ["t"*Sprint(i) : i in parameters ]; // in [1..T]
			AssignNames(~R, tNames);
			ts := [P | R.i : i in [1..T]];
		end if;
		f := Evaluate(f, ts cat [x,y] cat [0 : i in [2..g]]);
		// f /:= LeadingCoefficient(f); // ????????????????????????????????????
		// printf "f =\n"; IndentPush(); printf "%o\n", f; IndentPop();
		
		// Save needed non-zero parameters as variables
		for i in neededParams do
			j := Position(parameters, i);
			//Append(~invertibleVariables, j);
			Include(~assumeNonzero, 1+R.j);
		end for;
		


	when "deformation_cassou_mod":
		// INPUT
		_betas := semigroup;
		error if (not IsPlaneCurveSemiGroup(_betas)), "Please define a valid plane branch semigroup. Given: ", _betas;
		
		// Name
		curve := &*[Sprint(_b)*"-" : _b in _betas];
		curve := curve[1..#curve-1];
		
		if printDeformationProcess or printParameterOptions then print "Semigroup:", _betas; end if;
		
		// Topological information
		//semiGroupInfo := SemiGroupInfo(_betas);
		//g, c, betas, es, ms, ns, qs, _ms := Explode(semiGroupInfo);
		planeBranchNumbers := PlaneBranchNumbers(_betas);
		g, c, betas, es, ms, ns, qs, _betas, _ms, Nps, kps, Ns, ks := Explode(planeBranchNumbers);
		
		// // Choice of monomial curve equations and their deformations
		// eqs := allMonomialCurves(_betas); // [ [i-th equation options] ]
		// if (printDeformationProcess) then
		// 	print "Possible undeformed equations in space:";
		// 	for i in [1..#_betas-1] do
		// 		printf "Equation %o options:\n", i;
		// 		print eqs[i];
		// 	end for;
		// end if;
		// error if (ExtendedType(whichEquations) ne SeqEnum[RngIntElt]), "Please define a valid list of equation indexes";
		// error if (#whichEquations lt (#_betas-1)), "Please define a valid list of equation indexes, # of indexes too small";
		// whichEquations := whichEquations[1..g];
		// error if (&or[ (eqIdx le 0) or (eqIdx gt #(eqs[i])) : i -> eqIdx in whichEquations ]), "Please define a valid list of equation indexes, index out of bounds";
		// monomialCurve := [eqs[i, whichEquations[i]] : i in [1..#_betas-1]]; // Select the chosen equations
		// if (printDeformationProcess) then print "Chosen equation indexes:", whichEquations; end if;
		// if (printDeformationProcess) then print "Chosen equations:"; end if;
		// if (printDeformationProcess) then print monomialCurve; end if;
		
		// Deform the chosen monomial curve equations
		monomialCurve, Deformation := DeformationCurveCassou(_betas);
		// printf "Deformation =\n"; IndentPush(); printf "%o\n", Deformation; IndentPop();
		// printf "DeformationCurveSpecific\n%o\n", Deformation;
		
		PDeformation := Universe(Deformation); // Q[t_0, ..., t_{T-1}, u_0, ..., u_g] (localization)
		// printf "PDeformation =\n"; IndentPush(); printf "%o\n", PDeformation; IndentPop();
		totalDim := Rank(PDeformation);
		// g := #Deformation; // g = # of equations in space (F_1, ..., F_g), g+1 = # variables (u_0, ..., u_g)
		T := totalDim-(g+1); // # of parameters (t_0, ..., t_{T-1})
		
		// Determine, separate and show the needed and optional deformation parameters
		if printDeformationProcess or printParameterOptions then print "Parameters:"; end if;
		neededParams := []; // parameter needed at each Fi
		optionalParams := []; // [ [optional parameters for Fi] ]
		// Parameters of F_1, ..., F_{g-1}
		// F_i = f_i(u_0,...,u_i) - t_?*u_{i+1} + sum_r( t_?*phi_{r,i}(u_0,...,u_g) )
		for i in [1..g-1] do
			Fi := Deformation[i];
			ei := [ (j eq i+1) select 1 else 0 : j in [0..g] ]; // [0, ..., 0, 1, 0, ..., 0] at position corresponding to u_{i+1} among "u"s
			optionalParams[i] := [];
			for term in Terms(Fi) do
				exps := Exponents(term); // exponents of ts and us
				tExps := exps[1..T]; // exponents of (t_0, ..., t_{T-1})
				uExps := exps[T+1..T+g+1]; // exponents of (u_0, ..., u_g)
				if uExps eq ei then // Term t_?*u_{i+1} is necessarily nonzero, save t_? as needed parameter
					tIndex := Explode([j : j in [0..T-1] | tExps[j+1] gt 0]); // index of t_?
					Append(~neededParams, tIndex);
				else // Term is optional, save the new optional parameters of this divisor
					for j in [0..T-1] do
						if (tExps[j+1] gt 0) and (j notin neededParams) and (j notin &cat(optionalParams)) then
							Append(~optionalParams[i], j);
						end if;
					end for;
				end if;
			end for;
			Sort(~optionalParams[i]);
			if printDeformationProcess or printParameterOptions then printf "    Optional at E%o: %o\n", i, optionalParams[i]; end if;
		end for;
		// F_g treated separately, no neededParams
		// F_g = f_g(u_0,...,u_g) + sum_r( t_?*phi_{r,g}(u_0,...,u_g) )
		Fg := Deformation[g];
		optionalParams[g] := [];
		for term in Terms(Fg) do
			exps := Exponents(term); // exponents of ts and us
			tExps := exps[1..T]; // exponents of (t_0, ..., t_{T-1})
			uExps := exps[T+1..T+g+1]; // exponents of (u_0, ..., u_g)
			// Term is optional, save the new optional parameters of this divisor
			for j in [0..T-1] do
				if (tExps[j+1] gt 0) and (j notin neededParams) and (j notin &cat(optionalParams)) then
					Append(~optionalParams[g], j);
				end if;
			end for;
		end for;
		Sort(~optionalParams[g]);
		if printDeformationProcess or printParameterOptions then
			printf "    Optional at E%o: %o\n", g, optionalParams[g];
			for i in [1..g-1] do
				printf "    Needed at E%o: %o\n", i, neededParams[i];
			end for;
		end if;
		optionalParams := &cat(optionalParams); // optional parameters from any divisor -> [optional parameters]
		
		// Choose deformation parameters
		// INPUT
		parameters := deformationParameters;
		if Type(parameters) eq MonStgElt and parameters eq "all" then
			parameters := optionalParams;
		else
			error if ((ExtendedType(parameters) ne SeqEnum[RngIntElt]) and (parameters ne [])), "Please define a valid list of parameters. Given ", parameters;
			for p in parameters do
				error if ((p notin optionalParams) and (p notin neededParams)), "Please define a valid list of parameters. Given invalid parameter ", p;
			end for;
		end if;
		parameters cat:= neededParams; // neededParams always have to be included
		parameters := [p : p in Set(parameters)]; // remove duplicates
		Sort(~parameters);
		if printDeformationProcess or printParameterOptions then printf "Chosen parameters: %o\n", parameters; end if;
		// Create structures with the new number of parameters
		numL := g-1;
		newT := #parameters; // (temp variable) updated # of parameters (t_0, ..., t_{newT-1})
		R := RationalFunctionField(Q, newT + numL);
		tNames := ["t"*Sprint(i) : i in parameters ];
		lNames := ["l"*Sprint(i) : i in [1..numL] ];
		AssignNames(~R, tNames cat lNames);
		PDeformation := LocalPolynomialRing(R, g+1); // polynomial ring with updated # of parameters
		uNames := ["u"*Sprint(i) : i in [0..g] ];
		AssignNames(~PDeformation, uNames);
		// Create vector "oldToNewParam" which for each old parameter contains the corresponding new parameter (as variable) or a 0
		oldToNewParam := [PDeformation| 0 : i in [1..T]];
		k := 1;
		for i in [0..T-1] do
			if (i in parameters) then
				oldToNewParam[i+1] := (PDeformation!1) * R.k; // t_i -> new k-th variable
				k +:= 1;
			end if;
		end for;
		// Update variables
		newUs := [ PDeformation.i : i in [1..(g+1)]]; // new u_0, ..., u_g
		monomialCurve := [Evaluate(pol, oldToNewParam cat newUs) : pol in monomialCurve]; // Update variables
		Deformation := [Evaluate(pol, oldToNewParam cat newUs) : pol in Deformation]; // Update variables
		T := newT; // Update # of parameters
		us := newUs;
		delete newT; // (delete temp variable)
		delete newUs; // (delete temp variable)
		totalDim := T + numL + g+1; // Update total dimension
		
		// Elimination of variables (Cassou)
		
		C1          := [ (i lt g) select F + R.(T+i) * us[i+1 +1] else F : i->F in monomialCurve]; // Add plane curve monomials, to go from monomial curve C_Gamma to C_1
		Deformation := [ (i lt g) select F + R.(T+i) * us[i+1 +1] else F : i->F in Deformation]; // Add plane curve monomials, to go from deformation of monomial curve C_Gamma to deformation of C_1
		
		gammas := [ [Derivative(F, us[i+1]) : F in C1] : i in [0..g]];
		
		if printDeformationProcess then
			printf "monomialCurve =\n"; print monomialCurve;
			printf "C1 =\n"; print C1;
			printf "Deformation =\n"; print Deformation;
			printf "gammas =\n[\n"; IndentPush();
			for i in [0..g] do
				printf "[\n"; IndentPush();
				for j in [1..g] do
					printf "%o\n", gammas[i+1][j];
				end for;
				IndentPop(); printf "]\n";
			end for;
			IndentPop(); printf "]\n";
		end if;
		
		for i in [1..(g-1)] do
			termsToMove := PDeformation!0;
			for term in Terms(Deformation[i]) do
				exp := Exponents(term);
				if &+(exp[(i+1 +1)..(g +1)]) ne 0 then
					//if term ne R.(T+i) * us[i+1 +1] then
					termsToMove +:= term;
					//end if;
				end if;
			end for;
			termsToMove -:= R.(T+i) * us[i+1 +1];
			if printDeformationProcess then printf "termsToMove = %o\n", termsToMove; end if;
			Deformation := [pol - termsToMove * gammas[i+1 +1][j] / R.(T+i) : j->pol in Deformation];
		end for;
		
		if printDeformationProcess then printf "Deformation =\n"; print Deformation; end if;
		
		// Eliminate variables u2,...,ug
		for i in [1..(g-1)] do
			uip1 := us[i+1 +1] - Deformation[i] / R.(T+i); // F=0 -> u2=u2-F
			//Deformation[i] := PDeformation!0; // Avoid unnecessary calculations
			Deformation := [Evaluate(pol, i+1 +1, uip1) : pol in Deformation];
		end for;
		
		if printDeformationProcess then printf "Deformation =\n"; print Deformation; end if;
		
		f := Deformation[g];
		
		// printf "f =\n"; IndentPush(); printf "%o\n", f; IndentPop();
		
		// Separate parameters into the coefficient ring
		// From: Q[t_0, ..., t_{T-1}, u_0, ..., u_g]
		// To:   Q(t_0, ..., t_{T-1})[x,y]
		// u_0=x, u_1=y, ( u_2, ..., u_g have already been eliminated from the polynomials, can be evaluated to 0 )
		// if T eq 0 then
		// 	P<x,y> := LocalPolynomialRing(Q, 2);
		// 	R := BaseRing(P);
		// 	ts := [P | ];
		// else
		P<x,y> := LocalPolynomialRing(R, 2);
		f := Evaluate(f, [x,y] cat [0 : i in [2..g]]);
		f *:= LCM([Denominator(c) : c in Coefficients(f)]);
		//f /:= LeadingCoefficient(f); // ????????????????????????????????????
		// printf "f =\n"; IndentPush(); printf "%o\n", f; IndentPop();
		
		// Save needed non-zero parameters as variables
		//for i in neededParams do
		for i in [1..numL] do
			j := Position(parameters, neededParams[i]);
			//Append(~invertibleVariables, (T+i));
			Include(~assumeNonzero, R.(T+i) + R.j);
		end for;
		

	else: // input error
		error "Please choose a valid curve";
end case;

printf "\nCurve: %o\n\n", curve;
printf "f = %o\n\n", f;
print "assumeNonzero = "; print assumeNonzero; printf "\n";

//############################
//### Numerical invariants
//############################

if originalCurveString in {"deformation_restricted", "deformation_GroebnerElimination", "deformation_cassou", "deformation_cassou_mod"} then
	_betas := semigroup;
else
	_betas := SemiGroup(f);
end if;
planeBranchNumbers := PlaneBranchNumbers(_betas);
g, c, betas, es, ms, ns, qs, _betas, _ms, Nps, kps, Ns, ks := Explode(planeBranchNumbers);

// Print proximity matrix
printf "Proximity:\n";
proxMat := ProximityMatrix(_betas : ExtraPoint:=true);
//print proxMat;
proxMatSize := Nrows(proxMat);
//if proxMatSize ge 100 then printf "   "; for col in [1..proxMatSize] do printf "%1o", col div 100; end for; printf "\n"; end if;
//printf "    "; for col in [1..proxMatSize] do printf "%1o", (col ge 10) select col div 10 else " "; end for; printf "\n";
//printf "    "; for col in [1..proxMatSize] do printf "%1o", col mod 10; end for; printf "\n";
for row in [1..proxMatSize] do
	//printf "%3o ", row;
	for col in [1..row] do
		case proxMat[row,col]:
			when -1:
				if &+[Z| proxMat[row2,col]:row2 in [row+1..proxMatSize]] eq 0 then
					if &+[Z| proxMat[row,col2]:col2 in [1..col-1]] eq 0 then
						printf "└";
					else
						printf "┴";
					end if;
				else
					if &+[Z| proxMat[row,col2]:col2 in [1..col-1]] eq 0 then
						printf "├";
					else
						printf "┼";
					end if;//├└L┴┼
				end if;
			when 1: printf "%o", row-1;
			else:
				if &+[Z| proxMat[row,col2]:col2 in [1..col-1]] eq 0 then
					printf " ";
				else
					printf "─"; //─├└L
				end if;
		end case;
	end for;
	printf "\n";
end for;
printf "\n";

//##################
//### Candidates
//##################

nusForPoleCandidates, nusForRootCandidatesIncludingUndetermined, nusIncludingTopological, trueNonTopSigmas, coincidingTopAndNonTopSigmas, otherTopologicalSigmas, nonTopSigmaToIndexList, topologicalSigmaToIndexList, trueNonTopSigmasCoincidences, otherTopologicalSigmasCoincidences := CandidatesData(planeBranchNumbers);

if includeTopologicalRootsOfGeometricOriginInDefaultCandidates then
	defaultNus := nusIncludingTopological;
elif includeUndeterminedRootsInDefaultCandidates then
	defaultNus := nusForRootCandidatesIncludingUndetermined;
else
	defaultNus := nusForPoleCandidates;
end if;
nuChoices := [ useDefaultCandidates[r] select defaultNus[r] else nusIfNotDefaultCandidates[r] : r in [1..g]];

// Print candidates info
if printCandidatesLong then
	// Long print
	printf "\n_______________________________________________________________________\n";
	printf "Non-topological candidates (#=%o)\n", #trueNonTopSigmas;
	for sigma in Reverse(Sort([sigma : sigma in trueNonTopSigmas])) do
		printf "%-15o", sigma;
		for r_nu in nonTopSigmaToIndexList[sigma] do
			printf " = sigma_{%-2o,%-5o}", r_nu[1], r_nu[2];
		end for;
		printf "\n";
	end for;
	printf "\n_______________________________________________________________________\n";
	printf "Topological poles that coincide with 'non-topological' sigmas (#=%o)\n", #coincidingTopAndNonTopSigmas;
	for sigma in Reverse(Sort([sigma : sigma in coincidingTopAndNonTopSigmas])) do
		printf "%-15o", sigma;
		for r_nu in nonTopSigmaToIndexList[sigma] do
			printf " = sigma_{%-2o,%-5o}", r_nu[1], r_nu[2];
		end for;
		for r_nu in topologicalSigmaToIndexList[sigma] do
			printf " = topSigma_{%-2o,%-5o}", r_nu[1], r_nu[2];
		end for;
		printf "\n";
	end for;
	printf "\n_______________________________________________________________________\n";
	printf "Topological sigmas, excluding the previous set (#=%o)\n", #otherTopologicalSigmas;
	for sigma in Reverse(Sort([sigma : sigma in otherTopologicalSigmas])) do
		printf "%-15o", sigma;
		for r_nu in topologicalSigmaToIndexList[sigma] do
			printf " = topSigma_{%-2o,%-5o}", r_nu[1], r_nu[2];
		end for;
		printf "\n";
	end for;
else
	// Short print
	printf "\n_______________________________________________________________________\n";
	printf "Coinciding non-topological candidates (#=%o)\n", #trueNonTopSigmasCoincidences;
	for sigma in Reverse(Sort([sigma : sigma in trueNonTopSigmasCoincidences])) do
		printf "%-15o", sigma;
		for r_nu in nonTopSigmaToIndexList[sigma] do
			printf " = sigma_{%-2o,%-5o}", r_nu[1], r_nu[2];
		end for;
		printf "\n";
	end for;
	if includeUndeterminedRootsInDefaultCandidates or includeTopologicalRootsOfGeometricOriginInDefaultCandidates then
		printf "\n_______________________________________________________________________\n";
		printf "Topological poles that coincide with 'non-topological' sigmas (#=%o)\n", #coincidingTopAndNonTopSigmas;
		for sigma in Reverse(Sort([sigma : sigma in coincidingTopAndNonTopSigmas])) do
			printf "%-15o", sigma;
			for r_nu in nonTopSigmaToIndexList[sigma] do
				printf " = sigma_{%-2o,%-5o}", r_nu[1], r_nu[2];
			end for;
			for r_nu in topologicalSigmaToIndexList[sigma] do
				printf " = topSigma_{%-2o,%-5o}", r_nu[1], r_nu[2];
			end for;
			printf "\n";
		end for;
	end if;
	if includeTopologicalRootsOfGeometricOriginInDefaultCandidates then
		printf "\n_______________________________________________________________________\n";
		printf "Topological poles that coincide with topological poles (#=%o)\n", #otherTopologicalSigmasCoincidences ;
		for sigma in Reverse(Sort([sigma : sigma in otherTopologicalSigmasCoincidences ])) do
			printf "%-15o", sigma;
			for r_nu in topologicalSigmaToIndexList[sigma] do
				printf " = topSigma_{%-2o,%-5o}", r_nu[1], r_nu[2];
			end for;
			printf "\n";
		end for;
	end if;
end if;

// Print selected candidates info
printf "\n_______________________________________________________________________\n";
printf "Calculating stratification for the following candidates:\n";
for r in [1..g] do
	printf "E_%o: ", r;
	if useDefaultCandidates[r] then
		if includeTopologicalRootsOfGeometricOriginInDefaultCandidates then
			printf "all candidates, including topological poles of geometric origin";
		elif includeUndeterminedRootsInDefaultCandidates then
			printf "all candidates with nu not in Gamma_%o, ignoring coincidences with topological poles/roots of geometric origin", r;
		else
			printf "all non-geometric candidates";
		end if;
	else
		printf "user-selected nus";
	end if;
	printf " (#=%o):\n", #nuChoices[r];
	IndentPush(); printf "nus = %o\n", nuChoices[r]; IndentPop();
end for;
printf "\n";

//################################
//### Calculate stratification
//################################

L_all, sigma_all, assumeNonzero, Res_all, indexs_Res_all, epsilon_all := ZetaFunctionStratification(f : nuChoices:=nuChoices, assumeNonzero:=assumeNonzero, verboseLevel:=stratificationVerboseLevel, planeBranchNumbers:=planeBranchNumbers);

//#####################
//### Print results
//#####################

if printResultsAfterCompute then
	printf "\n_______________________________________________________________________\n";
	printf "RESULTS\n\n";
	for r in [1..g] do
		for rootIdx in [1..#L_all[r]] do
			printf "sigma_{%o,%o}=%o\n", sigma_all[r][rootIdx][1], sigma_all[r][rootIdx][2], sigma_all[r][rootIdx][3];
			if printApijInResults then
				for AIdx->ij in Sort([elt : elt in indexs_Res_all[r][rootIdx]]) do
					printf "[%o,%o]\n", ij[1], ij[2];
					IndentPush();
					printf "%o\n", SeqElt(Res_all[r][rootIdx],ij);
					//printf (AIdx lt #indexs_Res_all[r][rootIdx]) select ",\n"else "\n";
					IndentPop();
				end for;
				printf "Simplified:\n";
			end if;
			print L_all[r][rootIdx];
			printf "\n";
		end for;
	end for;
	// printf "sigma_all =\n"; printf "%o\n", sigma_all;
	// printf "epsilon_all =\n"; printf "%o\n", epsilon_all;
end if;

//###########################
//### To do when finished
//###########################

printf "\nFinished.\n";
if quitWhenFinished then
	quit;
end if;

