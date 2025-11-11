/*
	Author: Roger Gomez Lopez
	
	Blowups, transforms, information derived from the semigroup
*/

// Information related to the curve and its blowup(s)

function MatToSeq(M)
	// Sequence containing all matrix elements (preserving index if size is 1xN or Nx1)
	return [ M[i,j] : i in [1..Nrows(M)], j in [1..Ncols(M)] ];
end function;


intrinsic SemiGroupInfo(_betas::[]) -> Tup
	{
		Numbers related to the semigroup and the characteristic exponents.
		Input: _betas -> generators of the semigroup
		Theory indexing of all sequences 0..g -> Magma indexing 1..(g+1)
	}
	g := #_betas - 1; // Number of characteristic exponents (see PHD-Guillem, p.25)
	n := _betas[1]; // Multiplicity of the curve at the origin (see PHD-Guillem, p.24)
	
	charExpsData := CharExponents(_betas); // [<beta_i,e_i>] with e_i at starting point and rupture divisors
	betas := [cExp[1] : cExp in charExpsData]; // defining beta_0=0
	es := [cExp[2] : cExp in charExpsData];
	
	ms := [betas[i] div es[i] : i in [1..g+1]]; // defining m_0=0, m_i=beta_i/e_i (see PHD-Guillem, p.24)
	ns := [0] cat [es[i-1] div es[i] : i in [2..g+1]]; // n_0=0, n_i=e_{i-1}/e_i (see PHD-Guillem, p.24)
	_ms := [_betas[i] div es[i] : i in [1..g+1]]; // _m_i=_beta_i/e_i (see PHD-Guillem, p.25)
	qs := [0] cat [ms[i] - ns[i]*ms[i-1] : i in [2..g+1]]; // q_i=m_i-n_i*m_{i-1} (see PHD-Guillem, p.25)
	c := ns[g+1]*_betas[g+1] - betas[g+1] - (n-1); // Conductor of the semigroup / Milnor number, c=n_g*_beta_g-beta_g-(n-1) (see PHD-Guillem, p.25)
	
	// Characteristic exponents
	//[betas[i] / n : i in [1..g+1]];
	//[ms[i] / &*(ns[2..i+1]) : i in [1..g+1]];
	//PuiseuxExpansionReduced(f);
	
	return < g, c, betas, es, ms, ns, qs, _ms >;
end intrinsic;


intrinsic MultiplicitiesAtAllRuptureDivisors(_betas::[]) -> [], [], [], []
	{
		Multiplicities of the rupture divisors and their adjacent divisors
	}
	// All multiplicities
	ProxMat, e := ProximityMatrix(_betas : ExtraPoint := true); // e: strict transform multiplicities
	N := e*Transpose(ProxMat^(-1)); // (see TFG-Roger, p.16, Prop.2.3.21)
	ones := Matrix([[1 : i in [1..Ncols(ProxMat)]]]); // row matrix (1,...,1)
	k := ones*Transpose(ProxMat^(-1)); // (see TFG-Roger, p.17, Prop.2.3.22)
	e := MatToSeq(e); // e: strict transform multiplicities
	N := MatToSeq(N); // N: total transform multiplicities
	k := MatToSeq(k); // k: canonical divisor multiplicities
	
	// Multiplicities at rupture divisors
	E := -Transpose(ProxMat)*ProxMat; // Dual graph matrix / intersection matrix (see TFG-Roger, p.18, Def.2.3.23)
	EE := RowSequence(E - DiagonalMatrix(Integers(), Diagonal(E))); // Remove diagonal, now EE[i][j]=1 if i!=j and Ei intersects Ej, else EE[i][j]=0
	Rup := [i : i in [1..Ncols(ProxMat)] | &+EE[i] ge 3]; // Rupture divisors' indexes (divisors with >=3 intersections)
	Nps := N[Rup]; // N of rupture divisors
	kps := k[Rup]; // k of rupture divisor
	
	// Multiplicities of divisors adjacent to each rupture divisor
	Ns := [];
	ks := [];
	for p in Rup[1..#Rup] do
		Adj_p := [i : i in [1..Ncols(ProxMat)] | E[p][i] eq 1]; // indexes of divisors adjacent to each rupture divisor (they intersect)
		Append(~Ns, N[Adj_p]); // N's of adjacent divisors
		Append(~ks, k[Adj_p]); // k's of adjacent divisors
		Ns[#Ns,3] := e[p]; // e of the curve (see TFG-Roger, p.27, Def.4.2.1, from PHD-Guillem p.81 Def 8.2 together with p.89 at eq. 9.2)
		ks[#ks,3] := 0; // k of the curve (see TFG-Roger, p.27, Def.4.2.1, from PHD-Guillem p.81 Def 8.2 together with p.89 at eq. 9.2)
	end for;
	
	return Nps, kps, Ns, ks;
end intrinsic;


intrinsic PlaneBranchNumbers(_betas::[]) -> Tup
	{
		TO DO
	}
	g, c, betas, es, ms, ns, qs, _ms := Explode(SemiGroupInfo(_betas));
	Nps, kps, Ns, ks := MultiplicitiesAtAllRuptureDivisors(_betas);
	return < g, c, betas, es, ms, ns, qs, _betas, _ms, Nps, kps, Ns, ks >;
end intrinsic;


intrinsic MultiplicitiesAtThisRuptureDivisor(r::RngIntElt, Nps::[], kps::[], Ns::[], ks::[]) -> RngIntElt, RngIntElt, [], []
	{
		Multiplicities of the r-th rupture divisor and its adjacent divisors
	}
	Np := Nps[r]; // N of rupture divisor
	kp := kps[r]; // k of rupture divisor
	N := Ns[r]; // N's of adjacent divisors
	k := ks[r]; // k's of adjacent divisors
	return Np, kp, N, k;
end intrinsic;


intrinsic Sigma(Np::RngIntElt, kp::RngIntElt, nu::RngIntElt) -> FldRatElt
	{
		Root candidate corresponding to a nu
	}
	return - (kp + 1 + nu) / Np; // (see TFG-Roger p.27 eq.4.2.1)
end intrinsic;


intrinsic SemigroupElements(G::[], mu::RngIntElt) -> {}
	{
		Elements of the semigroup G up to (including) mu
	}
	if #G eq 0 or mu lt 0 then return {}; end if;
	L := {G[1]*i : i in [0..Floor(mu/G[1])]};
	if #G eq 1 then return L; end if;
	semigroupElements := {};
	for a in L do
		semigroupElements join:= {a+b : b in SemigroupElements(G[2..#G], mu-a)};
	end for;
	return semigroupElements;
end intrinsic;


intrinsic Nus(planeBranchNumbers, r : discardTopologial:=true) -> [], []
	{
		Values of nu which may correspond to a varying root of the Bernstein-Sato polynomial, and topological roots
	}
	g, c, betas, es, ms, ns, qs, _betas, _ms, Nps, kps, Ns, ks := Explode(planeBranchNumbers);
	Np, kp, N, k := MultiplicitiesAtThisRuptureDivisor(r, Nps, kps, Ns, ks);
	
	// Topological roots of Bernstein-Sato polynomial:
	// - they are roots for any topologically trivial deformation
	// - they give unit (=> nonzero) residues of the complex zeta function (see TFG-Roger, p.28-29)
	//
	// Their nus correspond to:
	//   semigroup of the divisorial valuation of Er
	//   == semigroup of the (r+1)-th maximal contact element
	// 
	// Beware the inconsistent notation Gamma_i:
	// 1) PHD-Guillem p.120 Theorem 12.3 -> top. roots sigma_i -> Gamma_i: Ei
	// 2) PHD-Guillem p.26 eq.2.22 -> Gamma_i: fi i-th max contact
	//    PHD-Guillem p.26 Lemma 2.10 -> Gamma_i: fi i-th max contact, E_{i-1}
	//    PHD-Guillem p.31 eq.2.43) -> Gamma_{i+1}: Ei => Gamma_i: fi
	// 3) TFG-Roger p.28 eq.4.2.9 AND ALL FOLLOWING RESULTS -> Gamma_i: Ei
	// 4) TFG-Roger p.29 eq.4.2.10 -> Gamma_i: fi => WRONG DEFINITION
	//
	// Define as in 1) and 3) -> Gamma_i: Ei
	//
	// Gamma_r = <
	//   (n_1*n_2*...*n_r) * _m_0,
	//       (n_2*...*n_r) * _m_1,
	//                 ...
	//               (n_r) * _m_{r-1},
	//                  () * _m_r
	// >
	// = < n_{j+1}*...*n_r * _m_j | j = 0,...,r >
	//
	Gamma_r := [ &*(ns[[(j+2)..(r+1)]]) * _ms[j+1] : j in [0..r] ];
	while 0 in Gamma_r do Exclude(~Gamma_r, 0); end while; // Remove all 0's in Gamma_r
	
	mu_r := ns[r+1] * _ms[r+1] - ms[r+1] - &*(ns[2..(r+1)]) + 1;
	Gamma_r_elements := SemigroupElements(Gamma_r, mu_r - 1);
	Gamma_r_elements := Sort([nu : nu in Gamma_r_elements]);
	gaps := Reverse([mu_r - 1 - a : a in Gamma_r_elements]);
	
	// Discard nus corresponding to the other divisors crossing the r-th exceptional divisor (they never correspond to roots of the Bernstein-Sato-polynomial, and they may give infinities and zeros at the calculation of the residue of the complex zeta function)
	// Conditions: _beta_r*sigma not integer
	//             e_{r-1}*sigma not integer
	// (see TFG-Roger, p.28, Th.4.2.6)
	Z := IntegerRing();
	nonTopNus := [nu : nu in gaps | _betas[r+1]*Sigma(Np,kp,nu) notin Z and es[r]*Sigma(Np,kp,nu) notin Z];
	topologicalNus := [nu : nu in (Gamma_r_elements cat [mu_r..(Np-1)]) | _betas[r+1]*Sigma(Np,kp,nu) notin Z and es[r]*Sigma(Np,kp,nu) notin Z];
	
	if discardTopologial then
		nus := nonTopNus;
	else
		nus := Sort(nonTopNus cat topologicalNus);
	end if;
	
	return nus, topologicalNus;
end intrinsic;


intrinsic CandidatesData(planeBranchNumbers) -> [], [], [], {}, {}, {}, Assoc, Assoc, {}
	{
		Return: nusForPoleCandidates, nusForRootCandidatesIncludingUndetermined, nusIncludingTopological, trueNonTopSigmas, coincidingTopAndNonTopSigmas, otherTopologicalSigmas, nonTopSigmaToIndexList, topologicalSigmaToIndexList, trueNonTopSigmasCoincidences, otherTopologicalSigmasCoincidences
	}
	Z := IntegerRing();
	Q := RationalField();
	
	g, c, betas, es, ms, ns, qs, _betas, _ms, Nps, kps, Ns, ks := Explode(planeBranchNumbers);
	
	nonTopNus := [[Z| ] : r in [1..g]];
	topologicalNus := [[Z| ] : r in [1..g]];
	for r in [1..g] do
		Np, kp, N, k := MultiplicitiesAtThisRuptureDivisor(r, Nps, kps, Ns, ks);
		nonTopNus[r], topologicalNus[r] := Nus(planeBranchNumbers, r : discardTopologial:=true);
	end for;
	
	nonTopSigmas := {Q| };
	nonTopSigmaToIndexList := AssociativeArray(); // map sigma_{r,nu} -> [<r_1,nu_1>, ...]
	for r in [1..g] do
		Np, kp, N, k := MultiplicitiesAtThisRuptureDivisor(r, Nps, kps, Ns, ks);
		for nu in nonTopNus[r] do
			sigma := Sigma(Np, kp, nu);
			if sigma in nonTopSigmas then
				Include(~nonTopSigmaToIndexList[sigma], <r,nu>);
			else
				nonTopSigmaToIndexList[sigma] := [<r, nu>];
				Include(~nonTopSigmas, sigma);
			end if;
		end for;
	end for;
	topologicalSigmas := {Q| };
	topologicalSigmaToIndexList := AssociativeArray(); // map sigma_{r,nu} -> [<r_1,nu_1>, ...]
	for r in [1..g] do
		Np, kp, N, k := MultiplicitiesAtThisRuptureDivisor(r, Nps, kps, Ns, ks);
		for nu in topologicalNus[r] do
			sigma := Sigma(Np, kp, nu);
			if sigma in topologicalSigmas then
				Include(~topologicalSigmaToIndexList[sigma], <r,nu>);
			else
				topologicalSigmaToIndexList[sigma] := [<r, nu>];
				Include(~topologicalSigmas, sigma);
			end if;
		end for;
	end for;
	
	coincidingTopAndNonTopSigmas := nonTopSigmas meet topologicalSigmas; // coinciding 1 (or more) nonTop sigma and 1 (or more) top sigma
	trueNonTopSigmas := nonTopSigmas diff coincidingTopAndNonTopSigmas;
	otherTopologicalSigmas := topologicalSigmas diff coincidingTopAndNonTopSigmas;
	
	nusForPoleCandidates := [[Z| ] : r in [1..g]];
	nusForRootCandidatesIncludingUndetermined := [[Z| ] : r in [1..g]];
	nusIncludingTopological := [[Z| ] : r in [1..g]];
	
	for sigma in trueNonTopSigmas do
		for tup in nonTopSigmaToIndexList[sigma] do
			r, nu := Explode(tup);
			Include(~nusForPoleCandidates[r], nu);
			Include(~nusForRootCandidatesIncludingUndetermined[r], nu);
			Include(~nusIncludingTopological[r], nu);
		end for;
	end for;
	for sigma in coincidingTopAndNonTopSigmas do
		for tup in (nonTopSigmaToIndexList[sigma] cat topologicalSigmaToIndexList[sigma]) do
			r, nu := Explode(tup);
			Include(~nusForRootCandidatesIncludingUndetermined[r], nu);
			Include(~nusIncludingTopological[r], nu);
		end for;
	end for;
	for sigma in otherTopologicalSigmas do
		for tup in topologicalSigmaToIndexList[sigma] do
			r, nu := Explode(tup);
			Include(~nusIncludingTopological[r], nu);
		end for;
	end for;
	
	for r in [1..g] do
		Sort(~nusForPoleCandidates[r]);
		Sort(~nusForRootCandidatesIncludingUndetermined[r]);
		Sort(~nusIncludingTopological[r]);
	end for;
	
	trueNonTopSigmasCoincidences := {sigma : sigma in trueNonTopSigmas | #nonTopSigmaToIndexList[sigma] gt 1};
	otherTopologicalSigmasCoincidences := {sigma : sigma in otherTopologicalSigmas | #topologicalSigmaToIndexList[sigma] gt 1};
	
	return nusForPoleCandidates, nusForRootCandidatesIncludingUndetermined, nusIncludingTopological, trueNonTopSigmas, coincidingTopAndNonTopSigmas, otherTopologicalSigmas, nonTopSigmaToIndexList, topologicalSigmaToIndexList, trueNonTopSigmasCoincidences, otherTopologicalSigmasCoincidences ;
end intrinsic;




// Blowup and centering

function xFactor(f)
	// Exponent of common factor x in f (f != 0)
	return Min([IntegerRing() | Exponents(term)[1] : term in Terms(f)]);
end function;


function yFactor(f)
	// Exponent of common factor y in f (f != 0)
	return Min([IntegerRing() | Exponents(term)[2] : term in Terms(f)]);
end function;


function strictPart(f)
	// Separate factors x^A and y^B from f (might result in 1)
	P := Parent(f); x := P.1; y := P.2;
	
	A := xFactor(f);
	B := yFactor(f);
	g := ExactQuotient(f, x^A*y^B);
	if TotalDegree(g) lt 1 and B gt 0 then
		B -:= 1;
		g *:= y;
	end if;
	return g, A, B;
end function;


function TangentTerm(f)
	// Terms of lowest degree of f, excluding factors x,y
	// assert f eq strictPart(f);
	ms := Monomials(f);
	P := Parent(f); min_deg := Infinity(); min_deg_terms := {P| };
	for m in ms do
		deg := TotalDegree(m);
		if deg lt min_deg then
			min_deg := deg;
			min_deg_terms := {P| m};
		elif deg eq min_deg then
			Include(~min_deg_terms, m);
		end if;
	end for;
	return &+[P| MonomialCoefficient(f,m) * m : m in min_deg_terms];
end function;


intrinsic Blowup(strictTransform_f::RngMPolLocElt, xyExp_fw::[], units_f::SetMulti, units_w::SetMulti, pointType::RngIntElt, assumeNonzero::{} : verboseLevel:="default") -> RngMPolLocElt, [], [], SetMulti, SetMulti, RngIntElt, FldElt, [], {}
	{
		Blowup from one rupture divisor to the next one
		
		(total transform of f) = x^xExp_f * y^yExp_f * units_f * strictTransform_f
		(pullback of dx^dy)    = x^xExp_w * y^yExp_w * units_w
		
		pointType:  0 -> starting point, 1 -> free point, 2 -> satellite point
		(0,lambda): intersection of rupture divisor and strict transform after last blowup
		e:          multiplicity of the strict transform
		PI_blowup:  blowup morphism from one rupture divisor to the next one
		
		Assumptions and conventions:
		- point to blow up: (0,0)
		- previous exceptional divisor (at free and satellite points): x=0
		- the other crossing exceptional divsor (at satellite points): y=0
		- strictTransform_f is singular at (0,0) or tangent to x=0
	}
	debugPrint := false;
	
	P := Parent(strictTransform_f); x := P.1; y := P.2; R := BaseRing(P);
	xExp_f, yExp_f, xExp_w, yExp_w := Explode(xyExp_fw);
	
	a := R!0;
	e := 0;
	PI_blowup := [P| x, y];
	
	if verboseLevel in {"detailed"} then printf "Start Blowup\n"; end if;
	
	tan := TangentTerm(strictTransform_f);
	if verboseLevel in {"detailed"} then
		printf "\n--------------------\n";
		printf "pointType = %o\n", pointType;
		printf "strictTransform_f = %o\n", strictTransform_f;
		printf "tan = %o\n", tan;
		printf "local blowup so far = "; print PI_blowup;
	end if;
	error if (TotalDegree(tan) le 0), "At Blowup(): Tangent term is constant\nstrictTransform_f=", strictTransform_f, "\n tangent=", tan; // Should never happen
	
	if pointType eq 0 then
		if verboseLevel in {"detailed"} then printf "pointType eq 0\n"; end if;
		// Ensure x=0 not tangent at initial point
		if Degree(tan,2) eq 0 then
			if verboseLevel in {"detailed"} then printf "Tangent=C*x^e => change of variables (y,x) to make x=0 not tangent\n"; end if;
			// Tangent=C*x^e => change of variables (y,x) to make x=0 not tangent
			
			pi := [P| y, x];
			PI_blowup := [P| Evaluate(t, pi) : t in PI_blowup];
			
			// The following should be irrelevant:
			xExp_f, yExp_f := Explode(< yExp_f, xExp_f >);
			xExp_w, yExp_w := Explode(< yExp_w, xExp_w >);
			units_f := {*P| Evaluate(t, pi)^^m : t -> m in units_f *};
			units_w := {*P| Evaluate(t, pi)^^m : t -> m in units_w *};
			
			// Strict transform of f
			strictTransform_f, A, B := strictPart(Evaluate(strictTransform_f, pi));
			xExp_f +:= A;
			yExp_f +:= B;
			
			// dy^dx = -dx^dy
			Include(~units_w, P!-1);
			
			if verboseLevel in {"detailed"} then printf "strictTransform_f = %o\n", strictTransform_f; end if;
		else
			if (Degree(tan,1) ne 0) then
				// Not tan=C*y^e => tan=C*(a*x + b*y)^e
				
				// Remove common multiplicative unit
				num := GCD([RingOfIntegers(R)| Numerator(coeff) : coeff in Coefficients(tan)]);
				den := GCD([RingOfIntegers(R)| Denominator(coeff) : coeff in Coefficients(tan)]);
				tan := tan * den / num;
				// tan=(a*x + b*y)^e
				
				e := Degree(tan, y);
				bToTheE := MonomialCoefficient(tan, y^e);
				if verboseLevel in {"detailed"} then
					printf "bToTheE = %o\n", bToTheE;
					print &*[R| tup[1] : tup in Factorization(Numerator(bToTheE))];
					print &*[R| tup[1] : tup in Factorization(Denominator(bToTheE))];
				end if;
				
				if Type(R) eq FldFunRat then // R = Q(t_1,...,t_k)
					if bToTheE notin BaseRing(R) then // bToTheE depends on t_i
						nonzeroFactors := [RingOfIntegers(R)| tup[1] : tup in Factorization(Numerator(bToTheE)) cat Factorization(Denominator(bToTheE))];
						//bNonzeroFactors := Reduce(bNonzeroFactors);
						firstPrint := true;
						for h in nonzeroFactors do
							if h notin assumeNonzero then
							//if h notin ideal<RingOfIntegers(R)| assumeNonzero> then
								if firstPrint then printf "\n"; firstPrint := false; end if;
								printf "WARNING! Assuming that the following is nonzero:\n"; print h; printf "\n";
								Include(~assumeNonzero, h);
								//assumeNonzero := Reduce(assumeNonzero);
							end if;
						end for;
					end if;
				end if;
			end if;
		end if;
	end if;
		
	
	while true do
		tan := TangentTerm(strictTransform_f);
		if verboseLevel in {"detailed"} then
			printf "\n--------------------\n";
			printf "pointType = %o\n", pointType;
			printf "strictTransform_f = %o\n", strictTransform_f;
			printf "tan = %o\n", tan;
			printf "local blowup so far = "; print PI_blowup;
		end if;
		error if (TotalDegree(tan) le 0), "At Blowup(): Tangent term is constant\nstrictTransform_f=", strictTransform_f, "\n tangent=", tan; // Should never happen
		
		if (pointType ne 0) and (Length(tan) eq 1) and (Exponents(tan)[2] eq 0) and (Exponents(tan)[1] gt 0) then
			if verboseLevel in {"detailed"} then printf "Tangent=C*x^e => next point is satellite\n"; end if;
			// Tangent=C*x^e => next point is satellite
			pointType := 2;
			
			pi := [P| x*y, x];
			PI_blowup := [P| Evaluate(t, pi) : t in PI_blowup];
			
			// x^xExp * y^yExp -> (x*y)^xExp * x^yExp = x^(xExp+yExp) * y^xExp
			xExp_f, yExp_f := Explode(< xExp_f + yExp_f, xExp_f >);
			xExp_w, yExp_w := Explode(< xExp_w + yExp_w, xExp_w >);
			
			// Blow up the units, preserve multiplicity
			// They will continue to be units after blowup (no common x,y)
			units_f := {*P| Evaluate(t, pi)^^m : t -> m in units_f *};
			units_w := {*P| Evaluate(t, pi)^^m : t -> m in units_w *};
			
			// Blow up the strict transform of f
			strictTransform_f, A, B := strictPart(Evaluate(strictTransform_f, pi));
			xExp_f +:= A;
			yExp_f +:= B;
			
			// Pullback of dx^dy by pi
			// dx^dy -> d(x*y)^dx = (y dx + x dy)^dx = -x dx^dy
			xExp_w +:= 1;
			Include(~units_w, P!-1);
		else
			if verboseLevel in {"detailed"} then printf "Case not tangent to x=0\n"; end if;
			// Case not tangent to x=0
			
			pi := [P| x, x*y];
			PI_blowup := [P| Evaluate(t, pi) : t in PI_blowup];
			
			// x^xExp * y^yExp -> x^xExp * (x*y)^yExp = x^(xExp+yExp) * y^yExp
			xExp_f, yExp_f := Explode(< xExp_f + yExp_f, yExp_f >);
			xExp_w, yExp_w := Explode(< xExp_w + yExp_w, yExp_w >);
			
			// Blow up the units, preserve multiplicity
			// They will continue to be units after blowup (no common x,y)
			units_f := {*P| Evaluate(t, pi)^^m : t -> m in units_f *};
			units_w := {*P| Evaluate(t, pi)^^m : t -> m in units_w *};
			
			// Blow up the strict transform of f
			strictTransform_f, A, B := strictPart(Evaluate(strictTransform_f, pi));
			xExp_f +:= A;
			yExp_f +:= B;
			
			// Pullback of dx^dy by pi
			// dx^dy -> dx^d(x*y) = dx^(y dx + x dy) = x dx^dy
			xExp_w +:= 1;
			
			if verboseLevel in {"detailed"} then printf "strictTransform_f = %o\n", strictTransform_f; end if;
			
			g0y := Evaluate(strictTransform_f, [0,y]); // g(0,y) = C*(y-a)^d = C*y^d - C*d*a*y^(d-1) + ...
			if verboseLevel in {"detailed"} then printf "g0y = %o\n", g0y; end if;
			d := TotalDegree(g0y); // >=1
			error if (d lt 1), "At Blowup(): Strict transform does not intersect the exceptional divisor. Strict transform = ", strictTransform_f, ", at x=0: ", g0y, ", degree=", d;
			if verboseLevel in {"detailed"} then printf "d = %o\n", d; end if;
			C := MonomialCoefficient(g0y, y^d);
			if verboseLevel in {"detailed"} then printf "C = %o\n", C; end if;
			
			// C != 0
			if Type(R) eq FldFunRat then // R = Q(t_1,...,t_k)
				if C notin BaseRing(R) then // C depends on t_i
					nonzeroFactors := [RingOfIntegers(R)| tup[1] : tup in Factorization(Numerator(C)) cat Factorization(Denominator(C))];
					firstPrint := true;
					for h in nonzeroFactors do
						if h notin assumeNonzero then
							if firstPrint then printf "\n"; firstPrint := false; end if;
							printf "WARNING! Assuming that the following is nonzero:\n"; print h;
							Include(~assumeNonzero, h);
						end if;
					end for;
				end if;
			end if;
			
			Cda := MonomialCoefficient(g0y, y^(d-1));
			a := (-1/d) * Cda / C;
			if verboseLevel in {"detailed"} then printf "a = %o\n", a; end if;
			
			if pointType eq 2 then
				if a eq 0 then
					if verboseLevel in {"detailed"} then printf "Satellite to satellite\n"; end if;
					pointType := 2;
				else
					if verboseLevel in {"detailed"} then printf "Free point on a rupture divisor\n"; end if;
					// Free point on a rupture divisor
					pointType := 1;
					break;
				end if;
			else
				if verboseLevel in {"detailed"} then printf "Free point\nCenter the point\n"; end if;
				// Free point
				pointType := 1;
				
				pi := [P| x, a + y];
				PI_blowup := [P| Evaluate(t, pi) : t in PI_blowup];
				
				// Change variables of each term, preserve multiplicity
				// They are units and will be units after change of variables
				// because the point is free: no common x,y
				units_f := {*P| Evaluate(t, pi)^^m : t -> m in units_f *};
				units_w := {*P| Evaluate(t, pi)^^m : t -> m in units_w *};
				
				// x^xExp * y^yExp -> x^xExp * (y-a)^yExp
				Include(~units_f, (pi[2])^^yExp_f);
				Include(~units_w, (pi[2])^^yExp_w);
				yExp_f := 0;
				yExp_w := 0;
				
				strictTransform_f, A, B := strictPart(Evaluate(strictTransform_f, pi));
				xExp_f +:= A;
				yExp_f +:= B;
				
				// dx^d(y-a) = dx^dy
				
				if verboseLevel in {"detailed"} then printf "strictTransform_f = %o\n", strictTransform_f; end if;
			end if;
		end if;
	end while;
	
	if verboseLevel in {"detailed"} then printf "strictTransform_f = %o\n", strictTransform_f; end if;
	// Free point on a rupture divisor (not centered)
	
	// a != 0
	if Type(R) eq FldFunRat then // R = Q(t_1,...,t_k)
		if a notin BaseRing(R) then // a depends on t_i
			nonzeroFactors := [RingOfIntegers(R)| tup[1] : tup in Factorization(Numerator(a)) cat Factorization(Denominator(a))];
			firstPrint := true;
			for h in nonzeroFactors do
				if h notin assumeNonzero then
					if firstPrint then printf "\n"; firstPrint := false; end if;
					printf "WARNING! Assuming that the following is nonzero:\n"; print h;
					Include(~assumeNonzero, h);
				end if;
			end for;
		end if;
	end if;
	
	// y-a=...*(1-lambda*y) => lambda=1/a
	lambda := 1 / a;
	
	if verboseLevel in {"detailed"} then
		printf "\n";
		printf "lambda = %o\n", lambda;
		printf "local blowup final = "; print PI_blowup;
		printf "strict transform = %o\n", strictTransform_f;
		printf "total transform of f has x^%o y^%o %o\n", xExp_f, yExp_f, &cat[Sprintf("(%o)^%o ",u,m):u->m in units_f];
		printf "total transform of w has x^%o y^%o %o\n", xExp_w, yExp_w, &cat[Sprintf("(%o)^%o ",u,m):u->m in units_w];;
		printf "\nEnd Blowup\n";
	end if;
	
	return strictTransform_f, [xExp_f,yExp_f], [xExp_w,yExp_w], units_f, units_w, pointType, lambda, PI_blowup, assumeNonzero;
end intrinsic;


intrinsic CenterOriginOnCurve(strictTransform_f::RngMPolLocElt, xyExp_fw::[], units_f::SetMulti, units_w::SetMulti, lambda::FldElt, assumeNonzero::{} : verboseLevel:="default") -> RngMPolLocElt, [], [], SetMulti, SetMulti, []
	{
		Change y variable moving (0, 1/lambda) to (0,0)
		
		Sends (0,0) to (0,1), (0,infinity) to (0,infinity)
	}
	debugPrint := false;
	
	P := Parent(strictTransform_f); x := P.1; y := P.2; R := BaseRing(P);
	xExp_f, yExp_f, xExp_w, yExp_w := Explode(xyExp_fw);
	
	// Center intersecion with current exceptional divisor to (0,0)
	if verboseLevel in {"detailed"} then
		printf "\n";
		printf "--------------------\n";
		printf "Start CenterOriginOnCurve\n";
		printf "strictTransform_f = %o\n", strictTransform_f;
	end if;
	
	// lambda != 0
	// This should not trigger because it has been performed in Blowup() for a=1/lambda
	if Type(R) eq FldFunRat then // R = Q(t_1,...,t_k)
		if lambda notin BaseRing(R) then // a depends on t_i
			nonzeroFactors := [RingOfIntegers(R)| tup[1] : tup in Factorization(Numerator(lambda)) cat Factorization(Denominator(lambda))];
			firstPrint := true;
			for h in nonzeroFactors do
				if h notin assumeNonzero then
					if firstPrint then printf "\n"; firstPrint := false; end if;
					printf "WARNING! Assuming that the following is nonzero:\n"; print h;
					Include(~assumeNonzero, h);
				end if;
			end for;
		end if;
	end if;
	
	//pi := [x, (1-y)/lambda];
	pi := [P| x, 1/lambda + y];
	
	// Change variables of each term, preserve multiplicity
	// They are units and will be units after change of variables
	// because the point is free: no common x,y
	units_f := {*P| Evaluate(t, pi)^^m : t -> m in units_f *};
	units_w := {*P| Evaluate(t, pi)^^m : t -> m in units_w *};
	
	// x^xExp * y^yExp -> x^xExp * ((1-y)/lambda)^yExp
	Include(~units_f, (pi[2])^^yExp_f);
	Include(~units_w, (pi[2])^^yExp_w);
	yExp_f := 0;
	yExp_w := 0;
	
	strictTransform_f, A, B := strictPart(Evaluate(strictTransform_f, pi));
	xExp_f +:= A;
	yExp_f +:= B;
	
	// Pullback of dx^dy by pi
	//// dx^d((1-y)/lambda) = -1/lambda dx^dy
	//Include(~units_w, -1/lambda);
	// dx^d(1/lambda + y) = dx^dy
	
	if verboseLevel in {"detailed"} then
		printf "Change of variables = "; print pi;
		printf "strictTransform_f = %o\n", strictTransform_f;
		printf "End CenterOriginOnCurve\n\n";
	end if;
	
	return strictTransform_f, [xExp_f,yExp_f], [xExp_w,yExp_w], units_f, units_w, pi, assumeNonzero;
end intrinsic;




