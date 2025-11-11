/*
	Author: Roger Gomez Lopez
	
	Formal derivatives, residues of the complex zeta function, helping functions for the changes of variable
*/

intrinsic DiscardVar(f::RngMPolLocElt, discard::SeqEnum) -> RngMPolLocElt
	{
		Discard terms with powers higher than x_discardVar^discardPow.
		discard = [discardVar, discardPow]
	}
	return &+[Parent(f)| t : t in Terms(f) | Degree(t,discard[1]) le discard[2]];
end intrinsic;


intrinsic ProductDiscardingVar(f::RngMPolLocElt, g::RngMPolLocElt, discard::SeqEnum) -> RngMPolLocElt
	{
		Calculate f*g.
		Discard terms with powers higher than x_discardVar^discardPow at the result
	}
	f := DiscardVar(f, discard);
	g := DiscardVar(g, discard);
	return DiscardVar(f*g, discard);
end intrinsic;


intrinsic PowerDiscardingVar(f::RngMPolLocElt, m::RngIntElt, discard::SeqEnum) -> RngMPolLocElt
	{
		Calculate f^m. Assuming m>=0.
		Discard terms with powers higher than x_discardVar^discardPow at the result
	}
	P := Parent(f);
	if (m lt 0) then return P!0; end if;
	if (m eq 0) then return P!1; end if;
	
	// Truncate f at x_discardVar^m where m is too high
	f := DiscardVar(f, discard);
	
	// Compute power (f o g)^m while truncating
	if (m eq 1) then return f; end if;
	// f^m = (f^mHalf)^2 * f^parity
	parity := m mod 2;
	mHalf := m div 2;
	fmHalf := PowerDiscardingVar(f, mHalf, discard);
	fm := fmHalf * fmHalf;
	fm := DiscardVar(fm, discard);
	if (parity eq 1) then fm *:= f; end if;
	fm := DiscardVar(fm, discard);
	
	return fm;
end intrinsic;


// Formal derivatives

intrinsic FormalDerivative(F::SeqEnum, indexsF::SetEnum, g::SeqEnum[RngMPolLocElt], i::RngIntElt) -> SeqEnum, SetEnum
	{
		Formal derivative of the composition (F o (g1,...,gm))(x1,...) with respect to the i-th variable.
		
		F       : sequence of sequences m times, where F[a1,...,am] represents the coefficient of (d_1^(a1-1) ... d_m^(am-1))F at (g1,...,gm)(x1,...).
		indexsF : nonzero elements of F.
		g       : sequence of functions [g1,...,gm] of (x1,...).
		i       : derive with respect to the i-th variable.
	}
	m := #g;
	DiF := [];
	indexsDiF := indexsF;
	// First term of the derivative: derivate the coefficients
	for a in indexsF do
		value := Derivative(SeqElt(F,a),1,i);
		AssignSeqElt(~DiF, a, value);
	end for;
	// Second term of the derivative: derivate (F o g)
	for a in indexsF do
		for L in [1 .. m] do
			b := a;
			b[L] +:= 1;
			value := SeqElt(F,a) * Derivative(g[L],1,i);
			PlusAssignSeqElt(~DiF, b, value);
			Include(~indexsDiF, b);
		end for;
	end for;
	// Remove zeros
	for a in indexsDiF do
		if SeqElt(DiF,a) eq 0 then
			UndefineSeqElt(~DiF, a);
			Exclude(~indexsDiF, a);
		end if;
	end for;
	return DiF, indexsDiF;
end intrinsic;


intrinsic FormalDerivative(F::SeqEnum, indexsF::SetEnum, g::SeqEnum[RngMPolLocElt], k::RngIntElt, i::RngIntElt) -> SeqEnum, SetEnum
	{
		Derivative of (F o g), k times with respect to the i-th variable
	}
	for repetition in [1..k] do
		F, indexsF := FormalDerivative(F, indexsF, g, i);
	end for;
	return F, indexsF;
end intrinsic;


intrinsic FormalDerivativeDiscardingVar(F::SeqEnum, indexsF::SetEnum, g::SeqEnum[RngMPolLocElt], k::RngIntElt, i::RngIntElt, discard::SeqEnum) -> SeqEnum, SetEnum
	{
		Derivative of (F o g), k times with respect to the i-th variable.
		Discard terms with powers higher than x_discardVar^discardPow at the result
	}
	discardVar, discardPow := Explode(discard);
	Z := IntegerRing();
	if #indexsF gt 0 then
		P := Parent(SeqElt(F,Rep(indexsF)));
	end if;
	
	// Truncate polynomials at x_discardVar^m where m is too high
	for I in indexsF do
		AssignSeqElt(~F, I,  &+[P | t : t in Terms(SeqElt(F,I)) | Degree(t,discardVar) le (k+discardPow)]);
	end for;
	
	// Derivate k times, truncating high powers
	for j in [1..k] do
		// Derivate once
		F, indexsF := FormalDerivative(F, indexsF, g, i);
		// Truncate polynomials at x_discardVar^m where m is too high
		for I in indexsF do
			AssignSeqElt(~F, I,  &+[P | t : t in Terms(SeqElt(F,I)) | Degree(t,discardVar) le (k-j+discardPow)]);
		end for;
	end for;
	
	return F, indexsF;
end intrinsic;


// Residues

function GammaFromTo_Risky(f, t)
	// GammaFromTo(f, t) = Gamma(f) / Gamma(t)
	// f and t must not be nonnegative integers
	// (f-t) must be an integer
	error if ((f-t) notin IntegerRing()), "At GammaFromTo(f, t): f and t must differ by an integer\nGiven arguments: ", f, ",", t;
	result := 1;
	while (f gt t) do
		f -:= 1;
		result *:= f;
	end while;
	while (f lt t) do
		result /:= f;
		f +:= 1;
	end while;
	return result;
end function;


intrinsic E(l::RngIntElt, ek::RngIntElt, epsilon::[]) -> FldFunRatMElt
	{
		( Gamma(epsilon1+1+l) * Gamma(epsilon3+1-ek) / Gamma(epsilon1+epsilon3+2+l-ek) ) / ( Gamma(epsilon1+1) * Gamma(epsilon3+1) / Gamma(epsilon1+epsilon3+2) ).
	}
	return GammaFromTo_Risky( (epsilon[1]+1) + l, epsilon[1]+1 ) *
		GammaFromTo_Risky( (epsilon[3]+1) - ek, epsilon[3]+1 ) /
		GammaFromTo_Risky( (epsilon[1]+epsilon[3]+2) + l - ek, epsilon[1]+epsilon[3]+2 );
end intrinsic;


function listYTerms(f)
	L := [];
	for l in [0..Degree(f,2)] do
		term := Coefficient(f, 2, l);
		if term ne 0 then
			Append(~L, <l, term>);
		end if;
	end for;
	return L;
end function;


intrinsic SeparateYTerms(s::SeqEnum, indexs::SetEnum) -> SeqEnum
	{
		Convert each polynomial in s to a sequence of pairs [l,term], where term is the coefficient of y^l of the polynomial (as member of R[y] with the corresponding ring R)
	}
	w := [];
	for I in indexs do
		AssignSeqElt(~w, I, listYTerms(SeqElt(s, I)));
	end for;
	return w;
end intrinsic;


function FallingFactorial(n, k)
	return &*[Parent(n) | (n-i) : i in [0..k-1]];
end function;


intrinsic ZetaFunctionResidueRelevant(DPhi_terms::SeqEnum, indexs_DPhi::SetEnum, sigma::FldRatElt, lambda::FldElt, epsilon::[], ep::RngIntElt) -> SeqEnum, SetEnum
	{
		Return: i,j (+1) -> Apij
		
		Nonconjugate part of the residue of the complex zeta function, with indexing representing the derivatives of delta(x,y). Multiply the result by its conjugate to obtain the full residue (apart from the multiplying constant).
	}
	Ap := [];
	indexs_Ap := {};
	
	for ijk in indexs_DPhi do
		ij := ijk[1..2]; // numbers of derivatives of delta distribution (+1: kept as indexs)
		k := ijk[3]-1; // number of derivatives of u^s
		
		// Integrate
		pijk_seq := SeqElt(DPhi_terms, ijk); // i,j,k (+1) -> [<  l, pijkl * (-1)^{i+j}  >]
		res := 0;
		for pair in pijk_seq do
			l, pijkl := Explode(pair);
			// Add term to the residue
			res +:= pijkl * lambda^(-l) * E(l, ep*k, epsilon);
		end for;
		PlusAssignSeqElt(~Ap, ~indexs_Ap, ij, res * (-1)^(&+ij));
	end for;
	
	// Remove zeros
	for ij in indexs_Ap do
		if SeqElt(Ap, ij) eq 0 then
			Exclude(~indexs_Ap, ij);
		end if;
	end for;
	return Ap, indexs_Ap;
end intrinsic;


intrinsic SimplifiedBasis(Res::[], indexs_Res::{}, P::RngMPolLoc, assumeNonzero::{} : verboseLevel:="default") -> []
	{
		Get a simplified basis of polynomials
	}
	debugPrint := false;
	
	R := BaseRing(P); // P = R[x,y]
	if #indexs_Res eq 0 then return [R| 0]; end if;
	
	// Ignore which derivative of delta-function
	listRes := [P | SeqElt(Res, ij) : ij in Sort([IJ : IJ in indexs_Res]) ];
	
	// Check that the residues have no terms with x,y => residues are in R
	error if (&or[TotalDegree(res) gt 0 : res in listRes]), "At SimplifiedBasis(Res, indexs_Res, P, assumeNonzero): Res contains x or y\nGiven arguments:", Res, ",", indexs_Res, ",", P, ",", assumeNonzero;
	listRes := [R| MonomialCoefficient(res, P!1) : res in listRes]; // residues are equal to the constant term in x,y
	//if verboseLevel in {"detailed"} then print listRes; end if;
	
	if Type(R) eq FldFunRat then // R = Q(t_1,...,t_k)
		if #listRes eq 0 then
			return [RingOfIntegers(R)| 0];
		end if;
		Rpol := RingOfIntegers(R);
		Q := BaseRing(R);
		k := Rank(R);
		l := #assumeNonzero;
		if verboseLevel in {"detailed"} then print "Clearing nonzero denominators"; end if;
		// Clear denominators while checking that they are nonzero
		for idx->res in listRes do
			denom := Denominator(res);
			denomFactorization := Factorization(denom);
			for tup in denomFactorization do
				factor, exponent := Explode(tup);
				if factor notin assumeNonzero then
					error "At SimplifiedBasis(): Residue has a denominator that may be zero. If it is nonzero, please add it to assumeNonzero.\nResidue term =\n", res, ", denominator factor=\n", factor;
				end if;
			end for;
			listRes[idx] *:= denom;
		end for;
		// Change ring to Q[t_1,...,t_k] and simplify the basis of the ideal
		ChangeUniverse(~listRes, Rpol);
		ChangeUniverse(~assumeNonzero, Rpol);
		if verboseLevel in {"detailed"} then print listRes; end if;
		//print "Computing radical";
		//I := ideal<Rpol| listRes>;
		//listRes := Basis(Radical(I));
		//print listRes;
		if verboseLevel in {"detailed"} then print "Removing factor powers"; end if;
		listRes := [ &*[Rpol|tup[1]:tup in Factorization(Numerator(res))|tup[1] notin assumeNonzero] : res in listRes];
		if verboseLevel in {"detailed"} then print listRes; end if;
		I := ideal<Rpol| listRes>;
		for h in assumeNonzero do
			if h in I then
			//if h in radI then
				return [Rpol| 1];
			end if;
		end for;
		// listRes := Basis(radI);
		// listRes := Reduce(listRes);
		if l gt 0 then
			//if verboseLevel in {"detailed"} then print "Eliminating nonzeros"; end if;
			Rext := PolynomialRing(Q,l+k);
			AssignNames(~Rext,[Sprintf("z%o",i):i in [1..l]] cat [Sprint(R.i):i in [1..k]]);
			listResNew       := [Evaluate(h,[Rext| Rext.(l+i):i in [1..k]]) : h in listRes];
			assumeNonzeroNew := [Evaluate(h,[Rext| Rext.(l+i):i in [1..k]]) : h in assumeNonzero];
			resIdeal       := ideal<Rext| listResNew>;
			relationsIdeal := ideal<Rext| [h*Rext.i - 1 : i->h in assumeNonzeroNew]>;
			I := resIdeal + relationsIdeal;
			if 1 in I then
				return [Rpol| 1];
			end if;
			//I := EliminationIdeal(I, l);
			////I := Radical(I);
			//listRes := Basis(I);
			//listRes := [Evaluate(res,[0:i in [1..l]]cat[Rpol.i:i in [1..k]]) : res in listRes];
			//if verboseLevel in {"detailed"} then print listRes; end if;
			//if verboseLevel in {"detailed"} then print "Removing factor powers"; end if;
			//listRes := [ &*[Rpol|tup[1]:tup in Factorization(Numerator(res))|tup[1] notin assumeNonzero] : res in listRes];
			//if verboseLevel in {"detailed"} then print listRes; end if;
		end if;
		if verboseLevel in {"detailed"} then print "Reduce"; end if;
		listRes := Reduce(listRes);
		if verboseLevel in {"detailed"} then print listRes; end if;
		if Q eq Rationals() then
			if verboseLevel in {"detailed"} then print "Simplifying rationals"; end if;
			// Reduce numerators and denominators as much as possible
			for resIdx->res in listRes do
				countsPositive := AssociativeArray();
				countsNegative := AssociativeArray();
				coeffs, monoms := CoefficientsAndMonomials(res);
				for i in [1..#coeffs] do
					c := coeffs[i];
					m := monoms[i];
					// No need to find all factors
					//factors, sign := Factorization(Numerator(c): Proof:=false, ECMLimit:=0, MPQSLimit:=0);
					factors := Factorization(Numerator(c) : Proof:=false, Bases:=1, SQUFOFLimit:=0, PollardRhoLimit:=0, ECMLimit:=0, MPQSLimit:=0);
					//Factorization(Numerator(c) : Proof:=false, Bases:=1, TrialDivisionLimit:=0, SQUFOFLimit:=0, PollardRhoLimit:=0, ECMLimit:=0, MPQSLimit:=0);
					for tup in factors do
						factor, exp := Explode(tup);
						if IsDefined(countsPositive, factor) then
							Append(~countsPositive[factor], exp);
						else
							countsPositive[factor] := [exp];
						end if;
					end for;
					// No need to find all factors
					//factors, sign := Factorization(Denominator(c): Proof:=false, ECMLimit:=0, MPQSLimit:=0);
					factors := Factorization(Denominator(c) : Proof:=false, Bases:=1, SQUFOFLimit:=0, PollardRhoLimit:=0, ECMLimit:=0, MPQSLimit:=0);
					//Factorization(Denominator(c) : Proof:=false, Bases:=1, TrialDivisionLimit:=0, SQUFOFLimit:=0, PollardRhoLimit:=0, ECMLimit:=0, MPQSLimit:=0);
					for tup in factors do
						factor, exp := Explode(tup);
						if IsDefined(countsNegative, factor) then
							Append(~countsNegative[factor], -exp);
						else
							countsNegative[factor] := [-exp];
						end if;
					end for;
					//printf "%o, %o\n", c, m;
				end for;
				lengthRes := Length(res);
				smallHalfLengthRes := lengthRes div 2;
				bigHalfLengthRes := lengthRes - smallHalfLengthRes;
				//printf "%o, %o\n", lengthRes, res;
				for factor in Keys(countsPositive) join Keys(countsNegative) do
					counts := [];
					if factor in Keys(countsPositive) then counts cat:= countsPositive[factor]; end if;
					if factor in Keys(countsNegative) then counts cat:= countsNegative[factor]; end if;
					N := #counts;
					//printf "factor %o -> #%o %o", factor, N, counts;
					if (N gt smallHalfLengthRes) or (lengthRes mod 2 eq 0 and N eq smallHalfLengthRes and counts[N] lt 0)then
						counts cat:= [0: i in [1..lengthRes-N]];
						Sort(~counts);
						medianExp := counts[bigHalfLengthRes];
						//printf "\n      -> %o, %o", counts, medianExp;
						if medianExp ne 0 then listRes[resIdx] *:= factor^-medianExp; end if;
					end if;
					//printf "\n";
				end for;
			end for;
		end if;
		return listRes;
	elif R eq Rationals() then
		listRes := [R| res : res in listRes | res ne 0];
		if #listRes gt 0 then
			return [R| 1];
		else
			return [R| 0];
		end if;
	else
		//listRes := [R| res : res in listRes | not IsUnit(res)];
		return listRes;
	end if;
end intrinsic;


intrinsic ZetaFunctionResidue(strictTransform_f::RngMPolLocElt, units_f::SetMulti, units_w::SetMulti, PI_TOTAL::[], lambda::FldElt, numbers::Tup: assumeNonzero:={}, verboseLevel:="default") -> List, List, List, List, List
	{
		Return and print stratification of the residue of the complez zeta function at candidate poles corresponding to nus in rupture divisor r, each one as [[]] which is a sequence of generators of the zero ideal, represented as sequences containing their irreducible factors.
		
		verboseLevel: "none", "default", "onlyStrata", or "detailed"
	}
	
	// Prepare arguments
	P:=Parent(strictTransform_f); x:=P.1; y:=P.2; R:=BaseRing(P);
	pi1, pi2 := Explode(PI_TOTAL);
	ep, Np, kp, N, k, nus, r := Explode(numbers);
	
	if #nus eq 0 then
		return [**], [**], [**], [**], [**];
	end if;
	
	nuMax := Max(nus);
	nuOld := 0;
	
	// Units
	//u := &*[t^m : t->m in units_f] * strictTransform_f;
	//v := &*[t^m : t->m in units_w];
	u := P!1;
	for t->m in units_f do
		tm := PowerDiscardingVar(t, m, [1,nuMax]); // t^m
		u := ProductDiscardingVar(u, tm, [1,nuMax]);
	end for;
	u := ProductDiscardingVar(u, strictTransform_f, [1,nuMax]);
	v := P!1;
	for t->m in units_w do
		tm := PowerDiscardingVar(t, m, [1,nuMax]); // t^m
		v := ProductDiscardingVar(v, tm, [1,nuMax]);
	end for;
	
	// u1(x,y) = u(x,y) / u(0,0) -> discard common unit |u(0,0)|^{2 sigma} from the residue (to B_p)
	u1 := u / Evaluate(u, [0,0]);
	
	// pi
	pi1 := DiscardVar(pi1, [1,nuMax]);
	pi2 := DiscardVar(pi2, [1,nuMax]);
	
	// Formal v(x,y) * phi(X,Y) * Z^s, to be evaluated at X=pi1, Y=pi2, Z=u1
	Phi := [[[v]]];
	indexs_Phi := {[1,1,1]};
	
	// Storage
	L_all := [**];
	Ap_all := [**];
	indexs_Ap_all := [**];
	sigma_all := [**];
	epsilon_all := [**];
	
	for nu in nus do
		//repeat // Do once, but group statements to calculate time easily
		
		// Relevant numbers
		sigma := Sigma(Np, kp, nu);
		epsilon := [N[j] * sigma + k[j] : j in [1..3] ];
		
		// // Info regarding the sign of B_p
		// printf "\nepsilon = [ %o, %o, %o ]\n", epsilon[1], epsilon[2], epsilon[3];
		// printf "Fractional part {-eps}: %o, %o, %o\n", FractionalPart(-epsilon[1]), FractionalPart(-epsilon[2]), FractionalPart(-epsilon[3]);
		// RR := RealField();
		// RAprox := RealField(6);
		// printf "cot(pi*(-eps)): %o, %o\n", RAprox!Cot(-Pi(RR)*epsilon[1]), RAprox!Cot(-Pi(RR)*epsilon[3]);
		// printf "cot(pi*(-eps)): %o, %o\n", (Cot(-Pi(RR)*epsilon[1]) gt 0)select"+++"else"---", (Cot(-Pi(RR)*epsilon[3]) gt 0)select"+++"else"---";
		// BFactor := Cot(Pi(RR)*epsilon[1]) + Cot(Pi(RR)*epsilon[3]);
		// printf "cot(pi*eps1)+cot(pi*eps3) = %o%o\n", RAprox!BFactor, (BFactor gt 0)select" !!!!!!"else"";
		
		// Derivative of 1/u(0,0)^s * Phi(pi1(...),pi2(...),u(...); x,y) with respect to x
		Phi, indexs_Phi := FormalDerivativeDiscardingVar(Phi, indexs_Phi, [pi1, pi2, u1], nu-nuOld, 1, [1, nuMax-nu]);
		// Phi = partial_x^nu (u1^s * v * phi|_{pi1,pi2})
		
		DPhi := Phi;
		indexs_DPhi := indexs_Phi;
		// Evaluate at x=0
		EvaluateSeq(~DPhi, ~indexs_DPhi, x, 0);
		// DPhi = partial_x^nu|_{x=0} (u1^s * v * phi|_{pi1,pi2})
		// i,j,k (+1) -> coefficient of ( partial_z1^i|_(0,0) partial_z2^j|_(0,0) phi * partial_Z^k|_u1(0,y) Z^s )
		
		// Convert d^k/dx^k (Z^s) = (s)*...*(s-k+1) * Z^(s-k)
		for ijk in indexs_DPhi do
			k_idx := ijk[3] - 1; // Number of derivatives of Z^s
			TimesAssignSeqElt(~DPhi, ijk, FallingFactorial(sigma, k_idx));
		end for;
		// i,j,k (+1) -> coefficient of ( partial_z1^i|_(0,0) partial_z2^j|_(0,0) phi * u1(0,y)^{sigma-k} )
		
		// Expand polynomials depending on power of y
		DPhi_terms := SeparateYTerms(DPhi, indexs_DPhi);
		// i,j,k (+1) -> [<  l, pijkl * (-1)^{i+j}  >]
		
		// Calculate the relevant part of the residue
		Ap, indexs_Ap := ZetaFunctionResidueRelevant(DPhi_terms, indexs_DPhi, sigma, lambda, epsilon, ep);
		// i,j (+1) -> Apij * (-1)^(i+j)
		
		// print
		if verboseLevel in {"default", "onlyStrata", "detailed"} then
			printf "sigma_{%o,%o}=%o\n", r, nu, sigma;
			if verboseLevel in {"detailed"} then
				for ij in Sort([elt : elt in indexs_Ap]) do
					printf "[%o,%o]\n", ij[1], ij[2];
					IndentPush();
					printf "%o\n", SeqElt(Ap,ij);
					IndentPop();
				end for;
				printf "Simplified:\n";
			end if;
		end if;
		
		// Basis of the ideal whose roots make the residue =0
		L := SimplifiedBasis(Ap, indexs_Ap, P, assumeNonzero : verboseLevel:=verboseLevel);
		
		// Storage
		Append(~L_all, L);
		Append(~Ap_all, Ap);
		Append(~indexs_Ap_all, indexs_Ap);
		Append(~sigma_all, <r, nu,sigma>);
		Append(~epsilon_all, epsilon);
		
		// print
		if verboseLevel in {"default", "onlyStrata", "detailed"} then
			print L;
			printf "\n";
		end if;
		
		nuOld := nu;
		
		//until true;
	end for;
	
	return L_all, Ap_all, indexs_Ap_all, sigma_all, epsilon_all;
end intrinsic;


// Changes of variables

intrinsic Evaluate(f::FldFunRatMElt, i::RngIntElt, r::RngElt) -> FldFunRatMElt
	{
		Evaluate a multivariate rational function in x_i=r
		Necessary in construction of curve from _betas
	}
	return Evaluate(Numerator(f), i, r) / Evaluate(Denominator(f), i, r);
end intrinsic;


// Full stratification

intrinsic ZetaFunctionStratification(f::RngMPolLocElt : nuChoices:=[], assumeNonzero:={}, verboseLevel:="default", planeBranchNumbers:=<>) -> List, List, List, List, List, {}
	{
		Stratification of mu-constant plane branch deformations by the poles of the complex zeta function.
		
		assumeNonzero (if f is defined over a field of rational functions): a list of polynomials that can be assumed to not take the value zero,
		verboseLevel: "none", "default", "onlyStrata", or "detailed"
	}
	debugPrint := false;
	
	// Prepare arguments
	if verboseLevel notin {"none","default","onlyStrata","detailed"} then verboseLevel:="default"; end if;
	P := Parent(f); x:=P.1; y:=P.2; R := BaseRing(P);
	if #planeBranchNumbers eq 0 then // if not provided
		_betas := SemiGroup(f);
		planeBranchNumbers := PlaneBranchNumbers(_betas);
	end if;
	g, c, betas, es, ms, ns, qs, _betas, _ms, Nps, kps, Ns, ks := Explode(planeBranchNumbers);
	if #nuChoices eq 0 then // if not provided
		nusForPoleCandidates, nusForRootCandidatesIncludingUndetermined, nusIncludingTopological, trueNonTopSigmas, coincidingTopAndNonTopSigmas, otherTopologicalSigmas, nonTopSigmaToIndexList, topologicalSigmaToIndexList, trueNonTopSigmasCoincidences, otherTopologicalSigmasCoincidences := CandidatesData(planeBranchNumbers);
		nuChoices := nusForPoleCandidates;
		delete nusForPoleCandidates, nusForRootCandidatesIncludingUndetermined, nusIncludingTopological, trueNonTopSigmas, coincidingTopAndNonTopSigmas, otherTopologicalSigmas, nonTopSigmaToIndexList, topologicalSigmaToIndexList, trueNonTopSigmasCoincidences, otherTopologicalSigmasCoincidences;
	end if;
	if Type(R) eq FldFunRat then
		assumeNonzero := {RingOfIntegers(R)| tup[1] : tup in Factorization(Numerator(h)) cat Factorization(Denominator(h)), h in assumeNonzero};
	end if;
	if verboseLevel in {"detailed"} then printf "assumeNonzero =\n"; print assumeNonzero; end if;
	//error if &or[g notin RingOfIntegers(R) : g in assumeNonzero], "At ZetaFunctionStratification(): assumeNonzero contains elements with denominators";
	
	// (total transform of f) = x^xExp_f * y^yExp_f * units_f * strictTransform_f
	// (pullback of dx^dy)    = x^xExp_w * y^yExp_w * units_w
	strictTransform_f := f;
	xyExp_f := [0,0];
	xyExp_w := [0,0];
	units_f := {*P| 1 *};
	units_w := {*P| 1 *};
	pointType := 0; // 0 -> starting point, 1 -> free point, 2 -> satellite point
	PI_TOTAL := [P| x, y]; // Total blowup morphism since starting point
	L_all := [**];
	Ap_all := [**];
	indexs_Ap_all := [**];
	sigma_all := [**];
	epsilon_all := [**];
	
	// ### For each rupture divisor ###
	// Non-rupture divisors don't contribute (see TFG-Roger, p.28, Cor.4.2.5 or PHD-Guillem p.87 Th.8.10)
	if (verboseLevel in {"default", "onlyStrata", "detailed"}) then printf "\n"; end if;
	for r in [1..g] do
		if (verboseLevel in {"default", "onlyStrata", "detailed"}) then
			printf "_______________________________________________________________________\n";
			printf "Divisor E_%o\n\n", r;
		end if;
		
		// Blowup
		// From: (0,0) singular point of the strict transform of the curve (starting point or a free point on the last rupture divisor)
		// To: next rupture divisor
		strictTransform_f, xyExp_f, xyExp_w, units_f, units_w, pointType, lambda, PI_blowup, assumeNonzero := Blowup(strictTransform_f, xyExp_f cat xyExp_w, units_f, units_w, pointType, assumeNonzero : verboseLevel:=verboseLevel);
		if debugPrint then printf "assumeNonzero =\n"; print assumeNonzero; end if;
		if (verboseLevel in {"default", "detailed"}) then
			printf "lambda = %o\n", lambda;
		end if;
		
		ep := es[r +1];
		// Total blowup morphism since starting point
		PI_TOTAL := [P| Evaluate(t, PI_blowup) : t in PI_TOTAL];
		// Multiplicities of rupture divisor x=0
		Np := xyExp_f[1];
		Kp := xyExp_w[1];
		// Multiplicities of y=0
		N1 := xyExp_f[2];
		K1 := xyExp_w[2];
		// Multiplicities of:
		// 1) proximate non-rupture divisor through (0,0): y=0
		// 2) proximate non-rupture divisor through (0,infinity)
		// 3) the curve
		// Np = N1 + N2 + ep (regardless of coordinates of N1,N2)
		N := [N1, Np-N1-ep, ep];
		k := [K1, Kp-K1-1, 0];
		if debugPrint then
			printf "strict = %o \n", strictTransform_f;
		end if;
		if (verboseLevel in {"detailed"}) then
			printf "Total blowup = "; print PI_TOTAL;
			printf "ep = %o \n", ep;
			printf "es = %o \n", es;
			printf "Np = %o, Nps[r] = %o\n", Np, Nps[r];
			printf "N = %o, Ns[r] = %o\n", N, Ns[r];
			printf "Kp = %o, kps[r] = %o\n", Kp, kps[r];
			printf "k = %o, ks[r] = %o\n", k, ks[r];
		end if;
		
		// printf "u = %o\n\n", u;
		// printf "v = %o\n\n", v;
		// printf "PI_TOTAL = %o\n\n", PI_TOTAL;
		
		nus := nuChoices[r];
		
		if (verboseLevel in {"default", "detailed"}) then
			printf "nus = %o\n\n", nuChoices[r];
		end if;
		
		L_all[r], Ap_all[r], indexs_Ap_all[r], sigma_all[r], epsilon_all[r] := ZetaFunctionResidue(strictTransform_f, units_f, units_w, PI_TOTAL, lambda, <ep, Np, Kp, N, k, nus, r> : assumeNonzero:=assumeNonzero, verboseLevel:=verboseLevel);
		
		// Prepare next iteration
		if r lt g then
			if (verboseLevel in {"detailed"}) then
				printf "_______________________________________________________________________\n";
				printf "Centering the singular point\n";
			end if;
			
			strictTransform_f, xyExp_f, xyExp_w, units_f, units_w, PI_center, assumeNonzero := CenterOriginOnCurve(strictTransform_f, xyExp_f cat xyExp_w, units_f, units_w, lambda, assumeNonzero : verboseLevel:=verboseLevel);
			if debugPrint then printf "assumeNonzero =\n"; print assumeNonzero; end if;
			// Total blowup morphism since starting point
			PI_TOTAL := [P| Evaluate(t, PI_center) : t in PI_TOTAL];
		end if;
	end for;
	
	return L_all, sigma_all, assumeNonzero, Ap_all, indexs_Ap_all, epsilon_all;
end intrinsic;





