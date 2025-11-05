// ### Basic requirements ###
AttachSpec("../SingularitiesDim2/IntegralClosureDim2.spec");
AttachSpec("../ZetaFunction/ZetaFunction.spec");
Z := IntegerRing();
Q := RationalField();


// Whether Magma should quit when the calculations are finished
quitWhenFinished    := true;
// Print settings
printCandidatesLong := false;
printCandidatesShort := false;

if false then
	semigroups := Sort([<[a,b,c,d],[a*c,b*c,a*b*(c+d)]> :
		d in [1..9],
		c in [2..9],
		b in [a+1..9],
		a in [2..9] |
		GCD(a,b) eq 1 and GCD(a,c) eq 1 and GCD(b,c) eq 1 and GCD(c,d) eq 1]);
else
	semigroups := Sort([<[a,b,c,d],[a*c,b*c,a*b*(c+d)]> :
		a in {abcd[1]},
		b in {abcd[2]},
		c in {abcd[3]},
		d in {abcd[4]},
		abcd in [[3,8,7,1], [4,5,7,1], [4,5,9,1]] ]);
end if;
for tup in semigroups do
	abcd, G := Explode(tup);
	planeBranchNumbers := PlaneBranchNumbers(G);
	g, c, betas, es, ms, ns, qs, _betas, _ms, Nps, kps, Ns, ks := Explode(planeBranchNumbers);
	nusForPoleCandidates, nusForRootCandidatesIncludingUndetermined, nusIncludingTopological, trueNonTopSigmas, coincidingTopAndNonTopSigmas, otherTopologicalSigmas, nonTopSigmaToIndexList, topologicalSigmaToIndexList, trueNonTopSigmasCoincidences, otherTopologicalSigmasCoincidences := CandidatesData(planeBranchNumbers);
	if #trueNonTopSigmasCoincidences gt 0 then
		printf "a=%o, b=%o, c=%o, d=%o -> Semigroup %o\n", abcd[1], abcd[2], abcd[3], abcd[4], _betas;
		IndentPush();
		// printf "nonTop coincidences: %o\n", #trueNonTopSigmasCoincidences;
		M, e := ProximityMatrix(G);
		printf "#Blowups=%o -> %o\n", Ncols(e), e;
		printf "Non-topological coincidences:\n";
		for sigma in trueNonTopSigmasCoincidences do
			print nonTopSigmaToIndexList[sigma];
		end for;
		printf "Topological-non-topological coincidences:\n";
		for sigma in coincidingTopAndNonTopSigmas do
			printf "%o = %o\n", &cat[Sprintf("%o",tup) cat ((i gt 1)select"="else"") : i->tup in topologicalSigmaToIndexList[sigma]], &cat[Sprintf("%o",tup) cat ((i gt 1)select"="else"") : i->tup in nonTopSigmaToIndexList[sigma]];
		end for;
		printf "\n";
		IndentPop();
	end if;
end for;

quit; ////////////////////////////////////////////////

// a,b,c pairwise coprime
a := 5; // a>=2
b := 7; // b>=a+1
c := 3; // c>=2
d := 1; // d>=1, coprime to c
// 5, 7, 3, 2
// 17, 19, 7, 6
_betas        := [a*c,b*c,a*b*(c+d)]; //[7*4,9*4,7*9*4+7*9*3];
// _betas        := [15,21,175];
// [18,48,146,441];
// [36,96,292,881];
// [5,7];
// [6,17];
// [4,6,13]; [4,10,21]; [6,9,22]; [6,14,43]; [8,18,73]; [10,15,36]; [10,24,121];
// [8,12,26,53];   -> 2-3|2-3|2-3
// [12,16,50,101]; -> 3-4|2-3|2-3
// [12,18,38,115]; -> 2-3|3-4|2-3
// [12,18,39,79];  -> 2-3|2-3|3-4
// [18,45,93,281]; -> 2-5|3-4|3-5 t=[1,73,235] nus=[[], [1,3,4], [2,3,5]]; 
// [36,96,292,881];



print _betas;

planeBranchNumbers := PlaneBranchNumbers(_betas);
g, c, betas, es, ms, ns, qs, _betas, _ms, Nps, kps, Ns, ks := Explode(planeBranchNumbers);

// Candidates
nusForPoleCandidates, nusForRootCandidatesIncludingUndetermined, nusIncludingTopological, trueNonTopSigmas, coincidingTopAndNonTopSigmas, otherTopologicalSigmas, nonTopSigmaToIndexList, topologicalSigmaToIndexList, trueNonTopSigmasCoincidences, otherTopologicalSigmasCoincidences := CandidatesData(planeBranchNumbers);

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
elif printCandidatesShort then
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
	if true then
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
	if false then
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




// To do when finished
printf "\nFinished.\n";
if quitWhenFinished then
	quit;
end if;

