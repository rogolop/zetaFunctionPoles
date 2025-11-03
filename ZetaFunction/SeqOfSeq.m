/*
	Author: Roger Gomez Lopez
	
	Functions to access and manipulate sequences of sequences using a multi-index
*/


intrinsic ProcOnSeqElt(~s::SeqEnum, I::SeqEnum, Proc::UserProgram, args::Any)
	{
		Proc(~t, i, args), where t[i] eq s[I], considering I as multi-index
	}
	if Type(I) eq RngIntElt then
		Proc(~s, I, args);
	elif #I eq 1 then
		Proc(~s, I[1], args);
	else
		i := I[1];
		Remove(~I, 1);
		if not IsDefined(s, i) then
			s[i] := [];
		end if;
		ProcOnSeqElt(~s[i], I, Proc, args);
	end if;
end intrinsic;


intrinsic AssignSeqElt(~s::SeqEnum, I::SeqEnum, e::Any)
	{
		s[I] := e, considering I as multi-index
	}
	procedure Assign(~s, i, ee)
		s[i] := ee;
	end procedure;
	ProcOnSeqElt(~s, I, Assign, e);
end intrinsic;


intrinsic AssignSeqElt(~s::SeqEnum, ~indexs::SetEnum, I::SeqEnum, e::Any)
	{
		"
	}
	AssignSeqElt(~s, I, e);
	Include(~indexs, I);
end intrinsic;


intrinsic PlusAssignSeqElt(~s::SeqEnum, I::SeqEnum, e::Any)
	{
		s[I] +:= e, considering I as multi-index
	}
	procedure PlusAssign(~s, i, ee)
		if IsDefined(s,i) then
			s[i] +:= ee;
		else
			s[i] := ee;
		end if;
	end procedure;
	ProcOnSeqElt(~s, I, PlusAssign, e);
end intrinsic;


intrinsic PlusAssignSeqElt(~s::SeqEnum, ~indexs::SetEnum, I::SeqEnum, e::Any)
	{
		"
	}
	PlusAssignSeqElt(~s, I, e);
	Include(~indexs, I);
end intrinsic;


intrinsic TimesAssignSeqElt(~s::SeqEnum, I::SeqEnum, e::Any)
	{
		s[I] *:= e, considering I as multi-index
	}
	procedure TimesAssign(~s, i, ee)
		if IsDefined(s,i) then
			s[i] *:= ee;
		end if;
	end procedure;
	ProcOnSeqElt(~s, I, TimesAssign, e);
end intrinsic;


intrinsic UndefineSeqElt(~s::SeqEnum, I::SeqEnum)
	{
		Undefine S[I], considering I as multi-index
	}
	procedure UndefElt(~s, i, ee)
		Undefine(~s, i);
	end procedure;
	ProcOnSeqElt(~s, I, UndefElt, 0);
end intrinsic;


intrinsic UndefineSeqElt(~s::SeqEnum, ~indexs::SetEnum, I::SeqEnum)
	{
		"
	}
	UndefineSeqElt(~s, I);
	Exclude(~indexs, I);
end intrinsic;


intrinsic SeqDepth(s::SeqEnum) -> RngIntElt
	{
		Count how many nested [...] has s (a sequence of sequences)
	}
	d := 0;
	repeat
		d +:= 1;
	until not ISA(ExtendedType(s), eval ("SeqEnum["^d * "Any" * "]"^d));
	return d-1;
end intrinsic;


intrinsic FuncOnSeqElt(s::SeqEnum, I::SeqEnum, Funct::UserProgram, args::Any) -> Any
	{
		Funct(t, i, args), where t[i] eq s[I], considering I as multi-index
	}
	if Type(I) eq RngIntElt then
		return Funct(s, I, args);
	elif #I eq 1 then
		return Funct(s, I[1], args);
	else
		i := I[1];
		Remove(~I, 1);
		if not IsDefined(s, i) then
			s[i] := [];
		end if;
		return FuncOnSeqElt(s[i], I, Funct, args);
	end if;
end intrinsic;


function GetElem(s, i, ee)
	return s[i];
end function;

intrinsic SeqElt(s::SeqEnum, I::SeqEnum) -> Any
	{
		Return s[I], considering I as multi-index
	}
	return FuncOnSeqElt(s, I, GetElem, 0);
end intrinsic;


procedure EvaluateElt(~t, k, ee)
	xii, eee := Explode(ee);
	t[k] := Evaluate(t[k], xii, eee);
end procedure;

intrinsic EvaluateSeq(~s::SeqEnum, ~indexs::SetEnum, xi::RngMPolLocElt, e::Any)
	{
		Evaluate each s[I] at xi=e, considering I as multi-index, for all I in indexs
	}
	for I in indexs do
		ProcOnSeqElt(~s, I, EvaluateElt, [xi,e]);
		if SeqElt(s, I) eq 0 then // Remove zeros
			UndefineSeqElt(~s, I);
			Exclude(~indexs, I);
		end if;
	end for;
end intrinsic;


intrinsic EvaluateSeq(~s::SeqEnum, ~indexs::SetEnum, i::RngIntElt, e::Any)
	{
		"
	}
	if #indexs gt 0 then
		P := Parent(SeqElt(s,Random(indexs)));
		xi := P.i;
		EvaluateSeq(~s, ~indexs, xi, e);
	end if;
end intrinsic;


intrinsic EvaluateSeq(s::SeqEnum, indexs::SetEnum, xi::RngMPolLocElt, e::Any) -> SeqEnum, SetEnum
	{
		"
	}
	EvaluateSeq(~s, ~indexs, xi, e);
	return s, indexs;
end intrinsic;


intrinsic EvaluateSeq(s::SeqEnum, indexs::SetEnum, i::RngIntElt, e::Any) -> SeqEnum, SetEnum
	{
		"
	}
	EvaluateSeq(~s, ~indexs, i, e);
	return s, indexs;
end intrinsic;


intrinsic PrintSeqD(s::SeqEnum, indexs::SetEnum)
	{
		Print sequence of sequences s, element by element, listed by indexs, ordered by total sum of indexes, then the higher first indexs first, writing the indexes -1
	}
	m := SeqDepth(s);
	sum := 0;
	print "[";
	while #indexs gt 0 do
		correctSumIndexs := Reverse(Sort([ I : I in indexs | &+I eq sum]));
		for I in correctSumIndexs do
			print " "^3, Explode([i-1 : i in I]), "->", SeqElt(s, I);
			Exclude(~indexs, I);
		end for;
		sum +:= 1;
	end while;
	print "]";
end intrinsic;


intrinsic PrintSeqFactors(s::SeqEnum, indexs::SetEnum)
	{
		Print the factorization of each element of sequence of sequences s, listed by indexs, ordered by total sum of indexes, then the higher first indexs first, writing the indexes -1
	}
	m := SeqDepth(s);
	sum := 0;
	print "[";
	while #indexs gt 0 do
		correctSumIndexs := Reverse(Sort([ I : I in indexs | &+I eq sum]));
		for I in correctSumIndexs do
			print " "^4*"delta^(", Explode([i-1 : i in I]), ")";
			factorization, coef := Factorization(SeqElt(s, I));
			printf " "^6*"* %o\n", coef;
			for j->factor in factorization do
				printf " "^6*"* ( %o )^%o\n", factor[1], factor[2];
			end for;
			Exclude(~indexs, I);
		end for;
		sum +:= 1;
	end while;
	print "]";
end intrinsic;


intrinsic PrintSeq(s::SeqEnum, indexs::SetEnum)
	{
		Print sequence of sequences s, element by element, listed by indexs
	}
	orderedIndexs := Sort(Setseq(indexs));
	print "[";
	for I in orderedIndexs do
		print " "^3, Explode(I), "->", SeqElt(s, I);
	end for;
	print "]";
end intrinsic;


intrinsic '+'(s::SeqEnum, e::Any) -> SeqEnum
	{
		Elementwise sum of the sequence (of sequences) s and the element e
	}
	return [ x + e : x in s];
end intrinsic;


intrinsic '+'(e::Any, s::SeqEnum) -> SeqEnum
	{
		"
	}
	return s + e; // commutativity
end intrinsic;


intrinsic '+'(t1::Tup, t2::Tup) -> SeqEnum, SetEnum
	{
		Elementwise sum of sequences (...of sequences) with zero removal, treating undef as 0 in element sums
		t1 : <s1, indexs1>
		t2 : <s2, indexs2>
	}
	s1, indexs1 := Explode(t1);
	s2, indexs2 := Explode(t2);
	require Type(s1) eq SeqEnum and Type(indexs1) eq SetEnum: "Bad argument types inside tuple 1\nArgument types given:", Type(s1), ",", Type(indexs1);
	require Type(s2) eq SeqEnum and Type(indexs2) eq SetEnum: "Bad argument types inside tuple 1\nArgument types given:", Type(s2), ",", Type(indexs2);
	
	for I in indexs2 do
		PlusAssignSeqElt(~s1, I, SeqElt(s2, I));
		Include(~indexs1, I);
		if SeqElt(s1, I) eq 0 then
			UndefineSeqElt(~s1, I);
			Exclude(~indexs1, I);
		end if;
	end for;
	return s1, indexs1;
end intrinsic;


intrinsic '-'(s::SeqEnum, e::Any) -> SeqEnum
	{
		Elementwise difference of the sequence (of sequences) s and the element e
	}
	return [ x - e : x in s];
end intrinsic;


intrinsic '*'(s::SeqEnum, t::SeqEnum) -> SeqEnum
	{
		Elementwise product of the sequence (of sequences) s and another sequence,
		expanding the left sequence first, preserving undefined elements
		(=> preserving indexing)
	}
	w := [];
	for i in [1..#s] do
		if IsDefined(s,i) then
			w[i] := s[i] * t;
		end if;
	end for;
	return w;
end intrinsic;


intrinsic '*'(s::SeqEnum, e::Any) -> SeqEnum
	{
		Elementwise product of the sequence (of sequences) s and the element e,
		preserving undefined elements (=> preserving indexing)
	}
	w := [];
	for i in [1..#s] do
		if IsDefined(s,i) then
			w[i] := s[i] * e;
		end if;
	end for;
	return w;
end intrinsic;


intrinsic '*'(e::Any, s::SeqEnum) -> SeqEnum
	{
		"
	}
	return s * e; // commutativity with e non-sequence
end intrinsic;


intrinsic '*'(t1::Tup, t2::Tup) -> SeqEnum, SetEnum
	{
		Produt of sequences (...of sequences)
		t1 : <s1, indexs1>
		t2 : <s2, indexs2>
	}
	s1, indexs1 := Explode(t1);
	s2, indexs2 := Explode(t2);
	require Type(s1) eq SeqEnum and Type(indexs1) eq SetEnum: "Bad argument types inside tuple 1\nArgument types given:", Type(s1), ",", Type(indexs1);
	require Type(s2) eq SeqEnum and Type(indexs2) eq SetEnum: "Bad argument types inside tuple 1\nArgument types given:", Type(s2), ",", Type(indexs2);
	
	t := s1 * s2;
	indexsT := { a cat b : a in indexs1, b in indexs2};
	
	return t, indexsT;
end intrinsic;


intrinsic '/'(s::SeqEnum, e::Any) -> SeqEnum
	{
		Elementwise quotient of the sequence (of sequences) s and the element e
	}
	return [ x / e : x in s];
end intrinsic;





	
