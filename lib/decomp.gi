
InstallMethod(IsFinerSetOfSubsetsPoset,
"for Poset, Object, Object",
[IsPoset, IsObject, IsObject],
function(P, y, x)
	return ForAll(x, s->ForAny(y, t->Ordering(P)(t,s)));
end);

InstallMethod(IsFinerSets,
"for List, List",
[IsList, IsList],
function(y, x)
	return ForAll(x, s->ForAny(y, t->ForAll(s,a->a in t)));
end);

InstallMethod(RefinementOrdering,
"for Poset",
[IsPoset],
function(P)
	local ord;
    ord := function(sigma, tau)
        return IsFinerSetOfSubsetsPoset(P, sigma, tau);
    end;
    return ord;
end);

InstallMethod(IsDecomposition,
"for Poset, List",
[IsPoset, IsList],
function(P, L)
	local subsets, A, B, i, j, imA, imB, image, image_h, AcapB;
    if Size(L) <> Size(Set(L)) then
        return fail;
    fi;
    subsets := Combinations(L);
	if not JoinElementsIsMax(P, L) or not MeetElementsIsMin(P, L) then
		return false;
	fi;
    image := List(subsets, s->JoinElements(P, s));
    if fail in image or Size(Unique(image)) <> Size(subsets) then
        return false;
    fi;
    image_h := List(image, x->Height(P,x));
    for i in [2..Size(subsets)] do
        A := subsets[i];
        imA := image[i];
        if Height(P, imA) <> Sum(A, x->Height(P, x)) then
            return false;
        fi;
        for j in [i+1..Size(subsets)] do
            B := subsets[j];
            imB := image[j];
            AcapB := Intersection(A, B);
            if image[Position(subsets, AcapB)] <> MeetElements(P, [imA, imB]) then
                return false;
            fi;
        od;
    od;
    return true;
end);



InstallMethod(DecompositionsOfPoset,
"for Poset",
[IsPoset],
function(P)
	local i, j, p, CC, decomp, propP, hP, part, elmByHeight;
    decomp := [];
    i := 2;
    hP:=Height(P);
    propP := Filtered(Set(P), x-> Height(P,x) in [1..hP-1]);
	elmByHeight:=List([1..hP-1], i->Filtered(Set(P), x->Height(P,x)=i));
    while i <= hP do
		part := List(Partitions(hP, i), Collected);
		for p in part do
            CC := List(Cartesian(List(p,m->Combinations(elmByHeight[m[1]],m[2]))), Concatenation);
			if Size(p)>1 then
				CC := Filtered(CC, c->IsAntichain(P,c));
			fi;
			for j in [1..Size(CC)] do
                if IsDecomposition(P, CC[j]) then
                    Add(decomp, CC[j]);
                fi;
            od;
		od;
        i := i+1;
    od;
    return decomp;
end);


InstallMethod(DecompositionsOfMatroid,
"for Poset",
[IsPoset],
function(P)
	local i, j, p, CC, decomp, propP, hP, part, elmByHeight, display;
	display:=Size(P) > 600;
    decomp := [];
    i := 2;
    hP:=Height(P);
    propP := Filtered(Set(P), x-> Height(P,x) in [1..hP-1]);
	elmByHeight:=List([1..hP-1], i->Filtered(Set(P), x->Height(P,x)=i));
    while i <= hP do
		part := List(Partitions(hP, i), Collected);
		for p in part do
            CC := List(Cartesian(List(p,m->Combinations(elmByHeight[m[1]],m[2]))), Concatenation);
			if display then
					Print("Size CC = ",Size(CC),"\n");
			fi;
			if Size(p)>1 then
				CC := Filtered(CC, c->IsAntichain(P,c));
				if display then
					Print("Size CC red = ",Size(CC),"\n");
				fi;
			fi;
			for j in [1..Size(CC)] do
				if display and RemInt(j,1000) =  0 then
					Print("j=",j,"\n");
				fi;
                if JoinElementsIsMax(P,CC[j]) then
                    Add(decomp, CC[j]);
                fi;
            od;
		od;
        i := i+1;
    od;
    return decomp;
end);

InstallMethod(DecompositionPoset,
"for Poset",
[IsPoset],
function(P)
	return PosetByFunctionNC(DecompositionsOfPoset(P), RefinementOrdering(P));
end);

InstallMethod(DecompositionPosetMatroid,
"for Poset",
[IsPoset],
function(P)
	return PosetByFunctionNC(DecompositionsOfMatroid(P), RefinementOrdering(P));
end);

InstallMethod(PDOfPoset,
"for Poset",
[IsPoset],
function(P)
	local decomp;
    decomp := DecompositionsOfPoset(P);
    return Set(Concatenation(List(decomp, d->Concatenation(List([1..Size(d)], i->Combinations(d,i))))));
end);


InstallMethod(PDOfMatroid,
"for Poset",
[IsPoset],
function(P)
	local decomp;
    decomp := DecompositionsOfMatroid(P);
    return Set(Concatenation(List(decomp, d->Concatenation(List([1..Size(d)], i->Combinations(d,i))))));
end);


InstallMethod(PDPoset,
"for Poset",
[IsPoset],
function(P)
	return PosetByFunctionNC(PDOfPoset(P), RefinementOrdering(P));
end);

InstallMethod(PDPosetMatroid,
"for Poset",
[IsPoset],
function(P)
	return PosetByFunctionNC(PDOfMatroid(P), RefinementOrdering(P));
end);


InstallMethod(PartialFramesOfPoset,
"for Poset, Int",
[IsPoset, IsInt],
function(P, n)
	local min;
    if not (n in Integers and n>0) then
        n := Height(P);
    fi;
    min := Filtered(Set(P), x->Height(P,x)=1);
    return Filtered(Combinations(min, n), p->IsDecomposition(P, p));
end);


InstallMethod(FrameComplexOfPoset,
"for Poset",
[IsPoset],
function(P)
	return MaximalSimplicesToSimplicialComplex(PartialFramesOfPoset(P, Height(P)));
end);


InstallMethod(EulerDecompositions,
"for Poset",
[IsPoset],
function(D)
	return -1-Sum(Set(D), d->(-1)^(Size(d)-1)*Factorial( Size(d)-1));
end);

InstallMethod(EulerFrames,
"for Poset",
[IsPoset],
function(F)
	return EulerCharacteristic(F)-1;
end);

InstallMethod(HeightD,
"for Poset, Object",
[IsPoset, IsObject],
function(P, d)
	return Height(P)-Size(d);
end);

InstallMethod(HeightPD,
"for Poset, Object",
[IsPoset, IsObject],
function(P, pd)
	return 2*Sum(pd, x->Height(P,x)) - Size(pd);
end);

