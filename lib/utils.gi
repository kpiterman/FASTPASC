CanonicalRightTransversal:= function(G,H)
	return List(RightTransversal(G,H),i->CanonicalRightCosetElement(H,i));
end;;


InstallMethod(ToPerm,
"for Group",
[IsGroup and IsFinite],
function(G)
	return Image(IsomorphismPermGroup(G));
end);


InstallMethod(PRank,
"for Group, Integer",
[IsGroup and IsFinite, IsInt],
function(G,p)
	local H;
	if not IsPrimeInt(p) then
		Print("p must be a prime number");
		return fail;
	fi;
	if not IsPermGroup(G) then
		H:=ToPerm(G);
	else
		H:=ShallowCopy(G);
	fi;
	return Maximum(List(Filtered(SubgroupsSolvableGroup(SylowSubgroup(H,p)), x->IsElementaryAbelian(x)), y->PValuation(Order(y),p)));
end);


InstallMethod(NrSylowSubgroups,
"for Group, Integer",
[IsGroup and IsFinite, IsInt],
function(G,p)
	if not IsPrimeInt(p) then
		Print("p must be a prime number");
		return fail;
	fi;
	return Order(G) / Order(Normalizer(G,SylowSubgroup(G,p)));
end);


InstallMethod(ReduceConjugacyClasses,
"for Group, List",
[IsGroup, IsList],
function(G, l)
	local reducedList, a;
	reducedList:=[];
	for a in l do
		if ForAll(reducedList, b-> not IsConjugate(G,a,b)) then
			Add(reducedList,a);
		fi;
	od;
	return reducedList;	
end);


InstallMethod(Omega1,
"for Group, Integer",
[IsGroup and IsFinite, IsInt],
function(G, p)
	if not IsPrimeInt(p) then
		Print("p must be a prime number");
		return fail;
	fi;
	return Subgroup(G, Filtered(G, x->Order(x) = p));
end);


InstallMethod(RetOmega1,
"for Group, Group, Integer",
[IsGroup and IsFinite, IsGroup and IsFinite, IsInt],
function(G, A, p)
	if not IsPrimeInt(p) then
		Print("p must be a prime number");
		return fail;
	fi;
	return Omega1(Center(Omega1(Centralizer(G,A),p)),p);
end);


InstallMethod(RepCC,
"for Group",
[IsGroup and IsFinite],
function(G)
	return List(ConjugacyClasses(G),Representative);
end);


InstallMethod(IsRadicalPSubgroup,
"for Group, Group, Integer",
[IsGroup and IsFinite, IsGroup and IsFinite, IsInt],
function(G, R, p)
	if not IsPrimeInt(p) then
		Print("p must be a prime number");
		return fail;
	fi;
	if IsSubgroup(G,R) and IsPGroup(R) and RemInt(Order(R),p)=0 then
		return Order(R) > 1 and Order(R) = Order(PCore(Normalizer(G,R),p));
	fi;
	return false;
end);


InstallMethod(SubgroupOrbit,
"for Group, List",
[IsGroup and IsFinite, IsList],
function(G, l)
	local i, g, H, reps, orbits, ncc, normalizers, transversals;
	
	reps:=ReduceConjugacyClasses(l, G);
	ncc:=Size(reps);
	normalizers:=List(reps, H-> Normalizer(G, H));
	transversals:=List(normalizers, N-> CanonicalRightTransversal(G,N));
	
	orbits:=[];
	
	for i in  [1..ncc] do
		for g in transversals[i] do
			H:=reps[i]^g;
			Add(orbits, H);
		od;
	od;
	
	return orbits;
end);


InstallMethod(PPrimeCore,
"for Group, Integer",
[IsGroup and IsFinite, IsInt],
function(G,p)
	local N;
	if not IsPrimeInt(p) then
		Print("p must be a prime number");
		return fail;
	fi;
	N:=Filtered(NormalSubgroups(G), H->RemInt(Order(H),p) <> 0);
	SortBy(N,Size);
	return Last(N);
end);
