InstallMethod(TypeAPartitionLattice,
"for Integer",
[IsInt],
function(n)
	local ord, P, i;
	P:=PosetByFunctionNC(PartitionsSet([1..n]), IsFinerSets);;
	P!.heights:=List(Set(P),x->-1);
	for i in [1..Size(P)] do
		P!.heights[i]:=n-Size(Set(P)[i]);
	od;
	return P;
end);


InstallMethod(TypeBPartitions,
"for Integer",
[IsInt],
function(n)
    local b, i, j, m, p, s, t, c0, int, l1, l2, minb, nonMinb, part, prevBlockSize, rem, signs, zeroBlock;
    int:=[];
    for m in [0..n] do
        for c0 in Combinations([1..n], m) do
            zeroBlock := Concatenation(List(c0, l->[l,-l]));
            rem := Filtered([1..n], i->not i in c0);
            for p in PartitionsSet(rem) do
                t:=Size(rem) - Size(p);                
                signs:=Tuples([1,-1], t);
                for s in signs do
                    prevBlockSize:=0;
                    part:=[zeroBlock];
                    for i in [1..Size(p)] do
                        b:=p[i];
                        minb:=Minimum(b);
                        nonMinb:=Filtered(b, x-> x>minb);
                        l1:=[minb];
                        l2:=[-minb];
                        for j in [1..Size(nonMinb)] do
                           Add(l1, nonMinb[j]*s[j+prevBlockSize]); 
                           Add(l2, -nonMinb[j]*s[j+prevBlockSize]);
                        od;
                        Add(part, l1);
                        Add(part, l2);
                        prevBlockSize:=prevBlockSize+Size(nonMinb);
                    od;
                    Add(int, part);
                od;
            od;
        od;
    od;
    return int;
end);

InstallMethod(TypeBPartitionLattice,
"for Integer",
[IsInt],
function(n)
    local P,i,x;
    P:=PosetByFunctionNC(TypeBPartitions(n), IsFinerSets);
    #SetGrading(P,x->n-(Size(x)-1)/2);
	#SetHeights(P);
	P!.heights:=List(Set(P),x->-1);
	for i in [1..Size(P)] do
		x:=Set(P)[i];
		P!.heights[i]:=n-(Size(x)-1)/2;
	od;
    return P;
end);

InstallMethod(EulerTypeBPartitionLattice,
"for Integer",
[IsInt],
function(n)
    return Product([2..n], k->2*k-1);
end);

InstallMethod(DecompPosetTypeBPartitionLattice,
"for Integer",
[IsInt],
function(n)
    return DecompositionPosetMatroid(TypeBPartitionLattice(n));
end);

InstallMethod(PDPosetTypeBPartitionLattice,
"for Integer",
[IsInt],
function(n)
    return PDPosetMatroid(TypeBPartitionLattice(n));
end);
