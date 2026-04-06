#! @Chapter Finite groups and p-subgroups


DeclareOperation("ToPerm", [IsGroup and IsFinite]);

DeclareOperation("PRank", [IsGroup and IsFinite, IsInt]);

DeclareOperation("NrSylowSubgroups", [IsGroup and IsFinite, IsInt]);

DeclareOperation("ReduceConjugacyClasses", [IsGroup, IsList]);

DeclareOperation("Omega1", [IsGroup and IsFinite, IsInt]);

DeclareOperation("RetOmega1", [IsGroup and IsFinite, IsGroup and IsFinite, IsInt]);

DeclareOperation("RepCC", [IsGroup and IsFinite]);

DeclareOperation("IsRadicalPSubgroup", [IsGroup and IsFinite, IsGroup and IsFinite, IsInt]);

DeclareOperation("SubgroupOrbit", [IsGroup and IsFinite, IsList]);

DeclareOperation("PPrimeCore", [IsGroup and IsFinite, IsInt]);


