#! @Chapter Decompositions of posets and matroids

DeclareOperation("IsFinerSetOfSubsetsPoset", [IsPoset, IsObject, IsObject]);

DeclareOperation("IsFinerOrderedSetOfSubsetsPoset", [IsPoset, IsObject, IsObject]);

DeclareOperation("IsFinerSets", [IsList, IsList]);

DeclareOperation("RefinementOrdering", [IsPoset]);

DeclareOperation("OrderedRefinementOrdering", [IsPoset]);

DeclareOperation("IsDecomposition", [IsPoset, IsList]);

DeclareOperation("DecompositionsOfPoset", [IsPoset]);

DeclareOperation("DecompositionsOfMatroid", [IsPoset]);

DeclareOperation("DecompositionPoset", [IsPoset]);

DeclareOperation("DecompositionPosetMatroid", [IsPoset]);

DeclareOperation("ToTuples", [IsList]);

DeclareOperation("OrderedDecompositionsOfPoset", [IsPoset]);

DeclareOperation("OrderedDecompositionsOfMatroid", [IsPoset]);

DeclareOperation("OrderedDecompositionPoset", [IsPoset]);

DeclareOperation("OrderedDecompositionPosetMatroid", [IsPoset]);

DeclareOperation("PDOfPoset", [IsPoset]);

DeclareOperation("PDOfMatroid", [IsPoset]);

DeclareOperation("PDPoset", [IsPoset]);

DeclareOperation("PDPosetMatroid", [IsPoset]);

DeclareOperation("PartialFramesOfPoset", [IsPoset, IsInt]);

DeclareOperation("FrameComplexOfPoset", [IsPoset]);

DeclareOperation("EulerDecompositions", [IsPoset]);

DeclareOperation("EulerDecompositionsMatroid", [IsPoset]);

DeclareOperation("EulerOrderedDecompositions", [IsPoset]);

DeclareOperation("EulerOrderedDecompositionsMatroid", [IsPoset]);

DeclareOperation("EulerFrames", [IsPoset]);

DeclareOperation("HeightD", [IsPoset, IsObject]);

DeclareOperation("HeightPD", [IsPoset, IsObject]);

