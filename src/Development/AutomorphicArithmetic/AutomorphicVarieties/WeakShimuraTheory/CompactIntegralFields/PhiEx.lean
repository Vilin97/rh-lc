module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.IsAlgClosureField
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.MapApi
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ConjPlace
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.PhiDet
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.PpSingle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.CharpolySmulUnit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.CpCont
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.CpRedProdScaleRoots
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.PhiUnr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ResidueEqOneOfMap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.CharpolyGspConjInvScaled
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.SpacePsiMul
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ResLeMemDec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.PhiFlag

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem chi_map {n : ℕ} {A A' G : Type} [CommRing A] [CommRing A'] [Group G] (E : W.GDet n A G) (f : A →+* A') (g : G) :
    (E.map f).chi (MonoidAlgebra.single g 1) = (E.chi (MonoidAlgebra.single g 1)).map f := by
  rw [← (AlgebraTools.Det.mapApi E f).1, MonoidAlgebra.mapRingHom_single, map_one]
