import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushInvertibleIffOfIsReduced
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsObjTwistBySimilitude
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompEqIdOfTwists
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjRigidClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartDenseProOpen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueLiftOfDensePart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionField
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModNOfDvdModulus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TateIsoDifferBySimilitude
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsQProjOverOfIsProjOver
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.DominatesLiftUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleGeneratorExtendingDensePart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabMapOfLbIso
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SabMapOfIsoOfExtendGen
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RangeSubsetAbLocusOfIsProper
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSemiAbelianDescentTameQuotient
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCmTripleMapDescendGroupQuotient
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSemiAbelianTripleOfFiniteQuotient
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsPullbackOfFpqcLeft
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo

noncomputable section

namespace GlobalTheory.ModelRelCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ModelCompare GlobalTheory.Models

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

section Dominates

variable {O' : Type} [CommRing O'] {β' : O' →+* c.F} (Y : Model Xo c β) (Y' : Model Xo c β') (b : O →+* O')
  (hb : β'.comp b = β)

end Dominates

section Dense

variable (Y : Model Xo c β)

theorem densePart (h : IsDedFrac β) : IsLocallyNoetherian Y.X ∧ IsReduced Y.X ∧ Y.X.IsSeparated ∧
    IsPreimmersion Y.j ∧ Flat Y.j ∧ IsDominant Y.j ∧ QuasiCompact Y.j := by
  obtain ⟨⟨_, _⟩, -, hfr⟩ := h
  letI := β.toAlgebra
  obtain ⟨h₁, -, h₂, h₃⟩ :=
    GlobalTheory.genericPart_dense_proOpen O c.F Y.X _ Y.s Y.jQ Y.flat Y.proj Y.jQ_open Y.jQ_dense
  have : ∀ x : Y.X, _root_.IsReduced (Y.X.presheaf.stalk x) := fun x ↦
    have := (Y.normal x).1
    inferInstance
  exact ⟨h₁, isReduced_of_isReduced_stalk Y.X, h₂, h₃⟩

end Dense

section Transition

variable {l₂ : Level H} {Xo₂ : Moduli D l₂} {c₂ : Coeff l₂} {O₂ : Type} [CommRing O₂] {β₂ : O₂ →+* c₂.F}
  (Y : Model Xo c β) (Y₂ : Model Xo₂ c₂ β₂) (hl : l.Dvd l₂) (hF : c.F ≤ c₂.F) (b : O →+* O₂)
  (hb : β₂.comp b = (IntermediateField.inclusion hF).toRingHom.comp β) (π : Y₂.X ⟶ Y.X)

end Transition

section Algebra

open IndefiniteRowSideFullHecke.LevelActionTransitions

end Algebra

section Action

open IndefiniteRowSideFullHecke.LevelActionTransitions (KMax Sends FixesLevel modulus cls exists_sends)

variable (Y : Model Xo c β)

variable {Y}

variable (Y)

end Action

end GlobalTheory.ModelRelCompare
