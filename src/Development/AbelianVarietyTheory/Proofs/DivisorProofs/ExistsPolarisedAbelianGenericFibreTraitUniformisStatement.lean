module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnifTrait
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamilyFibreEqUniformisedPullbackGenericFibre
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SmoothOfRelativeDimensionOfFibre
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfFaithfullyFlat
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PolarisationOfFaithfullyFlat
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProperRelAmpleKTrivOfFieldExtension
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointRepresentingWeightMumfordQuotient

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolAV

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.PolFieldDescent

theorem exists_polAV : ∀ (K K' : Type) [Field K] [Field K'] (ga : K →+* K') (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G] (L : LB G.left), L.IsLB → Out.Sym G L → ∀ (A' : PolAV (Sp K')) (α : A'.A.left ⟶ G.left), IsGrpPullback A'.A G (spMap ga) α → LBIso A'.L (L.pull α) → ∃ (A : PolAV (Sp K)) (gen : G ≅ A.A), IsMonHom gen.hom ∧ LBIso (A.L.pull gen.hom.left) L := by
  intro K K' _ _ ga G _ _ L hL hS A' α hP hw
  letI : Algebra K K' := ga.toAlgebra
  have hP' : IsGrpPullback A'.A G (spMap (algebraMap K K')) α := hP
  have : Flat (spMap ga) := Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  have : Surjective (spMap ga) := ⟨PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := K) (B := K')⟩
  have : QuasiCompact (spMap ga) := inferInstance
  have hAb : IsAbelianScheme G := PolFlatDescent.isAbelianScheme_of_pull hP A'.isAb
  have hdim : SmoothOfRelativeDimension A'.g G.hom :=
    CM.smoothOfRelativeDimension_of_fibre K K' ga G A'.A.left α A'.A.hom A'.g hAb hP.1 A'.smoothDim
  have hrig : Out.Rigidified G L := DVR.exists_gen_of_local L hL _ _
  have hamp : Out.RelAmple G L :=
    AmpleDescent.relAmple_of_faithfullyFlat K K' G A'.A α L A'.L hAb hP' hL A'.isLB hw A'.ample
  have hK : Out.KTriv G L := AmpleDescent.kTriv_of_pull hP hL A'.isLB hw A'.ktriv
  refine ⟨⟨G, hAb, A'.g, hdim, L, hL, hrig, hS, hamp, hK⟩, Iso.refl G, ?_, ?_⟩
  · show IsMonHom (𝟙 G); infer_instance
  · exact GlobalTheory.lbIso_pull_id hL

end GlobalTheory.PolFieldDescent
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarisedAbelianGenericFibreTraitUniformis

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.TraitGeneric

theorem exists_polAV_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : GlobalTheory.UU.CP G), IsSemiAbelian G → UnifTrait D G P.L.L →
    ∃ (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A), IsMonHom gen.hom ∧
      LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) := by
  intro R _ _ _ _ D G _ _ P _ hU
  obtain ⟨W, _, _, _, φ, G', _, _, β, D', A', U', -, hinj, -, hGP, hLβ, -⟩ := hU
  have hnz : nonZeroDivisors R ≤ (nonZeroDivisors W).comap φ :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective φ hinj
  let ga : FractionRing R →+* FractionRing W := IsLocalization.map (FractionRing W) φ hnz
  have hga : ga.comp (algebraMap R (FractionRing R)) = (algebraMap W (FractionRing W)).comp φ :=
    IsLocalization.map_comp hnz
  have hsq : jK W ≫ spMap φ = spMap ga ≫ jK R := by
    simp only [spMap, jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hga]
  let GK := (Over.pullback (jK R)).obj G
  let L : LB GK.left := P.L.L.pull (pullback.fst G.hom (jK R))
  have hL : L.IsLB := pull_isLB P.L.isLB _
  have hS : Out.Sym GK L :=
    GlobalTheory.PolBaseChange.sym_pull (isGrpPullback_pullback G (jK R)) (GlobalTheory.WtPoint.sym_of_cp P)
  have := U'.gen_hom
  set ψ₀ := U'.gen.inv.left ≫ pullback.fst G'.hom (jK W) with hψ₀
  have g₀ : IsGrpPullback A'.A G' (jK W) ψ₀ := by
    have : IsMonHom U'.gen.symm.hom := by show IsMonHom U'.gen.inv; infer_instance
    exact ((isGrpPullback_of_iso U'.gen.symm).comp (isGrpPullback_pullback G' (jK W))).congr
      (Category.id_comp _) rfl
  have g₁ : IsGrpPullback A'.A G (spMap ga ≫ jK R) (ψ₀ ≫ β) := (g₀.comp hGP).congr hsq rfl
  have gb := isGrpPullback_pullback G (jK R)
  have w₁ : (ψ₀ ≫ β) ≫ G.hom = (A'.A.hom ≫ spMap ga) ≫ jK R :=
    g₁.1.w.trans (Category.assoc _ _ _).symm
  obtain ⟨α, e₁, e₂⟩ : ∃ α : A'.A.left ⟶ GK.left, α ≫ pullback.fst G.hom (jK R) = ψ₀ ≫ β ∧
      α ≫ GK.hom = A'.A.hom ≫ spMap ga :=
    ⟨gb.1.lift _ _ w₁, gb.1.lift_fst _ _ _, gb.1.lift_snd _ _ _⟩
  have gα : IsGrpPullback A'.A GK (spMap ga) α := gb.cancel (g₁.congr rfl e₁.symm) e₂
  have hgi : U'.gen.inv.left ≫ U'.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hext : LBIso (A'.L.pull U'.gen.hom.left) (U'.LG.L.pull (pullback.fst G'.hom (jK W))) := U'.ext
  have h1 : LBIso (A'.L.pull (U'.gen.inv.left ≫ U'.gen.hom.left)) (U'.LG.L.pull ψ₀) :=
    LBIso.chartPull (Geo.Tor.chartPullSame A'.L _ (fun _ => U'.gen.hom.left) _ U'.gen.inv.left fun _ => rfl)
      (Geo.Tor.chartPullSame U'.LG.L _ (fun _ => pullback.fst G'.hom (jK W)) _ U'.gen.inv.left fun _ => rfl) hext
  have l₁ : LBIso A'.L (U'.LG.L.pull ψ₀) :=
    LBIso.chartPull (Geo.Tor.chartPullUnpull A'.L _ hgi)
      (Geo.Tor.chartPullSame U'.LG.L _ _ _ (𝟙 _) fun _ => (Category.id_comp _).symm) h1
  have l₂ : LBIso (U'.LG.L.pull ψ₀) (P.L.L.pull (ψ₀ ≫ β)) := GlobalTheory.Ex.GenericFibre.lbIso_pull hLβ ψ₀ rfl
  have l₃ : LBIso (L.pull α) (P.L.L.pull (ψ₀ ≫ β)) :=
    GlobalTheory.Ex.GenericFibre.lbIso_pull (GlobalTheory.PolBaseChange.lbIso_refl hL) α e₁.symm
  have hw : LBIso A'.L (L.pull α) :=
    LBIso.trans A'.isLB (pull_isLB P.L.isLB _) (pull_isLB hL _)
      (LBIso.trans A'.isLB (pull_isLB U'.LG.isLB _) (pull_isLB P.L.isLB _) l₁ l₂) l₃.symm
  exact GlobalTheory.PolFieldDescent.exists_polAV _ _ ga GK L hL hS A' α gα hw

end GlobalTheory.Mum.TraitGeneric
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarisedAbelianGenericFibreTraitUniformisStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_polarisedAbelian_generic_fibre_trait_uniformised : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : GlobalTheory.UU.CP G), IsSemiAbelian G → UnifTrait D G P.L.L →
    ∃ (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A), IsMonHom gen.hom ∧
      LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) := by
  first | exact @GlobalTheory.Mum.TraitGeneric.exists_polAV_generic | exact GlobalTheory.Mum.TraitGeneric.exists_polAV_generic | (intros; apply GlobalTheory.Mum.TraitGeneric.exists_polAV_generic <;> assumption)
end
end
