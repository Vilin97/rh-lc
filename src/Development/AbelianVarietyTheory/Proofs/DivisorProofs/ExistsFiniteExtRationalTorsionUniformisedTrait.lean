module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniTrait
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleSymmetryHypothesisBaseChange
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelsFinExt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPointsAlgClosureFractionRingBijective
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNumberFieldQkPointsComplexDegeneration
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Tactic.NormNum.Parity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationDataPullbackInjectiveLocalHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionFractionFieldUniformStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinExtIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisFixesQuotientPointsOfRational
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIsPullDegCompOfInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonPullbackFractionFieldFiniteLocalExt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedTraitDescentFiniteExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationOfFiniteExtTrans
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullDegUniqueAndComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationQuotientPointsRationalFiniteExtensio

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

open GlobalTheory.ArcPull GlobalTheory.TorusExt

theorem qkPt_rational_of_pull : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁], Base R₁ → ∀ (D₁ : DegData R₁ (maximalIdeal R₁)) (n : ℕ), 1 ≤ n → ∃ E : IntermediateField (FractionRing R₁) (Kb R₁), FiniteDimensional (FractionRing R₁) E ∧ ∀ (R₂ : Type) [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] (i₁₂ : R₁ →+* R₂) (e : E →+* FractionRing R₂), FinExt i₁₂ → IsLocalHom i₁₂ → (∀ r : R₁, e (algebraMap (FractionRing R₁) E (algebraMap R₁ (FractionRing R₁) r)) = algebraMap R₂ (FractionRing R₂) (i₁₂ r)) → ∀ (D₂ : DegData R₂ (maximalIdeal R₂)), Nonempty (IsPullDeg i₁₂ D₁.toPre D₂.toPre) → ∀ p : QkPt D₂.toPre (Kb R₂) n, ∃ (p₀ : QkPt D₂.toPre (FractionRing R₂) n) (p₁ : QkPt D₂.toPre (Kb R₂) n), QkExt (algebraMap (FractionRing R₂) (Kb R₂)) p₀ p₁ ∧ QkPt.Equiv D₂.toPre (Kb R₂) p₁ p := by
  intro R₁ _ _ _ hR D₁ n hn
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  have hG := hL.globalFns
  have hB₁ := D₁.tau_bimult
  have := hR.2
  have : CharZero (Kb R₁) := (RingHom.charZero_iff (algebraMap (FractionRing R₁) (Kb R₁)).injective).1 inferInstance
  obtain ⟨M, hM, H⟩ := GlobalTheory.QkNumberField.exists_finite_qk (D := D₁.toPre) (L := Kb R₁) hL hB₁ (N := n)
    (Nat.cast_ne_zero.2 (by omega))
  refine ⟨M, hM, ?_⟩
  intro R₂ _ _ _ i₁₂ e hfin _ he D₂ ⟨hD⟩ p
  have hB₂ := D₂.tau_bimult
  have hi : Function.Injective i₁₂ := hfin.2.1
  letI : Algebra (FractionRing R₁) (FractionRing R₂) := (fracMap hi).toAlgebra
  have he' : e.comp (algebraMap (FractionRing R₁) M) = algebraMap (FractionRing R₁) (FractionRing R₂) :=
    IsLocalization.ringHom_ext (nonZeroDivisors R₁) (RingHom.ext fun r => (he r).trans (fracMap_algebraMap hi r).symm)
  letI : Algebra (FractionRing R₁) (Kb R₂) := ((algebraMap (FractionRing R₂) (Kb R₂)).comp (fracMap hi)).toAlgebra
  have cK : Compat i₁₂ (Kb R₂) := fun r => congrArg (algebraMap (FractionRing R₂) (Kb R₂)) (fracMap_algebraMap hi r)
  have cF : Compat i₁₂ (FractionRing R₂) := fracMap_algebraMap hi
  letI : Algebra M (Kb R₂) := ((algebraMap (FractionRing R₂) (Kb R₂)).comp e).toAlgebra
  haveI : Module.IsTorsionFree M (Kb R₂) := DivisionSemiring.to_moduleIsTorsionFree
  haveI : Module.IsTorsionFree M (Kb R₁) := DivisionSemiring.to_moduleIsTorsionFree
  haveI : Algebra.IsAlgebraic M (Kb R₁) := Algebra.IsAlgebraic.tower_top (K := FractionRing R₁) M
  let σ' : Kb R₁ →ₐ[M] Kb R₂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hσ' : ∀ m : M, σ' (m : Kb R₁) = algebraMap (FractionRing R₂) (Kb R₂) (e m) := fun m => σ'.commutes m
  let σ : Kb R₁ →ₐ[FractionRing R₁] Kb R₂ := ⟨σ'.toRingHom, fun x => by
    show σ' (algebraMap (FractionRing R₁) (Kb R₁) x) = _
    exact (hσ' (algebraMap (FractionRing R₁) M x)).trans (congrArg (algebraMap (FractionRing R₂) (Kb R₂)) (RingHom.congr_fun he' x))⟩
  have key : σ.toRingHom.comp M.val.toRingHom = (algebraMap (FractionRing R₂) (Kb R₂)).comp e :=
    RingHom.ext fun m => hσ' m
  obtain ⟨q, rfl⟩ := pullQk_surjective hD hG cK hB₁ hB₂ p
  obtain ⟨q₀, hq₀⟩ := GlobalTheory.LabTrans.exists_of_ext hB₁ σ hn q
  obtain ⟨z, rfl⟩ := H n dvd_rfl q₀
  let z' : QkPt D₁.toPre (FractionRing R₂) n := qkExt hB₁ e he' z
  let p₀ := pullQk hD hG cF hB₁ hB₂ z'
  let p₁ := qkExt hB₂ (algebraMap (FractionRing R₂) (Kb R₂)) (RingHom.comp_id _) p₀
  have hp₁ : QkExt (algebraMap (FractionRing R₂) (Kb R₂)) p₀ p₁ := (qkExt_iff hB₂ _ _ _ _).2 rfl
  have hf₂ : (algebraMap (FractionRing R₂) (Kb R₂)).comp (algebraMap (FractionRing R₁) (FractionRing R₂)) =
      algebraMap (FractionRing R₁) (Kb R₂) := rfl
  let w := qkExt hB₁ (algebraMap (FractionRing R₂) (Kb R₂)) hf₂ z'
  have hw : QkExt (algebraMap (FractionRing R₂) (Kb R₂)) z' w := (qkExt_iff hB₁ _ _ _ _).2 rfl
  have hz' : QkExt e z z' := (qkExt_iff hB₁ _ _ _ _).2 rfl
  have hz : QkExt M.val.toRingHom z (qkExt hB₁ M.val.toRingHom (GlobalTheory.QkNumberField.val_comp M) z) :=
    (qkExt_iff hB₁ _ _ _ _).2 rfl
  have t₁ := GlobalTheory.LabTrans.qkExt_trans hz hq₀
  have t₂ := GlobalTheory.LabTrans.qkExt_trans hz' hw
  rw [← key] at t₂
  have hqw : q = w := GlobalTheory.QkClosure.qkExt_unique (σ.toRingHom.comp M.val.toRingHom) (σ.comp_algebraMap ▸ rfl) t₁ t₂
  refine ⟨p₀, p₁, hp₁, ?_⟩
  have e₁ : p₁ = pullQk hD hG cK hB₁ hB₂ q := by
    rw [eq_pullQk_iff]
    refine ⟨?_, ?_⟩
    · rw [hqw]; rfl
    · rw [hqw]
      exact isPullGtF_ext hD cK _ (RingHom.comp_id _) (isPullGtF_pullGt hD hG cF z'.g) hw hp₁
  rw [e₁]
  exact qk_equiv_refl hB₂ _

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationQuotientPointsRationalFiniteExtensioStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.degenerationQuotientPoints_rational_finiteExtension : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁], Base R₁ → ∀ (D₁ : DegData R₁ (maximalIdeal R₁)) (n : ℕ), 1 ≤ n → ∃ E : IntermediateField (FractionRing R₁) (Kb R₁), FiniteDimensional (FractionRing R₁) E ∧ ∀ (R₂ : Type) [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] (i₁₂ : R₁ →+* R₂) (e : E →+* FractionRing R₂), FinExt i₁₂ → IsLocalHom i₁₂ → (∀ r : R₁, e (algebraMap (FractionRing R₁) E (algebraMap R₁ (FractionRing R₁) r)) = algebraMap R₂ (FractionRing R₂) (i₁₂ r)) → ∀ (D₂ : DegData R₂ (maximalIdeal R₂)), Nonempty (IsPullDeg i₁₂ D₁.toPre D₂.toPre) → ∀ p : QkPt D₂.toPre (Kb R₂) n, ∃ (p₀ : QkPt D₂.toPre (FractionRing R₂) n) (p₁ : QkPt D₂.toPre (Kb R₂) n), QkExt (algebraMap (FractionRing R₂) (Kb R₂)) p₀ p₁ ∧ QkPt.Equiv D₂.toPre (Kb R₂) p₁ p := by
  first | exact @GlobalTheory.Mum.qkPt_rational_of_pull | exact GlobalTheory.Mum.qkPt_rational_of_pull | (intros; apply GlobalTheory.Mum.qkPt_rational_of_pull <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionRealisingSubextension

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.GalClosure

theorem exists_finExt_realising : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ : R →+* R₁), FinExt ρ → ∀ (E : IntermediateField (FractionRing R₁) (Kb R₁)), FiniteDimensional (FractionRing R₁) E → ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (i₁₂ : R₁ →+* R₂) (e : E →+* FractionRing R₂), FinExt i₁₂ ∧ FinExt (i₁₂.comp ρ) ∧ IsLocalHom i₁₂ ∧ ∀ r : R₁, e (algebraMap (FractionRing R₁) E (algebraMap R₁ (FractionRing R₁) r)) = algebraMap R₂ (FractionRing R₂) (i₁₂ r) := by
  intro R _ _ _ hR R₁ _ _ _ ρ hρ E hE
  obtain ⟨hadm, hinj, hfin⟩ := hρ
  haveI : CharZero R := hR.2
  haveI : CharZero R₁ := charZero_of_injective_ringHom hinj
  have hR₁ : Base R₁ := ⟨hadm, inferInstance⟩
  let E' := IntermediateField.normalClosure (FractionRing R₁) E (Kb R₁)
  haveI : IsGalois (FractionRing R₁) E' := inferInstance
  haveI : FiniteDimensional (FractionRing R₁) E' := inferInstance
  obtain ⟨hloc, hfe⟩ := finExt_integralClosure (E := E') hR₁
  letI : Algebra R₁ E' := (baseMap R₁ E').toAlgebra
  haveI : IsScalarTower R₁ (FractionRing R₁) E' := IsScalarTower.of_algebraMap_eq' rfl
  set R₂ := integralClosure R₁ E'
  haveI : IsFractionRing R₂ E' := integralClosure.isFractionRing_of_finite_extension (FractionRing R₁) E'
  let incl : E →ₐ[FractionRing R₁] E' := IntermediateField.inclusion (IntermediateField.le_normalClosure E)
  let eqv : E' ≃ₐ[R₂] FractionRing R₂ := (FractionRing.algEquiv R₂ E').symm
  have hloc' : IsLocalHom (algebraMap R₁ R₂) := by
    haveI : Module.Finite R₁ R₂ := RingHom.finite_algebraMap.1 hfe.2.2
    have : (Ideal.comap (algebraMap R₁ R₂) (maximalIdeal R₂)).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal (maximalIdeal R₂)
    exact ((local_hom_tfae (algebraMap R₁ R₂)).out 1 5).mpr (IsLocalRing.eq_maximalIdeal this)
  refine ⟨R₂, inferInstance, inferInstance, hloc, algebraMap R₁ R₂, eqv.toRingHom.comp incl.toRingHom, hfe,
    ⟨hfe.1, hfe.2.1.comp hinj, hfe.2.2.comp hfin⟩, hloc', fun r => ?_⟩
  have h1 : incl (algebraMap (FractionRing R₁) E (algebraMap R₁ (FractionRing R₁) r)) = algebraMap R₂ E' (algebraMap R₁ R₂ r) :=
    incl.commutes _
  change eqv (incl _) = _
  rw [h1]
  exact eqv.commutes _

end GlobalTheory.GalClosure
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionRealisingSubextensionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_finiteExtension_realising_subextension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ : R →+* R₁), FinExt ρ → ∀ (E : IntermediateField (FractionRing R₁) (Kb R₁)), FiniteDimensional (FractionRing R₁) E → ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (i₁₂ : R₁ →+* R₂) (e : E →+* FractionRing R₂), FinExt i₁₂ ∧ FinExt (i₁₂.comp ρ) ∧ IsLocalHom i₁₂ ∧ ∀ r : R₁, e (algebraMap (FractionRing R₁) E (algebraMap R₁ (FractionRing R₁) r)) = algebraMap R₂ (FractionRing R₂) (i₁₂ r) := by
  first | exact @GlobalTheory.GalClosure.exists_finExt_realising | exact GlobalTheory.GalClosure.exists_finExt_realising | (intros; apply GlobalTheory.GalClosure.exists_finExt_realising <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisFixesQuotientPointsOfRationalStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.galois_fixes_quotientPoints_of_rational : ∀ (R₂ : Type) [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] (D₂ : DegData R₂ (maximalIdeal R₂)) (n : ℕ), (∀ p : QkPt D₂.toPre (Kb R₂) n, ∃ (p₀ : QkPt D₂.toPre (FractionRing R₂) n) (p₁ : QkPt D₂.toPre (Kb R₂) n), QkExt (algebraMap (FractionRing R₂) (Kb R₂)) p₀ p₁ ∧ QkPt.Equiv D₂.toPre (Kb R₂) p₁ p) → ∀ σ : Kb R₂ →ₐ[FractionRing R₂] Kb R₂, ∀ p p' : QkPt D₂.toPre (Kb R₂) n, QkExt σ.toRingHom p p' → QkPt.Equiv D₂.toPre (Kb R₂) p p' := by
  first | exact @GlobalTheory.Mum.GalFixQ.qkExt_equiv_of_rational | exact GlobalTheory.Mum.GalFixQ.qkExt_equiv_of_rational | (intros; apply GlobalTheory.Mum.GalFixQ.qkExt_equiv_of_rational <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedTraitMovesToFiniteExtension

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.UniEnlarge

open GlobalTheory.Mum.ClosureDescent GlobalTheory.ThetaDescent

theorem uniTrait_of_finExt : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁], Base R₁ → ∀ (D₁ : DegData R₁ (maximalIdeal R₁)) (A : PolAV (Sp (FractionRing R₁))), UniTrait D₁.toPre A → ∀ (R₂ : Type) [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] (i₁₂ : R₁ →+* R₂), FinExt i₁₂ → IsLocalHom i₁₂ → ∀ (D₂ : DegData R₂ (maximalIdeal R₂)), Nonempty (IsPullDeg i₁₂ D₁.toPre D₂.toPre) → ∀ (A₂ : PolAV (Sp (FractionRing R₂))) (a : A₂.A.left ⟶ A.A.left), IsFib i₁₂ A A₂ a → UniTrait D₂.toPre A₂ := by
  intro R₁ _ _ _ _ D₁ A hU R₂ _ _ _ i₁₂ hi₁₂ hl₁₂ D₂ ⟨hD₂⟩ A₂ a₂ hA₂
  classical
  obtain ⟨W, _, _, _, φ, G', _, _, D', A', U', hD', a, hW, hφ, hφl, hG', ga, hga, g₁, l₁⟩ := hU
  obtain ⟨ga₂, hga₂, g₂, l₂⟩ := hA₂
  have hfin : i₁₂.Finite := hi₁₂.2.2
  let β : FractionRing W →+* AlgebraicClosure (FractionRing W) := algebraMap _ _
  have hβ : β.IsIntegral := fun x => Algebra.IsIntegral.isIntegral (R := FractionRing W) x
  obtain ⟨j₁, hj₁⟩ := exists_extend hfin (algebraMap R₁ (FractionRing R₁)) ga₂ (RingHom.ext fun r => hga₂ r)
    (β.comp ga)
  have hjρ : ∀ r, j₁ (algebraMap R₂ _ (i₁₂ r)) = β (((algebraMap W (FractionRing W)).comp φ) r) := fun r => by
    rw [← hga₂, ← RingHom.comp_apply j₁ ga₂, hj₁, RingHom.comp_apply, hga, RingHom.comp_apply]
  obtain ⟨s₀, hs₀⟩ := exists_range_le_gen hfin β ((algebraMap W _).comp φ) j₁ hjρ
  let i := β.codRestrict _ (mem_gen β s₀)
  let k := j₁.codRestrict _ hs₀
  have hi : i.Finite := finite_gen β hβ s₀
  have := hW.1
  have hWb : Base W := ⟨⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩, hW.2.2⟩
  obtain ⟨W₁, _, _, _, io, σ, hio, hiol, hσ⟩ := GlobalTheory.CommonCover.exists_cover_field W hWb _ i hi
  obtain ⟨D₃, hD₃, A₃, U₃, a₃, hA₃⟩ := exists_unif_fib hWb.1 hio.1 io hio.2.1 (map_maximalIdeal_le io) hG' U'
    (σ.comp i) ((RingHom.comp_assoc _ _ _).trans hσ)
  have f₁ : Fib A₃ A ((σ.comp i).comp ga) (a₃ ≫ a) := hA₃.comp ⟨g₁, l₁⟩ rfl
  have e : (σ.comp k).comp ga₂ = (σ.comp i).comp ga := RingHom.ext fun x =>
    congrArg σ (Subtype.ext (DFunLike.congr_fun hj₁ x))
  obtain ⟨d, -, hd⟩ := Fib.cancel (σ.comp k) (⟨g₂, l₂⟩ : Fib A₂ A ga₂ a₂) f₁ e
  haveI := hio.1.2.2.1
  obtain ⟨φ₂, hφ₂, hcomp, hinj, hl⟩ := exists_restrict hfin (io.comp φ) (σ.comp k) fun r => by
    have e₁ : k (algebraMap R₂ _ (i₁₂ r)) = i (algebraMap W _ (φ r)) := Subtype.ext (hjρ r)
    exact (congrArg σ e₁).trans (DFunLike.congr_fun hσ (φ r))
  obtain ⟨q⟩ := GlobalTheory.PullDegComp.nonempty_isPullDeg_comp hφ hio.2.1 hD' hD₃
  rw [← hcomp] at q
  obtain ⟨q₁⟩ := GlobalTheory.PullDegUniq.nonempty_isPullDeg_cancel hi₁₂.2.1 hinj hD₂ q
  exact ⟨W₁, _, _, _, φ₂, _, inferInstance, inferInstance, D₃, A₃, U₃, q₁, d, cDvr_of_finExt hW hio, hinj, hl,
    IsSemiAbelian.pullback _ G' hG', σ.comp k, hφ₂, hd.1, hd.2⟩

end GlobalTheory.Mum.UniEnlarge
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedTraitMovesToFiniteExtensionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.uniformisedTrait_moves_to_finite_extension : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁], Base R₁ → ∀ (D₁ : DegData R₁ (maximalIdeal R₁)) (A : PolAV (Sp (FractionRing R₁))), UniTrait D₁.toPre A → ∀ (R₂ : Type) [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] (i₁₂ : R₁ →+* R₂), FinExt i₁₂ → IsLocalHom i₁₂ → ∀ (D₂ : DegData R₂ (maximalIdeal R₂)), Nonempty (IsPullDeg i₁₂ D₁.toPre D₂.toPre) → ∀ (A₂ : PolAV (Sp (FractionRing R₂))) (a : A₂.A.left ⟶ A.A.left), IsFib i₁₂ A A₂ a → UniTrait D₂.toPre A₂ := by
  first | exact @GlobalTheory.Mum.UniEnlarge.uniTrait_of_finExt | exact GlobalTheory.Mum.UniEnlarge.uniTrait_of_finExt | (intros; apply GlobalTheory.Mum.UniEnlarge.uniTrait_of_finExt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtRationalTorsionUniformisedTrait

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.Enlarge

theorem exists_rational_ext : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ : R →+* R₁) (D₁ : DegData R₁ (maximalIdeal R₁)) (A : PolAV (Sp (FractionRing R₁))), FinExt ρ → Nonempty (IsPullDeg ρ D.toPre D₁.toPre) → (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) → UniTrait D₁.toPre A → ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (ρ₂ : R →+* R₂) (D₂ : DegData R₂ (maximalIdeal R₂)) (A₂ : PolAV (Sp (FractionRing R₂))), FinExt ρ₂ ∧ Nonempty (IsPullDeg ρ₂ D.toPre D₂.toPre) ∧ (letI := A₂.isAb.comm; GlobalTheory.ZH.HypS A₂.A A₂.L) ∧ UniTrait D₂.toPre A₂ ∧ ∀ σ : Kb R₂ →ₐ[FractionRing R₂] Kb R₂, (∀ p p' : QkPt D₂.toPre (Kb R₂) n, QkExt σ.toRingHom p p' → QkPt.Equiv D₂.toPre (Kb R₂) p p') ∧ ∀ x : TFK (R := R₂) (Kb R₂) ⟶ A₂.A, x ^ n = 1 → spMap σ.toRingHom ≫ x.left = x.left := by
  intro R _ _ _ hR D n hn hodd hnu R₁ _ _ _ ρ D₁ A hρ hP hS hU
  have hn1 : 1 ≤ n := hn.one_lt.le
  have hR₁ : Base R₁ := ⟨hρ.1, by haveI := hR.2; exact charZero_of_injective_ringHom hρ.2.1⟩
  obtain ⟨EQ, fQ, hQ⟩ := GlobalTheory.T.degenerationQuotientPoints_rational_finiteExtension R₁ hR₁ D₁ n hn1
  obtain ⟨EA, fA, hA⟩ := GlobalTheory.T.exists_finite_extension_fraction_field_uniform R₁ hR₁ A n hn1
  haveI := fQ
  haveI := fA
  obtain ⟨R₂, _, _, _, i₁₂, e, hi₁₂, hi₁₂ρ, hloc, he⟩ := GlobalTheory.T.exists_finiteExtension_realising_subextension R hR R₁ ρ hρ (EQ ⊔ EA) inferInstance
  obtain ⟨D₂, hD₂⟩ := GlobalTheory.MumPull.exists_pull R₁ R₂ i₁₂ hi₁₂.2.1 hloc D₁
  have hP₂ := nonempty_isPullDeg_comp_of_injective R R₁ R₂ ρ i₁₂ D.toPre D₁.toPre D₂.toPre hi₁₂.2.1 hP hD₂
  have hle : nonZeroDivisors R₁ ≤ (nonZeroDivisors R₂).comap i₁₂ :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective i₁₂ hi₁₂.2.1
  let ga : FractionRing R₁ →+* FractionRing R₂ := IsLocalization.map (FractionRing R₂) i₁₂ hle
  obtain ⟨A₂, g, hg, -, hm, t, ht⟩ := GlobalTheory.firstFiveLaws.1.polBaseChange _ _ (spMap ga) A
  have gp : IsGrpPullback A₂.A A.A (spMap ga) g := ⟨hg, fun T x y x₀ y₀ hx hy => by
    obtain rfl : x₀ = toBase hg.w x := Over.OverMorphism.ext hx
    obtain rfl : y₀ = toBase hg.w y := Over.OverMorphism.ext hy
    exact congrArg (·.left) (hm T x y).symm⟩
  have hlb : LBIso A₂.L (A.L.pull g) := LBIso.symm ⟨t, ht⟩
  have hfib : IsFib i₁₂ A A₂ g := ⟨ga, fun r => IsLocalization.map_eq hle r, gp, hlb⟩
  have hS₂ : (letI := A₂.isAb.comm; GlobalTheory.ZH.HypS A₂.A A₂.L) := by
    letI := A.isAb.comm
    letI := A₂.isAb.comm
    exact GlobalTheory.SymBaseChange.hypS_baseChange _ _ A.A A₂.A (spMap ga) g A.L A₂.L A.isLB A₂.isLB gp hlb hS
  let eQ : EQ →+* FractionRing R₂ := e.comp (IntermediateField.inclusion (le_sup_left : EQ ≤ EQ ⊔ EA)).toRingHom
  let eA : EA →+* FractionRing R₂ := e.comp (IntermediateField.inclusion (le_sup_right : EA ≤ EQ ⊔ EA)).toRingHom
  have hrat := hQ R₂ i₁₂ eQ hi₁₂ hloc (fun r => he r) D₂ hD₂
  refine ⟨R₂, inferInstance, inferInstance, inferInstance, i₁₂.comp ρ, D₂, A₂, hi₁₂ρ, hP₂, hS₂,
    GlobalTheory.T.uniformisedTrait_moves_to_finite_extension R₁ hR₁ D₁ A hU R₂ i₁₂ hi₁₂ hloc D₂ hD₂ A₂ g hfib, fun σ => ⟨GlobalTheory.T.galois_fixes_quotientPoints_of_rational R₂ D₂ n hrat σ, fun x hx => ?_⟩⟩
  obtain ⟨x₀, hx₀⟩ := hA R₂ i₁₂ eA hi₁₂.2.1 (fun r => he r) A₂ g hfib x hx
  rw [hx₀, ← Category.assoc, ← spMap_comp]
  exact congrArg (fun f => spMap f ≫ x₀) (RingHom.ext fun a => σ.commutes a)

end GlobalTheory.Mum.Enlarge
end
end
end
