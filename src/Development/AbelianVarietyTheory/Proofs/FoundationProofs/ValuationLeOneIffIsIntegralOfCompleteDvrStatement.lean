module

public import Mathlib.Basic.NNReal.Defs
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAbsoluteValueCompleteSpaceOfDvr
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAbsoluteValueCompleteSpaceOfDvrStatement

section

@[expose] public section

open scoped NNReal TensorProduct

theorem _root_.GlobalTheory.T.exists_absoluteValue_completeSpace_of_dvr : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Field K] [Algebra R K] [IsFractionRing R K], ∃ f : AbsoluteValue K ℝ, IsNonarchimedean f ∧ f.IsNontrivial ∧ (∀ x : K, f x ≤ 1 ↔ x ∈ Set.range (algebraMap R K)) ∧ CompleteSpace (WithAbs f) := by
  first | exact @GlobalTheory.KLC.exists_absoluteValue_completeSpace_of_isDiscreteValuationRing | exact GlobalTheory.KLC.exists_absoluteValue_completeSpace_of_isDiscreteValuationRing | (intros; apply GlobalTheory.KLC.exists_absoluteValue_completeSpace_of_isDiscreteValuationRing <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSpectralValuationAlgebraicExtension

section

@[expose] public section

open scoped NNReal TensorProduct

namespace GlobalTheory

open Polynomial

theorem exists_spectralValuation (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    (f : AbsoluteValue K ℝ) (hna : IsNonarchimedean f) (hnt : f.IsNontrivial)
    (hc : CompleteSpace (WithAbs f)) :
    ∃ v : Valuation Ω ℝ≥0, (∀ x : K, (v (algebraMap K Ω x) : ℝ) = f x) ∧
      ∀ x : Ω, v x ≤ 1 ↔ ∀ i, f ((minpoly K x).coeff i) ≤ 1 := by
  obtain ⟨a, ha⟩ := hnt.exists_abv_gt_one
  letI : NontriviallyNormedField (WithAbs f) :=
    NontriviallyNormedField.ofNormNeOne ⟨WithAbs.toAbs f a, by
      intro h; rw [WithAbs.toAbs_eq_zero] at h; rw [h, map_zero] at ha; linarith, by
      rw [WithAbs.norm_toAbs_eq]; exact ha.ne'⟩
  haveI : IsUltrametricDist (WithAbs f) :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm fun x y => hna x.ofAbs y.ofAbs
  haveI : IsScalarTower K (WithAbs f) Ω := inferInstance
  haveI : Algebra.IsAlgebraic (WithAbs f) Ω := Algebra.IsAlgebraic.tower_top (K := K) (WithAbs f)
  have hmin : ∀ x : Ω, minpoly (WithAbs f) x = (minpoly K x).map (algebraMap K (WithAbs f)) := by
    intro x
    have hx : IsIntegral K x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
    have hmap : (minpoly K x).map (algebraMap K (WithAbs f)) =
        Polynomial.mapEquiv (WithAbs.equiv f).symm (minpoly K x) := by
      rw [Polynomial.mapEquiv_apply]; rfl
    symm
    apply minpoly.eq_of_irreducible_of_monic
    · rw [hmap]; exact (MulEquiv.irreducible_iff _).mpr (minpoly.irreducible hx)
    · rw [Polynomial.aeval_map_algebraMap]; exact minpoly.aeval K x
    · exact (minpoly.monic hx).map _
  let v : Valuation Ω ℝ≥0 :=
    { toFun := fun x => ⟨spectralNorm (WithAbs f) Ω x, spectralNorm_nonneg x⟩
      map_zero' := by ext; exact spectralNorm_zero
      map_one' := by ext; exact spectralNorm_one
      map_mul' := fun x y => by
        ext; exact spectralAlgNorm_mul (K := WithAbs f) (L := Ω) x y
      map_add_le_max' := fun x y => by
        show spectralNorm (WithAbs f) Ω (x + y) ≤ max (spectralNorm (WithAbs f) Ω x) (spectralNorm (WithAbs f) Ω y)
        exact isNonarchimedean_spectralNorm x y }
  have hv : ∀ x : Ω, (v x : ℝ) = spectralNorm (WithAbs f) Ω x := fun _ => rfl
  refine ⟨v, fun x => ?_, fun x => ?_⟩
  · rw [hv]
    have : algebraMap K Ω x = algebraMap (WithAbs f) Ω (WithAbs.toAbs f x) := rfl
    rw [this, spectralNorm_extends, WithAbs.norm_toAbs_eq]
  · have hx : IsIntegral (WithAbs f) x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
    rw [← NNReal.coe_le_coe, NNReal.coe_one, hv]
    show spectralValue (minpoly (WithAbs f) x) ≤ 1 ↔ _
    rw [spectralValue_le_one_iff (minpoly.monic hx), hmin x]
    refine forall_congr' fun i => ?_
    rw [Polynomial.coeff_map, WithAbs.algebraMap_right_apply, WithAbs.norm_toAbs_eq]
    rfl

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSpectralValuationAlgebraicExtensionStatement

section

@[expose] public section

open scoped NNReal TensorProduct

theorem _root_.GlobalTheory.T.exists_spectral_valuation_algebraic_extension : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] (f : AbsoluteValue K ℝ), IsNonarchimedean f → f.IsNontrivial → CompleteSpace (WithAbs f) → ∃ v : Valuation Ω ℝ≥0, (∀ x : K, (v (algebraMap K Ω x) : ℝ) = f x) ∧ ∀ x : Ω, v x ≤ 1 ↔ ∀ i, f ((minpoly K x).coeff i) ≤ 1 := by
  first | exact @GlobalTheory.exists_spectralValuation | exact GlobalTheory.exists_spectralValuation | (intros; apply GlobalTheory.exists_spectralValuation <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationLeOneIffIsIntegralOfCompleteDvr

section

@[expose] public section

open scoped NNReal TensorProduct

namespace GlobalTheory

theorem valuation_le_one_iff_isIntegral_of_complete_dvr :
    ∀ (R Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Field Ω] [Algebra R Ω]
      [Algebra.IsAlgebraic R Ω], Function.Injective (algebraMap R Ω) →
      ∃ v : Valuation Ω ℝ≥0, ∀ x : Ω, v x ≤ 1 ↔ IsIntegral R x := by
  intro R Ω _ _ _ _ _ _ _ hinj
  haveI : FaithfulSMul R Ω := (faithfulSMul_iff_algebraMap_injective R Ω).mpr hinj
  letI : Algebra (FractionRing R) Ω := FractionRing.liftAlgebra R Ω
  haveI : IsScalarTower R (FractionRing R) Ω := FractionRing.isScalarTower_liftAlgebra R Ω
  haveI : Algebra.IsAlgebraic (FractionRing R) Ω :=
    Algebra.IsAlgebraic.extendScalars (IsFractionRing.injective R (FractionRing R))
  obtain ⟨f, hna, hnt, hball, hcomp⟩ := GlobalTheory.T.exists_absoluteValue_completeSpace_of_dvr R (FractionRing R)
  obtain ⟨v, -, hv⟩ := GlobalTheory.T.exists_spectral_valuation_algebraic_extension (FractionRing R) Ω f hna hnt hcomp
  refine ⟨v, fun x => ?_⟩
  rw [hv]
  simp only [hball]
  constructor
  · intro h
    have hl : minpoly (FractionRing R) x ∈ Polynomial.lifts (algebraMap R (FractionRing R)) :=
      (Polynomial.lifts_iff_coeff_lifts _).mpr h
    obtain ⟨q, hq, -, hmon⟩ := Polynomial.lifts_and_degree_eq_and_monic hl
      (minpoly.monic (Algebra.IsIntegral.isIntegral x))
    refine ⟨q, hmon, ?_⟩
    rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap (FractionRing R), hq]
    exact minpoly.aeval _ _
  · intro h i
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' (FractionRing R) h, Polynomial.coeff_map]
    exact ⟨_, rfl⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationLeOneIffIsIntegralOfCompleteDvrStatement

section

@[expose] public section

open scoped NNReal TensorProduct

theorem _root_.GlobalTheory.T.exists_valuation_le_one_iff_isIntegral_of_complete_dvr : ∀ (R Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Field Ω] [Algebra R Ω] [Algebra.IsAlgebraic R Ω], Function.Injective (algebraMap R Ω) → ∃ v : Valuation Ω ℝ≥0, ∀ x : Ω, v x ≤ 1 ↔ IsIntegral R x := by
  first | exact @GlobalTheory.valuation_le_one_iff_isIntegral_of_complete_dvr | exact GlobalTheory.valuation_le_one_iff_isIntegral_of_complete_dvr | (intros; apply GlobalTheory.valuation_le_one_iff_isIntegral_of_complete_dvr <;> assumption)
end
end
