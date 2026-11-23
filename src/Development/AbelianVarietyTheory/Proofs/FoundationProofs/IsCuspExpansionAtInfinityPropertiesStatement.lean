module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import Mathlib.RingTheory.HahnSeries.Summable
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FnHahnSeriesInvConvergesStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesEqOfQExpansionSumAboveEventuallyEqStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasCommonExponentDenominatorRingOperationsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasQExpansionSumAboveBasicPropertiesStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.ModularForms.SlashActions
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasQExpansionSumAboveMul

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNProd

theorem hs_mul : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (C : ℝ) (φ ψ : ℂ → ℂ) (h h' : HahnSeries ℚ Ω),
    HS ε C φ h → HS ε C ψ h' → HS ε C (φ * ψ) (h * h') := by
  intro Ω _ ε C φ ψ h h' H H' z hz
  set e : ℚ → ℂ := fun r => Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z) with he
  set a : ℚ → ℂ := fun r => ε (h.coeff r) * e r with ha
  set b : ℚ → ℂ := fun r => ε (h'.coeff r) * e r with hb
  have hA : HasSum a (φ z) := H z hz
  have hB : HasSum b (ψ z) := H' z hz
  have hAn : Summable fun r => ‖a r‖ := summable_norm_iff.2 hA.summable
  have hBn : Summable fun r => ‖b r‖ := summable_norm_iff.2 hB.summable
  have hP : HasSum (fun p : ℚ × ℚ => a p.1 * b p.2) (φ z * ψ z) :=
    hA.mul hB (summable_mul_of_summable_norm hAn hBn)
  have hF := hP.tsum_fiberwise (fun p : ℚ × ℚ => p.1 + p.2)
  refine hF.congr_fun ?_
  intro s
  have hexp : ∀ p : ℚ × ℚ, p.1 + p.2 = s → a p.1 * b p.2 = ε (h.coeff p.1) * ε (h'.coeff p.2) * e s := by
    intro p hp
    simp only [ha, hb, he, ← hp]
    have : Complex.exp (2 * Real.pi * Complex.I * ((p.1 + p.2 : ℚ) : ℂ) * z) =
        Complex.exp (2 * Real.pi * Complex.I * (p.1 : ℂ) * z) * Complex.exp (2 * Real.pi * Complex.I * (p.2 : ℂ) * z) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [this]; ring
  rw [tsum_subtype (f := fun p : ℚ × ℚ => a p.1 * b p.2)]
  rw [tsum_eq_sum (s := Finset.antidiagonal h.isPWO_support h'.isPWO_support s)]

  · simp only [HahnSeries.coeff_mul, map_sum, map_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_antidiagonal] at hp
    rw [Set.indicator_of_mem (by simpa using hp.2.2)]
    exact (hexp p hp.2.2).symm
  · intro p hp
    by_cases hs : p.1 + p.2 = s
    · rw [Set.indicator_of_mem (by simpa using hs), hexp p hs]
      rw [Finset.mem_antidiagonal] at hp
      simp only [HahnSeries.mem_support, not_and] at hp
      by_cases h1 : h.coeff p.1 = 0
      · simp [h1]
      · have h2 : h'.coeff p.2 = 0 := by
          by_contra h2; exact hp h1 h2 hs
        simp [h2]
    · exact Set.indicator_of_notMem (by simpa using hs) _

end GlobalTheory.FNProd
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasQExpansionSumAboveMulStatement

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.hasQExpansionSumAbove_mul : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (C : ℝ) (φ ψ : ℂ → ℂ) (h h' : HahnSeries ℚ Ω), HS ε C φ h → HS ε C ψ h' → HS ε C (φ * ψ) (h * h') := by
  first | exact @GlobalTheory.FNProd.hs_mul | exact GlobalTheory.FNProd.hs_mul | (intros; apply GlobalTheory.FNProd.hs_mul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneEqZeroOfVanishAboveIm

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem upperHalfPlane_eq_zero_of_vanish_high :
    ∀ (f : ℍ → ℂ) (C : ℝ), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f →
      (∀ τ : ℍ, C < τ.im → f τ = 0) → f = 0 := by
  intro f C hf hC
  have hd : DifferentiableOn ℂ (f ∘ UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp hf
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have han := hd.analyticOnNhd hopen
  have hpc : IsPreconnected {z : ℂ | 0 < z.im} := (convex_halfSpace_im_gt 0).isPreconnected
  set z₀ : ℂ := ((|C| + 1 : ℝ) : ℂ) * Complex.I with hz₀
  have hz₀im : z₀.im = |C| + 1 := by simp [hz₀]
  have hmem : z₀ ∈ {z : ℂ | 0 < z.im} := by
    show 0 < z₀.im
    rw [hz₀im]; positivity
  have hev : (f ∘ UpperHalfPlane.ofComplex) =ᶠ[nhds z₀] 0 := by
    have hopen2 : IsOpen {z : ℂ | max C 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
    have hin : z₀ ∈ {z : ℂ | max C 0 < z.im} := by
      show max C 0 < z₀.im
      rw [hz₀im]
      have := le_abs_self C
      have := abs_nonneg C
      exact max_lt (by linarith) (by linarith)
    filter_upwards [hopen2.mem_nhds hin] with z hz
    have hz' : max C 0 < z.im := hz
    have h0 : 0 < z.im := lt_of_le_of_lt (le_max_right _ _) hz'
    have h1 : C < z.im := lt_of_le_of_lt (le_max_left _ _) hz'
    simp only [Function.comp_apply, Pi.zero_apply, UpperHalfPlane.ofComplex_apply_of_im_pos h0]
    exact hC _ h1
  have heq := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpc hmem hev
  funext τ
  have := heq (show (τ : ℂ) ∈ {z : ℂ | 0 < z.im} from τ.im_pos)
  simpa [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using this

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneEqZeroOfVanishAboveImStatement

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.upperHalfPlane_eq_zero_of_vanish_above_im : ∀ (f : ℍ → ℂ) (C : ℝ), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → (∀ τ : ℍ, C < τ.im → f τ = 0) → f = 0 := by
  first | exact @GlobalTheory.upperHalfPlane_eq_zero_of_vanish_high | exact GlobalTheory.upperHalfPlane_eq_zero_of_vanish_high | (intros; apply GlobalTheory.upperHalfPlane_eq_zero_of_vanish_high <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspExpansionAtInfinityProperties

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNExp

theorem up_add (f f' : ℍ → ℂ) : up (f + f') = up f + up f' := rfl
theorem up_sub (f f' : ℍ → ℂ) : up (f - f') = up f - up f' := rfl
theorem up_mul (f f' : ℍ → ℂ) : up (f * f') = up f * up f' := rfl
theorem up_inv (f : ℍ → ℂ) : up f⁻¹ = (up f)⁻¹ := rfl

theorem exp_props : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ), (∀ (f f' : ℍ → ℂ) (h h' : HahnSeries ℚ Ω), IsExp ε f h → IsExp ε f' h' → IsExp ε (f + f') (h + h') ∧ IsExp ε (f - f') (h - h') ∧ IsExp ε (f * f') (h * h')) ∧ (∀ (f : ℍ → ℂ) (h h' : HahnSeries ℚ Ω), IsExp ε f h → IsExp ε f h' → h = h') ∧ (∀ c : Ω, IsExp ε (fun _ => ε c) (HahnSeries.C c)) ∧ (∀ f : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → IsExp ε f (0 : HahnSeries ℚ Ω) → f = 0) ∧ ∀ (f : ℍ → ℂ) (h : HahnSeries ℚ Ω), h ≠ 0 → IsExp ε f h → IsExp ε f⁻¹ h⁻¹ := by
  intro Ω _ ε
  obtain ⟨hden, hsing⟩ := GlobalTheory.T.hasCommonExponentDenominator_ring_operations Ω
  obtain ⟨hmono, hadd, hmon, hcongr⟩ := GlobalTheory.T.hasQExpansionSumAbove_basic_properties Ω ε
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro f f' h h' ⟨hd, C, hC⟩ ⟨hd', C', hC'⟩
    obtain ⟨d1, d2, d3⟩ := hden h h' hd hd'
    have e1 : HS ε (max C C') (up f) h := hmono _ _ _ _ (le_max_left _ _) hC
    have e2 : HS ε (max C C') (up f') h' := hmono _ _ _ _ (le_max_right _ _) hC'
    obtain ⟨s1, s2⟩ := hadd _ _ _ _ _ e1 e2
    refine ⟨⟨d1, max C C', ?_⟩, ⟨d2, max C C', ?_⟩, ⟨d3, max C C', ?_⟩⟩
    · rw [up_add]; exact s1
    · rw [up_sub]; exact s2
    · rw [up_mul]; exact GlobalTheory.T.hasQExpansionSumAbove_mul Ω ε _ _ _ _ _ e1 e2
  · rintro f h h' ⟨hd, C, hC⟩ ⟨hd', C', hC'⟩
    exact GlobalTheory.T.hahnSeries_eq_of_qExpansionSumAbove_eventually_eq Ω ε C C' 0 (up f) (up f) h h' hd hd' hC hC' (fun _ _ => rfl)
  · intro c
    have hC : HahnSeries.C c = (HahnSeries.single (0 : ℚ) c : HahnSeries ℚ Ω) := HahnSeries.C_apply c
    rw [hC]
    refine ⟨hsing 0 c, 0, ?_⟩
    refine hcongr 0 _ _ _ ?_ (hmon 0 0 c)
    intro z _
    simp [up]
  · rintro f hf ⟨_, C, hC⟩
    apply GlobalTheory.T.upperHalfPlane_eq_zero_of_vanish_above_im f C hf
    intro τ hτ
    have hz := hC (τ : ℂ) (by simpa using hτ)
    have h0 : (fun r : ℚ => ε ((0 : HahnSeries ℚ Ω).coeff r) * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * (τ : ℂ))) = fun _ => 0 := by
      funext r; simp
    rw [h0] at hz
    have := hz.unique hasSum_zero
    simpa [up, UpperHalfPlane.ofComplex_apply] using this
  · rintro f h hne ⟨hd, C, hC⟩
    obtain ⟨d, C', hC'⟩ := GlobalTheory.T.den_inv_and_hs_inv_of_hs Ω ε C (up f) h hd hne hC
    exact ⟨d, C', by rw [up_inv]; exact hC'⟩

end GlobalTheory.FNExp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspExpansionAtInfinityPropertiesStatement

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.isCuspExpansionAtInfinity_properties : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ), (∀ (f f' : ℍ → ℂ) (h h' : HahnSeries ℚ Ω), IsExp ε f h → IsExp ε f' h' → IsExp ε (f + f') (h + h') ∧ IsExp ε (f - f') (h - h') ∧ IsExp ε (f * f') (h * h')) ∧ (∀ (f : ℍ → ℂ) (h h' : HahnSeries ℚ Ω), IsExp ε f h → IsExp ε f h' → h = h') ∧ (∀ c : Ω, IsExp ε (fun _ => ε c) (HahnSeries.C c)) ∧ (∀ f : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → IsExp ε f (0 : HahnSeries ℚ Ω) → f = 0) ∧ ∀ (f : ℍ → ℂ) (h : HahnSeries ℚ Ω), h ≠ 0 → IsExp ε f h → IsExp ε f⁻¹ h⁻¹ := by
  first | exact @GlobalTheory.FNExp.exp_props | exact GlobalTheory.FNExp.exp_props | (intros; apply GlobalTheory.FNExp.exp_props <;> assumption)
end
end
