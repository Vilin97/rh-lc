module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.MeanValue

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasDerivAtOfContinuousHom

section

@[expose] public section

namespace GlobalTheory.CompanionTheory.CharDeriv

theorem hasDerivAt_of_continuous_hom :
    ∀ (χ : ℝ → ℂ), Continuous χ → χ 0 = 1 → (∀ s t, χ (s + t) = χ s * χ t) →
      ∃ c : ℂ, ∀ t, HasDerivAt χ (c * χ t) t := by
  intro χ hc h0 hadd
  have hP : ∀ x : ℝ, HasDerivAt (fun y : ℝ => ∫ s in (0 : ℝ)..y, χ s) (χ x) x := fun x =>
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
      (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
  obtain ⟨δ, hI⟩ : ∃ δ : ℝ, (∫ s in (0 : ℝ)..δ, χ s) ≠ 0 := by
    by_contra h
    push_neg at h
    have hz : (fun y : ℝ => ∫ s in (0 : ℝ)..y, χ s) = fun _ => (0 : ℂ) := funext h
    have h1 := hP 0
    rw [hz] at h1
    have h2 := h1.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
    rw [h0] at h2
    exact one_ne_zero h2
  have key : ∀ t : ℝ, χ t = ((∫ s in (0 : ℝ)..(t + δ), χ s) - ∫ s in (0 : ℝ)..t, χ s) /
      (∫ s in (0 : ℝ)..δ, χ s) := by
    intro t
    rw [eq_div_iff hI, ← intervalIntegral.integral_const_mul]
    have h1 : (∫ s in (0 : ℝ)..δ, χ t * χ s) = ∫ u in t..(t + δ), χ u := by
      have h2 := intervalIntegral.integral_comp_add_left (a := 0) (b := δ) (fun u => χ u) t
      rw [add_zero] at h2
      rw [← h2]
      exact intervalIntegral.integral_congr fun s _ => (hadd t s).symm
    rw [h1]
    exact (intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)).symm
  refine ⟨(χ δ - 1) / (∫ s in (0 : ℝ)..δ, χ s), fun t => ?_⟩
  have hD : HasDerivAt (fun y : ℝ => ((∫ s in (0 : ℝ)..(y + δ), χ s) - ∫ s in (0 : ℝ)..y, χ s) /
      (∫ s in (0 : ℝ)..δ, χ s)) ((χ (t + δ) - χ t) / (∫ s in (0 : ℝ)..δ, χ s)) t := by
    have h3 : HasDerivAt (fun y : ℝ => ∫ s in (0 : ℝ)..(y + δ), χ s) (χ (t + δ)) t := by
      simpa using (hP (t + δ)).comp_add_const t δ
    exact (h3.sub (hP t)).div_const _
  have hval : (χ δ - 1) / (∫ s in (0 : ℝ)..δ, χ s) * χ t =
      (χ (t + δ) - χ t) / (∫ s in (0 : ℝ)..δ, χ s) := by
    rw [hadd t δ]
    ring
  rw [hval]
  exact hD.congr_of_eventuallyEq (Filter.Eventually.of_forall key)

end GlobalTheory.CompanionTheory.CharDeriv
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WirtingerCombinationNeZero

section

@[expose] public section

namespace GlobalTheory.CompanionTheory.Unitary

theorem wirtinger_combination_ne_zero : ∀ (χ : ℂ → ℂ), Continuous χ → (∀ z w, χ (z + w) = χ z * χ w) →
    (∀ z, ‖χ z‖ = 1) → (∃ z, χ z ≠ 1) → ∀ (D : ℂ → ℂ),
    (∀ z, HasDerivAt (fun t : ℝ => χ (t * z)) (D z) 0) →
    ∀ β : ℂ, β ≠ 0 → D β - Complex.I * D (β * Complex.I) ≠ 0 := by
  intro χ _ hmul hnorm hnt D hD β hβ
  have χ0 : χ 0 = 1 := by
    have h1 := hmul 0 0
    rw [add_zero] at h1
    have hne : χ 0 ≠ 0 := by
      intro h
      have h2 := hnorm 0
      rw [h, norm_zero] at h2
      exact zero_ne_one h2
    exact mul_left_cancel₀ hne (h1.symm.trans (mul_one (χ 0)).symm)
  have hf0 : ∀ z, χ (((0 : ℝ) : ℂ) * z) = 1 := by
    intro z
    simp [χ0]
  have hre : ∀ w, (D w).re = 0 := by
    intro w
    have h1 := (hD w).mul (hD w).star
    have hconst : ((fun t : ℝ => χ (t * w)) * fun t : ℝ => star (χ (t * w))) = fun _ => (1 : ℂ) := by
      funext t
      simp only [Pi.mul_apply]
      rw [← starRingEnd_apply, RCLike.mul_conj, hnorm]
      simp
    rw [hconst] at h1
    have h2 := h1.unique (hasDerivAt_const (0 : ℝ) (1 : ℂ))
    rw [hf0] at h2
    simp only [star_one, mul_one, one_mul] at h2
    have h3 := congrArg Complex.re h2
    simp only [Complex.add_re, Complex.star_def, Complex.conj_re, Complex.zero_re] at h3
    linarith
  have hadd : ∀ z w, D (z + w) = D z + D w := by
    intro z w
    have h1 := (hD z).mul (hD w)
    have hfun : ((fun t : ℝ => χ (t * z)) * fun t : ℝ => χ (t * w)) = fun t : ℝ => χ (t * (z + w)) := by
      funext t
      simp only [Pi.mul_apply]
      rw [mul_add, hmul]
    rw [hfun, hf0, hf0, mul_one, one_mul] at h1
    exact (hD (z + w)).unique h1
  have hsmul : ∀ (r : ℝ) (z : ℂ), D (r * z) = r * D z := by
    intro r z
    have hr : HasDerivAt (fun t : ℝ => r * t) r 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul r
    have hz : HasDerivAt (fun t : ℝ => χ (t * z)) (D z) ((fun t : ℝ => r * t) 0) := by
      simp only [mul_zero]
      exact hD z
    have h1 := HasDerivAt.scomp (h := fun t : ℝ => r * t) (0 : ℝ) hz hr
    have hfun : ((fun t : ℝ => χ (t * z)) ∘ fun t : ℝ => r * t) = fun t : ℝ => χ (t * (r * z)) := by
      funext t
      simp only [Function.comp]
      congr 1
      push_cast
      ring
    rw [hfun] at h1
    rw [(hD (r * z)).unique h1, Complex.real_smul]
  have hzero : (∀ z, D z = 0) → False := by
    intro h0
    obtain ⟨z, hz⟩ := hnt
    apply hz
    have hder : ∀ s : ℝ, HasDerivAt (fun t : ℝ => χ (t * z)) 0 s := by
      intro s
      have h1 : HasDerivAt (fun t : ℝ => χ (((t - s : ℝ) : ℂ) * z)) (D z) s :=
        HasDerivAt.comp_sub_const (f := fun t : ℝ => χ (t * z)) s s (by rw [sub_self]; exact hD z)
      have h2 := h1.const_mul (χ (s * z))
      have hfun : (fun t : ℝ => χ (s * z) * χ (((t - s : ℝ) : ℂ) * z)) = fun t : ℝ => χ (t * z) := by
        funext t
        rw [← hmul]
        congr 1
        push_cast
        ring
      rw [hfun, h0, mul_zero] at h2
      exact h2
    have hc := is_const_of_deriv_eq_zero (fun s => (hder s).differentiableAt) (fun s => (hder s).deriv) 1 0
    simp only [Complex.ofReal_one, one_mul] at hc
    rw [hc, hf0]
  intro hcomb
  have ha : D β = Complex.I * D (β * Complex.I) := sub_eq_zero.mp hcomb
  have hb0 : D (β * Complex.I) = 0 := by
    apply Complex.ext
    · exact hre _
    · have h1 := congrArg Complex.re ha
      simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, hre] at h1
      simp only [Complex.zero_im]
      linarith
  have ha0 : D β = 0 := by rw [ha, hb0, mul_zero]
  apply hzero
  intro z
  have hz : z = ((z / β).re : ℂ) * β + ((z / β).im : ℂ) * (β * Complex.I) := by
    have e : z = (z / β) * β := by field_simp
    conv_lhs => rw [e, ← Complex.re_add_im (z / β)]
    ring
  rw [hz, hadd, hsmul, hsmul, ha0, hb0, mul_zero, mul_zero, add_zero]

end GlobalTheory.CompanionTheory.Unitary
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.ArchimedeanWhittakerDerivatives.HasDerivAtOfMulHom

section

@[expose] public section

namespace PositivityTheory.Rg.Cz

theorem hasDerivAt_of_mulHom (χ : ℝ → ℂ) (hc : Continuous χ) (h0 : χ 0 = 1) (hm : ∀ s t, χ (s + t) = χ s * χ t) :
    ∃ c : ℂ, ∀ t, HasDerivAt χ (c * χ t) t :=
  GlobalTheory.CompanionTheory.CharDeriv.hasDerivAt_of_continuous_hom χ hc h0 hm

theorem wirtinger_ne_zero (χ : ℂ → ℂ) (hc : Continuous χ) (hm : ∀ z w, χ (z + w) = χ z * χ w) (hn : ∀ z, ‖χ z‖ = 1)
    (ht : ∃ z, χ z ≠ 1) (D : ℂ → ℂ) (hD : ∀ z, HasDerivAt (fun t : ℝ => χ (t * z)) (D z) 0) (β : ℂ) (hβ : β ≠ 0) :
    D β - Complex.I * D (β * Complex.I) ≠ 0 :=
  GlobalTheory.CompanionTheory.Unitary.wirtinger_combination_ne_zero χ hc hm hn ht D hD β hβ

end PositivityTheory.Rg.Cz
end
end
