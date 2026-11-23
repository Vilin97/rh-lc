module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Tactic.Basify

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodicLeftHalfPlaneShiftNonnegOfImPos

section

@[expose] public section

open Complex MeasureTheory

namespace GlobalTheory

theorem periodic_strip_shift_nonneg (c : ℝ) (f : ℂ → ℂ) (m : ℤ)
    (hf : DifferentiableOn ℂ f {s : ℂ | s.re < c})
    (hper : ∀ s : ℂ, s.re < c → f (s + 2 * Real.pi * Complex.I) = f s + m)
    (hpos : ∀ s : ℂ, s.re < c → 0 < (f s).im) : 0 ≤ m := by
  have hcont : ContinuousOn f {s : ℂ | s.re < c} := hf.continuousOn
  have hvert : ∀ x : ℝ, x < c → IntervalIntegrable (fun y : ℝ => f (x + y * I)) volume 0 (2 * Real.pi) := by
    intro x hx
    apply ContinuousOn.intervalIntegrable
    refine hcont.comp (by fun_prop) ?_
    intro y _
    simp [hx]
  have hhor : ∀ (x₁ x₂ : ℝ), x₁ ≤ x₂ → x₂ < c → IntervalIntegrable (fun x : ℝ => f (x : ℂ)) volume x₁ x₂ := by
    intro x₁ x₂ h12 h2
    apply ContinuousOn.intervalIntegrable
    refine hcont.comp (by fun_prop) ?_
    intro x hx
    rw [Set.uIcc_of_le h12] at hx
    simp only [Set.mem_setOf_eq, ofReal_re]
    linarith [hx.2]
  have hVim : ∀ x : ℝ, x < c → 0 ≤ (∫ y : ℝ in (0:ℝ)..(2 * Real.pi), f (x + y * I)).im := by
    intro x hx
    have h2pi : (0:ℝ) ≤ 2 * Real.pi := by positivity
    have hc := Complex.imCLM.intervalIntegral_comp_comm (hvert x hx)
    simp only [Complex.imCLM_apply] at hc
    rw [← hc]
    apply intervalIntegral.integral_nonneg h2pi
    intro y _
    exact (hpos _ (by simp [hx])).le
  have key : ∀ x₁ x₂ : ℝ, x₁ ≤ x₂ → x₂ < c →
      (∫ y : ℝ in (0:ℝ)..(2 * Real.pi), f (x₁ + y * I)).im
        = (∫ y : ℝ in (0:ℝ)..(2 * Real.pi), f (x₂ + y * I)).im + m * (x₂ - x₁) := by
    intro x₁ x₂ h12 h2c
    have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f (x₁ : ℂ)
      ((x₂ : ℂ) + ((2 * Real.pi : ℝ) : ℂ) * I) ?_
    · simp only [ofReal_re, ofReal_im, add_re, add_im, mul_re, mul_im, I_re, I_im, ofReal_re, ofReal_im,
        mul_zero, mul_one, sub_zero, zero_mul, add_zero, zero_add, ofReal_zero] at hrect
      have htop : (∫ x : ℝ in x₁..x₂, f (x + ((2 * Real.pi : ℝ) : ℂ) * I))
          = (∫ x : ℝ in x₁..x₂, f (x : ℂ)) + (m : ℂ) * ((x₂ - x₁ : ℝ) : ℂ) := by
        have hc : (∫ x : ℝ in x₁..x₂, f (x + ((2 * Real.pi : ℝ) : ℂ) * I))
            = ∫ x : ℝ in x₁..x₂, (f (x : ℂ) + m) := by
          apply intervalIntegral.integral_congr
          intro x hx
          rw [Set.uIcc_of_le h12] at hx
          have hxc : (x : ℂ).re < c := by simp; linarith [hx.2]
          simp only
          rw [← hper _ hxc]
          congr 1
          push_cast
          ring
        rw [hc, intervalIntegral.integral_add (hhor x₁ x₂ h12 h2c) intervalIntegrable_const,
          intervalIntegral.integral_const]
        simp [mul_comm]
      rw [htop] at hrect
      have hre := congrArg Complex.re hrect
      simp at hre
      linarith
    · apply hf.mono
      intro z hz
      rw [Complex.mem_reProdIm] at hz
      simp only [ofReal_re, add_re, mul_re, I_re, I_im, ofReal_im, mul_zero, mul_one, sub_zero, add_zero] at hz
      rw [Set.uIcc_of_le h12] at hz
      show z.re < c
      linarith [hz.1.2]
  by_contra hm
  push_neg at hm
  have hm1 : (m : ℝ) ≤ -1 := by exact_mod_cast (by omega : m ≤ -1)
  set a := (∫ y : ℝ in (0:ℝ)..(2 * Real.pi), f ((c - 1 : ℝ) + y * I)).im with ha
  have ha0 : 0 ≤ a := hVim (c - 1) (by linarith)
  have h1 := key (c - 1 - (a + 1)) (c - 1) (by linarith) (by linarith)
  have h2 := hVim (c - 1 - (a + 1)) (by linarith)
  rw [h1] at h2
  nlinarith [mul_le_mul_of_nonneg_right hm1 (by linarith : (0:ℝ) ≤ a + 1)]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodicLeftHalfPlaneShiftNonnegOfImPosStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.periodic_left_halfPlane_shift_nonneg_of_im_pos : ∀ (c : ℝ) (f : ℂ → ℂ) (m : ℤ), DifferentiableOn ℂ f {s : ℂ | s.re < c} → (∀ s : ℂ, s.re < c → f (s + 2 * Real.pi * Complex.I) = f s + m) → (∀ s : ℂ, s.re < c → 0 < (f s).im) → 0 ≤ m := by
  first | exact @GlobalTheory.periodic_strip_shift_nonneg | exact GlobalTheory.periodic_strip_shift_nonneg | (intros; apply GlobalTheory.periodic_strip_shift_nonneg <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonodromyMatrixDotProductNonnegIntegral

section

@[expose] public section

open GlobalTheory.ShFam.Hor
open scoped Matrix

namespace GlobalTheory

theorem monodromy_dotProduct_nonneg : ∀ (n a g : ℕ) (ha : a ≤ n) (ρ₁ : ℝ) (τ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), 0 < ρ₁ → ρ₁ ≤ 1 → (∀ i j, DifferentiableOn ℂ (fun s => τ s i j) {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁}) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → (τ s).IsSymm ∧ ((τ s).map Complex.im).PosDef) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → ∀ k : Fin a, τ (s + Pi.single (Fin.castLE ha k) (2 * Real.pi * Complex.I)) = τ s + (B k).map (Int.cast : ℤ → ℂ)) → ∀ (k : Fin a) (v : Fin g → ℤ), 0 ≤ dotProduct v ((B k).mulVec v) := by
  intro n a g ha ρ₁ τ B hρ0 hρ1 hdiff hpos hmon k v
  by_cases hv : v = 0
  · subst hv; simp
  set j : Fin n := Fin.castLE ha k with hj
  have hjlt : (j : ℕ) < a := by simp [hj]
  let s₀ : Fin n → ℂ := fun i => if (i : ℕ) < a then ((Real.log (ρ₁ / 2) : ℝ) : ℂ) else 0
  let u : ℂ → Fin n → ℂ := fun t => Function.update s₀ j t
  let D := {s : Fin n → ℂ | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁}
  have hlog2 : Real.log (ρ₁ / 2) < 0 := Real.log_neg (by positivity) (by linarith)
  have hlogle : Real.log ρ₁ ≤ 0 := Real.log_nonpos hρ0.le hρ1
  have hexp2 : Real.exp (Real.log (ρ₁ / 2)) = ρ₁ / 2 := Real.exp_log (by positivity)
  have hmem : ∀ t : ℂ, t.re < Real.log ρ₁ → u t ∈ D := by
    intro t ht
    refine ⟨?_, ?_⟩
    · intro i
      by_cases hi : i = j
      · subst hi
        simp only [u, Function.update_self, hjlt, if_true]
        linarith
      · simp only [u, Function.update_of_ne hi, s₀]
        split_ifs with h
        · simpa using hlog2
        · simp
    · rw [mem_ball_zero_iff, pi_norm_lt_iff hρ0]
      intro i
      by_cases hi : i = j
      · subst hi
        simp only [logExp, u, Function.update_self, hjlt, if_true, Complex.norm_exp]
        calc Real.exp t.re < Real.exp (Real.log ρ₁) := Real.exp_lt_exp.2 ht
          _ = ρ₁ := Real.exp_log hρ0
      · simp only [logExp, u, Function.update_of_ne hi, s₀]
        split_ifs with h
        · rw [Complex.norm_exp, Complex.ofReal_re, hexp2]; linarith
        · simpa using hρ0
  let v' : Fin g → ℂ := fun i => (v i : ℂ)
  let f : ℂ → ℂ := fun t => v' ⬝ᵥ (τ (u t) *ᵥ v')
  have hshift : ∀ t : ℂ, u (t + 2 * Real.pi * Complex.I) = u t + Pi.single j (2 * Real.pi * Complex.I) := by
    intro t
    ext i
    by_cases hi : i = j
    · subst hi; simp [u]
    · simp [u, hi, Function.update_of_ne hi, Pi.single_apply]
  have hcast : v' ⬝ᵥ ((B k).map (Int.cast : ℤ → ℂ) *ᵥ v') = ((v ⬝ᵥ (B k *ᵥ v) : ℤ) : ℂ) := by
    simp [v', dotProduct, Matrix.mulVec, Matrix.map_apply]
  have hper : ∀ t : ℂ, t.re < Real.log ρ₁ → f (t + 2 * Real.pi * Complex.I) = f t + ((v ⬝ᵥ (B k *ᵥ v) : ℤ) : ℂ) := by
    intro t ht
    have h1 := hmon (u t) (hmem t ht).1 (hmem t ht).2 k
    simp only [f]
    rw [hshift t, h1, Matrix.add_mulVec, dotProduct_add, hcast]
  let v'' : Fin g → ℝ := fun i => (v i : ℝ)
  have hv'' : v'' ≠ 0 := by
    intro h0
    apply hv
    funext i
    have := congrFun h0 i
    simpa [v''] using this
  have him : ∀ t : ℂ, t.re < Real.log ρ₁ → 0 < (f t).im := by
    intro t ht
    have hp := ((hpos (u t) (hmem t ht).1 (hmem t ht).2).2).dotProduct_mulVec_pos hv''
    have heq : (f t).im = star v'' ⬝ᵥ (((τ (u t)).map Complex.im) *ᵥ v'') := by
      simp [f, v', v'', dotProduct, Matrix.mulVec, Complex.im_sum, Complex.mul_im, Finset.mul_sum]
    rw [heq]; exact hp
  have hu : Differentiable ℂ u := fun t => (hasFDerivAt_update s₀ t).differentiableAt
  have hent : ∀ i l, DifferentiableOn ℂ (fun t => τ (u t) i l) {t : ℂ | t.re < Real.log ρ₁} :=
    fun i l => (hdiff i l).comp hu.differentiableOn (fun t ht => hmem t ht)
  have hdf : DifferentiableOn ℂ f {t : ℂ | t.re < Real.log ρ₁} := by
    simp only [f, dotProduct, Matrix.mulVec]
    apply DifferentiableOn.fun_sum
    intro i _
    apply DifferentiableOn.const_mul
    apply DifferentiableOn.fun_sum
    intro l _
    exact (hent i l).mul_const _
  exact_mod_cast GlobalTheory.T.periodic_left_halfPlane_shift_nonneg_of_im_pos (Real.log ρ₁) f (v ⬝ᵥ (B k *ᵥ v)) hdf hper him

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonodromyMatrixDotProductNonnegIntegralStatement

section

@[expose] public section

open GlobalTheory.ShFam.Hor


theorem _root_.GlobalTheory.T.monodromy_matrix_dotProduct_nonneg_integral : ∀ (n a g : ℕ) (ha : a ≤ n) (ρ₁ : ℝ) (τ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), 0 < ρ₁ → ρ₁ ≤ 1 → (∀ i j, DifferentiableOn ℂ (fun s => τ s i j) {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁}) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → (τ s).IsSymm ∧ ((τ s).map Complex.im).PosDef) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → ∀ k : Fin a, τ (s + Pi.single (Fin.castLE ha k) (2 * Real.pi * Complex.I)) = τ s + (B k).map (Int.cast : ℤ → ℂ)) → ∀ (k : Fin a) (v : Fin g → ℤ), 0 ≤ dotProduct v ((B k).mulVec v) := by
  first | exact @GlobalTheory.monodromy_dotProduct_nonneg | exact GlobalTheory.monodromy_dotProduct_nonneg | (intros; apply GlobalTheory.monodromy_dotProduct_nonneg <;> assumption)
end
end
