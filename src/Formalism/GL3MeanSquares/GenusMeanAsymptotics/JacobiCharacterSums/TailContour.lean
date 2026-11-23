module

public import Formalism.GL3MeanSquares.SecondEstimateOfIntervalHypothesis
public import Formalism.LandauZeroFreeBounds.LogDerivRegionChiOf
public import Formalism.LandauZeroFreeBounds.NoZeroComplexOf
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LGrowth
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LRight
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LandauLemmaLfunctionZeros
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LandauLocal3
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.PerronChi
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.RectShiftChi
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.TailContourB
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LRight
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.NormIntegralComplLe
public import Mathlib.Analysis.Real.Pi.Bounds

-- Source module: Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.TailBox

section

@[expose] public section

open Complex

noncomputable section

namespace Formalism.HermitianLattices.Ext.BoxTail

lemma tail_box_log {n t Q : ℝ} (hn : 1 ≤ n) (hQ : 2 ≤ Q) (hnQ : n ≤ Q) (ht : |t| ≤ Q - 1) :
    Real.log (n * (|t| + 2)) ≤ 3 * Real.log Q := by
  have hn0 : 0 < n := by linarith
  have hpos : 0 < n * (|t| + 2) := mul_pos hn0 (by positivity)
  have h1 : n * (|t| + 2) ≤ Q ^ 3 := by
    have ht2 : |t| + 2 ≤ Q + 1 := by linarith
    have hQ2 : Q + 1 ≤ Q ^ 2 := by nlinarith
    calc n * (|t| + 2) ≤ Q * (Q + 1) := mul_le_mul hnQ ht2 (by positivity) (by linarith)
      _ ≤ Q * Q ^ 2 := mul_le_mul_of_nonneg_left hQ2 (by linarith)
      _ = Q ^ 3 := by ring
  calc Real.log (n * (|t| + 2)) ≤ Real.log (Q ^ 3) := Real.log_le_log hpos h1
    _ = 3 * Real.log Q := by rw [Real.log_pow]; norm_num

lemma tail_box_sum {δ : ℝ} (hδ : 0 < δ) (Z : Finset ℂ) (m : ℂ → ℕ) (s : ℂ)
    (h : ∀ ρ ∈ Z, δ ≤ ‖s - ρ‖) :
    ‖∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤ (∑ ρ ∈ Z, (m ρ : ℝ)) / δ := by
  calc ‖∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤ ∑ ρ ∈ Z, ‖(m ρ : ℂ) / (s - ρ)‖ := norm_sum_le _ _
    _ ≤ ∑ ρ ∈ Z, (m ρ : ℝ) / δ := Finset.sum_le_sum fun ρ hρ => by
        rw [norm_div, Complex.norm_natCast]
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hδ (h ρ hρ)
    _ = (∑ ρ ∈ Z, (m ρ : ℝ)) / δ := by rw [Finset.sum_div]

theorem tail_box_negLD (δ : ℝ) (hδ : 0 < δ) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (Q : ℝ), χ ≠ 1 → 2 ≤ Q → (N : ℝ) ≤ Q →
      Formalism.HermitianLattices.ZeroFreeRegionGL2.ZeroFreeBox Q χ →
      ∀ s : ℂ, 1 - 1 / 400 + δ ≤ s.re → |s.im| ≤ Q - 1 →
        ‖Formalism.ZeroFreeDirichlet.negLD χ s‖ ≤ K * Real.log Q := by
  obtain ⟨C, hC⟩ := Formalism.ZeroFreeDirichlet.lfunction_polynomial_growth
  obtain ⟨CR, hCR0, hCR⟩ := Formalism.ZeroFreeDirichlet.l_log_deriv_right
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hA0 : 0 ≤ Real.log (2 * (21 * (|C| + 1))) / Real.log 2 + 1 := by
    have : 0 ≤ Real.log (2 * (21 * (|C| + 1))) :=
      Real.log_nonneg (by have := abs_nonneg C; nlinarith)
    positivity
  refine ⟨3 * (Real.log (2 * (21 * (|C| + 1))) / Real.log 2 + 1) * (1440 / 11 + 1 / (δ * Real.log 2)) +
    (10 + CR) / Real.log 2, by positivity, ?_⟩
  intro N _ χ Q hχ hQ hNQ hbox s hs ht
  have hlogQ : Real.log 2 ≤ Real.log Q := Real.log_le_log two_pos hQ
  have hlogQ0 : 0 ≤ Real.log Q := hl2.le.trans hlogQ
  have hrest : 0 ≤ (10 + CR) / Real.log 2 * Real.log Q := by positivity
  by_cases hσ : s.re < 11 / 10
  ·
    have hfs : DirichletCharacter.LFunction χ s ≠ 0 := hbox s (by linarith) (by linarith)
    obtain ⟨Z, m, hZ, -, hsum, hdiff⟩ := Formalism.ZeroFreeDirichlet.landau_lemma_lfunction_zeros Formalism.ZeroFreeDirichlet.landau_local3 hC
      Formalism.ZeroFreeDirichlet.inverseBound hχ (by linarith) hσ hfs
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
    have hlog3 := tail_box_log hN1 hQ hNQ ht

    have hfar : ∀ ρ ∈ Z, δ ≤ ‖s - ρ‖ := by
      intro ρ hρ
      obtain ⟨hball, hzero⟩ := (hZ ρ).1 hρ
      rw [Metric.mem_closedBall, dist_eq_norm] at hball
      have him : |ρ.im - s.im| ≤ 11 / 20 / 3 := by
        have := Complex.abs_im_le_norm (ρ - ((21 / 20 : ℂ) + s.im * I))
        simp at this
        linarith
      have hre : ρ.re ≤ 1 - 1 / 400 := by
        by_contra hgt
        push Not at hgt
        have hρim : |ρ.im| ≤ Q := by
          have := abs_sub_abs_le_abs_sub ρ.im s.im
          linarith
        exact hbox ρ hgt hρim hzero
      have := Complex.re_le_norm (s - ρ)
      rw [Complex.sub_re] at this
      linarith
    have hS := tail_box_sum hδ Z m s hfar
    have e1 : ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s -
        ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤
        1440 / 11 * ((Real.log (2 * (21 * (|C| + 1))) / Real.log 2 + 1) * (3 * Real.log Q)) :=
      hdiff.trans (by gcongr)
    have e2 : ‖∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤
        (Real.log (2 * (21 * (|C| + 1))) / Real.log 2 + 1) * (3 * Real.log Q) / Real.log 2 / δ := by
      refine hS.trans (div_le_div_of_nonneg_right ?_ hδ.le)
      exact hsum.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog3 hA0) hl2.le)
    have htri : ‖Formalism.ZeroFreeDirichlet.negLD χ s‖ ≤
        ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s -
          ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ + ‖∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ := by
      rw [Formalism.ZeroFreeDirichlet.negLD, norm_neg]
      exact (norm_add_le _ _).trans_eq' (by rw [sub_add_cancel])
    have hδ0 : δ ≠ 0 := hδ.ne'
    have hl20 : Real.log 2 ≠ 0 := hl2.ne'
    have e3 : 1440 / 11 * ((Real.log (2 * (21 * (|C| + 1))) / Real.log 2 + 1) * (3 * Real.log Q)) +
        (Real.log (2 * (21 * (|C| + 1))) / Real.log 2 + 1) * (3 * Real.log Q) / Real.log 2 / δ =
        3 * (Real.log (2 * (21 * (|C| + 1))) / Real.log 2 + 1) * (1440 / 11 + 1 / (δ * Real.log 2)) *
          Real.log Q := by
      field_simp
    calc ‖Formalism.ZeroFreeDirichlet.negLD χ s‖ ≤ _ := htri
      _ ≤ _ := add_le_add e1 e2
      _ = _ := e3
      _ ≤ _ := by rw [add_mul]; linarith
  ·
    push Not at hσ
    have h1 : 1 < s.re := by linarith
    have hb := hCR N χ s h1
    have hinv : 1 / (s.re - 1) ≤ 10 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    have e5 : 10 + CR ≤ (10 + CR) / Real.log 2 * Real.log Q := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
      exact mul_le_mul_of_nonneg_left hlogQ (by linarith)
    have hbig : 0 ≤ 3 * (Real.log (2 * (21 * (|C| + 1))) / Real.log 2 + 1) *
        (1440 / 11 + 1 / (δ * Real.log 2)) * Real.log Q := by positivity
    calc ‖Formalism.ZeroFreeDirichlet.negLD χ s‖ ≤ 1 / (s.re - 1) + CR := hb
      _ ≤ 10 + CR := by linarith
      _ ≤ (10 + CR) / Real.log 2 * Real.log Q := e5
      _ ≤ _ := by rw [add_mul]; linarith

end Formalism.HermitianLattices.Ext.BoxTail
end
end
end

-- Source module: Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.TailContourA

section

@[expose] public section

open Complex MeasureTheory

noncomputable section

namespace Formalism.HermitianLattices.Ext.BoxTail

theorem tail_shift_alg (S R V0 V1 E a b : ℂ) (hS : S = (1 / (2 * Real.pi) : ℂ) * (V0 + E))
    (hrect : a - b + I * V0 - I * V1 = 2 * Real.pi * I * R) :
    (2 * Real.pi : ℂ) * (S - R) = E + I * (a - b) + V1 := by
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    have : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  rw [hS, mul_sub, ← mul_assoc, mul_one_div_cancel hpi, one_mul]
  linear_combination (-I) * hrect + (V0 - V1 - 2 * Real.pi * R) * Complex.I_sq

theorem tail_shift_identity {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (y σ₁ T : ℝ)
    (hy : 1 ≤ y) (hσ₁ : 0 < σ₁) (hσ₁' : σ₁ < 1) (hT : 0 < T)
    (hzf : ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ 2 → |w.im| ≤ T → DirichletCharacter.LFunction χ w ≠ 0) :
    (2 * Real.pi : ℂ) * (Formalism.ZeroFreeDirichlet.Schi χ y - Formalism.ZeroFreeDirichlet.negLD χ 1 * y) =
      (∫ t in (Set.Ioc (-T) T)ᶜ, Formalism.ZeroFreeDirichlet.Fchi χ y (((2 : ℝ) : ℂ) + (t : ℂ) * I))
      + I * ((∫ x in σ₁..2, Formalism.ZeroFreeDirichlet.Fchi χ y ((x : ℂ) + ((-T : ℝ) : ℂ) * I))
          - ∫ x in σ₁..2, Formalism.ZeroFreeDirichlet.Fchi χ y ((x : ℂ) + (T : ℂ) * I))
      + ∫ u in (-T)..T, Formalism.ZeroFreeDirichlet.Fchi χ y ((σ₁ : ℂ) + (u : ℂ) * I) := by
  obtain ⟨hint, hS⟩ := Formalism.ZeroFreeDirichlet.perron_formula_character N χ y hy 2 (by norm_num)
  have hrect := Formalism.ZeroFreeDirichlet.rectangle_contour_shift_character N χ hχ y (by linarith) σ₁ 2 T ∅ hσ₁ hσ₁' (by norm_num) hT
    (by simp) (fun w h1 h2 h3 hL => absurd hL (hzf w h1 h2 h3)) (by simp)
  simp only [Finset.sum_empty, sub_zero] at hrect
  unfold Formalism.ZF.rectInt at hrect
  rw [← integral_add_compl (s := Set.Ioc (-T) T) measurableSet_Ioc hint,
    ← intervalIntegral.integral_of_le (a := -T) (b := T) (by linarith)] at hS
  exact tail_shift_alg _ _ _ _ _ _ _ hS hrect

end Formalism.HermitianLattices.Ext.BoxTail
end
end
end

-- Source module: Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.TailContour

section

@[expose] public section

open Complex MeasureTheory

noncomputable section

namespace Formalism.HermitianLattices.Ext.BoxTail

theorem tail_contour (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 800) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (Q z η : ℝ), χ ≠ 1 → 2 ≤ Q → (N : ℝ) ≤ Q →
      Formalism.HermitianLattices.ZeroFreeRegionGL2.ZeroFreeBox Q χ → 1 ≤ z → 0 < η → η ≤ 1 →
      ‖Formalism.ZeroFreeDirichlet.Schi χ (z + z * η) - Formalism.ZeroFreeDirichlet.Schi χ z - ((z * η : ℝ) : ℂ) * Formalism.ZeroFreeDirichlet.negLD χ 1‖ ≤
        K * Real.log Q * (Real.log Q * η * z ^ (1 - 1 / 400 + δ) + z ^ 2 / Q) := by
  obtain ⟨KB, hKB0, hKB⟩ := tail_box_negLD δ hδ
  obtain ⟨C₀, hC₀, hR⟩ := Formalism.ZeroFreeDirichlet.l_log_deriv_right
  refine ⟨160 * KB + 32 * (1 + C₀), by positivity, ?_⟩
  intro N _ χ Q z η hχ hQ hNQ hbox hz hη hη1
  have hbox' : ∀ s : ℂ, 1 - 1 / 400 + δ ≤ s.re → |s.im| ≤ Q - 1 →
      ‖Formalism.ZeroFreeDirichlet.negLD χ s‖ ≤ KB * Real.log Q := hKB N χ Q hχ hQ hNQ hbox
  set σ₁ : ℝ := 1 - 1 / 400 + δ with hσ₁
  set T : ℝ := Q / 2 with hTdef
  set Lq : ℝ := Real.log Q with hLq
  have hT0 : 0 < T := by rw [hTdef]; linarith
  have hTQ : T ≤ Q - 1 := by rw [hTdef]; linarith
  have hσa : 0 < σ₁ := by rw [hσ₁]; linarith
  have hσb : σ₁ < 1 := by rw [hσ₁]; linarith
  have hσc : 1 / 2 ≤ σ₁ := by rw [hσ₁]; linarith
  have hσd : σ₁ ≤ 1 - 1 / 800 := by rw [hσ₁]; linarith
  have hLq2 : 1 / 2 ≤ Lq := by
    have := Real.log_le_log (by norm_num) hQ
    linarith [Real.log_two_gt_d9]
  have hzf : ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ 2 → |w.im| ≤ T →
      DirichletCharacter.LFunction χ w ≠ 0 := fun w h1 _ h3 =>
    hbox w (by rw [hσ₁] at h1; linarith) (by linarith)
  have hz0 : 0 < z := by linarith
  set y1 : ℝ := z + z * η with hy1def
  have hy1 : 1 ≤ y1 := by rw [hy1def]; nlinarith
  have hy12 : y1 ≤ 2 * z := by rw [hy1def]; nlinarith
  have I1 := tail_shift_identity χ hχ y1 σ₁ T hy1 hσa hσb hT0 hzf
  have I0 := tail_shift_identity χ hχ z σ₁ T hz hσa hσb hT0 hzf
  have key : (2 * Real.pi : ℂ) * (Formalism.ZeroFreeDirichlet.Schi χ y1 - Formalism.ZeroFreeDirichlet.Schi χ z - ((z * η : ℝ) : ℂ) * Formalism.ZeroFreeDirichlet.negLD χ 1)
      = (2 * Real.pi : ℂ) * (Formalism.ZeroFreeDirichlet.Schi χ y1 - Formalism.ZeroFreeDirichlet.negLD χ 1 * y1)
        - (2 * Real.pi : ℂ) * (Formalism.ZeroFreeDirichlet.Schi χ z - Formalism.ZeroFreeDirichlet.negLD χ 1 * z) := by
    rw [hy1def]; push_cast; ring
  rw [I1, I0] at key
  have hcomb := (congrArg norm key).le.trans (tc_norm_comb _ _ _ _ _ _ _ _)

  have hE : ∀ y : ℝ, 1 ≤ y → y ≤ 2 * z →
      ‖∫ t in (Set.Ioc (-T) T)ᶜ, Formalism.ZeroFreeDirichlet.Fchi χ y (((2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
        2 * Real.pi * (8 * (1 + C₀) * (z ^ 2 / Q)) := by
    intro y hy hy2
    have h := Formalism.ZF.norm_integral_compl_le (fun t => Formalism.ZeroFreeDirichlet.Fchi χ y (((2 : ℝ) : ℂ) + (t : ℂ) * I))
      ((1 + C₀) * (4 * z ^ 2)) T (by positivity) hT0 (fun t ht => by
        have ht0 : t ≠ 0 := by intro h0; rw [h0, abs_zero] at ht; linarith
        refine (tc_right_pt χ C₀ (fun s hs => hR N χ s hs) y t (by linarith) ht0).trans ?_
        have hyy : y ^ 2 ≤ 4 * z ^ 2 := by nlinarith
        gcongr)
    refine h.trans (le_of_eq ?_)
    rw [hTdef]; field_simp; ring

  have hH : ∀ y : ℝ, 1 ≤ y → y ≤ 2 * z → ∀ v : ℝ, |v| = T →
      ‖∫ x in σ₁..2, Formalism.ZeroFreeDirichlet.Fchi χ y ((x : ℂ) + (v : ℂ) * I)‖ ≤ 16 * KB * Lq * (z ^ 2 / Q) := by
    intro y hy hy2 v hv
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun x : ℝ => Formalism.ZeroFreeDirichlet.Fchi χ y ((x : ℂ) + (v : ℂ) * I))
      (C := KB * Lq * (4 * z ^ 2) / T ^ 2) (a := σ₁) (b := 2) (fun x hx => by
        rw [Set.uIoc_of_le (by linarith)] at hx
        have hM := hbox' ((x : ℂ) + (v : ℂ) * I) (by simp; exact hx.1.le)
          (by simp; rw [hv]; exact hTQ)
        refine (tc_horiz_pt χ _ y T x v hy hT0 hv hx.2 hM).trans ?_
        have hyy : y ^ 2 ≤ 4 * z ^ 2 := by nlinarith
        have hM0 : 0 ≤ KB * Real.log Q := le_trans (norm_nonneg _) hM
        gcongr)
    refine h.trans ?_
    have hlen : |2 - σ₁| ≤ 2 := by rw [abs_of_pos (by linarith)]; linarith
    have hKL : 0 ≤ KB * Lq := by positivity
    calc KB * Lq * (4 * z ^ 2) / T ^ 2 * |2 - σ₁| ≤ KB * Lq * (4 * z ^ 2) / T ^ 2 * 2 := by gcongr
      _ = 32 * (KB * Lq) * (z ^ 2 / Q) / Q := by rw [hTdef]; field_simp; ring
      _ ≤ 32 * (KB * Lq) * (z ^ 2 / Q) / 2 := by gcongr
      _ = 16 * KB * Lq * (z ^ 2 / Q) := by ring

  have hV := tc_left_int χ hχ z η σ₁ T (KB * Lq) hz0 hη.le hη1 hσc hσd hT0.le
    (fun u hu => hzf _ (by simp) (by simp; linarith) (by simpa using hu))
    (fun u hu => hbox' _ (by simp) (by simpa using hu.trans hTQ))
  rw [← hy1def] at hV
  have hlog : Real.log (1 + 800 * T) ≤ 10 * Lq := by rw [hTdef, hLq]; exact tc_log_bound Q hQ
  have hLq0 : 0 ≤ Lq := by linarith
  set A : ℝ := z ^ 2 / Q with hAdef
  set Bv : ℝ := η * z ^ σ₁ with hBvdef
  have hA0 : 0 ≤ A := div_nonneg (sq_nonneg z) (by linarith)
  have hB0 : 0 ≤ Bv := mul_nonneg hη.le (Real.rpow_nonneg hz0.le _)
  have hV' : ‖(∫ u in (-T)..T, Formalism.ZeroFreeDirichlet.Fchi χ y1 ((σ₁ : ℂ) + (u : ℂ) * I))
      - ∫ u in (-T)..T, Formalism.ZeroFreeDirichlet.Fchi χ z ((σ₁ : ℂ) + (u : ℂ) * I)‖ ≤ 160 * KB * Lq ^ 2 * Bv := by
    refine hV.trans ?_
    have hn : 0 ≤ KB * Lq * (4 * η * z ^ σ₁) :=
      mul_nonneg (mul_nonneg hKB0 hLq0) (mul_nonneg (by linarith) (Real.rpow_nonneg hz0.le _))
    calc KB * Lq * (4 * η * z ^ σ₁) * (4 * Real.log (1 + 800 * T))
        ≤ KB * Lq * (4 * η * z ^ σ₁) * (4 * (10 * Lq)) := by
          apply mul_le_mul_of_nonneg_left _ hn; linarith
      _ = 160 * KB * Lq ^ 2 * Bv := by rw [hBvdef]; ring
  have hE1 := hE y1 hy1 hy12
  have hE0 := hE z hz (by linarith)
  have hHa1 := hH y1 hy1 hy12 (-T) (by rw [abs_neg, abs_of_pos hT0])
  have hHb1 := hH y1 hy1 hy12 T (abs_of_pos hT0)
  have hHa0 := hH z hz (by linarith) (-T) (by rw [abs_neg, abs_of_pos hT0])
  have hHb0 := hH z hz (by linarith) T (abs_of_pos hT0)
  have hn : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by
    rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [norm_mul, hn] at hcomb
  set X := ‖Formalism.ZeroFreeDirichlet.Schi χ y1 - Formalism.ZeroFreeDirichlet.Schi χ z - ((z * η : ℝ) : ℂ) * Formalism.ZeroFreeDirichlet.negLD χ 1‖ with hXdef
  have hpi : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hW : 0 ≤ 64 * KB * Lq * A + 160 * KB * Lq ^ 2 * Bv := by
    have := mul_nonneg (mul_nonneg hKB0 hLq0) hA0
    have := mul_nonneg (mul_nonneg hKB0 (sq_nonneg Lq)) hB0
    linarith
  have hWW := le_mul_of_one_le_left hW hpi
  have h2X : 2 * Real.pi * X ≤
      2 * Real.pi * (16 * (1 + C₀) * A + (64 * KB * Lq * A + 160 * KB * Lq ^ 2 * Bv)) := by
    linarith
  have hXR : X ≤ 16 * (1 + C₀) * A + (64 * KB * Lq * A + 160 * KB * Lq ^ 2 * Bv) :=
    le_of_mul_le_mul_left h2X (by positivity)
  have p1 : 0 ≤ KB * Lq * A := mul_nonneg (mul_nonneg hKB0 hLq0) hA0
  have p2 : 0 ≤ (1 + C₀) * Lq ^ 2 * Bv := mul_nonneg (mul_nonneg (by linarith) (sq_nonneg Lq)) hB0
  have p3 : 0 ≤ (1 + C₀) * A * (2 * Lq - 1) := mul_nonneg (mul_nonneg (by linarith) hA0) (by linarith)
  have hgoal : (160 * KB + 32 * (1 + C₀)) * Lq * (Lq * η * z ^ σ₁ + A) =
      160 * KB * Lq ^ 2 * Bv + 160 * KB * Lq * A + 32 * (1 + C₀) * Lq ^ 2 * Bv
        + 32 * (1 + C₀) * Lq * A := by rw [hBvdef]; ring
  rw [hgoal]
  linarith

end Formalism.HermitianLattices.Ext.BoxTail
end
end
end
