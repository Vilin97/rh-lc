module

public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.IsTransSys
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorDefs
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.NormNatCastClOfNotDvd
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorBasic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.Style
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementK
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorContr
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorHensel
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.NonsingularNorm
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ExistsTeichmullerRepModPrime
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.NormNatCastClOfNotDvd
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorRes
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorSub
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorSub
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorClose

section

@[expose] public section

noncomputable section
open scoped Classical

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM Formalism.ELL WeierstrassCurve
open Formalism.L2.Th1.E (px py IntCurve)
open Formalism.L2.Th1.A (shortW)

theorem chord_identity {C : Type} [Field C] (W : WeierstrassCurve C) (h1 : W.a₁ = 0) (h2 : W.a₂ = 0)
    (h3 : W.a₃ = 0) (A B : W.toAffine.Point) (hA : A ≠ 0) (hB : B ≠ 0) (hs : A + B ≠ 0)
    (hd : A - B ≠ 0) :
    (px W A - px W B) ^ 2 * (px W (A + B) - px W (A - B)) = -4 * py W A * py W B := by
  rw [sub_eq_add_neg A B]
  rcases A with _ | ⟨xA, yA, hA'⟩
  · exact absurd rfl hA
  rcases B with _ | ⟨xB, yB, hB'⟩
  · exact absurd rfl hB
  by_cases hx : xA = xB
  · exfalso
    subst hx
    have e1 := (WeierstrassCurve.Affine.equation_iff _ _).1 hA'.1
    have e2 := (WeierstrassCurve.Affine.equation_iff _ _).1 hB'.1
    have hm : (yA - yB) * (yA + yB) = 0 := by
      linear_combination e1 - e2 - xA * (yA - yB) * h1 - (yA - yB) * h3
    rcases mul_eq_zero.1 hm with h | h
    · have hy : yA = yB := sub_eq_zero.1 h
      subst hy
      exact hd (sub_self _)
    · have hy : yA = W.toAffine.negY xA yB := by
        rw [WeierstrassCurve.Affine.negY]
        linear_combination h + xA * h1 + h3
      exact hs (WeierstrassCurve.Affine.Point.add_of_Y_eq rfl hy)
  · have hx' : xA - xB ≠ 0 := sub_ne_zero.2 hx
    rw [WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.add_of_X_ne hx,
      WeierstrassCurve.Affine.Point.add_of_X_ne hx]
    simp only [px, py, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.slope_of_X_ne hx,
      WeierstrassCurve.Affine.negY, h1, h2, h3]
    field_simp
    ring

variable {C : Type} [NormedField C] [IsUltrametricDist C]

theorem norm_x_sub_le_of_formalGroup (W : WeierstrassCurve C) (h1 : W.a₁ = 0) (h2 : W.a₂ = 0) (h3 : W.a₃ = 0)
    (hW : IntegralModel W) (A B : W.toAffine.Point) (hA : A ≠ 0) (hB : B ≠ 0)
    (hAy : ‖py W A‖ ≤ 1) (hBy : ‖py W B‖ ≤ 1) (hs : A + B ≠ 0) (hsx : ‖px W (A + B)‖ ≤ 1)
    (hd : A - B ≠ 0) (hdx : InFormalGroupPoints (A - B)) : ‖px W A - px W B‖ ≤ ‖uOf (A - B)‖ := by
  obtain ⟨-, -, -, h4, h6⟩ := hW
  have hc := chord_identity W h1 h2 h3 A B hA hB hs hd
  generalize A - B = D at hc hd hdx ⊢
  rcases D with _ | ⟨xd, yd, hdn⟩
  · exact absurd rfl hd
  have hX : 1 < ‖xd‖ := hdx
  have hX0 : 0 < ‖xd‖ := by linarith
  have hXne : ‖xd‖ ≠ 0 := hX0.ne'
  have hc' : (px W A - px W B) ^ 2 * (px W (A + B) - xd) = -4 * py W A * py W B := hc
  have eqd := (WeierstrassCurve.Affine.equation_iff _ _).1 hdn.1
  have e : yd ^ 2 = xd ^ 3 + (W.a₄ * xd + W.a₆) := by
    linear_combination eqd - xd * yd * h1 - yd * h3 + xd ^ 2 * h2
  have hr : ‖W.a₄ * xd + W.a₆‖ ≤ ‖xd‖ := by
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) h4
    · linarith
  have hX2 : 1 < ‖xd‖ ^ 2 := by nlinarith
  have hX3 : ‖xd‖ < ‖xd‖ ^ 3 := by
    have hm := mul_lt_mul_of_pos_left hX2 hX0
    nlinarith
  have hne2 : ‖xd ^ 3‖ ≠ ‖W.a₄ * xd + W.a₆‖ := by
    rw [norm_pow]
    exact ne_of_gt (lt_of_le_of_lt hr hX3)
  have hY : ‖yd‖ ^ 2 = ‖xd‖ ^ 3 := by
    rw [← norm_pow, e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne2, norm_pow,
      max_eq_left (by linarith)]
  have hne1 : ‖px W (A + B)‖ ≠ ‖-xd‖ := ne_of_lt (by rw [norm_neg]; linarith)
  have hxs : ‖px W (A + B) - xd‖ = ‖xd‖ := by
    rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne1, norm_neg,
      max_eq_right (by linarith)]
  have h2n : ‖(2 : C)‖ ≤ 1 := by
    have h := IsUltrametricDist.norm_add_le_max (1 : C) 1
    rw [one_add_one_eq_two, norm_one, max_self] at h
    exact h
  have h4n : ‖(4 : C)‖ ≤ 1 := by
    have h := IsUltrametricDist.norm_add_le_max (2 : C) 2
    rw [show (2 : C) + 2 = 4 by norm_num] at h
    exact h.trans (max_le h2n h2n)
  have hn := congrArg norm hc'
  rw [norm_mul, norm_pow, hxs, norm_mul, norm_mul, norm_neg] at hn
  have ha0 := norm_nonneg (py W A)
  have hb0 := norm_nonneg (py W B)
  have h40 := norm_nonneg (4 : C)
  have hab : ‖(4 : C)‖ * ‖py W A‖ ≤ 1 := by nlinarith
  have habc : ‖(4 : C)‖ * ‖py W A‖ * ‖py W B‖ ≤ 1 := by nlinarith [mul_nonneg h40 ha0]
  have hbound : ‖px W A - px W B‖ ^ 2 * ‖xd‖ ≤ 1 := by rw [hn]; exact habc
  show ‖px W A - px W B‖ ≤ ‖-xd / yd‖
  rw [norm_div, norm_neg]
  have hq : (‖xd‖ / ‖yd‖) ^ 2 * ‖xd‖ = 1 := by
    rw [div_pow, hY]
    first
      | (field_simp; ring)
      | field_simp
  have hs0 := norm_nonneg (px W A - px W B)
  have hq0 : 0 ≤ ‖xd‖ / ‖yd‖ := div_nonneg (norm_nonneg _) (norm_nonneg _)
  by_contra hlt
  push_neg at hlt
  have hsq : (‖xd‖ / ‖yd‖) ^ 2 < ‖px W A - px W B‖ ^ 2 := by
    nlinarith [mul_pos (sub_pos.2 hlt) (by linarith : 0 < ‖px W A - px W B‖ + ‖xd‖ / ‖yd‖)]
  nlinarith

end ReciprocityTheory.ChartRestriction.L1
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorLift

section

@[expose] public section

noncomputable section
open scoped Classical

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM Formalism.ELL WeierstrassCurve
open Formalism.L2.Th1.E (px py IntCurve)
open Formalism.L2.Th1.A (shortW)

variable {l : ℕ} [Fact l.Prime] {g2 g3 : ℂ_[l]}

theorem cubic_close {C : Type} [NormedField C] [IsUltrametricDist C] {x a p q : C} (hx : ‖x‖ ≤ 1)
    (ha : ‖a‖ ≤ 1) (hp : ‖p‖ ≤ 1) (hxa : ‖x - a‖ < 1) :
    ‖(a ^ 3 + p * a + q) - (x ^ 3 + p * x + q)‖ < 1 := by
  have e : (a ^ 3 + p * a + q) - (x ^ 3 + p * x + q) = (a - x) * (a ^ 2 + a * x + x ^ 2 + p) := by ring
  rw [e, norm_mul]
  have h1 : ‖a ^ 2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha
  have h2 : ‖a * x‖ ≤ 1 := by rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hx
  have h3 : ‖x ^ 2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx
  have hb : ‖a ^ 2 + a * x + x ^ 2 + p‖ ≤ 1 :=
    (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)) h3)) hp)
  rw [norm_sub_rev] at hxa
  calc ‖a - x‖ * ‖a ^ 2 + a * x + x ^ 2 + p‖ ≤ ‖a - x‖ * 1 := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ < 1 := by rw [mul_one]; exact hxa

theorem norm_one_of_close {C : Type} [NormedField C] [IsUltrametricDist C] {c d : C} (hd : ‖d‖ = 1)
    (h : ‖c - d‖ < 1) : ‖c‖ = 1 := by
  have hne : ‖d‖ ≠ ‖c - d‖ := by rw [hd]; exact (ne_of_lt h).symm
  have h2 := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
  rw [add_sub_cancel, hd] at h2
  rw [h2]
  exact max_eq_left h.le

theorem tor_lift (h : GoodPair l g2 g3) (P : (shortW g2 g3).toAffine.Point) (hP0 : P ≠ 0)
    (hx : ‖px _ P‖ ≤ 1) (hy : ‖py _ P‖ = 1) :
    ∃ Q : (shortW g2 g3).toAffine.Point, InSub (MaximalUnramifiedExtension l) Q ∧ InFormalGroupPoints (P - Q) := by
  have hI := good_int h
  have hC := good_coeff h
  obtain ⟨-, -, -, h4, h6, -⟩ := hI
  obtain ⟨-, -, -, m4, m6⟩ := hC
  have hl2 : l ≠ 2 := by have := h.five; omega
  cases P with
  | zero => exact absurd rfl hP0
  | some x y hns =>
    change ‖x‖ ≤ 1 at hx
    change ‖y‖ = 1 at hy
    obtain ⟨a, haT, hxa⟩ := res_full l x hx
    have haK : a ∈ MaximalUnramifiedExtension l := tch_mem_kur l haT
    have ha1 : ‖a‖ ≤ 1 := tch_norm_le l haT
    have hE : y ^ 2 = x ^ 3 + (shortW g2 g3).a₄ * x + (shortW g2 g3).a₆ := by
      have := (WeierstrassCurve.Affine.equation_iff _ _).1 hns.1
      simpa [shortW] using this
    set p := (shortW g2 g3).a₄ with hp
    set q := (shortW g2 g3).a₆ with hq
    have hc1 : ‖a ^ 3 + p * a + q‖ = 1 := by
      refine norm_one_of_close (d := y ^ 2) (by rw [norm_pow, hy, one_pow]) ?_
      rw [hE]
      exact cubic_close hx ha1 h4 hxa
    have hcK : a ^ 3 + p * a + q ∈ MaximalUnramifiedExtension l :=
      add_mem (add_mem (pow_mem haK 3) (mul_mem m4 haK)) m6
    obtain ⟨b, hbK, hb2, hb1⟩ := exists_sqrt l hl2 _ hcK hc1
    have hb0 : b ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hb1
      exact zero_ne_one hb1
    have hQns : (shortW g2 g3).toAffine.Nonsingular a b := by
      rw [WeierstrassCurve.Affine.nonsingular_iff]
      refine ⟨?_, Or.inr ?_⟩
      · rw [WeierstrassCurve.Affine.equation_iff]
        simp only [shortW] at hb2 hp hq ⊢
        rw [hb2, hp, hq]
        ring
      · simp only [shortW]
        intro hh
        apply hb0
        have h2 : (2 : ℂ_[l]) * b = 0 := by linear_combination hh
        rcases mul_eq_zero.1 h2 with h3 | h3
        · exact absurd h3 two_ne_zero
        · exact h3
    set P : (shortW g2 g3).toAffine.Point := .some x y hns with hPdef
    set Q : (shortW g2 g3).toAffine.Point := .some a b hQns with hQdef
    have hQS : InSub (MaximalUnramifiedExtension l) Q := ⟨haK, hbK⟩
    by_cases h1 : InFormalGroupPoints (P - Q)
    · exact ⟨Q, hQS, h1⟩
    by_cases h2 : InFormalGroupPoints (P + Q)
    · exact ⟨-Q, inSub_neg _ _ (good_coeff h) Q hQS, by rwa [sub_neg_eq_add]⟩
    exfalso
    obtain ⟨d0, dx, -⟩ := integral_of_not_mem_formalGroup h _ h1
    obtain ⟨s0, sx, -⟩ := integral_of_not_mem_formalGroup h _ h2
    have hu := Formalism.L2.Th1.E.UnitDiff_of Formalism.L2.Th1.E.nonsingular_norm ℂ_[l] (shortW g2 g3) (good_int h) P Q
      hP0 (WeierstrassCurve.Affine.Point.some_ne_zero _) s0 d0 hx hy.le ha1 hb1.le sx dx
    change ‖x - a‖ = 1 at hu
    exact absurd hu hxa.ne

end ReciprocityTheory.ChartRestriction.L1
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorTwo

section

@[expose] public section

noncomputable section
open scoped Classical

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM Formalism.ELL WeierstrassCurve
open Formalism.L2.Th1.E (px py IntCurve)
open Formalism.L2.Th1.A (shortW)

variable {l : ℕ} [Fact l.Prime] {g2 g3 : ℂ_[l]}

theorem cubic_coeff_ind (p : ℂ_[l] → Prop) (T : Cubic ℂ_[l]) (h0 : p 0) (ha : p T.a) (hb : p T.b)
    (hc : p T.c) (hd : p T.d) (i : ℕ) : p (T.toPoly.coeff i) := by
  rcases i with _ | _ | _ | _ | i
  · simpa [Cubic.coeff_eq_d] using hd
  · simpa [Cubic.coeff_eq_c] using hc
  · simpa [Cubic.coeff_eq_b] using hb
  · simpa [Cubic.coeff_eq_a] using ha
  · rw [Cubic.coeff_eq_zero (by omega)]
    exact h0

theorem tor_two (h : GoodPair l g2 g3) (P : (shortW g2 g3).toAffine.Point) (hP0 : P ≠ 0)
    (h2 : P + P = 0) : px _ P ∈ MaximalUnramifiedExtension l ∧ py _ P ∈ MaximalUnramifiedExtension l := by
  have hl2 : ¬ l ∣ 2 := fun hd => by
    have := Nat.le_of_dvd (by norm_num) hd
    have := h.five
    omega
  have hl4 : ¬ l ∣ 4 := fun hd => by
    have := Nat.le_of_dvd (by norm_num) hd
    have := h.five
    omega
  have hE : ¬ InFormalGroupPoints P := torsion_not_mem_formalGroup h P 2 hl2 (by rw [two_nsmul]; exact h2) hP0
  obtain ⟨-, hx, hy⟩ := integral_of_not_mem_formalGroup h P hE
  obtain ⟨hpsi, hkap⟩ :=
    Formalism.L2.Th1.E.UnitKap_of Formalism.L2.Th1.E.nonsingular_norm ℂ_[l] (shortW g2 g3) (good_int h) P hP0 h2 hx hy
  cases P with
  | zero => exact absurd rfl hP0
  | some x y hns =>
    change ‖x‖ ≤ 1 at hx
    change 2 * y + (shortW g2 g3).a₁ * x + (shortW g2 g3).a₃ = 0 at hpsi
    change ‖3 * x ^ 2 + 2 * (shortW g2 g3).a₂ * x + (shortW g2 g3).a₄ - (shortW g2 g3).a₁ * y‖ = 1 at hkap
    change x ∈ MaximalUnramifiedExtension l ∧ y ∈ MaximalUnramifiedExtension l
    have hy0 : y = 0 := by
      simp only [shortW, zero_mul, add_zero] at hpsi
      simpa using hpsi
    have heq := hns.1
    rw [WeierstrassCurve.Affine.equation_iff] at heq
    simp only [shortW] at heq hkap
    have n4 : ‖(4 : ℂ_[l])‖ = 1 := by exact_mod_cast norm_natCast_Cl_of_not_dvd (l := l) hl4
    have m4 : (4 : ℂ_[l]) ∈ MaximalUnramifiedExtension l := by exact_mod_cast natCast_mem (MaximalUnramifiedExtension l) 4
    refine ⟨?_, hy0 ▸ zero_mem _⟩
    refine hensel_mem l (Cubic.toPoly ⟨1, 0, -g2 / 4, -g3 / 4⟩) ?_ ?_ x hx ?_ ?_
    · exact cubic_coeff_ind (· ∈ MaximalUnramifiedExtension l) _ (zero_mem _) (one_mem _) (zero_mem _)
        (div_mem (neg_mem h.mem2) m4) (div_mem (neg_mem h.mem3) m4)
    · refine cubic_coeff_ind (‖·‖ ≤ 1) _ (by simp) (by simp) (by simp) ?_ ?_
      · simpa [norm_div, n4] using h.norm2
      · simpa [norm_div, n4] using h.norm3
    · simp only [Cubic.toPoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]
      rw [hy0] at heq
      linear_combination -heq
    · have : (Cubic.toPoly (⟨1, 0, -g2 / 4, -g3 / 4⟩ : Cubic ℂ_[l])).derivative.eval x
          = 3 * x ^ 2 + 2 * 0 * x + -g2 / 4 - 0 * y := by
        simp only [Cubic.toPoly, Polynomial.derivative_add, Polynomial.derivative_mul,
          Polynomial.derivative_C, Polynomial.derivative_X_pow, Polynomial.derivative_X,
          Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
          Polynomial.eval_X, Polynomial.eval_zero, Polynomial.eval_one, Polynomial.eval_natCast,
          map_natCast]
        push_cast
        ring
      rw [this]
      exact hkap

end ReciprocityTheory.ChartRestriction.L1
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorMain

section

@[expose] public section

noncomputable section
open scoped Classical

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM Formalism.ELL WeierstrassCurve
open Formalism.L2.Th1.E (px py IntCurve)
open Formalism.L2.Th1.A (shortW)

variable {l : ℕ} [Fact l.Prime] {g2 g3 : ℂ_[l]}

theorem tor_nsmul_fix {A : Type*} [AddGroup A] (P : A) (N n : ℕ) (hNP : N • P = 0)
    (hn : n ≡ 1 [MOD N]) : n • P = P := by
  have h1 : n ≡ 1 [MOD addOrderOf P] := hn.of_dvd (addOrderOf_dvd_of_nsmul_eq_zero hNP)
  have h2 := nsmul_eq_nsmul_iff_modEq.mpr h1
  simpa using h2

theorem tor_norm_mult_lt (N : ℕ) (hN0 : 0 < N) : ‖((l ^ N.totient : ℕ) : ℂ_[l])‖ < 1 := by
  have hl : ‖(l : ℂ_[l])‖ < 1 := by
    rw [norm_l_Cl]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  rw [Nat.cast_pow, norm_pow]
  exact pow_lt_one₀ (norm_nonneg _) hl (Nat.totient_pos.mpr hN0).ne'

theorem tor_x_step (h : GoodPair l g2 g3) (P Q : (shortW g2 g3).toAffine.Point) (N : ℕ)
    (hN : ¬ l ∣ N) (hNP : N • P = 0) (h2 : P + P ≠ 0) (hD : InFormalGroupPoints (P - Q)) (n : ℕ)
    (hn : n ≡ 1 [MOD N]) : ‖px _ P - px _ (n • Q)‖ ≤ ‖uOf (n • (P - Q))‖ := by
  obtain ⟨hW, hΔ⟩ := good_model h
  have hP0 : P ≠ 0 := by
    rintro rfl
    exact h2 (by simp)
  have hfix : n • P = P := tor_nsmul_fix P N n hNP hn
  have hsub : P - n • Q = n • (P - Q) := by
    rw [nsmul_sub, hfix]
  have hB : n • Q = P - n • (P - Q) := by
    rw [← hsub]; abel
  have hE : InFormalGroupPoints (n • (P - Q)) := (formalGroup_nsmul_estimate _ hW hΔ _ hD n).1
  by_cases h0 : n • (P - Q) = 0
  · have : n • Q = P := by rw [hB, h0, sub_zero]
    rw [this, sub_self, norm_zero]
    exact norm_nonneg _
  have hPE : ¬ InFormalGroupPoints P := torsion_not_mem_formalGroup h P N hN hNP hP0
  have hBE : ¬ InFormalGroupPoints (n • Q) := by
    rw [hB]; exact not_mem_formalGroup_sub h P _ hPE hE
  have h2E : ¬ InFormalGroupPoints (P + P) :=
    torsion_not_mem_formalGroup h (P + P) N hN (by rw [nsmul_add, hNP, add_zero]) h2
  have hS : P + n • Q = (P + P) - n • (P - Q) := by
    rw [hB]; abel
  have hSE : ¬ InFormalGroupPoints (P + n • Q) := by
    rw [hS]; exact not_mem_formalGroup_sub h _ _ h2E hE
  obtain ⟨_, _, hPy⟩ := integral_of_not_mem_formalGroup h P hPE
  obtain ⟨hB0, _, hBy⟩ := integral_of_not_mem_formalGroup h _ hBE
  obtain ⟨hS0, hSx, _⟩ := integral_of_not_mem_formalGroup h _ hSE
  have := norm_x_sub_le_of_formalGroup (shortW g2 g3) rfl rfl rfl hW P (n • Q) hP0 hB0 hPy hBy hS0 hSx
    (by rw [hsub]; exact h0) (by rw [hsub]; exact hE)
  rwa [hsub] at this

theorem tor_x_mem (h : GoodPair l g2 g3) (P : (shortW g2 g3).toAffine.Point) (N : ℕ) (hN0 : 0 < N)
    (hN : ¬ l ∣ N) (hNP : N • P = 0) (h2 : P + P ≠ 0) : px _ P ∈ MaximalUnramifiedExtension l := by
  obtain ⟨hW, hΔ⟩ := good_model h
  have hP0 : P ≠ 0 := by
    rintro rfl
    exact h2 (by simp)
  have hPE : ¬ InFormalGroupPoints P := torsion_not_mem_formalGroup h P N hN hNP hP0
  obtain ⟨_, hPx, _⟩ := integral_of_not_mem_formalGroup h P hPE
  obtain ⟨Q, hQ, hD⟩ := tor_lift h P hP0 hPx (tor_y_unit h P N hN hNP h2)
  have hcop : Nat.Coprime l N := ((Fact.out : l.Prime).coprime_iff_not_dvd).mpr hN
  have hM : ∀ k : ℕ, (l ^ N.totient) ^ k ≡ 1 [MOD N] := fun k => by
    simpa using (Nat.ModEq.pow_totient hcop).pow k
  have ht := formalGroup_pow_tendsto_zero _ hW hΔ _ hD (l ^ N.totient) (tor_norm_mult_lt N hN0)
  have hlim : Filter.Tendsto (fun k : ℕ => px _ ((l ^ N.totient) ^ k • Q)) Filter.atTop
      (nhds (px _ P)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) ht
    rw [norm_sub_rev]
    exact tor_x_step h P Q N hN hNP h2 hD _ (hM k)
  have hcl : IsClosed ((MaximalUnramifiedExtension l : Subfield ℂ_[l]) : Set ℂ_[l]) :=
    Subfield.isClosed_topologicalClosure _
  refine hcl.mem_of_tendsto hlim (Filter.Eventually.of_forall fun k => ?_)
  exact (inSub_px _ _ _ (inSub_nsmul _ _ (good_coeff h) _ Q hQ)).1

theorem tor_kur (h : GoodPair l g2 g3) (P : (shortW g2 g3).toAffine.Point) (N : ℕ) (hN0 : 0 < N)
    (hN : ¬ l ∣ N) (hNP : N • P = 0) (hP0 : P ≠ 0) : px _ P ∈ MaximalUnramifiedExtension l ∧ py _ P ∈ MaximalUnramifiedExtension l := by
  by_cases h2 : P + P = 0
  · exact tor_two h P hP0 h2
  have hx := tor_x_mem h P N hN0 hN hNP h2
  have hy := tor_y_unit h P N hN hNP h2
  refine ⟨hx, ?_⟩
  have hl : l ≠ 2 := by have := h.five; omega
  have heq : (py _ P) ^ 2 = (px _ P) ^ 3 - g2 / 4 * px _ P - g3 / 4 := by
    match P, hP0 with
    | .zero, hP0 => exact absurd rfl hP0
    | .some x y hxy, _ =>
      have := (Affine.equation_iff _ _).mp hxy.1
      simp only [shortW, px, py] at this ⊢
      linear_combination this
  have h4 : (4 : ℂ_[l]) ∈ MaximalUnramifiedExtension l := by exact_mod_cast natCast_mem (MaximalUnramifiedExtension l) 4
  refine sqrt_mem l hl _ _ ?_ hy heq
  exact sub_mem (sub_mem (pow_mem hx 3) (mul_mem (div_mem h.mem2 h4) hx)) (div_mem h.mem3 h4)

end ReciprocityTheory.ChartRestriction.L1
end
end
end
