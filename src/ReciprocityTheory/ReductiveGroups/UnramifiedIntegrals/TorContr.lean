module

public import Formalism.EllipticTorsion.FormalGroupPointsParametrisation
public import Formalism.EllipticTorsion.FormalGroupPointsNoTorsion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Ring.Ultra
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.EllipticTorsion.EllipticTorsionProofs.FormalGroupPointsHomDef
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.IsTransSys
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementK

-- Source module: ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorChord

section

@[expose] public section

noncomputable section
open scoped Classical

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM Formalism.ELL WeierstrassCurve
open Formalism.L2.Th1.E (px py IntCurve)
open Formalism.L2.Th1.A (shortW)

variable {C : Type} [NormedField C] [IsUltrametricDist C]

theorem chord_norm_add {a b : C} (h : ‖b‖ < ‖a‖) : ‖a + b‖ = ‖a‖ := by
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne', max_eq_left h.le]

theorem chord_norm_y_sq (W : WeierstrassCurve C) (hW : IntegralModel W) {x y : C}
    (h : W.toAffine.Equation x y) (hx : 1 < ‖x‖) : ‖y‖ ^ 2 = ‖x‖ ^ 3 := by
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  rw [Affine.equation_iff] at h
  have hx0 : 0 < ‖x‖ := lt_trans one_pos hx
  have e2 : ‖W.a₂ * x ^ 2‖ < ‖x ^ 3‖ := by
    rw [norm_mul, norm_pow, norm_pow]
    calc ‖W.a₂‖ * ‖x‖ ^ 2 ≤ 1 * ‖x‖ ^ 2 := by gcongr
      _ < ‖x‖ ^ 3 := by nlinarith [pow_pos hx0 2]
  have e4 : ‖W.a₄ * x‖ < ‖x ^ 3‖ := by
    rw [norm_mul, norm_pow]
    calc ‖W.a₄‖ * ‖x‖ ≤ 1 * ‖x‖ := by gcongr
      _ < ‖x‖ ^ 3 := by nlinarith [pow_pos hx0 2, mul_pos hx0 hx0]
  have e6 : ‖W.a₆‖ < ‖x ^ 3‖ := by
    rw [norm_pow]
    calc ‖W.a₆‖ ≤ 1 := h6
      _ < ‖x‖ ^ 3 := one_lt_pow₀ hx (by norm_num)
  have hR : ‖x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆‖ = ‖x‖ ^ 3 := by
    have s1 := chord_norm_add e2
    have s2 : ‖x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x‖ = ‖x ^ 3‖ := by
      rw [chord_norm_add (by rw [s1]; exact e4), s1]
    rw [chord_norm_add (by rw [s2]; exact e6), s2, norm_pow]
  have hL : y ^ 2 + W.a₁ * x * y + W.a₃ * y = y * (y + (W.a₁ * x + W.a₃)) := by ring
  rw [← h, hL, norm_mul] at hR
  have hc : ‖W.a₁ * x + W.a₃‖ ≤ ‖x‖ := by
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (h3.trans hx.le))
    rw [norm_mul]
    calc ‖W.a₁‖ * ‖x‖ ≤ 1 * ‖x‖ := by gcongr
      _ = ‖x‖ := one_mul _
  have hyx : ‖x‖ < ‖y‖ := by
    by_contra hcon
    rw [not_lt] at hcon
    have hs : ‖y + (W.a₁ * x + W.a₃)‖ ≤ ‖x‖ :=
      (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hcon hc)
    have : ‖y‖ * ‖y + (W.a₁ * x + W.a₃)‖ ≤ ‖x‖ * ‖x‖ :=
      mul_le_mul hcon hs (norm_nonneg _) hx0.le
    nlinarith [mul_pos hx0 hx0]
  rw [chord_norm_add (lt_of_le_of_lt hc hyx)] at hR
  rw [← hR]; ring

theorem chord_norm_u_sq (W : WeierstrassCurve C) (hW : IntegralModel W) {x y : C}
    (h : W.toAffine.Equation x y) (hx : 1 < ‖x‖) : ‖-x / y‖ ^ 2 * ‖x‖ = 1 := by
  have hy := chord_norm_y_sq W hW h hx
  have hx0 : 0 < ‖x‖ := by linarith
  have hx0' := hx0.ne'
  rw [norm_div, norm_neg, div_pow, hy]
  field_simp

theorem formalGroup_param_norm_lt_one (W : WeierstrassCurve C) (hW : IntegralModel W) (P : W.toAffine.Point) (hP : InFormalGroupPoints P) :
    ‖uOf P‖ < 1 := by
  rcases P with _ | @⟨x, y, h⟩
  · simp [uOf]
  · have hx : 1 < ‖x‖ := hP
    have hu := chord_norm_u_sq W hW h.1 hx
    show ‖-x / y‖ < 1
    by_contra hcon
    rw [not_lt] at hcon
    have : 1 ≤ ‖-x / y‖ ^ 2 := one_le_pow₀ hcon
    nlinarith

theorem chord_adjoin_le (W : WeierstrassCurve C) (hW : IntegralModel W) {c : C}
    (hc : c ∈ Algebra.adjoin ℤ ({W.a₁, W.a₂, W.a₃, W.a₄, W.a₆} : Set C)) : ‖c‖ ≤ 1 := by
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  induction hc using Algebra.adjoin_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
  | algebraMap n =>
    rw [eq_intCast]
    exact IsUltrametricDist.norm_intCast_le_one C n
  | add x y _ _ hx hy =>
    exact (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)
  | mul x y _ _ hx hy =>
    rw [norm_mul]
    exact mul_le_one₀ hx (norm_nonneg _) hy

theorem chord_eval_est [CompleteSpace C] {F : MvPowerSeries (Fin 2) C} (hF : Formalism.G.IntegralMv F)
    (h00 : MvPowerSeries.constantCoeff F = 0)
    (h10 : MvPowerSeries.coeff (Finsupp.single 0 1) F = 1)
    (h01 : MvPowerSeries.coeff (Finsupp.single 1 1) F = 1) {a b : C} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    ‖evalMv2 F a b - a - b‖ ≤ (max ‖a‖ ‖b‖) ^ 2 := by
  set r := max ‖a‖ ‖b‖ with hr
  have hr0 : 0 ≤ r := le_trans (norm_nonneg a) (le_max_left _ _)
  have hr1 : r < 1 := max_lt ha hb
  set G : MvPowerSeries (Fin 2) C := F - MvPowerSeries.X 0 - MvPowerSeries.X 1 with hG
  have hI1 : Formalism.G.IntegralMv (F - MvPowerSeries.X 0) :=
    (FormalGroupPointsHom.IL C).sub_mem hF (FormalGroupPointsHom.integral_X 0)
  have hIG : Formalism.G.IntegralMv G := (FormalGroupPointsHom.IL C).sub_mem hI1 (FormalGroupPointsHom.integral_X 1)
  have hev : evalMv2 G a b = evalMv2 F a b - a - b := by
    rw [hG, FormalGroupPointsHom.evalMv2_sub hI1 (FormalGroupPointsHom.integral_X 1) ha hb,
      FormalGroupPointsHom.evalMv2_sub hF (FormalGroupPointsHom.integral_X 0) ha hb, FormalGroupPointsHom.evalMv2_X0,
      FormalGroupPointsHom.evalMv2_X1]
  rw [← hev, FormalGroupPointsHom.evalMv2_eq]
  apply IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (pow_nonneg hr0 2)
  intro d
  by_cases hd : 2 ≤ d.degree
  · exact (FormalGroupPointsHom.norm_term_le hIG (le_max_left _ _) (le_max_right _ _) d).trans
      (pow_le_pow_of_le_one hr0 hr1.le hd)
  · have hz : MvPowerSeries.coeff d G = 0 := by
      rw [FormalGroupPointsHom.degree_fin_two_eq_add_of_ne] at hd
      have hcases : d = 0 ∨ d = Finsupp.single 0 1 ∨ d = Finsupp.single 1 1 := by
        have h3 : (d 0 = 0 ∧ d 1 = 0) ∨ (d 0 = 1 ∧ d 1 = 0) ∨ (d 0 = 0 ∧ d 1 = 1) := by omega
        rcases h3 with ⟨u, v⟩ | ⟨u, v⟩ | ⟨u, v⟩
        · left; ext i; fin_cases i <;> simp [u, v]
        · right; left; ext i; fin_cases i <;> simp [u, v]
        · right; right; ext i; fin_cases i <;> simp [u, v]
      have hne : (Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 := by
        intro he
        have := DFunLike.congr_fun he 0
        simp at this
      rcases hcases with rfl | rfl | rfl
      · rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hG]
        simp [h00]
      · rw [hG, map_sub, map_sub, h10, MvPowerSeries.coeff_X, MvPowerSeries.coeff_X, if_pos rfl,
          if_neg hne]
        ring
      · rw [hG, map_sub, map_sub, h01, MvPowerSeries.coeff_X, MvPowerSeries.coeff_X, if_pos rfl,
          if_neg hne.symm]
        ring
    rw [FormalGroupPointsHom.term, hz, zero_mul, norm_zero]
    exact pow_nonneg hr0 2

theorem formalGroup_add_estimate [CompleteSpace C] (W : WeierstrassCurve C) (hW : IntegralModel W)
    (P Q : W.toAffine.Point) (hP : InFormalGroupPoints P) (hQ : InFormalGroupPoints Q) :
    ‖uOf (P + Q) - uOf P - uOf Q‖ ≤ (max ‖uOf P‖ ‖uOf Q‖) ^ 2 := by
  obtain ⟨w, hw, -⟩ := wSeriesUnique.{0} C W
  obtain ⟨F, hFc, hch⟩ := wFormalGroup.{0} C W w hw
  have hF : Formalism.G.IntegralMv F.toPowerSeries := fun d => chord_adjoin_le W hW (hFc d)
  have hadd : uOf (P + Q) = evalMv2 F.toPowerSeries (uOf P) (uOf Q) :=
    FormalGroupPointsHom.e1hom_main wSubstUnique wChordSubst formal_group_points_param
      hW hw F hF hch P Q hP hQ
  rw [hadd]
  exact chord_eval_est hF F.zero_constantCoeff F.lin_coeff_X F.lin_coeff_Y
    (formalGroup_param_norm_lt_one W hW P hP) (formalGroup_param_norm_lt_one W hW Q hQ)

end ReciprocityTheory.ChartRestriction.L1
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorContr

section

@[expose] public section

noncomputable section
open scoped Classical

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM Formalism.ELL WeierstrassCurve
open Formalism.L2.Th1.E (px py IntCurve)
open Formalism.L2.Th1.A (shortW)

variable {C : Type} [NormedField C] [IsUltrametricDist C] [CompleteSpace C]

theorem formalGroup_nsmul_estimate (W : WeierstrassCurve C) (hW : IntegralModel W) (hΔ : ‖W.Δ‖ = 1)
    (D : W.toAffine.Point) (hD : InFormalGroupPoints D) (n : ℕ) :
    InFormalGroupPoints (n • D) ∧ ‖uOf (n • D) - (n : C) * uOf D‖ ≤ ‖uOf D‖ ^ 2 := by
  have hu : ‖uOf D‖ < 1 := formalGroup_param_norm_lt_one W hW D hD
  have hsq : ‖uOf D‖ ^ 2 ≤ ‖uOf D‖ := by
    have h0 := norm_nonneg (uOf D)
    nlinarith
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [zero_smul]; exact (trivial : InFormalGroupPoints (Affine.Point.zero : W.toAffine.Point))
    · rw [zero_smul]
      have : uOf (0 : W.toAffine.Point) = 0 := rfl
      rw [this]; simp
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    have hin : InFormalGroupPoints (n • D + D) := (formal_group_points_subgroup C W hW hΔ (n • D) D h1 hD).1
    have hn : ‖(n : C)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one C n
    have hnu : ‖(n : C) * uOf D‖ ≤ ‖uOf D‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) hn
    have hb : ‖uOf (n • D)‖ ≤ ‖uOf D‖ := by
      have e : uOf (n • D) = (uOf (n • D) - (n : C) * uOf D) + (n : C) * uOf D := by ring
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h2.trans hsq) hnu)
    have hadd := formalGroup_add_estimate W hW (n • D) D h1 hD
    rw [max_eq_right hb] at hadd
    rw [succ_nsmul]
    refine ⟨hin, ?_⟩
    have e : uOf (n • D + D) - ((n + 1 : ℕ) : C) * uOf D
        = (uOf (n • D + D) - uOf (n • D) - uOf D) + (uOf (n • D) - (n : C) * uOf D) := by
      push_cast; ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hadd h2)

theorem formalGroup_pow_tendsto_zero (W : WeierstrassCurve C) (hW : IntegralModel W) (hΔ : ‖W.Δ‖ = 1)
    (D : W.toAffine.Point) (hD : InFormalGroupPoints D) (M : ℕ) (hM : ‖(M : C)‖ < 1) :
    Filter.Tendsto (fun k : ℕ => ‖uOf (M ^ k • D)‖) Filter.atTop (nhds 0) := by
  have hu : ‖uOf D‖ < 1 := formalGroup_param_norm_lt_one W hW D hD
  set c : ℝ := max ‖(M : C)‖ ‖uOf D‖ with hc
  have hc0 : 0 ≤ c := le_max_of_le_left (norm_nonneg _)
  have hc1 : c < 1 := max_lt hM hu
  have key : ∀ k : ℕ, ‖uOf (M ^ k • D)‖ ≤ c ^ k * ‖uOf D‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hk : InFormalGroupPoints (M ^ k • D) := (formalGroup_nsmul_estimate W hW hΔ D hD (M ^ k)).1
      have hest := (formalGroup_nsmul_estimate W hW hΔ (M ^ k • D) hk M).2
      have hle : ‖uOf (M ^ k • D)‖ ≤ ‖uOf D‖ :=
        ih.trans (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hc0 hc1.le))
      have hr0 := norm_nonneg (uOf (M ^ k • D))
      have e0 : M ^ (k + 1) • D = M • (M ^ k • D) := by
        rw [smul_smul, pow_succ, mul_comm]
      have h1 : ‖uOf (M • (M ^ k • D))‖ ≤ c * ‖uOf (M ^ k • D)‖ := by
        have e : uOf (M • (M ^ k • D)) = (uOf (M • (M ^ k • D)) - (M : C) * uOf (M ^ k • D))
            + (M : C) * uOf (M ^ k • D) := by ring
        rw [e]
        refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hest.trans ?_) ?_)
        · rw [sq]
          exact mul_le_mul_of_nonneg_right (hle.trans (le_max_right _ _)) hr0
        · rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) hr0
      rw [e0, pow_succ, mul_comm (c ^ k) c, mul_assoc]
      exact h1.trans (mul_le_mul_of_nonneg_left ih hc0)
  have hlim : Filter.Tendsto (fun k : ℕ => c ^ k * ‖uOf D‖) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).mul_const ‖uOf D‖
  exact squeeze_zero (fun _ => norm_nonneg _) key hlim

end ReciprocityTheory.ChartRestriction.L1
end
end
end
