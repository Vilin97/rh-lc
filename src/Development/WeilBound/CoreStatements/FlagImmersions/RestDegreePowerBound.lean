module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import Development.WeilBound.CoreStatements.FlagImmersions.CoeffShift
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagDegreeWeightFormulaStatement
public import Development.WeilBound.CoreStatements.FlagImmersions.AltEqZero
public import Development.WeilBound.CoreStatements.FlagImmersions.RrCoeffSucc
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.WeilBound.CoreStatements.FlagImmersions.SumChooseLe

section

@[expose] public section

noncomputable section

open Polynomial

namespace RootFieldNumerics.M5

variable {N : ℕ}

theorem gdet_rho (N : ℕ) : ∃ c : ℝ, ∀ v : Fin N → Polynomial ℝ,
    gdet (fun c' : Fin N => N - 1 - (c' : ℕ)) v = Polynomial.C c * ∏ a, ∏ b ∈ Finset.Ioi a, (v b - v a) := by
  refine ⟨(∏ c : Fin N, (((N - 1 - (c : ℕ)).factorial : ℕ) : ℝ)⁻¹) *
    (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin N)) : ℤ) : ℝ)), fun v => ?_⟩
  have hM : (Matrix.of fun (c b : Fin N) => C ((((N - 1 - (c : ℕ)).factorial : ℕ) : ℝ))⁻¹ * v b ^ (N - 1 - (c : ℕ)))
      = Matrix.of fun (c b : Fin N) => C ((((N - 1 - (c : ℕ)).factorial : ℕ) : ℝ))⁻¹ *
        ((Matrix.vandermonde v).transpose.submatrix Fin.revPerm id) c b := by
    ext c b
    simp only [Matrix.of_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.vandermonde_apply,
      Fin.revPerm_apply, Fin.val_rev, id]
    rw [show N - ((c : ℕ) + 1) = N - 1 - (c : ℕ) by omega]
  unfold gdet
  rw [hM, Matrix.det_mul_column, Matrix.det_permute, Matrix.det_transpose, Matrix.det_vandermonde]
  simp only [map_mul, map_prod, map_intCast]
  ring

theorem sum_choose_le (M n : ℕ) : ∑ i ∈ Finset.range M, n.choose i ≤ 2 ^ n := by
  rw [← Nat.sum_range_choose]
  apply Finset.sum_le_sum_of_ne_zero
  intro i _ hi
  rw [Finset.mem_range]
  by_contra h
  exact hi (Nat.choose_eq_zero_of_lt (by omega))

theorem pow_eq_sum_rr (w : ℕ → Polynomial ℝ) (m a : ℕ) (ha : a < N) :
    w a ^ m = ∑ c : Fin N, (rr w m N).coeff (N - 1 - (c : ℕ)) * w a ^ (N - 1 - (c : ℕ)) := by
  have hd : (rr w m N).natDegree < N := by
    have : (rr w m N).natDegree ≤ N - 1 :=
      natDegree_le_iff_coeff_eq_zero.mpr fun n hn => rr_coeff_big w m N n (by omega)
    omega
  rw [← rr_eval w m N a ha, eval_eq_sum_range' hd, ← Finset.sum_range_reflect,
    ← Fin.sum_univ_eq_sum_range (fun i => (rr w m N).coeff (N - 1 - i) * w a ^ (N - 1 - i))]

theorem gdet_bump (k : ℕ) (hk : 1 ≤ k) (U : ℝ) (hU : 0 < U) (v : Fin N → Polynomial ℝ)
    (hv : ∀ b, Maj (v b) U (1 / U)) :
    ∃ r : Polynomial ℝ, Maj r (2 ^ (k - 1) / (k.factorial : ℝ) * U ^ k) (k / U) ∧
      ∑ c : Fin N, gdet (fun c' : Fin N => N - 1 - (c' : ℕ) + if c' = c then k else 0) v =
        r * gdet (fun c' : Fin N => N - 1 - (c' : ℕ)) v := by
  classical
  set w : ℕ → Polynomial ℝ := fun a => if h : a < N then v ⟨a, h⟩ else 0 with hw
  have hwv : ∀ b : Fin N, w b = v b := fun b => by simp [hw, b.isLt]
  have hwM : ∀ a, Maj (w a) U (1 / U) := by
    intro a
    by_cases h : a < N
    · simp only [hw, dif_pos h]
      exact hv _
    · simp only [hw, dif_neg h]
      exact Maj.zero hU.le (by positivity)
  refine ⟨∑ c : Fin N, C ((((N - 1 - (c : ℕ) + k).factorial : ℕ) : ℝ)⁻¹ * (((N - 1 - (c : ℕ)).factorial : ℕ) : ℝ)) *
      (rr w (N - 1 - (c : ℕ) + k) N).coeff (N - 1 - (c : ℕ)), ?_, ?_⟩
  · have hk0 : (0 : ℝ) ≤ k / U := by positivity
    have h1 := Maj.sum Finset.univ
      (fun c : Fin N => C ((((N - 1 - (c : ℕ) + k).factorial : ℕ) : ℝ)⁻¹ * (((N - 1 - (c : ℕ)).factorial : ℕ) : ℝ)) *
        (rr w (N - 1 - (c : ℕ) + k) N).coeff (N - 1 - (c : ℕ)))
      (fun c : Fin N => ((((N - 1 - (c : ℕ) + k).factorial : ℕ) : ℝ)⁻¹ * (((N - 1 - (c : ℕ)).factorial : ℕ) : ℝ)) *
        ((cnt (N - 1 - (c : ℕ)) k N : ℝ) * U ^ k)) hk0
      (fun c _ => (rr_maj U hU w hwM _ _ k N rfl).C_mul _ (by positivity))
    apply h1.mono hk0 _ le_rfl
    have hterm : ∀ c : Fin N, ((((N - 1 - (c : ℕ) + k).factorial : ℕ) : ℝ)⁻¹ * (((N - 1 - (c : ℕ)).factorial : ℕ) : ℝ)) *
        ((cnt (N - 1 - (c : ℕ)) k N : ℝ) * U ^ k) = ((k - 1).choose (c : ℕ) : ℝ) / (k.factorial : ℝ) * U ^ k := by
      intro c
      have hc : N - 1 - (c : ℕ) < N := by omega
      have hk1 : k ≠ 0 := by omega
      simp only [cnt, if_pos hc, if_neg hk1]
      rw [show N - 1 - (N - 1 - (c : ℕ)) = (c : ℕ) by omega]
      have hf := Nat.add_choose_mul_factorial_mul_factorial k (N - 1 - (c : ℕ))
      rw [add_comm k] at hf
      have hf' : (((N - 1 - (c : ℕ) + k).choose (N - 1 - (c : ℕ)) : ℕ) : ℝ) * (k.factorial : ℝ) *
          ((N - 1 - (c : ℕ)).factorial : ℝ) = ((N - 1 - (c : ℕ) + k).factorial : ℝ) := by
        exact_mod_cast hf
      push_cast
      rw [← hf']
      have h2 : (k.factorial : ℝ) ≠ 0 := by positivity
      have h3 : ((N - 1 - (c : ℕ)).factorial : ℝ) ≠ 0 := by positivity
      have h4 : (((N - 1 - (c : ℕ) + k).choose (N - 1 - (c : ℕ)) : ℕ) : ℝ) ≠ 0 := by
        have := Nat.choose_pos (show N - 1 - (c : ℕ) ≤ N - 1 - (c : ℕ) + k by omega)
        positivity
      field_simp
    rw [Finset.sum_congr rfl (fun c _ => hterm c), ← Finset.sum_mul, ← Finset.sum_div]
    have hs : (∑ c : Fin N, ((k - 1).choose (c : ℕ) : ℝ)) ≤ 2 ^ (k - 1) := by
      have := sum_choose_le N (k - 1)
      rw [← Fin.sum_univ_eq_sum_range (fun i => (k - 1).choose i) N] at this
      exact_mod_cast this
    gcongr
  · rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    simp only [gdet]
    set A : Matrix (Fin N) (Fin N) (Polynomial ℝ) := Matrix.of fun (c' b : Fin N) =>
      C ((((N - 1 - (c' : ℕ)).factorial : ℕ) : ℝ))⁻¹ * v b ^ (N - 1 - (c' : ℕ)) with hA
    have hrow : (Matrix.of fun (c' b : Fin N) =>
        C ((((N - 1 - (c' : ℕ) + if c' = c then k else 0).factorial : ℕ) : ℝ))⁻¹ *
          v b ^ (N - 1 - (c' : ℕ) + if c' = c then k else 0))
        = A.updateRow c (∑ c' : Fin N,
          (C ((((N - 1 - (c : ℕ) + k).factorial : ℕ) : ℝ)⁻¹ * (((N - 1 - (c' : ℕ)).factorial : ℕ) : ℝ)) *
            (rr w (N - 1 - (c : ℕ) + k) N).coeff (N - 1 - (c' : ℕ))) • A c') := by
      refine Matrix.ext fun i b => ?_
      rw [Matrix.updateRow_apply]
      by_cases hi : i = c
      · subst hi
        simp only [if_pos rfl, if_true, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hA]
        rw [← hwv b, pow_eq_sum_rr w _ b b.isLt, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun c' _ => ?_)
        have hP : C ((((N - 1 - (c' : ℕ)).factorial : ℕ) : ℝ)) * C ((((N - 1 - (c' : ℕ)).factorial : ℕ) : ℝ))⁻¹
            = (1 : Polynomial ℝ) := by
          rw [← map_mul, mul_inv_cancel₀ (by positivity), map_one]
        rw [map_mul]
        linear_combination (-(C ((((N - 1 - (i : ℕ) + k).factorial : ℕ) : ℝ))⁻¹ *
          (rr w (N - 1 - (i : ℕ) + k) N).coeff (N - 1 - (c' : ℕ)) * w b ^ (N - 1 - (c' : ℕ)))) * hP
      · simp only [if_neg hi, Matrix.of_apply, hA, add_zero]
    rw [hrow, Matrix.det_updateRow_sum, smul_eq_mul]

end RootFieldNumerics.M5
end
end
end

-- Source module: Development.WeilBound.CoreStatements.FlagImmersions.RestDegreePowerBound

section

@[expose] public section

noncomputable section

namespace RootFieldNumerics.M5

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Top

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

theorem maj_lin (r e c A : ℝ) (hA : 0 ≤ A) (hr : |r| ≤ c) (he : |e| ≤ c * A) :
    Maj (Polynomial.C r + Polynomial.C e * Polynomial.X) c A := by
  have hc : 0 ≤ c := (abs_nonneg r).trans hr
  intro s
  rcases s with _ | _ | s
  · simpa using hr
  · simpa using he
  · have : (Polynomial.C r + Polynomial.C e * Polynomial.X).coeff (s + 1 + 1) = 0 := by
      simp [Polynomial.coeff_X, Polynomial.coeff_C]
    rw [this, abs_zero]
    positivity

theorem maj_C (r : ℝ) : Maj (Polynomial.C r) |r| 0 := by
  simpa using maj_lin r 0 |r| 0 le_rfl le_rfl (by simp)

theorem maj_rho (u : Wt Ψ N) (τ' : Ψ) (i : Fin N) (g : ℝ) (hg : 0 < g)
    (hsep : ∀ b, i ≠ b → g ≤ |u τ' i - u τ' b|) :
    Maj (∏ τ, gdet (rho τ) (vv u (τ', i) τ)) |(∏ τ, gdet (rho τ) (vv u (τ', i) τ)).coeff 0| (N / g) := by
  obtain ⟨c, hc⟩ := gdet_rho N
  have hP : (∏ τ, gdet (rho τ) (vv u (τ', i) τ)) =
      ∏ τ, (Polynomial.C c * ∏ a, ∏ b ∈ Finset.Ioi a, (vv u (τ', i) τ b - vv u (τ', i) τ a)) :=
    Finset.prod_congr rfl fun τ _ => hc _
  have h0 : |(∏ τ, gdet (rho τ) (vv u (τ', i) τ)).coeff 0| =
      ∏ τ, (|c| * ∏ a, ∏ b ∈ Finset.Ioi a, |u τ b - u τ a|) := by
    rw [hP, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod, Finset.abs_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, abs_mul, Polynomial.eval_prod, Finset.abs_prod]
    congr 1
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [Polynomial.eval_prod, Finset.abs_prod]
    refine Finset.prod_congr rfl fun b _ => ?_
    congr 1
    simp only [vv, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_C]
    split_ifs <;> simp
  let w : Ψ → Fin N → ℝ := fun τ a => if (τ, a) = (τ', i) then 1 / g else 0
  have hw : ∀ τ a, 0 ≤ w τ a := fun τ a => by
    simp only [w]; split_ifs <;> positivity
  have hfac : ∀ τ a, ∀ b ∈ Finset.Ioi a,
      Maj (vv u (τ', i) τ b - vv u (τ', i) τ a) |u τ b - u τ a| (w τ a + w τ b) := by
    intro τ a b hb
    have hab : a < b := Finset.mem_Ioi.mp hb
    have hA := add_nonneg (hw τ a) (hw τ b)
    by_cases ha : (τ, a) = (τ', i)
    · have hb' : (τ, b) ≠ (τ', i) := fun h => hab.ne (by rw [← h] at ha; exact (Prod.mk.inj ha).2)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj ha
      have : vv u (τ, a) τ b - vv u (τ, a) τ a =
          Polynomial.C (u τ b - u τ a) + Polynomial.C (-1) * Polynomial.X := by
        simp only [vv, if_neg hb', if_true, map_sub, map_neg, map_one]; ring
      rw [this]
      refine maj_lin _ _ _ _ hA le_rfl ?_
      have h1 := hsep b hab.ne
      simp only [w, if_neg hb', if_true, add_zero, abs_neg, abs_one]
      rw [abs_sub_comm, mul_one_div, one_le_div hg]
      exact h1
    · by_cases hb' : (τ, b) = (τ', i)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hb'
        have : vv u (τ, b) τ b - vv u (τ, b) τ a =
            Polynomial.C (u τ b - u τ a) + Polynomial.C 1 * Polynomial.X := by
          simp only [vv, if_neg ha, if_true, map_sub, map_one]; ring
        rw [this]
        refine maj_lin _ _ _ _ hA le_rfl ?_
        have h1 := hsep a hab.ne'
        simp only [w, if_neg ha, if_true, zero_add, abs_one]
        rw [mul_one_div, one_le_div hg]
        exact h1
      · have : vv u (τ', i) τ b - vv u (τ', i) τ a =
            Polynomial.C (u τ b - u τ a) + Polynomial.C 0 * Polynomial.X := by
          simp only [vv, if_neg ha, if_neg hb', map_sub, map_zero]; ring
        rw [this]
        refine maj_lin _ _ _ _ hA le_rfl ?_
        rw [abs_zero]
        exact mul_nonneg (abs_nonneg _) hA
  have hin : ∀ τ a, 0 ≤ ∑ b ∈ Finset.Ioi a, (w τ a + w τ b) := fun τ a =>
    Finset.sum_nonneg fun b _ => add_nonneg (hw τ a) (hw τ b)
  have hM := Maj.prod Finset.univ
    (fun τ => Polynomial.C c * ∏ a, ∏ b ∈ Finset.Ioi a, (vv u (τ', i) τ b - vv u (τ', i) τ a))
    (fun τ => |c| * ∏ a, ∏ b ∈ Finset.Ioi a, |u τ b - u τ a|)
    (fun τ => 0 + ∑ a, ∑ b ∈ Finset.Ioi a, (w τ a + w τ b))
    (fun τ _ => Maj.mul (maj_C c)
      (Maj.prod Finset.univ _ _ _
        (fun a _ => Maj.prod (Finset.Ioi a) _ _ _ (hfac τ a) (fun b _ => add_nonneg (hw τ a) (hw τ b)))
        (fun a _ => hin τ a)) le_rfl (Finset.sum_nonneg fun a _ => hin τ a))
    (fun τ _ => by rw [zero_add]; exact Finset.sum_nonneg fun a _ => hin τ a)
  rw [h0, hP]
  refine hM.mono (Finset.sum_nonneg fun τ _ => by
    rw [zero_add]; exact Finset.sum_nonneg fun a _ => hin τ a) le_rfl ?_
  rw [Finset.sum_eq_single τ' (fun τ _ hτ => by simp [w, hτ]) (by simp), zero_add]
  have hw' : ∀ a, w τ' a = if a = i then 1 / g else 0 := fun a => by simp [w]
  simp only [hw', Finset.sum_add_distrib]
  have e1 : ∑ a : Fin N, ∑ _b ∈ Finset.Ioi a, (if a = i then 1 / g else 0) = ((Finset.Ioi i).card : ℝ) * (1 / g) := by
    rw [Finset.sum_eq_single i (fun a _ ha => by simp [ha]) (by simp)]
    simp
  have e2 : ∑ a : Fin N, ∑ b ∈ Finset.Ioi a, (if b = i then 1 / g else 0) = ((Finset.Iio i).card : ℝ) * (1 / g) := by
    simp only [Finset.sum_ite_eq', Finset.mem_Ioi]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    congr 2
    congr 1
    ext a
    simp
  rw [e1, e2, ← add_mul, mul_one_div]
  refine div_le_div_of_nonneg_right ?_ hg.le
  rw [Fin.card_Ioi, Fin.card_Iio]
  have := i.2
  exact_mod_cast (by omega : N - 1 - (i : ℕ) + (i : ℕ) ≤ N)

theorem flagDeg_coeff (u : Wt Ψ N) (x0 : Ψ × Fin N) :
    flagDeg u = ((dimFl Ψ N).factorial : ℝ) * (∏ τ, gdet (rho τ) (vv u x0 τ)).coeff 0 := by
  have h := alt_pow (rho : Ψ → Fin N → ℕ) u x0 0 (dimFl Ψ N) (by rw [sum_rho]; rfl)
  rw [pow_zero, one_mul] at h
  rw [flagDeg, degFl_eq, h]
  have h1 : ((-1 : ℝ) ^ dimFl Ψ N) * (-1) ^ dimFl Ψ N = 1 := by
    rw [← mul_pow]; norm_num
  simp only [Nat.factorial_zero, Nat.cast_one, mul_one]
  linear_combination (((dimFl Ψ N).factorial : ℝ) * (∏ τ, gdet (rho τ) (vv u x0 τ)).coeff 0) * h1

theorem lam_bound (u : Wt Ψ N) (τ τ' : Ψ) (i : Fin N) (g U : ℝ) (hg : 0 < g) (hU : 0 < U)
    (hsep : ∀ b, i ≠ b → g ≤ |u τ' i - u τ' b|) (hu : ∀ b, |u τ b| ≤ U) (k : ℕ) (hk : 1 ≤ k) :
    |lam τ k (X (τ', i) ^ (k - 1) * linRoot u ^ (dimFl Ψ N + 1))| ≤
      ((dimFl Ψ N : ℝ) + 1) * |flagDeg u| * (2 ^ (k - 1) / (k.factorial : ℝ) * U * (k + N * U / g) ^ (k - 1)) := by
  have hv : ∀ b, Maj (vv u (τ', i) τ b) U (1 / U) := by
    intro b
    by_cases h : (τ, b) = (τ', i)
    · have : vv u (τ', i) τ b = Polynomial.C (u τ b) + Polynomial.C 1 * Polynomial.X := by simp [vv, h]
      rw [this]
      exact maj_lin _ _ _ _ (by positivity) (hu b) (by rw [mul_one_div_cancel hU.ne', abs_one])
    · have : vv u (τ', i) τ b = Polynomial.C (u τ b) + Polynomial.C 0 * Polynomial.X := by
        simp only [vv, if_neg h, map_zero, zero_mul]
      rw [this]
      exact maj_lin _ _ _ _ (by positivity) (hu b) (by rw [abs_zero]; positivity)
  obtain ⟨r, hr, hre⟩ := gdet_bump k hk U hU (vv u (τ', i) τ) hv
  have hsum : ∑ c, ∏ τ'', gdet (bump τ c k τ'') (vv u (τ', i) τ'') =
      r * ∏ τ'', gdet (rho τ'') (vv u (τ', i) τ'') := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), ← mul_assoc]
    have hre' : ∑ c, gdet (bump τ c k τ) (vv u (τ', i) τ) = r * gdet (rho τ) (vv u (τ', i) τ) := by
      refine Eq.trans (Finset.sum_congr rfl fun c _ => ?_) hre
      congr 1
      funext c'
      simp [bump]
    rw [← hre', Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ)]
    congr 1
    refine Finset.prod_congr rfl fun τ'' h => ?_
    congr 1
    funext c'
    simp [bump, rho, Finset.ne_of_mem_erase h]
  have hl : lam τ k (X (τ', i) ^ (k - 1) * linRoot u ^ (dimFl Ψ N + 1)) =
      (-1) ^ (dimFl Ψ N + 1) * ((dimFl Ψ N + 1).factorial : ℝ) * ((k - 1).factorial : ℝ) *
        (r * ∏ τ'', gdet (rho τ'') (vv u (τ', i) τ'')).coeff (k - 1) := by
    rw [← hsum, Polynomial.finsetSum_coeff, Finset.mul_sum, lam]
    refine Finset.sum_congr rfl fun c _ => ?_
    exact alt_pow _ _ _ _ _ (by rw [sum_bump]; omega)
  have hM := (hr.mul (maj_rho u τ' i g hg hsep) (by positivity) (by positivity)) (k - 1)
  have hF : |flagDeg u| = ((dimFl Ψ N).factorial : ℝ) * |(∏ τ, gdet (rho τ) (vv u (τ', i) τ)).coeff 0| := by
    rw [flagDeg_coeff u (τ', i), abs_mul, Nat.abs_cast]
  rw [hl, abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast, Nat.abs_cast, hF]
  refine (mul_le_mul_of_nonneg_left hM (by positivity)).trans (le_of_eq ?_)
  obtain ⟨s, rfl⟩ : ∃ s, k = s + 1 := ⟨k - 1, by omega⟩
  have h2 : (s.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have h3 : ((s + 1 : ℕ) : ℝ) + N * U / g = U * (((s + 1 : ℕ) : ℝ) / U + N / g) := by field_simp
  rw [h3, mul_pow, Nat.factorial_succ (dimFl Ψ N), Nat.add_sub_cancel]
  push_cast
  field_simp
  ring

theorem lam_decomp {F : RP Ψ N} {Q : Ψ → ℕ → RP Ψ N} (hQ : IsDecomp F Q) (τ : Ψ) (k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N)
    (γ : RP Ψ N) : lam τ k (γ * F) = k * alt rho (γ * Q τ k) := by
  rw [hQ.2, Finset.mul_sum, lam_sum]
  simp only [Finset.mul_sum, lam_sum]
  have : ∀ τ', ∀ m ∈ Finset.Icc 1 N, lam τ k (γ * (pk τ' m * Q τ' m)) =
      if τ' = τ ∧ m = k then (k : ℝ) * alt rho (γ * Q τ' m) else 0 := by
    intro τ' m hm
    rw [mul_left_comm]
    exact lam_pk τ τ' k m hk hkN (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hm).2 _
  rw [Finset.sum_congr rfl fun τ' _ => Finset.sum_congr rfl (this τ'),
    Finset.sum_eq_single τ (fun τ' _ h => by simp [h]) (by simp),
    Finset.sum_eq_single k (fun m _ h => by simp [h]) (fun h => absurd (Finset.mem_Icc.mpr ⟨hk, hkN⟩) h)]
  simp

theorem lam_shift (u : Wt Ψ N) (τ : Ψ) (a : ℝ) (k : ℕ) (hk : 2 ≤ k) (hkN : k ≤ N) (γ : RP Ψ N) (n : ℕ) :
    lam τ k (γ * linRoot (fun σ b => u σ b - if σ = τ then a else 0) ^ n) = lam τ k (γ * linRoot u ^ n) := by
  have h : linRoot (fun σ b => u σ b - if σ = τ then a else 0) - linRoot u = pk τ 1 * C a := by
    simp only [linRoot, pk, pow_one, map_sub, sub_mul, Finset.sum_sub_distrib]
    have : ∑ x : Ψ × Fin N, (C (if x.1 = τ then a else 0) * X x : RP Ψ N) = (∑ i : Fin N, X (τ, i)) * C a := by
      rw [Fintype.sum_prod_type, Finset.sum_eq_single τ (fun σ _ h => by simp [h]) (by simp), Finset.sum_mul]
      exact Finset.sum_congr rfl fun b _ => by simp [mul_comm]
    rw [this]; ring
  obtain ⟨G, hG⟩ := sub_dvd_pow_sub_pow (linRoot (fun σ b => u σ b - if σ = τ then a else 0)) (linRoot u) n
  rw [h, sub_eq_iff_eq_add] at hG
  rw [hG, mul_add, lam_add, show γ * (pk τ 1 * C a * G) = pk τ 1 * (γ * C a * G) by ring,
    lam_pk τ τ k 1 (by omega) hkN le_rfl (by omega), if_neg (by omega), zero_add]

theorem one_bound (j : ℕ) (u : Wt Ψ N) (g : ℝ) (Q : Ψ → ℕ → RP Ψ N) (hW : WeightHyp j u g)
    (hQ : IsDecomp (linRoot u ^ (dimFl Ψ N + 1)) Q) (τ τ' : Ψ) (k : ℕ) (hk : 2 ≤ k) (hkN : k ≤ N) (i : Fin N)
    (hi : InSmall j i) :
    |k * alt rho (X (τ', i) ^ (k - 1) * Q τ k)| ≤ ((dimFl Ψ N : ℝ) + 1) * flagDeg u *
      ((2 ^ (k - 1) / (k.factorial : ℝ)) * ((⨆ i, u τ i) - ⨅ i, u τ i) * (N * (1 + 2 * (‖u‖ / g))) ^ (k - 1)) := by
  obtain ⟨hg, hreg, -, hsep⟩ := hW
  haveI : Nonempty (Fin N) := ⟨i⟩
  have hle : ∀ b, u τ b ≤ ⨆ i, u τ i := fun b => le_ciSup (Set.finite_range _).bddAbove b
  have hge : ∀ b, (⨅ i, u τ i) ≤ u τ b := fun b => ciInf_le (Set.finite_range _).bddBelow b
  have hn : ∀ b, |u τ b| ≤ ‖u‖ := fun b =>
    (norm_le_pi_norm (u τ) b).trans (norm_le_pi_norm u τ)
  have hs : (⨆ i, u τ i) ≤ ‖u‖ := ciSup_le fun b => (abs_le.mp (hn b)).2
  have hI : -‖u‖ ≤ ⨅ i, u τ i := le_ciInf fun b => (abs_le.mp (hn b)).1
  set U := (⨆ i, u τ i) - ⨅ i, u τ i with hUd
  have hU : 0 < U := by
    have := hreg τ ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp [Fin.lt_def])
    have h1 := hle ⟨0, by omega⟩
    have h2 := hge ⟨1, by omega⟩
    linarith
  have hpos : 0 < flagDeg u := (GlobalTheory.T.flag_degree_weight_formula Ψ N u).2.1 hreg
  have hfl : flagDeg (fun σ b => u σ b - if σ = τ then ⨅ i, u τ i else 0) = flagDeg u := by
    rw [(GlobalTheory.T.flag_degree_weight_formula Ψ N u).1, (GlobalTheory.T.flag_degree_weight_formula Ψ N _).1]
    simp only [sub_sub_sub_cancel_right]
  have hb := lam_bound (fun σ b => u σ b - if σ = τ then ⨅ i, u τ i else 0) τ τ' i g U hg hU
    (fun b hb => by rw [sub_sub_sub_cancel_right]; exact hsep τ' i b hi hb)
    (fun b => by
      rw [if_pos rfl, abs_of_nonneg (sub_nonneg.mpr (hge b))]
      linarith [hle b]) k (by omega)
  rw [lam_shift u τ _ k hk hkN, lam_decomp hQ τ k (by omega) hkN, hfl, abs_of_pos hpos] at hb
  refine hb.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) ?_ _) (by positivity)) (by positivity))
  have h1 : (k : ℝ) ≤ N := by exact_mod_cast hkN
  have h2 : U / g ≤ 2 * (‖u‖ / g) := by
    rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right (by linarith) hg.le
  have h3 : (N : ℝ) * (U / g) ≤ N * (2 * (‖u‖ / g)) := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
  rw [mul_div_assoc]
  linarith

theorem small_block (j : ℕ) (hj : j < N) (σ : Ψ ⊕ Ψ) (m : ℕ) (hm : 1 ≤ m) (G : RP Ψ N) :
    ∃ (τ' : Ψ) (I : Finset (Fin N)), I.card = min j (N - j) ∧ (∀ i ∈ I, InSmall j i) ∧
      |alt rho (pLie j m σ * G)| = |∑ i ∈ I, alt rho (X (τ', i) ^ m * G)| := by
  have cL : (Finset.univ.filter fun i : Fin N => (i : ℕ) < j).card = j := by
    rw [Fin.card_filter_val_lt]; omega
  have cH : (Finset.univ.filter fun i : Fin N => j ≤ (i : ℕ)).card = N - j := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N))) (fun i : Fin N => (i : ℕ) < j)
    simp only [not_lt, cL, Finset.card_univ, Fintype.card_fin] at this
    omega
  have key : ∀ τ' : Ψ, |∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), alt rho (X (τ', i) ^ m * G)| =
      |∑ i ∈ Finset.univ.filter (fun i : Fin N => j ≤ (i : ℕ)), alt rho (X (τ', i) ^ m * G)| := by
    intro τ'
    have h := alt_rho_pk τ' m hm G
    rw [pk, Finset.sum_mul, alt_sum,
      ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin N => (i : ℕ) < j)] at h
    simp only [not_lt] at h
    rw [eq_neg_of_add_eq_zero_left h, abs_neg]
  have base : ∃ τ' : Ψ, |alt rho (pLie j m σ * G)| =
      |∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), alt rho (X (τ', i) ^ m * G)| := by
    rcases σ with τ' | τ'
    · exact ⟨τ', by rw [pLie, pkLow, Finset.sum_mul, alt_sum]⟩
    · refine ⟨τ', ?_⟩
      rw [key, pLie, Finset.sum_mul, alt_sum,
        Finset.sum_congr rfl (g := fun i => (-1 : ℝ) ^ m * alt rho (X (τ', i) ^ m * G)) (fun i _ => by
          rw [← alt_C_mul, neg_pow, mul_assoc]; simp),
        ← Finset.mul_sum, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  obtain ⟨τ', h⟩ := base
  by_cases hc : j ≤ N - j
  · exact ⟨τ', _, by rw [cL, min_eq_left hc], fun i hi => by
      rw [InSmall, if_pos hc]; exact (Finset.mem_filter.mp hi).2, h⟩
  · exact ⟨τ', _, by rw [cH, min_eq_right (not_le.mp hc).le], fun i hi => by
      rw [InSmall, if_neg hc]; exact (Finset.mem_filter.mp hi).2, h.trans (key τ')⟩

end RootFieldNumerics.M5

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
end
end
end
