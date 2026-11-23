module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.DecMomentsA
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.CBinet
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Tactic.Basify
import Mathlib.Tactic.TypeStar
public import Mathlib.Analysis.MeanInequalitiesPow
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.DecMoments
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.SpecialFunctions.Exponential

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.DecLog

section

@[expose] public section

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem exp_ge_one_add_add_sq_div_three {u : ℝ} (hu : |u| ≤ 1) :
    1 + u + u ^ 2 / 3 ≤ Real.exp u := by
  have hb := Real.exp_bound hu (n := 5) (by norm_num)
  have h1 : -(|u| ^ 5 * ((Nat.succ 5 : ℝ) / ((Nat.factorial 5 : ℝ) * 5))) ≤
      Real.exp u - ∑ i ∈ Finset.range 5, u ^ i / (Nat.factorial i : ℝ) := (abs_le.mp hb).1
  norm_num [Finset.sum_range_succ, Nat.factorial] at h1
  have hu2 : |u| ^ 5 ≤ u ^ 2 := by
    have h0 : 0 ≤ |u| := abs_nonneg u
    have h3 : |u| ^ 3 ≤ 1 := pow_le_one₀ h0 hu
    calc |u| ^ 5 = |u| ^ 2 * |u| ^ 3 := by ring
      _ ≤ |u| ^ 2 * 1 := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = u ^ 2 := by rw [mul_one, sq_abs]
  have hlo : -1 ≤ u := (abs_le.mp hu).1
  have hq : 0 ≤ (u + 1) * (u + 3) := mul_nonneg (by linarith) (by linarith)
  nlinarith [mul_nonneg (sq_nonneg u) hq, sq_nonneg u]

theorem logSumExp_lower {ι : Type*} [Fintype ι] (w y : ι → ℝ) (hw : ∀ j, 0 ≤ w j)
    (h1 : ∑ j, w j = 1) (h0 : ∑ j, w j * y j = 0) {R : ℝ} (hR : 0 < R) (hy : ∀ j, |y j| ≤ R) :
    min 1 (1 / R) * (∑ j, w j * y j ^ 2) / 4 ≤ Real.log (∑ j, w j * Real.exp (y j)) := by
  have hc0 : 0 < min 1 (1 / R) := lt_min one_pos (by positivity)
  have hc1 : min 1 (1 / R) ≤ 1 := min_le_left _ _
  have hcR : min 1 (1 / R) * R ≤ 1 := by
    calc min 1 (1 / R) * R ≤ (1 / R) * R := mul_le_mul_of_nonneg_right (min_le_right _ _) hR.le
      _ = 1 := by field_simp
  generalize hcdef : min 1 (1 / R) = c at hc0 hc1 hcR ⊢
  have hQ0 : 0 ≤ ∑ j, w j * y j ^ 2 := Finset.sum_nonneg fun j _ => mul_nonneg (hw j) (sq_nonneg _)
  have hQR : ∑ j, w j * y j ^ 2 ≤ R ^ 2 := by
    calc ∑ j, w j * y j ^ 2 ≤ ∑ j, w j * R ^ 2 :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (by
            have h := hy j
            have : y j ^ 2 = |y j| ^ 2 := (sq_abs _).symm
            rw [this]
            exact pow_le_pow_left₀ (abs_nonneg _) h 2) (hw j)
      _ = R ^ 2 := by rw [← Finset.sum_mul, h1, one_mul]
  have hpt : ∀ j, 1 + c * y j + (c * y j) ^ 2 / 3 ≤ Real.exp (c * y j) := fun j =>
    exp_ge_one_add_add_sq_div_three (by
      rw [abs_mul, abs_of_pos hc0]
      calc c * |y j| ≤ c * R := mul_le_mul_of_nonneg_left (hy j) hc0.le
        _ ≤ 1 := hcR)
  have hsum : ∑ j, w j * (1 + c * y j + (c * y j) ^ 2 / 3) =
      1 + c ^ 2 * (∑ j, w j * y j ^ 2) / 3 := by
    have e : ∑ j, w j * (1 + c * y j + (c * y j) ^ 2 / 3) =
        ∑ j, w j + c * ∑ j, w j * y j + c ^ 2 / 3 * ∑ j, w j * y j ^ 2 := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e, h1, h0]
    ring
  have hS : 1 + c ^ 2 * (∑ j, w j * y j ^ 2) / 3 ≤ ∑ j, w j * Real.exp (c * y j) := by
    rw [← hsum]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hpt j) (hw j)
  have hS1 : 0 < 1 + c ^ 2 * (∑ j, w j * y j ^ 2) / 3 := by positivity
  have hSpos : 0 < ∑ j, w j * Real.exp (c * y j) := lt_of_lt_of_le hS1 hS
  have hJ : (∑ j, w j * Real.exp (c * y j)) ^ (1 / c) ≤ ∑ j, w j * Real.exp (y j) := by
    have := Real.rpow_arith_mean_le_arith_mean_rpow Finset.univ w (fun j => Real.exp (c * y j))
      (fun j _ => hw j) h1 (fun j _ => (Real.exp_pos _).le) (p := 1 / c)
      (by rw [le_div_iff₀ hc0]; linarith)
    refine this.trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
    rw [← Real.exp_mul]
    congr 2
    field_simp
  have ht1 : c ^ 2 * (∑ j, w j * y j ^ 2) ≤ 1 := by
    calc c ^ 2 * (∑ j, w j * y j ^ 2) ≤ c ^ 2 * R ^ 2 := mul_le_mul_of_nonneg_left hQR (sq_nonneg c)
      _ = (c * R) ^ 2 := by ring
      _ ≤ 1 := by nlinarith [mul_pos hc0 hR]
  have hlog1 : 3 / 4 * (c ^ 2 * (∑ j, w j * y j ^ 2) / 3) ≤
      Real.log (1 + c ^ 2 * (∑ j, w j * y j ^ 2) / 3) := by
    have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hS1)
    rw [Real.log_inv] at h
    have hinv : (1 + c ^ 2 * (∑ j, w j * y j ^ 2) / 3)⁻¹ ≤
        1 - 3 / 4 * (c ^ 2 * (∑ j, w j * y j ^ 2) / 3) := by
      rw [inv_eq_one_div, div_le_iff₀ hS1]
      nlinarith [mul_nonneg (sq_nonneg c) hQ0]
    linarith
  have hlog : 3 / 4 * (c ^ 2 * (∑ j, w j * y j ^ 2) / 3) ≤ Real.log (∑ j, w j * Real.exp (c * y j)) :=
    hlog1.trans (Real.log_le_log hS1 hS)
  calc c * (∑ j, w j * y j ^ 2) / 4
      = (1 / c) * (3 / 4 * (c ^ 2 * (∑ j, w j * y j ^ 2) / 3)) := by
        field_simp
    _ ≤ (1 / c) * Real.log (∑ j, w j * Real.exp (c * y j)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = Real.log ((∑ j, w j * Real.exp (c * y j)) ^ (1 / c)) := by rw [Real.log_rpow hSpos]
    _ ≤ Real.log (∑ j, w j * Real.exp (y j)) := Real.log_le_log (by positivity) hJ

end ReciprocityTheory.ChartRestriction.DS.S7
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.DecALogLower

section

@[expose] public section

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {ε : Fin n → Bool}

lemma decA_spec {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inP ε Y) :
    ∃ (U : Matrix (Fin n) (Fin n) ℂ) (y : Fin n → ℝ), U ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
      Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ := by
  obtain ⟨h1, h2⟩ := hY
  have hJJ : Jm ε * Jm ε = 1 := by
    unfold Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> simp
  have hH : Yᴴ = Y := by
    unfold inG at h1
    have h3 : Yᴴ * Jm ε = Y * Jm ε := by
      rw [h2]
      exact eq_neg_of_add_eq_zero_left h1
    calc Yᴴ = Yᴴ * Jm ε * Jm ε := by rw [Matrix.mul_assoc, hJJ, Matrix.mul_one]
      _ = Y * Jm ε * Jm ε := by rw [h3]
      _ = Y := by rw [Matrix.mul_assoc, hJJ, Matrix.mul_one]
  have hA : Y.IsHermitian := hH
  refine ⟨hA.eigenvectorUnitary, hA.eigenvalues, (hA.eigenvectorUnitary).2, ?_⟩
  first
    | exact hA.spectral_theorem
    | simpa [Matrix.star_eq_conjTranspose] using hA.spectral_theorem
    | (conv_lhs => rw [hA.spectral_theorem]); rfl

lemma decA_exp {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (y : Fin n → ℝ) :
    NormedSpace.exp (U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ) =
      U * Matrix.diagonal (fun j => ((Real.exp (y j) : ℝ) : ℂ)) * Uᴴ := by
  have hinv : U⁻¹ = Uᴴ := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.mp hU)
  have hu : IsUnit U := (Matrix.isUnit_iff_isUnit_det U).mpr (isUnit_iff_ne_zero.mpr
    (left_ne_zero_of_mul_eq_one (b := (star U).det)
      (by rw [← Matrix.det_mul, Matrix.mem_unitaryGroup_iff.mp hU, Matrix.det_one])))
  have hd : NormedSpace.exp (fun j => ((y j : ℝ) : ℂ)) = fun j => ((Real.exp (y j) : ℝ) : ℂ) := by
    funext j
    first
      | (rw [Pi.exp_apply]; simp [← Complex.exp_eq_exp_ℂ, Complex.ofReal_exp])
      | (simp [Pi.exp_def, ← Complex.exp_eq_exp_ℂ, Complex.ofReal_exp])
      | (simp [NormedSpace.exp_pi, ← Complex.exp_eq_exp_ℂ, Complex.ofReal_exp])
  rw [← hinv, Matrix.exp_conj U _ hu, Matrix.exp_diagonal, hd]

lemma decA_lead_re {U : Matrix (Fin n) (Fin n) ℂ} (y : Fin n → ℝ) (i : ℕ) (hi : i ≤ n) :
    (lead i (U * Matrix.diagonal (fun j => ((Real.exp (y j) : ℝ) : ℂ)) * Uᴴ)).re =
      ∑ J : {J : Finset (Fin n) // J.card = i}, dmW U hi J * Real.exp (∑ j ∈ J.1, y j) := by
  rw [lead_unitary_diag _ i hi, Complex.re_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [show (∏ j ∈ J.1, ((Real.exp (y j) : ℝ) : ℂ)) = ((∏ j ∈ J.1, Real.exp (y j) : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_mul, Complex.ofReal_re, ← Real.exp_sum]
  rfl

lemma decA_log_lower {Y U : Matrix (Fin n) (Fin n) ℂ} {y : Fin n → ℝ} (hYp : inP ε Y)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ)
    (hq : 1 ≤ q0 ε) (hpos : 0 < hs Y) (m : ℕ) (hm : m ≤ n) :
    min 1 (1 / (Real.sqrt (2 * q0 ε) * Real.sqrt (hs Y))) *
        (∑ a : Fin n, ∑ b : Fin n, if (b : ℕ) < m ∧ m ≤ (a : ℕ) then ‖Y a b‖ ^ 2 else 0) / 4 ≤
      Real.log (lead m (NormedSpace.exp Y)).re := by
  obtain ⟨h1, h2, h3, h4⟩ := dec_moments hU hY hYp m hm
  have hE : NormedSpace.exp Y = U * Matrix.diagonal (fun j => ((Real.exp (y j) : ℝ) : ℂ)) * Uᴴ := by
    rw [hY]; exact decA_exp hU y
  rw [hE, decA_lead_re y m hm, ← h3]
  have hq' : (0 : ℝ) < 2 * q0 ε := by
    have : (1 : ℝ) ≤ q0 ε := by exact_mod_cast hq
    linarith
  have hR : 0 < Real.sqrt (2 * q0 ε) * Real.sqrt (hs Y) :=
    mul_pos (Real.sqrt_pos.mpr hq') (Real.sqrt_pos.mpr hpos)
  exact logSumExp_lower (fun J => dmW U hm J) (fun J => ∑ j ∈ J.1, y j) (fun J => by unfold dmW; positivity)
    h1 h2 hR h4

lemma decA_lead_last {Y U : Matrix (Fin n) (Fin n) ℂ} {y : Fin n → ℝ} (hYp : inP ε Y)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ) :
    (lead n (NormedSpace.exp Y)).re = 1 := by
  obtain ⟨_, h2⟩ := hYp
  have hJJ : Jm ε * Jm ε = 1 := by
    unfold Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> simp
  have htr : Matrix.trace Y = 0 := by
    have e1 : Matrix.trace Y = Matrix.trace (Jm ε * (Y * Jm ε)) := by
      rw [← Matrix.trace_mul_comm (Y * Jm ε) (Jm ε), Matrix.mul_assoc, hJJ, Matrix.mul_one]
    rw [h2, Matrix.mul_neg, ← Matrix.mul_assoc, hJJ, Matrix.one_mul, Matrix.trace_neg] at e1
    have e2 : (2 : ℂ) * Matrix.trace Y = 0 := by linear_combination e1
    simpa using e2
  have hUU : Uᴴ * U = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hU
  have hsum : ∑ j, y j = 0 := by
    have e3 : Matrix.trace Y = ((∑ j, y j : ℝ) : ℂ) := by
      rw [hY, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hUU, Matrix.one_mul, Matrix.trace_diagonal]
      push_cast
      rfl
    rw [htr] at e3
    exact_mod_cast e3.symm
  rw [hY, decA_exp hU y, decA_lead_re y n le_rfl]
  have huniq : ∀ J : {J : Finset (Fin n) // J.card = n}, J = ⟨Finset.univ, by simp⟩ :=
    fun J => Subtype.ext (Finset.eq_univ_of_card _ (by simpa using J.2))
  rw [Fintype.sum_eq_single ⟨Finset.univ, by simp⟩ (fun J hJ => absurd (huniq J) hJ)]
  rw [hsum, Real.exp_zero, mul_one]
  unfold dmW
  have hid : ((Finset.univ : Finset (Fin n)).orderEmbOfFin (by simp) : Fin n → Fin n) = id :=
    (Finset.orderEmbOfFin_unique (by simp) (fun x => Finset.mem_univ x) strictMono_id).symm
  have hsub : U.submatrix (Fin.castLE (le_refl n))
      ((Finset.univ : Finset (Fin n)).orderEmbOfFin (by simp)) = U := by
    ext i j
    rw [Matrix.submatrix_apply, show Fin.castLE (le_refl n) i = i from Fin.ext rfl,
      show ((Finset.univ : Finset (Fin n)).orderEmbOfFin (by simp) : Fin n → Fin n) j = j from congrFun hid j]
  rw [hsub]
  have hdet : star U.det * U.det = 1 := by
    rw [← Matrix.det_conjTranspose, ← Matrix.det_mul, hUU, Matrix.det_one]
  have h5 : ((‖U.det‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← hdet, Complex.star_def, Complex.conj_mul']
    push_cast
    rfl
  exact_mod_cast h5

lemma decA_hs_trace (A : Matrix (Fin n) (Fin n) ℂ) : ((hs A : ℝ) : ℂ) = Matrix.trace (A * Aᴴ) := by
  unfold hs
  rw [Matrix.trace]
  push_cast
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

lemma decA_hs_conj {K : Matrix (Fin n) (Fin n) ℂ} (hK : K * Kᴴ = 1) (X : Matrix (Fin n) (Fin n) ℂ) :
    hs (Kᴴ * X * K) = hs X := by
  apply Complex.ofReal_injective
  rw [decA_hs_trace, decA_hs_trace, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  calc Matrix.trace (Kᴴ * X * K * (Kᴴ * (Xᴴ * K))) = Matrix.trace (Kᴴ * ((X * Xᴴ) * K)) := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc K Kᴴ, hK, Matrix.one_mul]
    _ = Matrix.trace ((X * Xᴴ) * K * Kᴴ) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (X * Xᴴ) := by rw [Matrix.mul_assoc, hK, Matrix.mul_one]

end ReciprocityTheory.ChartRestriction.DS.S7
end
end
end
