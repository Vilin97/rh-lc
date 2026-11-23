module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.DecMomentsA
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.DecMomentsB

section

@[expose] public section

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

lemma dm_swap4 (F : Fin n → Fin n → Fin n → Fin n → ℂ) :
    ∑ k, ∑ l, ∑ a, ∑ b, F k l a b = ∑ a, ∑ b, ∑ k, ∑ l, F k l a b := by
  calc ∑ k, ∑ l, ∑ a, ∑ b, F k l a b = ∑ k, ∑ a, ∑ l, ∑ b, F k l a b :=
        Finset.sum_congr rfl (fun k _ => Finset.sum_comm)
    _ = ∑ a, ∑ k, ∑ l, ∑ b, F k l a b := Finset.sum_comm
    _ = ∑ a, ∑ k, ∑ b, ∑ l, F k l a b :=
        Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun k _ => Finset.sum_comm))
    _ = ∑ a, ∑ b, ∑ k, ∑ l, F k l a b := Finset.sum_congr rfl (fun a _ => Finset.sum_comm)

variable {U Y : Matrix (Fin n) (Fin n) ℂ} {y : Fin n → ℝ}

lemma dm_Ye (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ) (a b : Fin n) :
    Y a b = ∑ j, U a j * (y j : ℂ) * star (U b j) := by
  rw [hY, dm_entry]

lemma dm_herm (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ) (a b : Fin n) :
    Y b a = star (Y a b) := by
  rw [dm_Ye hY, dm_Ye hY, star_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [star_mul', star_star]
  simp only [Complex.star_def, Complex.conj_ofReal]
  ring

lemma trace_diag_conj_eq (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ) (i : ℕ) :
    ∑ k, (y k : ℂ) * dmK U i k k = ∑ a, dmChi i a * Y a a := by
  simp only [dmK, Finset.mul_sum, dm_Ye hY]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => ?_
  ring

lemma trace_sq_diag_conj_eq (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ) (i : ℕ) :
    ∑ k, ∑ l, (y k : ℂ) * (y l : ℂ) * (dmK U i k l * dmK U i l k) =
      ∑ a, ∑ b, dmChi i a * dmChi i b * (Y b a * Y a b) := by
  have hL : ∀ k l, (y k : ℂ) * (y l : ℂ) * (dmK U i k l * dmK U i l k) =
      ∑ a, ∑ b, (y k : ℂ) * (y l : ℂ) *
        ((dmChi i a * (star (U a k) * U a l)) * (dmChi i b * (star (U b l) * U b k))) := by
    intro k l
    rw [dmK, dmK, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
  have hR : ∀ a b, dmChi i a * dmChi i b * (Y b a * Y a b) =
      ∑ k, ∑ l, dmChi i a * dmChi i b *
        ((U b k * (y k : ℂ) * star (U a k)) * (U a l * (y l : ℂ) * star (U b l))) := by
    intro a b
    rw [dm_Ye hY b a, dm_Ye hY a b, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
  simp only [hL, hR]
  rw [dm_swap4]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

lemma trace_pow_two_diag_conj (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ)
    (i : ℕ) :
    ∑ k, (y k : ℂ) ^ 2 * dmK U i k k = ∑ a, dmChi i a * ∑ b, Y a b * Y b a := by
  have hYY : Y * Y = U * Matrix.diagonal (fun j => (y j : ℂ) ^ 2) * Uᴴ := by
    rw [hY]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U, dm_UhU hU, Matrix.one_mul, ← Matrix.mul_assoc (Matrix.diagonal _),
      Matrix.diagonal_mul_diagonal]
    simp only [sq]
  have hrow : ∀ a, ∑ b, Y a b * Y b a = ∑ k, U a k * (y k : ℂ) ^ 2 * star (U a k) := by
    intro a
    rw [← Matrix.mul_apply, hYY, dm_entry]
  simp only [hrow, dmK, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => ?_
  ring

lemma dm_S (J : Finset (Fin n)) : ((∑ j ∈ J, y j : ℝ) : ℂ) = ∑ k, dmInd J k * (y k : ℂ) := by
  push_cast
  unfold dmInd
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

lemma dm_mean (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ)
    (hd : ∀ a, Y a a = 0) {i : ℕ} (hi : i ≤ n) :
    ∑ J : {J : Finset (Fin n) // J.card = i}, ((dmW U hi J : ℝ) : ℂ) * ((∑ j ∈ J.1, y j : ℝ) : ℂ) = 0 := by
  simp only [dm_S, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h : ∀ k, ∑ J : {J : Finset (Fin n) // J.card = i}, ((dmW U hi J : ℝ) : ℂ) * (dmInd J.1 k * (y k : ℂ)) =
      (y k : ℂ) * dmK U i k k := by
    intro k
    rw [← sum_minorWeights_indicator hU hi k, Finset.mul_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    ring
  simp only [h, trace_diag_conj_eq hY, hd, mul_zero, Finset.sum_const_zero]

lemma dm_var (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ)
    (hd : ∀ a, Y a a = 0) {i : ℕ} (hi : i ≤ n) :
    ∑ J : {J : Finset (Fin n) // J.card = i}, ((dmW U hi J : ℝ) : ℂ) * ((∑ j ∈ J.1, y j : ℝ) : ℂ) ^ 2 =
      ∑ a, ∑ b, dmChi i a * (1 - dmChi i b) * (Y a b * Y b a) := by
  calc ∑ J : {J : Finset (Fin n) // J.card = i}, ((dmW U hi J : ℝ) : ℂ) * ((∑ j ∈ J.1, y j : ℝ) : ℂ) ^ 2
        = ∑ J : {J : Finset (Fin n) // J.card = i}, ∑ k, ∑ l,
            ((dmW U hi J : ℝ) : ℂ) * (dmInd J.1 k * dmInd J.1 l) * ((y k : ℂ) * (y l : ℂ)) := by
          refine Finset.sum_congr rfl fun J _ => ?_
          rw [dm_S, sq, Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          ring
    _ = ∑ k, ∑ J : {J : Finset (Fin n) // J.card = i}, ∑ l,
            ((dmW U hi J : ℝ) : ℂ) * (dmInd J.1 k * dmInd J.1 l) * ((y k : ℂ) * (y l : ℂ)) :=
          Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ J : {J : Finset (Fin n) // J.card = i},
            ((dmW U hi J : ℝ) : ℂ) * (dmInd J.1 k * dmInd J.1 l) * ((y k : ℂ) * (y l : ℂ)) :=
          Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ k, ∑ l, (y k : ℂ) * (y l : ℂ) * (dmK U i k k * dmK U i l l - dmK U i k l * dmK U i l k +
            if k = l then dmK U i k k else 0) := by
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
          rw [← dm_m hU hi k l, Finset.mul_sum]
          refine Finset.sum_congr rfl fun J _ => ?_
          ring
    _ = (∑ k, (y k : ℂ) * dmK U i k k) * (∑ l, (y l : ℂ) * dmK U i l l) -
          ∑ k, ∑ l, (y k : ℂ) * (y l : ℂ) * (dmK U i k l * dmK U i l k) +
          ∑ k, (y k : ℂ) ^ 2 * dmK U i k k := by
          have hk : ∀ k, ∑ l, (y k : ℂ) * (y l : ℂ) * (dmK U i k k * dmK U i l l - dmK U i k l * dmK U i l k +
              if k = l then dmK U i k k else 0) =
              ∑ l, ((y k : ℂ) * dmK U i k k) * ((y l : ℂ) * dmK U i l l) -
              ∑ l, (y k : ℂ) * (y l : ℂ) * (dmK U i k l * dmK U i l k) + (y k : ℂ) ^ 2 * dmK U i k k := by
            intro k
            have e : ∀ l, (y k : ℂ) * (y l : ℂ) * (dmK U i k k * dmK U i l l - dmK U i k l * dmK U i l k +
                if k = l then dmK U i k k else 0) =
                ((y k : ℂ) * dmK U i k k) * ((y l : ℂ) * dmK U i l l) -
                (y k : ℂ) * (y l : ℂ) * (dmK U i k l * dmK U i l k) +
                if k = l then (y k : ℂ) ^ 2 * dmK U i k k else 0 := by
              intro l
              split_ifs with h
              · subst h; ring
              · ring
            rw [Finset.sum_congr rfl fun l _ => e l, Finset.sum_add_distrib, Finset.sum_sub_distrib,
              Finset.sum_ite_eq]
            simp only [Finset.mem_univ, if_true]
          rw [Finset.sum_congr rfl fun k _ => hk k, Finset.sum_add_distrib, Finset.sum_sub_distrib,
            Finset.sum_mul_sum]
    _ = ∑ a, ∑ b, dmChi i a * (1 - dmChi i b) * (Y a b * Y b a) := by
          rw [trace_diag_conj_eq hY, trace_sq_diag_conj_eq hY, trace_pow_two_diag_conj hU hY]
          simp only [hd, mul_zero, Finset.sum_const_zero, zero_sub]
          have e : ∀ a b, dmChi i a * (1 - dmChi i b) * (Y a b * Y b a) =
              dmChi i a * (Y a b * Y b a) - dmChi i a * dmChi i b * (Y b a * Y a b) := by
            intro a b; ring
          simp only [e, Finset.sum_sub_distrib, ← Finset.mul_sum]
          ring

lemma dm_rhs (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ) (i : ℕ) :
    ∑ a, ∑ b, dmChi i a * (1 - dmChi i b) * (Y a b * Y b a) =
      ((∑ a : Fin n, ∑ b : Fin n, if (b : ℕ) < i ∧ i ≤ (a : ℕ) then ‖Y a b‖ ^ 2 else 0 : ℝ) : ℂ) := by
  conv_lhs => rw [Finset.sum_comm]
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hb : (b : ℕ) < i <;> by_cases ha : (a : ℕ) < i
  · rw [if_neg (fun h => absurd h.2 (not_le.mpr ha))]; simp [dmChi, hb, ha]
  · rw [if_pos ⟨hb, not_lt.mp ha⟩, dm_normsq, ← dm_herm hY a b]
    simp only [dmChi, if_pos hb, if_neg ha]; ring
  · rw [if_neg (fun h => hb h.1)]; simp [dmChi, hb, ha]
  · rw [if_neg (fun h => hb h.1)]; simp [dmChi, hb, ha]

end ReciprocityTheory.ChartRestriction.DS.S7
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.DecMoments

section

@[expose] public section

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

lemma dm_rank_add (A B : Matrix (Fin n) (Fin n) ℂ) : (A + B).rank ≤ A.rank + B.rank := by
  simp only [← Matrix.finrank_range_mulVecLin]
  rw [Matrix.mulVecLin_add]
  calc Module.finrank ℂ (LinearMap.range (A.mulVecLin + B.mulVecLin))
      ≤ Module.finrank ℂ ↥(LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin) := by
        apply Submodule.finrank_mono
        rintro _ ⟨v, rfl⟩
        exact Submodule.add_mem_sup ⟨v, rfl⟩ ⟨v, rfl⟩
    _ ≤ _ := Submodule.finrank_add_le_finrank_add_finrank _ _

lemma dm_zero_of_eq {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (hYp : inP ε Y) (a b : Fin n)
    (hab : ε a = ε b) : Y a b = 0 := by
  have h := congrFun (congrFun hYp.2 a) b
  simp only [Jm, Matrix.mul_diagonal, Matrix.neg_apply, Matrix.diagonal_mul, hab] at h
  split_ifs at h
  · linear_combination (1 / 2 : ℂ) * h
  · linear_combination (-1 / 2 : ℂ) * h

lemma dm_rank_le {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (hYp : inP ε Y) :
    Y.rank ≤ 2 * q0 ε := by
  classical
  set P : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun a => if ε a then 1 else 0 with hPd
  set Q : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun a => if ε a then 0 else 1 with hQd
  have hY : Y = P * Y * Q + Q * Y * P := by
    ext a b
    simp only [hPd, hQd, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases ha : ε a <;> by_cases hb : ε b <;> simp [ha, hb] <;>
      exact dm_zero_of_eq hYp a b (by simp [ha, hb])
  have hP : P.rank = pOf ε := by
    rw [hPd, Matrix.rank_diagonal, Fintype.card_subtype]
    unfold pOf
    congr 1; ext a; by_cases h : ε a <;> simp [h]
  have hQ : Q.rank = qOf ε := by
    rw [hQd, Matrix.rank_diagonal, Fintype.card_subtype]
    unfold qOf
    congr 1; ext a; by_cases h : ε a <;> simp [h]
  have h1 : (P * Y * Q).rank ≤ q0 ε :=
    le_min ((Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_left _ _).trans hP.le))
      ((Matrix.rank_mul_le_right _ _).trans hQ.le)
  have h2 : (Q * Y * P).rank ≤ q0 ε :=
    le_min ((Matrix.rank_mul_le_right _ _).trans hP.le)
      ((Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_left _ _).trans hQ.le))
  calc Y.rank = (P * Y * Q + Q * Y * P).rank := congrArg Matrix.rank hY
    _ ≤ (P * Y * Q).rank + (Q * Y * P).rank := dm_rank_add _ _
    _ ≤ q0 ε + q0 ε := add_le_add h1 h2
    _ = 2 * q0 ε := by ring

lemma dm_card_le {ε : Fin n → Bool} {Y U : Matrix (Fin n) (Fin n) ℂ} {y : Fin n → ℝ}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ)
    (hYp : inP ε Y) : (univ.filter fun j => y j ≠ 0).card ≤ 2 * q0 ε := by
  have hdet : IsUnit U.det := Matrix.isUnit_det_of_left_inverse (Matrix.mem_unitaryGroup_iff'.1 hU)
  have hdet' : IsUnit Uᴴ.det := Matrix.isUnit_det_of_right_inverse (Matrix.mem_unitaryGroup_iff'.1 hU)
  have h1 : Y.rank = (univ.filter fun j => y j ≠ 0).card := by
    rw [hY, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hdet',
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ hdet, Matrix.rank_diagonal, Fintype.card_subtype]
    simp [Complex.ofReal_eq_zero]
  rw [← h1]
  exact dm_rank_le hYp

lemma dm_range {ε : Fin n → Bool} {Y U : Matrix (Fin n) (Fin n) ℂ} {y : Fin n → ℝ}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ)
    (hYp : inP ε Y) (J : Finset (Fin n)) :
    |∑ j ∈ J, y j| ≤ Real.sqrt (2 * q0 ε) * Real.sqrt (hs Y) := by
  unfold hs
  have key : ∀ M : Matrix (Fin n) (Fin n) ℂ, (((∑ i, ∑ j, ‖M i j‖ ^ 2 : ℝ)) : ℂ) = (M * Mᴴ).trace := by
    intro M
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.ofReal_sum, Complex.ofReal_pow]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    first
      | (rw [Complex.star_def, Complex.mul_conj'])
      | (rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring)
      | simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hUU : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
  have h2 : ∀ M : Matrix (Fin n) (Fin n) ℂ, Uᴴ * (U * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hUU, Matrix.one_mul]
  have htr : (Y * Yᴴ).trace = (((∑ j, y j ^ 2 : ℝ)) : ℂ) := by
    rw [hY]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, h2]
    rw [Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, hUU, Matrix.mul_one,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Complex.conj_ofReal, sq]
  have hsum : ∑ i, ∑ j, ‖Y i j‖ ^ 2 = ∑ j, y j ^ 2 := by
    have h := key Y
    rw [htr] at h
    exact_mod_cast h
  have hT : ∑ j ∈ J, y j = ∑ j ∈ J.filter (fun j => y j ≠ 0), y j :=
    (Finset.sum_filter_ne_zero _).symm
  have hcard : (J.filter fun j => y j ≠ 0).card ≤ 2 * q0 ε :=
    (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ J))).trans
      (dm_card_le hU hY hYp)
  have hcs : (∑ j ∈ J.filter (fun j => y j ≠ 0), y j) ^ 2 ≤
      ((J.filter fun j => y j ≠ 0).card : ℝ) * ∑ j, y j ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (J.filter fun j => y j ≠ 0) (fun _ => (1 : ℝ)) y
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => sq_nonneg _)
  rw [hsum, ← Real.sqrt_mul (by positivity), hT]
  apply Real.abs_le_sqrt
  refine hcs.trans (mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun j _ => sq_nonneg _))
  exact_mod_cast hcard

theorem dec_moments {ε : Fin n → Bool} {Y U : Matrix (Fin n) (Fin n) ℂ} {y : Fin n → ℝ}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ)
    (hYp : inP ε Y) (i : ℕ) (hi : i ≤ n) :
    (∑ J : {J : Finset (Fin n) // J.card = i},
        ‖(U.submatrix (Fin.castLE hi) (J.1.orderEmbOfFin J.2)).det‖ ^ 2 = 1) ∧
    (∑ J : {J : Finset (Fin n) // J.card = i},
        ‖(U.submatrix (Fin.castLE hi) (J.1.orderEmbOfFin J.2)).det‖ ^ 2 * (∑ j ∈ J.1, y j) = 0) ∧
    (∑ J : {J : Finset (Fin n) // J.card = i},
        ‖(U.submatrix (Fin.castLE hi) (J.1.orderEmbOfFin J.2)).det‖ ^ 2 * (∑ j ∈ J.1, y j) ^ 2 =
      ∑ a : Fin n, ∑ b : Fin n, if (b : ℕ) < i ∧ i ≤ (a : ℕ) then ‖Y a b‖ ^ 2 else 0) ∧
    (∀ J : {J : Finset (Fin n) // J.card = i},
        |∑ j ∈ J.1, y j| ≤ Real.sqrt (2 * q0 ε) * Real.sqrt (hs Y)) := by
  have hd : ∀ a, Y a a = 0 := fun a => dm_zero_of_eq hYp a a rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := dm_mass hU hi
    have h2 : ∑ J : {J : Finset (Fin n) // J.card = i}, dmW U hi J = 1 := by exact_mod_cast h
    exact h2
  · have h := dm_mean hU hY hd hi
    have h2 : ∑ J : {J : Finset (Fin n) // J.card = i}, dmW U hi J * (∑ j ∈ J.1, y j) = 0 := by
      exact_mod_cast h
    exact h2
  · have h := (dm_var hU hY hd hi).trans (dm_rhs hY i)
    have h2 : ∑ J : {J : Finset (Fin n) // J.card = i}, dmW U hi J * (∑ j ∈ J.1, y j) ^ 2 =
        ∑ a : Fin n, ∑ b : Fin n, if (b : ℕ) < i ∧ i ≤ (a : ℕ) then ‖Y a b‖ ^ 2 else 0 := by
      exact_mod_cast h
    exact h2
  · intro J
    exact dm_range hU hY hYp J.1

end ReciprocityTheory.ChartRestriction.DS.S7
end
end
end
