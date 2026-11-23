module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixMulEntryNormLeUltrametricStatement
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.Analysis.Normed.Group.Ultra

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UltrametricMatrixInvNearOne

section

@[expose] public section

namespace GlobalTheory

theorem matrix_inv_near_one : ∀ (E : Type) [NormedField E] [IsUltrametricDist E] (n : Type) [Fintype n]
    [DecidableEq n] (X Z : Matrix n n E) (t : ℝ), 0 ≤ t → t < 1 → Z * X = 1 →
    (∀ i j, ‖(X - 1) i j‖ ≤ t) → ∀ i j, ‖(Z - 1) i j‖ ≤ t := by
  intro E _ _ n _ _ X Z t ht0 ht1 hZX hX i j
  have key : Z - 1 = -((X - 1) + (Z - 1) * (X - 1)) := by
    have h : (Z - 1) * (X - 1) = Z * X - Z - X + 1 := by noncomm_ring
    rw [h, hZX]; abel
  haveI : Nonempty (n × n) := ⟨(i, j)⟩
  obtain ⟨⟨i0, j0⟩, hmax⟩ := Finite.exists_max (fun p : n × n => ‖(Z - 1) p.1 p.2‖)
  set s := ‖(Z - 1) i0 j0‖ with hs
  have hbound : ∀ a b, ‖(Z - 1) a b‖ ≤ max t (s * t) := by
    intro a b
    have hprod : ‖((Z - 1) * (X - 1)) a b‖ ≤ s * t := by
      rw [Matrix.mul_apply]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
        (mul_nonneg (norm_nonneg _) ht0) fun k _ => ?_
      rw [norm_mul]
      exact mul_le_mul (hmax (a, k)) (hX k b) (norm_nonneg _) (norm_nonneg _)
    rw [key, Matrix.neg_apply, norm_neg, Matrix.add_apply]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max (hX a b) hprod)
  have hs0 : 0 ≤ s := norm_nonneg _
  have hst : s ≤ t := by
    by_contra hlt
    push_neg at hlt
    have h1 := hbound i0 j0
    rw [← hs] at h1
    rcases le_max_iff.mp h1 with h | h
    · linarith
    · nlinarith
  exact (hmax (i, j)).trans hst

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UltrametricMatrixInvNearOneStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.ultrametric_matrix_inv_near_one : ∀ (E : Type) [NormedField E] [IsUltrametricDist E] (n : Type) [Fintype n] [DecidableEq n] (X Z : Matrix n n E) (t : ℝ), 0 ≤ t → t < 1 → Z * X = 1 → (∀ i j, ‖(X - 1) i j‖ ≤ t) → ∀ i j, ‖(Z - 1) i j‖ ≤ t := by
  first | exact @GlobalTheory.matrix_inv_near_one | exact GlobalTheory.matrix_inv_near_one | (intros; apply GlobalTheory.matrix_inv_near_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CongruenceSubgroupsGLPadic

section

@[expose] public section

namespace GlobalTheory

theorem norm_mul_sub_one_le_of_norm_sub_one_le {E : Type} [NormedField E] [IsUltrametricDist E]
    {n : Type} [Fintype n] [DecidableEq n] (X Y : Matrix n n E) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (hX : ∀ i j, ‖(X - 1) i j‖ ≤ t) (hY : ∀ i j, ‖(Y - 1) i j‖ ≤ t) :
    ∀ i j, ‖(X * Y - 1) i j‖ ≤ t := by
  intro i j
  have hXY : X * Y - 1 = (X - 1) + (Y - 1) + (X - 1) * (Y - 1) := by
    simp only [sub_mul, mul_sub, mul_one, one_mul]; abel
  have hp := GlobalTheory.T.norm_mul_apply_le_of_ultrametric E n (X - 1) (Y - 1) t t h0 h0 hX hY i j
  have htt : t * t ≤ t := by nlinarith
  rw [hXY, Matrix.add_apply, Matrix.add_apply]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (hp.trans htt))
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hX i j) (hY i j))

theorem congruenceSubgroups_GL_padic : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n],
    ∃ Γ : ℕ → Subgroup (GL n ℚ_[l]), ∀ k X, X ∈ Γ k ↔
      ∀ i j, ‖((X : Matrix n n ℚ_[l]) - 1) i j‖ ≤ (l : ℝ) ^ (-((k : ℤ) + 2)) := by
  intro l _ n _ _
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have ht : ∀ k : ℕ, 0 ≤ (l : ℝ) ^ (-((k : ℤ) + 2)) ∧ (l : ℝ) ^ (-((k : ℤ) + 2)) < 1 := by
    intro k
    refine ⟨zpow_nonneg (by linarith) _, zpow_lt_one_of_neg₀ hl (by omega)⟩
  refine ⟨fun k => {
    carrier := {X | ∀ i j, ‖((X : Matrix n n ℚ_[l]) - 1) i j‖ ≤ (l : ℝ) ^ (-((k : ℤ) + 2))}
    one_mem' := by
      intro i j
      simpa using (ht k).1
    mul_mem' := by
      intro X Y hX hY
      simp only [Set.mem_setOf_eq, Units.val_mul] at *
      exact norm_mul_sub_one_le_of_norm_sub_one_le _ _ _ (ht k).1 (ht k).2.le hX hY
    inv_mem' := by
      intro X hX
      simp only [Set.mem_setOf_eq] at *
      exact GlobalTheory.T.ultrametric_matrix_inv_near_one ℚ_[l] n (X : Matrix n n ℚ_[l]) ((X⁻¹ : GL n ℚ_[l]) : Matrix n n ℚ_[l]) _
        (ht k).1 (ht k).2 (Units.inv_mul X) hX }, fun k X => Iff.rfl⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CongruenceSubgroupsGLPadicStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.exists_congruenceSubgroups_GL_padic : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n], ∃ Γ : ℕ → Subgroup (GL n ℚ_[l]), ∀ k X, X ∈ Γ k ↔ ∀ i j, ‖((X : Matrix n n ℚ_[l]) - 1) i j‖ ≤ (l : ℝ) ^ (-((k : ℤ) + 2)) := by
  first | exact @GlobalTheory.congruenceSubgroups_GL_padic | exact GlobalTheory.congruenceSubgroups_GL_padic | (intros; apply GlobalTheory.congruenceSubgroups_GL_padic <;> assumption)
end
end
