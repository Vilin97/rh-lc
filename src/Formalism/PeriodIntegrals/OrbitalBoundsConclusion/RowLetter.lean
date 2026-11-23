module

public import Formalism.PeriodIntegrals.RowLetter
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowDerivationChainRule.ChainRule
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowDerivationChainRule.Development
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowDerivationChainRule.DetDer

section

@[expose] public section

open MvPolynomial

noncomputable section

namespace PI.RL.W

section General

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

theorem derivation_finset_prod {ι : Type*} [DecidableEq ι] (D : Derivation R S S) (f : ι → S) (s : Finset ι) :
    D (∏ j ∈ s, f j) = ∑ i ∈ s, ∏ j ∈ s, Function.update f i (D (f i)) j := by
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih
  have hne : ∀ i ∈ s, i ≠ a := fun i hi h => ha (h ▸ hi)
  have h0 : Function.update f a (D (f a)) a = D (f a) := by simp
  have h1 : ∏ j ∈ s, Function.update f a (D (f a)) j = ∏ j ∈ s, f j :=
    Finset.prod_congr rfl fun j hj => Function.update_of_ne (hne j hj) _ _
  have h2 : ∀ i ∈ s, ∏ j ∈ insert a s, Function.update f i (D (f i)) j =
      f a * ∏ j ∈ s, Function.update f i (D (f i)) j := fun i hi => by
    rw [Finset.prod_insert ha, Function.update_of_ne (hne i hi).symm]
  rw [Finset.prod_insert ha, Derivation.leibniz, ih, Finset.sum_insert ha, Finset.prod_insert ha, h0, h1,
    Finset.sum_congr rfl h2, ← Finset.mul_sum, smul_eq_mul, smul_eq_mul]
  ring

theorem derivation_det {n : Type*} [Fintype n] [DecidableEq n] (D : Derivation R S S) (A : Matrix n n S) :
    D A.det = ∑ i, (A.updateRow i fun j => D (A i j)).det := by
  have key : ∀ B : Matrix n n S, B.det = ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : S) * ∏ i, B i (σ i) :=
    fun B => by rw [← Matrix.det_transpose, Matrix.det_apply']; rfl
  have hc : ∀ k : ℤ, D (k : S) = 0 := fun k => by
    rw [← map_intCast (algebraMap R S) k, Derivation.map_algebraMap]
  have hrow : ∀ (i : n) (σ : Equiv.Perm n), ∏ j, (A.updateRow i fun j => D (A i j)) j (σ j) =
      ∏ j, Function.update (fun j => A j (σ j)) i (D (A i (σ i))) j := fun i σ =>
    Finset.prod_congr rfl fun j _ => by
      by_cases h : j = i
      · subst h; simp
      · simp [Matrix.updateRow_ne h, Function.update_of_ne h]

  rw [key, map_sum]
  simp_rw [key, hrow, Derivation.leibniz, hc, smul_zero, add_zero, derivation_finset_prod, smul_eq_mul,
    Finset.mul_sum]
  exact Finset.sum_comm

theorem derivation_sum_apply {ι : Type*} {A M : Type*} [CommSemiring A] [AddCommMonoid M] [Module A M]
    [Algebra R A] [Module R M] (s : Finset ι) (D : ι → Derivation R A M) (x : A) :
    (∑ t ∈ s, D t) x = ∑ t ∈ s, D t x := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]

end General

def REder (K : Type) [CommRing K] (k : ℕ) (a b : Fin k) :
    Derivation K (MvPolynomial (Fin k × Fin k) K) (MvPolynomial (Fin k × Fin k) K) :=
  ∑ t : Fin k, (X (a, t) : MvPolynomial (Fin k × Fin k) K) • pderiv (b, t)

theorem RE_eq_REder (K : Type) [CommRing K] (k : ℕ) (a b : Fin k) (f : MvPolynomial (Fin k × Fin k) K) :
    PI.RL.RE K k a b f = REder K k a b f := by
  unfold PI.RL.RE REder
  rw [derivation_sum_apply]
  rfl

theorem REder_X (K : Type) [CommRing K] (k : ℕ) (a b : Fin k) (i j : Fin k) :
    REder K k a b (X (i, j)) = if i = b then X (a, j) else 0 := by
  unfold REder
  rw [derivation_sum_apply]
  simp only [Derivation.smul_apply, pderiv_X, smul_eq_mul]
  by_cases h : i = b
  · subst h
    simp [Pi.single_apply, mul_ite]
  · simp [Pi.single_apply, h]

end PI.RL.W
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowDerivationChainRule.NvFalseEq

section

@[expose] public section

open MvPolynomial

noncomputable section

namespace PI.RL.W

open PI.RL

theorem Nv_false_eq (K : Type) [Field K] (m : ℕ) (c : Fin (m + 1)) :
    Nv K m false c = ((genM K m).updateRow c (Pi.single (Fin.last m) 1)).det := by
  simp [Nv, Matrix.adjugate_apply]

theorem keyCov : KeyCov := by
  intro K _ m a b c
  have hN : ∀ d, Nv K m false d =
      ((genM K m).updateRow d (Pi.single (Fin.last m) 1)).det := fun d => Nv_false_eq K m d
  have hG : ∀ i j, genM K m i j = X (i, j) := fun i j => rfl
  rw [RE_eq_REder, hN c, hN b, derivation_det]
  have hrow : ∀ i j, REder K (m + 1) a b
      (((genM K m).updateRow c (Pi.single (Fin.last m) 1)) i j) =
        if i = c then 0 else if i = b then X (a, j) else 0 := by
    intro i j
    by_cases hic : i = c
    · subst hic
      rw [Matrix.updateRow_self, if_pos rfl]
      by_cases hj : j = Fin.last m
      · subst hj; simp
      · simp [Pi.single_apply, hj]
    · rw [Matrix.updateRow_ne hic, hG, REder_X, if_neg hic]
  simp_rw [hrow]
  have hz : ∀ (M : Matrix (Fin (m + 1)) (Fin (m + 1)) (MvPolynomial (Fin (m + 1) × Fin (m + 1)) K))
      (i : Fin (m + 1)) (r : Fin (m + 1) → MvPolynomial (Fin (m + 1) × Fin (m + 1)) K),
      (∀ j, r j = 0) → (M.updateRow i r).det = 0 := by
    intro M i r hr
    exact Matrix.det_eq_zero_of_row_eq_zero i (fun j => by rw [Matrix.updateRow_self]; exact hr j)
  by_cases hbc : b = c
  · subst hbc
    rw [Finset.sum_eq_zero]
    · simp
    · intro i _
      apply hz
      intro j
      split_ifs <;> rfl
  rw [Finset.sum_eq_single b]
  rotate_left
  · intro i _ hib
    apply hz
    intro j
    split_ifs <;> rfl
  · intro h; exact absurd (Finset.mem_univ b) h
  simp only [hbc, if_false, if_true, eq_self_iff_true, ite_true, ite_false]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl, if_neg hbc, sub_zero]
    congr 1
    refine Matrix.ext fun i j => ?_
    by_cases hi : i = a
    · rw [hi, Matrix.updateRow_self]
      simp only [Matrix.updateRow_apply, hG]
      try (split_ifs <;> simp_all)
    · rw [Matrix.updateRow_ne hi]
  rw [if_neg hab]
  by_cases hac : a = c
  · subst hac
    rw [if_pos rfl, zero_sub]
    have hperm : (((genM K m).updateRow a (Pi.single (Fin.last m) 1)).updateRow b
        (fun j => X (a, j))) =
        ((genM K m).updateRow b (Pi.single (Fin.last m) 1)).submatrix (Equiv.swap b a) id := by
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.submatrix_apply, id, Matrix.updateRow_apply, Equiv.swap_apply_def, hG]
      split_ifs <;> simp_all
    rw [hperm, Matrix.det_permute, Equiv.Perm.sign_swap hbc]
    simp
  · rw [if_neg hac, sub_zero]
    apply Matrix.det_zero_of_row_eq hab
    funext j
    rw [Matrix.updateRow_ne hab, Matrix.updateRow_self, Matrix.updateRow_ne hac, hG]

end PI.RL.W
end
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.RowLetter

section

@[expose] public section

theorem row_letter_rule : PI.RowLetter :=
  PI.RL.W.rowLetter_of PI.RL.W.chainRule PI.RL.W.vecX PI.RL.W.keyCov PI.RL.W.hdHom
end
end
