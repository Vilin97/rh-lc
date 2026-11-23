module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.EntryMulSubOne
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
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
public import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.FirstLemmaE

section

@[expose] public section

namespace Bl.FirstLemmaE

theorem goal1 :
  ∀ {L : Type} [inst : NontriviallyNormedField.{0} L] [IsUltrametricDist.{0} L] {ι : Type} (s : Finset.{0} ι)
  (f g : ι → L) {r : Real},
  LE.le.{0} 0 r →
    (∀ (i : ι), LE.le.{0} (Norm.norm.{0} (f i)) 1) →
      (∀ (i : ι), LE.le.{0} (Norm.norm.{0} (g i)) 1) →
        (∀ (i : ι), LE.le.{0} (Norm.norm.{0} (HSub.hSub.{0, 0, 0} (f i) (g i))) r) →
          LE.le.{0}
            (Norm.norm.{0}
              (HSub.hSub.{0, 0, 0} (Finset.prod.{0, 0} s fun (i : ι) ↦ f i) (Finset.prod.{0, 0} s fun (i : ι) ↦ g i)))
            r := by
  intro L _ _ ι s f g r hr hf hg hfg
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hr
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hG : ‖∏ i ∈ t, g i‖ ≤ 1 := by
      rw [norm_prod]
      exact Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => hg i)
    have key : f a * ∏ i ∈ t, f i - g a * ∏ i ∈ t, g i
        = f a * (∏ i ∈ t, f i - ∏ i ∈ t, g i) + (f a - g a) * ∏ i ∈ t, g i := by ring
    rw [key]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      calc ‖f a‖ * ‖∏ i ∈ t, f i - ∏ i ∈ t, g i‖ ≤ 1 * r :=
            mul_le_mul (hf a) ih (norm_nonneg _) zero_le_one
        _ = r := one_mul r
    · rw [norm_mul]
      calc ‖f a - g a‖ * ‖∏ i ∈ t, g i‖ ≤ r * 1 :=
            mul_le_mul (hfg a) hG (norm_nonneg _) hr
        _ = r := mul_one r

end Bl.FirstLemmaE
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MatrixNearIdentityInCongruenceSubgroup

section

@[expose] public section

noncomputable section

open Matrix

namespace GlobalTheory.CompanionTheory.CartGL

section SlopeTestRemainingChoices

variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {n : ℕ}

theorem norm_prod_sub_prod_le {ι : Type} (s : Finset ι) (f g : ι → L) {r : ℝ} (h0 : 0 ≤ r)
    (hf : ∀ i, ‖f i‖ ≤ 1) (hg : ∀ i, ‖g i‖ ≤ 1) (hfg : ∀ i, ‖f i - g i‖ ≤ r) :
    ‖∏ i ∈ s, f i - ∏ i ∈ s, g i‖ ≤ r :=
  _root_.Bl.FirstLemmaE.goal1 s f g h0 hf hg hfg

theorem norm_det_sub_det_le {A B : Matrix (Fin n) (Fin n) L} {r : ℝ} (h0 : 0 ≤ r)
    (hA : ∀ i j, ‖A i j‖ ≤ 1) (hB : ∀ i j, ‖B i j‖ ≤ 1) (hAB : ∀ i j, ‖(A - B) i j‖ ≤ r) :
    ‖A.det - B.det‖ ≤ r := by
  rw [Matrix.det_apply, Matrix.det_apply, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg h0 fun σ _ => ?_
  rw [← smul_sub]
  have h := norm_prod_sub_prod_le Finset.univ (fun i => A (σ i) i) (fun i => B (σ i) i) h0
    (fun i => hA _ _) (fun i => hB _ _) (fun i => by simpa using hAB (σ i) i)
  have h' : ‖∏ i, B (σ i) i - ∏ i, A (σ i) i‖ ≤ r := by
    rw [norm_sub_rev]
    exact h
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · simpa [hs, Units.smul_def] using h
  · simpa [hs, Units.smul_def] using h'

theorem norm_det_le_one {A : Matrix (Fin n) (Fin n) L} (hA : ∀ i j, ‖A i j‖ ≤ 1) : ‖A.det‖ ≤ 1 := by
  rw [Matrix.det_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  have h : ‖∏ i, A (σ i) i‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => hA _ _
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simpa [hs, Units.smul_def] using h

theorem norm_one_entry_le (i j : Fin n) : ‖(1 : Matrix (Fin n) (Fin n) L) i j‖ ≤ 1 := by
  by_cases h : i = j
  · subst h
    rw [Matrix.one_apply_eq, norm_one]
  · rw [Matrix.one_apply_ne h, norm_zero]
    exact zero_le_one

theorem norm_adjugate_entry_le {A : Matrix (Fin n) (Fin n) L} (hA : ∀ i j, ‖A i j‖ ≤ 1) (i j : Fin n) :
    ‖A.adjugate i j‖ ≤ 1 := by
  rw [Matrix.adjugate_apply]
  refine norm_det_le_one fun a b => ?_
  by_cases h : a = j
  · subst h
    rw [Matrix.updateRow_self]
    by_cases h' : b = i
    · simp [h']
    · simp [Pi.single_eq_of_ne h']
  · rw [Matrix.updateRow_ne h]
    exact hA a b

end SlopeTestRemainingChoices

theorem exists_mem_congK_of_entries : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L]
    (n : ℕ) (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1), r < 1 → ∀ A : Matrix (Fin n) (Fin n) L,
    (∀ i j, ‖(A - 1) i j‖ ≤ r) →
    ∃ k ∈ GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1, (k : Matrix (Fin n) (Fin n) L) = A := by
  intro L _ _ n r h0 h1 hr A hA
  have hA1 : ∀ i j, ‖A i j‖ ≤ 1 := by
    intro i j
    have e : A i j = (A - 1) i j + (1 : Matrix (Fin n) (Fin n) L) i j := by simp
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le ((hA i j).trans h1) (norm_one_entry_le i j))
  have hd : ‖A.det - 1‖ ≤ r := by
    have := norm_det_sub_det_le h0 hA1 norm_one_entry_le hA
    rwa [Matrix.det_one] at this
  have hd1 : 1 ≤ ‖A.det‖ := by
    have e : (1 : L) = A.det + -(A.det - 1) := by ring
    have h2 : ‖(1 : L)‖ ≤ max ‖A.det‖ ‖A.det - 1‖ := by
      conv_lhs => rw [e]
      rw [← norm_neg (A.det - 1)]
      exact IsUltrametricDist.norm_add_le_max _ _
    rw [norm_one] at h2
    rcases le_max_iff.mp h2 with h | h
    · exact h
    · linarith
  have hne : A.det ≠ 0 := by
    intro h
    rw [h, norm_zero] at hd1
    linarith
  have hinv : ∀ i j, ‖A⁻¹ i j‖ ≤ 1 := by
    intro i j
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv]
    exact mul_le_one₀ (inv_le_one_of_one_le₀ hd1) (norm_nonneg _) (norm_adjugate_entry_le hA1 i j)
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hne
  have hk : ((Matrix.GeneralLinearGroup.mkOfDetNeZero A hne : GL (Fin n) L) :
      Matrix (Fin n) (Fin n) L) = A := rfl
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hne, ?_, hk⟩
  rw [mem_congK]
  intro i j
  refine ⟨by rw [hk]; exact hA i j, ?_⟩
  rw [Matrix.coe_units_inv, hk]
  have e : A⁻¹ - 1 = -(A⁻¹ * (A - 1)) := by
    rw [Matrix.mul_sub, Matrix.nonsing_inv_mul A hu, Matrix.mul_one]
    abel
  rw [e, Matrix.neg_apply, norm_neg]
  simpa using entry_mul zero_le_one h0 hinv hA i j

end GlobalTheory.CompanionTheory.CartGL
end
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MatrixNearIdentityInCongruenceSubgroupStatement

section

@[expose] public section

open Matrix

theorem _root_.GlobalTheory.T.matrix_near_identity_in_congruence_subgroup : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1), r < 1 → ∀ A : Matrix (Fin n) (Fin n) L, (∀ i j, ‖(A - 1) i j‖ ≤ r) → ∃ k ∈ GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1, (k : Matrix (Fin n) (Fin n) L) = A := by
  first | exact @GlobalTheory.CompanionTheory.CartGL.exists_mem_congK_of_entries | exact GlobalTheory.CompanionTheory.CartGL.exists_mem_congK_of_entries | (intros; apply GlobalTheory.CompanionTheory.CartGL.exists_mem_congK_of_entries <;> assumption)
end
end
