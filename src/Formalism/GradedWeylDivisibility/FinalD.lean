module

public import Formalism.GradedWeylDivisibility.StatementD
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.BlockActTensor
import Formalism.GradedWeylDivisibility.StatementD
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LDlatLemmas
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.NablaLKBasis
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.NablaLLe
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.RowActMul
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.SSBasis
import Mathlib.Data.Finsupp.Interval
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.TensorBasis

-- Source module: Formalism.GradedWeylDivisibility.FockSpaceTableaux.NablaLBasis

section

section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem nablaLBasis_of (h : RowActMul) : NablaLBasis := by
  intro R K _ _ _ _ hinj k n ν ι b μ hb g hg
  have hid : ∀ x : MvPolynomial (Fin k × Fin n) K, rowAct K (1 : Matrix (Fin k) (Fin k) K) x = x := by
    intro x
    have e1 : rowAct K (n := n) (1 : Matrix (Fin k) (Fin k) K) = AlgHom.id K _ := by
      apply MvPolynomial.algHom_ext
      intro v
      simp only [rowAct, aeval_X, AlgHom.coe_id, id_eq, Matrix.one_apply]
      rw [Finset.sum_eq_single v.1]
      · simp
      · intro c _ hc
        simp [Ne.symm hc]
      · simp
    rw [e1]
    rfl
  have hinvA : ∀ A : Matrix (Fin k) (Fin k) K, IsUnit A.det → ∀ x : MvPolynomial (Fin k × Fin n) K,
      rowAct K A (rowAct K A⁻¹ x) = x ∧ rowAct K A⁻¹ (rowAct K A x) = x := by
    intro A hA x
    have e1 := congrArg (fun F => F x) (h K k n A A⁻¹)
    have e2 := congrArg (fun F => F x) (h K k n A⁻¹ A)
    simp only [AlgHom.comp_apply] at e1 e2
    rw [Matrix.nonsing_inv_mul A hA] at e1
    rw [Matrix.mul_nonsing_inv A hA] at e2
    exact ⟨e1.trans (hid x), e2.trans (hid x)⟩
  have hφinj : Function.Injective (map (algebraMap R K) : MvPolynomial (Fin k × Fin n) R → _) :=
    MvPolynomial.map_injective _ hinj
  let L : MvPolynomial (Fin k × Fin n) R →ₗ[R] MvPolynomial (Fin k × Fin n) K :=
    ((rowAct K g⁻¹).toLinearMap.restrictScalars R).comp (mapAlgHom (Algebra.ofId R K)).toLinearMap
  have hL : ∀ p, L p = rowAct K g⁻¹ (map (algebraMap R K) p) := fun p => rfl
  have hLinj : Function.Injective L := by
    intro p q hpq
    rw [hL, hL] at hpq
    have e := congrArg (rowAct K g) hpq
    rw [(hinvA g hg _).1, (hinvA g hg _).1] at e
    exact hφinj e
  refine ⟨?_, ?_⟩
  · exact hb.1.map' L (LinearMap.ker_eq_bot.mpr hLinj)
  · have e1 : Set.range (fun i => rowAct K g⁻¹ (map (algebraMap R K) (b i))) = L '' Set.range b := by
      rw [← Set.range_comp]
      rfl
    rw [e1, ← Submodule.map_span, hb.2.1]
    ext F
    unfold nablaL
    rw [Submodule.mem_map, Submodule.mem_comap, Submodule.mem_map]
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨p, hp, ?_⟩
      show map (algebraMap R K) p = rowAct K g (L p)
      rw [hL, (hinvA g hg _).1]
    · rintro ⟨p, hp, hpF⟩
      refine ⟨p, hp, ?_⟩
      have e : map (algebraMap R K) p = rowAct K g F := hpF
      rw [hL, e, (hinvA g hg _).2]

end Formalism.GradedWeylDivisibility
end
end
end

-- Source module: Formalism.GradedWeylDivisibility.FockSpaceTableaux.NablaLDiag

section

@[expose] public section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem nablaLDiag_of (h1 : RowActMul) (h2 : RowActDiagWeight) (h3 : NablaLBasis) : NablaLDiag := by
  intro R K _ _ _ _ hinj k n ν ι b μ hb g t hg ht
  have hD : IsUnit (Matrix.diagonal t).det := by
    rw [Matrix.det_diagonal]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun a _ => ht a)
  have hgD : IsUnit (g * Matrix.diagonal t).det := by
    rw [Matrix.det_mul]
    exact hg.mul hD
  have hDinv : (Matrix.diagonal t)⁻¹ = Matrix.diagonal (fun a => (t a)⁻¹) := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.diagonal_mul_diagonal]
    convert Matrix.diagonal_one with a
    exact inv_mul_cancel₀ (ht a)
  have hfam : (fun i => rowAct K (g * Matrix.diagonal t)⁻¹ (map (algebraMap R K) (b i))) =
      fun i => (∏ a, t a ^ μ i a)⁻¹ • rowAct K g⁻¹ (map (algebraMap R K) (b i)) := by
    funext i
    rw [Matrix.mul_inv_rev, ← h1 K k n g⁻¹ (Matrix.diagonal t)⁻¹, AlgHom.comp_apply, hDinv,
      h2 K k n _ (μ i) _ (ldlat_isWH_map _ (hb.2.2 i)), map_smul]
    congr 1
    rw [← Finset.prod_inv_distrib]
    simp [inv_pow]
  obtain ⟨hl, hs⟩ := h3 R K hinj k n ν b μ hb (g * Matrix.diagonal t) hgD
  rw [hfam] at hl hs
  exact ⟨hl, hs⟩

end Formalism.GradedWeylDivisibility
end
end
end

-- Source module: Formalism.GradedWeylDivisibility.FockSpaceTableaux.NablaLTwMem

section

section

open MvPolynomial

namespace Formalism.GradedWeylDivisibility

theorem nabla_twist_mem : NablaLTwMem := by
  intro R K _ _ _ m lam g hg F
  have hd : g.det ≠ 0 := hg.ne_zero
  unfold nablaLTw nablaL
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨G, hG, rfl⟩
    rw [Submodule.mem_comap] at hG
    change g.det ^ lam (Fin.last m) • rowAct K g (g.det ^ (-(lam (Fin.last m))) • G) ∈ _
    rw [map_smul, smul_smul, ← zpow_add₀ hd, add_neg_cancel, zpow_zero, one_smul]
    exact hG
  · intro hF
    refine ⟨g.det ^ (lam (Fin.last m)) • F, ?_, ?_⟩
    · rw [Submodule.mem_comap]
      change rowAct K g (g.det ^ (lam (Fin.last m)) • F) ∈ _
      rw [map_smul]
      exact hF
    · change g.det ^ (-(lam (Fin.last m))) • g.det ^ (lam (Fin.last m)) • F = F
      rw [smul_smul, ← zpow_add₀ hd, neg_add_cancel, zpow_zero, one_smul]

end Formalism.GradedWeylDivisibility
end
end

-- Source module: Formalism.GradedWeylDivisibility.FockSpaceTableaux.RowActDiagWeight

section

section

open MvPolynomial Finset

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem row_action_diagonal_weight : RowActDiagWeight := by
  intro R _ k n t μ f hf
  have hX : (rowAct R (n := n) (Matrix.diagonal t)) = aeval fun v : Fin k × Fin n => C (t v.1) * X v := by
    unfold rowAct
    congr 1
    funext v
    rw [Finset.sum_eq_single v.1]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  have hwt : ∀ (d : Fin k × Fin n →₀ ℕ) (a : Fin k), Finsupp.weight (rowW k n) d a = ∑ s, d (a, s) := by
    intro d a
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply,
      Fintype.sum_prod_type]
    simp only [rowW, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]

  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hw : Finsupp.weight (rowW k n) d = μ := hf (mem_support_iff.mp hd)
  have hp : (d.prod fun v e => t v.1 ^ e) = ∏ a, t a ^ μ a := by
    rw [← hw, Finsupp.prod_fintype _ _ (by simp), Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [hwt]
    dsimp only
    rw [Finset.prod_pow_eq_pow_sum]
  rw [hX, aeval_monomial, ← hp, smul_eq_C_mul, monomial_eq]
  simp only [mul_pow, Finsupp.prod_mul, map_finsuppProd, map_pow, MvPolynomial.algebraMap_eq]
  ring

end Formalism.GradedWeylDivisibility
end
end
end

-- Source module: Formalism.GradedWeylDivisibility.FockSpaceTableaux.SSIdxFinite

section

@[expose] public section

open MvPolynomial

namespace Formalism.GradedWeylDivisibility

theorem ldbasis_ssIdx_subset_Iic (k n : ℕ) (ν : Fin n → ℕ) :
    ssIdx k n ν ⊆ Set.Iic (Finsupp.equivFunOnFinite.symm (fun v : Fin k × Fin n => ν v.2)) := by
  intro m hm
  simp only [ssIdx, Set.mem_setOf_eq] at hm
  rw [Set.mem_Iic]
  intro v
  obtain ⟨a, t⟩ := v
  show m (a, t) ≤ ν t
  rw [← hm.2 t]
  exact Finset.single_le_sum (f := fun a' => m (a', t)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)

theorem semistandard_index_finite : SSIdxFinite := by
  intro k n ν
  exact (Set.finite_Iic _).subset (ldbasis_ssIdx_subset_Iic k n ν)

end Formalism.GradedWeylDivisibility
end
end

-- Source module: Formalism.GradedWeylDivisibility.FinalD

section

@[expose] public section

namespace Formalism.GradedWeylDivisibility

theorem sSIdxFinite : SSIdxFinite := semistandard_index_finite
theorem sSBasis : SSBasis := semistandard_basis
theorem rowActDiagWeight : RowActDiagWeight := row_action_diagonal_weight
theorem rowActMul : RowActMul := row_action_mul
theorem nablaLLe : NablaLLe := nabla_weight_le
theorem nablaLBasis : NablaLBasis := nablaLBasis_of rowActMul
theorem nablaLKBasis : NablaLKBasis := nablaLKBasis_of rowActMul sSBasis
theorem nablaLDiag : NablaLDiag := nablaLDiag_of rowActMul rowActDiagWeight nablaLBasis
theorem nablaLTwMem : NablaLTwMem := nabla_twist_mem
theorem tensorBasis : TensorBasis := tensor_power_basis
theorem blockActTensor : BlockActTensor := block_action_tensor

end Formalism.GradedWeylDivisibility
end
end
