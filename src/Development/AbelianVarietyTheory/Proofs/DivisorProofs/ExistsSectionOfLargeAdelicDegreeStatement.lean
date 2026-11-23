module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceLocalIndexScaledUniformiserStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceOrderCalculusStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannInequalityCofinalFunctionField
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroLinearCombinationMemCommonKernel

section

@[expose] public section

open GlobalTheory.Nef

namespace GlobalTheory

theorem exists_ne_zero_comb_mem_ker :
    ∀ (k F ι : Type) [Field k] [Field F] [Algebra k F] (n m : ℕ) (f : Fin m → F),
  LinearIndependent k f → ∀ (S : Finset ι) (N : ι → ℕ) (ψ : ∀ v, (Fin n → F) →ₗ[k] (Fin (N v) → k)),
    ∑ v ∈ S, N v < n * m → ∃ c : Fin n → Fin m → k, (fun i => ∑ j, c i j • f j) ≠ 0 ∧
      ∀ v ∈ S, ψ v (fun i => ∑ j, c i j • f j) = 0 := by
  intro k F ι _ _ _ n m f hf S N ψ hlt
  let T : (Fin n → Fin m → k) →ₗ[k] (Fin n → F) :=
    { toFun := fun c i => ∑ j, c i j • f j
      map_add' := by
        intro a b; funext i; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro r a; funext i; simp [Finset.smul_sum, smul_smul] }
  have hT : ∀ c, T c = fun i => ∑ j, c i j • f j := fun c => rfl
  let Ψ : (Fin n → Fin m → k) →ₗ[k] ((v : S) → Fin (N v) → k) :=
    LinearMap.pi fun v => (ψ v).comp T
  have hlt' : Module.finrank k ((v : S) → Fin (N v) → k) < Module.finrank k (Fin n → Fin m → k) := by
    rw [Module.finrank_pi_fintype]
    simp only [Module.finrank_fin_fun]
    rw [Finset.sum_coe_sort S (fun v => N v), Module.finrank_pi_fintype]
    simpa [Module.finrank_fin_fun] using hlt
  have hk : LinearMap.ker Ψ ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hlt'
  obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff _).1 hk
  refine ⟨c, ?_, ?_⟩
  · intro h0
    apply hc0
    funext i j
    have hi : ∑ j, c i j • f j = 0 := congrFun h0 i
    exact Fintype.linearIndependent_iff.1 hf (c i) hi j
  · intro v hv
    have := congrFun (LinearMap.mem_ker.1 hc) ⟨v, hv⟩
    simpa [Ψ, hT] using this

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroLinearCombinationMemCommonKernelStatement

section

@[expose] public section

open GlobalTheory.Nef


theorem _root_.GlobalTheory.T.exists_ne_zero_linear_combination_mem_common_kernel : ∀ (k F ι : Type) [Field k] [Field F] [Algebra k F] (n m : ℕ) (f : Fin m → F),
  LinearIndependent k f → ∀ (S : Finset ι) (N : ι → ℕ) (ψ : ∀ v, (Fin n → F) →ₗ[k] (Fin (N v) → k)),
    ∑ v ∈ S, N v < n * m → ∃ c : Fin n → Fin m → k, (fun i => ∑ j, c i j • f j) ≠ 0 ∧
      ∀ v ∈ S, ψ v (fun i => ∑ j, c i j • f j) = 0 := by
  first | exact @GlobalTheory.exists_ne_zero_comb_mem_ker | exact GlobalTheory.exists_ne_zero_comb_mem_ker | (intros; apply GlobalTheory.exists_ne_zero_comb_mem_ker <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannInequalityCofinalFunctionFieldStatement

section

@[expose] public section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef


theorem _root_.GlobalTheory.T.riemann_inequality_cofinal_functionField : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∃ γ : ℕ, ∀ D : Place k F →₀ ℤ, ∃ D' : Place k F →₀ ℤ, D ≤ D' ∧ ∃ (n : ℕ) (f : Fin n → F), LinearIndependent k f ∧ (D'.sum fun _ m => m) - γ ≤ n ∧ ∀ (i : Fin n) (v : Place k F), -D' v ≤ ord v (f i) := by
  first | exact @GlobalTheory.Nef.riemann_cofinal | exact GlobalTheory.Nef.riemann_cofinal | (intros; apply GlobalTheory.Nef.riemann_cofinal <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionOfLargeAdelicDegree

section

@[expose] public section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

variable {k F : Type} [Field k] [Field F] [Algebra k F]

theorem val_le_exp_of_ord (v : Place k F) (x : F) (d : ℤ) (hd : 0 ≤ d) (h : -d ≤ ord v x) :
    v.1 x ≤ WithZero.exp d := by
  by_cases hx : v.1 x = 0
  · rw [hx]; exact zero_le'
  · rw [← WithZero.exp_log hx, WithZero.exp_le_exp]
    unfold ord at h; omega

theorem val_algebraMap_le_one (v : Place k F) (c : k) : v.1 (algebraMap k F c) ≤ 1 := by
  by_cases hc : c = 0
  · simp [hc]
  · exact (v.2.2 c hc).le

theorem val_comb_le (v : Place k F) {m : ℕ} (f : Fin m → F) (c : Fin m → k)
    (B : WithZero (Multiplicative ℤ)) (h : ∀ j, v.1 (f j) ≤ B) : v.1 (∑ j, c j • f j) ≤ B := by
  apply v.1.map_sum_le
  intro j _
  rw [Algebra.smul_def, map_mul]
  calc v.1 (algebraMap k F (c j)) * v.1 (f j) ≤ 1 * B := mul_le_mul' (val_algebraMap_le_one v _) (h j)
    _ = B := one_mul B

theorem val_mulVec_le_one (v : Place k F) {n : ℕ} (M : Matrix (Fin n) (Fin n) F)
    (hM : ∀ i j, v.1 (M i j) ≤ 1) (p : Fin n → F) (hp : ∀ i, v.1 (p i) ≤ 1) (i : Fin n) :
    v.1 (M.mulVec p i) ≤ 1 := by
  simp only [Matrix.mulVec, dotProduct]
  apply v.1.map_sum_le
  intro j _
  rw [map_mul]
  calc v.1 (M i j) * v.1 (p j) ≤ 1 * 1 := mul_le_mul' (hM i j) (hp j)
    _ = 1 := one_mul 1

theorem exists_exp_bound (v : Place k F) {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    ∃ d : ℕ, ∀ i j, v.1 (M i j) ≤ WithZero.exp (d : ℤ) := by
  refine ⟨Finset.univ.sup fun ij : Fin n × Fin n => (WithZero.log (v.1 (M ij.1 ij.2))).toNat,
    fun i j => ?_⟩
  by_cases hx : v.1 (M i j) = 0
  · rw [hx]; exact zero_le'
  · rw [← WithZero.exp_log hx, WithZero.exp_le_exp]
    have := Finset.le_sup (f := fun ij : Fin n × Fin n => (WithZero.log (v.1 (M ij.1 ij.2))).toNat)
      (Finset.mem_univ (i, j))
    simp only at this
    omega

theorem exists_section_of_large_deg : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∃ γ : ℕ, ∀ (n : ℕ) (g : Place k F → Matrix (Fin n) (Fin n) F), admitted g → (n : ℤ) * γ < deg g → ∃ p : Fin n → F, p ≠ 0 ∧ ∀ (v : Place k F) (i : Fin n), v.1 ((g v).mulVec p i) ≤ 1 := by
  intro k F _ _ _ _ _ hFF
  obtain ⟨γ, hγ⟩ := GlobalTheory.T.riemann_inequality_cofinal_functionField k F hFF
  refine ⟨γ, fun n g hg hdeg => ?_⟩
  classical
  set B := hg.2.toFinset with hBdef
  choose d0 hd0 using fun v => exists_exp_bound v (g v)⁻¹
  let D : Place k F →₀ ℤ := Finsupp.onFinset B (fun v => if v ∈ B then (d0 v : ℤ) else 0)
    (by intro v hv; by_contra h; exact hv (if_neg h))
  obtain ⟨D', hDD', m, f, hf, hm, hford⟩ := hγ D
  have hD0 : ∀ v, 0 ≤ D' v := fun v => le_trans
    (by simp only [D, Finsupp.onFinset_apply]; split_ifs <;> omega) (hDD' v)
  have hloc : ∀ v, ∃ (N : ℕ) (φ : (Fin n → F) →ₗ[k] (Fin N → k)),
      (N : ℤ) = n * ((D' v).toNat : ℕ) - ord v (g v).det ∧
      ∀ p : Fin n → F, (∀ i, v.1 (p i) ≤ WithZero.exp (((D' v).toNat : ℕ) : ℤ)) → φ p = 0 →
        ∀ i, v.1 ((g v).mulVec p i) ≤ 1 := by
    intro v
    refine GlobalTheory.T.functionFieldPlace_localIndex_scaled_uniformiser k F hFF v n (g v) _ (hg.1 v) ?_
    intro i j
    by_cases hv : v ∈ B
    · have hDv : D v = d0 v := by simp [D, Finsupp.onFinset_apply, hv]
      calc v.1 ((g v)⁻¹ i j) ≤ WithZero.exp (d0 v : ℤ) := hd0 v i j
        _ ≤ _ := by
          rw [WithZero.exp_le_exp]; have := hDD' v; rw [hDv] at this; omega
    · have hU : Unimod v (g v) := by simpa [B] using hv
      have hU' := ((GlobalTheory.T.functionFieldPlaceOrder_calculus k F v).2.2.2.2.2.2.2.2.2 n (g v) (g v) hU hU).2
      calc v.1 ((g v)⁻¹ i j) ≤ 1 := hU'.1 i j
        _ = WithZero.exp 0 := rfl
        _ ≤ _ := by rw [WithZero.exp_le_exp]; omega
  choose N φ hN hφ using hloc
  set S := B ∪ D'.support with hS
  have hsumD : D'.sum (fun _ m => m) = ∑ v ∈ S, D' v := by
    unfold Finsupp.sum
    apply Finset.sum_subset Finset.subset_union_right
    intro v _ hv; simpa using hv
  have hdegS : deg g = ∑ v ∈ S, ord v (g v).det := by
    unfold deg
    apply finsum_eq_sum_of_support_subset
    intro v hv
    rw [Finset.coe_union]; left
    simp only [B, Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    intro hU; apply hv
    simp [ord, hU.2]
  have hNsum : ((∑ v ∈ S, N v : ℕ) : ℤ) < n * m := by
    push_cast
    rw [Finset.sum_congr rfl (fun v _ => hN v), Finset.sum_sub_distrib, ← Finset.mul_sum]
    have : ∀ v, (((D' v).toNat : ℕ) : ℤ) = D' v := fun v => Int.toNat_of_nonneg (hD0 v)
    simp_rw [this]
    rw [← hsumD, ← hdegS]
    have := mul_le_mul_of_nonneg_left hm (Int.natCast_nonneg n)
    nlinarith
  obtain ⟨c, hp0, hpψ⟩ := GlobalTheory.T.exists_ne_zero_linear_combination_mem_common_kernel k F (Place k F) n m f hf S N φ (by exact_mod_cast hNsum)
  refine ⟨_, hp0, fun v i => ?_⟩
  have hpb : ∀ i, v.1 (∑ j, c i j • f j) ≤ WithZero.exp (((D' v).toNat : ℕ) : ℤ) := fun i =>
    val_comb_le v f (c i) _ (fun j => val_le_exp_of_ord v _ _ (by omega)
      (by rw [Int.toNat_of_nonneg (hD0 v)]; exact hford j v))
  by_cases hv : v ∈ S
  · exact hφ v _ hpb (hpψ v hv) i
  · have hvB : v ∉ B := fun h => hv (Finset.mem_union_left _ h)
    have hD'v : D' v = 0 := by
      by_contra h; exact hv (Finset.mem_union_right _ (Finsupp.mem_support_iff.2 h))
    have hU : Unimod v (g v) := by simpa [B] using hvB
    apply val_mulVec_le_one v _ hU.1
    intro i; have := hpb i; rw [hD'v] at this; simpa using this

end GlobalTheory.Nef
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionOfLargeAdelicDegreeStatement

section

@[expose] public section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef


theorem _root_.GlobalTheory.T.exists_section_of_large_adelic_degree : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∃ γ : ℕ, ∀ (n : ℕ) (g : Place k F → Matrix (Fin n) (Fin n) F), admitted g → (n : ℤ) * γ < deg g → ∃ p : Fin n → F, p ≠ 0 ∧ ∀ (v : Place k F) (i : Fin n), v.1 ((g v).mulVec p i) ≤ 1 := by
  first | exact @GlobalTheory.Nef.exists_section_of_large_deg | exact GlobalTheory.Nef.exists_section_of_large_deg | (intros; apply GlobalTheory.Nef.exists_section_of_large_deg <;> assumption)
end
end
