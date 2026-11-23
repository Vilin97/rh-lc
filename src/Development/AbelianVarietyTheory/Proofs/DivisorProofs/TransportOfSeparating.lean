module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Mathlib.Geometry.Manifold.StructureGroupoid
import Mathlib.NumberTheory.ModularForms.SlashActions
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportPowerSumsModularFamiliesStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMvPolynomialPickPoint

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

namespace GlobalTheory.QFam

theorem exists_mvPolynomial_pick_point :
    ∀ (S : Type) (T : Finset (S → ℂ)) (p : S → ℂ), ∃ Q : MvPolynomial S ℂ,
      MvPolynomial.eval p Q = 1 ∧ ∀ t ∈ T, t ≠ p → MvPolynomial.eval t Q = 0 := by
  classical
  intro S T p
  induction T using Finset.induction_on with
  | empty => exact ⟨1, by simp, by simp⟩
  | insert a T _ ih =>
    obtain ⟨Q, hQ1, hQ0⟩ := ih
    by_cases hap : a = p
    · refine ⟨Q, hQ1, fun t ht htp => ?_⟩
      rcases Finset.mem_insert.1 ht with rfl | ht
      · exact absurd hap htp
      · exact hQ0 t ht htp
    · obtain ⟨s, hs⟩ := Function.ne_iff.1 hap
      have hne : p s - a s ≠ 0 := sub_ne_zero.2 (Ne.symm hs)
      refine ⟨Q * (MvPolynomial.C (p s - a s)⁻¹ * (MvPolynomial.X s - MvPolynomial.C (a s))),
        ?_, fun t ht htp => ?_⟩
      · simp only [map_mul, map_sub, MvPolynomial.eval_C, MvPolynomial.eval_X, hQ1, one_mul]
        exact inv_mul_cancel₀ hne
      · rcases Finset.mem_insert.1 ht with rfl | ht
        · simp
        · simp [hQ0 t ht htp]

end GlobalTheory.QFam
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPermOfSumMonomialEq

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

namespace GlobalTheory.QFam

theorem sum_eval_eq_of_sum_monomial_eq {ι S : Type} [Fintype ι] [Fintype S] (x y : ι → S → ℂ)
    (h : ∀ μ : S → ℕ, ∑ i, ∏ s, x i s ^ μ s = ∑ i, ∏ s, y i s ^ μ s) (Q : MvPolynomial S ℂ) :
    ∑ i, MvPolynomial.eval (x i) Q = ∑ i, MvPolynomial.eval (y i) Q := by
  simp only [MvPolynomial.eval_eq']
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ)]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.mul_sum, ← Finset.mul_sum, h d]

theorem exists_perm_of_sum_monomial_eq :
    ∀ (ι S : Type) [Fintype ι] [Fintype S] (x y : ι → S → ℂ),
      (∀ μ : S → ℕ, ∑ i, ∏ s, x i s ^ μ s = ∑ i, ∏ s, y i s ^ μ s) →
      ∃ ρ : Equiv.Perm ι, ∀ i, x i = y (ρ i) := by
  classical
  intro ι S _ _ x y h
  have hcard : ∀ p : S → ℂ, Fintype.card {i // x i = p} = Fintype.card {i // y i = p} := by
    intro p
    obtain ⟨Q, hQ1, hQ0⟩ := exists_mvPolynomial_pick_point S
      (Finset.univ.image x ∪ Finset.univ.image y) p
    have key : ∀ z : ι → S → ℂ, (∀ i, z i ∈ Finset.univ.image x ∪ Finset.univ.image y) →
        ∑ i, MvPolynomial.eval (z i) Q = (Fintype.card {i // z i = p} : ℂ) := by
      intro z hz
      have : ∀ i, MvPolynomial.eval (z i) Q = if z i = p then 1 else 0 := by
        intro i
        split_ifs with hi
        · rw [hi, hQ1]
        · exact hQ0 _ (hz i) hi
      simp only [this]
      rw [Finset.sum_boole, Fintype.card_subtype]
    have h1 := key x (fun i => by simp)
    have h2 := key y (fun i => by simp)
    have h3 := sum_eval_eq_of_sum_monomial_eq x y h Q
    rw [h1, h2] at h3
    exact_mod_cast h3
  refine ⟨Equiv.ofFiberEquiv (f := x) (g := y) (fun p => Fintype.equivOfCardEq (hcard p)),
    fun i => ?_⟩
  exact (Equiv.ofFiberEquiv_map _ i).symm

end GlobalTheory.QFam
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPermOfSumMonomialEqStatement

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

theorem _root_.GlobalTheory.T.exists_perm_of_sum_monomial_eq' : ∀ (ι S : Type) [Fintype ι] [Fintype S] (x y : ι → S → ℂ), (∀ μ : S → ℕ, ∑ i, ∏ s, x i s ^ μ s = ∑ i, ∏ s, y i s ^ μ s) → ∃ ρ : Equiv.Perm ι, ∀ i, x i = y (ρ i) := by
  first | exact @GlobalTheory.QFam.exists_perm_of_sum_monomial_eq | exact GlobalTheory.QFam.exists_perm_of_sum_monomial_eq | (intros; apply GlobalTheory.QFam.exists_perm_of_sum_monomial_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPermTransportModularFamiliesValues

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam

theorem exists_perm_transport_families (g : ℂ ≃+* ℂ) (ι S : Type) [Fintype ι] [Fintype S]
    (act : ι → SL(2, ℤ) → ι) (N : ℕ) (m : S → ℕ) (f f' : S → ι → ℍ → ℂ) (τ₀ τ₁ : ℍ)
    (ω₀ ω₁ : ℂ) (hN : 0 < N) (hact : ActBij act) (hf : ∀ s, IsFam act (m s) (f s))
    (hc : ∀ s i, QConj g N (f s i) (f' s i))
    (h4 : g (E₄ τ₀ / ω₀ ^ 4) = E₄ τ₁ / ω₁ ^ 4) (h6 : g (E₆ τ₀ / ω₀ ^ 6) = E₆ τ₁ / ω₁ ^ 6) :
    ∃ ρ : Equiv.Perm ι, ∀ s i, g (f s i τ₀ / ω₀ ^ m s) = f' s (ρ i) τ₁ / ω₁ ^ m s := by
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.exists_perm_of_sum_monomial_eq' ι S (fun i s => g (f s i τ₀ / ω₀ ^ m s))
    (fun i s => f' s i τ₁ / ω₁ ^ m s)
    (GlobalTheory.T.transport_power_sums_modular_families g ι S act N m f f' τ₀ τ₁ ω₀ ω₁ hN hact hf hc h4 h6)
  exact ⟨ρ, fun s i => congrFun (hρ i) s⟩

end GlobalTheory.QFam
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPermTransportModularFamiliesValuesStatement

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.exists_perm_transport_modular_families_values : ∀ (g : ℂ ≃+* ℂ) (ι S : Type) [Fintype ι] [Fintype S] (act : ι → SL(2, ℤ) → ι) (N : ℕ) (m : S → ℕ) (f f' : S → ι → ℍ → ℂ) (τ₀ τ₁ : ℍ) (ω₀ ω₁ : ℂ), 0 < N → ActBij act → (∀ s, IsFam act (m s) (f s)) → (∀ s i, QConj g N (f s i) (f' s i)) → g (E₄ τ₀ / ω₀ ^ 4) = E₄ τ₁ / ω₁ ^ 4 → g (E₆ τ₀ / ω₀ ^ 6) = E₆ τ₁ / ω₁ ^ 6 → ∃ ρ : Equiv.Perm ι, ∀ s i, g (f s i τ₀ / ω₀ ^ m s) = f' s (ρ i) τ₁ / ω₁ ^ m s := by
  first | exact @GlobalTheory.QFam.exists_perm_transport_families | exact GlobalTheory.QFam.exists_perm_transport_families | (intros; apply GlobalTheory.QFam.exists_perm_transport_families <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportOfSeparating

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam

theorem transport_of_separating : ∀ (g : ℂ ≃+* ℂ) (ι S : Type) [Fintype ι] [Fintype S] (act : ι → SL(2, ℤ) → ι) (N w : ℕ) (m : S → ℕ) (f f' : ι → ℍ → ℂ) (u u' : S → ι → ℍ → ℂ) (τ₀ τ₁ : ℍ) (ω₀ ω₁ : ℂ), 0 < N → ActBij act → IsFam act w f → (∀ s, IsFam act (m s) (u s)) → (∀ i, QConj g N (f i) (f' i)) → (∀ s i, QConj g N (u s i) (u' s i)) → ω₀ ≠ 0 → g (E₄ τ₀ / ω₀ ^ 4) = E₄ τ₁ / ω₁ ^ 4 → g (E₆ τ₀ / ω₀ ^ 6) = E₆ τ₁ / ω₁ ^ 6 → ∀ i i' : ι, (∀ j, (∀ s, u s j τ₀ = u s i τ₀) → f j τ₀ = f i τ₀) → (∀ s, g (u s i τ₀ / ω₀ ^ m s) = u' s i' τ₁ / ω₁ ^ m s) → g (f i τ₀ / ω₀ ^ w) = f' i' τ₁ / ω₁ ^ w := by
  intro g ι S _ _ act N w m f f' u u' τ₀ τ₁ ω₀ ω₁ hN hact hf hu hq hqu hω h4 h6 i i' hsep hi
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.exists_perm_transport_modular_families_values g ι (Option S) act N (fun o => o.elim w m)
    (fun o => o.elim f u) (fun o => o.elim f' u') τ₀ τ₁ ω₀ ω₁ hN hact
    (by rintro (_ | s); exacts [hf, hu s])
    (by rintro (_ | s) k; exacts [hq k, hqu s k]) h4 h6
  have hj : f (ρ.symm i') τ₀ = f i τ₀ := by
    apply hsep
    intro s
    have h1 : g (u s (ρ.symm i') τ₀ / ω₀ ^ m s) = u' s (ρ (ρ.symm i')) τ₁ / ω₁ ^ m s :=
      hρ (some s) (ρ.symm i')
    rw [Equiv.apply_symm_apply, ← hi s] at h1
    have h2 := g.injective h1
    exact (div_left_inj' (pow_ne_zero _ hω)).1 h2
  have h3 : g (f (ρ.symm i') τ₀ / ω₀ ^ w) = f' (ρ (ρ.symm i')) τ₁ / ω₁ ^ w :=
    hρ none (ρ.symm i')
  rwa [Equiv.apply_symm_apply, hj] at h3

end GlobalTheory.QFam
end
end
