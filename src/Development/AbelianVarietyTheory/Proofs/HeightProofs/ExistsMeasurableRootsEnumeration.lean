module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Basic.Complex.Basic
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
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsProdXSubCOfMonic

section

@[expose] public section

open Polynomial

namespace GlobalTheory.MonicRootsProduct

theorem exists_prod_X_sub_C_of_monic (p : ℂ[X]) (hm : p.Monic) :
    ∃ r : Fin p.natDegree → ℂ, ∏ j, (X - C (r j)) = p := by
  classical
  have hc : p.roots.toList.length = p.natDegree := by
    rw [Multiset.length_toList, IsAlgClosed.card_roots_eq_natDegree]
  refine ⟨fun j => p.roots.toList[(j : ℕ)]'(by rw [hc]; exact j.2), ?_⟩
  have hprod := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm
    IsAlgClosed.card_roots_eq_natDegree
  rw [← Multiset.coe_toList p.roots, Multiset.map_coe, Multiset.prod_coe,
    ← Fin.prod_univ_fun_getElem] at hprod
  exact (Fintype.prod_equiv (finCongr hc.symm) _ _ (fun j => rfl)).trans hprod

theorem exists_roots {δ : ℕ} (c : Fin δ → ℂ) :
    ∃ r : Fin δ → ℂ, ∏ j : Fin δ, (X - C (r j)) =
      X ^ δ + ∑ i : Fin δ, C (c i) * X ^ (i : ℕ) := by
  have hdeg := Polynomial.degree_sum_fin_lt c
  have hmon : (X ^ δ + ∑ i : Fin δ, C (c i) * X ^ (i : ℕ)).Monic := Polynomial.monic_X_pow_add hdeg
  have hd : (X ^ δ + ∑ i : Fin δ, C (c i) * X ^ (i : ℕ)).natDegree = δ := by
    rw [Polynomial.natDegree_add_eq_left_of_degree_lt (by rwa [Polynomial.degree_X_pow]),
      Polynomial.natDegree_X_pow]
  obtain ⟨r, hr⟩ := exists_prod_X_sub_C_of_monic _ hmon
  exact ⟨fun j => r (Fin.cast hd.symm j),
    (Fintype.prod_equiv (finCongr hd.symm) _ _ (fun j => rfl)).trans hr⟩

end GlobalTheory.MonicRootsProduct
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsMeasurableRootsEnumeration

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct

namespace GlobalTheory

open Polynomial

theorem continuous_coeff_prod_X_sub_C {ι : Type} (s : Finset ι) (n : ℕ) :
    Continuous fun r : ι → ℂ => (∏ j ∈ s, (X - C (r j))).coeff n := by
  classical
  induction s using Finset.induction_on generalizing n with
  | empty => simpa using continuous_const
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha, coeff_mul]
    refine continuous_finsetSum _ fun p _ => Continuous.mul ?_ (ih _)
    simp only [coeff_sub, coeff_C]
    refine continuous_const.sub ?_
    split_ifs
    · exact continuous_apply a
    · exact continuous_const

theorem prod_X_sub_C_eq_X_pow_add_sum {δ : ℕ} (r : Fin δ → ℂ) :
    ∏ j, (X - C (r j)) =
      X ^ δ + ∑ i : Fin δ, C ((∏ j, (X - C (r j))).coeff i) * X ^ (i : ℕ) := by
  have hm : (∏ j, (X - C (r j)) : ℂ[X]).Monic :=
    monic_prod_of_monic _ _ fun j _ => monic_X_sub_C _
  have hd : (∏ j, (X - C (r j)) : ℂ[X]).natDegree = δ := by
    rw [natDegree_prod_of_monic _ _ fun j _ => monic_X_sub_C _]
    simp
  have := hm.as_sum
  rw [hd, Finset.sum_range] at this
  exact this

theorem exists_prod_X_sub_C_eq {δ : ℕ} (c : Fin δ → ℂ) :
    ∃ r : Fin δ → ℂ,
      ∏ j, (X - C (r j)) = X ^ δ + ∑ i : Fin δ, C (c i) * X ^ (i : ℕ) := by
  first
  | exact @_root_.GlobalTheory.MonicRootsProduct.exists_roots
  | exact _root_.GlobalTheory.MonicRootsProduct.exists_roots
  | (apply _root_.GlobalTheory.MonicRootsProduct.exists_roots <;> assumption)
  | (intros; apply _root_.GlobalTheory.MonicRootsProduct.exists_roots <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MonicRootsProduct.exists_roots <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MonicRootsProduct.exists_roots ..)

theorem exists_measurable_roots_enumeration :
    ∀ δ : ℕ, ∃ ρ : (Fin δ → ℂ) → (Fin δ → ℂ), Measurable ρ ∧ ∀ c : Fin δ → ℂ,
      ∏ i, (Polynomial.X - Polynomial.C (ρ c i)) =
        Polynomial.X ^ δ + ∑ i : Fin δ, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ) := by
  intro δ
  let e : ℂ ≃ᵐ ℝ := PolishSpace.measurableEquivOfNotCountable
    (fun _ => not_countable_iff.mpr (inferInstance : Uncountable ℝ)
      Complex.ofReal_injective.countable) (not_countable_iff.mpr inferInstance)
  let S : Set (Fin δ → ℂ) := {r | Monotone (e ∘ r)}
  have hS : MeasurableSet S := by
    have : S = ⋂ i, ⋂ j, ⋂ _ : i ≤ j, {r : Fin δ → ℂ | e (r i) ≤ e (r j)} := by
      ext r
      simp only [S, Set.mem_setOf_eq, Set.mem_iInter, Monotone, Function.comp]
    rw [this]
    refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun _ => measurableSet_le ?_ ?_
    · exact e.measurable.comp (measurable_pi_apply i)
    · exact e.measurable.comp (measurable_pi_apply j)
  let V : (Fin δ → ℂ) → (Fin δ → ℂ) := fun r i => (∏ j, (X - C (r j))).coeff i
  have hV : Measurable V :=
    (continuous_pi fun i => continuous_coeff_prod_X_sub_C _ _).measurable
  haveI : StandardBorelSpace S := hS.standardBorel
  have hinj : Function.Injective fun x : S => V x := by
    rintro ⟨r, hr⟩ ⟨s, hs⟩ h
    have h1 : (∏ j, (X - C (r j)) : ℂ[X]) = ∏ j, (X - C (s j)) := by
      refine (prod_X_sub_C_eq_X_pow_add_sum r).trans
        (Eq.trans ?_ (prod_X_sub_C_eq_X_pow_add_sum s).symm)
      refine congrArg (X ^ δ + ·) (Finset.sum_congr rfl fun i _ => ?_)
      exact congrArg (fun a => C a * X ^ (i : ℕ)) (congrFun h i)
    have h2 : Finset.univ.val.map r = Finset.univ.val.map s := by
      rw [← roots_multiset_prod_X_sub_C (Finset.univ.val.map r),
        ← roots_multiset_prod_X_sub_C (Finset.univ.val.map s), Multiset.map_map,
        Multiset.map_map]
      exact congrArg roots h1
    have h3 : Finset.univ.val.map (e ∘ r) = Finset.univ.val.map (e ∘ s) := by
      rw [← Multiset.map_map, ← Multiset.map_map, h2]
    rw [Fin.univ_val_map, Fin.univ_val_map, Multiset.coe_eq_coe] at h3
    have h4 := List.ofFn_injective
      (h3.eq_of_sortedLE (List.sortedLE_ofFn_iff.mpr hr) (List.sortedLE_ofFn_iff.mpr hs))
    ext i
    exact e.injective (congrFun h4 i)
  have hemb : MeasurableEmbedding fun x : S => V x :=
    (hV.comp measurable_subtype_coe).measurableEmbedding hinj
  obtain ⟨ρ, hρ, hρV⟩ := hemb.exists_measurable_extend (g := fun x : S => (x : Fin δ → ℂ))
    measurable_subtype_coe fun _ => inferInstance
  refine ⟨ρ, hρ, fun c => ?_⟩
  obtain ⟨r, hr⟩ := exists_prod_X_sub_C_eq c
  have hrS : r ∘ Tuple.sort (e ∘ r) ∈ S := Tuple.monotone_sort (e ∘ r)
  have hp : (∏ j, (X - C ((r ∘ Tuple.sort (e ∘ r)) j)) : ℂ[X])
      = X ^ δ + ∑ i : Fin δ, C (c i) * X ^ (i : ℕ) := by
    rw [← hr]
    exact Equiv.prod_comp (Tuple.sort (e ∘ r)) fun j => X - C (r j)
  have hc : V (r ∘ Tuple.sort (e ∘ r)) = c := by
    funext i
    simp only [V]
    rw [hp, coeff_add, coeff_X_pow, if_neg i.2.ne, zero_add, Polynomial.finsetSum_coeff]
    simp only [coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      exact if_neg fun h => hj (Fin.ext h.symm)
    · simp
  have : ρ c = r ∘ Tuple.sort (e ∘ r) := by
    rw [← hc]
    exact congrFun hρV ⟨_, hrS⟩
  rw [this, hp]

end GlobalTheory
end
end
