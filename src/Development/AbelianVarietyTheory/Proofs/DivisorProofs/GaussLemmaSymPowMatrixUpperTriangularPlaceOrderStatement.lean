module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistAtOfNe
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NrmCoeffProdLinear

section

@[expose] public section

set_option autoImplicit false

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef


open Polynomial in
theorem coeff_max_mul_linear {F Γ : Type} [Field F] [LinearOrderedCommGroupWithZero Γ] (v : Valuation F Γ)
    (p : F[X]) (N : Γ) (α β : F) (h1 : ∀ i, v (p.coeff i) ≤ N) (h2 : ∃ i, v (p.coeff i) = N) :
    (∀ i, v (((C α + C β * X) * p).coeff i) ≤ max (v α) (v β) * N) ∧
      ∃ i, v (((C α + C β * X) * p).coeff i) = max (v α) (v β) * N := by
  classical
  have c0 : ((C α + C β * X) * p).coeff 0 = α * p.coeff 0 := by
    simp [add_mul, mul_assoc]
  have cs : ∀ i, ((C α + C β * X) * p).coeff (i + 1) = α * p.coeff (i + 1) + β * p.coeff i := by
    intro i
    simp [add_mul, mul_assoc, coeff_X_mul]
  have hle : ∀ i, v (((C α + C β * X) * p).coeff i) ≤ max (v α) (v β) * N := by
    intro i
    cases i with
    | zero =>
      rw [c0, map_mul]
      exact mul_le_mul' (le_max_left _ _) (h1 _)
    | succ i =>
      rw [cs]
      refine v.map_add_le ?_ ?_
      · rw [map_mul]; exact mul_le_mul' (le_max_left _ _) (h1 _)
      · rw [map_mul]; exact mul_le_mul' (le_max_right _ _) (h1 _)
  refine ⟨hle, ?_⟩
  by_cases hz : max (v α) (v β) * N = 0
  · exact ⟨0, le_antisymm (hle 0) (hz ▸ zero_le')⟩
  have hM : max (v α) (v β) ≠ 0 := left_ne_zero_of_mul hz
  have hN : N ≠ 0 := right_ne_zero_of_mul hz
  rcases le_or_gt (v β) (v α) with h | h
  · rw [max_eq_left h] at hM ⊢
    have hs := Nat.find_spec h2
    have hm := fun j => @Nat.find_min _ _ h2 j
    refine ⟨Nat.find h2, ?_⟩
    generalize Nat.find h2 = i at hs hm
    cases i with
    | zero => rw [c0, map_mul, hs]
    | succ i =>
      have hlt : v (p.coeff i) < N := lt_of_le_of_ne (h1 i) (hm i (Nat.lt_succ_self i))
      rw [cs, v.map_add_eq_of_lt_left, map_mul, hs]
      rw [map_mul, map_mul, hs]
      calc v β * v (p.coeff i) ≤ v α * v (p.coeff i) := mul_le_mul' h le_rfl
        _ < v α * N := mul_lt_mul_of_pos_left hlt (zero_lt_iff.2 hM)
  · rw [max_eq_right h.le]
    obtain ⟨i, hi⟩ := h2
    refine ⟨i + 1, ?_⟩
    rw [cs, v.map_add_eq_of_lt_right, map_mul, hi]
    rw [map_mul, map_mul, hi]
    calc v α * v (p.coeff (i + 1)) ≤ v α * N := mul_le_mul' le_rfl (h1 _)
      _ < v β * N := mul_lt_mul_of_pos_right h (zero_lt_iff.2 hN)


open Polynomial in
theorem coeff_max_prod_linear {F Γ ι : Type} [Field F] [LinearOrderedCommGroupWithZero Γ] (v : Valuation F Γ)
    (α β : ι → F) (s : Finset ι) :
    (∀ i, v ((∏ j ∈ s, (C (α j) + C (β j) * X)).coeff i) ≤ ∏ j ∈ s, max (v (α j)) (v (β j))) ∧
      ∃ i, v ((∏ j ∈ s, (C (α j) + C (β j) * X)).coeff i) = ∏ j ∈ s, max (v (α j)) (v (β j)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨fun i => ?_, 0, by simp⟩
    by_cases h : i = 0 <;> simp [coeff_one, h]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact coeff_max_mul_linear v _ _ _ _ ih.1 ih.2

theorem nrm_coeff_prod_linear : ∀ (k F : Type) [Field k] [Field F] [Algebra k F], ∀ (v : Place k F) (m : ℕ) (α β : Fin m → F), nrm v (fun a : Fin (m + 1) => (∏ j, (Polynomial.C (α j) + Polynomial.C (β j) * Polynomial.X)).coeff a) = ∏ j, max (v.1 (α j)) (v.1 (β j)) := by
  intro k F _ _ _ v m α β
  obtain ⟨h1, i, hi⟩ := coeff_max_prod_linear v.1 α β Finset.univ
  have hdeg : (∏ j, (Polynomial.C (α j) + Polynomial.C (β j) * Polynomial.X)).natDegree ≤ m := by
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    calc _ ≤ ∑ _j : Fin m, 1 := Finset.sum_le_sum fun j _ => by
            rw [add_comm]; exact Polynomial.natDegree_linear_le
      _ = m := by simp
  refine le_antisymm (Finset.sup_le fun a _ => h1 a) ?_
  rw [← hi]
  by_cases him : i < m + 1
  · exact Finset.le_sup (f := fun a : Fin (m + 1) =>
      v.1 ((∏ j, (Polynomial.C (α j) + Polynomial.C (β j) * Polynomial.X)).coeff a))
      (Finset.mem_univ (⟨i, him⟩ : Fin (m + 1)))
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero]
    exact zero_le'

end GlobalTheory.Nef
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NrmCoeffProdLinearStatement

section

@[expose] public section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef


theorem _root_.GlobalTheory.T.nrm_coeff_prod_linear' : ∀ (k F : Type) [Field k] [Field F] [Algebra k F], ∀ (v : Place k F) (m : ℕ) (α β : Fin m → F), nrm v (fun a : Fin (m + 1) => (∏ j, (Polynomial.C (α j) + Polynomial.C (β j) * Polynomial.X)).coeff a) = ∏ j, max (v.1 (α j)) (v.1 (β j)) := by
  first | exact @GlobalTheory.Nef.nrm_coeff_prod_linear | exact GlobalTheory.Nef.nrm_coeff_prod_linear | (intros; apply GlobalTheory.Nef.nrm_coeff_prod_linear <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussLemmaSymPowMatrixUpperTriangularPlaceOrder

section

@[expose] public section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef Polynomial

namespace GlobalTheory.Nef

theorem ordVec_symMat_mulVec_triangular : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (P : Place k E) (m : ℕ)
    (A : Matrix (Fin 2) (Fin 2) E), A 1 0 = 0 → A.det ≠ 0 → ∀ (q : Fin (m + 1) → E) (c : E) (s t : Fin m → E),
    c ≠ 0 → (∀ j, ![s j, t j] ≠ 0) →
    ∑ i : Fin (m + 1), C (q i) * (C (A 0 1) + C (A 1 1) * X) ^ (i : ℕ) * C (A 0 0) ^ (m - i) =
      C c * ∏ j, (C (s j) * C (A 0 0) + C (t j) * (C (A 0 1) + C (A 1 1) * X)) →
    ordVec P ((symMat m A).mulVec q) = ord P c + ∑ j, ordVec P (A.mulVec ![s j, t j]) := by
  intro k E _ _ _ P m A hA10 hdet q c s t hc hst hq
  classical
  let α : Fin m → E := fun j => s j * A 0 0 + t j * A 0 1
  let β : Fin m → E := fun j => t j * A 1 1
  have hfac : ∀ j, C (s j) * C (A 0 0) + C (t j) * (C (A 0 1) + C (A 1 1) * X) = C (α j) + C (β j) * X := by
    intro j
    simp only [α, β, C_add, C_mul]
    ring
  have hvec : (symMat m A).mulVec q = fun a : Fin (m + 1) => c * (∏ j, (C (α j) + C (β j) * X)).coeff a := by
    rw [symMat_mulVec, hq]
    funext a
    simp only [hfac, coeff_C_mul]
  have hsup : ∀ (n : ℕ) (x : Fin n → E), nrm P (fun a => c * x a) = P.1 c * nrm P x := by
    intro n x
    have h := Finset.comp_sup_eq_sup_comp (s := Finset.univ) (f := fun a => P.1 (x a)) (fun y => P.1 c * y)
      (fun a b => by
        rcases le_total a b with h | h
        · rw [sup_eq_right.2 h, sup_eq_right.2 (mul_le_mul' le_rfl h)]
        · rw [sup_eq_left.2 h, sup_eq_left.2 (mul_le_mul' le_rfl h)]) (by simp)
    simp only [nrm, map_mul]
    exact h.symm
  have hfin2 : ∀ f : Fin 2 → WithZero (Multiplicative ℤ), Finset.univ.sup f = max (f 0) (f 1) := by
    intro f
    refine le_antisymm (Finset.sup_le fun i _ => ?_) (max_le (Finset.le_sup (Finset.mem_univ 0))
      (Finset.le_sup (Finset.mem_univ 1)))
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hw : ∀ j, nrm P (A.mulVec ![s j, t j]) = max (P.1 (α j)) (P.1 (β j)) := by
    intro j
    rw [nrm, hfin2]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      hA10, zero_mul, zero_add, α, β]
    rw [mul_comm (A 0 0), mul_comm (A 0 1), mul_comm (A 1 1)]
  have hnz : ∀ j, nrm P (A.mulVec ![s j, t j]) ≠ 0 := by
    intro j h0
    have hne : A.mulVec ![s j, t j] ≠ 0 := fun h => hst j (Matrix.eq_zero_of_mulVec_eq_zero hdet h)
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
    have h1 : P.1 (A.mulVec ![s j, t j] i) ≤ nrm P (A.mulVec ![s j, t j]) :=
      Finset.le_sup (f := fun i => P.1 (A.mulVec ![s j, t j] i)) (Finset.mem_univ i)
    rw [h0] at h1
    exact (Valuation.ne_zero_iff _).2 hi (le_antisymm h1 zero_le')
  have hPc : P.1 c ≠ 0 := (Valuation.ne_zero_iff _).2 hc
  have hlogprod : ∀ S : Finset (Fin m), WithZero.log (∏ j ∈ S, nrm P (A.mulVec ![s j, t j])) =
      ∑ j ∈ S, WithZero.log (nrm P (A.mulVec ![s j, t j])) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert a S ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha,
        WithZero.log_mul (hnz a) (Finset.prod_ne_zero_iff.2 fun j _ => hnz j), ih]
  have hmain : nrm P ((symMat m A).mulVec q) = P.1 c * ∏ j, nrm P (A.mulVec ![s j, t j]) := by
    rw [hvec, hsup, GlobalTheory.T.nrm_coeff_prod_linear' k E P m α β]
    simp only [hw]
  rw [ordVec, hmain, WithZero.log_mul hPc (Finset.prod_ne_zero_iff.2 fun j _ => hnz j), hlogprod, ord]
  simp only [ordVec, Finset.sum_neg_distrib]
  ring

end GlobalTheory.Nef
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussLemmaSymPowMatrixUpperTriangularPlaceOrderStatement

section

@[expose] public section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef Polynomial

theorem _root_.GlobalTheory.T.gaussLemma_symPowMatrix_upperTriangular_placeOrder : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (P : Place k E) (m : ℕ) (A : Matrix (Fin 2) (Fin 2) E), A 1 0 = 0 → A.det ≠ 0 → ∀ (q : Fin (m + 1) → E) (c : E) (s t : Fin m → E), c ≠ 0 → (∀ j, ![s j, t j] ≠ 0) → ∑ i : Fin (m + 1), C (q i) * (C (A 0 1) + C (A 1 1) * X) ^ (i : ℕ) * C (A 0 0) ^ (m - i) = C c * ∏ j, (C (s j) * C (A 0 0) + C (t j) * (C (A 0 1) + C (A 1 1) * X)) → ordVec P ((symMat m A).mulVec q) = ord P c + ∑ j, ordVec P (A.mulVec ![s j, t j]) := by
  first | exact @GlobalTheory.Nef.ordVec_symMat_mulVec_triangular | exact GlobalTheory.Nef.ordVec_symMat_mulVec_triangular | (intros; apply GlobalTheory.Nef.ordVec_symMat_mulVec_triangular <;> assumption)
end
end
