module

public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedDefs
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.SemiChar

-- Source module: ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedProjA

section

@[expose] public section

noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F Polynomial

namespace ReciprocityTheory.ChartRestriction.L1

variable {K : Type} [Field K] (U : PowerSeries K)

theorem homS_add (m : ℕ) (P Q : K[X]) : homS U m (P + Q) = homS U m P + homS U m Q := by
  simp only [homS, coeff_add, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem homS_sub (m : ℕ) (P Q : K[X]) : homS U m (P - Q) = homS U m P - homS U m Q := by
  simp only [homS, coeff_sub, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem homS_zero (m : ℕ) : homS U m (0 : K[X]) = 0 := by
  simp [homS]

theorem homS_sum {ι : Type} (s : Finset ι) (m : ℕ) (f : ι → K[X]) :
    homS U m (∑ i ∈ s, f i) = ∑ i ∈ s, homS U m (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [homS_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, homS_add, ih]

theorem homS_monomial (m i : ℕ) (hi : i ≤ m) (a : K) :
    homS U m (monomial i a) = PowerSeries.C a * U ^ i * PowerSeries.X ^ (2 * (m - i)) := by
  unfold homS
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    rw [coeff_monomial_of_ne a hb]
    simp
  · intro h
    exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le hi)) h

theorem homS_mul (m n : ℕ) (P Q : K[X]) (hP : P.natDegree ≤ m) (hQ : Q.natDegree ≤ n) :
    homS U (m + n) (P * Q) = homS U m P * homS U n Q := by
  have eP : P = ∑ i ∈ Finset.range (m + 1), monomial i (P.coeff i) :=
    P.as_sum_range' (m + 1) (Nat.lt_succ_of_le hP)
  have eQ : Q = ∑ j ∈ Finset.range (n + 1), monomial j (Q.coeff j) :=
    Q.as_sum_range' (n + 1) (Nat.lt_succ_of_le hQ)
  have e : P * Q = ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
      monomial (i + j) (P.coeff i * Q.coeff j) := by
    conv_lhs => rw [eP, eQ]
    rw [Finset.sum_mul_sum]
    simp only [monomial_mul_monomial]
  rw [e, homS_sum]
  simp only [homS_sum]
  unfold homS
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
  have hi' : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hj' : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  have := homS_monomial U (m + n) (i + j) (by omega) (P.coeff i * Q.coeff j)
  unfold homS at this
  rw [this]
  have h2 : 2 * (m + n - (i + j)) = 2 * (m - i) + 2 * (n - j) := by omega
  rw [h2, pow_add, pow_add, map_mul]
  ring

theorem homS_eq_zero (hU : PowerSeries.constantCoeff U = 1) (m : ℕ) (P : K[X]) (hP : P.natDegree ≤ m)
    (h : homS U m P = 0) : P = 0 := by
  have h1 : PowerSeries.coeff (2 * (m - P.natDegree)) (homS U m P) = P.leadingCoeff := by
    unfold homS

    rw [map_sum, Finset.sum_eq_single P.natDegree]
    · rw [PowerSeries.coeff_mul_X_pow', if_pos le_rfl, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply,
        map_mul, map_pow, hU]
      simp
    · intro b hb hne
      have hb' : b ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hb)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · rw [PowerSeries.coeff_mul_X_pow', if_neg (by omega)]
      · rw [coeff_eq_zero_of_natDegree_lt hgt]
        simp
    · intro hh
      exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le hP)) hh
  rw [h, map_zero] at h1
  exact leadingCoeff_eq_zero.1 h1.symm

end ReciprocityTheory.ChartRestriction.L1
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedProj

section

@[expose] public section

noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F Polynomial

namespace ReciprocityTheory.ChartRestriction.L1

section Proj

variable {E : Type} [Field E]

def serMap (ψ : E →+ E) (S : PowerSeries E) : PowerSeries E :=
  PowerSeries.mk fun n => ψ (PowerSeries.coeff n S)

def polMap (ψ : E →+ E) (m : ℕ) (Q : E[X]) : E[X] :=
  ∑ i ∈ Finset.range (m + 1), monomial i (ψ (Q.coeff i))

theorem coeff_serMap (ψ : E →+ E) (S : PowerSeries E) (n : ℕ) :
    PowerSeries.coeff n (serMap ψ S) = ψ (PowerSeries.coeff n S) := by
  simp [serMap]

theorem serMap_sum (ψ : E →+ E) {ι : Type} (s : Finset ι) (f : ι → PowerSeries E) :
    serMap ψ (∑ i ∈ s, f i) = ∑ i ∈ s, serMap ψ (f i) := by
  ext n

  simp [coeff_serMap, map_sum]

theorem coeff_polMap (ψ : E →+ E) (m : ℕ) (Q : E[X]) (i : ℕ) :
    (polMap ψ m Q).coeff i = if i ≤ m then ψ (Q.coeff i) else 0 := by
  simp only [polMap, finsetSum_coeff, coeff_monomial_apply]
  rw [Finset.sum_ite_eq' (Finset.range (m + 1)) i]
  simp

theorem natDegree_polMap_le (ψ : E →+ E) (m : ℕ) (Q : E[X]) : (polMap ψ m Q).natDegree ≤ m := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro i hi
  rw [coeff_polMap, if_neg (by omega)]

variable (k : Subfield E)

theorem coeff_mem_mul {S T : PowerSeries E} (hS : ∀ n, PowerSeries.coeff n S ∈ k)
    (hT : ∀ n, PowerSeries.coeff n T ∈ k) : ∀ n, PowerSeries.coeff n (S * T) ∈ k := by
  intro n
  rw [PowerSeries.coeff_mul]
  exact sum_mem fun p _ => mul_mem (hS _) (hT _)

theorem coeff_mem_one : ∀ n, PowerSeries.coeff n (1 : PowerSeries E) ∈ k := by
  intro n
  rw [PowerSeries.coeff_one]
  split_ifs
  · exact one_mem k
  · exact zero_mem k

theorem coeff_mem_pow {S : PowerSeries E} (hS : ∀ n, PowerSeries.coeff n S ∈ k) (i : ℕ) :
    ∀ n, PowerSeries.coeff n (S ^ i) ∈ k := by
  induction i with
  | zero => simpa using coeff_mem_one k
  | succ i ih => rw [pow_succ]; exact coeff_mem_mul k ih hS

theorem coeff_mem_X : ∀ n, PowerSeries.coeff n (PowerSeries.X : PowerSeries E) ∈ k := by
  intro n
  rw [PowerSeries.coeff_X]
  split_ifs
  · exact one_mem k
  · exact zero_mem k

variable {k}

theorem serMap_mul (ψ : E →+ E) (hψ : ∀ c ∈ k, ∀ x, ψ (c * x) = c * ψ x) {W : PowerSeries E}
    (hW : ∀ n, PowerSeries.coeff n W ∈ k) (S : PowerSeries E) :
    serMap ψ (W * S) = W * serMap ψ S := by
  ext n

  rw [coeff_serMap, PowerSeries.coeff_mul, PowerSeries.coeff_mul, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [hψ _ (hW _), coeff_serMap]

theorem serMap_C (ψ : E →+ E) (q : E) : serMap ψ (PowerSeries.C q) = PowerSeries.C (ψ q) := by
  ext n
  rw [coeff_serMap, PowerSeries.coeff_C, PowerSeries.coeff_C]
  split_ifs
  · rfl
  · exact map_zero ψ

theorem serMap_homS (ψ : E →+ E) (hψ : ∀ c ∈ k, ∀ x, ψ (c * x) = c * ψ x) {U : PowerSeries E}
    (hU : ∀ n, PowerSeries.coeff n U ∈ k) (m : ℕ) (Q : E[X]) :
    serMap ψ (homS U m Q) = homS U m (polMap ψ m Q) := by
  unfold homS
  rw [serMap_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hW : ∀ n, PowerSeries.coeff n (U ^ i * PowerSeries.X ^ (2 * (m - i))) ∈ k :=
    coeff_mem_mul k (coeff_mem_pow k hU i) (coeff_mem_pow k (coeff_mem_X k) _)
  rw [coeff_polMap, if_pos hi', mul_assoc, mul_assoc, mul_comm (PowerSeries.C (Q.coeff i)),
    serMap_mul ψ hψ hW, serMap_C, mul_comm]

theorem exists_proj (k : Subfield E) : ∃ ψ : E →+ E, (∀ c ∈ k, ∀ x, ψ (c * x) = c * ψ x) ∧
    (∀ x, ψ x ∈ k) ∧ ψ 1 = 1 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap k E)
    (LinearMap.ker_eq_bot.mpr (algebraMap k E).injective)
  refine ⟨(k.subtype : k →+ E).comp g.toAddMonoidHom, ?_, ?_, ?_⟩
  · intro c hc x
    have := g.map_smul (⟨c, hc⟩ : k) x
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe]
    have h2 : (⟨c, hc⟩ : k) • x = c * x := rfl
    rw [← h2, this]
    rfl
  · intro x
    exact (g x).2
  · have := LinearMap.congr_fun hg 1
    simp only [LinearMap.comp_apply, Algebra.linearMap_apply, map_one, LinearMap.id_apply] at this
    simp [this]

end Proj

theorem proj_trick {E : Type} [Field E] (k : Subfield E) (U V : PowerSeries E)
    (hU : ∀ n, PowerSeries.coeff n U ∈ k) (hV : ∀ n, PowerSeries.coeff n V ∈ k)
    (hU0 : PowerSeries.constantCoeff U = 1) (A B : E[X]) (N : ℕ) (hA : A.natDegree ≤ N + 1)
    (hB : B.Monic) (hBd : B.natDegree = N) (hc : IsCoprime A B)
    (h : V * homS U N B = homS U (N + 1) A) : ∀ i, B.coeff i ∈ k := by
  obtain ⟨ψ, hψ, hψk, hψ1⟩ := exists_proj k
  set A' := polMap ψ (N + 1) A with hA'
  set B' := polMap ψ N B with hB'
  have hA'd : A'.natDegree ≤ N + 1 := natDegree_polMap_le ψ _ A
  have hB'd : B'.natDegree ≤ N := natDegree_polMap_le ψ _ B
  have h' : V * homS U N B' = homS U (N + 1) A' := by
    rw [hA', hB', ← serMap_homS ψ hψ hU, ← serMap_homS ψ hψ hU, ← serMap_mul ψ hψ hV, h]
  have hBN : B'.coeff N = 1 := by
    rw [hB', coeff_polMap, if_pos le_rfl, ← hBd, hB.coeff_natDegree, hψ1]
  have hB'deg : B'.natDegree = N := by
    refine le_antisymm hB'd (le_natDegree_of_ne_zero ?_)
    rw [hBN]; exact one_ne_zero
  have hB'm : B'.Monic := by
    rw [Monic, leadingCoeff, hB'deg, hBN]
  have hcross : A * B' = A' * B := by
    have h0 : homS U (N + 1 + N) (A * B' - A' * B) = 0 := by
      rw [homS_sub, homS_mul U _ _ _ _ hA hB'd, homS_mul U _ _ _ _ hA'd hBd.le, ← h, ← h']
      ring
    have hdeg : (A * B' - A' * B).natDegree ≤ N + 1 + N := by
      refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · exact natDegree_mul_le.trans (add_le_add hA hB'd)
      · exact natDegree_mul_le.trans (add_le_add hA'd hBd.le)
    exact sub_eq_zero.mp (homS_eq_zero U hU0 _ _ hdeg h0)
  have hdvd : B ∣ B' := by
    refine hc.symm.dvd_of_dvd_mul_left ?_
    rw [hcross]
    exact dvd_mul_left _ _
  have heq : B = B' :=
    (eq_of_monic_of_dvd_of_natDegree_le hB hB'm hdvd (by rw [hB'deg, hBd])).symm
  intro i
  rw [heq, hB', coeff_polMap]
  split_ifs
  · exact hψk _
  · exact zero_mem k

end ReciprocityTheory.ChartRestriction.L1
end
end
end
