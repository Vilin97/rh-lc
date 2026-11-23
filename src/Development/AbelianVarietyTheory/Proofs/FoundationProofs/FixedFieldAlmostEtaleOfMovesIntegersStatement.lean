module

public import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.RingTheory.Valuation.Basic
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
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Order.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.SeparatingFamilySumClosedUnderProd

section

@[expose] public section

open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory

theorem sepFamily_prod : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G] [MulSemiringAction G L] (F : Subfield L) (ι : Type) (s : Finset ι) (x y : ι → L), (∀ j ∈ s, x j ∈ F ∧ y j ∈ F ∧ v (x j) ≤ 1 ∧ v (y j) ≤ 1) → ∃ (n : ℕ) (a b : Fin n → L), (∀ i, a i ∈ F ∧ b i ∈ F ∧ v (a i) ≤ 1 ∧ v (b i) ≤ 1) ∧ ∀ σ : G, ∑ i, a i * σ • b i = ∏ j ∈ s, (x j - σ • y j) := by
  intro L _ v G _ _ F ι s x y hs
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨1, fun _ => 1, fun _ => 1, fun _ => ⟨F.one_mem, F.one_mem, by simp, by simp⟩,
      fun σ => by simp⟩
  | insert j s hj ih =>
    obtain ⟨n, a, b, hab, hsum⟩ := ih (fun k hk => hs k (Finset.mem_insert_of_mem hk))
    obtain ⟨hxF, hyF, hxv, hyv⟩ := hs j (Finset.mem_insert_self j s)
    refine ⟨n + n, Fin.append (fun i => x j * a i) (fun i => - a i),
      Fin.append b (fun i => y j * b i), ?_, ?_⟩
    · intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simp only [Fin.append_left]
        obtain ⟨h1, h2, h3, h4⟩ := hab i
        exact ⟨F.mul_mem hxF h1, h2, by rw [map_mul]; exact mul_le_one' hxv h3, h4⟩
      · simp only [Fin.append_right]
        obtain ⟨h1, h2, h3, h4⟩ := hab i
        exact ⟨F.neg_mem h1, F.mul_mem hyF h2, by rw [Valuation.map_neg]; exact h3,
          by rw [map_mul]; exact mul_le_one' hyv h4⟩
    · intro σ
      rw [Finset.prod_insert hj, ← hsum σ, Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, smul_mul']
      have e1 : ∑ i, x j * a i * σ • b i = x j * ∑ i, a i * σ • b i := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
      have e2 : ∑ i, -a i * (σ • y j * σ • b i) = -(σ • y j * ∑ i, a i * σ • b i) := by
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      rw [e1, e2]; ring

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.SeparatingFamilySumClosedUnderProdStatement

section

@[expose] public section

open GlobalTheory.AlmostEt
open scoped NNReal

theorem _root_.GlobalTheory.T.separating_family_sum_closed_under_prod : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G] [MulSemiringAction G L] (F : Subfield L) (ι : Type) (s : Finset ι) (x y : ι → L), (∀ j ∈ s, x j ∈ F ∧ y j ∈ F ∧ v (x j) ≤ 1 ∧ v (y j) ≤ 1) → ∃ (n : ℕ) (a b : Fin n → L), (∀ i, a i ∈ F ∧ b i ∈ F ∧ v (a i) ≤ 1 ∧ v (b i) ≤ 1) ∧ ∀ σ : G, ∑ i, a i * σ • b i = ∏ j ∈ s, (x j - σ • y j) := by
  first | exact @GlobalTheory.sepFamily_prod | exact GlobalTheory.sepFamily_prod | (intros; apply GlobalTheory.sepFamily_prod <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.FixedFieldAlmostEtaleOfMovesIntegers

section

@[expose] public section

open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

open Topology

lemma exists_lt_one_lt_pow (r : ℝ≥0) (hr : r < 1) (k : ℕ) : ∃ t : ℝ≥0, t < 1 ∧ r < t ^ k := by
  have hopen : IsOpen {t : ℝ≥0 | r < t ^ k} := isOpen_lt continuous_const (continuous_pow k)
  have hmem : {t : ℝ≥0 | r < t ^ k} ∈ 𝓝 (1 : ℝ≥0) := hopen.mem_nhds (by simpa using hr)
  obtain ⟨l, hl, hsub⟩ := exists_Ioc_subset_of_mem_nhds hmem ⟨0, zero_lt_one⟩
  obtain ⟨t, hlt, ht1⟩ := exists_between hl
  exact ⟨t, ht1, hsub ⟨hlt, ht1.le⟩⟩

lemma smul_mem_fix {L : Type} [Field L] {G : Type} [Group G] [MulSemiringAction G L]
    (N : Subgroup G) [hN : N.Normal] (g : G) {y : L} (hy : y ∈ Fix L N) : g • y ∈ Fix L N := by
  intro n
  have hc : g⁻¹ * (n : G) * g ∈ N := by
    have := hN.conj_mem (n : G) n.2 g⁻¹
    simpa using this
  have h1 : (g⁻¹ * (n : G) * g) • y = y := hy ⟨_, hc⟩
  show (n : G) • g • y = g • y
  calc (n : G) • g • y = g • ((g⁻¹ * (n : G) * g) • y) := by
        simp only [mul_smul, smul_inv_smul]
    _ = g • y := by rw [h1]

lemma fix_smul {L : Type} [Field L] {G : Type} [Group G] [MulSemiringAction G L]
    (N : Subgroup G) {y : L} (hy : y ∈ Fix L N) {σ : G} (hσ : σ ∈ N) : σ • y = y :=
  hy ⟨σ, hσ⟩

theorem almostSep_of_moves : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G]
    [MulSemiringAction G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ N : Subgroup G, N.Normal →
    N.FiniteIndex → (∀ σ : G, σ ∉ N → Moves v (Fix L N) σ) → AlmostSep v N := by
  intro L _ v G _ _ hv N hN hfi hmov r hr
  classical
  haveI : Finite (G ⧸ N) := inferInstance
  letI : Fintype (G ⧸ N) := Fintype.ofFinite _
  set s : Finset (G ⧸ N) := Finset.univ.erase 1 with hs
  obtain ⟨t, ht1, hrt⟩ := exists_lt_one_lt_pow r hr s.card
  have hex : ∀ q : G ⧸ N, ∃ y : L, y ∈ Fix L N ∧ v y ≤ 1 ∧ (q ≠ 1 → t < v (q.out • y - y)) := by
    intro q
    by_cases hq : q = 1
    · exact ⟨0, zero_mem _, by simp, fun h => absurd hq h⟩
    · have hout : q.out ∉ N := by
        intro hm
        apply hq
        rw [← QuotientGroup.out_eq' q]
        exact (QuotientGroup.eq_one_iff _).2 hm
      obtain ⟨y, hyF, hyv, hyt⟩ := hmov _ hout t ht1
      exact ⟨y, hyF, hyv, fun _ => hyt⟩
  choose y hyF hyv hyt using hex
  let x : G ⧸ N → L := fun q => q.out • y q
  have hxF : ∀ q, x q ∈ Fix L N := fun q => smul_mem_fix N _ (hyF q)
  have hxv : ∀ q, v (x q) ≤ 1 := fun q => by simp only [x, hv]; exact hyv q
  obtain ⟨n, a, b, hab, hsum⟩ := GlobalTheory.T.separating_family_sum_closed_under_prod L v G (Fix L N) (G ⧸ N) s x y
    (fun j _ => ⟨hxF j, hyF j, hxv j, hyv j⟩)
  refine ⟨n, a, b, ∏ q ∈ s, (x q - y q), ?_, ?_⟩
  · refine
      { a_mem := fun i => (hab i).1
        b_mem := fun i => (hab i).2.1
        c_mem := ?_
        a_le := fun i => (hab i).2.2.1
        b_le := fun i => (hab i).2.2.2
        c_le := ?_
        sum_in := ?_
        sum_out := ?_ }
    · exact prod_mem fun q _ => sub_mem (hxF q) (hyF q)
    · rw [map_prod]
      refine Finset.prod_le_one₀ (fun _ _ => zero_le) fun q _ => ?_
      exact (Valuation.map_sub v _ _).trans (max_le (hxv q) (hyv q))
    · intro σ hσ
      rw [hsum σ]
      refine Finset.prod_congr rfl fun q _ => ?_
      rw [fix_smul N (hyF q) hσ]
    · intro σ hσ
      rw [hsum σ]
      have hq : (σ : G ⧸ N) ∈ s := by
        rw [hs, Finset.mem_erase]
        refine ⟨?_, Finset.mem_univ _⟩
        intro h
        exact hσ ((QuotientGroup.eq_one_iff σ).1 h)
      refine Finset.prod_eq_zero hq ?_
      obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul N σ
      simp only [x]
      rw [hm, mul_smul, fix_smul N (hyF _) m.2, sub_self]
  · rw [map_prod]
    calc r < t ^ s.card := hrt
      _ = ∏ _q ∈ s, t := by rw [Finset.prod_const]
      _ ≤ ∏ q ∈ s, v (x q - y q) := by
        refine Finset.prod_le_prod₀ (fun _ _ => zero_le) fun q hq => ?_
        exact (hyt q (Finset.ne_of_mem_erase hq)).le

end GlobalTheory.AlmostEt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.FixedFieldAlmostEtaleOfMovesIntegersStatement

section

@[expose] public section

open GlobalTheory.AlmostEt
open scoped NNReal

theorem _root_.GlobalTheory.T.fixedFieldAlmostEtale_of_moves_integers : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G] [MulSemiringAction G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ N : Subgroup G, N.Normal → N.FiniteIndex → (∀ σ : G, σ ∉ N → Moves v (Fix L N) σ) → AlmostSep v N := by
  first | exact @GlobalTheory.AlmostEt.almostSep_of_moves | exact GlobalTheory.AlmostEt.almostSep_of_moves | (intros; apply GlobalTheory.AlmostEt.almostSep_of_moves <;> assumption)
end
end
