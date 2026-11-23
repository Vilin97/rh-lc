module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegersEqSumZetaPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegersLevelOneEqSumZetaPow
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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicFrobeniusTwistedValueEq
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegersLevelOneEqSumZetaPowStatement

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

theorem _root_.GlobalTheory.T.exists_integral_eq_sum_zeta_pow_level_one : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (ζ : Om l), IsPrimitiveRoot ζ l → ∀ α : Om l, α ∈ Ks K 1 → ‖α‖ ≤ 1 → ∃ y : Fin l → Om l, (∀ a, y a ∈ K0 K ∧ ‖y a‖ ≤ 1) ∧ α = ∑ a : Fin l, ζ ^ (a : ℕ) * y a := by
  first | exact @GlobalTheory.Cyc.integers_level_one_eq_sum_zeta_pow | exact GlobalTheory.Cyc.integers_level_one_eq_sum_zeta_pow | (intros; apply GlobalTheory.Cyc.integers_level_one_eq_sum_zeta_pow <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicLevelIntegersMemClosureLevels

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

namespace GlobalTheory.Cyc.LevelGen

theorem chain_pow {l : ℕ} {M : Type} [Monoid M] (ζ : ℕ → M) (h : ∀ j, ζ (j + 1) ^ l = ζ j)
    (j k : ℕ) : ζ (j + k) ^ (l ^ k) = ζ j := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc ζ (j + (k + 1)) ^ (l ^ (k + 1)) = (ζ (j + k + 1) ^ l) ^ (l ^ k) := by
          rw [pow_succ', pow_mul, ← add_assoc]
      _ = ζ j := by rw [h, ih]

theorem chain_primitive {l : ℕ} [Fact l.Prime] {M : Type} [CommMonoid M] (ζ : ℕ → M)
    (h0 : ζ 0 = 1) (h1 : ζ 1 ≠ 1) (h : ∀ j, ζ (j + 1) ^ l = ζ j) (j : ℕ) :
    IsPrimitiveRoot (ζ (j + 1)) (l ^ (j + 1)) := by
  have hfin : ζ (j + 1) ^ l ^ (j + 1) = 1 := by
    have := chain_pow ζ h 0 (j + 1)
    rw [zero_add] at this
    rw [this, h0]
  have hnot : ¬ ζ (j + 1) ^ l ^ j = 1 := by
    have := chain_pow ζ h 1 j
    rw [add_comm 1 j] at this
    rw [this]
    exact h1
  rw [← orderOf_eq_prime_pow hnot hfin]
  exact IsPrimitiveRoot.orderOf _

theorem mem_closure_all (l : ℕ) [Fact l.Prime] (K : FinExt l) (ζ : ℕ → Om l) (h0 : ζ 0 = 1)
    (h1 : ζ 1 ≠ 1) (h : ∀ j, ζ (j + 1) ^ l = ζ j) (s : ℕ) :
    ∀ α : Om l, α ∈ Ks K (s + 1) → ‖α‖ ≤ 1 → α ∈ AddSubgroup.closure
      {x : Om l | ∃ (n : ℕ) (c : Om l), c ∈ K0 K ∧ ‖c‖ ≤ 1 ∧ x = c * ζ (s + 1) ^ n} := by
  induction s with
  | zero =>
    intro α hα hn
    have hp : IsPrimitiveRoot (ζ (0 + 1)) l := by
      simpa using chain_primitive ζ h0 h1 h 0
    obtain ⟨y, hy, rfl⟩ := GlobalTheory.T.exists_integral_eq_sum_zeta_pow_level_one l K (ζ (0 + 1)) hp α hα hn
    refine AddSubgroup.sum_mem _ (fun a _ => AddSubgroup.subset_closure ?_)
    exact ⟨a, y a, (hy a).1, (hy a).2, mul_comm _ _⟩
  | succ s ih =>
    intro α hα hn
    have hp : IsPrimitiveRoot (ζ (s + 1 + 1)) (l ^ (s + 1 + 1)) := chain_primitive ζ h0 h1 h (s + 1)
    have hα' : α ∈ Ks K (s + 1 + 1) := hα
    obtain ⟨y, hy, rfl⟩ := (GlobalTheory.Cyc.integers_eq_sum_zeta_pow l K (s + 1 + 1) (by omega)
      (ζ (s + 1 + 1)) hp).1 α hα' hn
    refine AddSubgroup.sum_mem _ (fun a _ => ?_)
    have hya : y a ∈ Ks K (s + 1) := by simpa using (hy a).1
    have hmem := ih (y a) hya (hy a).2
    have hle : AddSubgroup.closure
        {x : Om l | ∃ (n : ℕ) (c : Om l), c ∈ K0 K ∧ ‖c‖ ≤ 1 ∧ x = c * ζ (s + 1) ^ n} ≤
        (AddSubgroup.closure
          {x : Om l | ∃ (n : ℕ) (c : Om l), c ∈ K0 K ∧ ‖c‖ ≤ 1 ∧ x = c * ζ (s + 1 + 1) ^ n}).comap
          (AddMonoidHom.mulLeft (ζ (s + 1 + 1) ^ (a : ℕ))) := by
      rw [AddSubgroup.closure_le]
      rintro x ⟨n, c, hc, hcn, rfl⟩
      apply AddSubgroup.subset_closure
      refine ⟨(a : ℕ) + l * n, c, hc, hcn, ?_⟩
      simp only [AddMonoidHom.coe_mulLeft]
      rw [← h (s + 1), pow_add, pow_mul]
      ring
    exact hle hmem

end GlobalTheory.Cyc.LevelGen


open GlobalTheory.Cyc.LevelGen in
theorem GlobalTheory.Cyc.integers_mem_closure_levels : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (ζ : ℕ → Om l), ζ 0 = 1 → ζ 1 ≠ 1 → (∀ j, ζ (j + 1) ^ l = ζ j) → ∀ s : ℕ, 1 ≤ s → ∀ α : Om l, α ∈ Ks K s → ‖α‖ ≤ 1 → α ∈ AddSubgroup.closure {x : Om l | ∃ (j n : ℕ) (c : Om l), 1 ≤ j ∧ j ≤ s ∧ ¬ l ∣ n ∧ c ∈ K0 K ∧ ‖c‖ ≤ 1 ∧ x = c * ζ j ^ n} := by
  intro l _ K ζ h0 h1 h s hs α hα hn
  set S : AddSubgroup (Om l) := AddSubgroup.closure
    {x : Om l | ∃ (j n : ℕ) (c : Om l), 1 ≤ j ∧ j ≤ s ∧ ¬ l ∣ n ∧ c ∈ K0 K ∧ ‖c‖ ≤ 1 ∧
      x = c * ζ j ^ n} with hS
  have hl : 1 < l := (Fact.out : l.Prime).one_lt

  have hconst : ∀ c : Om l, c ∈ K0 K → ‖c‖ ≤ 1 → c ∈ S := by
    intro c hc hcn
    have hp : IsPrimitiveRoot (ζ 1) l := by simpa using chain_primitive ζ h0 h1 h 0
    have hsum := hp.geom_sum_eq_zero hl
    obtain ⟨m, hm⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
    have hr : Finset.range l = Finset.range (m + 1) := by rw [hm]
    rw [hr, Finset.sum_range_succ', pow_zero] at hsum
    have hc' : c = ∑ i ∈ Finset.range m, (-c) * ζ 1 ^ (i + 1) := by
      rw [← Finset.mul_sum, eq_neg_of_add_eq_zero_left hsum]
      ring
    rw [hc']
    refine AddSubgroup.sum_mem _ (fun i hi => AddSubgroup.subset_closure ?_)
    have hi' := Finset.mem_range.1 hi
    refine ⟨1, i + 1, -c, le_rfl, hs, ?_, neg_mem hc, by rwa [norm_neg], rfl⟩
    intro hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hlev : ∀ j, j ≤ s → ∀ (n : ℕ) (c : Om l), c ∈ K0 K → ‖c‖ ≤ 1 → c * ζ j ^ n ∈ S := by
    intro j
    induction j with
    | zero =>
      intro _ n c hc hcn
      rw [h0, one_pow, mul_one]
      exact hconst c hc hcn
    | succ j ih =>
      intro hj n c hc hcn
      by_cases hd : l ∣ n
      · obtain ⟨m, rfl⟩ := hd
        rw [pow_mul, h j]
        exact ih (by omega) m c hc hcn
      · exact AddSubgroup.subset_closure ⟨j + 1, n, c, by omega, hj, hd, hc, hcn, rfl⟩
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  have hmem := mem_closure_all l K ζ h0 h1 h t α hα hn
  have hle : AddSubgroup.closure
      {x : Om l | ∃ (n : ℕ) (c : Om l), c ∈ K0 K ∧ ‖c‖ ≤ 1 ∧ x = c * ζ (t + 1) ^ n} ≤ S := by
    rw [AddSubgroup.closure_le]
    rintro x ⟨n, c, hc, hcn, rfl⟩
    exact hlev (t + 1) le_rfl n c hc hcn
  exact hle hmem
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicLevelIntegersMemClosureLevelsStatement

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

theorem _root_.GlobalTheory.T.cyclotomicLevel_integers_mem_closure_levels : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (ζ : ℕ → Om l), ζ 0 = 1 → ζ 1 ≠ 1 → (∀ j, ζ (j + 1) ^ l = ζ j) → ∀ s : ℕ, 1 ≤ s → ∀ α : Om l, α ∈ Ks K s → ‖α‖ ≤ 1 → α ∈ AddSubgroup.closure {x : Om l | ∃ (j n : ℕ) (c : Om l), 1 ≤ j ∧ j ≤ s ∧ ¬ l ∣ n ∧ c ∈ K0 K ∧ ‖c‖ ≤ 1 ∧ x = c * ζ j ^ n} := by
  first | exact @GlobalTheory.Cyc.integers_mem_closure_levels | exact GlobalTheory.Cyc.integers_mem_closure_levels | (intros; apply GlobalTheory.Cyc.integers_mem_closure_levels <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicFrobeniusTwistedValueEqStatement

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

theorem _root_.GlobalTheory.T.exists_cyclotomicFrobeniusTwistedValue_eq : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s e j n : ℕ), 1 ≤ j → j ≤ s → ¬ l ∣ n → ∀ c : Om l, c ∈ K0 K → ‖c‖ ≤ 1 → ∃ (lam : ℕ → ↥(K0 K)) (d : ↥(K0 K)), (∀ a, ‖(lam a : Om l)‖ ≤ 1) ∧ ‖(d : Om l)‖ ≤ 1 ∧ d - (l : ↥(K0 K)) ^ e * frK P K d = (frK P K ^ s) (∑ a ∈ primeTo l s, lam a) ∧ cycVal P K s e lam d = (l : Om l) ^ ((e + 1) * (s - 1)) * (c * P.ζQ j ^ n) := by
  first | exact @GlobalTheory.ExpImage.Values.exists_cycVal_eq | exact GlobalTheory.ExpImage.Values.exists_cycVal_eq | (intros; apply GlobalTheory.ExpImage.Values.exists_cycVal_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicFrobeniusTwistedValueEqPowMul

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

namespace GlobalTheory.ExpImage

theorem cycVal_add {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s e : ℕ)
    (lam lam' : ℕ → ↥(K0 K)) (d d' : ↥(K0 K)) :
    cycVal P K s e (fun a => lam a + lam' a) (d + d') =
      cycVal P K s e lam d + cycVal P K s e lam' d' := by
  unfold cycVal
  simp only [map_add (f := _)]
  push_cast
  simp only [add_mul, Finset.sum_add_distrib, mul_add]
  ring

theorem cycVal_neg {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s e : ℕ)
    (lam : ℕ → ↥(K0 K)) (d : ↥(K0 K)) :
    cycVal P K s e (fun a => -lam a) (-d) = -cycVal P K s e lam d := by
  unfold cycVal
  simp only [map_neg]
  push_cast
  simp only [neg_mul, Finset.sum_neg_distrib, mul_neg]
  ring

theorem cycVal_zero {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s e : ℕ) :
    cycVal P K s e (fun _ => 0) 0 = 0 := by
  simp [cycVal]

theorem exists_cycVal_eq_pow_mul (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s e : ℕ)
    (hs : 1 ≤ s) (α : Om l) (hα : α ∈ Ks K s) (hn : ‖α‖ ≤ 1) :
    ∃ (lam : ℕ → ↥(K0 K)) (d : ↥(K0 K)), (∀ a, ‖(lam a : Om l)‖ ≤ 1) ∧ ‖(d : Om l)‖ ≤ 1 ∧
      d - (l : ↥(K0 K)) ^ e * frK P K d = (frK P K ^ s) (∑ a ∈ primeTo l s, lam a) ∧
      cycVal P K s e lam d = (l : Om l) ^ ((e + 1) * (s - 1)) * α := by
  have hl1 : 1 < l := (Fact.out : l.Prime).one_lt
  have hsum := GlobalTheory.ExpImage.Values.sum_zeta P
  have hgeom : ∑ r ∈ Finset.range l, P.ζQ 1 ^ r = 0 := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega), hsum]
    simp
  have hpow : P.ζQ 1 ^ l = 1 := by
    have h := geom_sum_mul (P.ζQ 1) l
    rw [hgeom, zero_mul] at h
    exact (sub_eq_zero.mp h.symm)
  have h0 : P.ζQ 0 = 1 := by
    have h := GlobalTheory.ExpImage.Values.zeta_pow P 0 1
    simpa [hpow] using h.symm
  have h1 : P.ζQ 1 ≠ 1 := by
    intro h
    rw [h] at hsum
    have hc : ((l - 1 : ℕ) : Om l) = -1 := by simpa using hsum
    have hz : ((l : ℕ) : Om l) = 0 := by
      push_cast [Nat.cast_sub hl1.le] at hc
      linear_combination hc
    exact (Nat.cast_ne_zero.mpr (by omega : l ≠ 0)) hz
  have hchain : ∀ j, P.ζQ (j + 1) ^ l = P.ζQ j := fun j => by
    simpa using GlobalTheory.ExpImage.Values.zeta_pow P j 1
  have hmem := GlobalTheory.T.cyclotomicLevel_integers_mem_closure_levels l K P.ζQ h0 h1 hchain s hs α hα hn
  clear hα hn
  induction hmem using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨j, n, c, hj, hjs, hn', hc, hc1, rfl⟩ := hx
    exact GlobalTheory.T.exists_cyclotomicFrobeniusTwistedValue_eq l P K s e j n hj hjs hn' c hc hc1
  | zero =>
    refine ⟨fun _ => 0, 0, fun _ => by simp, by simp, by simp, ?_⟩
    rw [cycVal_zero, mul_zero]
  | add x y _ _ ihx ihy =>
    obtain ⟨lam, d, hlam, hd, hfr, hv⟩ := ihx
    obtain ⟨lam', d', hlam', hd', hfr', hv'⟩ := ihy
    refine ⟨fun a => lam a + lam' a, d + d', fun a => ?_, ?_, ?_, ?_⟩
    · push_cast
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hlam a) (hlam' a))
    · push_cast
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hd hd')
    · simp only [map_add (f := _), Finset.sum_add_distrib]
      rw [← hfr, ← hfr']
      ring
    · rw [cycVal_add, hv, hv']
      ring
  | neg x _ ih =>
    obtain ⟨lam, d, hlam, hd, hfr, hv⟩ := ih
    refine ⟨fun a => -lam a, -d, fun a => by simpa using hlam a, by simpa using hd, ?_, ?_⟩
    · simp only [map_neg, Finset.sum_neg_distrib]
      rw [← hfr]
      ring
    · rw [cycVal_neg, hv]
      ring

end GlobalTheory.ExpImage
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicFrobeniusTwistedValueEqPowMulStatement

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

theorem _root_.GlobalTheory.T.exists_cyclotomicFrobeniusTwistedValue_eq_pow_mul : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s e : ℕ), 1 ≤ s → ∀ α : Om l, α ∈ Ks K s → ‖α‖ ≤ 1 → ∃ (lam : ℕ → ↥(K0 K)) (d : ↥(K0 K)), (∀ a, ‖(lam a : Om l)‖ ≤ 1) ∧ ‖(d : Om l)‖ ≤ 1 ∧ d - (l : ↥(K0 K)) ^ e * frK P K d = (frK P K ^ s) (∑ a ∈ primeTo l s, lam a) ∧ cycVal P K s e lam d = (l : Om l) ^ ((e + 1) * (s - 1)) * α := by
  first | exact @GlobalTheory.ExpImage.exists_cycVal_eq_pow_mul | exact GlobalTheory.ExpImage.exists_cycVal_eq_pow_mul | (intros; apply GlobalTheory.ExpImage.exists_cycVal_eq_pow_mul <;> assumption)
end
end
