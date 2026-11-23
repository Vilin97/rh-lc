module

public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.NumberTheory.Padics.Complex
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardRootsClosedBallBoundsUltrametricStatement
public import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.TypeStar
public import Mathlib.Analysis.Normed.Group.Defs
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Normed.Group.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdditivePolyTaylorCoeffSubNormLe

section

@[expose] public section

open Polynomial

namespace GlobalTheory

theorem additive_poly_taylor_coeff_sub_norm_le :
    ∀ (l : ℕ) [Fact l.Prime] (E : ℕ) (a : ℕ → ℂ_[l]) (W : ℂ_[l]), (∀ k, k ≤ E → ‖a k‖ ≤ 1) → ‖W‖ ≤ 1 →
      ∀ j : ℕ, 1 ≤ j → ‖(Polynomial.taylor W (∑ k ∈ Finset.range (E + 1), Polynomial.monomial (l ^ k) (a k) : Polynomial ℂ_[l])).coeff j - (∑ k ∈ Finset.range (E + 1), Polynomial.monomial (l ^ k) (a k) : Polynomial ℂ_[l]).coeff j‖ ≤ ‖(l : ℂ_[l])‖ := by
  intro l hl E a W ha hW j hj
  have hp : l.Prime := hl.out

  rw [map_sum, Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun k hk => ?_
  have hak : ‖a k‖ ≤ 1 := ha k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  rw [Polynomial.taylor_monomial, ← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_C_mul,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow, Polynomial.coeff_X_pow]
  rcases lt_trichotomy j (l ^ k) with h | h | h
  · have hne : j ≠ l ^ k := h.ne
    simp only [hne, if_false, mul_zero, sub_zero]
    obtain ⟨m, hm⟩ : l ∣ (l ^ k).choose j := hp.dvd_choose_pow (by omega) h.ne
    rw [hm, Nat.cast_mul, norm_mul, norm_mul, norm_mul]
    have h1 : ‖W ^ (l ^ k - j)‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hW
    have h2 : ‖(m : ℂ_[l])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ m
    calc ‖a k‖ * (‖W ^ (l ^ k - j)‖ * (‖(l : ℂ_[l])‖ * ‖(m : ℂ_[l])‖))
        ≤ 1 * (1 * (‖(l : ℂ_[l])‖ * 1)) := by gcongr
      _ = ‖(l : ℂ_[l])‖ := by ring
  · subst h
    simp
  · have hne : j ≠ l ^ k := h.ne'
    simp only [hne, if_false, mul_zero, sub_zero, Nat.choose_eq_zero_of_lt h, Nat.cast_zero]
    simp

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdditivePolyTaylorCoeffSubNormLeStatement

section

@[expose] public section

open Polynomial

theorem _root_.GlobalTheory.T.norm_taylor_coeff_sub_coeff_le_norm_l : ∀ (l : ℕ) [Fact l.Prime] (E : ℕ) (a : ℕ → ℂ_[l]) (W : ℂ_[l]), (∀ k, k ≤ E → ‖a k‖ ≤ 1) → ‖W‖ ≤ 1 → ∀ j : ℕ, 1 ≤ j → ‖(Polynomial.taylor W (∑ k ∈ Finset.range (E + 1), Polynomial.monomial (l ^ k) (a k) : Polynomial ℂ_[l])).coeff j - (∑ k ∈ Finset.range (E + 1), Polynomial.monomial (l ^ k) (a k) : Polynomial ℂ_[l]).coeff j‖ ≤ ‖(l : ℂ_[l])‖ := by
  first | exact @GlobalTheory.additive_poly_taylor_coeff_sub_norm_le | exact GlobalTheory.additive_poly_taylor_coeff_sub_norm_le | (intros; apply GlobalTheory.additive_poly_taylor_coeff_sub_norm_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FewRootsSmallDisc

section

@[expose] public section

open Polynomial
open Classical

namespace GlobalTheory

theorem roots_taylor_eq_map_sub {K : Type*} [Field K] (p : K[X]) (w : K) :
    (taylor w p).roots = p.roots.map (fun x => x - w) := by
  have h := roots_comp_C_mul_X_add_C p (1 : K) w isUnit_one
  rw [taylor_apply]
  simpa using h

theorem coeff_sum_monomial_pow (l : ℕ) [Fact l.Prime] (E : ℕ) (a : ℕ → ℂ_[l]) (k : ℕ)
    (hk : k ≤ E) :
    (∑ i ∈ Finset.range (E + 1), monomial (l ^ i) (a i) : ℂ_[l][X]).coeff (l ^ k) = a k := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  rw [finsetSum_coeff, Finset.sum_eq_single k]
  · simp [coeff_monomial]
  · intro i _ hik
    rw [coeff_monomial, Finsupp.single_apply, if_neg]
    intro h
    exact hik (Nat.pow_right_injective hl h)
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

theorem coeff_sum_monomial_small (l : ℕ) [Fact l.Prime] (E M : ℕ) (a : ℕ → ℂ_[l]) (ρ : ℝ)
    (hρ : 0 < ρ)
    (hgt : ∀ k, M < k → k ≤ E → ‖a k‖ * ρ ^ l ^ k < ‖(l : ℂ_[l])‖) (j : ℕ) (hj : l ^ M < j) :
    ‖(∑ i ∈ Finset.range (E + 1), monomial (l ^ i) (a i) : ℂ_[l][X]).coeff j‖ * ρ ^ j
      < ‖(l : ℂ_[l])‖ := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hlpos : 0 < ‖(l : ℂ_[l])‖ := by
    rw [norm_pos_iff]; exact_mod_cast (by omega : l ≠ 0)
  by_cases h : ∃ k, k ≤ E ∧ l ^ k = j
  · obtain ⟨k, hkE, rfl⟩ := h
    rw [coeff_sum_monomial_pow l E a k hkE]
    have hMk : M < k := (Nat.pow_lt_pow_iff_right (by omega)).mp hj
    exact hgt k hMk hkE
  · have h0 : (∑ i ∈ Finset.range (E + 1), monomial (l ^ i) (a i) : ℂ_[l][X]).coeff j = 0 := by
      rw [finsetSum_coeff]
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [coeff_monomial, Finsupp.single_apply, if_neg]
      intro hij
      exact h ⟨i, by have := Finset.mem_range.mp hi; omega, hij⟩
    rw [h0, norm_zero, zero_mul]
    exact hlpos

theorem few_roots_small_disc : ∀ (l : ℕ) [Fact l.Prime] (E M : ℕ) (a : ℕ → ℂ_[l]) (ρ : ℝ) (W : ℂ_[l]), M ≤ E → (∀ k, k ≤ E → ‖a k‖ ≤ 1) → 0 < ρ → ρ < 1 → ‖a M‖ * ρ ^ l ^ M = ‖(l : ℂ_[l])‖ → (∀ k, M < k → k ≤ E → ‖a k‖ * ρ ^ l ^ k < ‖(l : ℂ_[l])‖) → ‖W‖ ≤ 1 → Multiset.card ((∑ k ∈ Finset.range (E + 1), Polynomial.monomial (l ^ k) (a k) : Polynomial ℂ_[l]).roots.filter fun z => ‖z - W‖ ≤ ρ) ≤ l ^ M := by
  intro l _ E M a ρ W hME ha hρ0 hρ1 hM hgt hW
  set G : ℂ_[l][X] := ∑ k ∈ Finset.range (E + 1), monomial (l ^ k) (a k) with hG
  set H := taylor W G with hH
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hlpos : 0 < ‖(l : ℂ_[l])‖ := by
    rw [norm_pos_iff]; exact_mod_cast (by omega : l ≠ 0)
  have hroots : Multiset.card (G.roots.filter fun z => ‖z - W‖ ≤ ρ)
      = Multiset.card (H.roots.filter fun z => ‖z‖ ≤ ρ) := by
    rw [hH, roots_taylor_eq_map_sub, Multiset.filter_map, Multiset.card_map]
    rfl
  rw [hroots]
  have hd1 : 1 ≤ l ^ M := Nat.one_le_pow _ _ (by omega)
  have hGd : G.coeff (l ^ M) = a M := coeff_sum_monomial_pow l E a M hME
  have hdiff : ∀ j, 1 ≤ j → ‖H.coeff j - G.coeff j‖ ≤ ‖(l : ℂ_[l])‖ :=
    GlobalTheory.T.norm_taylor_coeff_sub_coeff_le_norm_l l E a W ha hW
  have hρj : ∀ j, 1 ≤ j → ρ ^ j < 1 := fun j hj => pow_lt_one₀ hρ0.le hρ1 (by omega)
  have hdiffsmall : ∀ j, 1 ≤ j → ‖H.coeff j - G.coeff j‖ * ρ ^ j < ‖(l : ℂ_[l])‖ := by
    intro j hj
    calc ‖H.coeff j - G.coeff j‖ * ρ ^ j ≤ ‖(l : ℂ_[l])‖ * ρ ^ j :=
          mul_le_mul_of_nonneg_right (hdiff j hj) (by positivity)
      _ < ‖(l : ℂ_[l])‖ := mul_lt_of_lt_one_right hlpos (hρj j hj)
  have hHd : ‖H.coeff (l ^ M)‖ * ρ ^ l ^ M = ‖(l : ℂ_[l])‖ := by
    have hlt : ‖H.coeff (l ^ M) - G.coeff (l ^ M)‖ < ‖G.coeff (l ^ M)‖ := by
      have h1 : ‖H.coeff (l ^ M) - G.coeff (l ^ M)‖ * ρ ^ l ^ M
          < ‖G.coeff (l ^ M)‖ * ρ ^ l ^ M := by
        rw [hGd, hM]; have h0 := hdiffsmall _ hd1; rwa [hGd] at h0
      exact lt_of_mul_lt_mul_right h1 (by positivity)
    have h2 : H.coeff (l ^ M) = G.coeff (l ^ M) + (H.coeff (l ^ M) - G.coeff (l ^ M)) := by ring
    rw [h2, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le, hGd, hM]
  have hHd0 : H.coeff (l ^ M) ≠ 0 := by
    intro h0
    rw [h0, norm_zero, zero_mul] at hHd
    exact hlpos.ne hHd
  have hbig : ∀ j, l ^ M < j → ‖H.coeff j‖ * ρ ^ j < ‖H.coeff (l ^ M)‖ * ρ ^ l ^ M := by
    intro j hj
    rw [hHd]
    have h2 : H.coeff j = G.coeff j + (H.coeff j - G.coeff j) := by ring
    have h3 := IsUltrametricDist.norm_add_le_max (G.coeff j) (H.coeff j - G.coeff j)
    rw [← h2] at h3
    have hρ : 0 ≤ ρ ^ j := by positivity
    calc ‖H.coeff j‖ * ρ ^ j ≤ max ‖G.coeff j‖ ‖H.coeff j - G.coeff j‖ * ρ ^ j :=
          mul_le_mul_of_nonneg_right h3 hρ
      _ = max (‖G.coeff j‖ * ρ ^ j) (‖H.coeff j - G.coeff j‖ * ρ ^ j) := max_mul_of_nonneg _ _ hρ
      _ < ‖(l : ℂ_[l])‖ := max_lt (coeff_sum_monomial_small l E M a ρ hρ0 hgt j hj)
          (hdiffsmall j (by omega))
  exact (GlobalTheory.T.card_roots_closedBall_bounds_ultrametric ℂ_[l] H ρ (l ^ M) hρ0 hHd0).2 hbig

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FewRootsSmallDiscStatement

section

@[expose] public section

open Polynomial
open Classical

theorem _root_.GlobalTheory.T.card_roots_closedBall_le_prime_pow : ∀ (l : ℕ) [Fact l.Prime] (E M : ℕ) (a : ℕ → ℂ_[l]) (ρ : ℝ) (W : ℂ_[l]), M ≤ E → (∀ k, k ≤ E → ‖a k‖ ≤ 1) → 0 < ρ → ρ < 1 → ‖a M‖ * ρ ^ l ^ M = ‖(l : ℂ_[l])‖ → (∀ k, M < k → k ≤ E → ‖a k‖ * ρ ^ l ^ k < ‖(l : ℂ_[l])‖) → ‖W‖ ≤ 1 → Multiset.card ((∑ k ∈ Finset.range (E + 1), Polynomial.monomial (l ^ k) (a k) : Polynomial ℂ_[l]).roots.filter fun z => ‖z - W‖ ≤ ρ) ≤ l ^ M := by
  first | exact @GlobalTheory.few_roots_small_disc | exact GlobalTheory.few_roots_small_disc | (intros; apply GlobalTheory.few_roots_small_disc <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MultisetManySeparatedPoints

section

@[expose] public section

open Polynomial
open Classical

namespace GlobalTheory

theorem multiset_many_separated_points : ∀ (K : Type) [NormedAddCommGroup K] (s : Multiset K) (ρ : ℝ) (A B : ℕ), 0 ≤ ρ → 0 < B → A * B ≤ Multiset.card s → (∀ W ∈ s, Multiset.card (s.filter fun z => ‖z - W‖ ≤ ρ) ≤ B) → ∃ Z : Finset K, A ≤ Z.card ∧ (∀ W ∈ Z, W ∈ s) ∧ ∀ W ∈ Z, ∀ W' ∈ Z, W ≠ W' → ρ < ‖W - W'‖ := by
  intro K _ s ρ A B hρ hB hAB hball
  set S := s.toFinset.powerset.filter
    (fun Z : Finset K => ∀ W ∈ Z, ∀ W' ∈ Z, W ≠ W' → ρ < ‖W - W'‖) with hS
  have hne : S.Nonempty := ⟨∅, by simp [hS]⟩
  obtain ⟨Z, hZS, hZmax⟩ := Finset.exists_max_image S Finset.card hne
  rw [hS, Finset.mem_filter, Finset.mem_powerset] at hZS
  obtain ⟨hZsub, hZsep⟩ := hZS
  have hZs : ∀ W ∈ Z, W ∈ s := fun W hW => Multiset.mem_toFinset.mp (hZsub hW)
  have hcov : ∀ z ∈ s, ∃ W ∈ Z, ‖z - W‖ ≤ ρ := by
    intro z hz
    by_contra h
    push_neg at h
    have hzZ : z ∉ Z := by
      intro hzZ
      have := h z hzZ
      simp at this
      linarith
    have hmem : insert z Z ∈ S := by
      rw [hS, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.insert_subset (Multiset.mem_toFinset.mpr hz) hZsub, ?_⟩
      intro W hW W' hW' hne
      rw [Finset.mem_insert] at hW hW'
      rcases hW with rfl | hW <;> rcases hW' with rfl | hW'
      · exact absurd rfl hne
      · exact h W' hW'
      · rw [norm_sub_rev]; exact h W hW
      · exact hZsep W hW W' hW' hne
    have := hZmax _ hmem
    rw [Finset.card_insert_of_notMem hzZ] at this
    omega
  have hle : s ≤ ∑ W ∈ Z, s.filter (fun z => ‖z - W‖ ≤ ρ) := by
    rw [Multiset.le_iff_count]
    intro a
    rw [Multiset.count_sum']
    by_cases ha : a ∈ s
    · obtain ⟨W, hW, hd⟩ := hcov a ha
      calc Multiset.count a s = Multiset.count a (s.filter (fun z => ‖z - W‖ ≤ ρ)) := by
            rw [Multiset.count_filter_of_pos (p := fun z => ‖z - W‖ ≤ ρ) hd]
        _ ≤ _ := Finset.single_le_sum
            (f := fun W => Multiset.count a (s.filter (fun z => ‖z - W‖ ≤ ρ)))
            (fun _ _ => Nat.zero_le _) hW
    · rw [Multiset.count_eq_zero_of_notMem ha]; exact Nat.zero_le _
  have hcard : Multiset.card s ≤ Z.card * B := by
    calc Multiset.card s ≤ Multiset.card (∑ W ∈ Z, s.filter (fun z => ‖z - W‖ ≤ ρ)) :=
          Multiset.card_le_card hle
      _ = ∑ W ∈ Z, Multiset.card (s.filter (fun z => ‖z - W‖ ≤ ρ)) := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp [map_sum]
      _ ≤ ∑ W ∈ Z, B := Finset.sum_le_sum fun W hW => hball W (hZs W hW)
      _ = Z.card * B := by simp
  exact ⟨Z, Nat.le_of_mul_le_mul_right (hAB.trans hcard) hB, hZs, hZsep⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MultisetManySeparatedPointsStatement

section

@[expose] public section

open Polynomial
open Classical

theorem _root_.GlobalTheory.T.exists_finset_separated_of_multiset_bounded_cluster : ∀ (K : Type) [NormedAddCommGroup K] (s : Multiset K) (ρ : ℝ) (A B : ℕ), 0 ≤ ρ → 0 < B → A * B ≤ Multiset.card s → (∀ W ∈ s, Multiset.card (s.filter fun z => ‖z - W‖ ≤ ρ) ≤ B) → ∃ Z : Finset K, A ≤ Z.card ∧ (∀ W ∈ Z, W ∈ s) ∧ ∀ W ∈ Z, ∀ W' ∈ Z, W ≠ W' → ρ < ‖W - W'‖ := by
  first | exact @GlobalTheory.multiset_many_separated_points | exact GlobalTheory.multiset_many_separated_points | (intros; apply GlobalTheory.multiset_many_separated_points <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeparatedRootsAdditivePoly

section

@[expose] public section

open Polynomial
open Classical

namespace GlobalTheory

theorem separated_roots_additive_poly : ∀ (l : ℕ) [Fact l.Prime] (E M h : ℕ) (a : ℕ → ℂ_[l]) (ρ : ℝ), M + h ≤ E → (∀ k, k ≤ E → ‖a k‖ ≤ 1) → ‖a (M + h)‖ = 1 → 0 < ρ → ρ < 1 → ‖a M‖ * ρ ^ l ^ M = ‖(l : ℂ_[l])‖ → (∀ k, M < k → k ≤ E → ‖a k‖ * ρ ^ l ^ k < ‖(l : ℂ_[l])‖) → ∃ Z : Finset ℂ_[l], l ^ h ≤ Z.card ∧ (∀ W ∈ Z, ‖W‖ ≤ 1 ∧ ∑ k ∈ Finset.range (E + 1), a k * W ^ l ^ k = 0) ∧ ∀ W ∈ Z, ∀ W' ∈ Z, W ≠ W' → ρ < ‖W - W'‖ := by
  intro l _ E M h a ρ hMh ha1 haMh hρ0 hρ1 haM hak
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hinj : Function.Injective (fun k : ℕ => l ^ k) := Nat.pow_right_injective hl
  set G : ℂ_[l][X] := ∑ k ∈ Finset.range (E + 1), Polynomial.monomial (l ^ k) (a k) with hG
  have hcoeff : ∀ j, G.coeff j = ∑ k ∈ Finset.range (E + 1), if l ^ k = j then a k else 0 := by
    intro j
    simp only [hG, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial_apply]
  have hcd : G.coeff (l ^ (M + h)) = a (M + h) := by
    rw [hcoeff, Finset.sum_eq_single (M + h)]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro hh; exact hb (hinj hh)
    · intro hn; exact absurd (Finset.mem_range.2 (by omega)) hn
  have hcd0 : G.coeff (l ^ (M + h)) ≠ 0 := by
    rw [hcd]; intro h0; rw [h0, norm_zero] at haMh; exact zero_ne_one haMh
  have hcle : ∀ j, ‖G.coeff j‖ ≤ 1 := by
    intro j
    rw [hcoeff]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k hk => ?_
    split_ifs
    · exact ha1 k (by have := Finset.mem_range.1 hk; omega)
    · simp
  have hrc := (GlobalTheory.T.card_roots_closedBall_bounds_ultrametric ℂ_[l] G 1 (l ^ (M + h)) one_pos hcd0).1 (by
    intro j; simp only [one_pow, mul_one]; rw [hcd, haMh]; exact hcle j)
  set s := G.roots.filter fun z => ‖z‖ ≤ 1 with hs
  have hG0 : G ≠ 0 := by
    intro h0; apply hcd0; rw [h0]; simp
  obtain ⟨Z, hZc, hZs, hZsep⟩ := GlobalTheory.T.exists_finset_separated_of_multiset_bounded_cluster ℂ_[l] s ρ (l ^ h) (l ^ M) hρ0.le
    (pow_pos (by omega) _) (by rw [mul_comm, ← pow_add]; exact hrc) (by
      intro W hW
      have hW1 : ‖W‖ ≤ 1 := (Multiset.mem_filter.1 hW).2
      refine le_trans (Multiset.card_le_card ?_) (GlobalTheory.T.card_roots_closedBall_le_prime_pow l E M a ρ W (by omega) ha1 hρ0 hρ1 haM hak hW1)
      exact Multiset.monotone_filter_left _ (Multiset.filter_le _ _))
  refine ⟨Z, hZc, fun W hW => ?_, hZsep⟩
  have hWs := Multiset.mem_filter.1 (hZs W hW)
  refine ⟨hWs.2, ?_⟩
  have hr := (Polynomial.mem_roots hG0).1 hWs.1
  have := hr.eq_zero
  rw [hG, Polynomial.eval_finsetSum] at this
  simpa [Polynomial.eval_monomial] using this

end GlobalTheory
end
end
