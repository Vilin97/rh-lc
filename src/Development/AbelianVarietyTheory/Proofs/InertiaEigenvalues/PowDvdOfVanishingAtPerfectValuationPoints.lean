module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdicCompletionPrincipalPerfect
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
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdicCompletionValuationRingCompleteValuationDoma
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdicCompletionPrincipalPerfectStatement

section

@[expose] public section

open scoped NNReal

theorem _root_.GlobalTheory.T.adicCompletion_principal_perfect : ∀ (l : ℕ) [Fact l.Prime] (V : Type) [CommRing V] [CharP V l] [PerfectRing V l] (x : V), ((l : ℕ) : AdicCompletion (Ideal.span {x}) V) = 0 ∧ Function.Bijective fun y : AdicCompletion (Ideal.span {x}) V => y ^ l := by
  first | exact @GlobalTheory.PerfectCompletion.perfect | exact GlobalTheory.PerfectCompletion.perfect | (intros; apply GlobalTheory.PerfectCompletion.perfect <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdicCompletionValuationRingCompleteValuationDomaStatement

section

@[expose] public section

open scoped NNReal

theorem _root_.GlobalTheory.T.adicCompletion_valuationRing_complete_valuationDomain : ∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] (x : V), x ≠ 0 → ¬ IsUnit x → IsDomain (AdicCompletion (Ideal.span {x}) V) ∧ PreValuationRing (AdicCompletion (Ideal.span {x}) V) ∧ algebraMap V (AdicCompletion (Ideal.span {x}) V) x ≠ 0 ∧ ¬ IsUnit (algebraMap V (AdicCompletion (Ideal.span {x}) V) x) ∧ IsAdicComplete (Ideal.span {algebraMap V (AdicCompletion (Ideal.span {x}) V) x}) (AdicCompletion (Ideal.span {x}) V) := by
  first | exact @GlobalTheory.adicCompletion_valuationRing_props | exact GlobalTheory.adicCompletion_valuationRing_props | (intros; apply GlobalTheory.adicCompletion_valuationRing_props <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsValuationSubringAlgClosedNotIsUnit

section

@[expose] public section

open scoped NNReal

namespace GlobalTheory

theorem exists_valuationSubring_not_isUnit_and_nonZeroDivisors_ne_zero :
    ∀ (S : Type) [CommRing S] (u : S), ¬ IsUnit u →
      ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (V : ValuationSubring L) (f : S →+* ↥V),
        ¬ IsUnit (f u) ∧ ∀ s ∈ nonZeroDivisors S, f s ≠ 0 := by
  intro S _ u hu
  obtain ⟨m, hm, hum⟩ := Ideal.exists_le_maximal (Ideal.span {u})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hum' : u ∈ m := hum (Ideal.mem_span_singleton_self u)
  haveI := hm.isPrime
  obtain ⟨q, hq, hqm⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal S)) (J := m) bot_le
  haveI hqp : q.IsPrime := hq.1.1
  let L := AlgebraicClosure (FractionRing (S ⧸ q))
  let g : S →+* L := ((algebraMap (FractionRing (S ⧸ q)) L).comp
    (algebraMap (S ⧸ q) (FractionRing (S ⧸ q)))).comp (Ideal.Quotient.mk q)
  have hg : ∀ s, g s = 0 ↔ s ∈ q := by
    intro s
    simp only [g, RingHom.comp_apply]
    rw [map_eq_zero_iff _ (algebraMap (FractionRing (S ⧸ q)) L).injective,
      map_eq_zero_iff _ (IsFractionRing.injective (S ⧸ q) (FractionRing (S ⧸ q))),
      Ideal.Quotient.eq_zero_iff_mem]
  have hne : m.map g.rangeRestrict ≠ ⊤ := by
    intro h
    have h1 : (1 : g.range) ∈ m.map g.rangeRestrict := h ▸ Submodule.mem_top
    obtain ⟨x, hx, hx1⟩ :=
      (Ideal.mem_map_iff_of_surjective _ g.rangeRestrict_surjective).1 h1
    have h2 : g (x - 1) = 0 := by
      have := congrArg Subtype.val hx1
      simp only [RingHom.coe_rangeRestrict, OneMemClass.coe_one] at this
      rw [map_sub, this, map_one, sub_self]
    have h3 : x - 1 ∈ m := hqm ((hg _).1 h2)
    have h4 : (1 : S) ∈ m := by simpa using m.sub_mem hx h3
    exact hm.ne_top ((Ideal.eq_top_iff_one m).2 h4)
  obtain ⟨V, hV, hV'⟩ := Ideal.image_subset_nonunits_valuationSubring _ hne
  have hmem : ∀ s, g s ∈ V := fun s => hV (show g s ∈ g.range from ⟨s, rfl⟩)
  refine ⟨L, inferInstance, inferInstance, V, g.codRestrict V hmem, ?_, ?_⟩
  · have h1 : g u ∈ V.nonunits :=
      hV' ⟨g.rangeRestrict u, Ideal.mem_map_of_mem _ hum', rfl⟩
    have h2 := (ValuationSubring.coe_mem_nonunits_iff (A := V) (a := ⟨g u, hmem u⟩)).1 h1
    exact h2
  · intro s hs h0
    have h1 : g s = 0 := congrArg Subtype.val h0
    exact Set.disjoint_left.1 (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hq)
      ((hg s).1 h1) hs

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsValuationSubringAlgClosedNotIsUnitStatement

section

@[expose] public section

open scoped NNReal

theorem _root_.GlobalTheory.T.exists_valuationSubring_algClosed_not_isUnit : ∀ (S : Type) [CommRing S] (u : S), ¬ IsUnit u → ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (V : ValuationSubring L) (f : S →+* ↥V), ¬ IsUnit (f u) ∧ ∀ s ∈ nonZeroDivisors S, f s ≠ 0 := by
  first | exact @GlobalTheory.exists_valuationSubring_not_isUnit_and_nonZeroDivisors_ne_zero | exact GlobalTheory.exists_valuationSubring_not_isUnit_and_nonZeroDivisors_ne_zero | (intros; apply GlobalTheory.exists_valuationSubring_not_isUnit_and_nonZeroDivisors_ne_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundedPowersOrExistsValuationSubringDvd

section

@[expose] public section

open scoped NNReal
open Polynomial

namespace GlobalTheory

theorem pow_dvd_pow_mul_pow_of_homogeneous_relation {R : Type*} [CommRing R] (v x : R)
    (q : ℕ → R) (n N : ℕ) (h0 : IsUnit (q 0))
    (h : x ^ N * ∑ i ∈ Finset.range (n + 1), q i * v ^ i * x ^ (n - i) = 0) (j : ℕ) :
    v ^ j ∣ v ^ (N + n) * x ^ j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    by_cases hj : j ≤ N + n
    · exact Dvd.dvd.mul_right (pow_dvd_pow v hj) _
    · obtain ⟨d, rfl⟩ : ∃ d, j = N + n + d := ⟨j - (N + n), by omega⟩
      rw [Finset.sum_range_succ'] at h
      have key : q 0 * (v ^ (N + n) * x ^ (N + n + d)) =
          - ∑ i ∈ Finset.range n,
            v ^ (N + n) * x ^ d * x ^ N * (q (i + 1) * v ^ (i + 1) * x ^ (n - (i + 1))) := by
        rw [← Finset.mul_sum]
        simp only [pow_zero, mul_one, Nat.sub_zero] at h
        linear_combination (v ^ (N + n) * x ^ d) * h
      rw [← h0.dvd_mul_left, key, dvd_neg]
      refine Finset.dvd_sum fun i hi => ?_
      have hi' : i < n := Finset.mem_range.1 hi
      obtain ⟨e, rfl⟩ : ∃ e, n = i + 1 + e := ⟨n - (i + 1), by omega⟩
      obtain ⟨w, hw⟩ := ih (N + e + d) (by omega)
      refine ⟨q (i + 1) * w, ?_⟩
      rw [Nat.add_sub_cancel_left]
      linear_combination (q (i + 1) * v ^ (i + 1)) * hw

theorem bounded_powers_or_exists_valuationSubring_dvd :
    ∀ (R : Type) [CommRing R] (u x : R) (M : ℕ), u ∈ nonZeroDivisors R →
      (∀ r, IsUnit (1 - u * r)) →
      (∃ c : ℕ, ∀ n : ℕ, u ^ (M * n) ∣ u ^ c * x ^ n) ∨
        ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (V : ValuationSubring L)
          (f : R →+* ↥V), f u ≠ 0 ∧ ¬ IsUnit (f u) ∧ f x ∣ f u ^ M := by
  intro R _ u x M hu hJ
  let T := Localization.Away (u * x)
  have hux : IsUnit (algebraMap R T (u * x)) := IsLocalization.Away.algebraMap_isUnit (u * x)
  rw [map_mul, IsUnit.mul_iff] at hux
  obtain ⟨huT, hxT⟩ := hux
  obtain ⟨y, hy⟩ := hxT.exists_right_inv
  let t : T := algebraMap R T u ^ M * y
  have ht : algebraMap R T x * t = algebraMap R T u ^ M := by
    simp only [t]
    linear_combination (algebraMap R T u ^ M) * hy
  let S := Algebra.adjoin R ({t} : Set T)
  by_cases hS : IsUnit (algebraMap R S u)
  · left
    obtain ⟨⟨z, hz⟩, hz1⟩ := hS.exists_right_inv
    have hz2 : algebraMap R T u * z = 1 := congrArg Subtype.val hz1
    have hz' := hz
    simp only [S] at hz'
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hz'
    obtain ⟨p, hp⟩ := hz'
    have hp' : aeval t p = z := hp
    set q : R[X] := 1 - C u * p with hq
    have hq0 : aeval t q = 0 := by
      simp [hq, hp', hz2]
    have hc : IsUnit (q.coeff 0) := by
      simpa [hq] using hJ (p.coeff 0)
    have hsum : algebraMap R T
        (∑ i ∈ Finset.range (q.natDegree + 1),
          q.coeff i * (u ^ M) ^ i * x ^ (q.natDegree - i)) = 0 := by
      have h1 : algebraMap R T x ^ q.natDegree * aeval t q = 0 := by rw [hq0, mul_zero]
      rw [aeval_eq_sum_range, Finset.mul_sum] at h1

      rw [map_sum, ← h1]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ q.natDegree := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hi'
      rw [he, Nat.add_sub_cancel_left, Algebra.smul_def]
      simp only [map_mul, map_pow]
      rw [← ht]
      ring
    obtain ⟨⟨_, N, rfl⟩, hN⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers (u * x)) T _).1 hsum
    simp only [mul_pow, mul_assoc] at hN
    have hN' := (mul_left_mem_nonZeroDivisors_eq_zero_iff (pow_mem hu N)).1 hN
    refine ⟨M * (N + q.natDegree), fun j => ?_⟩
    rw [pow_mul, pow_mul]
    refine pow_dvd_pow_mul_pow_of_homogeneous_relation (u ^ M) x q.coeff _ N hc ?_ j
    simpa only [mul_assoc] using hN'
  · right
    obtain ⟨L, _, _, V, f, hf1, hf2⟩ := GlobalTheory.T.exists_valuationSubring_algClosed_not_isUnit S _ hS
    refine ⟨L, inferInstance, inferInstance, V, f.comp (algebraMap R S), ?_, hf1, ?_⟩
    · refine hf2 _ (mem_nonZeroDivisors_iff_right.2 fun s hs => ?_)
      have h1 : (s : T) * algebraMap R T u = 0 := congrArg Subtype.val hs
      exact Subtype.ext (huT.mul_left_eq_zero.1 h1)
    · refine ⟨f ⟨t, Algebra.self_mem_adjoin_singleton R t⟩, ?_⟩
      simp only [RingHom.comp_apply]
      rw [← map_mul, ← map_pow]
      congr 1
      exact Subtype.ext ht.symm

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundedPowersOrExistsValuationSubringDvdStatement

section

@[expose] public section

open scoped NNReal

theorem _root_.GlobalTheory.T.pow_dvd_bound_or_exists_valuationSubring_dvd : ∀ (R : Type) [CommRing R] (u x : R) (M : ℕ), u ∈ nonZeroDivisors R → (∀ r, IsUnit (1 - u * r)) → (∃ c : ℕ, ∀ n : ℕ, u ^ (M * n) ∣ u ^ c * x ^ n) ∨ ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (V : ValuationSubring L) (f : R →+* ↥V), f u ≠ 0 ∧ ¬ IsUnit (f u) ∧ f x ∣ f u ^ M := by
  first | exact @GlobalTheory.bounded_powers_or_exists_valuationSubring_dvd | exact GlobalTheory.bounded_powers_or_exists_valuationSubring_dvd | (intros; apply GlobalTheory.bounded_powers_or_exists_valuationSubring_dvd <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowDvdOfVanishingAtPerfectValuationPoints

section

@[expose] public section

open scoped NNReal

namespace GlobalTheory

theorem perfectRing_valuationSubring_of_isAlgClosed (l : ℕ) [Fact l.Prime] {L : Type} [Field L]
    [IsAlgClosed L] (V : ValuationSubring L) [CharP V l] : PerfectRing V l := by
  haveI : ExpChar V l := ExpChar.prime Fact.out
  refine PerfectRing.ofSurjective V l ?_
  intro v
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (v : L) (Nat.pos_of_ne_zero hl0)
  have hyV : y ∈ V := by
    rw [← V.valuation_le_one_iff]
    have hv : V.valuation (v : L) ≤ 1 := (V.valuation_le_one_iff _).2 v.2
    rw [← hy, map_pow] at hv
    exact (pow_le_one_iff_of_nonneg (zero_le') hl0).1 hv
  refine ⟨⟨y, hyV⟩, ?_⟩
  apply Subtype.ext
  simp [frobenius_def, hy]

theorem s_points_kpt : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (u x : R), ((l : ℕ) : R) = 0 →
    u ∈ nonZeroDivisors R → (∀ r, IsUnit (1 - u * r)) →
    (∀ (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l]
      (f : R →+* O), f u ≠ 0 → ¬ IsUnit (f u) → IsAdicComplete (Ideal.span {f u}) O → f x = 0) →
    ∀ M : ℕ, ∃ c : ℕ, ∀ n : ℕ, u ^ (M * n) ∣ u ^ c * x ^ n := by
  intro l _ R _ u x hl hu hrad H M
  rcases GlobalTheory.T.pow_dvd_bound_or_exists_valuationSubring_dvd R u x M hu hrad with h | ⟨L, _, _, V, f, hfu, hfnu, hdvd⟩
  · exact h
  exfalso
  haveI : CharP V l := (CharP.charP_iff_prime_eq_zero Fact.out).2 (by
    rw [← map_natCast f, hl, map_zero])
  haveI : PerfectRing V l := perfectRing_valuationSubring_of_isAlgClosed l V
  obtain ⟨hdom, hpre, hne, hnu, hcomp⟩ := GlobalTheory.T.adicCompletion_valuationRing_complete_valuationDomain V (f u) hfu hfnu
  obtain ⟨hl', hbij⟩ := GlobalTheory.T.adicCompletion_principal_perfect l V (f u)
  set O := AdicCompletion (Ideal.span {f u}) V
  haveI : IsDomain O := hdom
  haveI : ValuationRing O := { toPreValuationRing := hpre }
  haveI : CharP O l := (CharP.charP_iff_prime_eq_zero Fact.out).2 hl'
  haveI : PerfectRing O l := ⟨hbij⟩
  let g : R →+* O := (algebraMap V O).comp f
  have hgx : g x = 0 := H O g hne hnu hcomp
  have hd : g x ∣ g u ^ M := by
    simpa [g, map_pow] using map_dvd (algebraMap V O) hdvd
  rw [hgx, zero_dvd_iff] at hd
  exact hne (by_contra fun h => pow_ne_zero M h hd)

end GlobalTheory
end
end
