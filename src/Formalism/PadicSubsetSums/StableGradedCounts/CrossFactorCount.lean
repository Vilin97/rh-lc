module

public import Formalism.PadicSubsetSums.CentralIdempotents.EigenbasisOfDistinctRoots
public import Formalism.PadicSubsetSums.StableGradedCounts.CoeffZeroNeZeroOfIrreducible
import Formalism.PadicSubsetSums.StableGradedCounts.IRRIrredCountUpper
public import Formalism.PadicSubsetSums.CentralIdempotents.GaloisIrreducibility
public import Formalism.PadicSubsetSums.StableGradedCounts.IRRPrimeToPartSpec
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.PadicSubsetSums.StableGradedCounts.IRRSamePartCount
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Formalism.PadicSubsetSums.StableGradedCounts.IRRPrimeToPartEqIff

section

@[expose] public section

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem pow_lpow_add {M : Type*} [Monoid M] {l a : ℕ} {x z : M} (h : x ^ (l ^ a) = z ^ (l ^ a))
    (b : ℕ) : x ^ (l ^ (a + b)) = z ^ (l ^ (a + b)) := by
  rw [pow_add, pow_mul, pow_mul, h]

theorem eq_of_pow_eq_of_coprime_order {M : Type*} [Monoid M] {r : ℕ} {u w : M}
    (hu : 0 < orderOf u) (hw : 0 < orderOf w) (hcu : Nat.Coprime r (orderOf u))
    (hcw : Nat.Coprime r (orderOf w)) (h : u ^ r = w ^ r) : u = w := by
  by_cases h1 : orderOf u * orderOf w = 1
  · have hu1 : orderOf u = 1 := Nat.eq_one_of_mul_eq_one_right h1
    have hw1 : orderOf w = 1 := Nat.eq_one_of_mul_eq_one_left h1
    rw [orderOf_eq_one_iff.mp hu1, orderOf_eq_one_iff.mp hw1]
  · have hpos : 0 < orderOf u * orderOf w := Nat.mul_pos hu hw
    have hlt : 1 < orderOf u * orderOf w := by omega
    obtain ⟨s, -, hs⟩ := Nat.exists_mul_mod_eq_one_of_coprime (Nat.Coprime.mul_right hcu hcw) hlt
    have hmod : r * s ≡ 1 [MOD orderOf u * orderOf w] := by
      unfold Nat.ModEq
      rw [hs, Nat.mod_eq_of_lt hlt]
    have hm1 : r * s ≡ 1 [MOD orderOf u] := Nat.ModEq.of_mul_right (orderOf w) hmod
    have hm2 : r * s ≡ 1 [MOD orderOf w] := Nat.ModEq.of_mul_left (orderOf u) hmod
    have hu' : u ^ (r * s) = u := by
      rw [← pow_mod_orderOf, show r * s % orderOf u = 1 % orderOf u from hm1, pow_mod_orderOf,
        pow_one]
    have hw' : w ^ (r * s) = w := by
      rw [← pow_mod_orderOf, show r * s % orderOf w = 1 % orderOf w from hm2, pow_mod_orderOf,
        pow_one]
    rw [← hu', ← hw', pow_mul, pow_mul, h]

theorem prime_to_part_eq_iff : PrimeToPartEqIff := by
  intro M _ l x y hl hx hy
  obtain ⟨hox, a, ha⟩ := prime_to_part_spec M l x hl hx
  obtain ⟨hoy, b, hb⟩ := prime_to_part_spec M l y hl hy
  have hnx : orderOf x ≠ 0 := (orderOf_pos_iff.mpr hx).ne'
  have hny : orderOf y ≠ 0 := (orderOf_pos_iff.mpr hy).ne'
  constructor
  · intro h
    refine ⟨a + b, ?_⟩
    rw [pow_lpow_add ha b, h, add_comm a b, pow_lpow_add hb a]
  · rintro ⟨c, hc⟩
    have e1 : primeToPart l x ^ (l ^ (a + (b + c))) = x ^ (l ^ (a + (b + c))) :=
      (pow_lpow_add ha _).symm
    have e2 : primeToPart l y ^ (l ^ (b + (a + c))) = y ^ (l ^ (b + (a + c))) :=
      (pow_lpow_add hb _).symm
    have e3 : x ^ (l ^ (c + (a + b))) = y ^ (l ^ (c + (a + b))) := pow_lpow_add hc _
    have s1 : a + (b + c) = c + (a + b) := by omega
    have s2 : b + (a + c) = c + (a + b) := by omega
    rw [s1] at e1
    rw [s2] at e2
    refine eq_of_pow_eq_of_coprime_order (r := l ^ (c + (a + b))) ?_ ?_ ?_ ?_ (by rw [e1, e2, e3])
    · rw [hox]; exact Nat.ordCompl_pos l hnx
    · rw [hoy]; exact Nat.ordCompl_pos l hny
    · rw [hox]; exact Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hl hnx)
    · rw [hoy]; exact Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hl hny)

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
end

-- Source module: Formalism.PadicSubsetSums.StableGradedCounts.CrossFactorCount

section

@[expose] public section

open Finset Polynomial

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

section

variable {K L : Type} [Field K] [Fintype K] [Field L] [Algebra K L] [IsAlgClosed L]

theorem root_conj' {f : K[X]} (hi : Irreducible f) {x y : L} (hx : aeval x f = 0)
    (hy : aeval y f = 0) : ∃ n : ℕ, y = x ^ Fintype.card K ^ n := by
  have hf0 : f ≠ 0 := hi.ne_zero
  have hu : IsUnit (C f.leadingCoeff⁻¹ : K[X]) :=
    Polynomial.isUnit_C.mpr (IsUnit.mk0 _ (inv_ne_zero (leadingCoeff_ne_zero.mpr hf0)))
  have hm : (f * C f.leadingCoeff⁻¹).Monic := monic_mul_leadingCoeff_inv hf0
  have hi' : Irreducible (f * C f.leadingCoeff⁻¹) := (irreducible_mul_isUnit hu).mpr hi
  have hx' : aeval x (f * C f.leadingCoeff⁻¹) = 0 := by rw [map_mul, hx, zero_mul]
  have hy' : aeval y (f * C f.leadingCoeff⁻¹) = 0 := by rw [map_mul, hy, zero_mul]
  exact root_conj hm hi' hx' hy'

theorem card_samePart_le {l n : ℕ} (hl : l.Prime) (hn : n ≠ 0) (w : L) (S : Finset L)
    (hS : ∀ x ∈ S, x ^ n = 1 ∧ primeToPart l x = w) : S.card ≤ l ^ padicValNat l n := by
  classical
  rcases S.eq_empty_or_nonempty with hS0 | ⟨x0, hx0⟩
  · simp [hS0]
  obtain ⟨hx0n, hx0w⟩ := hS x0 hx0
  have hx0ne : x0 ≠ 0 := by
    rintro rfl
    rw [zero_pow hn] at hx0n
    exact zero_ne_one hx0n
  have hfin : ∀ x : L, x ^ n = 1 → IsOfFinOrder x := fun x hx =>
    isOfFinOrder_iff_pow_eq_one.mpr ⟨n, Nat.pos_of_ne_zero hn, hx⟩
  have hmap : ∀ x ∈ S, x * x0⁻¹ ∈ nthRootsFinset (l ^ padicValNat l n) (1 : L) := by
    intro x hx
    obtain ⟨hxn, hxw⟩ := hS x hx
    obtain ⟨a, ha⟩ := (prime_to_part_eq_iff L l x x0 hl (hfin x hxn) (hfin x0 hx0n)).mp
      (hxw.trans hx0w.symm)
    have hz : (x * x0⁻¹) ^ n = 1 := by rw [mul_pow, inv_pow, hxn, hx0n, inv_one, mul_one]
    have hza : (x * x0⁻¹) ^ (l ^ a) = 1 := by
      rw [mul_pow, inv_pow, ha, mul_inv_cancel₀ (pow_ne_zero _ hx0ne)]
    rw [mem_nthRootsFinset (pow_pos hl.pos _)]
    exact (lpow_order_iff hl hn _ hz).mp ⟨a, hza⟩
  calc S.card ≤ (nthRootsFinset (l ^ padicValNat l n) (1 : L)).card :=
        Finset.card_le_card_of_injOn (fun x => x * x0⁻¹) (fun x hx => hmap x hx)
          (fun a _ b _ h => mul_right_cancel₀ (inv_ne_zero hx0ne) h)
    _ ≤ l ^ padicValNat l n := card_nthRootsFinset_le _

end

theorem cross_factor_count : CrossFactorCount := by
  intro K L _ _ _ _ _ δ l P' hl hδ hP' hP'0 hBB
  classical
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  have hn : Fintype.card K ^ δ - 1 ≠ 0 :=
    Nat.sub_ne_zero_of_lt (Nat.one_lt_pow (by omega) hq)
  have hfin : ∀ (z : L) (m : ℕ), 0 < m → z ^ m = 1 → IsOfFinOrder z := fun z m hm h =>
    isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm, h⟩
  rcases (P'.rootSet L).eq_empty_or_nonempty with h0 | ⟨y0, hy0⟩
  · convert (by positivity : (0 : ℝ) ≤ (Fintype.card K : ℝ) ^ ((δ : ℝ) / 4))
    norm_cast
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro c - ⟨-, -, x, -, y, hy, -⟩
    rw [h0] at hy
    exact hy
  have hy0r : aeval y0 P' = 0 := (mem_rootSet.mp hy0).2
  have hm' : 0 < Fintype.card K ^ P'.natDegree - 1 :=
    Nat.sub_pos_of_lt (Nat.one_lt_pow (Irreducible.natDegree_pos hP').ne' hq)
  let S := (nthRootsFinset (Fintype.card K ^ δ - 1) (1 : L)).filter
    (fun x => primeToPart l x = primeToPart l y0)
  have hSprop : ∀ x ∈ S, x ^ (Fintype.card K ^ δ - 1) = 1 ∧ primeToPart l x = primeToPart l y0 := by
    intro x hx
    rw [Finset.mem_filter, mem_nthRootsFinset (Nat.pos_of_ne_zero hn)] at hx
    exact hx
  refine le_trans (Nat.cast_le.mpr (card_le_of_root_mem _ ?_ S ?_)) ?_
  · intro c hc
    exact (Finset.mem_filter.mp hc).2.1
  · intro c hc
    obtain ⟨hirr, hc0, x, hx, y, hy, hxy⟩ := (Finset.mem_filter.mp hc).2
    have hxr : aeval x (monicOf c) = 0 := (mem_rootSet.mp hx).2
    have hyr : aeval y P' = 0 := (mem_rootSet.mp hy).2
    obtain ⟨k, hk⟩ := root_conj' hP' hyr hy0r
    have hx'r := root_frob (f := monicOf c) k hxr
    refine ⟨x ^ Fintype.card K ^ k, ?_, hx'r⟩
    have hpow : ∀ {z : L}, aeval z (monicOf c) = 0 → z ^ (Fintype.card K ^ δ - 1) = 1 := by
      intro z hz
      have := root_pow_sub_one hirr hc0 hz
      rwa [monicOf_natDegree] at this
    have hyn : y ^ (Fintype.card K ^ P'.natDegree - 1) = 1 := root_pow_sub_one hP' hP'0 hyr
    have hyk : (y ^ Fintype.card K ^ k) ^ (Fintype.card K ^ P'.natDegree - 1) = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hyn, one_pow]
    rw [Finset.mem_filter, mem_nthRootsFinset (Nat.pos_of_ne_zero hn)]
    refine ⟨hpow hx'r, ?_⟩
    obtain ⟨a, ha⟩ := (prime_to_part_eq_iff L l x y hl
      (hfin x _ (Nat.pos_of_ne_zero hn) (hpow hxr)) (hfin y _ hm' hyn)).mp hxy
    rw [hk]
    refine (prime_to_part_eq_iff L l _ _ hl
      (hfin _ _ (Nat.pos_of_ne_zero hn) (hpow hx'r)) (hfin _ _ hm' hyk)).mpr ⟨a, ?_⟩
    have hsw : ∀ z : L, (z ^ Fintype.card K ^ k) ^ l ^ a = (z ^ l ^ a) ^ Fintype.card K ^ k :=
      fun z => by rw [← pow_mul, ← pow_mul, mul_comm]
    rw [hsw, hsw, ha]
  · exact le_trans (Nat.cast_le.mpr (card_samePart_le hl hn _ S hSprop)) (lpow_le_rpow_quarter hBB)

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
end
