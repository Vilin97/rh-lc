module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Algebra.CharP.Defs
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Ring.NonZeroDivisors
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowDvdOfVanishingAtPerfectValuationPoints

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusPowEquationDvdAllPow

section

@[expose] public section

open scoped NNReal

namespace GlobalTheory

theorem phiEq_iterate (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] [ExpChar R l] (u : R)
    (κ : Type) [Fintype κ] (D : κ → R) (c : κ → κ → R) (h : ℕ)
    (hD : ∀ j, u ^ h * D j = ∑ i, D i ^ l * c i j) (k : ℕ) :
    ∃ a : ℕ, a + h ≤ h * l ^ k ∧ ∃ e : κ → κ → R,
      ∀ j, u ^ a * D j = ∑ i, D i ^ (l ^ k) * e i j := by
  classical
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  induction k with
  | zero =>
    refine ⟨0, by simp, fun i j => if i = j then 1 else 0, fun j => ?_⟩
    simp
  | succ k ih =>
    obtain ⟨a, ha, e, he⟩ := ih
    refine ⟨h + l * a, ?_, fun i' j => ∑ i, e i' i ^ l * c i j, fun j => ?_⟩
    · have h1 : l * (a + h) ≤ l * (h * l ^ k) := Nat.mul_le_mul_left _ ha
      have h2 : 2 * h ≤ l * h := Nat.mul_le_mul_right _ hl2
      calc h + l * a + h = 2 * h + l * a := by ring
        _ ≤ l * h + l * a := by omega
        _ = l * (a + h) := by ring
        _ ≤ l * (h * l ^ k) := h1
        _ = h * l ^ (k + 1) := by ring
    · calc u ^ (h + l * a) * D j = ∑ i, (u ^ a * D i) ^ l * c i j := by
            rw [pow_add, mul_comm (u ^ h) (u ^ (l * a)), mul_assoc, hD j, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [mul_pow, ← pow_mul, mul_comm a l]; ring
        _ = ∑ i, (∑ i', D i' ^ (l ^ k) * e i' i) ^ l * c i j := by
            simp only [he]
        _ = ∑ i, ∑ i', D i' ^ (l ^ (k + 1)) * (e i' i ^ l * c i j) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [sum_pow_char, Finset.sum_mul]
            refine Finset.sum_congr rfl fun i' _ => ?_
            rw [mul_pow, ← pow_mul, pow_succ]; ring
        _ = ∑ i', D i' ^ (l ^ (k + 1)) * ∑ i, e i' i ^ l * c i j := by
            rw [Finset.sum_comm]
            simp only [Finset.mul_sum]

theorem phiEq_dvd_all_pow : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (u : R),
    ((l : ℕ) : R) = 0 → u ∈ nonZeroDivisors R → ∀ (κ : Type) [Fintype κ] (D : κ → R)
    (c : κ → κ → R) (h : ℕ), (∀ j, u ^ h * D j = ∑ i, D i ^ l * c i j) →
    (∀ j (M : ℕ), ∃ c : ℕ, ∀ n : ℕ, u ^ (M * n) ∣ u ^ c * D j ^ n) → ∀ (m : ℕ) j, u ^ m ∣ D j := by
  intro l _ R _ u hl hu κ _ D c h hD hnil m j
  classical
  have hlp : l.Prime := Fact.out
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨0, Subsingleton.elim _ _⟩
  have hchar : ringChar R = l := by
    rcases (Nat.dvd_prime hlp).1 (ringChar.dvd hl) with h1 | h1
    · exact absurd h1 CharP.ringChar_ne_one
    · exact h1
  haveI : CharP R l := hchar ▸ ringChar.charP R
  haveI : ExpChar R l := ExpChar.prime hlp
  choose C hC using fun i => hnil i (h + 1)
  set Cm := ∑ i, C i with hCm
  obtain ⟨k, hk⟩ : ∃ k, m + Cm < l ^ k := ⟨m + Cm, Nat.lt_pow_self hlp.one_lt⟩
  obtain ⟨a, ha, e, he⟩ := phiEq_iterate l R u κ D c h hD k
  have hdiv : u ^ ((h + 1) * l ^ k) ∣ u ^ (Cm + a) * D j := by
    rw [pow_add, mul_assoc, he j, Finset.mul_sum]
    refine Finset.dvd_sum fun i _ => ?_
    rw [← mul_assoc]
    refine Dvd.dvd.mul_right ?_ _
    have hCi : C i ≤ Cm := Finset.single_le_sum (fun i _ => Nat.zero_le (C i)) (Finset.mem_univ i)
    refine (hC i (l ^ k)).trans ?_
    have hsp : u ^ Cm = u ^ C i * u ^ (Cm - C i) := by rw [← pow_add, Nat.add_sub_cancel' hCi]
    rw [hsp]
    exact ⟨u ^ (Cm - C i), by ring⟩
  have hle : Cm + a + m ≤ (h + 1) * l ^ k := by
    have : h * l ^ k + l ^ k = (h + 1) * l ^ k := by ring
    omega
  obtain ⟨y, hy⟩ := hdiv
  have hsplit : (h + 1) * l ^ k = (Cm + a) + ((h + 1) * l ^ k - (Cm + a)) := by omega
  rw [hsplit, pow_add u (Cm + a), mul_assoc] at hy
  have hreg : u ^ (Cm + a) ∈ nonZeroDivisors R := pow_mem hu _
  have hDj := (mul_cancel_left_mem_nonZeroDivisors hreg).1 hy
  rw [hDj]
  refine Dvd.dvd.mul_right (pow_dvd_pow u ?_) _
  omega

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusPowEquationDvdAllPowStatement

section

@[expose] public section

open scoped NNReal

theorem _root_.GlobalTheory.T.frobeniusPowEquation_dvd_all_pow : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (u : R), ((l : ℕ) : R) = 0 → u ∈ nonZeroDivisors R → ∀ (κ : Type) [Fintype κ] (D : κ → R) (c : κ → κ → R) (h : ℕ), (∀ j, u ^ h * D j = ∑ i, D i ^ l * c i j) → (∀ j (M : ℕ), ∃ c : ℕ, ∀ n : ℕ, u ^ (M * n) ∣ u ^ c * D j ^ n) → ∀ (m : ℕ) j, u ^ m ∣ D j := by
  first | exact @GlobalTheory.phiEq_dvd_all_pow | exact GlobalTheory.phiEq_dvd_all_pow | (intros; apply GlobalTheory.phiEq_dvd_all_pow <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowDvdOfVanishingAtPerfectValuationPointsStatement

section

@[expose] public section

open scoped NNReal

theorem _root_.GlobalTheory.T.pow_dvd_of_vanishing_at_perfect_valuation_points : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (u x : R), ((l : ℕ) : R) = 0 → u ∈ nonZeroDivisors R → (∀ r, IsUnit (1 - u * r)) → (∀ (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (f : R →+* O), f u ≠ 0 → ¬ IsUnit (f u) → IsAdicComplete (Ideal.span {f u}) O → f x = 0) → ∀ M : ℕ, ∃ c : ℕ, ∀ n : ℕ, u ^ (M * n) ∣ u ^ c * x ^ n := by
  first | exact @GlobalTheory.s_points_kpt | exact GlobalTheory.s_points_kpt | (intros; apply GlobalTheory.s_points_kpt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdAllPowOfFrobeniusEqKilledByPerfectPoints

section

@[expose] public section

open scoped NNReal

namespace GlobalTheory.PointsKey

def oneSubMul {R : Type} [CommRing R] (u : R) : Submonoid R where
  carrier := {x | ∃ r, x = 1 - u * r}
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b - u * a * b, by ring⟩
  one_mem' := ⟨0, by simp⟩

theorem dvd_of_one_sub_mul {R : Type} [CommRing R] (u r D a : R) (m : ℕ)
    (h : (1 - u * r) * D = u ^ m * a) : u ^ m ∣ D := by
  have hg : (1 - u * r) * (∑ i ∈ Finset.range m, (u * r) ^ i) = 1 - (u * r) ^ m := by
    rw [mul_comm, geom_sum_mul_neg]
  refine ⟨a * ∑ i ∈ Finset.range m, (u * r) ^ i + r ^ m * D, ?_⟩
  calc D = (1 - (u * r) ^ m) * D + (u * r) ^ m * D := by ring
    _ = (∑ i ∈ Finset.range m, (u * r) ^ i) * ((1 - u * r) * D) + (u * r) ^ m * D := by
        rw [← hg]; ring
    _ = _ := by rw [h]; ring

theorem key : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (u : R), ((l : ℕ) : R) = 0 → u ∈ nonZeroDivisors R → ∀ (κ : Type) [Fintype κ] (D : κ → R) (c : κ → κ → R) (h : ℕ), (∀ j, u ^ h * D j = ∑ i, D i ^ l * c i j) → (∀ (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (f : R →+* O), f u ≠ 0 → ¬ IsUnit (f u) → IsAdicComplete (Ideal.span {f u}) O → ∀ j, f (D j) = 0) → ∀ (m : ℕ) j, u ^ m ∣ D j := by
  intro l _ R _ u hl hu κ _ D c h heq hpts m j
  set S := oneSubMul u with hS
  let R' := Localization S
  let φ : R →+* R' := algebraMap R R'
  have hl' : ((l : ℕ) : R') = 0 := by rw [← map_natCast φ, hl, map_zero]
  have hu' : φ u ∈ nonZeroDivisors R' := by
    rw [mem_nonZeroDivisors_iff_right]
    intro x hx
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective S x
    have hx' : φ u * IsLocalization.mk' R' a s = 0 := by rw [mul_comm]; exact hx
    rw [IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_zero_iff] at hx'
    obtain ⟨t, ht⟩ := hx'
    have hta : (t : R) * a = 0 := by
      rw [mem_nonZeroDivisors_iff_right] at hu
      exact hu _ (by rw [← ht]; ring)
    exact (IsLocalization.mk'_eq_zero_iff a s).2 ⟨t, hta⟩
  have hunit : ∀ r', IsUnit (1 - φ u * r') := by
    intro r'
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective S r'
    obtain ⟨b, hb⟩ := s.2
    have hmem : (s : R) - u * a ∈ S := ⟨b + a, by rw [hb]; ring⟩
    have hsp := IsLocalization.mk'_spec R' a s
    have : (1 - φ u * IsLocalization.mk' R' a s) * φ s = φ ((s : R) - u * a) := by
      rw [map_sub, map_mul, sub_mul, one_mul, mul_assoc, hsp]
    exact isUnit_of_mul_isUnit_left (this ▸ IsLocalization.map_units R' ⟨_, hmem⟩)
  have heq' : ∀ j, φ u ^ h * φ (D j) = ∑ i, φ (D i) ^ l * φ (c i j) := by
    intro j; simpa [map_sum, map_mul, map_pow] using congrArg φ (heq j)
  have hpts' : ∀ j, ∀ (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (f : R' →+* O), f (φ u) ≠ 0 → ¬ IsUnit (f (φ u)) → IsAdicComplete (Ideal.span {f (φ u)}) O → f (φ (D j)) = 0 := by
    intro j O _ _ _ _ _ f h1 h2 h3
    exact hpts O (f.comp φ) h1 h2 h3 j
  have hb : ∀ j (M : ℕ), ∃ c : ℕ, ∀ n : ℕ, φ u ^ (M * n) ∣ φ u ^ c * φ (D j) ^ n := fun j M =>
    GlobalTheory.T.pow_dvd_of_vanishing_at_perfect_valuation_points l R' (φ u) (φ (D j)) hl' hu' hunit (hpts' j) M
  obtain ⟨y, hy⟩ := GlobalTheory.T.frobeniusPowEquation_dvd_all_pow l R' (φ u) hl' hu' κ (fun i => φ (D i)) (fun i j => φ (c i j)) h heq' hb m j
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective S y
  have h2 : φ (D j * s) = φ (u ^ m * a) := by
    rw [map_mul, hy, map_mul, map_pow, mul_assoc, IsLocalization.mk'_spec]
  obtain ⟨t, ht⟩ := (IsLocalization.eq_iff_exists S R').1 h2
  obtain ⟨r, hr⟩ := (t * s).2
  refine dvd_of_one_sub_mul u r (D j) (t * a) m ?_
  rw [← hr]
  simp only [Submonoid.coe_mul]
  linear_combination ht

end GlobalTheory.PointsKey
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdAllPowOfFrobeniusEqKilledByPerfectPointsStatement

section

@[expose] public section

open scoped NNReal

theorem _root_.GlobalTheory.T.dvd_all_pow_of_frobenius_eq_killed_by_perfect_points : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (u : R), ((l : ℕ) : R) = 0 → u ∈ nonZeroDivisors R → ∀ (κ : Type) [Fintype κ] (D : κ → R) (c : κ → κ → R) (h : ℕ), (∀ j, u ^ h * D j = ∑ i, D i ^ l * c i j) → (∀ (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (f : R →+* O), f u ≠ 0 → ¬ IsUnit (f u) → IsAdicComplete (Ideal.span {f u}) O → ∀ j, f (D j) = 0) → ∀ (m : ℕ) j, u ^ m ∣ D j := by
  first | exact @GlobalTheory.PointsKey.key | exact GlobalTheory.PointsKey.key | (intros; apply GlobalTheory.PointsKey.key <;> assumption)
end
end
