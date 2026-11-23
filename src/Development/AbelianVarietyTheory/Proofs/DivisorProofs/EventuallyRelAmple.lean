module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsAmpleTensorAmplePowProjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Tactic.Linter.Style
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Polynomial.AlgebraMap
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqMulOfQuadraticBoundNormalLocal

section

@[expose] public section

open IsLocalRing ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory


open IsDiscreteValuationRing in
theorem mul_dvd_pow_of_quadratic_bound_dvr {V : Type} [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] {X : Type} [AddCommGroup X] (h h' : X →+ X) (C : ℕ)
    (hq : ∀ q : X → ℤ, (∀ y, 0 ≤ q y) → q 0 = 0 → (∀ y, q (-y) = q y) →
      (∀ x y z, q (x + y + z) + q x + q y + q z = q (x + y) + q (x + z) + q (y + z)) →
      (∀ y z, q (h y + z) + q y + q (h' z) = q (y + h' z) + q (h y) + q z) →
      ∀ y, q (h y) ≤ C * q y) {N : ℕ} (hN : C + 1 ≤ N) (k : X → V) (hk0 : ∀ y, k y ≠ 0)
    (h1 : ∀ y, k (-y) = k y) (h2 : k 0 = 1)
    (h3 : ∀ x y z, k (x + y + z) * k x * k y * k z = k (x + y) * k (x + z) * k (y + z))
    (h4 : ∀ y z, ∃ u : V, IsUnit u ∧
      k (h y + z) * k y * k (h' z) = u * (k (y + h' z) * k (h y) * k z)) (y : X) :
    k y * k (h y) ∣ k y ^ N := by
  have hn : ∀ z, ∃ n : ℕ, addVal V (k z) = n := fun z =>
    (ENat.ne_top_iff_exists.1 (mt addVal_eq_top_iff.1 (hk0 z))).imp fun _ e => e.symm
  choose n hn using hn
  have key := hq (fun z => (n z : ℤ)) (fun _ => Int.natCast_nonneg _)
    (by
      have := hn 0
      rw [h2, addVal_one] at this
      exact_mod_cast this.symm)
    (fun z => by
      have := hn (-z)
      rw [h1, hn] at this
      exact_mod_cast this.symm)
    (fun a b c => by
      have := congrArg (addVal V) (h3 a b c)
      simp only [addVal_mul, hn] at this
      exact_mod_cast this)
    (fun a b => by
      obtain ⟨u, hu, e⟩ := h4 a b
      have := congrArg (addVal V) e
      simp only [addVal_mul, hn, addVal_eq_zero_iff.2 hu, zero_add] at this
      exact_mod_cast this) y
  have key' : n (h y) ≤ C * n y := by exact_mod_cast key
  rw [← addVal_le_iff_dvd, addVal_mul, addVal_pow, hn, hn, nsmul_eq_mul]
  have : n y + n (h y) ≤ N * n y := by nlinarith [Nat.mul_le_mul_right (n y) hN]
  exact_mod_cast this

theorem exists_pow_eq_mul_of_quadratic_bound :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (X : Type) [AddCommGroup X] (h h' : X →+ X) (C : ℕ), (∀ q : X → ℤ, (∀ y, 0 ≤ q y) → q 0 = 0 → (∀ y, q (-y) = q y) → (∀ x y z, q (x + y + z) + q x + q y + q z = q (x + y) + q (x + z) + q (y + z)) → (∀ y z, q (h y + z) + q y + q (h' z) = q (y + h' z) + q (h y) + q z) → ∀ y, q (h y) ≤ C * q y) → ∀ N : ℕ, C + 1 ≤ N → ∀ (κ : X → (FractionRing R)ˣ), (∀ y, κ (-y) = κ y) → κ 0 = 1 → (∀ x y z, κ (x + y + z) * κ x * κ y * κ z = κ (x + y) * κ (x + z) * κ (y + z)) → (∀ y, ∃ r : R, (κ y : FractionRing R) = algebraMap R _ r) → (∀ y z, ∃ u : Rˣ, ((κ (h y + z) * κ y * κ (h' z) : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ (u : R) * ((κ (y + h' z) * κ (h y) * κ z : (FractionRing R)ˣ) : FractionRing R)) → ∀ y, ∃ r : R, ((κ y ^ N : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ r * κ y * κ (h y) := by
  intro R _ _ _ hR X _ h h' C hq N hN κ h1 h2 h3 hκ h4 y
  obtain ⟨hno, -, hic, -⟩ := hR
  have hx : ∃ r : R, algebraMap R (FractionRing R) r =
      ((κ y ^ N * (κ y * κ (h y))⁻¹ : (FractionRing R)ˣ) : FractionRing R) := by
    refine exists_algebraMap_eq_of_forall_discreteValuationSubring fun V hV hRV _ => ?_
    have hm : ∀ z, (κ z : FractionRing R) ∈ V := fun z => by
      obtain ⟨r, e⟩ := hκ z
      exact e ▸ hRV r
    obtain ⟨c, hc⟩ := mul_dvd_pow_of_quadratic_bound_dvr (V := V) h h' C hq hN
      (fun z => ⟨κ z, hm z⟩) (fun z e => (κ z).ne_zero (congrArg Subtype.val e))
      (fun z => Subtype.ext (congrArg Units.val (h1 z)))
      (Subtype.ext (congrArg Units.val h2))
      (fun a b c => Subtype.ext (congrArg Units.val (h3 a b c)))
      (fun a b => by
        obtain ⟨u, e⟩ := h4 a b
        exact ⟨(algebraMap R (FractionRing R)).codRestrict V hRV u, u.isUnit.map _,
          Subtype.ext e⟩) y
    have hc' : (κ y : FractionRing R) ^ N = κ y * κ (h y) * (c : FractionRing R) := by
      simpa using congrArg Subtype.val hc
    have : ((κ y ^ N * (κ y * κ (h y))⁻¹ : (FractionRing R)ˣ) : FractionRing R) = c := by
      rw [Units.val_mul, Units.mul_inv_eq_iff_eq_mul, Units.val_pow_eq_pow_val, hc', Units.val_mul, mul_comm]
    exact this ▸ c.2
  obtain ⟨r, hr⟩ := hx
  refine ⟨r, ?_⟩
  rw [hr, mul_assoc, ← Units.val_mul, ← Units.val_mul, inv_mul_cancel_right]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqMulOfQuadraticBoundNormalLocalStatement

section

@[expose] public section

open IsLocalRing ReciprocityTheory.ChartRestriction.G.Out

theorem _root_.GlobalTheory.T.exists_pow_eq_mul_of_quadraticBound_normalLocal : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (X : Type) [AddCommGroup X] (h h' : X →+ X) (C : ℕ), (∀ q : X → ℤ, (∀ y, 0 ≤ q y) → q 0 = 0 → (∀ y, q (-y) = q y) → (∀ x y z, q (x + y + z) + q x + q y + q z = q (x + y) + q (x + z) + q (y + z)) → (∀ y z, q (h y + z) + q y + q (h' z) = q (y + h' z) + q (h y) + q z) → ∀ y, q (h y) ≤ C * q y) → ∀ N : ℕ, C + 1 ≤ N → ∀ (κ : X → (FractionRing R)ˣ), (∀ y, κ (-y) = κ y) → κ 0 = 1 → (∀ x y z, κ (x + y + z) * κ x * κ y * κ z = κ (x + y) * κ (x + z) * κ (y + z)) → (∀ y, ∃ r : R, (κ y : FractionRing R) = algebraMap R _ r) → (∀ y z, ∃ u : Rˣ, ((κ (h y + z) * κ y * κ (h' z) : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ (u : R) * ((κ (y + h' z) * κ (h y) * κ z : (FractionRing R)ˣ) : FractionRing R)) → ∀ y, ∃ r : R, ((κ y ^ N : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ r * κ y * κ (h y) := by
  first | exact @GlobalTheory.exists_pow_eq_mul_of_quadratic_bound | exact GlobalTheory.exists_pow_eq_mul_of_quadratic_bound | (intros; apply GlobalTheory.exists_pow_eq_mul_of_quadratic_bound <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosSemidefQuadraticAdjointPairBound

section

@[expose] public section

namespace GlobalTheory.PosFormAdjoint

theorem int_cauchy_schwarz {X : Type} [AddCommGroup X] (F : X →+ X →+ ℤ)
    (hsym : ∀ u v, F u v = F v u) (hpos : ∀ u, 0 ≤ F u u) (u v : X) :
    F u v ^ 2 ≤ F u u * F v v := by
  have key : ∀ a b : ℤ, 0 ≤ a ^ 2 * F u u + 2 * a * b * F u v + b ^ 2 * F v v := by
    intro a b
    have h1 := hpos (a • u + b • v)
    have e : F (a • u + b • v) (a • u + b • v)
        = a ^ 2 * F u u + 2 * a * b * F u v + b ^ 2 * F v v := by
      simp only [map_add (f := _), map_zsmul, AddMonoidHom.add_apply, AddMonoidHom.smul_apply, smul_eq_mul]
      rw [hsym v u]
      ring
    rw [e] at h1
    exact h1
  rcases (hpos u).lt_or_eq with ht | ht
  · have h2 := key (-(F u v)) (F u u)
    have h3 : 0 ≤ F u u * (F u u * F v v - F u v ^ 2) := by nlinarith [h2]
    have h4 : 0 ≤ F u u * F v v - F u v ^ 2 := by
      by_contra hc
      push_neg at hc
      nlinarith [mul_neg_of_pos_of_neg ht hc]
    linarith
  · rw [← ht]
    simp only [zero_mul]
    by_contra hc
    push_neg at hc
    have hs : (1 : ℤ) ≤ F u v ^ 2 := hc
    have h2 := key (-(F v v + 1) * F u v) 1
    rw [← ht] at h2
    have hv := hpos v
    nlinarith [h2, hs, hv]

theorem seq_bound (a c : ℕ → ℤ) (n : ℕ) (hpos : ∀ k, 0 ≤ a k)
    (hlc : ∀ k, a (k + 1) ^ 2 ≤ a k * a (k + 2))
    (hrec : a n + ∑ i ∈ Finset.range n, c i * a i = 0) :
    a 1 ≤ (((∑ i ∈ Finset.range n, (c i).natAbs : ℕ) + 1 : ℕ) : ℤ) * a 0 := by
  set S : ℤ := ∑ i ∈ Finset.range n, |c i| with hS
  have hcast : (((∑ i ∈ Finset.range n, (c i).natAbs : ℕ) + 1 : ℕ) : ℤ) = S + 1 := by
    push_cast
    simp [hS, Int.natCast_natAbs]
  rw [hcast]
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  by_contra H
  push_neg at H
  have ha0 : 0 < a 0 := by
    rcases (hpos 0).lt_or_eq with h | h
    · exact h
    · exfalso
      have h1 := hlc 0
      rw [← h] at h1 H
      simp at h1 H
      nlinarith [sq_nonneg (a 1)]
  have h01 : a 0 < a 1 := by nlinarith
  have hind : ∀ k, 0 < a k ∧ a 1 * a k ≤ a (k + 1) * a 0 := by
    intro k
    induction k with
    | zero => exact ⟨ha0, by simp [mul_comm]⟩
    | succ k ih =>
      obtain ⟨hk, hk'⟩ := ih
      have hk1 : 0 < a (k + 1) := by
        by_contra hc
        push_neg at hc
        nlinarith [mul_pos (by linarith : (0:ℤ) < a 1) hk]
      refine ⟨hk1, ?_⟩
      have h2 := hlc k
      have h3 : a k * (a 1 * a (k + 1)) ≤ a k * (a (k + 2) * a 0) := by
        nlinarith [mul_le_mul_of_nonneg_left hk' hk1.le]
      exact le_of_mul_le_mul_left h3 hk
  have hmono : ∀ k, a k ≤ a (k + 1) := by
    intro k
    obtain ⟨hk, hk'⟩ := hind k
    have : a 0 * a k ≤ a 0 * a (k + 1) := by nlinarith [mul_le_mul_of_nonneg_right h01.le hk.le]
    exact le_of_mul_le_mul_left this ha0
  have hmono' : Monotone a := monotone_nat_of_le_succ hmono
  rcases n with _ | m
  · simp at hrec
    linarith
  · rw [Finset.sum_range_succ] at hrec
    obtain ⟨hm, hm'⟩ := hind m
    have hle : -(∑ i ∈ Finset.range (m + 1), c i * a i) ≤ S * a m := by
      rw [hS, Finset.sum_mul, ← Finset.sum_neg_distrib]
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have h1 : -(c i * a i) ≤ |c i| * a i := by
        have := neg_abs_le (c i)
        nlinarith [hpos i]
      have h2 : |c i| * a i ≤ |c i| * a m :=
        mul_le_mul_of_nonneg_left (hmono' hi') (abs_nonneg _)
      linarith
    have hrec' : a (m + 1) = -(∑ i ∈ Finset.range (m + 1), c i * a i) := by
      rw [Finset.sum_range_succ]; linarith
    have h5 : (S + 1) * a 0 * a m < a 1 * a m := by nlinarith
    have h6 : (S + 1) * a m * a 0 < a (m + 1) * a 0 := by nlinarith
    have h7 : (S + 1) * a m < a (m + 1) := lt_of_mul_lt_mul_right h6 ha0.le
    nlinarith

end GlobalTheory.PosFormAdjoint

namespace GlobalTheory.PosFormAdjoint

theorem pos_form_adjoint_bound : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (h h' : X →+ X), ∃ C : ℕ, ∀ q : X → ℤ, (∀ y, 0 ≤ q y) → q 0 = 0 → (∀ y, q (-y) = q y) →
      (∀ x y z, q (x + y + z) + q x + q y + q z = q (x + y) + q (x + z) + q (y + z)) →
      (∀ y z, q (h y + z) + q y + q (h' z) = q (y + h' z) + q (h y) + q z) →
      ∀ y, q (h y) ≤ C * q y := by
  intro X _ _ _ h h'
  let T : Module.End ℤ X := h'.toIntLinearMap * h.toIntLinearMap
  have hT : ∀ u, T u = h' (h u) := fun u => rfl
  let p := T.charpoly
  refine ⟨(∑ i ∈ Finset.range p.natDegree, (-(p.coeff i)).natAbs) + 1, ?_⟩
  intro q hq hq0 hqneg hcube hadj y
  let B : X →+ X →+ ℤ := AddMonoidHom.mk' (fun u => AddMonoidHom.mk' (fun v => q (u + v) - q u - q v)
      (fun a b => by
        have := hcube u a b
        rw [← add_assoc]
        linarith))
    (fun a b => by
      ext v
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
      have := hcube a b v
      linarith)
  have hB : ∀ u v, B u v = q (u + v) - q u - q v := fun u v => rfl
  have Bsym : ∀ u v, B u v = B v u := by
    intro u v; rw [hB, hB, add_comm]; ring
  have Bdiag : ∀ u, B u u = 2 * q u := by
    intro u
    have := hcube u u (-u)
    simp only [add_neg_cancel_right, add_neg_cancel, hq0, hqneg] at this
    rw [hB]; linarith
  have Badj : ∀ u v, B (h u) v = B u (h' v) := by
    intro u v; rw [hB, hB]; have := hadj u v; linarith
  have BT : ∀ u v, B (T u) v = B u (T v) := by
    intro u v
    rw [hT, hT, Bsym, ← Badj, Bsym, Badj]
  have BTpow : ∀ k u v, B ((T ^ k) u) v = B u ((T ^ k) v) := by
    intro k
    induction k with
    | zero => intro u v; rfl
    | succ k ih =>
      intro u v
      rw [pow_succ', Module.End.mul_apply, BT, ih]
      congr 1
      rw [← Module.End.mul_apply, ← pow_succ, ← pow_succ']
  let G : X →+ X →+ ℤ := B.comp (T : X →+ X)
  have hG : ∀ u v, G u v = B (T u) v := fun u v => rfl
  have Gsym : ∀ u v, G u v = G v u := by
    intro u v; rw [hG, hG, BT, Bsym]
  have Gdiag : ∀ u, G u u = 2 * q (h u) := by
    intro u; rw [hG, hT, Bsym, ← Badj, Bdiag]
  have Bpos : ∀ u, 0 ≤ B u u := fun u => by rw [Bdiag]; linarith [hq u]
  have Gpos : ∀ u, 0 ≤ G u u := fun u => by rw [Gdiag]; linarith [hq (h u)]
  let a : ℕ → ℤ := fun k => B ((T ^ k) y) y
  have aB : ∀ i j, a (i + j) = B ((T ^ i) y) ((T ^ j) y) := by
    intro i j
    show B ((T ^ (i + j)) y) y = _
    rw [pow_add, Module.End.mul_apply, BTpow]
    exact Bsym _ _
  have aG : ∀ i j, a (i + j + 1) = G ((T ^ i) y) ((T ^ j) y) := by
    intro i j
    rw [hG, ← Module.End.mul_apply, ← pow_succ', add_right_comm, aB]
  have apos : ∀ k, 0 ≤ a k := by
    intro k
    rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
    · rw [two_mul, aB]; exact Bpos _
    · rw [two_mul, aG]; exact Gpos _
  have alc : ∀ k, a (k + 1) ^ 2 ≤ a k * a (k + 2) := by
    intro k
    rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
    · have e1 : a (2 * m + 1) = B ((T ^ m) y) ((T ^ (m + 1)) y) := by
        rw [← aB]; congr 1; ring
      have e2 : a (2 * m + 2) = B ((T ^ (m + 1)) y) ((T ^ (m + 1)) y) := by
        rw [← aB]; congr 1; ring
      rw [e1, e2, two_mul, aB]
      exact int_cauchy_schwarz B Bsym Bpos _ _
    · have e1 : a (2 * m + 1 + 1) = G ((T ^ m) y) ((T ^ (m + 1)) y) := by
        rw [← aG]; congr 1; ring
      have e2 : a (2 * m + 1 + 2) = G ((T ^ (m + 1)) y) ((T ^ (m + 1)) y) := by
        rw [← aG]; congr 1; ring
      rw [e1, e2, two_mul, aG]
      exact int_cauchy_schwarz G Gsym Gpos _ _
  have hmonic : p.Monic := LinearMap.charpoly_monic T
  have hrec : a p.natDegree + ∑ i ∈ Finset.range p.natDegree, p.coeff i * a i = 0 := by
    have hCH : (Polynomial.aeval T p) y = 0 := by
      rw [LinearMap.aeval_self_charpoly]; rfl
    rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, hmonic.coeff_natDegree, one_smul] at hCH
    have h2 := congrArg (fun x => B x y) hCH

    simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_add (f := _),
    map_sum, map_zsmul, AddMonoidHom.add_apply, AddMonoidHom.finsetSum_apply,
    AddMonoidHom.smul_apply, smul_eq_mul, map_zero, AddMonoidHom.zero_apply] at h2
    rw [add_comm]; exact h2
  have hb := seq_bound a (fun i => p.coeff i) p.natDegree apos alc hrec
  have a0 : a 0 = 2 * q y := by show B ((T ^ 0) y) y = _; rw [pow_zero]; exact Bdiag y
  have a1 : a 1 = 2 * q (h y) := by
    have := aG 0 0
    simp only [zero_add, pow_zero] at this
    rw [this]; exact Gdiag y
  rw [a0, a1] at hb
  have habs : ∀ i, (-(p.coeff i)).natAbs = (p.coeff i).natAbs := fun i => Int.natAbs_neg _
  simp only [habs]
  linarith

end GlobalTheory.PosFormAdjoint
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosSemidefQuadraticAdjointPairBoundStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.posSemidef_quadratic_adjoint_pair_bound : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (h h' : X →+ X), ∃ C : ℕ, ∀ q : X → ℤ, (∀ y, 0 ≤ q y) → q 0 = 0 → (∀ y, q (-y) = q y) → (∀ x y z, q (x + y + z) + q x + q y + q z = q (x + y) + q (x + z) + q (y + z)) → (∀ y z, q (h y + z) + q y + q (h' z) = q (y + h' z) + q (h y) + q z) → ∀ y, q (h y) ≤ C * q y := by
  first | exact @GlobalTheory.PosFormAdjoint.pos_form_adjoint_bound | exact GlobalTheory.PosFormAdjoint.pos_form_adjoint_bound | (intros; apply GlobalTheory.PosFormAdjoint.pos_form_adjoint_bound <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyRelAmple

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory.Mum.PosMult

theorem eventually_relAmple : ∀ (R : Type) [CommRing R] (P : PolAV (Sp R)) (a : P.A ⟶ P.A), ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → RelAmple P.A (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, a.left] ![(N : ℤ), -1]) := by
  intro R _ P a
  have := P.isAb.proper
  have hL := P.isLB
  have hA : IsAmpleLB P.L := isAmpleLB_of_relAmple_of_isAffine P.A hL P.ample
  have hNb : (LB.LinComb P.L (K := Fin 1) ![a.left] ![-1]).IsLB := LB.isLB_linComb hL _ _
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 (hA.eventually_isAmpleLB_tens_lbPow_succ hNb)
  refine ⟨n₀ + 1, fun N hN => ?_⟩
  have key := hn₀ (N - 1) (by omega)
  have hN1 : N - 1 + 1 = N := by omega
  rw [hN1] at key
  have hM := LB.isLB_linComb hL (K := Fin 2) ![𝟙 P.A.left, a.left] ![(N : ℤ), -1]
  rw [relAmple_iff_isAmpleLB_of_isAffine P.A hM]
  refine key.of_lbIso hM ((cls_eq_iff hM (isLB_tens hNb (isLB_lbPow hL N))).1 ?_)
  rw [cls_tens hNb (isLB_lbPow hL N), cls_lbPow hL, cls_linComb hL, cls_linComb hL]
  simp [Fin.sum_univ_two, pull_id]
  abel

theorem exists_pos_mult : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∃ N : ℕ, 1 ≤ N ∧ RelAmple D.toPre.P.A (LB.LinComb D.toPre.P.L (K := Fin 2) ![𝟙 D.toPre.P.A.left, a.left] ![(N : ℤ), -1]) ∧ ∀ (κ : D.toPre.X → (FractionRing R)ˣ), (∀ y, κ (-y) = κ y) → κ 0 = 1 → (∀ x y z, κ (x + y + z) * κ x * κ y * κ z = κ (x + y) * κ (x + z) * κ (y + z)) → (∀ y, ∃ r : R, (κ y : FractionRing R) = algebraMap R _ r) → (∀ y z, ∃ u : Rˣ, ((κ (h y + z) * κ y * κ (h' z) : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ (u : R) * ((κ (y + h' z) * κ (h y) * κ z : (FractionRing R)ˣ) : FractionRing R)) → ∀ y, ∃ r : R, ((κ y ^ N : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ r * κ y * κ (h y) := by
  intro R _ _ _ hR D a a' h h' _
  obtain ⟨N₀, hN₀⟩ := eventually_relAmple R D.toPre.P a
  obtain ⟨C, hC⟩ := GlobalTheory.T.posSemidef_quadratic_adjoint_pair_bound D.toPre.X h h'
  refine ⟨max N₀ (C + 1), le_trans (by omega) (le_max_right _ _), hN₀ _ (le_max_left _ _), ?_⟩
  exact GlobalTheory.T.exists_pow_eq_mul_of_quadraticBound_normalLocal R hR D.toPre.X h h' C hC _ (le_max_right _ _)

end GlobalTheory.Mum.PosMult
end
end
