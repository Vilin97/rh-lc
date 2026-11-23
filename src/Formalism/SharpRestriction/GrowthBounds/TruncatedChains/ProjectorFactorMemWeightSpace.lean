module

public import Formalism.SharpRestriction.GrowthBounds.RootWeights.NontrivialIsotypicWeightZeroKilled
public import Formalism.SharpRestriction.GrowthBounds.TruncatedChains.RestPair
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.MemWeightSpaceIffDiagonalEigen
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees
import Formalism.SharpRestriction.GrowthBounds.RootWeights.NontrivialIsotypicWeightZeroKilled
public import Formalism.SharpRestriction.GrowthBounds.TruncatedChains.PfTrunc
public import Formalism.SharpRestriction.GrowthBounds.TruncatedChains.ProjectorCoeffSuccIndex
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Formalism.SharpRestriction.GrowthBounds.TruncatedChains.CommPow

section

@[expose] public section

noncomputable section

open Finset

namespace Formalism.MainNotions.G.ExtremalProjector

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory

theorem comm_pow {R : Type*} [Ring R] {x y z : R} (h : x * y = y * x + z) (hz : z * y = y * z) (k : ℕ) :
    x * y ^ (k + 1) = y ^ (k + 1) * x + (k + 1) • (y ^ k * z) := by
  induction k with
  | zero => simp [h]
  | succ k ih =>
    calc x * y ^ (k + 1 + 1) = (x * y ^ (k + 1)) * y := by rw [pow_succ y (k + 1), mul_assoc]
      _ = (y ^ (k + 1) * x + (k + 1) • (y ^ k * z)) * y := by rw [ih]
      _ = y ^ (k + 1) * (x * y) + (k + 1) • (y ^ k * (z * y)) := by
          simp only [add_mul, smul_mul_assoc, mul_assoc]
      _ = y ^ (k + 1) * (y * x + z) + (k + 1) • (y ^ k * (y * z)) := by rw [h, hz]
      _ = y ^ (k + 1 + 1) * x + (k + 1 + 1) • (y ^ (k + 1) * z) := by
          rw [mul_add, ← mul_assoc, ← pow_succ, ← mul_assoc (y ^ k) y z, ← pow_succ,
            succ_nsmul (y ^ (k + 1) * z) (k + 1)]
          first
          | abel
          | rw [add_assoc, add_comm (y ^ (k + 1) * z)]

section

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def cA (K : Type*) [Field K] (s k : ℕ) : K :=
  (-1 : K) ^ k / ((Nat.choose (s + k) k : ℕ) : K) * (((k.factorial : K)⁻¹) * ((k.factorial : K)⁻¹))

theorem pf_eq (E : GLOps n K V) (a b : Fin n) (s T : ℕ) :
    pf E a b s T = ∑ k ∈ Finset.range (T + 1), cA K s k • ((E b a) ^ k * (E a b) ^ k) := by
  first
  | simp only [pf, cA]
  | unfold pf cA
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold divPowE
  first
  | rw [smul_mul_smul_comm, smul_smul]
  | simp only [smul_mul_smul_comm, smul_smul]
  | simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
  | simp [smul_smul, mul_assoc, mul_comm, mul_left_comm]

theorem cA_succ [CharZero K] (s k : ℕ) :
    ((k + 1 : ℕ) : K) * cA K s (k + 1) = - ((s : K) + 1)⁻¹ * cA K (s + 1) k := by
  have hk : ((k : K) + 1) ≠ 0 := Nat.cast_add_one_ne_zero k
  have hs : ((s : K) + 1) ≠ 0 := Nat.cast_add_one_ne_zero s
  have hf : ((k.factorial : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have h2 : ((Nat.choose (s + 1 + k) k : ℕ) : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne'

  have hc : ((Nat.choose (s + (k + 1)) (k + 1) : ℕ) : K)
      = ((Nat.choose (s + 1 + k) k : ℕ) : K) * ((s : K) + 1) / ((k : K) + 1) := by
    rw [eq_div_iff hk]
    have h := Nat.choose_succ_right_eq (s + k + 1) k
    have e3 : s + k + 1 - k = s + 1 := by omega
    rw [e3] at h
    have e1 : s + (k + 1) = s + k + 1 := by omega
    have e2 : s + 1 + k = s + k + 1 := by omega
    rw [e1, e2]
    exact_mod_cast h
  unfold cA
  rw [hc, Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem cross_ab [CharZero K] {E : GLOps n K V} (hE : IsGLRep E) {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (s T : ℕ) (hnil : (E a b) ^ T = 0) :
    E b c * pf E a b s T = pf E a b s T * E b c + ((s : K) + 1)⁻¹ • (E b a * pf E a b (s + 1) T * E a c) := by
  have hrel := hE.1
  have hYF : E b c * E b a = E b a * E b c := by
    have h := hrel b c b a
    rw [if_neg (Ne.symm hbc), if_neg hab, sub_zero, sub_eq_zero] at h
    exact h
  have hYX : E b c * E a b = E a b * E b c + -(E a c) := by
    have h := hrel b c a b
    rw [if_neg (Ne.symm hac), if_pos rfl, zero_sub] at h
    rw [← h]; abel
  have hZX : -(E a c) * E a b = E a b * -(E a c) := by
    have h := hrel a c a b
    rw [if_neg (Ne.symm hac), if_neg (Ne.symm hab), sub_zero, sub_eq_zero] at h
    rw [neg_mul, mul_neg, h]
  have hFc : ∀ k : ℕ, E b c * E b a ^ k = E b a ^ k * E b c := fun k =>
    (Commute.pow_right (hYF : Commute (E b c) (E b a)) k).eq
  have hpow : ∀ j : ℕ, E b c * E a b ^ (j + 1) =
      E a b ^ (j + 1) * E b c - ((j + 1 : ℕ) : K) • (E a b ^ j * E a c) := by
    intro j
    rw [comm_pow hYX hZX j, Nat.cast_smul_eq_nsmul, mul_neg, smul_neg, sub_eq_add_neg]
  have hT : ∀ j : ℕ, E b c * (E b a ^ (j + 1) * E a b ^ (j + 1)) =
      (E b a ^ (j + 1) * E a b ^ (j + 1)) * E b c -
        ((j + 1 : ℕ) : K) • (E b a ^ (j + 1) * E a b ^ j * E a c) := by
    intro j
    rw [← mul_assoc, hFc, mul_assoc (E b a ^ (j + 1)) (E b c), hpow j, mul_sub, mul_smul_comm]
    simp only [mul_assoc]
  rw [pf_eq, pf_eq]
  have hL : E b c * (∑ k ∈ Finset.range (T + 1), cA K s k • (E b a ^ k * E a b ^ k)) -
      (∑ k ∈ Finset.range (T + 1), cA K s k • (E b a ^ k * E a b ^ k)) * E b c =
        -∑ j ∈ Finset.range T, (cA K s (j + 1) * ((j + 1 : ℕ) : K)) •
          (E b a ^ (j + 1) * E a b ^ j * E a c) := by
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.sum_range_succ',
      ← Finset.sum_neg_distrib]
    have h0 : E b c * (cA K s 0 • (E b a ^ 0 * E a b ^ 0)) - cA K s 0 • (E b a ^ 0 * E a b ^ 0) * E b c = 0 := by
      simp only [pow_zero, mul_one, mul_smul_comm, smul_mul_assoc, one_mul, sub_self]
    rw [h0, add_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_smul_comm, smul_mul_assoc, hT j, smul_sub, sub_sub_cancel_left, smul_smul]
  have hR : ((s : K) + 1)⁻¹ • (E b a * (∑ k ∈ Finset.range (T + 1), cA K (s + 1) k • (E b a ^ k * E a b ^ k)) *
      E a c) = ∑ j ∈ Finset.range T, (((s : K) + 1)⁻¹ * cA K (s + 1) j) •
        (E b a ^ (j + 1) * E a b ^ j * E a c) := by
    rw [Finset.sum_range_succ, hnil, mul_zero, smul_zero, add_zero, Finset.mul_sum, Finset.sum_mul,
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_smul_comm, smul_mul_assoc, smul_smul, ← mul_assoc, ← pow_succ']
  rw [← sub_eq_iff_eq_add', hL, hR, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← neg_smul]
  congr 1
  rw [mul_comm (cA K s (j + 1)), cA_succ, neg_mul, neg_neg]

theorem cross_ac [CharZero K] {E : GLOps n K V} (hE : IsGLRep E) {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (u T : ℕ) (hnil : (E a c) ^ T = 0) :
    E b c * pf E a c u T = pf E a c u T * E b c - ((u : K) + 1)⁻¹ • (E b a * pf E a c (u + 1) T * E a c) := by
  have hrel := hE.1
  have hYX : E b c * E a c = E a c * E b c := by
    have h := hrel b c a c
    rw [if_neg (Ne.symm hac), if_neg (Ne.symm hbc), sub_zero, sub_eq_zero] at h
    exact h
  have hYF : E b c * E c a = E c a * E b c + E b a := by
    have h := hrel b c c a
    rw [if_pos rfl, if_neg hab, sub_zero] at h
    rw [← h]; abel
  have hEF : E b a * E c a = E c a * E b a := by
    have h := hrel b a c a
    rw [if_neg hac, if_neg hab, sub_zero, sub_eq_zero] at h
    exact h
  have hXc : ∀ k : ℕ, E b c * E a c ^ k = E a c ^ k * E b c := fun k =>
    (Commute.pow_right (hYX : Commute (E b c) (E a c)) k).eq
  have hEFk : ∀ k : ℕ, E b a * E c a ^ k = E c a ^ k * E b a := fun k =>
    (Commute.pow_right (hEF : Commute (E b a) (E c a)) k).eq
  have hEF' : ∀ (k : ℕ) (M : Module.End K V), E b a * (E c a ^ k * M) = E c a ^ k * (E b a * M) := by
    intro k M
    rw [← mul_assoc, hEFk k, mul_assoc]
  have hpow : ∀ j : ℕ, E b c * E c a ^ (j + 1) =
      E c a ^ (j + 1) * E b c + ((j + 1 : ℕ) : K) • (E c a ^ j * E b a) := by
    intro j
    rw [comm_pow hYF hEF j, Nat.cast_smul_eq_nsmul]
  have hT : ∀ j : ℕ, E b c * (E c a ^ (j + 1) * E a c ^ (j + 1)) =
      (E c a ^ (j + 1) * E a c ^ (j + 1)) * E b c +
        ((j + 1 : ℕ) : K) • (E c a ^ j * E b a * E a c ^ (j + 1)) := by
    intro j
    rw [← mul_assoc, hpow j, add_mul, smul_mul_assoc]
    simp only [mul_assoc, hXc]
  rw [pf_eq, pf_eq]
  have hL : E b c * (∑ k ∈ Finset.range (T + 1), cA K u k • (E c a ^ k * E a c ^ k)) -
      (∑ k ∈ Finset.range (T + 1), cA K u k • (E c a ^ k * E a c ^ k)) * E b c =
        ∑ j ∈ Finset.range T, (cA K u (j + 1) * ((j + 1 : ℕ) : K)) •
          (E c a ^ j * E b a * E a c ^ (j + 1)) := by
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.sum_range_succ']
    have h0 : E b c * (cA K u 0 • (E c a ^ 0 * E a c ^ 0)) - cA K u 0 • (E c a ^ 0 * E a c ^ 0) * E b c = 0 := by
      simp only [pow_zero, mul_one, mul_smul_comm, smul_mul_assoc, one_mul, sub_self]
    rw [h0, add_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_smul_comm, smul_mul_assoc, hT j, smul_add, add_sub_cancel_left, smul_smul]
  have hR : ((u : K) + 1)⁻¹ • (E b a * (∑ k ∈ Finset.range (T + 1), cA K (u + 1) k • (E c a ^ k * E a c ^ k)) *
      E a c) = ∑ j ∈ Finset.range T, (((u : K) + 1)⁻¹ * cA K (u + 1) j) •
        (E c a ^ j * E b a * E a c ^ (j + 1)) := by
    rw [Finset.sum_range_succ, hnil, mul_zero, smul_zero, add_zero, Finset.mul_sum, Finset.sum_mul,
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_smul_comm, smul_mul_assoc, smul_smul, ← mul_assoc, hEFk j, mul_assoc (E c a ^ j * E b a),
      ← pow_succ]
  rw [sub_eq_add_neg, ← sub_eq_iff_eq_add', hL, hR, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← neg_smul]
  congr 1
  rw [mul_comm (cA K u (j + 1)), cA_succ, neg_mul]

end

end Formalism.MainNotions.G.ExtremalProjector
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.TruncatedChains.ProjectorFactorMemWeightSpace

section

@[expose] public section

noncomputable section

open Finset

namespace Formalism.MainNotions.G.ExtremalProjector

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory

section

variable {n : ℕ} {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]

theorem raising_lowering_mul_comm_add {E : GLOps n K V} (hE : IsGLRep E) (a b : Fin n) :
    E a b * E b a = E b a * E a b + (E a a - E b b) := by
  have h := hE.1 a b b a
  simp only [if_true] at h
  exact eq_add_of_sub_eq' h

theorem cartan_raising_commute {E : GLOps n K V} (hE : IsGLRep E) {a b : Fin n} (hab : a ≠ b) :
    (E a a - E b b) * E a b = E a b * (E a a - E b b) + (2 : K) • E a b := by
  have h1 := hE.1 a a a b
  have h2 := hE.1 b b a b
  simp only [if_true, if_neg (Ne.symm hab), sub_zero, zero_sub] at h1 h2
  rw [sub_mul, mul_sub, two_smul, eq_add_of_sub_eq' h1, eq_add_of_sub_eq' h2]
  abel

theorem cartan_lowering_commute {E : GLOps n K V} (hE : IsGLRep E) {a b : Fin n} (hab : a ≠ b) :
    (E a a - E b b) * E b a = E b a * (E a a - E b b) - (2 : K) • E b a := by
  have h1 := hE.1 a a b a
  have h2 := hE.1 b b b a
  simp only [if_true, if_neg hab, if_neg (Ne.symm hab), sub_zero, zero_sub] at h1 h2
  rw [sub_mul, mul_sub, two_smul, eq_add_of_sub_eq' h1, eq_add_of_sub_eq' h2]
  abel

theorem cartan_difference_apply_weight (E : GLOps n K V) (a b : Fin n) (ν : Fin n → ℤ) (x : V) (hx : x ∈ weightSp E ν) :
    (E a a - E b b) x = ((ν a : K) - (ν b : K)) • x := by
  have hw : ∀ c, E c c x = (ν c : K) • x := fun c => by
    have h := (Submodule.mem_iInf _).1 hx c
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      sub_eq_zero] at h
    exact h
  rw [LinearMap.sub_apply, hw a, hw b, sub_smul]

theorem raising_projector_factor_commute {E : GLOps n K V} (hE : IsGLRep E) {a b : Fin n} (hab : a ≠ b) (ν : Fin n → ℤ) (s T : ℕ)
    (hnil : (E a b) ^ T = 0) (x : V) (hx : x ∈ weightSp E ν) :
    E a b (pf E a b s T x) =
      (((s : K) - ((ν a : K) - (ν b : K)) - 1) / ((s : K) + 1)) • pf E a b (s + 1) T (E a b x) := by
  rw [pf_eq_P, pf_eq_P]
  exact R1 (raising_lowering_mul_comm_add hE a b) (cartan_raising_commute hE hab) (cartan_lowering_commute hE hab) (cartan_difference_apply_weight E a b ν x hx) s T hnil

theorem projector_factor_lowering_commute {E : GLOps n K V} (hE : IsGLRep E) {a b : Fin n} (hab : a ≠ b) (ν : Fin n → ℤ) (s T : ℕ)
    (hnil : (E a b) ^ T = 0) (z : V) (hz : z ∈ weightSp E ν) :
    pf E a b s T (E b a z) =
      (((s : K) + 1 - ((ν a : K) - (ν b : K))) / ((s : K) + 1)) • E b a (pf E a b (s + 1) T z) := by
  rw [pf_eq_P, pf_eq_P]
  exact sl2_projector_apply_f_eq_smul_f_projector_succ (raising_lowering_mul_comm_add hE a b) (cartan_raising_commute hE hab) (cartan_difference_apply_weight E a b ν z hz) s T hnil

theorem projector_factor_mem_weight_space {E : GLOps n K V} (hs : OperatorsShiftWeightsByRoots E) (ν : Fin n → ℤ) (a b : Fin n) (c T : ℕ) (x : V)
    (hx : x ∈ weightSp E ν) : pf E a b c T x ∈ weightSp E ν := by
  have hpow : ∀ (a' b' : Fin n) (k : ℕ) (μ : Fin n → ℤ) (y : V), y ∈ weightSp E μ →
      ((E a' b') ^ k) y ∈ weightSp E (μ + k • rootW a' b') := by
    intro a' b' k
    induction k with
    | zero =>
      intro μ y hy
      simpa using hy
    | succ k ih =>
      intro μ y hy
      rw [pow_succ', Module.End.mul_apply, succ_nsmul, ← add_assoc]
      exact hs a' b' _ _ (ih μ y hy)
  rw [pf_eq, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [LinearMap.smul_apply]
  refine Submodule.smul_mem _ _ ?_
  rw [Module.End.mul_apply]
  have h1 := hpow b a k _ _ (hpow a b k ν x hx)
  have e : ν + k • rootW a b + k • rootW b a = ν := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, rootW, Pi.sub_apply, smul_eq_mul]
    ring
  rwa [e] at h1

end

theorem restKill : RestKill := by
  intro K V _ _ _ _ _ n E hE a b hab ν s hs T hT x hx
  have hnil := restNil K V n E hE a b hab T hT
  rw [raising_projector_factor_commute hE hab ν s T hnil x hx]
  have h0 : ((s : K) - ((ν a : K) - (ν b : K)) - 1) = 0 := by
    have h1 : ((s : ℤ) : K) = ((ν a - ν b + 1 : ℤ) : K) := by rw [hs]
    push_cast at h1
    rw [h1]
    ring
  rw [h0, zero_div, zero_smul]

theorem restPair : RestPair := by
  intro K V _ _ _ _ _ n E hE a b c hab hac hbc ν s u hsu T hT w hw
  have hsh := gl_rep_shifts_weights hE
  have n1 := restNil K V n E hE a b hab T hT
  have n3 := restNil K V n E hE a c hac T hT
  have c1 := fun y : V => congrArg (fun g : Module.End K V => g y) (cross_ab hE hab hac hbc s T n1)
  have c3 := fun y : V => congrArg (fun g : Module.End K V => g y) (cross_ac hE hab hac hbc u T n3)
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply] at c1 c3
  have hz : pf E a c (u + 1) T (E a c w) ∈ weightSp E (ν + rootW a c) :=
    projector_factor_mem_weight_space hsh _ a c _ T _ (hsh a c ν w hw)
  rw [c1, c3, raising_projector_factor_commute hE hac ν u T n3 w hw, map_sub, map_smul, map_smul, map_smul,
    projector_factor_lowering_commute hE hab _ s T n1 _ hz]
  generalize E b a (pf E a b (s + 1) T (pf E a c (u + 1) T (E a c w))) = Y
  rw [smul_smul, smul_smul, sub_add, sub_eq_self, ← sub_smul]
  have hs1 : (s : K) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero s
  have hu1 : (u : K) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero u
  have hK : (u : K) - ((ν a : K) - (ν c : K)) - 1 = (s : K) - ((ν a : K) - (ν b : K)) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : K)) hsu
  have ra : (ν + rootW a c) a = ν a + 1 := by simp [rootW, hac]
  have rb : (ν + rootW a c) b = ν b := by simp [rootW, hab.symm, hbc]
  rw [ra, rb, hK]
  convert zero_smul K Y using 2
  push_cast
  field_simp
  ring

end Formalism.MainNotions.G.ExtremalProjector
end
end
end
