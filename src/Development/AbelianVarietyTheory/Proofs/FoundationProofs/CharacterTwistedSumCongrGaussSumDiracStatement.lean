module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ChSumSubCMul
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormSubOnePowThreeLe
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.DirichletCharacter.GaussSum
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
public import Mathlib.Algebra.Field.GeomSum
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLocallyConstantCycMod

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumPrimCharMulRootPowModPow

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

theorem zpow_eq_zpow_of_intCast_eq {K : Type} [Field K] {ξ : K} {N : ℕ} (h0 : ξ ≠ 0)
    (h : ξ ^ N = 1) {k j : ℤ} (hkj : (k : ZMod N) = (j : ZMod N)) : ξ ^ k = ξ ^ j := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hkj
  obtain ⟨q, hq⟩ := hkj
  have hj : j = k + (N : ℤ) * q := by linarith
  rw [hj, zpow_add₀ h0, zpow_mul, zpow_natCast, h, one_zpow, mul_one]

theorem sum_zmod_val_eq_sum_range {K : Type} [Field K] (N : ℕ) [NeZero N] (G : ℕ → K) :
    ∑ r : ZMod N, G r.val = ∑ k ∈ Finset.range N, G k := by
  refine Finset.sum_nbij' (fun f => f.val) (fun v => (v : ZMod N)) ?_ ?_ ?_ ?_ ?_
  · intro f _; simpa using ZMod.val_lt f
  · intro v _; simp
  · intro f _; simp
  · intro v hv; exact ZMod.val_cast_of_lt (by simpa using hv)
  · intro f _; rfl

theorem sum_range_mul_split {K : Type} [Field K] (G : ℕ → K) (b c : ℕ) :
    ∑ k ∈ Finset.range (b * c), G k = ∑ t ∈ Finset.range c, ∑ a ∈ Finset.range b, G (a + b * t) := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [add_comm]

end GlobalTheory.EisM

namespace GlobalTheory.EisM

theorem sum_primChar_mul_rootPow_mod_pow : ∀ (K : Type) [Field K] [CharZero K] (l m n : ℕ) [NeZero (l ^ n)] [NeZero (l ^ m)] (ζ : K) (ψ : DirichletCharacter K (l ^ m)), l.Prime → 1 ≤ m → m ≤ n → IsPrimitiveRoot ζ (l ^ n) → ψ.IsPrimitive → ∀ X : ℤ, ∑ r : ZMod (l ^ n), ψ ((r.val : ℕ) : ZMod (l ^ m)) * ζ ^ ((r.val : ℤ) * X) = if (l : ℤ) ^ (n - m) ∣ X then (l : K) ^ (n - m) * (∑ a : ZMod (l ^ m), ψ a * ζ ^ (l ^ (n - m) * a.val)) * ψ⁻¹ ((X / (l : ℤ) ^ (n - m) : ℤ) : ZMod (l ^ m)) else 0 := by
  intro K _ _ l m n _ _ ζ ψ hl hm hmn hζ hψ X
  have hl0 : 0 < l := hl.pos
  have hN : l ^ n = l ^ (n - m) * l ^ m := by rw [← pow_add, Nat.sub_add_cancel hmn]
  have hN' : l ^ n = l ^ m * l ^ (n - m) := by rw [hN, mul_comm]
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by positivity)
  set F : ℕ → K := fun k => ψ (k : ZMod (l ^ m)) * ζ ^ ((k : ℤ) * X) with hF
  have h1 : ∑ r : ZMod (l ^ n), ψ ((r.val : ℕ) : ZMod (l ^ m)) * ζ ^ ((r.val : ℤ) * X)
      = ∑ k ∈ Finset.range (l ^ n), F k := sum_zmod_val_eq_sum_range (l ^ n) F
  set y : K := ζ ^ (((l ^ m : ℕ) : ℤ) * X) with hy
  have h3 : ∀ a t : ℕ, F (a + l ^ m * t) = F a * y ^ t := by
    intro a t
    simp only [hF, hy]
    have hc : ((a + l ^ m * t : ℕ) : ZMod (l ^ m)) = (a : ZMod (l ^ m)) := by
      rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero]
    rw [hc, mul_assoc]
    congr 1
    have he : ((a + l ^ m * t : ℕ) : ℤ) * X = (a : ℤ) * X + (((l ^ m : ℕ) : ℤ) * X) * (t : ℤ) := by
      push_cast; ring
    rw [he, zpow_add₀ hζ0, zpow_mul ζ (((l ^ m : ℕ) : ℤ) * X) (t : ℤ), zpow_natCast]
  have h2 : ∑ k ∈ Finset.range (l ^ n), F k
      = (∑ a ∈ Finset.range (l ^ m), F a) * ∑ t ∈ Finset.range (l ^ (n - m)), y ^ t := by
    rw [hN', sum_range_mul_split, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [h3]
  have hω : IsPrimitiveRoot (ζ ^ (l ^ m)) (l ^ (n - m)) := hζ.pow (by positivity) hN'
  have hyω : y = (ζ ^ (l ^ m)) ^ X := by
    rw [hy, zpow_mul, zpow_natCast]
  have h4 : ∑ t ∈ Finset.range (l ^ (n - m)), y ^ t
      = if (l : ℤ) ^ (n - m) ∣ X then ((l : K) ^ (n - m)) else 0 := by
    split_ifs with hd
    · have : y = 1 := by
        rw [hyω]; exact (hω.zpow_eq_one_iff_dvd X).2 (by exact_mod_cast hd)
      simp [this]
    · have hy1 : y ≠ 1 := by
        rw [hyω]; intro h
        exact hd (by exact_mod_cast (hω.zpow_eq_one_iff_dvd X).1 h)
      rw [geom_sum_eq hy1]
      have : y ^ (l ^ (n - m)) = 1 := by
        rw [hyω, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hω.pow_eq_one,
          one_zpow]
      rw [this, sub_self, zero_div]
  have h5 : ∑ a ∈ Finset.range (l ^ m), F a = ∑ a : ZMod (l ^ m), ψ a * ζ ^ ((a.val : ℤ) * X) := by
    rw [← sum_zmod_val_eq_sum_range (l ^ m) F]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [hF, ZMod.natCast_zmod_val]
  rw [h1, h2, h4, h5]
  split_ifs with hd
  · obtain ⟨Y, rfl⟩ := hd
    have hL0 : (l : ℤ) ^ (n - m) ≠ 0 := by positivity
    rw [Int.mul_ediv_cancel_left _ hL0]
    have hξ : IsPrimitiveRoot (ζ ^ (l ^ (n - m))) (l ^ m) := hζ.pow (by positivity) hN
    have hξ0 : ζ ^ (l ^ (n - m)) ≠ 0 := pow_ne_zero _ hζ0
    let e : AddChar (ZMod (l ^ m)) K := AddChar.zmodChar (l ^ m) hξ.pow_eq_one
    have key := gaussSum_mulShift_of_isPrimitive e hψ (Y : ZMod (l ^ m))
    have hG : gaussSum ψ e = ∑ a : ZMod (l ^ m), ψ a * ζ ^ (l ^ (n - m) * a.val) := by
      unfold gaussSum
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [AddChar.zmodChar_apply, pow_mul]
    have hS : ∑ a : ZMod (l ^ m), ψ a * ζ ^ ((a.val : ℤ) * ((l : ℤ) ^ (n - m) * Y))
        = gaussSum ψ (e.mulShift Y) := by
      unfold gaussSum
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [AddChar.mulShift_apply, AddChar.zmodChar_apply]
      congr 1
      have he : (a.val : ℤ) * ((l : ℤ) ^ (n - m) * Y) = ((l ^ (n - m) : ℕ) : ℤ) * ((a.val : ℤ) * Y) := by
        push_cast; ring
      rw [he, zpow_mul, zpow_natCast, ← zpow_natCast (ζ ^ l ^ (n - m)) ((Y : ZMod (l ^ m)) * a).val]
      refine zpow_eq_zpow_of_intCast_eq hξ0 hξ.pow_eq_one ?_
      push_cast
      simp [ZMod.natCast_val, ZMod.cast_id', mul_comm]
    rw [hS, key, ← hG]
    ring
  · simp
end GlobalTheory.EisM
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterTwistedSumCongrGaussSumDirac

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries GlobalTheory.KZ.Cmp

noncomputable section

namespace GlobalTheory.KZ.Cmp.ChD

variable {l : ℕ} [Fact l.Prime]

theorem sum_units_eq_sum {N : ℕ} [NeZero N] (ψ : DirichletCharacter (Qbar l) N) (f : ZMod N → Qbar l) :
    ∑ b : (ZMod N)ˣ, ψ b * f b = ∑ a : ZMod N, ψ a * f a := by
  refine Fintype.sum_of_injective (fun b : (ZMod N)ˣ => (b : ZMod N)) Units.val_injective _ _ ?_ (fun b => rfl)
  intro a ha
  have : ¬ IsUnit a := fun hu => ha ⟨hu.unit, rfl⟩
  rw [MulChar.map_nonunit ψ this, zero_mul]

theorem norm_apply_unit_le_one {N : ℕ} [NeZero N] (ψ : DirichletCharacter (Qbar l) N) (b : (ZMod N)ˣ) :
    ‖ψ b‖ ≤ 1 := by
  have h : (ψ b) ^ (Fintype.card (ZMod N)ˣ) = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]
  have h1 := congrArg norm h
  rw [norm_pow, norm_one] at h1
  exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) Fintype.card_ne_zero).1 h1).le

theorem sum_units_char_pow (m : ℕ) (hm : 1 ≤ m) (z : Qbar l) (ψ : DirichletCharacter (Qbar l) (l ^ m))
    (hz : IsPrimitiveRoot z (l ^ m)) (hψ : ψ.IsPrimitive) (j : ℕ) :
    ∑ b : (ZMod (l ^ m))ˣ, ψ b * (z ^ (b : ZMod (l ^ m)).val) ^ j = ψ⁻¹ (j : ZMod (l ^ m)) * gSum m z ψ := by
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have key := GlobalTheory.EisM.sum_primChar_mul_rootPow_mod_pow (Qbar l) l m m z ψ (Fact.out) hm le_rfl hz hψ (j : ℤ)
  simp only [Nat.sub_self, pow_zero, one_dvd, if_true, one_mul, Int.ediv_one, Int.cast_natCast] at key
  rw [sum_units_eq_sum ψ (fun a => (z ^ a.val) ^ j)]
  unfold gSum
  rw [sum_units_eq_sum ψ (fun a => z ^ a.val)]
  have e1 : ∑ a : ZMod (l ^ m), ψ a * (z ^ a.val) ^ j =
      ∑ r : ZMod (l ^ m), ψ ((r.val : ℕ) : ZMod (l ^ m)) * z ^ ((r.val : ℤ) * (j : ℤ)) := by
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [ZMod.natCast_zmod_val, ← Nat.cast_mul, zpow_natCast, pow_mul]
  rw [e1, key, mul_comm]

theorem chSum_gauss : ∀ (l : ℕ) [Fact l.Prime] (F : PowerSeries (Qbar l)) (a : ℕ → Qbar l) (N m : ℕ) (z : Qbar l) (ψ : DirichletCharacter (Qbar l) (l ^ m)), 1 ≤ m → l ^ (3 * m) ≤ N → (∀ n, ‖F.coeff n‖ ≤ 1) → (∀ y : Qbar l, tval F N y = ∑ j ∈ Finset.range N, a j * y ^ j) → IsPrimitiveRoot z (l ^ m) → ψ.IsPrimitive → Cg (2 * m) (chSum F m z ψ) (gSum m z ψ * ∑ j ∈ Finset.range N, a j * ψ⁻¹ (j : ZMod (l ^ m))) := by
  intro l _ F a N m z ψ hm hN hF htv hz hψ
  have hl := (Fact.out : l.Prime)
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hex : gSum m z ψ * ∑ j ∈ Finset.range N, a j * ψ⁻¹ (j : ZMod (l ^ m)) =
      ∑ b : (ZMod (l ^ m))ˣ, ψ b * tval F N (z ^ (b : ZMod (l ^ m)).val) := by
    simp_rw [htv, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e : ∑ b : (ZMod (l ^ m))ˣ, ψ b * (a j * (z ^ (b : ZMod (l ^ m)).val) ^ j) =
        a j * ∑ b : (ZMod (l ^ m))ˣ, ψ b * (z ^ (b : ZMod (l ^ m)).val) ^ j := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    rw [e, sum_units_char_pow m hm z ψ hz hψ j]
    ring
  unfold Cg
  rw [hex]
  unfold chSum
  rw [← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun b _ => ?_
  rw [← mul_sub, norm_mul]
  refine (mul_le_of_le_one_left (norm_nonneg _) (norm_apply_unit_le_one ψ b)).trans ?_
  have hy : (z ^ (b : ZMod (l ^ m)).val) ^ (l ^ m) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hz.pow_eq_one, one_pow]
  have hy1 := GlobalTheory.AmiceDist.norm_sub_one_le hy
  have hy3 := GlobalTheory.AmiceDist.norm_sub_one_pow_three_le hy
  unfold tval
  rw [← Finset.sum_range_add_sum_Ico _ hN, sub_add_cancel_left, norm_neg]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun n hn => ?_
  rw [norm_mul, norm_pow]
  exact (mul_le_of_le_one_left (by positivity) (hF n)).trans
    ((pow_le_pow_of_le_one (norm_nonneg _) hy1 (Finset.mem_Ico.1 hn).1).trans hy3)

end GlobalTheory.KZ.Cmp.ChD
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterTwistedSumCongrGaussSumDiracStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries GlobalTheory.KZ.Cmp

theorem _root_.GlobalTheory.T.characterTwistedSum_congr_gaussSum_dirac : ∀ (l : ℕ) [Fact l.Prime] (F : PowerSeries (Qbar l)) (a : ℕ → Qbar l) (N m : ℕ) (z : Qbar l) (ψ : DirichletCharacter (Qbar l) (l ^ m)), 1 ≤ m → l ^ (3 * m) ≤ N → (∀ n, ‖F.coeff n‖ ≤ 1) → (∀ y : Qbar l, tval F N y = ∑ j ∈ Finset.range N, a j * y ^ j) → IsPrimitiveRoot z (l ^ m) → ψ.IsPrimitive → Cg (2 * m) (chSum F m z ψ) (gSum m z ψ * ∑ j ∈ Finset.range N, a j * ψ⁻¹ (j : ZMod (l ^ m))) := by
  first | exact @GlobalTheory.KZ.Cmp.ChD.chSum_gauss | exact GlobalTheory.KZ.Cmp.ChD.chSum_gauss | (intros; apply GlobalTheory.KZ.Cmp.ChD.chSum_gauss; all_goals assumption)
end
end
