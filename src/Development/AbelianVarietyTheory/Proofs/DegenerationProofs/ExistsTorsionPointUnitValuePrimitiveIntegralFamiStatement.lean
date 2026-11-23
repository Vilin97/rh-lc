module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionPointPrimitiveComponentValuationZerStatement
public import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FinsuppEqZeroOfSumTorsionCharactersEqZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtOntoDivisibleKernel
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTerms
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTermsStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionIdentificationWithPairingStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuationsTorusPointsFramesFamilyTerms
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtFormalTorsion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BOfNsmulLeft
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CoeffRecoveryByTorsionAverages

section

@[expose] public section

namespace GlobalTheory.TorsRecov

theorem card_tors (F X : Type) [Field F] [IsAlgClosed F] [CharZero F] [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (N : ℕ) (hN : 0 < N) :
    Nat.card {t : Multiplicative X →* Fˣ // t ^ N = 1} = N ^ Module.finrank ℤ X := by
  classical
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero (N : F) := ⟨by exact_mod_cast hN.ne'⟩
  let b := Module.Free.chooseBasis ℤ X
  let f : {t : Multiplicative X →* Fˣ // t ^ N = 1} →
      (Module.Free.ChooseBasisIndex ℤ X → rootsOfUnity N F) := fun t i =>
    ⟨t.1 (Multiplicative.ofAdd (b i)), by
      rw [mem_rootsOfUnity, ← MonoidHom.pow_apply, t.2, MonoidHom.one_apply]⟩
  have hrep : ∀ (t : Multiplicative X →* Fˣ) (x : X), t (Multiplicative.ofAdd x) =
      ∏ i, t (Multiplicative.ofAdd (b i)) ^ (b.repr x i) := by
    intro t x
    conv_lhs => rw [← b.sum_repr x]
    rw [ofAdd_sum, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [ofAdd_zsmul, map_zpow]
  have hf : Function.Bijective f := by
    constructor
    · intro s t h
      apply Subtype.ext
      refine MonoidHom.ext fun x => ?_
      have h1 := hrep s.1 x.toAdd
      have h2 := hrep t.1 x.toAdd
      rw [ofAdd_toAdd] at h1 h2
      rw [h1, h2]
      refine Finset.prod_congr rfl fun i _ => ?_
      have := congrArg Subtype.val (congrFun h i)
      simp only [f] at this
      rw [this]
    · intro u
      let t : Multiplicative X →* Fˣ :=
        { toFun := fun x => ∏ i, (u i : Fˣ) ^ (b.repr (Multiplicative.toAdd x) i)
          map_one' := by simp
          map_mul' := by
            intro x y
            simp [zpow_add, Finset.prod_mul_distrib] }
      have ht : t ^ N = 1 := by
        refine MonoidHom.ext fun x => ?_
        rw [MonoidHom.pow_apply, MonoidHom.one_apply]
        change (∏ i, (u i : Fˣ) ^ (b.repr (Multiplicative.toAdd x) i)) ^ N = 1
        rw [← Finset.prod_pow]
        refine Finset.prod_eq_one fun i _ => ?_
        have hu : (u i : Fˣ) ^ N = 1 := (mem_rootsOfUnity _ _).1 (u i).2
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu, one_zpow]
      refine ⟨⟨t, ht⟩, ?_⟩
      funext i
      apply Subtype.ext
      change ∏ j, (u j : Fˣ) ^ (b.repr (b i) j) = u i
      rw [Finset.prod_eq_single i]
      · simp
      · intro j _ hj
        simp [Finsupp.single_apply, hj.symm]
      · simp
  rw [Nat.card_congr (Equiv.ofBijective f hf), Nat.card_fun, HasEnoughRootsOfUnity.natCard_rootsOfUnity,
    Module.finrank_eq_card_chooseBasisIndex, Nat.card_eq_fintype_card]

open Classical in
theorem sum_tors (F X : Type) [Field F] [IsAlgClosed F] [CharZero F] [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (N : ℕ) (hN : 0 < N)
    [Fintype {t : Multiplicative X →* Fˣ // t ^ N = 1}] (α β : X) :
    ∑ t : {t : Multiplicative X →* Fˣ // t ^ N = 1},
      ((t.1 (Multiplicative.ofAdd β))⁻¹).val * (t.1 (Multiplicative.ofAdd α)).val =
      if ∃ z, α = β + N • z then (N : F) ^ Module.finrank ℤ X else 0 := by
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero (N : F) := ⟨by exact_mod_cast hN.ne'⟩
  split_ifs with h
  · obtain ⟨z, rfl⟩ := h
    rw [Finset.sum_congr rfl (g := fun _ => (1 : F))]
    · rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, card_tors F X N hN]
      simp
    · intro t _
      rw [ofAdd_add, map_mul, ofAdd_nsmul, map_pow, ← MonoidHom.pow_apply, t.2]
      simp
  · obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F N
    have : ∃ t₀ : Multiplicative X →* Fˣ, t₀ ^ N = 1 ∧
        t₀ (Multiplicative.ofAdd α) ≠ t₀ (Multiplicative.ofAdd β) := by
      by_contra hc
      push_neg at hc
      exact h (GlobalTheory.exists_eq_add_nsmul_of_torsion_characters_eq F X N ζ hN hζ α β hc)
    obtain ⟨t₀, h₀, hne⟩ := this
    have h₀' : t₀⁻¹ ^ N = 1 := by rw [inv_pow, h₀, inv_one]
    let e : {t : Multiplicative X →* Fˣ // t ^ N = 1} ≃ {t : Multiplicative X →* Fˣ // t ^ N = 1} :=
      { toFun := fun t => ⟨t₀ * t.1, by rw [mul_pow, h₀, t.2, mul_one]⟩
        invFun := fun t => ⟨t₀⁻¹ * t.1, by rw [mul_pow, h₀', t.2, mul_one]⟩
        left_inv := fun t => Subtype.ext (inv_mul_cancel_left _ _)
        right_inv := fun t => Subtype.ext (mul_inv_cancel_left _ _) }
    set s := ∑ t : {t : Multiplicative X →* Fˣ // t ^ N = 1},
      ((t.1 (Multiplicative.ofAdd β))⁻¹).val * (t.1 (Multiplicative.ofAdd α)).val with hs
    have h1 : s = (((t₀ (Multiplicative.ofAdd β))⁻¹).val * (t₀ (Multiplicative.ofAdd α)).val) * s := by
      conv_lhs => rw [hs, ← e.sum_comp]
      rw [hs, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      simp only [e, Equiv.coe_fn_mk, MonoidHom.mul_apply, mul_inv, Units.val_mul]
      ring
    by_contra hs0
    apply hne
    have h2 : ((t₀ (Multiplicative.ofAdd β))⁻¹).val * (t₀ (Multiplicative.ofAdd α)).val = 1 :=
      mul_right_cancel₀ hs0 (by rw [← h1, one_mul])
    rw [← Units.val_mul, Units.val_eq_one, inv_mul_eq_one] at h2
    exact h2.symm

theorem eq_zero_of_div (X : Type) [AddCommGroup X] [Module.Free ℤ X] (n : ℕ) (hn : 2 ≤ n) (x : X)
    (h : ∀ k, ∃ z, x = n ^ k • z) : x = 0 := by
  let b := Module.Free.chooseBasis ℤ X
  apply b.repr.injective
  ext i
  rw [map_zero, Finsupp.zero_apply]
  obtain ⟨z, hz⟩ := h (b.repr x i).natAbs
  refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (d := ((n ^ (b.repr x i).natAbs : ℕ) : ℤ))
    ⟨b.repr z i, ?_⟩ ?_
  · conv_lhs => rw [hz]
    rw [map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]
  · rw [Int.natAbs_natCast]
    exact Nat.lt_pow_self (by omega)

theorem class_mono (X : Type) [AddCommGroup X] (n : ℕ) (c : ℕ → X)
    (hc : ∀ k, ∃ z, c (k + 1) = c k + n ^ k • z) (α : X) (j k : ℕ) (hjk : j ≤ k)
    (h : ∃ z, α = c k + n ^ k • z) : ∃ z, α = c j + n ^ j • z := by
  induction k, hjk using Nat.le_induction with
  | base => exact h
  | succ k _ ih =>
    apply ih
    obtain ⟨z, hz⟩ := h
    obtain ⟨w, hw⟩ := hc k
    exact ⟨w + n • z, by rw [hz, hw, pow_succ, mul_smul, smul_add, add_assoc]⟩

theorem val_eq_zero_of_pow {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) (x : F) (N : ℕ)
    (hN : 0 < N) (h : x ^ N = 1) : v x = 0 := by
  have h1 : N • v x = 0 := by rw [← v.map_pow, h, v.map_one]
  have hx : x ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at h
    exact zero_ne_one h
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 ((v.ne_top_iff).2 hx)
  rw [← hr, ← WithTop.coe_nsmul, WithTop.coe_eq_zero, smul_eq_zero] at h1
  rw [← hr, h1.resolve_left hN.ne', WithTop.coe_zero]

theorem val_inv_pow {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) (x : F) (m : ℕ)
    (h : v x = 0) : v (x ^ m)⁻¹ = 0 := by
  have hx : x ≠ 0 := by
    rintro rfl
    rw [v.map_zero] at h
    exact WithTop.top_ne_zero h
  have h1 : v (x ^ m) = 0 := by rw [v.map_pow, h, smul_zero]
  have h2 := v.map_mul (x ^ m) (x ^ m)⁻¹
  rw [mul_inv_cancel₀ (pow_ne_zero _ hx), v.map_one, h1, zero_add] at h2
  exact h2.symm

end GlobalTheory.TorsRecov

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

theorem GlobalTheory.coeff_recovery_by_torsion_averages : ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] (v : AddValuation F (WithTop ℚ)) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (n : ℕ), 2 ≤ n → v (n : F) = 0 → ∀ a : X → F, NullV v a → ∀ S : (Multiplicative X →* Fˣ) → F, (∀ t : Multiplicative X →* Fˣ, (∃ k, t ^ n ^ k = 1) → SumV v (fun α => (t (Multiplicative.ofAdd α)).val * a α) (S t)) → ∀ c : ℕ → X, (∀ k, ∃ z, c (k + 1) = c k + n ^ k • z) → ∀ (lim : F), ((∃ χ, (∀ k, ∃ z, χ = c k + n ^ k • z) ∧ lim = a χ) ∨ ((¬ ∃ χ, ∀ k, ∃ z, χ = c k + n ^ k • z) ∧ lim = 0)) → ∀ q : ℚ, ∃ k₀, ∀ k ≥ k₀, (q : WithTop ℚ) ≤ v (lim - ((n : F) ^ (k * Module.finrank ℤ X))⁻¹ * ∑ᶠ t : {t : Multiplicative X →* Fˣ // t ^ n ^ k = 1}, ((t.1 (Multiplicative.ofAdd (c k)))⁻¹).val * S t.1) := by
  intro F _ _ _ v X _ _ _ n hn hv a ha S hS c hc lim hlim q
  classical
  have hB : ∀ α : X, ∃ j : ℕ, (¬ ∀ k, ∃ z, α = c k + n ^ k • z) → ¬ ∃ z, α = c j + n ^ j • z := by
    intro α
    by_cases h : ∀ k, ∃ z, α = c k + n ^ k • z
    · exact ⟨0, fun h' => (h' h).elim⟩
    · obtain ⟨j, hj⟩ := not_forall.1 h
      exact ⟨j, fun _ => hj⟩
  choose j hj using hB
  refine ⟨(ha q).toFinset.sup j, fun k hk => ?_⟩
  have hN : 0 < n ^ k := pow_pos (by omega) k
  have hn0 : (n : F) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have key : ∀ α : X, (∃ z, α = c k + n ^ k • z) → (¬ ∀ k, ∃ z, α = c k + n ^ k • z) →
      (q : WithTop ℚ) ≤ v (a α) := by
    intro α h1 h2
    by_contra h3
    have h4 : α ∈ (ha q).toFinset := (ha q).mem_toFinset.2 (not_le.1 h3)
    exact hj α h2 (GlobalTheory.TorsRecov.class_mono X n c hc α _ k ((Finset.le_sup h4).trans hk) h1)
  haveI : Finite {t : Multiplicative X →* Fˣ // t ^ n ^ k = 1} :=
    Nat.finite_of_card_ne_zero (by
      rw [GlobalTheory.TorsRecov.card_tors F X _ hN]; exact pow_ne_zero _ hN.ne')
  letI := Fintype.ofFinite {t : Multiplicative X →* Fˣ // t ^ n ^ k = 1}
  rw [finsum_eq_sum_of_fintype]
  have hS' := fun t : {t : Multiplicative X →* Fˣ // t ^ n ^ k = 1} => hS t.1 ⟨k, t.2⟩ q
  choose S₀ hS₀ using hS'
  have main : ∀ T : Finset X, (∀ t, S₀ t ⊆ T) →
      (q : WithTop ℚ) ≤ v (lim - ∑ α ∈ T.filter (fun α => ∃ z, α = c k + n ^ k • z), a α) →
      (q : WithTop ℚ) ≤ v (lim - ((n : F) ^ (k * Module.finrank ℤ X))⁻¹ *
        ∑ t : {t : Multiplicative X →* Fˣ // t ^ n ^ k = 1},
          ((t.1 (Multiplicative.ofAdd (c k)))⁻¹).val * S t.1) := by
    intro T hT h
    have e1 : ∑ t : {t : Multiplicative X →* Fˣ // t ^ n ^ k = 1},
          ((t.1 (Multiplicative.ofAdd (c k)))⁻¹).val *
            ∑ α ∈ T, (t.1 (Multiplicative.ofAdd α)).val * a α =
        (n : F) ^ (k * Module.finrank ℤ X) *
          ∑ α ∈ T.filter (fun α => ∃ z, α = c k + n ^ k • z), a α := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm, Finset.sum_filter]
      refine Finset.sum_congr rfl fun α _ => ?_
      simp only [← _root_.mul_assoc]
      rw [← Finset.sum_mul, GlobalTheory.TorsRecov.sum_tors F X _ hN]
      split_ifs
      · rw [Nat.cast_pow, ← pow_mul]
      · rw [zero_mul]
    have e2 : lim - ((n : F) ^ (k * Module.finrank ℤ X))⁻¹ *
        ∑ t : {t : Multiplicative X →* Fˣ // t ^ n ^ k = 1},
          ((t.1 (Multiplicative.ofAdd (c k)))⁻¹).val * S t.1 =
        (lim - ∑ α ∈ T.filter (fun α => ∃ z, α = c k + n ^ k • z), a α) -
        ((n : F) ^ (k * Module.finrank ℤ X))⁻¹ *
        ∑ t : {t : Multiplicative X →* Fˣ // t ^ n ^ k = 1},
          ((t.1 (Multiplicative.ofAdd (c k)))⁻¹).val *
            (S t.1 - ∑ α ∈ T, (t.1 (Multiplicative.ofAdd α)).val * a α) := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      rw [e1, inv_mul_cancel_left₀ (pow_ne_zero _ hn0)]
      ring
    rw [e2]
    refine v.map_le_sub h ?_
    rw [v.map_mul, GlobalTheory.TorsRecov.val_inv_pow v _ _ hv, zero_add]
    refine v.map_le_sum fun t _ => ?_
    rw [v.map_mul, GlobalTheory.TorsRecov.val_eq_zero_of_pow v _ _ hN, zero_add]
    · exact hS₀ t T (hT t)
    · rw [← Units.val_pow_eq_pow_val, inv_pow, ← MonoidHom.pow_apply, t.2]
      simp
  rcases hlim with ⟨χ, hχ, rfl⟩ | ⟨hno, rfl⟩
  · refine main (insert χ (Finset.univ.biUnion S₀)) (fun t => ?_) ?_
    · exact (Finset.subset_biUnion_of_mem S₀ (Finset.mem_univ t)).trans (Finset.subset_insert _ _)
    · rw [← Finset.add_sum_erase _ a (a := χ)
        (Finset.mem_filter.2 ⟨Finset.mem_insert_self _ _, hχ k⟩), sub_add_cancel_left, v.map_neg]
      refine v.map_le_sum fun α hα => ?_
      obtain ⟨h1, h2⟩ := Finset.mem_erase.1 hα
      refine key α (Finset.mem_filter.1 h2).2 fun h3 => h1 ?_
      rw [← sub_eq_zero]
      refine GlobalTheory.TorsRecov.eq_zero_of_div X n hn _ fun m => ?_
      obtain ⟨z, hz⟩ := h3 m
      obtain ⟨w, hw⟩ := hχ m
      exact ⟨z - w, by rw [hz, hw, smul_sub, add_sub_add_left_eq_sub]⟩
  · refine main (Finset.univ.biUnion S₀)
      (fun t => Finset.subset_biUnion_of_mem S₀ (Finset.mem_univ t)) ?_
    rw [zero_sub, v.map_neg]
    refine v.map_le_sum fun α hα => ?_
    exact key α (Finset.mem_filter.1 hα).2 fun h3 => hno ⟨α, h3⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionPointUnitValuePrimitiveIntegralFami

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section
namespace GlobalTheory.OneBasis.UnitValue
open GlobalTheory.TorusExt GlobalTheory.UT.WeightValue GlobalTheory.UT.CoefBasic

theorem not_all_ne_zero {F : Type} [Field F] [IsAlgClosed F] [CharZero F] {v : AddValuation F (WithTop ℚ)} {X : Type}
    [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] {n : ℕ} (hn : 2 ≤ n) (hvn : v (n : F) = 0) {a : X → F}
    (ha : NullV v a) (h0 : ∀ χ, 0 ≤ v (a χ)) {α : X} (hα : v (a α) = 0)
    (H : ∀ t : Multiplicative X →* Fˣ, (∃ k, t ^ n ^ k = 1) →
      ∃ S, SumV v (fun χ => (t (Multiplicative.ofAdd χ)).val * a χ) S ∧ v S ≠ 0) : False := by
  classical
  choose! S hS hS0 using H
  have hroot : ∀ (t : Multiplicative X →* Fˣ) (k : ℕ), t ^ n ^ k = 1 → ∀ χ, v (t χ).val = 0 ∧ v ((t χ)⁻¹).val = 0 := by
    intro t k ht χ
    have e : t χ ^ n ^ k = 1 := by rw [← MonoidHom.pow_apply, ht, MonoidHom.one_apply]
    have hN : 0 < n ^ k := pow_pos (by omega) k
    exact ⟨GlobalTheory.TorsRecov.val_eq_zero_of_pow v _ _ hN (by rw [← Units.val_pow_eq_pow_val, e, Units.val_one]),
      GlobalTheory.TorsRecov.val_eq_zero_of_pow v _ _ hN (by rw [← Units.val_pow_eq_pow_val, inv_pow, e, inv_one, Units.val_one])⟩
  have hpos : ∀ (t : Multiplicative X →* Fˣ) (k : ℕ), t ^ n ^ k = 1 → 0 < v (S t) := fun t k ht =>
    lt_of_le_of_ne (le_of_sumV (q := 0) (hS t ⟨k, ht⟩) fun χ => by
      rw [v.map_mul, (hroot t k ht _).1, zero_add]; exact h0 χ) (hS0 t ⟨k, ht⟩).symm
  obtain ⟨k, hk⟩ := GlobalTheory.coeff_recovery_by_torsion_averages F v X n hn hvn a ha S hS (fun _ => α)
    (fun _ => ⟨0, by simp⟩) (a α) (Or.inl ⟨α, fun _ => ⟨0, by simp⟩, rfl⟩) 1
  have h1 := hk k le_rfl
  have hN : 0 < n ^ k := pow_pos (by omega) k
  haveI : Finite {t : Multiplicative X →* Fˣ // t ^ n ^ k = 1} :=
    Nat.finite_of_card_ne_zero (by
      rw [GlobalTheory.TorsRecov.card_tors F X _ hN]; exact pow_ne_zero _ hN.ne')
  letI := Fintype.ofFinite {t : Multiplicative X →* Fˣ // t ^ n ^ k = 1}
  rw [finsum_eq_sum_of_fintype] at h1
  have h2 : 0 < v (((n : F) ^ (k * Module.finrank ℤ X))⁻¹ * ∑ t : {t : Multiplicative X →* Fˣ // t ^ n ^ k = 1},
      ((t.1 (Multiplicative.ofAdd α))⁻¹).val * S t.1) := by
    rw [v.map_mul, GlobalTheory.TorsRecov.val_inv_pow v _ _ hvn, zero_add]
    refine v.map_lt_sum WithTop.zero_ne_top fun t _ => ?_
    rw [v.map_mul, (hroot t.1 k t.2 _).2, zero_add]
    exact hpos t.1 k t.2
  have h3 := v.map_lt_add (lt_of_lt_of_le (by exact_mod_cast (zero_lt_one : (0 : ℚ) < 1)) h1) h2
  rw [sub_add_cancel, hα] at h3
  exact lt_irrefl _ h3

section
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} {hϖ : Irreducible ϖ}
  {D : DegData V (maximalIdeal V)}
  {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)} {hv : ValOver ϖ F v}

theorem exists_frm_zero (k : ℕ) (g : GtPtF D.toPre F) : ∃ w : Frm D.toPre F k g.b, w.IsGen ∧ GenV hϖ hv w 0 := by
  obtain ⟨w, hw⟩ := (coef_basic V D.toPre F k g).1
  obtain ⟨r, φ₀, hφ, t₀, ht₀, x, hx, e⟩ := CoefVal.exists_genV_frm (hϖ := hϖ) (hv := hv) hw
  have hx0 : x ≠ 0 := v.ne_top_iff.1 (by rw [hx]; exact WithTop.coe_ne_top)
  obtain ⟨w', hw', e'⟩ := TorsionValue.exists_frm_scale w hw (inv_ne_zero hx0)
  refine ⟨w', hw', φ₀, hφ, t₀, ht₀, 1, v.map_one, fun z J hJ => ?_⟩
  rw [e' z J hJ, e z J hJ, ← _root_.mul_assoc, cst_eq, cst_eq, cst_eq, ← map_mul, inv_mul_cancel₀ hx0]

theorem exists_frm_cast {k : ℕ} {b b' : TF (R := V) F ⟶ D.toPre.P.A} (hb : b' = b) (w : Frm D.toPre F k b) (hw : w.IsGen)
    (h0 : GenV hϖ hv w 0) : ∃ w' : Frm D.toPre F k b', w'.IsGen ∧ GenV hϖ hv w' 0 ∧
      ∀ z J, Good D.toPre.P.L z J → val w' (𝟙 _) z J = val w (𝟙 _) z J := by
  subst hb
  exact ⟨w, hw, h0, fun _ _ _ => rfl⟩

end


attribute [local instance] gtGroup in
theorem exists_unit_value : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ k n : ℕ, 4 ≤ k → n.Prime → IsUnit (n : V) → ∀ (t : SecA A F k) (s : Fam D.toPre F k) (α : D.toPre.X), U.ExpandsF F k w₀ t s → IntGe D v s 0 → (∀ q : ℚ, 0 < q → ¬ VGe D F v k α (s.s α) q) → ∃ (j : ℕ) (x : TFK (R := V) F ⟶ A.A), 2 ≤ j ∧ FromGt U.toUnifPre (n ^ j) x ∧ ∀ e (c : F), IsTorsFrame A ρ (n ^ j) x e → ValAt t x e c → v c = 0 := by
  intro hL hT hVR hTW hUU V _ _ _ _ hcpl ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hN k n hk hn hnV t s α hts hint hprim
  by_contra hcon
  have hk1 : 1 ≤ k := by omega
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hcpl⟩
  have : CharZero (FractionRing V) := IsFractionRing.charZero V
  have : CharZero F := (algebraMap (FractionRing V) F).charZero_iff (algebraMap (FractionRing V) F).injective |>.1 this
  obtain ⟨i, g, o, ho, hgo, hg⟩ := GlobalTheory.T.exists_torsion_point_primitive_component_valuation_zero hL hT hVR hTW hUU V hcpl ϖ hϖ D Q hQ F v hv k n hk hn hnV s α
    (hint α) hprim
  have hgi : n ^ i • g = 0 := ((isNsmul_iff_eq _ _ _).1 hgo).symm.trans ((isZero_iff_eq _).1 ho)
  obtain ⟨w, hw, hw0⟩ := exists_frm_zero (hϖ := hϖ) (hv := hv) k g
  have hB := D.tau_bimult
  have hiota0 : ∀ (h : GtPtF D.toPre F), h.IsZero → h.IsIota 0 := by
    intro h hh
    obtain ⟨hb, hv⟩ := (isZero_iff h).1 hh
    refine (isIota_iff 0 h).2 ⟨hb.trans (cPoint_zero _).symm, fun χ y J hJ => ?_⟩
    have face : ∀ x z, th D.toPre (T := TF (R := V) F) y J 1 x z = 1 := by
      intro x z
      have e := val_corr hJ (D.toPre.cub.face 0) (lift x z).left
      rw [val_one] at e
      refine Eq.trans ?_ e
      refine Eq.trans ?_ (val_cub D.toPre.cub (lift x z) hJ (pzero _ _) (x2 _ 0) (x2 _ 1)).symm
      congr 1 <;> simp [x2, pzero, Hom.one_def]
    have tt := tau_mul (𝟙 (TF (R := V) F)) hJ hB 0 0 χ
    rw [add_zero, cPoint_zero, face, _root_.mul_one] at tt
    exact (hv χ y J hJ).trans (mul_eq_left.1 tt.symm).symm
  let qkMk (g : GtPtF D.toPre F) {k : ℕ} (h : k • g = 0) : QkPt D.toPre F k :=
    ⟨0, g, k • g, (isNsmul_iff_eq _ _ _).2 rfl, hiota0 _ ((isZero_iff_eq _).2 h)⟩
  have hgV : ∀ χ, GenV hϖ hv (g.s χ) 0 := fun χ => by
    have e := CoefVal.gtV_qk (hϖ := hϖ) (hv := hv) hVR hQ (Nat.one_le_pow i n hn.pos)
      (qkMk g hgi) χ
    simpa only [qkMk, bOf_zero_left hϖ hQ, Int.cast_zero, zero_div] using e
  have hvn : v (n : F) = 0 := by
    have e := GC.v_alg_unit hv hnV.unit
    rwa [IsUnit.unit_spec, map_natCast, map_natCast] at e
  refine not_all_ne_zero (v := v) (a := coef s g w) (α := α) hn.two_le hvn
    (((CoefVal.main hL hT hVR hTW hUU V hcpl ϖ hϖ D Q hQ F v hv g).2.2.2.2.2.2 k hk1 w s hw).1)
    (fun χ => by simpa using CoefVal.le_v_coef hw (hint χ) (hgV χ) hw0) (hg w hw hw0) ?_
  rintro τ ⟨m, hm⟩
  have hj : 1 ≤ n ^ (i + m + 2) := Nat.one_le_pow _ n hn.pos
  let p : QkPt D.toPre F (n ^ (i + m + 2)) := qkMk (g + torusPt D.toPre F (Additive.ofMul τ)) (by
    have e₁ : n ^ (i + m + 2) • g = 0 := by rw [add_assoc, pow_add, mul_comm, mul_smul, hgi, smul_zero]
    have e₂ : τ ^ n ^ (i + m + 2) = 1 := by
      rw [show i + m + 2 = m + (i + 2) by ring, pow_add, pow_mul, hm, one_pow]
    rw [smul_add, e₁, ← map_nsmul, ← ofMul_pow, e₂, ofMul_one, map_zero, add_zero])
  obtain ⟨f, hf, -⟩ := GlobalTheory.T.uniformisation_torsion_identification_with_pairing hL V (maximalIdeal V) hA D A G hG U F _ hj
  have hx : QkToAkU U.toUnifPre F _ p (f p) := (hf p _).2 rfl
  have hex : ∃ e c, IsTorsFrame A ρ (n ^ (i + m + 2)) (f p) e ∧ ValAt t (f p) e c ∧ v c ≠ 0 := by
    by_contra h
    refine hcon ⟨i + m + 2, f p, by omega, ⟨p, rfl, hx⟩, fun e c he hc => ?_⟩
    by_contra h'
    exact h ⟨e, c, he, hc, h'⟩
  obtain ⟨e, c, he, hc, hc0⟩ := hex
  obtain ⟨w₁, hw₁, hv₁, hsum⟩ := GlobalTheory.T.section_value_at_torsionPoint_eq_sum_terms hL hT hVR hTW hUU V hcpl ϖ hϖ D Q hQ F v hv A G hG U w₀ ρ hN _ hj p _ hx e he
  have hv₁ : GenV hϖ hv w₁ 0 := by
    have e0 : ((Q p.y : ℚ) / ((n ^ (i + m + 2) : ℕ) : ℚ) ^ 2) = 0 := by
      rw [show p.y = 0 from by simp only [p, qkMk], QForm.Q_zero hϖ D hQ]; simp
    rwa [e0] at hv₁
  obtain ⟨w₂, hw₂, hwv⟩ := exists_pow k (line_exp k) w₁ hw₁
  have hw₂0 : GenV hϖ hv w₂ 0 := genV_pow k (line_exp k) hv₁ fun z J _ => hwv _ _ z J
  have hS : SumV v (coef s p.g w₂) c := hsum k hk1 w₂ ⟨hw₂, fun z J _ => hwv _ _ z J⟩ t s c hts hc
  have hb : p.g.b = g.b := by
    simp only [p, qkMk, add_b, torusPt_b, _root_.mul_one]
  obtain ⟨w', hw', hw'0, hww⟩ := exists_frm_cast hb w hw hw0
  obtain ⟨u, hu, huv, huc⟩ := ((coef_basic V D.toPre F k p.g).2.2 w₂ hw₂).2.2.1 w' hw'
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 (v.ne_top_iff.2 hu)
  have r0 : r = 0 := by
    have := CoefVal.sep D
    exact CoefVal.genV_unique D.toPre.P.isLB (genV_smul hw₂0 hr.symm huv) hw'0
  have hu0 : v u = 0 := by rw [← hr, r0]; rfl
  have htr := ((coef_basic V D.toPre F k g).2.2 w hw).2.2.2 τ _ p.g w'
    ((isTor_iff _ _).2 (isTorusPtF_torusPt τ)) ((isAdd_iff_eq _ _ _).2 (by simp only [p, qkMk])) hww s
  refine ⟨u * c, ?_, by rwa [v.map_mul, hu0, zero_add]⟩
  have := sumV_mul hS hu0
  simpa only [← huc, htr] using this

end GlobalTheory.OneBasis.UnitValue
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionPointUnitValuePrimitiveIntegralFamiStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

theorem _root_.GlobalTheory.T.exists_torsionPoint_unit_value_primitive_integral_family : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ k n : ℕ, 4 ≤ k → n.Prime → IsUnit (n : V) → ∀ (t : SecA A F k) (s : Fam D.toPre F k) (α : D.toPre.X), U.ExpandsF F k w₀ t s → IntGe D v s 0 → (∀ q : ℚ, 0 < q → ¬ VGe D F v k α (s.s α) q) → ∃ (j : ℕ) (x : TFK (R := V) F ⟶ A.A), 2 ≤ j ∧ FromGt U.toUnifPre (n ^ j) x ∧ ∀ e (c : F), IsTorsFrame A ρ (n ^ j) x e → ValAt t x e c → v c = 0 := by
  first | exact @GlobalTheory.OneBasis.UnitValue.exists_unit_value | exact GlobalTheory.OneBasis.UnitValue.exists_unit_value | (intros; apply GlobalTheory.OneBasis.UnitValue.exists_unit_value <;> assumption)
end
end
