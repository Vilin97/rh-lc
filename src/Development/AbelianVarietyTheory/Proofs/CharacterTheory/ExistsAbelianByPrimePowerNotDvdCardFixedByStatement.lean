module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.SetTheory.Cardinal.Finite
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
import Mathlib.Tactic.Linter.Style
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
public import Mathlib.GroupTheory.GroupAction.FixedPoints
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.Nat.Factorization.Basic
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsSylowOverSubgroupStatement
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.CharacterTheory.CardFixedByPowPrimePowModEq

section

@[expose] public section

namespace GlobalTheory

theorem card_fixedBy_pow_prime_pow_modEq (G : Type) [Group G] (X : Type) [Finite X] [MulAction G X]
    (x : G) (p k : ℕ) (hp : p.Prime) :
    Nat.card (MulAction.fixedBy X (x ^ p ^ k)) ≡ Nat.card (MulAction.fixedBy X x) [MOD p] := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype X := Fintype.ofFinite X
  let f : Function.End (MulAction.fixedBy X (x ^ p ^ k)) := fun y => ⟨x • (y : X), by
    have hy : (x ^ p ^ k) • (y : X) = y := y.2
    show (x ^ p ^ k) • x • (y : X) = x • (y : X)
    rw [← mul_smul, ← pow_succ, pow_succ', mul_smul, hy]⟩
  have hf : ∀ (n : ℕ) (y : MulAction.fixedBy X (x ^ p ^ k)), (((f ^ n) y : MulAction.fixedBy X (x ^ p ^ k)) : X) = x ^ n • (y : X) := by
    intro n
    induction n with
    | zero => intro y; rw [pow_zero, pow_zero, one_smul]; rfl
    | succ n ih =>
      intro y
      rw [pow_succ', pow_succ', mul_smul, ← ih y]
      rfl
  have h1 : f ^ p ^ k = 1 := by
    funext y
    apply Subtype.ext
    rw [hf]
    exact y.2
  have h2 := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := p) (n := k) h1
  have e : (Function.fixedPoints f) ≃ MulAction.fixedBy X x :=
    { toFun := fun y => ⟨(y.1 : X), congrArg Subtype.val y.2⟩
      invFun := fun y => ⟨⟨y.1, MulAction.fixedBy_subset_fixedBy_zpow X x ((p ^ k : ℕ) : ℤ) y.2 |> fun h => by
          rwa [zpow_natCast] at h⟩, Subtype.ext y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  convert h2

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CharacterTheory.CardFixedByPowPrimePowModEqStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.card_fixedBy_pow_prime_pow_modEq_card_fixedBy : ∀ (G : Type) [Group G] (X : Type) [Finite X] [MulAction G X] (x : G) (p k : ℕ), p.Prime → Nat.card (MulAction.fixedBy X (x ^ p ^ k)) ≡ Nat.card (MulAction.fixedBy X x) [MOD p] := by
  first | exact @GlobalTheory.card_fixedBy_pow_prime_pow_modEq | exact GlobalTheory.card_fixedBy_pow_prime_pow_modEq | (intros; apply GlobalTheory.card_fixedBy_pow_prime_pow_modEq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CharacterTheory.CardFixedByQuotientEqRelIndexOfPRegular

section

@[expose] public section

namespace GlobalTheory

theorem conj_mem_zpowers_of_mem_of_pRegular {G : Type} [Group G] (c : G) (p : ℕ) (H : Subgroup G)
    (hc : Nat.Coprime (orderOf c) p)
    (hp : ∀ h ∈ H, ∃ k : ℕ, h ^ p ^ k ∈ Subgroup.zpowers c) (g : G)
    (hg : g⁻¹ * c * g ∈ H) : g⁻¹ * c * g ∈ Subgroup.zpowers c := by
  obtain ⟨k, hk⟩ := hp _ hg
  have ho : orderOf (g⁻¹ * c * g) = orderOf c := by
    have := (MulAut.conj g⁻¹).orderOf_eq c
    simpa using this
  have hcop : Nat.Coprime (p ^ k) (orderOf (g⁻¹ * c * g)) := by
    rw [ho]
    exact Nat.Coprime.pow_left k hc.symm
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm]
  exact Subgroup.pow_mem _ hk m

theorem card_fixedBy_quotient_eq_relIndex_of_pRegular :
    ∀ (G : Type) [Group G] [Finite G] (c : G) (p : ℕ) (H N : Subgroup G), Nat.Coprime (orderOf c) p → Subgroup.zpowers c ≤ H → (∀ h ∈ H, ∃ k : ℕ, h ^ p ^ k ∈ Subgroup.zpowers c) → (∀ g : G, g ∈ N ↔ ∀ d ∈ Subgroup.zpowers c, g * d * g⁻¹ ∈ Subgroup.zpowers c) → Nat.card (MulAction.fixedBy (G ⧸ H) c) = H.relIndex N := by
  intro G _ _ c p H N hc hH hp hN
  have key : ∀ g : G, c • (g : G ⧸ H) = (g : G ⧸ H) ↔ g ∈ N := by
    intro g
    have h1 : c • (g : G ⧸ H) = (g : G ⧸ H) ↔ g⁻¹ * c * g ∈ H := by
      rw [eq_comm, MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq, mul_assoc]
    rw [h1]
    constructor
    · intro hg
      have hy := conj_mem_zpowers_of_mem_of_pRegular c p H hc hp g hg
      rw [← N.inv_mem_iff, hN]
      rintro d ⟨n, rfl⟩
      have h2 := Subgroup.zpow_mem _ hy n
      have h3 : (g⁻¹ * c * g) ^ n = g⁻¹ * c ^ n * g⁻¹⁻¹ := by
        rw [← conj_zpow, inv_inv]
      rw [h3] at h2
      exact h2
    · intro hg
      have := (hN _).1 (N.inv_mem hg) c (Subgroup.mem_zpowers c)
      rw [inv_inv] at this
      exact hH this
  let f : N ⧸ H.subgroupOf N → MulAction.fixedBy (G ⧸ H) c :=
    Quotient.lift (fun n : N => ⟨((n : G) : G ⧸ H), (key n).2 n.2⟩) (by
      intro a b hab
      apply Subtype.ext
      have h : a⁻¹ * b ∈ H.subgroupOf N := QuotientGroup.leftRel_apply.1 hab
      exact QuotientGroup.eq.2 (by simpa [Subgroup.mem_subgroupOf] using h))
  have hf : Function.Bijective f := by
    constructor
    · intro x y
      induction x using QuotientGroup.induction_on with
      | H a =>
      induction y using QuotientGroup.induction_on with
      | H b =>
      intro hab
      have h : ((a : G) : G ⧸ H) = ((b : G) : G ⧸ H) := congrArg Subtype.val hab
      rw [QuotientGroup.eq] at h ⊢
      simpa [Subgroup.mem_subgroupOf] using h
    · rintro ⟨x, hx⟩
      induction x using QuotientGroup.induction_on with
      | H g => exact ⟨((⟨g, (key g).1 hx⟩ : N) : N ⧸ H.subgroupOf N), rfl⟩
  exact (Nat.card_eq_of_bijective f hf).symm

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CharacterTheory.CardFixedByQuotientEqRelIndexOfPRegularStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.card_fixedBy_quotient_eq_relIndex_normalizer_of_coprime : ∀ (G : Type) [Group G] [Finite G] (c : G) (p : ℕ) (H N : Subgroup G), Nat.Coprime (orderOf c) p → Subgroup.zpowers c ≤ H → (∀ h ∈ H, ∃ k : ℕ, h ^ p ^ k ∈ Subgroup.zpowers c) → (∀ g : G, g ∈ N ↔ ∀ d ∈ Subgroup.zpowers c, g * d * g⁻¹ ∈ Subgroup.zpowers c) → Nat.card (MulAction.fixedBy (G ⧸ H) c) = H.relIndex N := by
  first | exact @GlobalTheory.card_fixedBy_quotient_eq_relIndex_of_pRegular | exact GlobalTheory.card_fixedBy_quotient_eq_relIndex_of_pRegular | (intros; apply GlobalTheory.card_fixedBy_quotient_eq_relIndex_of_pRegular <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsCoprimeOrderOfPowPrimePow

section

@[expose] public section

namespace GlobalTheory

theorem exists_coprime_orderOf_pow_prime_pow (G : Type) [Group G] [Finite G] (x : G) (p : ℕ)
    (hp : p.Prime) : ∃ k : ℕ, Nat.Coprime (orderOf (x ^ p ^ k)) p := by
  obtain ⟨k, u, hu, h⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' p hp.ne_one
  refine ⟨k, ?_⟩
  have h1 : orderOf (x ^ p ^ k) ∣ u := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← pow_mul, ← h, pow_orderOf_eq_one]
  exact Nat.Coprime.coprime_dvd_left h1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hu).symm

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsCoprimeOrderOfPowPrimePowStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.exists_coprime_orderOf_pow_prime_pow' : ∀ (G : Type) [Group G] [Finite G] (x : G) (p : ℕ), p.Prime → ∃ k : ℕ, Nat.Coprime (orderOf (x ^ p ^ k)) p := by
  first | exact @GlobalTheory.exists_coprime_orderOf_pow_prime_pow | exact GlobalTheory.exists_coprime_orderOf_pow_prime_pow | (intros; apply GlobalTheory.exists_coprime_orderOf_pow_prime_pow <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsAbelianByPrimePowerNotDvdCardFixedBy

section

@[expose] public section

open GlobalTheory.BI
namespace GlobalTheory.BI

theorem exists_abelianByPrimePower_not_dvd_card_fixedBy₂ :
    ∀ (G : Type) [Group G] [Finite G] (x : G) (p : ℕ), p.Prime →
      ∃ H : Subgroup G, AbByP H ∧ ¬ p ∣ Nat.card (MulAction.fixedBy (G ⧸ H) x) := by
  intro G _ _ x p hp
  obtain ⟨k, hk⟩ := GlobalTheory.T.exists_coprime_orderOf_pow_prime_pow' G x p hp
  obtain ⟨H, hCH, hnorm, hpow, hidx⟩ := GlobalTheory.T.exists_subgroup_ge_normalizing_not_dvd_relIndex G (Subgroup.zpowers (x ^ p ^ k)) p hp
  have hN : ∀ g : G, g ∈ Subgroup.normalizer ((Subgroup.zpowers (x ^ p ^ k) : Subgroup G) : Set G) ↔
      ∀ d ∈ Subgroup.zpowers (x ^ p ^ k), g * d * g⁻¹ ∈ Subgroup.zpowers (x ^ p ^ k) := by
    intro g
    constructor
    · intro hg d hd
      exact (Subgroup.mem_normalizer_iff.1 hg d).1 hd
    · intro h
      exact Subgroup.mem_normalizer_fintype h
  refine ⟨H, ⟨p, hp, (Subgroup.zpowers (x ^ p ^ k)).subgroupOf H, ⟨?_⟩, ?_, ?_⟩, ?_⟩
  · intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hnorm g g.2 n hn
  · intro a ha b hb
    rw [Subgroup.mem_subgroupOf] at ha hb
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hm, ← hn]
    exact (Commute.refl _).zpow_zpow m n
  · intro g
    obtain ⟨j, hj⟩ := hpow g g.2
    exact ⟨j, by rw [Subgroup.mem_subgroupOf]; simpa using hj⟩
  · intro hd
    haveI : Finite (G ⧸ H) := inferInstance
    have h1 := GlobalTheory.T.card_fixedBy_quotient_eq_relIndex_normalizer_of_coprime G (x ^ p ^ k) p H _ hk hCH hpow hN
    have h2 := GlobalTheory.T.card_fixedBy_pow_prime_pow_modEq_card_fixedBy G (G ⧸ H) x p k hp
    apply hidx _ hN
    rw [← h1]
    exact (h2.dvd_iff dvd_rfl).2 hd

end GlobalTheory.BI
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsAbelianByPrimePowerNotDvdCardFixedByStatement

section

@[expose] public section

open GlobalTheory.BI

theorem _root_.GlobalTheory.T.exists_abelianByPrimePower_not_dvd_card_fixedBy : ∀ (G : Type) [Group G] [Finite G] (x : G) (p : ℕ), p.Prime → ∃ H : Subgroup G, AbByP H ∧ ¬ p ∣ Nat.card (MulAction.fixedBy (G ⧸ H) x) := by
  first | exact @GlobalTheory.BI.exists_abelianByPrimePower_not_dvd_card_fixedBy₂ | exact GlobalTheory.BI.exists_abelianByPrimePower_not_dvd_card_fixedBy₂ | (intros; apply GlobalTheory.BI.exists_abelianByPrimePower_not_dvd_card_fixedBy₂ <;> assumption)
end
end
