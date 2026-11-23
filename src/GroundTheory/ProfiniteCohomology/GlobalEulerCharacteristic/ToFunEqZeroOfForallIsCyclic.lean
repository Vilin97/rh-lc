module

public import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.ArtinDefs
public import GroundTheory.GlobalFields.HerbrandQuotients.SUnitsPerm
public import Mathlib.Algebra.Group.Action.Sigma
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.SetTheory.Cardinal.Finite
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.OrbitInvariants
public import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.PermLattice
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.Additive
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.AdditiveSnake

-- Source module: GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.ArtinCount

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open MulAction

theorem natCard_subtype_eq_sum_natCard_fiber {α β : Type*} [Finite α] [DecidableEq β] (f : α → β)
    (t : Finset β) (P : α → Prop) (hP : ∀ a, P a ↔ f a ∈ t) :
    Nat.card {a // P a} = ∑ b ∈ t, Nat.card {a // f a = b} := by
  classical
  have := Fintype.ofFinite α
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := t)
    (fun a ha => (hP a).1 (Finset.mem_filter.1 ha).2)]
  refine Finset.sum_congr rfl fun b hb => ?_
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨And.right, fun h => ⟨(hP a).2 (h ▸ hb), h⟩⟩

variable {Γ : Type*} [Group Γ]

theorem card_mul_card_fixedBy_quotient [Finite Γ] (D : Subgroup Γ) (x : Γ) :
    Nat.card D * Nat.card (fixedBy (Γ ⧸ D) x) = Nat.card {y : Γ // y⁻¹ * x * y ∈ D} := by
  have hP : ∀ y : Γ, y⁻¹ * x * y ∈ D ↔
      (Subgroup.groupEquivQuotientProdSubgroup (s := D) y).1 ∈ fixedBy (Γ ⧸ D) x := by
    intro y
    change _ ↔ x • (y : Γ ⧸ D) = y
    rw [MulAction.Quotient.smul_mk, eq_comm, QuotientGroup.eq, smul_eq_mul, ← mul_assoc]
  let e : {y : Γ // y⁻¹ * x * y ∈ D} ≃ fixedBy (Γ ⧸ D) x × D :=
    (Subgroup.groupEquivQuotientProdSubgroup.subtypeEquiv hP).trans
      (Equiv.prodSubtypeFstEquivSubtypeProd (p := fun q => q ∈ fixedBy (Γ ⧸ D) x))
  rw [Nat.card_congr e, Nat.card_prod, mul_comm]

theorem exists_artin_relation [Finite Γ] :
    ∃ (s : Finset (Subgroup Γ)) (c : Subgroup Γ → ℤ), (∀ D ∈ s, IsCyclic D) ∧
      ∀ x : Γ, (Nat.card Γ : ℤ) = ∑ D ∈ s, c D * Nat.card (fixedBy (Γ ⧸ D) x) := by
  classical
  have := Fintype.ofFinite (Subgroup Γ)
  let π : Subgroup Γ → Γ → ℤ := fun D x => Nat.card (fixedBy (Γ ⧸ D) x)
  let f : Subgroup Γ → Γ → ℤ := fun C x => Nat.card {y : Γ // Subgroup.zpowers (y⁻¹ * x * y) = C}
  let V : Submodule ℤ (Γ → ℤ) :=
    Submodule.span ℤ (Set.range fun D : {D : Subgroup Γ // IsCyclic D} => π D)
  have hrec : ∀ (C : Subgroup Γ) (x : Γ),
      (Nat.card C : ℤ) * π C x = ∑ D ∈ Finset.univ.filter (· ≤ C), f D x := by
    intro C x
    simp only [π, f]
    rw [← Nat.cast_mul, card_mul_card_fixedBy_quotient,
      natCard_subtype_eq_sum_natCard_fiber (fun y => Subgroup.zpowers (y⁻¹ * x * y))
        (Finset.univ.filter (· ≤ C)) _ (fun y => by simp [Subgroup.zpowers_le])]
    push_cast
    rfl
  have htot : ∀ x : Γ, (Nat.card Γ : ℤ) = ∑ C, f C x := by
    intro x
    have h := natCard_subtype_eq_sum_natCard_fiber (fun y : Γ => Subgroup.zpowers (y⁻¹ * x * y))
      Finset.univ (fun _ => True) (by simp)
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => trivial))] at h
    simp only [f]
    exact_mod_cast h
  have hcyc : ∀ C : Subgroup Γ, ¬ IsCyclic C → f C = 0 := by
    intro C hC
    funext x
    simp only [f, Pi.zero_apply, Nat.cast_eq_zero]
    rw [Nat.card_eq_zero]
    left
    constructor
    rintro ⟨y, hy⟩
    exact hC (hy ▸ inferInstance)
  have hmem : ∀ C, f C ∈ V := by
    intro C
    refine WellFounded.induction (C := fun C => f C ∈ V) wellFounded_lt C ?_
    intro C ih
    by_cases hC : IsCyclic C
    · have hsplit : Finset.univ.filter (· ≤ C) = insert C (Finset.univ.filter (· < C)) := by
        ext D
        simp [le_iff_eq_or_lt]
      have hnot : C ∉ Finset.univ.filter (· < C) := by simp
      have heq : f C = (Nat.card C : ℤ) • π C - ∑ D ∈ Finset.univ.filter (· < C), f D := by
        funext x
        have h := hrec C x
        rw [hsplit, Finset.sum_insert hnot] at h
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
        linarith
      rw [heq]
      exact V.sub_mem (V.smul_mem _ (Submodule.subset_span ⟨⟨C, hC⟩, rfl⟩))
        (V.sum_mem fun D hD => ih D (Finset.mem_filter.1 hD).2)
    · rw [hcyc C hC]
      exact V.zero_mem
  have hconst : (fun _ : Γ => (Nat.card Γ : ℤ)) ∈ V := by
    have h : (fun _ : Γ => (Nat.card Γ : ℤ)) = ∑ C, f C := by
      funext x
      rw [Finset.sum_apply]
      exact htot x
    rw [h]
    exact V.sum_mem fun C _ => hmem C
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hconst
  refine ⟨Finset.univ.filter (fun D => IsCyclic D), fun D => if h : IsCyclic D then c ⟨D, h⟩ else 0,
    fun D hD => (Finset.mem_filter.1 hD).2, fun x => ?_⟩
  have h := congrFun hc x
  rw [Finset.sum_apply] at h
  rw [← h, Finset.sum_subtype (Finset.univ.filter (fun D => IsCyclic D))
    (p := fun D : Subgroup Γ => IsCyclic D) (by simp)]
  refine Finset.sum_congr rfl fun D _ => ?_
  rw [Pi.smul_apply, smul_eq_mul]
  show c D * π D x = (if h : IsCyclic (D : Subgroup Γ) then c ⟨D, h⟩ else 0) * π D x
  rw [dite_eq_left D.2]

end GroundTheory.ProfCoh
end
end

-- Source module: GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.ToFunEqZeroOfForallIsCyclic

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open MulAction Representation
open scoped TensorProduct

universe u

attribute [local instance] QuotientGroup.subsingleton_quotient_top

theorem natCard_fixedBy_sigma {G : Type*} [Group G] {J : Type*} [Fintype J] (Y : J → Type*)
    [∀ j, MulAction G (Y j)] [∀ j, Finite (Y j)] (x : G) :
    Nat.card (fixedBy (Σ j, Y j) x) = ∑ j, Nat.card (fixedBy (Y j) x) := by
  rw [← Nat.card_sigma]
  refine Nat.card_congr
    { toFun := fun p => ⟨p.1.1, p.1.2, ?_⟩
      invFun := fun p => ⟨⟨p.1, p.2.1⟩, ?_⟩
      left_inv := fun p => rfl
      right_inv := fun p => rfl }
  · obtain ⟨⟨j, y⟩, hp⟩ := p
    exact sigma_mk_injective hp
  · rw [mem_fixedBy, Sigma.smul_mk, (mem_fixedBy.1 p.2.2)]

namespace AdditiveFunction

variable {l : ℕ} {Γ : Type u} [Group Γ] (d : AdditiveFunction.{u} l Γ)

theorem toFun_piFamilyRep (J : Type u) [Fintype J] (V : J → Type u) [∀ j, AddCommGroup (V j)]
    [∀ j, Module (ZMod l) (V j)] [∀ j, Finite (V j)] (ρ : ∀ j, Representation (ZMod l) Γ (V j)) :
    d.toFun (∀ j, V j) (piFamilyRep V ρ) = ∑ j, d.toFun (V j) (ρ j) := by
  revert V
  refine Fintype.induction_empty_option (P := fun J _ => ∀ (V : J → Type u)
    [∀ j, AddCommGroup (V j)] [∀ j, Module (ZMod l) (V j)] [∀ j, Finite (V j)]
    (ρ : ∀ j, Representation (ZMod l) Γ (V j)),
    d.toFun (∀ j, V j) (piFamilyRep V ρ) = ∑ j, d.toFun (V j) (ρ j)) ?_ ?_ ?_ J
  · intro α β _ e h V _ _ _ ρ
    let : Fintype α := Fintype.ofEquiv β e.symm
    have h' := h (fun a => V (e a)) (fun a => ρ (e a))
    rw [← Equiv.sum_comp e, ← h']
    refine (d.toFun_congr _ _ (LinearEquiv.piCongrLeft (ZMod l) V e) fun γ x => ?_).symm
    funext b
    obtain ⟨a, rfl⟩ := e.surjective b
    change Equiv.piCongrLeft V e _ (e a) = ρ (e a) γ (Equiv.piCongrLeft V e x (e a))
    rw [Equiv.piCongrLeft_apply_apply, Equiv.piCongrLeft_apply_apply]
    rfl
  · intro V _ _ _ ρ
    rw [d.toFun_eq_zero_of_subsingleton]
    simp
  · intro α _ ih V _ _ _ ρ
    rw [Fintype.sum_option, ← ih (fun a => V (some a)) (fun a => ρ (some a)), ← d.toFun_prod]
    exact d.toFun_congr _ _ (LinearEquiv.piOptionEquivProd (ZMod l)) fun γ x => rfl

theorem tensorRep_funPermRep [Fact l.Prime] {N : Type u} [AddCommGroup N] [Module (ZMod l) N]
    [Finite N] (σ : Representation (ZMod l) Γ N) (Y : Type u) [MulAction Γ Y] [Finite Y] :
    (d.tensorRep σ).toFun (Y → ZMod l) (GroundTheory.Global.funPermRep (ZMod l) Γ Y) =
      d.toFun (Y → N) (funRep Y σ) := by
  classical
  have := Fintype.ofFinite Y
  have := finite_tensorProduct_zmod l (Y → ZMod l) N
  rw [tensorRep_apply]
  exact d.toFun_congr _ _ funTensorEquiv fun γ t => funext fun y => funTensorEquiv_tprod σ γ t y

theorem toFun_funRep_sigma {N : Type u} [AddCommGroup N] [Module (ZMod l) N] [Finite N]
    (σ : Representation (ZMod l) Γ N) {J : Type u} [Fintype J] (Y : J → Type u)
    [∀ j, MulAction Γ (Y j)] [∀ j, Finite (Y j)] :
    d.toFun ((Σ j, Y j) → N) (funRep (Σ j, Y j) σ) = ∑ j, d.toFun (Y j → N) (funRep (Y j) σ) := by
  rw [← d.toFun_piFamilyRep J (fun j => Y j → N) (fun j => funRep (Y j) σ)]
  exact d.toFun_congr _ _ (LinearEquiv.piCurry (ZMod l) fun j (_ : Y j) => N) fun γ F => rfl

theorem toFun_funRep_quotient_top {N : Type u} [AddCommGroup N] [Module (ZMod l) N] [Finite N]
    (σ : Representation (ZMod l) Γ N) :
    d.toFun ((Γ ⧸ (⊤ : Subgroup Γ)) → N) (funRep (Γ ⧸ (⊤ : Subgroup Γ)) σ) = d.toFun N σ := by
  let e : ((Γ ⧸ (⊤ : Subgroup Γ)) → N) ≃ₗ[ZMod l] N :=
    { toFun := fun F => F ((1 : Γ) : Γ ⧸ (⊤ : Subgroup Γ))
      invFun := fun n _ => n
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun F => funext fun q => congrArg F (Subsingleton.elim _ _)
      right_inv := fun _ => rfl }
  refine d.toFun_congr _ _ e fun γ F => ?_
  change σ γ (F (γ⁻¹ • _)) = σ γ (F _)
  rw [Subsingleton.elim (γ⁻¹ • ((1 : Γ) : Γ ⧸ (⊤ : Subgroup Γ))) _]

end AdditiveFunction

theorem natCard_fixedBy_quotient_top {Γ : Type*} [Group Γ] (x : Γ) :
    Nat.card (fixedBy (Γ ⧸ (⊤ : Subgroup Γ)) x) = 1 :=
  Nat.card_eq_one_iff_unique.2 ⟨inferInstance,
    ⟨⟨((1 : Γ) : Γ ⧸ (⊤ : Subgroup Γ)), Subsingleton.elim _ _⟩⟩⟩

namespace AdditiveFunction

variable {l : ℕ} {Γ : Type u} [Group Γ] (d : AdditiveFunction.{u} l Γ)

theorem card_mul_toFun_eq_sum [Fact l.Prime] [Finite Γ] (s : Finset (Subgroup Γ)) (c : Subgroup Γ → ℤ)
    (hc : ∀ x : Γ, (Nat.card Γ : ℤ) = ∑ D ∈ s, c D * Nat.card (fixedBy (Γ ⧸ D) x))
    {N : Type u} [AddCommGroup N] [Module (ZMod l) N] [Finite N] (σ : Representation (ZMod l) Γ N) :
    (Nat.card Γ : ℤ) * d.toFun N σ =
      ∑ D ∈ s, c D * d.toFun ((Γ ⧸ D) → N) (funRep (Γ ⧸ D) σ) := by
  classical
  let Jp := Σ D : s, Fin (c D).toNat
  let Jn := Fin (Nat.card Γ) ⊕ Σ D : s, Fin (-c D).toNat
  let Hp : Jp → Subgroup Γ := fun j => j.1
  let Hn : Jn → Subgroup Γ := Sum.elim (fun _ => ⊤) (fun j => j.1)

  have hsides : ∀ φ : Subgroup Γ → ℤ,
      (∑ j : Jp, φ (Hp j)) = ∑ D : s, ((c D).toNat : ℤ) * φ D ∧
      (∑ j : Jn, φ (Hn j)) = Nat.card Γ * φ ⊤ + ∑ D : s, ((-c D).toNat : ℤ) * φ D := by
    intro φ
    constructor
    · rw [Fintype.sum_sigma]
      simp [Hp]
    · rw [Fintype.sum_sum_type, Fintype.sum_sigma]
      simp [Hn]

  have hdiff : ∀ φ : Subgroup Γ → ℤ,
      (∑ D : s, ((c D).toNat : ℤ) * φ D) - ∑ D : s, ((-c D).toNat : ℤ) * φ D = ∑ D ∈ s, c D * φ D := by
    intro φ
    rw [← Finset.sum_sub_distrib, ← Finset.sum_coe_sort s]
    refine Finset.sum_congr rfl fun D _ => ?_
    rw [← sub_mul, Int.toNat_sub_toNat_neg]

  have hfix : ∀ x : Γ, Nat.card (fixedBy (Σ j : Jp, Γ ⧸ Hp j) x) =
      Nat.card (fixedBy (Σ j : Jn, Γ ⧸ Hn j) x) := by
    intro x
    rw [natCard_fixedBy_sigma, natCard_fixedBy_sigma]
    have h1 := (hsides fun D => Nat.card (fixedBy (Γ ⧸ D) x)).1
    have h2 := (hsides fun D => Nat.card (fixedBy (Γ ⧸ D) x)).2
    have h3 := hdiff fun D => Nat.card (fixedBy (Γ ⧸ D) x)
    rw [natCard_fixedBy_quotient_top, Nat.cast_one, mul_one] at h2
    have h4 := hc x
    zify
    linarith
  have hP := (d.tensorRep σ).toFun_funPermRep_eq_of_card_fixedBy_eq hfix
  rw [tensorRep_funPermRep, tensorRep_funPermRep, toFun_funRep_sigma, toFun_funRep_sigma] at hP
  have h1 := (hsides fun D => d.toFun ((Γ ⧸ D) → N) (funRep (Γ ⧸ D) σ)).1
  have h2 := (hsides fun D => d.toFun ((Γ ⧸ D) → N) (funRep (Γ ⧸ D) σ)).2
  have h3 := hdiff fun D => d.toFun ((Γ ⧸ D) → N) (funRep (Γ ⧸ D) σ)
  rw [toFun_funRep_quotient_top] at h2
  linarith

theorem toFun_eq_zero_of_forall_isCyclic [Fact l.Prime] [Finite Γ] {N : Type u} [AddCommGroup N]
    [Module (ZMod l) N] [Finite N] (σ : Representation (ZMod l) Γ N)
    (h : ∀ D : Subgroup Γ, IsCyclic D → d.toFun ((Γ ⧸ D) → N) (funRep (Γ ⧸ D) σ) = 0) :
    d.toFun N σ = 0 := by
  obtain ⟨s, c, hs, hc⟩ := exists_artin_relation (Γ := Γ)
  have key := d.card_mul_toFun_eq_sum s c hc σ
  rw [Finset.sum_eq_zero fun D hD => by rw [h D (hs D hD), mul_zero]] at key
  have hm : (Nat.card Γ : ℤ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  exact (mul_eq_zero.1 key).resolve_left hm

end AdditiveFunction

end GroundTheory.ProfCoh
end
end
