module

public import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionGLOneLeftRightUnitStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraProductCuspidalGLListPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCharacterHarishChandraProductCuspidalGLOfRegulStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInCharacterIsotypicPartSelfStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLDegRegStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularPairLiftToPrimePowerField
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShintaniLiftHarishChandraInductionEqTwistedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShintaniLiftKillsCuspDivisibleDegree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShintaniLiftKillsCuspOfDegreeNotDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedHarishChandraInductionGLIsTwistedClassFunStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedHarishChandraIsotypicPartStatement
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalGermOpenAffine

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory

theorem liftAll_deg_reg : ∀ (q l : ℕ) (L : List (ℕ × ℕ)), 2 ≤ q → l.Prime → (∀ p ∈ L, 0 < p.1 ∧ Reg q p.1 p.2) →
    deg (liftAll q l L) = deg L ∧ ∀ p ∈ liftAll q l L, 0 < p.1 ∧ Reg (q ^ l) p.1 p.2 := by
  intro q l L hq hl hL
  induction L with
  | nil => simp [liftAll, deg]
  | cons p L ih =>
    have hp := hL p (by simp)
    have ih' := ih (fun x hx => hL x (by simp [hx]))
    have hcons : liftAll q l (p :: L) = (if l ∣ p.1 then liftL q l [p]
        else [(p.1, p.2 * ∑ i ∈ Finset.range l, q ^ (p.1 * i))]) ++ liftAll q l L := by
      simp [liftAll, List.flatMap_cons]
    have hdegapp : ∀ A B : List (ℕ × ℕ), deg (A ++ B) = deg A + deg B := by intro A B; simp [deg]
    have hdegcons : deg (p :: L) = p.1 + deg L := by simp [deg]
    rw [hcons, hdegapp, hdegcons]
    by_cases h : l ∣ p.1
    · obtain ⟨h1, h2⟩ := GlobalTheory.T.deg_liftL_and_reg_pow q l [p] hq hl.pos (by
        intro x hx; rw [List.mem_singleton] at hx; subst hx; exact ⟨hp.1, h, hp.2⟩)
      rw [if_pos h]
      have hs : deg [p] = p.1 := by simp [deg]
      refine ⟨by rw [h1, hs, ih'.1], ?_⟩
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact h2 x hx
      · exact ih'.2 x hx
    · rw [if_neg h]
      have hr := (GlobalTheory.T.regular_pair_lift_to_prime_power_field q l p.1 p.2 hq hl hp.1 h hp.2).1
      have hs : deg [(p.1, p.2 * ∑ i ∈ Finset.range l, q ^ (p.1 * i))] = p.1 := by simp [deg]
      refine ⟨by rw [hs, ih'.1], ?_⟩
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · rw [List.mem_singleton] at hx; subst hx; exact ⟨hp.1, hr⟩
      · exact ih'.2 x hx

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftAllPreservesDegreeAndRegularity

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.lift_all_preserves_degree_and_regularity : ∀ (q l : ℕ) (L : List (ℕ × ℕ)), 2 ≤ q → l.Prime → (∀ p ∈ L, 0 < p.1 ∧ Reg q p.1 p.2) → deg (liftAll q l L) = deg L ∧ ∀ p ∈ liftAll q l L, 0 < p.1 ∧ Reg (q ^ l) p.1 p.2 := by
  first | (exact @GlobalTheory.liftAll_deg_reg) | (exact GlobalTheory.liftAll_deg_reg) | (intros; apply GlobalTheory.liftAll_deg_reg <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGermBaseChange

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

noncomputable section

namespace GlobalTheory.Shin.DescentAll

theorem mem_zpowers_of_prime {F F' : Type} [Field F] [Field F'] [Algebra F F'] [Finite F']
    (s : F' ≃ₐ[F] F') (hl : (Module.finrank F F').Prime) (hs : s ≠ 1) :
    ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s := by
  haveI : Finite F := Finite.of_injective _ (algebraMap F F').injective
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fintype F' := Fintype.ofFinite F'
  haveI : FiniteDimensional F F' := Module.Finite.of_finite
  haveI : IsGalois F F' := inferInstance
  haveI : Fact (Module.finrank F F').Prime := ⟨hl⟩
  have hc : Nat.card (F' ≃ₐ[F] F') = Module.finrank F F' := IsGalois.card_aut_eq_finrank F F'
  intro t
  rw [zpowers_eq_top_of_prime_card hc hs]
  exact Subgroup.mem_top t

theorem isCl_cusp (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (m k : ℕ) :
    IsCl (cusp θ m k) := by
  intro x y
  have h := ((GlobalTheory.T.twistedHarishChandraInductionGL_isTwistedClassFunction F (RingHom.id F) 0 0 m (fun _ => 1) (fun _ => 1)).2.2 (rootSum θ k)).1 x y
  simp only [cusp]
  rw [h]

end GlobalTheory.Shin.DescentAll

namespace GlobalTheory.Shin.DescentAll

theorem kills_liftAll : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'),
    (Module.finrank F F').Prime → s ≠ 1 → ∀ (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F')
    (θ : AlgebraicClosure F' →* ℂ), (∀ x y : AlgebraicClosure F', x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) →
    ∀ L : List (ℕ × ℕ), (∀ p ∈ L, 0 < p.1 ∧ Reg (Nat.card F) p.1 p.2) → ∀ n, n = deg L →
    Kills (shLift s (J (pullθ ι θ) L n)) (J θ (liftAll (Nat.card F) (Module.finrank F F') L) n) := by
  intro F F' _ _ _ _ s hl hs ι θ hθ
  haveI : Finite F := Finite.of_injective _ (algebraMap F F').injective
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fintype F' := Fintype.ofFinite F'
  haveI : FiniteDimensional F F' := Module.Finite.of_finite
  have hgen := mem_zpowers_of_prime s hl hs
  set q := Nat.card F with hqdef
  set l := Module.finrank F F' with hldef
  have hq2 : 2 ≤ q := by
    rw [hqdef, Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
  have hcard' : Nat.card F' = q ^ l := by
    rw [hqdef, hldef, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Module.card_eq_pow_finrank
  have hlist := GlobalTheory.T.harishChandraProductCuspidalGL_list_properties F' θ
  have happ : ∀ (A B : List (ℕ × ℕ)) (a b : ℕ), deg A = a → deg B = b →
      J θ (A ++ B) (a + b) = hc a b (J θ A a) (J θ B b) (a + b) := by
    intro A B a b ha hb
    subst ha hb
    exact hlist.2.1 A B _ rfl
  intro L
  induction L with
  | nil =>
    intro _ n hn
    obtain rfl : n = 0 := hn
    have hlift : liftAll q l ([] : List (ℕ × ℕ)) = [] := by simp [liftAll]
    rw [hlift]
    have h1 : shLift s (J (pullθ ι θ) [] 0) = J θ [] 0 := by
      funext δ
      have hδ : δ = 1 := by ext i j; exact i.elim0
      unfold shLift
      rw [dite_eq_left ⟨1, by rw [hδ]; exact isNorm_one s 0⟩]
      rfl
    rw [h1]
    exact GlobalTheory.T.isInCharacterIsotypicPart_self _ _ (GlobalTheory.T.isCharacter_harishChandraProductCuspidalGL_of_regular F' θ hθ [] (by simp) 0 rfl)
  | cons p L ih =>
    intro hL n hn
    have hp := hL p List.mem_cons_self
    have hLt : ∀ x ∈ L, 0 < x.1 ∧ Reg q x.1 x.2 := fun x hx => hL x (List.mem_cons_of_mem _ hx)
    have hdeg : deg (p :: L) = p.1 + deg L := by simp [deg]
    obtain rfl : n = p.1 + deg L := hn.trans hdeg
    set A : List (ℕ × ℕ) := (if l ∣ p.1 then liftL q l [p] else [(p.1, p.2 * ∑ i ∈ Finset.range l, q ^ (p.1 * i))])
      with hAdef
    have hsplit : liftAll q l (p :: L) = A ++ liftAll q l L := by simp [liftAll, hAdef]
    have hA1 : liftAll q l [p] = A := by simp [liftAll, hAdef]
    obtain ⟨hdA, hRA⟩ := GlobalTheory.T.lift_all_preserves_degree_and_regularity q l [p] hq2 hl (by simpa using hp)
    obtain ⟨hdB, hRB⟩ := GlobalTheory.T.lift_all_preserves_degree_and_regularity q l L hq2 hl hLt
    rw [hA1] at hdA hRA
    have hdA' : deg A = p.1 := by rw [hdA]; simp [deg]
    have hKA : Kills (shLift s (cusp (pullθ ι θ) p.1 p.2)) (J θ A p.1) := by
      by_cases h : l ∣ p.1
      · have := GlobalTheory.T.shintani_lift_kills_cusp_divisible_degree F F' s hl hs ι θ hθ p.1 p.2 hp.1 h hp.2
        rw [hAdef, if_pos h]
        simpa only [Prod.mk.eta] using this
      · rw [hAdef, if_neg h]
        have hu := GlobalTheory.T.shintani_lift_kills_cusp_of_degree_not_dvd F F' s hl hs ι θ hθ p.1 p.2 hp.1 h hp.2
        have hJ : J θ [(p.1, p.2 * ∑ i ∈ Finset.range l, q ^ (p.1 * i))] p.1 =
            cusp θ p.1 (p.2 * ∑ i ∈ Finset.range l, q ^ (p.1 * i)) := by
          rw [J_cons]
          exact (GlobalTheory.T.harishChandraInductionGL_one_left_right_unit F' p.1 _ (isCl_cusp F' θ _ _)).2
        rw [hJ]
        exact hu
    have hRA' : ∀ x ∈ A, 0 < x.1 ∧ Reg (Nat.card F') x.1 x.2 := by rw [hcard']; exact hRA
    have hRB' : ∀ x ∈ liftAll q l L, 0 < x.1 ∧ Reg (Nat.card F') x.1 x.2 := by rw [hcard']; exact hRB
    have hcharA := GlobalTheory.T.isCharacter_harishChandraProductCuspidalGL_of_regular F' θ hθ A hRA' p.1 hdA'.symm
    have hcharB := GlobalTheory.T.isCharacter_harishChandraProductCuspidalGL_of_regular F' θ hθ (liftAll q l L) hRB' (deg L) hdB.symm
    rw [J_cons, GlobalTheory.T.shintaniLift_harishChandraInduction_eq_twisted F F' s hgen p.1 (deg L) _ rfl _ _ (isCl_cusp F _ _ _)
      ((GlobalTheory.T.harishChandraProductCuspidalGL_list_properties F (pullθ ι θ)).1 L (deg L)), hsplit, happ A (liftAll q l L) p.1 (deg L) hdA' hdB]
    exact GlobalTheory.T.twistedHarishChandra_isotypic_part F' (s : F' →+* F') p.1 (deg L) _ rfl _ _ _ _ hcharA hcharB hKA (ih hLt (deg L) rfl)

end GlobalTheory.Shin.DescentAll
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShintaniLiftKillsProductOfCuspForms

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.shintani_lift_kills_product_of_cusp_forms : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (Module.finrank F F').Prime → s ≠ 1 → ∀ (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F') (θ : AlgebraicClosure F' →* ℂ), (∀ x y : AlgebraicClosure F', x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ L : List (ℕ × ℕ), (∀ p ∈ L, 0 < p.1 ∧ Reg (Nat.card F) p.1 p.2) → ∀ n, n = deg L → Kills (shLift s (J (pullθ ι θ) L n)) (J θ (liftAll (Nat.card F) (Module.finrank F F') L) n) := by
  first | (exact @GlobalTheory.Shin.DescentAll.kills_liftAll) | (exact GlobalTheory.Shin.DescentAll.kills_liftAll) | (intros; apply GlobalTheory.Shin.DescentAll.kills_liftAll  <;> assumption)
end
end
