module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharTraceMulIdempotent
public import Mathlib.RepresentationTheory.Irreducible
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.CharacterTheory.SumConjIdempotentEqCardSmul

section

@[expose] public section

namespace GlobalTheory

theorem sum_conj_idempotent_eq_card_smul (L : Type) [Field L] (G : Type) [Group G] [Fintype G]
    (V : Type) [AddCommGroup V] [Module L V] (ρ : Representation L G V) (T : Subgroup G)
    (e : Module.End L V) (hirr : ρ.IsIrreducible) (he0 : e ≠ 0) (hee : e * e = e)
    (hT : ∀ t ∈ T, ρ t * e = e * ρ t) (hoff : ∀ g ∉ T, e * ρ g * e = 0) :
    ∑ x : G, ρ x * e * ρ x⁻¹ = (Nat.card T : L) • (1 : Module.End L V) := by
  classical
  set E : Module.End L V := ∑ x : G, ρ x * e * ρ x⁻¹ with hE
  have hcomm : ∀ g : G, ρ g * E = E * ρ g := by
    intro g
    rw [hE, Finset.mul_sum, Finset.sum_mul]
    refine Fintype.sum_equiv (Equiv.mulLeft g) _ _ ?_
    intro x
    have h1 : ρ (g * x)⁻¹ * ρ g = ρ x⁻¹ := by
      rw [← map_mul]; congr 1; group
    simp only [Equiv.coe_mulLeft]
    rw [mul_assoc (ρ (g * x) * e), h1, map_mul]
    simp only [mul_assoc]
  have hEe : E * e = (Nat.card T : L) • e := by
    rw [hE, Finset.sum_mul]
    have h2 : ∀ x : G, ρ x * e * ρ x⁻¹ * e = if x ∈ T then e else 0 := by
      intro x
      split_ifs with hx
      · have h3 : ρ x * ρ x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
        rw [hT x hx, mul_assoc e, h3, mul_one, hee]
      · have h4 := hoff x⁻¹ (fun h => hx (by simpa using T.inv_mem h))
        calc ρ x * e * ρ x⁻¹ * e = ρ x * (e * ρ x⁻¹ * e) := by simp only [mul_assoc]
          _ = 0 := by rw [h4, mul_zero]
    rw [Finset.sum_congr rfl (fun x _ => h2 x), ← Finset.sum_filter, Finset.sum_const,
      Nat.cast_smul_eq_nsmul, Nat.card_eq_fintype_card, Fintype.card_subtype]
  set D : Module.End L V := E - (Nat.card T : L) • (1 : Module.End L V) with hD
  have hDc : ∀ g : G, ρ g * D = D * ρ g := by
    intro g
    rw [hD, mul_sub, sub_mul, hcomm, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
  have hDe : D * e = 0 := by
    rw [hD, sub_mul, hEe, smul_mul_assoc, one_mul, sub_self]
  let K : Subrepresentation ρ :=
    { toSubmodule := LinearMap.ker D
      apply_mem_toSubmodule := by
        intro g v hv
        rw [LinearMap.mem_ker] at hv ⊢
        have := congrArg (fun f : Module.End L V => f v) (hDc g)
        simp only [Module.End.mul_apply] at this
        rw [← this, hv, map_zero] }
  have := hirr
  rcases IsSimpleOrder.eq_bot_or_eq_top K with h | h
  · exfalso
    apply he0
    ext v
    have hv : e v ∈ K.toSubmodule := by
      change e v ∈ LinearMap.ker D
      rw [LinearMap.mem_ker, ← Module.End.mul_apply, hDe]; rfl
    rw [h] at hv
    exact hv
  · have hk : LinearMap.ker D = ⊤ := by
      change K.toSubmodule = ⊤
      rw [h]; rfl
    exact sub_eq_zero.mp (LinearMap.ker_eq_top.mp hk)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharacterEqInducedOfImprimitivitySystem

section

@[expose] public section

open GlobalTheory.BI

namespace GlobalTheory.BI

theorem character_eq_ind_of_imprimitive :
    ∀ (L : Type) [Field L] [CharZero L] (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module L V] [FiniteDimensional L V] (ρ : Representation L G V) (T : Subgroup G) (e : Module.End L V), ρ.IsIrreducible → e ≠ 0 → e * e = e → (∀ t ∈ T, ρ t * e = e * ρ t) → (∀ g ∉ T, e * ρ g * e = 0) → ∃ ψ : T → L, IsChar L L ψ ∧ ∀ g, ρ.character g = ind T ψ g := by
  intro L _ _ G _ _ V _ _ _ ρ T e hirr he0 hee hT hoff
  classical
  have : Fintype G := Fintype.ofFinite G
  refine ⟨fun t => LinearMap.trace L V (ρ t * e), ?_, ?_⟩
  · exact isChar_trace_mul_idempotent L T V (ρ.comp T.subtype) e hee (fun t => hT t t.2)
  · intro g
    have hsum := GlobalTheory.sum_conj_idempotent_eq_card_smul L G V ρ T e hirr he0 hee hT hoff
    have hcard : (Nat.card T : L) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := T)).ne'
    have hkey : ∀ h : G, LinearMap.trace L V (ρ h * e)
        = ext0 T (fun t : T => LinearMap.trace L V (ρ t * e)) h := by
      intro h
      unfold ext0
      split_ifs with hh
      · rfl
      · have h2 : ρ h * e = ρ h * e * e := by rw [mul_assoc, hee]
        rw [h2, LinearMap.trace_mul_comm, ← mul_assoc, hoff h hh, map_zero]
    have hterm : ∀ x : G, LinearMap.trace L V (ρ g * (ρ x * e * ρ x⁻¹))
        = LinearMap.trace L V (ρ (x⁻¹ * g * x) * e) := by
      intro x
      rw [show ρ g * (ρ x * e * ρ x⁻¹) = (ρ g * ρ x * e) * ρ x⁻¹ by simp only [mul_assoc],
        LinearMap.trace_mul_comm]
      simp only [map_mul, mul_assoc]
    have htr : (Nat.card T : L) * LinearMap.trace L V (ρ g)
        = ∑ x : G, LinearMap.trace L V (ρ (x⁻¹ * g * x) * e) := by
      have h3 : (Nat.card T : L) * LinearMap.trace L V (ρ g)
          = LinearMap.trace L V (ρ g * ∑ x : G, ρ x * e * ρ x⁻¹) := by
        rw [hsum, mul_smul_comm, mul_one, map_smul, smul_eq_mul]

      rw [h3, Finset.mul_sum, map_sum]
      exact Finset.sum_congr rfl (fun x _ => hterm x)
    rw [Representation.character, ind, finsum_eq_sum_of_fintype]
    simp only [← hkey]
    rw [← htr, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

end GlobalTheory.BI
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharacterEqInducedOfImprimitivitySystemStatement

section

@[expose] public section

open GlobalTheory.BI

theorem _root_.GlobalTheory.T.character_eq_induced_of_imprimitivity_system : ∀ (L : Type) [Field L] [CharZero L] (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module L V] [FiniteDimensional L V] (ρ : Representation L G V) (T : Subgroup G) (e : Module.End L V), ρ.IsIrreducible → e ≠ 0 → e * e = e → (∀ t ∈ T, ρ t * e = e * ρ t) → (∀ g ∉ T, e * ρ g * e = 0) → ∃ ψ : T → L, IsChar L L ψ ∧ ∀ g, ρ.character g = ind T ψ g := by
  first | exact @GlobalTheory.BI.character_eq_ind_of_imprimitive | exact GlobalTheory.BI.character_eq_ind_of_imprimitive | (intros; apply GlobalTheory.BI.character_eq_ind_of_imprimitive <;> assumption)
end
end
