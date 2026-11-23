module

public import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockParabolicSubgroupLeviProjectionStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotypicPartExteriorProductInflatedSurjectionStatement
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInCharacterIsotypicPartTwistedInduction

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.IndIso

theorem sum_dite_mem {G M : Type} [Group G] [Fintype G] [AddCommMonoid M] (H : Subgroup G)
    (f : H → M) : ∑ z : G, (if h : z ∈ H then f ⟨z, h⟩ else 0) = ∑ h : H, f h := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun z => z ∈ H)]
  have h2 : ∑ i : {x // ¬ x ∈ H}, (if h : (i : G) ∈ H then f ⟨i, h⟩ else 0) = 0 :=
    Finset.sum_eq_zero fun i _ => dif_neg i.2
  rw [h2, add_zero]
  exact Fintype.sum_congr _ _ fun i => dif_pos i.2

theorem star_ext_zero {G : Type} [Group G] (H : Subgroup G) (c : H → ℂ) (z : G) :
    star (ext0 H c z) = ext0 H (fun h => star (c h)) z := by
  unfold ext0; split_ifs <;> simp

theorem reidx {G M : Type} [Group G] [Fintype G] [AddCommMonoid M] [Module ℂ M] (H : Subgroup G)
    (a b : G) (c : H → ℂ) (T : G → M) :
    ∑ x : G, ext0 H c (a * x * b) • T x = ∑ h : H, c h • T (a⁻¹ * h * b⁻¹) := by
  rw [Fintype.sum_equiv ((Equiv.mulLeft a).trans (Equiv.mulRight b)) _
    (fun z => ext0 H c z • T (a⁻¹ * z * b⁻¹)) (fun x => by simp [mul_assoc])]
  rw [← sum_dite_mem H (fun h => c h • T (a⁻¹ * h * b⁻¹))]
  refine Fintype.sum_congr _ _ fun z => ?_
  unfold ext0; split_ifs <;> simp

end GlobalTheory.Shin.IndIso

namespace GlobalTheory.Shin.IndIso

theorem kills_ind : ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G) (τ : G → G) (φ Y : H → ℂ), Kills φ Y →
    Kills (fun x => (Nat.card H : ℂ)⁻¹ * ∑ᶠ y : G, ext0 H φ (y⁻¹ * x * τ y)) (ind H Y) := by
  intro G _ _ H τ φ Y hK V _ _ _ ρ hρ
  letI : Fintype G := Fintype.ofFinite G
  have hHc : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hGc : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'

  have hres : ∑ᶠ h : H, star (Y h) * LinearMap.trace ℂ V ((ρ.comp H.subtype) h) = 0 := by
    rw [finsum_eq_sum_of_fintype]
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
    simp only [ind, finsum_eq_sum_of_fintype, star_mul', star_inv₀, star_natCast, star_sum, star_ext_zero] at hρ
    simp only [mul_assoc, ← Finset.mul_sum] at hρ
    have hρ' := (mul_eq_zero.mp hρ).resolve_left (inv_ne_zero hHc)
    have trc : ∀ g x : G, LinearMap.trace ℂ V (ρ (g * (x * g⁻¹))) = LinearMap.trace ℂ V (ρ x) := by
      intro g x
      rw [map_mul ρ, map_mul ρ, LinearMap.trace_mul_comm, mul_assoc, ← map_mul ρ, ← map_mul ρ]
      simp
    simp only [Finset.sum_mul] at hρ'
    rw [Finset.sum_comm] at hρ'
    have key : ∀ g : G, ∑ x : G, ext0 H (fun h => star (Y h)) (g⁻¹ * (x * g)) * LinearMap.trace ℂ V (ρ x)
        = ∑ h : H, star (Y h) * LinearMap.trace ℂ V (ρ h) := by
      intro g
      have := reidx (M := ℂ) H g⁻¹ g (fun h => star (Y h)) (fun x => LinearMap.trace ℂ V (ρ x))
      simp only [smul_eq_mul, inv_inv, mul_assoc] at this
      rw [this]
      exact Fintype.sum_congr _ _ fun h => by rw [trc]
    simp only [key, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hρ'
    rw [← Nat.card_eq_fintype_card] at hρ'
    exact (mul_eq_zero.mp hρ').resolve_left hGc
  have hk := hK V (ρ.comp H.subtype) hres
  rw [finsum_eq_sum_of_fintype] at hk
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype] at hk

  rw [finsum_eq_sum_of_fintype]
  simp only [finsum_eq_sum_of_fintype, star_mul', star_inv₀, star_natCast, star_sum, star_ext_zero, mul_smul,
    Finset.sum_smul]
  rw [← Finset.smul_sum, Finset.sum_comm]
  have key2 : ∀ y : G, ∑ x : G, ext0 H (fun h => star (φ h)) (y⁻¹ * x * τ y) • ρ x = 0 := by
    intro y
    rw [reidx H y⁻¹ (τ y) (fun h => star (φ h)) (fun x => ρ x)]
    simp only [inv_inv, map_mul]
    have : ∑ h : H, star (φ h) • (ρ y * ρ h * ρ (τ y)⁻¹) = ρ y * (∑ h : H, star (φ h) • ρ h) * ρ (τ y)⁻¹ := by
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Fintype.sum_congr _ _ fun h => ?_
      rw [mul_smul_comm, smul_mul_assoc]
    rw [this, hk, mul_zero, zero_mul]
  simp only [key2, Finset.sum_const_zero, smul_zero]

end GlobalTheory.Shin.IndIso
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInCharacterIsotypicPartTwistedInductionStatement

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.isInCharacterIsotypicPart_twistedInduction : ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G) (τ : G → G) (φ Y : H → ℂ), Kills φ Y → Kills (fun x => (Nat.card H : ℂ)⁻¹ * ∑ᶠ y : G, ext0 H φ (y⁻¹ * x * τ y)) (ind H Y) := by
  first | (exact @GlobalTheory.Shin.IndIso.kills_ind) | (exact GlobalTheory.Shin.IndIso.kills_ind) | (intros; apply GlobalTheory.Shin.IndIso.kills_ind  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedHarishChandraIsotypicPart

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

noncomputable section

namespace GlobalTheory.Shin.HcIso

theorem kills_hcTw : ∀ (F : Type) [Field F] [Finite F], ∀ (t : F →+* F) (a b n : ℕ), n = a + b →
    ∀ (α A : GL (Fin a) F → ℂ) (β B : GL (Fin b) F → ℂ), IsChar ℂ ℂ A → IsChar ℂ ℂ B → Kills α A →
      Kills β B → Kills (hcTw t a b α β n) (hc a b A B n) := by
  intro F _ _ t a b n hn α A β B hA hB hαA hβB
  obtain ⟨H, π, hmem, hsurj, hπ, -, -⟩ := GlobalTheory.T.exists_blockParabolic_subgroup_levi_projection F a b n hn
  have hcard : (Nat.card {p : GL (Fin n) F // InPar a p} : ℂ) = (Nat.card H : ℂ) := by
    congr 1
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => (hmem x).symm)
  have hE : ∀ (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ) (z : GL (Fin n) F),
      (if InPar a z then α (tlG a z) * β (brG a b z) else 0) =
        ext0 H (fun p => α (π p).1 * β (π p).2) z := by
    intro α β z
    unfold ext0
    by_cases h : InPar a z
    · have hz : z ∈ H := (hmem z).2 h
      rw [if_pos h, dite_eq_left hz]
      show _ = α (π ⟨z, hz⟩).1 * β (π ⟨z, hz⟩).2
      rw [hπ]
    · have hz : z ∉ H := fun hz => h ((hmem z).1 hz)
      rw [if_neg h, dite_eq_right hz]
  have h1 : hcTw t a b α β n = fun x => (Nat.card H : ℂ)⁻¹ *
      ∑ᶠ y : GL (Fin n) F, ext0 H (fun p => α (π p).1 * β (π p).2) (y⁻¹ * x * (fun y => gal t n y) y) := by
    funext x
    unfold hcTw
    rw [hcard]
    congr 1
    congr 1
    funext y
    exact hE α β _
  have hid : ∀ y : GL (Fin n) F, gal (RingHom.id F) n y = y := by
    intro y
    ext i j
    simp [gal]
  have h2 : hc a b A B n = ind H (fun p => A (π p).1 * B (π p).2) := by
    funext x
    unfold hc hcTw ind
    rw [hcard]
    congr 1
    congr 1
    funext y
    rw [hid, hE]
  have hk := GlobalTheory.T.isotypicPart_exteriorProduct_inflated_surjection H (GL (Fin a) F) (GL (Fin b) F) π hsurj α A β B hA hB hαA hβB
  rw [h1, h2]
  exact GlobalTheory.T.isInCharacterIsotypicPart_twistedInduction (GL (Fin n) F) H (fun y => gal t n y) _ _ hk

end GlobalTheory.Shin.HcIso
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedHarishChandraIsotypicPartStatement

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.twistedHarishChandra_isotypic_part : ∀ (F : Type) [Field F] [Finite F], ∀ (t : F →+* F) (a b n : ℕ), n = a + b → ∀ (α A : GL (Fin a) F → ℂ) (β B : GL (Fin b) F → ℂ), IsChar ℂ ℂ A → IsChar ℂ ℂ B → Kills α A → Kills β B → Kills (hcTw t a b α β n) (hc a b A B n) := by
  first | (exact @GlobalTheory.Shin.HcIso.kills_hcTw) | (exact GlobalTheory.Shin.HcIso.kills_hcTw) | (intros; apply GlobalTheory.Shin.HcIso.kills_hcTw <;> assumption)
end
end
