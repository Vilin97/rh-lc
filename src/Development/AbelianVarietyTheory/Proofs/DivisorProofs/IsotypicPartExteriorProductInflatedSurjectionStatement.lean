module

public import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharactersMulComapConjIndLinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInCharacterIsotypicPartSelfStatement
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInCharacterIsotypicPartIffConvolution

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

noncomputable section

namespace GlobalTheory.Shin

theorem isChar_conj_eq {G : Type} [Group G] {Y : G → ℂ} (hY : IsChar ℂ ℂ Y) (g z : G) :
    Y (z * g * z⁻¹) = Y g := by
  obtain ⟨n, ρ, h⟩ := hY
  rw [h, h, Representation.char_conj]

theorem conv_op_eq {G V : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (Y h : G → ℂ) :
    ∑ x, star (∑ y, Y y * h (y⁻¹ * x)) • ρ x =
      (∑ y, star (Y y) • ρ y) * (∑ z, star (h z) • ρ z) := by
  rw [Finset.sum_mul_sum]
  simp_rw [star_sum, star_mul', Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Equiv.sum_comp (Equiv.mulLeft y)]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp [map_mul, smul_mul_smul_comm, smul_smul, mul_comm]

def convL {G : Type} [Group G] [Fintype G] (Y : G → ℂ) : (G → ℂ) →ₗ[ℂ] (G → ℂ) :=
  ∑ g, star (Y g) • LinearMap.funLeft ℂ ℂ (fun z => g * z)

theorem convL_apply {G : Type} [Group G] [Fintype G] (Y : G → ℂ) (a : G → ℂ) (z : G) :
    convL Y a z = ∑ g, star (Y g) * a (g * z) := by
  simp [convL, LinearMap.funLeft, Finset.sum_apply]

def regKer {G : Type} [Group G] [Fintype G] (Y : G → ℂ) :
    Representation ℂ G (LinearMap.ker (convL Y)) where
  toFun g := (LinearMap.funLeft ℂ ℂ (fun z => z * g)).restrict (p := LinearMap.ker (convL Y))
      (q := LinearMap.ker (convL Y)) (by
        intro a ha
        rw [LinearMap.mem_ker] at ha ⊢
        funext z
        have := congrFun ha (z * g)
        simp only [convL_apply, Pi.zero_apply] at this ⊢
        simpa [LinearMap.funLeft, mul_assoc] using this)
  map_one' := by ext a z; simp [LinearMap.funLeft]
  map_mul' g h := by ext a z; simp [LinearMap.funLeft, mul_assoc]

theorem regKer_apply {G : Type} [Group G] [Fintype G] (Y : G → ℂ) (g : G) (a : LinearMap.ker (convL Y))
    (z : G) : ((regKer Y g a : LinearMap.ker (convL Y)) : G → ℂ) z = (a : G → ℂ) (z * g) := rfl

theorem kills_iff_conv : ∀ (G : Type) [Group G] [Finite G] (φ Y : G → ℂ), IsChar ℂ ℂ Y →
    (Kills φ Y ↔ ∃ h : G → ℂ, ∀ x, φ x = ∑ᶠ y, Y y * h (y⁻¹ * x)) := by
  intro G _ _ φ Y hY
  have := Fintype.ofFinite G
  constructor
  · intro hK
    set K := LinearMap.ker (convL Y)

    have hT : ∑ g, star (Y g) • regKer Y g = 0 := by
      ext a z
      have ha := congrFun (LinearMap.mem_ker.1 a.2) z
      rw [convL_apply, Pi.zero_apply] at ha
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul,
        Finset.sum_apply, Pi.smul_apply, regKer_apply, smul_eq_mul, LinearMap.zero_apply,
        Submodule.coe_zero, Pi.zero_apply]
      rw [← ha, ← Equiv.sum_comp (MulAut.conj z⁻¹).toEquiv]
      refine Finset.sum_congr rfl fun g _ => ?_
      have hc := isChar_conj_eq hY g z⁻¹
      simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, inv_inv] at hc ⊢
      rw [hc]
      congr 2
      group
    have hK' := hK K (regKer Y) (by
      rw [finsum_eq_sum_of_fintype]
      have := congrArg (LinearMap.trace ℂ K) hT

      simpa [map_sum, smul_eq_mul] using this)
    rw [finsum_eq_sum_of_fintype] at hK'

    let ℓ : Module.Dual ℂ (G → ℂ) := ∑ x, star (φ x) • (LinearMap.proj x : (G → ℂ) →ₗ[ℂ] ℂ)
    have hℓ : ∀ a, ℓ a = ∑ x, star (φ x) * a x := fun a => by simp [ℓ]
    have hmem : ℓ ∈ K.dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro a ha
      have := congrFun (congrArg Subtype.val (LinearMap.congr_fun hK' ⟨a, ha⟩)) 1
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul,
        Finset.sum_apply, Pi.smul_apply, regKer_apply, smul_eq_mul, LinearMap.zero_apply,
        Submodule.coe_zero, Pi.zero_apply] at this
      have e : ∀ x, ((regKer Y x ⟨a, ha⟩ : LinearMap.ker (convL Y)) : G → ℂ) 1 = a x := fun x => by
        show a (1 * x) = a x
        rw [one_mul]
      simp only [e] at this
      rw [hℓ, this]
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hmem
    obtain ⟨μ, hμ⟩ := hmem
    refine ⟨fun w => star (μ (Pi.single w 1)), fun x => ?_⟩
    have hδ : convL Y (Pi.single x 1) = ∑ g, star (Y g) • Pi.single (g⁻¹ * x) 1 := by
      funext z
      rw [convL_apply, Finset.sum_apply]
      refine Finset.sum_congr rfl fun g _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul]
      congr 1
      simp only [Pi.single_apply, eq_inv_mul_iff_mul_eq]
    have h1 := LinearMap.congr_fun hμ (Pi.single x 1)

    rw [LinearMap.dualMap_apply, hδ, map_sum, hℓ] at h1
    simp only [map_smul, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
    rw [finsum_eq_sum_of_fintype]
    have h2 := congrArg star h1
    simp only [star_sum, star_mul', star_star] at h2
    rw [← h2]
  · rintro ⟨h, hφ⟩ V _ _ _ ρ hV
    have hY0 := GlobalTheory.T.isInCharacterIsotypicPart_self G Y hY V ρ hV
    rw [finsum_eq_sum_of_fintype] at hY0 ⊢
    simp_rw [hφ, finsum_eq_sum_of_fintype]
    rw [conv_op_eq, hY0, zero_mul]

end GlobalTheory.Shin
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInCharacterIsotypicPartIffConvolutionStatement

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.isInCharacterIsotypicPart_iff_convolution : ∀ (G : Type) [Group G] [Finite G] (φ Y : G → ℂ), IsChar ℂ ℂ Y → (Kills φ Y ↔ ∃ h : G → ℂ, ∀ x, φ x = ∑ᶠ y, Y y * h (y⁻¹ * x)) := by
  first | (exact @GlobalTheory.Shin.kills_iff_conv) | (exact GlobalTheory.Shin.kills_iff_conv) | (intros; apply GlobalTheory.Shin.kills_iff_conv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotypicPartExteriorProductInflatedSurjection

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem kills_prod_comp_surj : ∀ (P G₁ G₂ : Type) [Group P] [Finite P] [Group G₁] [Group G₂] (π : P →* G₁ × G₂), Function.Surjective π → ∀ (φ₁ Y₁ : G₁ → ℂ) (φ₂ Y₂ : G₂ → ℂ), IsChar ℂ ℂ Y₁ → IsChar ℂ ℂ Y₂ → Kills φ₁ Y₁ → Kills φ₂ Y₂ → Kills (fun p => φ₁ (π p).1 * φ₂ (π p).2) (fun p => Y₁ (π p).1 * Y₂ (π p).2) := by
  intro P G₁ G₂ _ _ _ _ π hπ φ₁ Y₁ φ₂ Y₂ hY₁ hY₂ h₁ h₂
  haveI : Finite G₁ := Finite.of_surjective (fun p => (π p).1) (fun g => by
    obtain ⟨p, hp⟩ := hπ (g, 1); exact ⟨p, by simp [hp]⟩)
  haveI : Finite G₂ := Finite.of_surjective (fun p => (π p).2) (fun g => by
    obtain ⟨p, hp⟩ := hπ (1, g); exact ⟨p, by simp [hp]⟩)
  haveI := Fintype.ofFinite P
  haveI := Fintype.ofFinite G₁
  haveI := Fintype.ofFinite G₂
  have hY : IsChar ℂ ℂ (fun p => Y₁ (π p).1 * Y₂ (π p).2) := by
    obtain ⟨n, ρ, hρ⟩ := hY₁
    obtain ⟨m, σ, hσ⟩ := hY₂
    exact isChar_mul_complex (a := fun p => Y₁ (π p).1) (b := fun p => Y₂ (π p).2)
      ⟨n, ρ.comp ((MonoidHom.fst G₁ G₂).comp π), fun p => hρ _⟩
      ⟨m, σ.comp ((MonoidHom.snd G₁ G₂).comp π), fun p => hσ _⟩
  obtain ⟨k₁, hk₁⟩ := (GlobalTheory.T.isInCharacterIsotypicPart_iff_convolution G₁ φ₁ Y₁ hY₁).1 h₁
  obtain ⟨k₂, hk₂⟩ := (GlobalTheory.T.isInCharacterIsotypicPart_iff_convolution G₂ φ₂ Y₂ hY₂).1 h₂
  apply (GlobalTheory.T.isInCharacterIsotypicPart_iff_convolution P _ _ hY).2
  set c : ℕ := (Finset.univ.filter fun q : P => π q = 1).card with hcdef
  have hc : (c : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    apply Finset.card_ne_zero_of_mem (a := (1 : P))
    simp
  refine ⟨fun p => k₁ (π p).1 * k₂ (π p).2 / c, fun x => ?_⟩
  rw [hk₁, hk₂]
  simp only [finsum_eq_sum_of_fintype]
  set F : G₁ × G₂ → ℂ := fun g => Y₁ g.1 * Y₂ g.2 * (k₁ (g.1⁻¹ * (π x).1) * k₂ (g.2⁻¹ * (π x).2)) with hF
  have hR : ∀ q : P, Y₁ (π q).1 * Y₂ (π q).2 * (k₁ (π (q⁻¹ * x)).1 * k₂ (π (q⁻¹ * x)).2 / c) = F (π q) / c := by
    intro q
    simp only [hF, map_mul, map_inv, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv]
    ring
  simp only [hR]
  rw [← Finset.sum_div]
  have hfib : ∑ q : P, F (π q) = ∑ g : G₁ × G₂, (c : ℂ) * F g := by
    rw [← Finset.sum_fiberwise Finset.univ (fun q => π q) (fun q => F (π q))]
    refine Finset.sum_congr rfl fun g _ => ?_
    have e : ∀ q ∈ Finset.univ.filter (fun q : P => π q = g), F (π q) = F g := by
      intro q hq; rw [(Finset.mem_filter.1 hq).2]
    rw [Finset.sum_congr rfl e, Finset.sum_const, nsmul_eq_mul, hcdef,
      MonoidHom.card_fiber_eq_of_mem_range π (hπ g) (hπ 1)]
  rw [hfib, ← Finset.mul_sum, mul_div_cancel_left₀ _ hc, Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [hF]
  ring

end GlobalTheory.Shin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotypicPartExteriorProductInflatedSurjectionStatement

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.isotypicPart_exteriorProduct_inflated_surjection : ∀ (P G₁ G₂ : Type) [Group P] [Finite P] [Group G₁] [Group G₂] (π : P →* G₁ × G₂), Function.Surjective π → ∀ (φ₁ Y₁ : G₁ → ℂ) (φ₂ Y₂ : G₂ → ℂ), IsChar ℂ ℂ Y₁ → IsChar ℂ ℂ Y₂ → Kills φ₁ Y₁ → Kills φ₂ Y₂ → Kills (fun p => φ₁ (π p).1 * φ₂ (π p).2) (fun p => Y₁ (π p).1 * Y₂ (π p).2) := by
  first | (exact @GlobalTheory.Shin.kills_prod_comp_surj) | (exact GlobalTheory.Shin.kills_prod_comp_surj) | (intros; apply GlobalTheory.Shin.kills_prod_comp_surj <;> assumption)
end
end
