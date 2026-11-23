module

public import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondOperatorOfMatrixCuspFormGamma1InterGamma0Statement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeOperatorCommutesDiamondStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTOperatorExplicitCuspFormStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiamondMatrixConjMemGamma1InterGamma0Level
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PeterssonCosetIntegralSumHeckeTAdjoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PeterssonCosetIntegralSumSelfPosGamma1InterGammaStatement
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.CocycleCoefficients.PetAdjQuot
public import Mathlib.NumberTheory.ModularForms.Bounds
import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiamondMatrixConjMemGamma1InterGamma0LevelStatement

section

@[expose] public section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

theorem _root_.GlobalTheory.T.isDiamondMatrix_conj_mem_gamma1InterGamma0Level : ∀ (N l : ℕ) (d : ℤ) (σ γ : SL(2, ℤ)), GlobalTheory.Hk.IsDia N l d σ → γ ∈ GlobalTheory.Hk.lev N l → σ * γ * σ⁻¹ ∈ GlobalTheory.Hk.lev N l := by
  first | exact @GlobalTheory.Hk.isDia_conj_mem_lev | exact GlobalTheory.Hk.isDia_conj_mem_lev | (intros; apply GlobalTheory.Hk.isDia_conj_mem_lev <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.PeterssonCosetIntegralSumDiamondOperatorUnitary

section

@[expose] public section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

lemma petersson_smul_of_mem {Γ : Subgroup SL(2, ℤ)} {k : ℤ} (f g : CuspForm Γ k) {h : SL(2, ℤ)}
    (hh : h ∈ Γ) (τ : ℍ) : petersson k ⇑f ⇑g (h • τ) = petersson k ⇑f ⇑g τ := by
  have hf : (⇑f ∣[k] h) = ⇑f := by
    rw [ModularForm.SL_slash]; exact SlashInvariantForm.slash_action_eqn f _ ⟨h, hh, rfl⟩
  have hg : (⇑g ∣[k] h) = ⇑g := by
    rw [ModularForm.SL_slash]; exact SlashInvariantForm.slash_action_eqn g _ ⟨h, hh, rfl⟩
  rw [← petersson_slash_SL, hf, hg]

def cosetShift (Γ : Subgroup SL(2, ℤ)) (σ : SL(2, ℤ))
    (h₁ : ∀ γ ∈ Γ, σ * γ * σ⁻¹ ∈ Γ) (h₂ : ∀ γ ∈ Γ, σ⁻¹ * γ * σ ∈ Γ) :
    SL(2, ℤ) ⧸ Γ ≃ SL(2, ℤ) ⧸ Γ where
  toFun := Quotient.map' (· * σ⁻¹) fun a b hab => by
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    simpa [mul_assoc] using h₁ _ hab
  invFun := Quotient.map' (· * σ) fun a b hab => by
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    simpa [mul_assoc] using h₂ _ hab
  left_inv q := by
    induction q using Quotient.inductionOn' with
    | h a => simp [Quotient.map'_mk'']
  right_inv q := by
    induction q using Quotient.inductionOn' with
    | h a => simp [Quotient.map'_mk'']

theorem pet_dia_dia : ∀ (N l : ℕ) (k d : ℤ) (σ : SL(2, ℤ)), 0 < N → 0 < l → GlobalTheory.Hk.IsDia N l d σ →
    ∀ f g : CuspForm (GlobalTheory.Hk.lev N l) k,
      GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k (GlobalTheory.Hk.dia k σ ⇑f) (GlobalTheory.Hk.dia k σ ⇑g) =
        GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k ⇑f ⇑g := by
  intro N l k d σ _ _ hσ f g
  have h₁ : ∀ γ ∈ lev N l, σ * γ * σ⁻¹ ∈ lev N l := fun γ hγ => GlobalTheory.T.isDiamondMatrix_conj_mem_gamma1InterGamma0Level N l d σ γ hσ hγ
  have hσ' : IsDia N l (σ 0 0) σ⁻¹ := by
    refine ⟨?_, ?_⟩
    · simp [Matrix.SpecialLinearGroup.SL2_inv_expl, hσ.1]
    · simp [Matrix.SpecialLinearGroup.SL2_inv_expl]
  have h₂ : ∀ γ ∈ lev N l, σ⁻¹ * γ * σ ∈ lev N l := fun γ hγ => by
    simpa using GlobalTheory.T.isDiamondMatrix_conj_mem_gamma1InterGamma0Level N l _ σ⁻¹ γ hσ' hγ
  set e := cosetShift (lev N l) σ h₁ h₂
  unfold pet
  conv_rhs => rw [← finsum_comp_equiv e]
  refine finsum_congr fun γ => ?_
  congr 1
  funext z
  have he : e γ = QuotientGroup.mk (γ.out * σ⁻¹) := by
    conv_lhs => rw [← QuotientGroup.out_eq' γ]
    rfl
  have hx : (QuotientGroup.mk (e γ).out : SL(2, ℤ) ⧸ lev N l) = QuotientGroup.mk (γ.out * σ⁻¹) := by
    rw [QuotientGroup.out_eq', he]
  have hmem := QuotientGroup.eq.mp hx.symm
  have hinv : (e γ).out⁻¹ = ((γ.out * σ⁻¹)⁻¹ * (e γ).out)⁻¹ * (σ * γ.out⁻¹) := by group
  rw [hinv, mul_smul, petersson_smul_of_mem f g (inv_mem hmem), dia, dia, petersson_slash_SL,
    mul_smul]

end GlobalTheory.Hk
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.PeterssonCosetIntegralSumDiamondOperatorUnitaryStatement

section

@[expose] public section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

theorem _root_.GlobalTheory.T.peterssonCosetIntegralSum_diamondOperator_unitary : ∀ (N l : ℕ) (k d : ℤ) (σ : SL(2, ℤ)), 0 < N → 0 < l → GlobalTheory.Hk.IsDia N l d σ → ∀ f g : CuspForm (GlobalTheory.Hk.lev N l) k, GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k (GlobalTheory.Hk.dia k σ ⇑f) (GlobalTheory.Hk.dia k σ ⇑g) = GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k ⇑f ⇑g := by
  first | exact @GlobalTheory.Hk.pet_dia_dia | exact GlobalTheory.Hk.pet_dia_dia | (intros; apply GlobalTheory.Hk.pet_dia_dia <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.PeterssonCosetIntegralSumHeckeTAdjointStatement

section

@[expose] public section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

theorem _root_.GlobalTheory.T.peterssonCosetIntegralSum_heckeT_adjoint : ∀ (N l q : ℕ) (k : ℤ) (σ σ' : SL(2, ℤ)), 0 < N → 0 < l → q.Prime → ¬ q ∣ N * l → GlobalTheory.Hk.IsDia N l q σ → GlobalTheory.Hk.IsDia N l q σ' → ∀ f g : CuspForm (GlobalTheory.Hk.lev N l) k, GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k (GlobalTheory.Hk.heckeT k q σ ⇑f) (GlobalTheory.Hk.dia k σ' ⇑g) = GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k ⇑f (GlobalTheory.Hk.heckeT k q σ ⇑g) := by
  first | exact @GlobalTheory.Hk.pet_heckeT_adj | exact GlobalTheory.Hk.pet_heckeT_adj | (intros; apply GlobalTheory.Hk.pet_heckeT_adj <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.PeterssonCosetIntegralSumSesquilinearHermitian

section

@[expose] public section

noncomputable section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem lev_finiteIndex' (N l : ℕ) (hN : 0 < N) (hl : 0 < l) : (lev N l).FiniteIndex := by
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero l := ⟨hl.ne'⟩
  unfold lev
  infer_instance

theorem pet_eq_quotInt (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f g : ℍ → ℂ) :
    pet Γ k f g = UpperTheory.V.Lit.KT.quotInt Γ (petersson k f g) := rfl

theorem pet_sesq : ∀ (N l : ℕ) (k : ℤ), 0 < N → 0 < l → ∀ (f g h : CuspForm (GlobalTheory.Hk.lev N l) k) (c : ℂ), GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k ⇑f (⇑g + c • ⇑h) = GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k ⇑f ⇑g + c * GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k ⇑f ⇑h ∧ GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k ⇑g ⇑f = (starRingEnd ℂ) (GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k ⇑f ⇑g) := by
  intro N l k hN hl f g h c
  haveI := lev_finiteIndex' N l hN hl
  haveI : Fintype (SL(2, ℤ) ⧸ lev N l) := Fintype.ofFinite _
  refine ⟨?_, ?_⟩
  · have e : petersson k ⇑f (⇑g + c • ⇑h) = fun z => petersson k f g z + c * petersson k f h z := by
      funext z
      simp only [petersson, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    obtain ⟨B, hB⟩ := CuspFormClass.petersson_bounded_left k _ f g
    obtain ⟨B', hB'⟩ := CuspFormClass.petersson_bounded_left k _ f h
    have hc := petersson_continuous k (ModularFormClass.continuous f) (ModularFormClass.continuous g)
    have hc' := petersson_continuous k (ModularFormClass.continuous f) (ModularFormClass.continuous h)
    have hb'' : ∀ z, ‖c * petersson k f h z‖ ≤ ‖c‖ * B' := fun z => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hB' z) (norm_nonneg _)
    rw [pet_eq_quotInt, pet_eq_quotInt, pet_eq_quotInt, e,
      UpperTheory.V.Lit.KT.quotInt_add (ψ := fun z => c * petersson k f h z) _ hc hB (continuous_const.mul hc') hb'', UpperTheory.V.Lit.KT.quotInt_mul]
  · simp only [pet, finsum_eq_sum_of_fintype]

    rw [map_sum]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [← integral_conj]
    congr 1
    funext z
    exact petersson_symm _ _ _ _

end GlobalTheory.Hk
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.PeterssonCosetIntegralSumSesquilinearHermitianStatement

section

@[expose] public section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

theorem _root_.GlobalTheory.T.peterssonCosetIntegralSum_sesquilinear_hermitian : ∀ (N l : ℕ) (k : ℤ), 0 < N → 0 < l → ∀ (f g h : CuspForm (GlobalTheory.Hk.lev N l) k) (c : ℂ), GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k ⇑f (⇑g + c • ⇑h) = GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k ⇑f ⇑g + c * GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k ⇑f ⇑h ∧ GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k ⇑g ⇑f = (starRingEnd ℂ) (GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k ⇑f ⇑g) := by
  first | exact @GlobalTheory.Hk.pet_sesq | exact GlobalTheory.Hk.pet_sesq | (intros; apply GlobalTheory.Hk.pet_sesq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTOperatorExplicitSemisimpleCuspForms

section

@[expose] public section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk.Semisimple

theorem dia_sub_smul (k : ℤ) (σ : SL(2, ℤ)) (f g : ℍ → ℂ) (c : ℂ) :
    GlobalTheory.Hk.dia k σ (f - c • g) = GlobalTheory.Hk.dia k σ f - c • GlobalTheory.Hk.dia k σ g := by
  unfold GlobalTheory.Hk.dia
  rw [sub_eq_add_neg, SlashAction.add_slash, ← _root_.neg_smul, ModularForm.SL_smul_slash, _root_.neg_smul,
    ← sub_eq_add_neg]

theorem heckeT_zero (k : ℤ) (q : ℕ) (σ : SL(2, ℤ)) : GlobalTheory.Hk.heckeT k q σ 0 = 0 := by
  funext τ
  simp [GlobalTheory.Hk.heckeT, GlobalTheory.Hk.uOp, GlobalTheory.Hk.vOp]

section
variable {N l : ℕ} {k : ℤ}

local notation "P" => GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k

theorem pet_zero_right (hN : 0 < N) (hl : 0 < l) (f : CuspForm (GlobalTheory.Hk.lev N l) k) :
    P ⇑f 0 = 0 := by
  have h := (GlobalTheory.T.peterssonCosetIntegralSum_sesquilinear_hermitian N l k hN hl f 0 0 1).1
  simp only [CuspForm.coe_zero, smul_zero, add_zero, one_mul] at h
  linear_combination -h

theorem pet_smul_right (hN : 0 < N) (hl : 0 < l) (f h : CuspForm (GlobalTheory.Hk.lev N l) k) (c : ℂ) :
    P ⇑f (c • ⇑h) = c * P ⇑f ⇑h := by
  have e := (GlobalTheory.T.peterssonCosetIntegralSum_sesquilinear_hermitian N l k hN hl f 0 h c).1
  simp only [CuspForm.coe_zero, zero_add] at e
  rw [e, pet_zero_right hN hl f, zero_add]

theorem pet_lin_right (hN : 0 < N) (hl : 0 < l) (f g h : CuspForm (GlobalTheory.Hk.lev N l) k) (a b : ℂ) :
    P ⇑f (a • ⇑g - b • ⇑h) = a * P ⇑f ⇑g - b * P ⇑f ⇑h := by
  have e := (GlobalTheory.T.peterssonCosetIntegralSum_sesquilinear_hermitian N l k hN hl f (a • g) h (-b)).1
  rw [CuspForm.coe_smul, _root_.neg_smul, ← sub_eq_add_neg] at e
  rw [e, pet_smul_right hN hl]
  ring

theorem pet_conj (hN : 0 < N) (hl : 0 < l) (f g : CuspForm (GlobalTheory.Hk.lev N l) k) :
    P ⇑g ⇑f = (starRingEnd ℂ) (P ⇑f ⇑g) :=
  (GlobalTheory.T.peterssonCosetIntegralSum_sesquilinear_hermitian N l k hN hl f g 0 0).2

theorem pet_lin_left (hN : 0 < N) (hl : 0 < l) (f g h : CuspForm (GlobalTheory.Hk.lev N l) k) (a b : ℂ) :
    P (a • ⇑g - b • ⇑h) ⇑f = (starRingEnd ℂ) a * P ⇑g ⇑f - (starRingEnd ℂ) b * P ⇑h ⇑f := by
  have e : a • ⇑g - b • ⇑h = ⇑(a • g - b • h) := by
    rw [CuspForm.coe_sub, CuspForm.coe_smul, CuspForm.coe_smul]
  rw [e, pet_conj hN hl, CuspForm.coe_sub, CuspForm.coe_smul, CuspForm.coe_smul,
    pet_lin_right hN hl, map_sub, map_mul, map_mul, ← pet_conj hN hl, ← pet_conj hN hl]

theorem eq_zero_of_pet_self (hN : 0 < N) (hl : 0 < l) (f : CuspForm (GlobalTheory.Hk.lev N l) k)
    (h : P ⇑f ⇑f = 0) : f = 0 := by
  by_contra hf
  have := (GlobalTheory.T.peterssonCosetIntegralSum_self_pos_gamma1InterGamma0 N l k hN hl f hf).1
  rw [h] at this
  simp at this

theorem eigen_dia (hN : 0 < N) (hl : 0 < l) {q : ℕ} {σ : SL(2, ℤ)} (hq : q.Prime)
    (hqN : ¬ q ∣ N * l) (hσ : GlobalTheory.Hk.IsDia N l q σ) (c : ℂ) (u v : CuspForm (GlobalTheory.Hk.lev N l) k)
    (hv : ⇑v = GlobalTheory.Hk.dia k σ ⇑u) (hu : GlobalTheory.Hk.heckeT k q σ ⇑u = c • ⇑u) :
    c • ⇑u = (starRingEnd ℂ) c • ⇑v := by
  have h1 : P ⇑v ⇑v = P ⇑u ⇑u := by
    rw [hv]; exact GlobalTheory.T.peterssonCosetIntegralSum_diamondOperator_unitary N l k q σ hN hl hσ u u
  have h2 : (starRingEnd ℂ) c * P ⇑u ⇑v = c * P ⇑u ⇑u := by
    have h := GlobalTheory.T.peterssonCosetIntegralSum_heckeT_adjoint N l q k σ σ hN hl hq hqN hσ hσ u u
    rw [hu, ← hv, pet_smul_right hN hl, ← CuspForm.coe_smul, pet_conj hN hl, CuspForm.coe_smul,
      pet_smul_right hN hl, map_mul, ← pet_conj hN hl] at h
    exact h
  have h3 : c * P ⇑v ⇑u = (starRingEnd ℂ) c * P ⇑u ⇑u := by
    have h := congrArg (starRingEnd ℂ) h2
    rw [map_mul, map_mul, ← pet_conj hN hl, ← pet_conj hN hl, Complex.conj_conj] at h
    exact h
  have e : ⇑(c • u - (starRingEnd ℂ) c • v) = c • ⇑u - (starRingEnd ℂ) c • ⇑v := by
    rw [CuspForm.coe_sub, CuspForm.coe_smul, CuspForm.coe_smul]
  have hw : c • u - (starRingEnd ℂ) c • v = 0 := by
    apply eq_zero_of_pet_self hN hl
    have := pet_lin_left hN hl (c • u - (starRingEnd ℂ) c • v) u v c ((starRingEnd ℂ) c)
    rw [← e] at this
    rw [this, e, pet_lin_right hN hl, pet_lin_right hN hl, h1, h2, h3]
    ring
  rw [hw, CuspForm.coe_zero] at e
  exact (sub_eq_zero.mp e.symm)

theorem ker_sq (hN : 0 < N) (hl : 0 < l) {q : ℕ} {σ : SL(2, ℤ)} (hq : q.Prime)
    (hqN : ¬ q ∣ N * l) (hσ : GlobalTheory.Hk.IsDia N l q σ) (c : ℂ) (g u : CuspForm (GlobalTheory.Hk.lev N l) k)
    (hg : ⇑u = GlobalTheory.Hk.heckeT k q σ ⇑g - c • ⇑g) (hu : GlobalTheory.Hk.heckeT k q σ ⇑u = c • ⇑u) :
    u = 0 := by
  obtain ⟨v, hv⟩ := GlobalTheory.T.diamondOperatorOfMatrix_cuspForm_gamma1InterGamma0 N l k q σ hN hσ u
  obtain ⟨dg, hdg⟩ := GlobalTheory.T.diamondOperatorOfMatrix_cuspForm_gamma1InterGamma0 N l k q σ hN hσ g
  obtain ⟨sdg, hsdg⟩ := GlobalTheory.T.heckeTOperatorExplicit_cuspForm N l q k σ hN hq hqN hσ dg
  have hw := eigen_dia hN hl hq hqN hσ c u v hv hu
  have hcomm : GlobalTheory.Hk.heckeT k q σ (GlobalTheory.Hk.dia k σ ⇑g)
      = GlobalTheory.Hk.dia k σ (GlobalTheory.Hk.heckeT k q σ ⇑g) :=
    GlobalTheory.T.hecke_operator_commutes_diamond N l q k q σ σ hN hq hqN hσ hσ (CuspForm.toModularFormₗ g)
  have hv' : ⇑v = (1 : ℂ) • ⇑sdg - c • ⇑dg := by
    rw [hv, hg, dia_sub_smul, ← hcomm, hsdg, hdg, one_smul]
  have h1 : P ⇑v ⇑v = P ⇑u ⇑u := by
    rw [hv]; exact GlobalTheory.T.peterssonCosetIntegralSum_diamondOperator_unitary N l k q σ hN hl hσ u u
  have h2 : P ⇑sdg ⇑v = (starRingEnd ℂ) c * P ⇑dg ⇑v := by
    have h := GlobalTheory.T.peterssonCosetIntegralSum_heckeT_adjoint N l q k σ σ hN hl hq hqN hσ hσ dg u
    rw [← hsdg, ← hv, hu, hw, pet_smul_right hN hl] at h
    exact h
  apply eq_zero_of_pet_self hN hl
  have h3 := pet_lin_left hN hl v sdg dg 1 c
  rw [← hv', h1, h2] at h3
  rw [h3]
  simp

end

theorem heckeT_semisimple : ∀ (N l q : ℕ) (k : ℤ) (σ : SL(2, ℤ)) (c : ℂ) (n : ℕ), 0 < N → 0 < l → q.Prime → ¬ q ∣ N * l → GlobalTheory.Hk.IsDia N l q σ → ∀ f : CuspForm (GlobalTheory.Hk.lev N l) k, (fun h => GlobalTheory.Hk.heckeT k q σ h - c • h)^[n] ⇑f = 0 → GlobalTheory.Hk.heckeT k q σ ⇑f = c • ⇑f := by
  intro N l q k σ c n hN hl hq hqN hσ
  induction n with
  | zero =>
    intro f hf
    have hf' : ⇑f = 0 := hf
    rw [hf', heckeT_zero, smul_zero]
  | succ n ih =>
    intro f hf
    obtain ⟨sf, hsf⟩ := GlobalTheory.T.heckeTOperatorExplicit_cuspForm N l q k σ hN hq hqN hσ f
    have e : ⇑(sf - c • f) = GlobalTheory.Hk.heckeT k q σ ⇑f - c • ⇑f := by
      rw [CuspForm.coe_sub, CuspForm.coe_smul, hsf]
    rw [Function.iterate_succ_apply] at hf
    have hu := ih (sf - c • f) (by rw [e]; exact hf)
    have h0 := ker_sq hN hl hq hqN hσ c f (sf - c • f) e hu
    rw [h0, CuspForm.coe_zero] at e
    exact sub_eq_zero.mp e.symm

end GlobalTheory.Hk.Semisimple
end
end
