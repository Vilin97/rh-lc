module

public import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ChapterMu
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AtkinLehnerIntertwinesHeckeOperatorsStatement
public import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashIntMatrixPosDetProperties
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Gamma1CharElementary
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspidalAtAllCuspsSL2SlashIntMatrix
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormGammaOneOfCoeffSeq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashIntMatrixPosDetProperties
import Mathlib.NumberTheory.ModularForms.Bounds
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSturmBoundIsModularFormCoeffSeq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsModularFormCoeffSeqHeckeTOfPrimeNotDvdStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsModularFormCoeffSeqHeckeUAndDepletionStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LamExtendByZeroStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LinearFunctionalEqCoeffLinearCombinationFinite
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormCoeffSeqLinearStructure
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionFunctionInjectiveOfPolynomialGrowth
import Mathlib.RingTheory.PiTensorProduct

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.AtkinLehnerSlashInverseCharacter

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

theorem atkinLehner_conj_int (N l : ℕ) (a b c d : ℤ) (h : (N : ℤ) * a * d - l * b * c = 1) (γ : M2)
    (hγ : ((N * l : ℕ) : ℤ) ∣ γ 1 0) (hdet : γ.det = 1) :
    ∃ γ' : M2, !![(N : ℤ) * a, b; N * l * c, N * d] * γ = γ' * !![(N : ℤ) * a, b; N * l * c, N * d] ∧
    γ'.det = 1 ∧ ((N * l : ℕ) : ℤ) ∣ γ' 1 0 ∧ (N : ℤ) ∣ γ' 1 1 - γ 0 0 := by
  obtain ⟨r, hr⟩ := hγ
  push_cast at hr
  set p := γ 0 0
  set q := γ 0 1
  set s := γ 1 1
  have hdet' : p * s - (N * l * r) * q = 1 := by
    rw [Matrix.det_fin_two] at hdet; rw [hr] at hdet; linarith
  refine ⟨!![(N : ℤ) * a * d * p + N * l * b * d * r - N * l * a * c * q - l * b * c * s,
     -(a * b * p) - l * b * b * r + N * a * a * q + a * b * s;
     N * l * (c * d * p + N * d * d * r - l * c * c * q - c * d * s),
     -(l * b * c * p) - N * l * b * d * r + N * l * a * c * q + N * a * d * s], ?_, ?_, ?_, ?_⟩
  · have hγe : γ = !![p, q; N * l * r, s] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [p, q, s, hr]
    rw [hγe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination -(N * a * p + b * N * l * r) * h
    · linear_combination -(N * a * q + b * s) * h
    · linear_combination -(N * l * c * p + N * d * N * l * r) * h
    · linear_combination -(N * l * c * q + N * d * s) * h
  · rw [Matrix.det_fin_two_of]
    linear_combination ((N : ℤ) * a * d - l * b * c) ^ 2 * hdet' + ((N : ℤ) * a * d - l * b * c + 1) * h
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one]
    push_cast
    exact Dvd.intro _ rfl
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one]
    exact ⟨-(b * d * l * r) + l * a * c * q + a * d * s - a * d * p, by linear_combination p * h⟩

theorem inv_slz_atkinLehner : ∀ (k N l : ℕ) (χ : DirichletCharacter ℂ N) (f : ℍ → ℂ) (a₀ b₀ c₀ d₀ : ℤ),
    N * a₀ * d₀ - l * b₀ * c₀ = 1 → 1 ≤ k → 0 < N → Inv k (N * l) (ch χ) f →
    Inv k (N * l) (ch χ⁻¹) (slz k !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] f) := by
  intro k N l χ f a b c d h hk hN hf
  set Q : M2 := !![(N : ℤ) * a, b; N * l * c, N * d] with hQ
  have hQdet : 0 < Q.det := by
    have : Q.det = N * (N * a * d - l * b * c) := by rw [hQ, Matrix.det_fin_two_of]; ring
    rw [this, h, mul_one]; exact_mod_cast hN
  have hiff := (slz_props k (slz k Q f) hk).2.2.1 (N * l) (ch χ⁻¹)
  have hiff0 := (slz_props k f hk).2.2.1 (N * l) (ch χ)
  refine hiff.2 fun γ hγ => ?_
  have hγdet : (γ : M2).det = 1 := Matrix.SpecialLinearGroup.det_coe γ
  have hγ' : ((N * l : ℕ) : ℤ) ∣ (γ : M2) 1 0 := by exact_mod_cast hγ
  obtain ⟨g, hg, hgdet, hgdvd, hgcong⟩ := atkinLehner_conj_int N l a b c d h (γ : M2) hγ' hγdet
  let γ₁ : SL(2, ℤ) := ⟨g, hgdet⟩
  have hf1 := hiff0.1 hf γ₁ (by exact_mod_cast hgdvd)
  have hcalc : slz k (γ : M2) (slz k Q f) = slz k Q (slz k (γ₁ : M2) f) := by
    rw [← slz_mul k f Q (γ : M2) hQdet (by rw [hγdet]; exact one_pos), hg,
      slz_mul k f g Q (by rw [hgdet]; exact one_pos) hQdet]
  rw [hcalc, hf1]
  have hchar : ch χ (γ₁ 1 1) = ch χ⁻¹ (γ 1 1) := by
    simp only [ch]
    have e1 : ((γ₁ 1 1 : ℤ) : ZMod N) = ((γ 0 0 : ℤ) : ZMod N) :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).2 (by
        have : (N : ℤ) ∣ g 1 1 - γ 0 0 := hgcong
        rw [← dvd_neg, neg_sub]; exact this)
    have e2 : ((γ 0 0 : ℤ) : ZMod N) * ((γ 1 1 : ℤ) : ZMod N) = 1 := by
      have hd := hγdet
      rw [Matrix.det_fin_two] at hd
      obtain ⟨r, hr⟩ := hγ'
      have : ((((γ : M2) 0 0 * (γ : M2) 1 1 - (γ : M2) 0 1 * (γ : M2) 1 0 : ℤ)) : ZMod N) = 1 := by
        rw [hd]; simp
      rw [hr] at this
      push_cast at this
      simpa using this
    rw [e1, MulChar.inv_apply_eq_inv']
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul, e2, map_one]
  funext τ
  simp only [slz]
  rw [hchar]
  ring

end GlobalTheory.EisM
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.AtkinLehnerSlashInverseCharacterStatement

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.atkinLehner_slash_inverse_character : ∀ (k N l : ℕ) (χ : DirichletCharacter ℂ N) (f : ℍ → ℂ) (a₀ b₀ c₀ d₀ : ℤ), N * a₀ * d₀ - l * b₀ * c₀ = 1 → 1 ≤ k → 0 < N → Inv k (N * l) (ch χ) f → Inv k (N * l) (ch χ⁻¹) (slz k !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] f) := by
  first | exact @GlobalTheory.EisM.inv_slz_atkinLehner | exact GlobalTheory.EisM.inv_slz_atkinLehner | (intros; apply GlobalTheory.EisM.inv_slz_atkinLehner <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.AtkinLehnerSlashIsModularFormCoeffSeq

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM.AtkinLehnerForm

theorem toGL_entry (A : M2) (hA : A.det ≠ 0) (i j : Fin 2) :
    (↑(GlobalTheory.HeckeFamilyMatrices.toGL A) : Matrix (Fin 2) (Fin 2) ℝ) i j = (A i j : ℝ) := by
  rw [GlobalTheory.HeckeFamilyMatrices.toGL_val A hA]; simp

theorem slz_eq_slash (k : ℕ) (hk : 1 ≤ k) (δ : M2) (hδ : 0 < δ.det) (f : ℍ → ℂ) :
    slz k δ f = f ∣[(k : ℤ)] GlobalTheory.HeckeFamilyMatrices.toGL δ := by
  funext τ
  have hd : 0 < (GlobalTheory.HeckeFamilyMatrices.toGL δ).det.val := GlobalTheory.HeckeFamilyMatrices.toGL_det_pos δ hδ
  have hpt : ofComplex ((((δ 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 1 1 : ℤ) : ℂ)))
      = GlobalTheory.HeckeFamilyMatrices.toGL δ • τ := by
    ext1
    rw [slzMob_coe δ hδ τ, UpperHalfPlane.coe_smul_of_det_pos hd]
    simp [UpperHalfPlane.num, UpperHalfPlane.denom, toGL_entry δ hδ.ne']
  rw [ModularForm.slash_apply, GlobalTheory.HeckeFamilyMatrices.sigma_pos hd, slz, hpt]
  have hdet : (GlobalTheory.HeckeFamilyMatrices.toGL δ).det.val = (δ.det : ℝ) := GlobalTheory.HeckeFamilyMatrices.toGL_det δ hδ.ne'
  rw [hdet, abs_of_pos (by exact_mod_cast hδ)]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have e1 : (((m + 1 : ℕ) : ℤ) - 1) = ((m : ℕ) : ℤ) := by push_cast; ring
  rw [e1, zpow_natCast, zpow_neg, zpow_natCast]
  simp only [Nat.add_sub_cancel, UpperHalfPlane.denom, toGL_entry δ hδ.ne', Complex.ofReal_intCast]
  ring

end GlobalTheory.EisM.AtkinLehnerForm

namespace GlobalTheory.EisM.AtkinLehnerForm

theorem qs_add_int (a : ℕ → ℂ) (τ : ℍ) (m : ℤ) : qs a (ofComplex ((τ : ℂ) + m)) = qs a τ := by
  have him : 0 < ((τ : ℂ) + m).im := by simpa using τ.im_pos
  have hcoe : ((ofComplex ((τ : ℂ) + m) : ℍ) : ℂ) = (τ : ℂ) + m := by
    rw [ofComplex_apply_of_im_pos him]
  simp only [qs, hcoe]
  congr 1
  funext n
  have e : cexp (2 * π * Complex.I * n * ((τ : ℂ) + m)) = cexp (2 * π * Complex.I * n * τ) := by
    rw [show 2 * π * Complex.I * n * ((τ : ℂ) + m) = 2 * π * Complex.I * n * τ + ((n * m : ℤ) : ℂ) * (2 * π * Complex.I) by
      push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [e]

theorem slz_levelOne (k : ℕ) (a : ℕ → ℂ) (a₀ b₀ c₀ d₀ : ℤ) (h : a₀ * d₀ = 1) :
    slz k !![((1 : ℕ) : ℤ) * a₀, b₀; ((1 : ℕ) : ℤ) * ((0 : ℕ) : ℤ) * c₀, ((1 : ℕ) : ℤ) * d₀] (qs a)
      = fun τ => ((d₀ : ℂ) ^ k)⁻¹ * qs a τ := by
  funext τ
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have e : (((((1 : ℕ) : ℤ) * 1 : ℤ) : ℂ) * (τ : ℂ) + ((b₀ : ℤ) : ℂ)) / (((((1 : ℕ) : ℤ) * ((0 : ℕ) : ℤ) * c₀ : ℤ) : ℂ) * (τ : ℂ) + ((((1 : ℕ) : ℤ) * 1 : ℤ) : ℂ))
        = (τ : ℂ) + ((b₀ : ℤ) : ℂ) := by push_cast; ring
    simp only [slz, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.det_fin_two_of, e, qs_add_int]
    push_cast
    try simp
  · have e : (((((1 : ℕ) : ℤ) * (-1) : ℤ) : ℂ) * (τ : ℂ) + ((b₀ : ℤ) : ℂ)) / (((((1 : ℕ) : ℤ) * ((0 : ℕ) : ℤ) * c₀ : ℤ) : ℂ) * (τ : ℂ) + ((((1 : ℕ) : ℤ) * (-1) : ℤ) : ℂ))
        = (τ : ℂ) + ((-b₀ : ℤ) : ℂ) := by push_cast; ring
    simp only [slz, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.det_fin_two_of, e, qs_add_int]
    push_cast
    try simp

end GlobalTheory.EisM.AtkinLehnerForm


open GlobalTheory.EisM.AtkinLehnerForm in
theorem GlobalTheory.EisM.atkinLehner_MF : ∀ (k N l : ℕ) (χ : DirichletCharacter ℂ N) (a : ℕ → ℂ) (a₀ b₀ c₀ d₀ : ℤ), N * a₀ * d₀ - l * b₀ * c₀ = 1 → 1 ≤ k → 0 < N → MF k (N * l) (ch χ) a → ∃ a' : ℕ → ℂ, MF k (N * l) (ch χ⁻¹) a' ∧ qs a' = slz k !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] (qs a) := by
  intro k N l χ a a₀ b₀ c₀ d₀ h hk hN ha
  have hinv := GlobalTheory.T.atkinLehner_slash_inverse_character k N l χ (qs a) a₀ b₀ c₀ d₀ h hk hN ha.2
  suffices hex : ∃ a' : ℕ → ℂ, PolyB a' ∧ qs a' = slz k !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] (qs a) by
    obtain ⟨a', h1, h2⟩ := hex
    exact ⟨a', ⟨h1, h2 ▸ hinv⟩, h2⟩
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · have h' : (N : ℤ) * (a₀ * d₀) = 1 := by linear_combination h
    have hN1 : N = 1 := by exact_mod_cast Int.eq_one_of_mul_eq_one_right (by positivity) h'
    subst hN1
    have had : a₀ * d₀ = 1 := by simpa using h'
    rw [slz_levelOne k a a₀ b₀ c₀ d₀ had]
    obtain ⟨C, A, hC⟩ := ha.1
    refine ⟨fun n => ((d₀ : ℂ) ^ k)⁻¹ * a n, ⟨‖((d₀ : ℂ) ^ k)⁻¹‖ * C, A, fun n => ?_⟩, ?_⟩
    · rw [norm_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hC n) (norm_nonneg _)
    · funext τ
      simp only [qs]
      rw [← tsum_mul_left]
      congr 1
      funext n
      ring
  · set δ : M2 := !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] with hδdef
    have hdet : δ.det = N := by rw [hδdef, Matrix.det_fin_two_of]; linear_combination (N : ℤ) * h
    have hδ : 0 < δ.det := by rw [hdet]; exact_mod_cast hN
    have hL : 0 < N * l := Nat.mul_pos hN hl
    haveI : NeZero (N * l) := ⟨hL.ne'⟩
    obtain ⟨f, hf⟩ := GlobalTheory.EisM.modularForm_gammaOne_of_MF k (N * l) N χ a hL (dvd_mul_right N l) ha
    have hF : slz k δ (qs a) = ⇑f ∣[(k : ℤ)] GlobalTheory.HeckeFamilyMatrices.toGL δ := by rw [hf]; exact slz_eq_slash k hk δ hδ _
    let F : ModularForm (Gamma1 (N * l)) (k : ℤ) :=
      { toFun := slz k δ (qs a)
        slash_action_eq' := by
          rintro _ ⟨A, (hA : A ∈ Gamma1 (N * l)), rfl⟩
          exact GlobalTheory.EisM.OnGammaOne.slash_inv (dvd_mul_right N l) hinv A hA
        holo' := by
          show MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (slz k δ (qs a))
          rw [hF]; exact (ModularFormClass.holo f).slash _ _
        bdd_at_cusps' := by
          intro c hc
          show c.IsBoundedAt (slz k δ (qs a)) (k : ℤ)
          rw [hF, ← OnePoint.IsBoundedAt.smul_iff]
          apply ModularFormClass.bdd_at_cusps f
          rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
          exact GlobalTheory.HeckeFamilyMatrices.isCusp_SL2Z_toGL_smul δ hδ.ne' hc }
    refine ⟨coef F, ?_, qs_coef_of_mfc F⟩
    have hb := ModularFormClass.qExpansion_isBigO (Int.natCast_nonneg k) F
    simp only [strictWidthInfty_Gamma1, zpow_natCast] at hb
    exact polyB_of_isBigO hb
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.AtkinLehnerSlashIsModularFormCoeffSeqStatement

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.atkinLehner_slash_isModularFormCoeffSeq : ∀ (k N l : ℕ) (χ : DirichletCharacter ℂ N) (a : ℕ → ℂ) (a₀ b₀ c₀ d₀ : ℤ), N * a₀ * d₀ - l * b₀ * c₀ = 1 → 1 ≤ k → 0 < N → MF k (N * l) (ch χ) a → ∃ a' : ℕ → ℂ, MF k (N * l) (ch χ⁻¹) a' ∧ qs a' = slz k !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] (qs a) := by
  first | exact @GlobalTheory.EisM.atkinLehner_MF | exact GlobalTheory.EisM.atkinLehner_MF | (intros; apply GlobalTheory.EisM.atkinLehner_MF <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.EigenfunctionalAllCharactersOfAtkinLehner

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem lam_add' (B : ℕ) (c a b : ℕ → ℂ) : lam B c (a + b) = lam B c a + lam B c b := by
  simp only [lam, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem lam_smul' (B : ℕ) (c a : ℕ → ℂ) (z : ℂ) : lam B c (z • a) = z * lam B c a := by
  simp only [lam, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem slz_add' (k : ℕ) (δ : M2) (f g : ℍ → ℂ) : slz k δ (f + g) = slz k δ f + slz k δ g := by
  funext τ; simp only [slz, Pi.add_apply]; ring

theorem slz_smul' (k : ℕ) (δ : M2) (z : ℂ) (f : ℍ → ℂ) : slz k δ (z • f) = z • slz k δ f := by
  funext τ; simp only [slz, Pi.smul_apply, smul_eq_mul]; ring

theorem eigAll_of_atkinLehner : ∀ (k N l : ℕ) (χ : DirichletCharacter ℂ N) (g : ℕ → ℂ) (α : ℂ) (B : ℕ) (c : ℕ → ℂ)
    (a₀ b₀ c₀ d₀ : ℤ), N * a₀ * d₀ - l * b₀ * c₀ = 1 → 1 ≤ k → 0 < N → l.Prime → ¬ l ∣ N →
    EigF k N l χ⁻¹ (fun q => χ⁻¹ q * g q) α B c → ∃ (B' : ℕ) (c' : ℕ → ℂ), EigAll k N l χ g (χ l * α) B' c' ∧
    ∀ a a', MF k (N * l) (ch χ) a → MF k (N * l) (ch χ⁻¹) a' →
      qs a' = slz k !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] (qs a) → lam B' c' a = lam B c a' := by
  intro k N l χ g α B c a₀ b₀ c₀ d₀ hdet hk hN hl hlN hE
  set δ : M2 := !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] with hδ
  have hL : 0 < N * l := Nat.mul_pos hN hl.pos
  obtain ⟨hz1, hadd1, hsm1, -, -, -⟩ := mf_linear k (N * l) (ch χ)
  obtain ⟨hz2, hadd2, hsm2, -, -, -⟩ := mf_linear k (N * l) (ch χ⁻¹)

  have uniq : ∀ x y, MF k (N * l) (ch χ⁻¹) x → MF k (N * l) (ch χ⁻¹) y → qs x = qs y → x = y :=
    fun x y hx hy h => qs_injective x y hx.1 hy.1 h
  let S : Set (ℕ → ℂ) := {a | MF k (N * l) (ch χ) a}
  classical
  let φ : (ℕ → ℂ) → ℂ := fun a =>
    if h : ∃ a', MF k (N * l) (ch χ⁻¹) a' ∧ qs a' = slz k δ (qs a) then lam B c h.choose else 0
  have hφ : ∀ a a', MF k (N * l) (ch χ⁻¹) a' → qs a' = slz k δ (qs a) → φ a = lam B c a' := by
    intro a a' h1 h2
    have h : ∃ a', MF k (N * l) (ch χ⁻¹) a' ∧ qs a' = slz k δ (qs a) := ⟨a', h1, h2⟩
    simp only [φ, dif_pos h]
    rw [uniq _ _ h.choose_spec.1 h1 (h.choose_spec.2.trans h2.symm)]
  have hex : ∀ a, MF k (N * l) (ch χ) a → ∃ a', MF k (N * l) (ch χ⁻¹) a' ∧ qs a' = slz k δ (qs a) :=
    fun a ha => GlobalTheory.T.atkinLehner_slash_isModularFormCoeffSeq k N l χ a a₀ b₀ c₀ d₀ hdet hk hN ha
  obtain ⟨B₀, hB₀⟩ := sturm_coef_zero k (N * l) N χ hL (dvd_mul_right N l)
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.func_eq_lam S B₀ φ hz1
    (by
      intro a ha b hb
      obtain ⟨a', ha', ea⟩ := hex a ha
      obtain ⟨b', hb', eb⟩ := hex b hb
      obtain ⟨hab, hqab⟩ := hadd1 a b ha hb
      obtain ⟨hab', hqab'⟩ := hadd2 a' b' ha' hb'
      refine ⟨hab, ?_⟩
      rw [hφ a a' ha' ea, hφ b b' hb' eb, hφ (a + b) (a' + b') hab' (by rw [hqab', hqab, slz_add', ea, eb]),
        lam_add'])
    (by
      intro z a ha
      obtain ⟨a', ha', ea⟩ := hex a ha
      obtain ⟨hza, hqza⟩ := hsm1 z a ha
      obtain ⟨hza', hqza'⟩ := hsm2 z a' ha'
      refine ⟨hza, ?_⟩
      rw [hφ a a' ha' ea, hφ (z • a) (z • a') hza' (by rw [hqza', hqza, slz_smul', ea]), lam_smul'])
    (fun a ha h => hB₀ a ha h)
  obtain ⟨B', c', hagree, hkill⟩ := GlobalTheory.T.exists_lam_eq_and_vanishes_off_character k (N * l) N χ B₀ c₁ hL (dvd_mul_right N l)
  have key : ∀ a a', MF k (N * l) (ch χ) a → MF k (N * l) (ch χ⁻¹) a' → qs a' = slz k δ (qs a) →
      lam B' c' a = lam B c a' := by
    intro a a' ha ha' e
    rw [hagree a ha, ← hc₁ a ha, hφ a a' ha' e]
  refine ⟨B', c', ⟨⟨?_, ?_⟩, hkill⟩, key⟩
  · intro a ha q hq hqNl
    obtain ⟨a', ha', ea⟩ := hex a ha
    have hqN : ¬ q ∣ N := fun h => hqNl (dvd_mul_of_dvd_left h l)
    obtain ⟨hT, -⟩ := GlobalTheory.T.atkinLehner_intertwines_hecke_operators k N l χ a a' a₀ b₀ c₀ d₀ hdet hk hN hl hlN ha ha' ea
    have hTa : MF k (N * l) (ch χ) (To k (ch χ q) q a) :=
      GlobalTheory.T.isModularFormCoeffSeq_heckeT_of_prime_not_dvd k (N * l) N q χ a hk (dvd_mul_right N l) hq hqNl ha
    have hTa' : MF k (N * l) (ch χ⁻¹) (To k (ch χ⁻¹ q) q a') :=
      GlobalTheory.T.isModularFormCoeffSeq_heckeT_of_prime_not_dvd k (N * l) N q χ⁻¹ a' hk (dvd_mul_right N l) hq hqNl ha'
    obtain ⟨hs, hqs⟩ := hsm2 (ch χ q) _ hTa'
    rw [key _ _ hTa hs (by rw [hqs, hT q hq hqNl]), lam_smul', hE.T a' ha' q hq hqNl, key a a' ha ha' ea]
    have hunit : IsUnit ((q : ℕ) : ZMod N) := by
      rw [ZMod.isUnit_iff_coprime]
      exact (Nat.Prime.coprime_iff_not_dvd hq).mpr hqN
    have h1 : χ (q : ZMod N) * χ⁻¹ (q : ZMod N) = 1 := by
      rw [show χ (q : ZMod N) * χ⁻¹ (q : ZMod N) = (χ * χ⁻¹) (q : ZMod N) by rw [MulChar.coeToFun_mul]; rfl,
        mul_inv_cancel, MulChar.one_apply hunit]
    simp only [ch, Int.cast_natCast]
    linear_combination (g q * lam B c a') * h1
  · intro a ha
    obtain ⟨a', ha', ea⟩ := hex a ha
    obtain ⟨-, hU⟩ := GlobalTheory.T.atkinLehner_intertwines_hecke_operators k N l χ a a' a₀ b₀ c₀ d₀ hdet hk hN hl hlN ha ha' ea
    have hper : ∀ (ε : DirichletCharacter ℂ N) (d : ℤ), ch ε (d + (N * l : ℕ)) = ch ε d := by
      intro ε d
      simp [ch]
    have hUa := (GlobalTheory.T.isModularFormCoeffSeq_heckeU_and_depletion k (N * l) l (ch χ) a hk hl (dvd_mul_left l N) (hper χ) ha).1
    have hUa' := (GlobalTheory.T.isModularFormCoeffSeq_heckeU_and_depletion k (N * l) l (ch χ⁻¹) a' hk hl (dvd_mul_left l N) (hper χ⁻¹) ha').1
    obtain ⟨hs, hqs⟩ := hsm2 (ch χ l) _ hUa'
    rw [key _ _ hUa hs (by rw [hqs, hU]), lam_smul', hE.U a' ha', key a a' ha ha' ea]
    simp only [ch, Int.cast_natCast]
    ring

end GlobalTheory.EisM
end
end
