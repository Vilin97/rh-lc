module

public import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffHeckeUVCauchyProductIdentitiesStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffHeckeVOperatorRaisesLevelStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormConjugateCoefficientsInvCharStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSturmBoundIsModularFormCoeffSeq
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
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HalfPeterssonIntegralHeckeTAdjointStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HalfPeterssonIntegralHeckeUAdjointStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasModerateGrowthQExpansionOfCoeffPolynomialGrowStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrablePeterssonIntegrandModerateGrowthStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionPolyGrowthSummableContinuousStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsModularFormCoeffSeqHeckeTOfPrimeNotDvdStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsModularFormCoeffSeqHeckeUAndDepletionStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LinearFunctionalEqCoeffLinearCombinationFiniteStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormCoeffSeqLinearStructureStatement
public import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumSlashHeckeRepLowerHeckeVEigenform
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSturmBoundIsModularFormCoeffSeqStatement

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.exists_sturmBound_isModularFormCoeffSeq : ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N), 0 < L → N ∣ L → ∃ B : ℕ, ∀ a, MF k L (ch ε) a → (∀ n < B, a n = 0) → a = 0 := by
  first | exact @GlobalTheory.EisM.sturm_coef_zero | exact GlobalTheory.EisM.sturm_coef_zero | (intros; apply GlobalTheory.EisM.sturm_coef_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.HalfPeterssonIntegralWeightedLinearForms

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem qs_lin (a b : ℕ → ℂ) (x y : ℂ) (ha : PolyB a) (hb : PolyB b) (τ : ℍ) :
    qs (x • a + y • b) τ = x * qs a τ + y * qs b τ := by
  have sa : Summable fun n : ℕ => a n * cexp (2 * π * Complex.I * n * τ) :=
    ((GlobalTheory.T.qExpansion_polyGrowth_summable_continuous a ha).1 τ).of_norm
  have sb : Summable fun n : ℕ => b n * cexp (2 * π * Complex.I * n * τ) :=
    ((GlobalTheory.T.qExpansion_polyGrowth_summable_continuous b hb).1 τ).of_norm
  unfold qs
  rw [← tsum_mul_left, ← tsum_mul_left, ← (sa.mul_left x).tsum_add (sb.mul_left y)]
  congr 1; funext n; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

theorem pet_linear : ∀ (k L L' N : ℕ) (ε : DirichletCharacter ℂ N) (ρ : ℍ → ℝ), 1 ≤ k → 0 < L' → N ∣ L' → Wt L ρ → (∀ (h a b : ℕ → ℂ) (x y : ℂ), CF k L' (ch ε) h → PolyB a → PolyB b → pet k ρ (qs h) (qs (x • a + y • b)) = x * pet k ρ (qs h) (qs a) + y * pet k ρ (qs h) (qs b)) ∧ ∀ (h h' a : ℕ → ℂ) (x y : ℂ), CF k L' (ch ε) h → CF k L' (ch ε) h' → PolyB a → pet k ρ (fun τ => x * qs h τ + y * qs h' τ) (qs a) = conj x * pet k ρ (qs h) (qs a) + conj y * pet k ρ (qs h') (qs a) := by
  intro k L L' N ε ρ hk hL' hN hW
  have intg : ∀ h a : ℕ → ℂ, CF k L' (ch ε) h → PolyB a →
      Integrable (fun τ : ℍ => (ρ τ : ℂ) * (conj (qs h τ) * qs a τ * (τ.im : ℂ) ^ k)) := by
    intro h a hh ha
    exact GlobalTheory.T.integrable_petersson_integrand_moderateGrowth k L L' N ε h ρ (qs a) hk hL' hN hW hh
      (GlobalTheory.T.qExpansion_polyGrowth_summable_continuous a ha).2.aestronglyMeasurable (GlobalTheory.T.hasModerateGrowth_qExpansion_of_coeffPolynomialGrowth a ha)
  refine ⟨?_, ?_⟩
  · intro h a b x y hh ha hb
    unfold pet
    have e : (fun τ : ℍ => (ρ τ : ℂ) * (conj (qs h τ) * qs (x • a + y • b) τ * (τ.im : ℂ) ^ k)) =
        fun τ => x * ((ρ τ : ℂ) * (conj (qs h τ) * qs a τ * (τ.im : ℂ) ^ k)) +
          y * ((ρ τ : ℂ) * (conj (qs h τ) * qs b τ * (τ.im : ℂ) ^ k)) := by
      funext τ; rw [qs_lin a b x y ha hb τ]; ring
    rw [e, integral_add ((intg h a hh ha).const_mul x) ((intg h b hh hb).const_mul y),
      integral_const_mul, integral_const_mul]
  · intro h h' a x y hh hh' ha
    unfold pet
    have e : (fun τ : ℍ => (ρ τ : ℂ) * (conj (x * qs h τ + y * qs h' τ) * qs a τ * (τ.im : ℂ) ^ k)) =
        fun τ => conj x * ((ρ τ : ℂ) * (conj (qs h τ) * qs a τ * (τ.im : ℂ) ^ k)) +
          conj y * ((ρ τ : ℂ) * (conj (qs h' τ) * qs a τ * (τ.im : ℂ) ^ k)) := by
      funext τ; simp only [map_add (f := _), map_mul]; ring
    rw [e, integral_add ((intg h a hh ha).const_mul _) ((intg h' a hh' ha).const_mul _),
      integral_const_mul, integral_const_mul]

end GlobalTheory.EisM
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.HalfPeterssonIntegralWeightedLinearFormsStatement

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.halfPeterssonIntegralWeighted_linear_forms : ∀ (k L L' N : ℕ) (ε : DirichletCharacter ℂ N) (ρ : ℍ → ℝ), 1 ≤ k → 0 < L' → N ∣ L' → Wt L ρ → (∀ (h a b : ℕ → ℂ) (x y : ℂ), CF k L' (ch ε) h → PolyB a → PolyB b → pet k ρ (qs h) (qs (x • a + y • b)) = x * pet k ρ (qs h) (qs a) + y * pet k ρ (qs h) (qs b)) ∧ ∀ (h h' a : ℕ → ℂ) (x y : ℂ), CF k L' (ch ε) h → CF k L' (ch ε) h' → PolyB a → pet k ρ (fun τ => x * qs h τ + y * qs h' τ) (qs a) = conj x * pet k ρ (qs h) (qs a) + conj y * pet k ρ (qs h') (qs a) := by
  first | exact @GlobalTheory.EisM.pet_linear | exact GlobalTheory.EisM.pet_linear | (intros; apply GlobalTheory.EisM.pet_linear <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumSlashHeckeRepLowerHeckeVEigenformStatement

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.sum_slash_heckeRepLower_heckeV_eigenform : ∀ (k N l : ℕ) (ε : DirichletCharacter ℂ N) (h : ℕ → ℂ) (t : ℂ), 1 ≤ k → 0 < N → l.Prime → ¬ l ∣ N → MF k N (ch ε) h → To k (ch ε l) l h = t • h → ∀ τ : ℍ, ∑ j : Fin l, slz k (repL (N * l) l (some j)) (qs (Vo l h)) τ = ch ε⁻¹ l * (t * qs (Vo l h) τ - (l : ℂ)⁻¹ * qs h τ) := by
  first | exact @GlobalTheory.EisM.sum_slz_repL_Vo | exact GlobalTheory.EisM.sum_slz_repL_Vo | (intros; apply GlobalTheory.EisM.sum_slz_repL_Vo <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumSlashHeckeRepLowerLevelEqPowMulHeckeV

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

theorem qExpansionFunction_coeffHeckeVOperator_eq_tsum (l : ℕ) (hl : 0 < l) (a : ℕ → ℂ) (τ : ℍ) :
    qs (Vo l a) τ = ∑' m : ℕ, a m * cexp (2 * π * Complex.I * m * ((l : ℂ) * τ)) := by
  unfold qs Vo
  have hinj : Function.Injective (fun m : ℕ => l * m) := fun x y h => by
    simpa [hl.ne'] using h
  rw [← hinj.tsum_eq]
  · congr 1; ext m
    simp only [dvd_mul_right, if_true, Nat.mul_div_cancel_left m hl]
    congr 2; push_cast; ring
  · intro n hn
    by_cases h : l ∣ n
    · obtain ⟨m, rfl⟩ := h; exact ⟨m, rfl⟩
    · simp [Function.mem_support, h] at hn

theorem adjU_sum (k N l : ℕ) (ε : DirichletCharacter ℂ N) (h : ℕ → ℂ) (hk : 1 ≤ k) (hl : 0 < l)
    (hf : MF k N (ch ε) h) (τ : ℍ) :
    ∑ j : Fin l, slz k (repL (N * l) l (some j)) (qs h) τ = (l : ℂ) ^ k * qs (Vo l h) τ := by
  have hlC : (0 : ℝ) < l := by exact_mod_cast hl
  let τ' : ℍ := ⟨(l : ℂ) * τ, by simpa using mul_pos hlC τ.im_pos⟩
  have hτ' : (τ' : ℂ) = (l : ℂ) * τ := rfl
  have key : ∀ j : Fin l, slz k (repL (N * l) l (some j)) (qs h) τ = (l : ℂ) ^ (k - 1) * qs h τ' := by
    intro j
    let γ : SL(2, ℤ) := ⟨!![1, 0; (N * (j : ℕ) : ℤ), 1], by simp [Matrix.det_fin_two]⟩
    have hγ := hf.2 γ (by simp [γ]) τ'
    have hpt : ((γ • τ' : ℍ) : ℂ) = ((l : ℂ) * τ) / (((N * l * (j : ℕ) : ℕ) : ℂ) * τ + 1) := by
      rw [coe_specialLinearGroup_apply]; simp [γ, hτ']; ring
    have hden : ((((N * (j : ℕ) : ℤ)) : ℂ) * (τ' : ℂ) + 1) = (((N * l * (j : ℕ) : ℕ) : ℂ) * τ + 1) := by
      rw [hτ']; push_cast; ring
    have hne : (((N * l * (j : ℕ) : ℕ) : ℂ) * τ + 1) ≠ 0 := by
      intro h0
      have := congrArg Complex.im h0
      simp at this
      rcases this with h1 | h1
      · have h2 : N * l * (j : ℕ) = 0 := by rcases h1 with (h1 | h1) | h1 <;> simp [h1]
        simp [h2] at h0
      · exact (τ.im_pos.ne' h1)
    have hγ' : qs h (γ • τ') = (((N * l * (j : ℕ) : ℕ) : ℂ) * τ + 1) ^ k * qs h τ' := by
      rw [← hden, hγ]; simp [γ, ch]
    have harg : ((l : ℂ) * τ / ((N : ℂ) * l * ((j : ℕ) : ℂ) * τ + 1)) = ((γ • τ' : ℍ) : ℂ) := by
      rw [hpt]; push_cast; ring
    unfold slz repL
    simp [Matrix.det_fin_two]
    rw [harg, ofComplex_apply, hγ']
    push_cast at hne ⊢
    field_simp
  simp only [key, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [qExpansionFunction_coeffHeckeVOperator_eq_tsum l hl h τ]
  have hp : (l : ℂ) * (l : ℂ) ^ (k - 1) = (l : ℂ) ^ k := by
    rw [← pow_succ', Nat.sub_add_cancel hk]
  rw [← mul_assoc, hp]
  rfl
end GlobalTheory.EisM

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumSlashHeckeRepLowerLevelEqPowMulHeckeVStatement

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.sum_slash_heckeRepLowerLevel_eq_pow_mul_heckeV : ∀ (k N l : ℕ) (ε : DirichletCharacter ℂ N) (h : ℕ → ℂ), 1 ≤ k → 0 < l → MF k N (ch ε) h → ∀ τ : ℍ, ∑ j : Fin l, slz k (repL (N * l) l (some j)) (qs h) τ = (l : ℂ) ^ k * qs (Vo l h) τ := by
  first | exact @GlobalTheory.EisM.adjU_sum | exact GlobalTheory.EisM.adjU_sum | (intros; apply GlobalTheory.EisM.adjU_sum <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHeckeEigenfunctionalOfDepletedEigenform

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem eigF_of_prim : ∀ (k N l : ℕ) (χ : DirichletCharacter ℂ N) (g : ℕ → ℂ) (ρ : ℍ → ℝ) (α β : ℂ), 1 ≤ k → 0 < N → l.Prime → ¬ l ∣ N → Prim k N χ g → Wt (N * l) ρ → α + β = χ⁻¹ l * g l → α * β = χ⁻¹ l * (l : ℂ) ^ (k - 1) → ∃ (B : ℕ) (c : ℕ → ℂ), EigF k N l χ⁻¹ (fun q => χ⁻¹ q * g q) α B c ∧ ∀ a, MF k (N * l) (ch χ⁻¹) a → lam B c a = pet k ρ (qs (Vo l fun n => conj (g n))) (qs a) - β / (l : ℂ) ^ k * pet k ρ (qs fun n => conj (g n)) (qs a) := by
  intro k N l χ g ρ α β hk hN hl hlN hg hρ hab hαβ
  haveI : NeZero N := ⟨by omega⟩
  set h : ℕ → ℂ := fun n => conj (g n) with hh_def
  have hNl : 0 < N * l := Nat.mul_pos hN hl.pos
  have hdvd : N ∣ N * l := dvd_mul_right N l
  have hP : Prim k N χ⁻¹ h := (GlobalTheory.T.cuspForm_conjugate_coefficients_inv_char k N χ g).2 hg
  have hMFh : MF k N (ch χ⁻¹) h := hP.cf.1
  have lin := GlobalTheory.T.modularFormCoeffSeq_linear_structure k (N * l) (ch χ⁻¹)
  have hCFh : CF k (N * l) (ch χ⁻¹) h := (GlobalTheory.T.modularFormCoeffSeq_linear_structure k N (ch χ⁻¹)).2.2.2.2.2 (N * l) h hdvd hP.cf
  have hCFV : CF k (N * l) (ch χ⁻¹) (Vo l h) := (GlobalTheory.T.coeffHeckeVOperator_raises_level k N l (ch χ⁻¹) h hl.pos).2 hP.cf
  have petlin := GlobalTheory.T.halfPeterssonIntegralWeighted_linear_forms k (N * l) (N * l) N χ⁻¹ ρ hk hNl hdvd hρ

  have hsc : ∀ (h' a : ℕ → ℂ) (x : ℂ), CF k (N * l) (ch χ⁻¹) h' → MF k (N * l) (ch χ⁻¹) a →
      pet k ρ (qs (x • h')) (qs a) = conj x * pet k ρ (qs h') (qs a) := by
    intro h' a x hh' ha
    have e : qs (x • h') = fun τ => x * qs h' τ + 0 * qs h' τ := by
      rw [(lin.2.2.1 x h' hh'.1).2]; funext τ; simp
    rw [e, petlin.2 h' h' a x 0 hh' hh' ha.1]; simp
  have hconj : ∀ x : ZMod N, conj (χ x) = χ⁻¹ x := fun x => MulChar.star_apply' χ x
  have hch : ∀ n : ℕ, ch χ⁻¹ (n : ℤ) = χ⁻¹ (n : ZMod N) := by intro n; simp [ch]
  set φ : (ℕ → ℂ) → ℂ := fun a => pet k ρ (qs (Vo l h)) (qs a) - β / (l : ℂ) ^ k * pet k ρ (qs h) (qs a) with hφ_def
  obtain ⟨B, hB⟩ := GlobalTheory.T.exists_sturmBound_isModularFormCoeffSeq k (N * l) N χ⁻¹ hNl hdvd
  obtain ⟨c, hc⟩ := GlobalTheory.T.linearFunctional_eq_coeffLinearCombinationFinite {a | MF k (N * l) (ch χ⁻¹) a} B φ lin.1
    (by
      intro a ha b hb
      refine ⟨(lin.2.1 a b ha hb).1, ?_⟩
      have e1 := petlin.1 (Vo l h) a b 1 1 hCFV ha.1 hb.1
      have e2 := petlin.1 h a b 1 1 hCFh ha.1 hb.1
      simp only [one_smul, one_mul] at e1 e2
      simp only [hφ_def, e1, e2]; ring)
    (by
      intro x a ha
      refine ⟨(lin.2.2.1 x a ha).1, ?_⟩
      have e1 := petlin.1 (Vo l h) a a x 0 hCFV ha.1 ha.1
      have e2 := petlin.1 h a a x 0 hCFh ha.1 ha.1
      simp only [zero_smul, add_zero, zero_mul] at e1 e2
      simp only [hφ_def, e1, e2]; ring)
    hB
  have hφ : ∀ a, MF k (N * l) (ch χ⁻¹) a → lam B c a = φ a := fun a ha => (hc a ha).symm
  refine ⟨B, c, ⟨?_, ?_⟩, hφ⟩
  ·
    intro a ha q hq hqNl
    have hqN : ¬ q ∣ N := fun d => hqNl (dvd_mul_of_dvd_left d l)
    have hql : q ≠ l := fun e => hqNl (e ▸ dvd_mul_left q N)
    have hcop : q.Coprime l := (Nat.coprime_primes hq hl).2 hql
    have hTa := GlobalTheory.T.isModularFormCoeffSeq_heckeT_of_prime_not_dvd k (N * l) N q χ⁻¹ a hk hdvd hq hqNl ha
    rw [hφ _ hTa, hφ _ ha]
    have eigh : To k (ch χ⁻¹ q) q h = h q • h := by
      rw [hP.eig q hq hqN]; funext n; simp
    have eigV : To k (ch χ⁻¹ q) q (Vo l h) = h q • Vo l h := by
      rw [(GlobalTheory.T.coeffHecke_UV_cauchyProduct_identities ℂ l hl.pos).2.2.2.2.1 k q _ h hcop hq.pos, eigh]
      funext n; simp only [Vo, Pi.smul_apply, smul_eq_mul]; split_ifs <;> simp
    have adj0 := GlobalTheory.T.halfPeterssonIntegral_heckeT_adjoint k (N * l) N q χ⁻¹ ρ h a hk hNl hdvd hq hqNl hρ hCFh ha
    have adj1 := GlobalTheory.T.halfPeterssonIntegral_heckeT_adjoint k (N * l) N q χ⁻¹ ρ (Vo l h) a hk hNl hdvd hq hqNl hρ hCFV ha
    rw [eigh, hsc h a _ hCFh ha] at adj0
    rw [eigV, hsc (Vo l h) a _ hCFV ha] at adj1
    have hgq : conj (h q) = g q := by simp [hh_def]
    simp only [hφ_def]
    rw [adj0, adj1]
    simp only [hgq, hch]
    ring
  ·
    intro a ha
    have hper : ∀ d : ℤ, ch χ⁻¹ (d + ((N * l : ℕ) : ℤ)) = ch χ⁻¹ d := by
      intro d; simp only [ch]; congr 1; push_cast; simp
    have hUa := (GlobalTheory.T.isModularFormCoeffSeq_heckeU_and_depletion k (N * l) l (ch χ⁻¹) a hk hl (dvd_mul_left l N) hper ha).1
    rw [hφ _ hUa, hφ _ ha]
    have adjU0 := GlobalTheory.T.halfPeterssonIntegral_heckeU_adjoint k (N * l) N l χ⁻¹ ρ h a hk hNl hdvd hl (dvd_mul_left l N) hlN hρ hCFh ha
    have adjU1 := GlobalTheory.T.halfPeterssonIntegral_heckeU_adjoint k (N * l) N l χ⁻¹ ρ (Vo l h) a hk hNl hdvd hl (dvd_mul_left l N) hlN hρ hCFV ha
    have tr0 := GlobalTheory.T.sum_slash_heckeRepLowerLevel_eq_pow_mul_heckeV k N l χ⁻¹ h hk hl.pos hMFh
    have eigl : To k (ch χ⁻¹ l) l h = h l • h := by
      rw [hP.eig l hl hlN]; funext n; simp
    have tr1 := GlobalTheory.T.sum_slash_heckeRepLower_heckeV_eigenform k N l χ⁻¹ h (h l) hk hN hl hlN hMFh eigl
    have f0 : (fun τ => ∑ j : Fin l, slz k (repL (N * l) l (some j)) (qs h) τ)
        = fun τ => ((l : ℂ) ^ k) * qs (Vo l h) τ + 0 * qs (Vo l h) τ := by
      funext τ; rw [tr0]; ring
    have f1 : (fun τ => ∑ j : Fin l, slz k (repL (N * l) l (some j)) (qs (Vo l h)) τ)
        = fun τ => (ch χ⁻¹⁻¹ l * h l) * qs (Vo l h) τ + (-(ch χ⁻¹⁻¹ l * (l : ℂ)⁻¹)) * qs h τ := by
      funext τ; rw [tr1]; ring
    rw [f0, petlin.2 (Vo l h) (Vo l h) a _ 0 hCFV hCFV ha.1] at adjU0
    rw [f1, petlin.2 (Vo l h) h a _ _ hCFV hCFh ha.1] at adjU1
    have e1 : conj (ch χ⁻¹⁻¹ (l : ℤ)) = χ⁻¹ (l : ZMod N) := by
      rw [inv_inv]; simp only [ch, Int.cast_natCast]; exact hconj _
    have hgl : conj (h l) = g l := by simp [hh_def]
    have hl0 : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne_zero
    have key : (l : ℂ) ^ (k - 1) / (l : ℂ) ^ k = (l : ℂ)⁻¹ := by
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      simp only [Nat.add_sub_cancel, pow_succ]; field_simp
    simp only [map_mul, map_neg, map_inv₀, map_pow, Complex.conj_natCast, map_zero, e1, hgl, zero_mul, add_zero] at adjU0 adjU1
    simp only [hφ_def, adjU0, adjU1]
    set P0 := pet k ρ (qs h) (qs a)
    set P1 := pet k ρ (qs (Vo l h)) (qs a)
    have hcan : (l : ℂ) ^ k / (l : ℂ) ^ k = 1 := div_self (pow_ne_zero _ hl0)
    linear_combination (-P1) * hab + (P0 / (l : ℂ) ^ k) * hαβ + (χ⁻¹ (l : ZMod N) * P0) * key + (-β * P1) * hcan

end GlobalTheory.EisM
end
end
