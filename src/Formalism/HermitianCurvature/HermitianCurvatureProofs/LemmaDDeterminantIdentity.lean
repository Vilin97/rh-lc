module

public import Formalism.HermitianCurvature.StatementQ
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CovariantHatSqOfLin
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmIndep
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmRowForm
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmStar
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnCovDet
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnCovHat
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnCovLin
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnEabGl
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnEabPres
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnMinorLeft
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnRdSkew
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RightSingleRule.EllSingleZero
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnYLeibniz
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylConjugationFixedColumn.ReflectionScalarDualIsotropic
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialFirstColumn.FirstColumnSplitBijective
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowExpansionMinor.FirstColumnSplitBijective
public import Formalism.PeriodIntegrals.QmDefs
public import Formalism.PeriodIntegrals.ContractionsCovariantIff

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdaptedCharacterForm.SecondCapelliMinorStandardBasis

section

@[expose] public section

open Matrix Finset

namespace Formalism.FourierDecayAlt.Q.Adapted

open Formalism.REAL

theorem mulVec_col {n : ℕ} (P Q : Matrix (Fin n) (Fin n) ℂ) (h : Q * P = 1) (k : Fin n) :
    (Q *ᵥ fun p => P p k) = Pi.single k 1 := by
  funext i
  have h1 := congrFun (congrFun h i) k
  rw [Matrix.mul_apply, Matrix.one_apply] at h1
  simp only [Matrix.mulVec, dotProduct, h1, Pi.single_apply]

theorem chatA_single {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (u : ℂ)
    (l : Fin m) (γ : Fin m → ℂ) (hγ : ∀ j, j ≠ l → γ j = 0) :
    chatA E u (Pi.single l 1) γ = γ l • qminor E (skip1 l) (skip1 l) u := by
  unfold chatA
  rw [Finset.sum_eq_single l (fun i _ hi => ?_) (fun h => absurd (Finset.mem_univ l) h)]
  · rw [Finset.sum_eq_single l (fun j _ hj => ?_) (fun h => absurd (Finset.mem_univ l) h)]
    · congr 1
      rw [Pi.single_eq_same, mul_one, ← two_mul, pow_mul]
      norm_num
    · simp [Pi.single_apply, hj]
  · exact Finset.sum_eq_zero fun j _ => by simp [hγ i hi]

theorem coefA {n : ℕ} (j j' : Fin (n + 2)) (h : j < j') :
    (Pi.single 0 1 : Fin (n + 2) → ℂ) j * (Pi.single 1 1 : Fin (n + 2) → ℂ) j' -
      (Pi.single 0 1 : Fin (n + 2) → ℂ) j' * (Pi.single 1 1 : Fin (n + 2) → ℂ) j =
      if j = 0 ∧ j' = 1 then 1 else 0 := by
  have hC : j' ≠ 0 := by
    rintro rfl
    simp [Fin.lt_def] at h
  by_cases hA : j = 0 <;> by_cases hB : j' = 1 <;> simp [Pi.single_apply, hA, hB, hC]

theorem coefB {n : ℕ} (γ γ' : Fin (n + 2) → ℂ) (hγ : ∀ j : Fin (n + 2), 2 ≤ j.val → γ j = 0 ∧ γ' j = 0)
    (i i' : Fin (n + 2)) (h : i < i') (hne : ¬ (i = 0 ∧ i' = 1)) :
    γ i * γ' i' - γ i' * γ' i = 0 := by
  have hi' : 2 ≤ i'.val := by
    by_contra hlt
    push_neg at hlt
    apply hne
    have h1 : i.val < i'.val := h
    refine ⟨Fin.ext ?_, Fin.ext ?_⟩ <;> simp only [Fin.val_zero, Fin.val_one] <;> omega
  rw [(hγ i' hi').1, (hγ i' hi').2]
  ring

theorem second_capelli_minor_standard_basis {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin (n + 2) → Fin (n + 2) → A)
    (u : ℂ) (γ γ' : Fin (n + 2) → ℂ) (hγ : ∀ j : Fin (n + 2), 2 ≤ j.val → γ j = 0 ∧ γ' j = 0) :
    chat2A E u (Pi.single 0 1) (Pi.single 1 1) γ γ' =
      (γ 0 * γ' 1 - γ 1 * γ' 0) • qminor E (skip2 0 1) (skip2 0 1) u := by
  unfold chat2A
  have key : ∀ i i' j j' : Fin (n + 2),
      (if i < i' ∧ j < j' then
        ((-1) ^ ((i : ℕ) + (i' : ℕ) + (j : ℕ) + (j' : ℕ)) * (γ i * γ' i' - γ i' * γ' i) *
          ((Pi.single 0 1 : Fin (n + 2) → ℂ) j * (Pi.single 1 1 : Fin (n + 2) → ℂ) j' -
            (Pi.single 0 1 : Fin (n + 2) → ℂ) j' * (Pi.single 1 1 : Fin (n + 2) → ℂ) j)) •
          qminor E (skip2 i i') (skip2 j j') u
      else 0) =
      if j' = 1 ∧ j = 0 ∧ i' = 1 ∧ i = 0 then (γ 0 * γ' 1 - γ 1 * γ' 0) • qminor E (skip2 0 1) (skip2 0 1) u else 0 := by
    intro i i' j j'
    by_cases h : i < i' ∧ j < j'
    · rw [if_pos h, coefA j j' h.2]
      by_cases hii : i = 0 ∧ i' = 1
      · by_cases hjj : j = 0 ∧ j' = 1
        · obtain ⟨rfl, rfl⟩ := hii
          obtain ⟨rfl, rfl⟩ := hjj
          norm_num
        · rw [if_neg hjj, if_neg (show ¬(j' = 1 ∧ j = 0 ∧ i' = 1 ∧ i = 0) from fun h' => hjj ⟨h'.2.1, h'.1⟩),
            mul_zero, zero_smul]
      · rw [coefB γ γ' hγ i i' h.1 hii,
          if_neg (show ¬(j' = 1 ∧ j = 0 ∧ i' = 1 ∧ i = 0) from fun h' => hii ⟨h'.2.2.2, h'.2.2.1⟩),
          mul_zero, zero_mul, zero_smul]
    · rw [if_neg h, if_neg]
      rintro ⟨rfl, rfl, rfl, rfl⟩
      exact h ⟨by simp [Fin.lt_def], by simp [Fin.lt_def]⟩
  simp only [key]
  simp only [ite_and, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem chatAdapted_of (hcov : ContractionsCovariant) : ChatAdapted := by
  intro A _ _ n E P Q hE hQP hPQ u β hβ
  have h := (hcov A (n + 1) E P Q hE hQP hPQ u (fun p => P p (Fin.last n)) 0 β 0).2.1
  rw [← h, mulVec_col P Q hQP (Fin.last n)]
  exact chatA_single _ u (Fin.last n) (β ᵥ* P) hβ

theorem chat2Adapted_of (hcov : ContractionsCovariant) : Chat2Adapted := by
  intro A _ _ n E P Q hE hQP hPQ u β β' hβ
  have h := (hcov A (n + 2) E P Q hE hQP hPQ u (fun p => P p 0) (fun p => P p 1) β β').2.2
  rw [← h, mulVec_col P Q hQP 0, mulVec_col P Q hQP 1]
  exact second_capelli_minor_standard_basis _ u (β ᵥ* P) (β' ᵥ* P) hβ

end Formalism.FourierDecayAlt.Q.Adapted
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnAdapted

section

@[expose] public section

theorem contraction_adapted : Formalism.FourierDecayAlt.Q.ContractionsCovariant → Formalism.FourierDecayAlt.Q.ChatAdapted ∧ Formalism.FourierDecayAlt.Q.Chat2Adapted := by
  intro hcov
  exact ⟨Formalism.FourierDecayAlt.Q.Adapted.chatAdapted_of hcov, Formalism.FourierDecayAlt.Q.Adapted.chat2Adapted_of hcov⟩
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnRuleRight

section

@[expose] public section

theorem qnRuleRight : Formalism.FourierDecayAlt.Q.RuleRight := Formalism.FourierDecayAlt.Q.QRR.ruleRight_main
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WeylLevelElementProperties

section

@[expose] public section

theorem weyl_level_element_properties' : Formalism.FourierDecayAlt.Q.WeylLevelElementFacts :=
  PI.IsotropicReflections.isotropic_reflection_properties
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SkipSuccessorIndex.SkipSucc2

section

@[expose] public section

namespace PI.QmSkipWork

theorem val_succAbove {n : ℕ} (p : Fin (n + 1)) (k : Fin n) :
    (p.succAbove k).val = if k.val < p.val then k.val else k.val + 1 := by
  by_cases h : k.val < p.val
  · rw [if_pos h, Fin.succAbove_of_castSucc_lt p k (by simpa [Fin.lt_def] using h)]
    simp
  · rw [if_neg h, Fin.succAbove_of_le_castSucc p k (by simp [Fin.le_def]; omega)]
    simp

theorem skipSucc : PI.SkipSucc := by
  unfold PI.SkipSucc
  intro t i j
  apply Fin.ext
  rw [PI.QmSkipWork.val_succAbove]
  unfold PI.skip1
  split_ifs <;> rfl

theorem skipSucc2 : PI.SkipSucc2 := by
  unfold PI.SkipSucc2
  intro t i i' j hii'
  have hb : (i.succAbove i').val = i'.val + 1 := by
    rw [PI.QmSkipWork.val_succAbove, if_neg (by omega)]
  apply Fin.ext
  simp only [PI.QmSkipWork.val_succAbove]
  unfold PI.skip2
  split_ifs <;> (try dsimp only) <;> omega

end PI.QmSkipWork
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.LemmaDDeterminantIdentity

section

@[expose] public section

theorem Formalism.FourierDecayAlt.P.expansion_first_column : Formalism.FourierDecayAlt.Q.ExpFirstCol := PI.QmColExpWork.expFirstCol

theorem Formalism.FourierDecayAlt.P.expansion_last_column : Formalism.FourierDecayAlt.Q.ExpLastCol := PI.QmColExpWork.expLastCol

theorem Formalism.FourierDecayAlt.P.expansion_first_line : Formalism.FourierDecayAlt.Q.ExpFirstRow := PI.QmRowExpWork.expFirstRow_of quantum_minor_row_form

theorem Formalism.FourierDecayAlt.P.expansion_last_line : Formalism.FourierDecayAlt.Q.ExpLastRow := PI.QmRowExpWork.expLastRow_of quantum_minor_row_form

theorem Formalism.FourierDecayAlt.P.line_form_of_minor : Formalism.FourierDecayAlt.Q.RowForm := quantum_minor_row_form

theorem Formalism.FourierDecayAlt.P.skip_succ_identity : Formalism.FourierDecayAlt.Q.SkipSucc := PI.QmSkipWork.skipSucc

theorem Formalism.FourierDecayAlt.P.skip_succ_double_identity : Formalism.FourierDecayAlt.Q.SkipSucc2 := PI.QmSkipWork.skipSucc2

theorem Formalism.FourierDecayAlt.P.star_quantum_minor : Formalism.FourierDecayAlt.Q.StarMinor := quantum_minor_star

theorem Formalism.FourierDecayAlt.P.rtt_independence : Formalism.FourierDecayAlt.Q.RTTIndependence := rtt_independence'

theorem Formalism.FourierDecayAlt.P.contractions_covariant : Formalism.FourierDecayAlt.Q.ContractionsCovariant := PI.contractionsCovariant_iff.mpr ⟨covariant_det_of_lin covariant_linear, covariant_hat_of_lin covariant_linear, covariant_hat_sq_of_lin covariant_linear⟩

theorem Formalism.FourierDecayAlt.P.first_contraction_adapted : Formalism.FourierDecayAlt.Q.ChatAdapted := (contraction_adapted Formalism.FourierDecayAlt.P.contractions_covariant).1

theorem Formalism.FourierDecayAlt.P.second_contraction_adapted : Formalism.FourierDecayAlt.Q.Chat2Adapted := (contraction_adapted Formalism.FourierDecayAlt.P.contractions_covariant).2

theorem Formalism.FourierDecayAlt.P.generator_gl_level : Formalism.FourierDecayAlt.Q.EabGlLev := qnEabGl

theorem Formalism.FourierDecayAlt.P.generator_action_preserved : Formalism.FourierDecayAlt.Q.EabPres := qnEabPres

theorem Formalism.FourierDecayAlt.P.quantum_minor_left_hermitian : Formalism.FourierDecayAlt.Q.QMinorLeftH := quantum_minor_left

theorem Formalism.FourierDecayAlt.P.right_differential_skew : Formalism.FourierDecayAlt.Q.RdSkew := qnRdSkew

theorem Formalism.FourierDecayAlt.P.right_action_rule : Formalism.FourierDecayAlt.Q.RuleRight := qnRuleRight

theorem Formalism.FourierDecayAlt.P.weyl_level_element_properties : Formalism.FourierDecayAlt.Q.WeylLevelElementFacts := weyl_level_element_properties'

theorem Formalism.FourierDecayAlt.P.twisted_leibniz_rule : Formalism.FourierDecayAlt.Q.YLeibniz := qnYLeibniz
end
end
