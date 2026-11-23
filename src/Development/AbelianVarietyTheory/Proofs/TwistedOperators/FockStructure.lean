module

public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFockJointHarmonicsHighestWeightOfShape
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FischerDecompositionFockNoncompactParts
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicHomogeneousOfKType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJointHarmonicsHighestWeightEqBotOfNotShape
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightDegreeLeOfHomogeneousFockWeightVector
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFockJointHarmonicsHighestWeightOfShapeStatement

section

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

theorem _root_.GlobalTheory.T.finrank_fockJointHarmonics_highestWeight_of_shape : ∀ (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ), JointShape p q r s μ μ' → Module.finrank ℂ ↥(hwSub (fockAct1 p q r s) μ ⊓ hwSub (fockAct2 p q r s) μ' ⊓ Submodule.span ℂ (jointHarm p q r s)) = 1 := by
  first | exact @GlobalTheory.JointHarm.finrank_joint_highest_of_shape | exact GlobalTheory.JointHarm.finrank_joint_highest_of_shape | (intros; apply GlobalTheory.JointHarm.finrank_joint_highest_of_shape <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FischerDecompositionFockNoncompactPartsStatement

section

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

theorem _root_.GlobalTheory.T.fischerDecomposition_fockNoncompactParts : ∀ (p q r s d : ℕ), (homog (Ix p q × Ix r s) (d + 2) = (homog (Ix p q × Ix r s) (d + 2) ⊓ Submodule.span ℂ (harm2 p q r s)) ⊔ Submodule.span ℂ {R | ∃ Q ∈ homog (Ix p q × Ix r s) d, ∃ Z : Mat p q, IsPC Z ∧ R = plusPart (fockAct1 p q r s Z) Q}) ∧ (homog (Ix p q × Ix r s) (d + 2) = (homog (Ix p q × Ix r s) (d + 2) ⊓ Submodule.span ℂ (harm1 p q r s)) ⊔ Submodule.span ℂ {R | ∃ Q ∈ homog (Ix p q × Ix r s) d, ∃ Z : Mat r s, IsPC Z ∧ R = plusPart (fockAct2 p q r s Z) Q}) ∧ (homog (Ix p q × Ix r s) (d + 2) = (homog (Ix p q × Ix r s) (d + 2) ⊓ Submodule.span ℂ (jointHarm p q r s)) ⊔ Submodule.span ℂ {R | ∃ Q ∈ homog (Ix p q × Ix r s) d, (∃ Z : Mat p q, IsPC Z ∧ R = plusPart (fockAct1 p q r s Z) Q) ∨ ∃ Z : Mat r s, IsPC Z ∧ R = plusPart (fockAct2 p q r s Z) Q}) := by
  first | exact @GlobalTheory.FischerParts.fischer_parts | exact GlobalTheory.FischerParts.fischer_parts | (intros; apply GlobalTheory.FischerParts.fischer_parts <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicHomogeneousOfKTypeStatement

section

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

theorem _root_.GlobalTheory.T.fockHarmonic_homogeneous_of_KType : ∀ (p q r s : ℕ), (∀ (μ : Ix p q → ℚ) (P : Pol p q r s), P ≠ 0 → OfType (fockAct1 p q r s) μ P → P ∈ harm1 p q r s → ∃ d : ℕ, (d : ℚ) = degW (cPair r s) μ ∧ P ∈ homog (Ix p q × Ix r s) d) ∧ (∀ (μ : Ix r s → ℚ) (P : Pol p q r s), P ≠ 0 → OfType (fockAct2 p q r s) μ P → P ∈ harm2 p q r s → ∃ d : ℕ, (d : ℚ) = degW (cPair p q) μ ∧ P ∈ homog (Ix p q × Ix r s) d) := by
  first | exact @GlobalTheory.FockAlg.harmonic_homog_of_type | exact GlobalTheory.FockAlg.harmonic_homog_of_type | (intros; apply GlobalTheory.FockAlg.harmonic_homog_of_type <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJointHarmonicsHighestWeightEqBotOfNotShapeStatement

section

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

theorem _root_.GlobalTheory.T.fockJointHarmonics_highestWeight_eq_bot_of_not_shape : ∀ (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ), ¬ JointShape p q r s μ μ' → hwSub (fockAct1 p q r s) μ ⊓ hwSub (fockAct2 p q r s) μ' ⊓ Submodule.span ℂ (jointHarm p q r s) = ⊥ := by
  first | exact @GlobalTheory.FockAlg.jointHarm_hw_eq_bot | exact GlobalTheory.FockAlg.jointHarm_hw_eq_bot | (intros; apply GlobalTheory.FockAlg.jointHarm_hw_eq_bot <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightDegreeLeOfHomogeneousFockWeightVectorStatement

section

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

theorem _root_.GlobalTheory.T.weightDegree_le_of_homogeneous_fockWeightVector : ∀ (p q r s : ℕ), (∀ (d : ℕ) (μ : Ix p q → ℚ) (P : Pol p q r s), P ∈ homog (Ix p q × Ix r s) d → P ≠ 0 → P ∈ wtSub (fockAct1 p q r s) μ → degW (cPair r s) μ ≤ d) ∧ (∀ (d : ℕ) (μ : Ix r s → ℚ) (P : Pol p q r s), P ∈ homog (Ix p q × Ix r s) d → P ≠ 0 → P ∈ wtSub (fockAct2 p q r s) μ → degW (cPair p q) μ ≤ d) := by
  first | exact @GlobalTheory.FockAlg.degW_le_of_homog_wtSub | exact GlobalTheory.FockAlg.degW_le_of_homog_wtSub | (intros; apply GlobalTheory.FockAlg.degW_le_of_homog_wtSub <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockStructure

section

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg

namespace GlobalTheory.FockAlg

theorem fock_structure : ∀ X : ProvA, admH2 X := by
  intro X p q r s
  refine ⟨fun d μ P hP hw => (GlobalTheory.T.weightDegree_le_of_homogeneous_fockWeightVector p q r s).1 d μ P hP hw.1 hw.2.1,
    fun d μ P hP hw => (GlobalTheory.T.weightDegree_le_of_homogeneous_fockWeightVector p q r s).2 d μ P hP hw.1 hw.2.1,
    fun μ P h0 ht hh => (GlobalTheory.T.fockHarmonic_homogeneous_of_KType p q r s).1 μ P h0 ht hh,
    fun μ P h0 ht hh => (GlobalTheory.T.fockHarmonic_homogeneous_of_KType p q r s).2 μ P h0 ht hh,
    fun μ μ' => ⟨GlobalTheory.T.finrank_fockJointHarmonics_highestWeight_of_shape p q r s μ μ', GlobalTheory.T.fockJointHarmonics_highestWeight_eq_bot_of_not_shape p q r s μ μ'⟩, ?_⟩
  intro u1 u2 hu d
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.fischerDecomposition_fockNoncompactParts p q r s d
  cases u1 <;> cases u2
  · simp at hu
  · have e1 : lowKer X (X.fock p q r s) false true = harm1 p q r s := by
      ext P; simp [lowKer, harm1, FockData.act2]
    have e2 : raised X (X.fock p q r s) false true d = {R | ∃ Q ∈ homog (Ix p q × Ix r s) d,
        ∃ Z : Mat r s, IsPC Z ∧ R = plusPart (fockAct2 p q r s Z) Q} := by
      ext P; simp [raised, FockData.act2]
    rw [e1, e2]; exact h2
  · have e1 : lowKer X (X.fock p q r s) true false = harm2 p q r s := by
      ext P; simp [lowKer, harm2, FockData.act1]
    have e2 : raised X (X.fock p q r s) true false d = {R | ∃ Q ∈ homog (Ix p q × Ix r s) d,
        ∃ Z : Mat p q, IsPC Z ∧ R = plusPart (fockAct1 p q r s Z) Q} := by
      ext P; simp [raised, FockData.act1]
    rw [e1, e2]; exact h1
  · have e1 : lowKer X (X.fock p q r s) true true = jointHarm p q r s := by
      ext P; simp [lowKer, jointHarm, harm1, harm2, FockData.act1, FockData.act2]
    have e2 : raised X (X.fock p q r s) true true d = {R | ∃ Q ∈ homog (Ix p q × Ix r s) d,
        (∃ Z : Mat p q, IsPC Z ∧ R = plusPart (fockAct1 p q r s Z) Q) ∨
          ∃ Z : Mat r s, IsPC Z ∧ R = plusPart (fockAct2 p q r s Z) Q} := by
      ext P; simp [raised, FockData.act1, FockData.act2]
    rw [e1, e2]; exact h3

end GlobalTheory.FockAlg
end
end
