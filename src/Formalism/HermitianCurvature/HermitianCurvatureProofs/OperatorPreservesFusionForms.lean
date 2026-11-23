module

public import Formalism.HermitianCurvature.StatementQ
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmBorderES
public import Formalism.PeriodIntegrals.QmBorderFull
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmColExp
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmRowExp
public import Formalism.PeriodIntegrals.QmSkip
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BorderMinorRotation.QmBorderFullOf
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmCapComm
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmSandwich
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelImageArithmetic.GlevImageOf
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnHermHaar
public import Formalism.FormalDegreeBessel.StatementRP
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelLiftBasics.LevelGroupUnitaryHermitian
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelTransfer.LzOutRight
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelTransfer.SecondCapelliMinorLevel
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LeftPhaseRule.LeftMultiplicationRule
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TorusConjugationRule.SecondHermitianPartDiagonal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnTInv
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnTPres

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmSkip

section

@[expose] public section

theorem quantum_minor_skip : PI.QmSkip := by
  have hsa : ∀ {n : ℕ} (p : Fin (n + 1)) (k : Fin n),
      (p.succAbove k).val = if k.val < p.val then k.val else k.val + 1 := by
    intro n p k
    unfold Fin.succAbove
    split_ifs with h1 h2 h2 <;> simp_all [Fin.lt_def]
  refine ⟨fun t i j => ?_, fun t i i' j hii' => ?_⟩
  · apply Fin.ext
    have e := hsa i j
    unfold PI.skip1
    split_ifs at e ⊢ <;> simp only at * <;> omega
  · apply Fin.ext
    have e1 := hsa i i'
    have e2 := hsa i' j
    have e3 := hsa i (i'.succAbove j)
    rw [if_neg (by omega)] at e1
    unfold PI.skip2
    split_ifs at e2 e3 ⊢ <;> simp only at * <;> omega
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmBorderFull

section

@[expose] public section

theorem quantum_minor_border_full : PI.QmBorderFull :=
  PI.qmBorderFull_of quantum_minor_border_es quantum_minor_column_expansion quantum_minor_row_expansion quantum_minor_skip
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnGlevImage

section

@[expose] public section

theorem gl_level_image : Formalism.QuantumDeterminants.LevHom → Formalism.QuantumDeterminants.LevUH → Formalism.FourierDecayAlt.Q.GlevImage :=
  QnGlevImageW.glevImage_of
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnLevBasics

section

@[expose] public section

theorem level_basics : Formalism.QuantumDeterminants.LevHom ∧ Formalism.QuantumDeterminants.LevUH ∧ Formalism.QuantumDeterminants.LevN ∧ Formalism.QuantumDeterminants.LevUW ∧ Formalism.QuantumDeterminants.LevWb ∧ Formalism.QuantumDeterminants.LevEll :=
  ⟨PI.QnLevBasicsW.level_group_homomorphism, PI.QnLevBasicsW.level_group_unitary_hermitian, PI.QnLevBasicsW.level_group_nilpotent,
    PI.QnLevBasicsW.level_group_unitary_weyl, PI.QnLevBasicsW.level_group_isotropic_vector, PI.QnLevBasicsW.level_group_ellipticity⟩
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnLevTransfer

section

@[expose] public section

theorem level_transfer_of_levHom : Formalism.QuantumDeterminants.LevHom → Formalism.FourierDecayAlt.Q.LevelTransfer := by
  open PIQnLT Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q in
  intro hL E _ _ k i r' z z' Y p q f g hg
  have hinv : (ιLev k i r' g)⁻¹ = ιLev k i r' g⁻¹ := ιLev_inv hL g (isUnit_det_of_UH g hg)
  have hm := mdim_lev k i r'
  have hP : ∀ j, posL k (i + r') ⟨i, by omega⟩ j = levPos k i r' (posL k r' 0 (Fin.cast hm j)) :=
    posL_lev k i r'
  have hx : ∀ j, xv k (i + r') (liftVec k i r' z') ⟨i, by omega⟩ j = xv k r' z' 0 (Fin.cast hm j) := by
    intro j
    simp only [xv]
    rw [fvec_lift, hP, liftVec_lev]
  have hxb : ∀ j, xbv k (i + r') (liftVec k i r' z') ⟨i, by omega⟩ j =
      xbv k r' z' 0 (Fin.cast hm j) := by
    intro j
    simp only [xbv]
    rw [fvec_lift, hP, bvec_lev, herm_liftVec]
  have hy : ∀ j, yv k (i + r') (liftVec k i r' z) ⟨i, by omega⟩ (ιLev k i r' g) j =
      yv k r' z 0 g (Fin.cast hm j) := by
    intro j
    simp only [yv]
    rw [hinv, fvec_lift, mulVec_liftVec, hP, liftVec_lev]
  have hyb : ∀ j, ybv k (i + r') (liftVec k i r' z) ⟨i, by omega⟩ (ιLev k i r' g) j =
      ybv k r' z 0 g (Fin.cast hm j) := by
    intro j
    simp only [ybv]
    rw [fvec_lift, hP, bvec_lev, mulVec_liftVec, herm_liftVec]
  have hu := uC_lev k i r' Y
  fin_cases p <;> fin_cases q
  · simp only [tL, capL]
    rw [hu]
    exact capL_cast hL hm _ _ hP _ f g
  · simp only [tL, Pi.neg_apply]
    rw [hu]
    congr 1
    exact chatL_cast hL hm _ _ hP _ _ _ _ _ f g (fun j => hx j) (fun j => hyb j)
  · simp only [tL, Pi.neg_apply]
    rw [hu]
    congr 1
    exact chatL_cast hL hm _ _ hP _ _ _ _ _ f g (fun j => hy j) (fun j => hxb j)
  · simp only [tL, Pi.neg_apply]
    rw [hu]
    congr 1
    exact second_capelli_minor_cast hL hm _ _ hP _ _ _ _ _ _ _ _ _ f g (fun j => hy j) (fun j => hx j)
      (fun j => hyb j) (fun j => hxb j)
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnRuleLeft

section

@[expose] public section

theorem qnRuleLeft : Formalism.FourierDecayAlt.Q.RuleLeft := Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.left_multiplication_rule
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnRuleTorus

section

@[expose] public section

theorem qnRuleTorus : Formalism.FourierDecayAlt.Q.RuleTorus := by
  open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q PI.QnRT in
  intro E _ _ k r l D f hD hf c hc g₁ hg₁ hmem
  have hcl : c l ≠ 0 := hc l
  have h1 : -((1 / 2 : ℝ) : ℂ) = -star ((1 / 2 : ℝ) : ℂ) := by simp
  have h2 : ((-1 / 2 : ℝ) : ℂ) * Complex.I = -star (((-1 / 2 : ℝ) : ℂ) * Complex.I) := by
    simp
  have h3 : ((1 / 2 : ℝ) : ℂ) = -star (-((1 / 2 : ℝ) : ℂ)) := by simp
  set φ : (Fin r → ℂ) → E := fun c' => f (w1 k r l (c' l) * g₁) with hφ
  set L := fderiv ℝ φ c with hL
  refine ⟨?_, ?_⟩
  · simp only [EH, EabH]
    rw [X1_eq, depthNumbers_threshold_eq, rdV_dz' l D f hf c hcl g₁ hg₁ hmem _ _ h1,
      rdV_dz' l D f hf c hcl g₁ hg₁ hmem _ _ h2]
    simp only [pOp, wirt, if_pos hc]
    rw [lin_single l L (c l * ((1 / 2 : ℝ) : ℂ)), lin_single l L (c l * (((-1 / 2 : ℝ) : ℂ) * Complex.I))]
    generalize L (Pi.single l 1) = A
    generalize L (Pi.single l Complex.I) = B
    obtain ⟨a, b, hab⟩ : ∃ a b : ℝ, c l = (a : ℂ) + (b : ℂ) * Complex.I :=
      ⟨_, _, (Complex.re_add_im _).symm⟩
    rw [hab]
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im]
    match_scalars <;> simp [Complex.ext_iff] <;> ring
  · simp only [EH, EabH]
    rw [first_hermitian_part_diagonal, second_hermitian_part_diagonal, rdV_dz' l D f hf c hcl g₁ hg₁ hmem _ _ h3,
      rdV_dz' l D f hf c hcl g₁ hg₁ hmem _ _ h2]
    simp only [pbOp, wirtBar, if_pos hc]
    rw [lin_single l L (c l * -((1 / 2 : ℝ) : ℂ)), lin_single l L (c l * (((-1 / 2 : ℝ) : ℂ) * Complex.I))]
    generalize L (Pi.single l 1) = A
    generalize L (Pi.single l Complex.I) = B
    obtain ⟨a, b, hab⟩ : ∃ a b : ℝ, c l = (a : ℂ) + (b : ℂ) * Complex.I :=
      ⟨_, _, (Complex.re_add_im _).symm⟩
    rw [hab]
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im]
    match_scalars <;> simp [Complex.ext_iff] <;> ring
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.OperatorPreservesFusionForms

section

@[expose] public section

theorem Formalism.FourierDecayAlt.P.border_first_expansion : Formalism.FourierDecayAlt.Q.BorderE := by
  exact quantum_minor_border_es.1

theorem Formalism.FourierDecayAlt.P.border_last_expansion : Formalism.FourierDecayAlt.Q.BorderS := by
  exact quantum_minor_border_es.2

theorem Formalism.FourierDecayAlt.P.border_full_expansion : Formalism.FourierDecayAlt.Q.BorderFull := by
  exact quantum_minor_border_full

theorem Formalism.FourierDecayAlt.P.rtt_sandwich : Formalism.FourierDecayAlt.Q.RTTSandwich := by
  exact rtt_sandwich'

theorem Formalism.FourierDecayAlt.P.level_group_image : Formalism.FourierDecayAlt.Q.GlevImage := by
  obtain ⟨hH, hU, -⟩ := level_basics
  exact gl_level_image hH hU

theorem Formalism.FourierDecayAlt.P.level_transfer : Formalism.FourierDecayAlt.Q.LevelTransfer := by
  exact level_transfer_of_levHom level_basics.1

theorem Formalism.FourierDecayAlt.P.left_action_rule : Formalism.FourierDecayAlt.Q.RuleLeft := by
  exact qnRuleLeft

theorem Formalism.FourierDecayAlt.P.torus_action_rule : Formalism.FourierDecayAlt.Q.RuleTorus := by
  exact qnRuleTorus

theorem Formalism.FourierDecayAlt.P.operator_invariance : Formalism.FourierDecayAlt.Q.TInvariant := by
  exact qnTInv

theorem Formalism.FourierDecayAlt.P.operator_preserves_fusion_forms : Formalism.FourierDecayAlt.Q.TPreservesFF := by
  exact qnTPres

theorem Formalism.FourierDecayAlt.P.capelli_commutation : Formalism.FourierDecayAlt.Q.CapCommute := by
  exact capelli_det_commute

theorem Formalism.FourierDecayAlt.P.hermitian_haar_invariance : Formalism.FourierDecayAlt.Q.HermHaar := by
  exact qnHermHaar
end
end
