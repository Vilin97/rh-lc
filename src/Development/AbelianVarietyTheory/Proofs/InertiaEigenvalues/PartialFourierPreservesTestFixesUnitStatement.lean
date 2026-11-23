module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralTraceUnitUnramifiedQuadraticStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNhdsZeroTranslationInvariantOfLocallyConst
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasCompactSupportPartialFourierGLBlock
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantPartialFourierGLBlock
public import Mathlib.Analysis.Normed.Field.ProperSpace
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialFourierGLBlockUnitIndicatorStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialFourierHermitianBlockHasCompactSupportStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialFourierHermitianBlockIsLocallyConstantStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialFourierHermitianBlockUnitIndicatorStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitIndicatorGLBlockIsLocallyConstantCompactSuppStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PsiKMulNLEqOneOnIntegralLattice
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.Trace.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNhdsZeroTranslationInvariantOfLocallyConstStatement

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.exists_nhds_zero_translation_invariant_of_locallyConstant : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] (f : X → ℂ), IsTest f → ∃ U ∈ 𝓝 (0 : X), ∀ x : X, ∀ u ∈ U, f (x + u) = f x := by
  first | exact @GlobalTheory.isTest_nhds_inv | exact GlobalTheory.isTest_nhds_inv | (intros; apply GlobalTheory.isTest_nhds_inv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasCompactSupportPartialFourierGLBlockStatement

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.hasCompactSupport_partialFourierGLBlock : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ f' : Gl r F → ℂ, IsTest f' → (∃ U ∈ 𝓝 (0 : Gl r F), ∀ Y : Gl r F, ∀ u ∈ U, f' (Y + u) = f' Y) → HasCompactSupport (fourG M ψ f') := by
  first | exact @GlobalTheory.JR.fourG_hasCompactSupport | exact GlobalTheory.JR.fourG_hasCompactSupport | (intros; apply GlobalTheory.JR.fourG_hasCompactSupport <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantPartialFourierGLBlockStatement

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.isLocallyConstant_partialFourierGLBlock : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ f' : Gl r F → ℂ, IsTest f' → (∃ U ∈ 𝓝 (0 : Gl r F), ∀ Y : Gl r F, ∀ u ∈ U, f' (Y + u) = f' Y) → IsLocallyConstant (fourG M ψ f') := by
  first | exact @GlobalTheory.JR.fourG_isLocallyConstant_of_invariant | exact GlobalTheory.JR.fourG_isLocallyConstant_of_invariant | (intros; apply GlobalTheory.JR.fourG_isLocallyConstant_of_invariant <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsTestUnitIndicatorHermitianBlock

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem isTest_indicator_one_of_clopen_compact {X : Type} [TopologicalSpace X] {S : Set X} (hS : IsClopen S)
    (hK : IsCompact S) : IsTest (Set.indicator S (1 : X → ℂ)) := by
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hx : x ∈ S
    · filter_upwards [hS.isOpen.mem_nhds hx] with y hy
      simp [hx, hy]
    · filter_upwards [hS.isClosed.isOpen_compl.mem_nhds hx] with y hy
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
  · exact HasCompactSupport.intro' hK hS.isClosed fun x hx => Set.indicator_of_notMem hx _

theorem isTest_unitU (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [StarRing E]
    [IsUltrametricDist F] [LocallyCompactSpace F] [IsUltrametricDist E] [LocallyCompactSpace E] (r : ℕ)
    (hstar : ∀ y : E, ‖star y‖ = ‖y‖) : IsTest (unitU r F E) := by
  haveI : ProperSpace F := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  haveI : ProperSpace E := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace E
  haveI : ContinuousStar E := ⟨(AddMonoidHomClass.isometry_of_norm (starAddEquiv (R := E)) hstar).continuous⟩
  have hF : {x : F | ‖x‖ ≤ 1} = Metric.closedBall 0 1 := by ext x; simp
  have hE : {x : E | ‖x‖ ≤ 1} = Metric.closedBall 0 1 := by ext x; simp
  have cF : IsClopen {x : F | ‖x‖ ≤ 1} := hF ▸ IsUltrametricDist.isClopen_closedBall _ one_ne_zero
  have cE : IsClopen {x : E | ‖x‖ ≤ 1} := hE ▸ IsUltrametricDist.isClopen_closedBall _ one_ne_zero
  have kF : IsCompact {x : F | ‖x‖ ≤ 1} := hF ▸ isCompact_closedBall _ _
  have kE : IsCompact {x : E | ‖x‖ ≤ 1} := hE ▸ isCompact_closedBall _ _
  have cV : IsClopen {v : Fin r → E | ∀ i, ‖v i‖ ≤ 1} := by
    rw [Set.ofPred_forall]
    exact isClopen_iInter_of_finite fun i => cE.preimage (continuous_apply i)
  have kV : IsCompact {v : Fin r → E | ∀ i, ‖v i‖ ≤ 1} := isCompact_pi_infinite fun _ => kE
  have cM : IsClopen {A : Matrix (Fin r) (Fin r) E | ∀ i j, ‖A i j‖ ≤ 1} := by
    rw [Set.ofPred_forall]
    exact isClopen_iInter_of_finite fun i => cV.preimage (continuous_apply i)
  have kM : IsCompact {A : Matrix (Fin r) (Fin r) E | ∀ i j, ‖A i j‖ ≤ 1} :=
    isCompact_pi_infinite (s := fun _ : Fin r => {v : Fin r → E | ∀ i, ‖v i‖ ≤ 1}) fun _ => kV
  have hcl : IsClosed ((selfAdjoint (Matrix (Fin r) (Fin r) E)) : Set (Matrix (Fin r) (Fin r) E)) :=
    isClosed_eq continuous_star continuous_id
  have cA : IsClopen {A : selfAdjoint (Matrix (Fin r) (Fin r) E) | ∀ i j, ‖A.1 i j‖ ≤ 1} :=
    cM.preimage continuous_subtype_val
  have kA : IsCompact {A : selfAdjoint (Matrix (Fin r) (Fin r) E) | ∀ i j, ‖A.1 i j‖ ≤ 1} :=
    hcl.isClosedEmbedding_subtypeVal.isCompact_preimage kM
  exact isTest_indicator_one_of_clopen_compact (cA.prod (cV.prod cF)) (kA.prod (kV.prod kF))

end GlobalTheory.JR
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsTestUnitIndicatorHermitianBlockStatement

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.isTest_unitIndicatorHermitianBlock : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [StarRing E] [IsUltrametricDist F] [LocallyCompactSpace F] [IsUltrametricDist E] [LocallyCompactSpace E] (r : ℕ), (∀ y : E, ‖star y‖ = ‖y‖) → IsTest (unitU r F E) := by
  first | exact @GlobalTheory.JR.isTest_unitU | exact GlobalTheory.JR.isTest_unitU | (intros; apply GlobalTheory.JR.isTest_unitU <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedQuadraticTraceEqAddStar

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

theorem trace_eq_add_star : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E], ∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y := by
  apply GlobalTheory.JR.NormInt.traceE <;> assumption

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedQuadraticTraceEqAddStarStatement

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.unramifiedQuadratic_trace_eq_add_star : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E], ∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y := by
  first | exact @GlobalTheory.trace_eq_add_star | exact GlobalTheory.trace_eq_add_star | (intros; apply GlobalTheory.trace_eq_add_star <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialFourierPreservesTestFixesUnit

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

theorem fourier_test_unit : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → (∀ f', IsTest f' → IsTest (fourG M ψ f')) ∧ (∀ f, IsTest f → IsTest (fourU M ψ f)) ∧ IsTest (unitG r F) ∧ IsTest (unitU r F E) ∧ fourG M ψ (unitG r F) = unitG r F ∧ fourU M ψ (unitU r F E) = unitU r F E := by
  intro F E _ _ _ _ hU r M ψ hψ
  haveI := hU.ultraF; haveI := hU.ultraE; haveI := hU.lcF; haveI := hU.lcE
  have htr := GlobalTheory.T.unramifiedQuadratic_trace_eq_add_star F E
  refine ⟨fun f' hf => ⟨GlobalTheory.T.isLocallyConstant_partialFourierGLBlock F E r M ψ hψ f' hf (GlobalTheory.T.exists_nhds_zero_translation_invariant_of_locallyConstant _ f' hf), GlobalTheory.T.hasCompactSupport_partialFourierGLBlock F E r M ψ hψ f' hf (GlobalTheory.T.exists_nhds_zero_translation_invariant_of_locallyConstant _ f' hf)⟩,
    fun f hf => ⟨GlobalTheory.T.partialFourierHermitianBlock_isLocallyConstant F E r M ψ hψ htr f hf (GlobalTheory.T.exists_nhds_zero_translation_invariant_of_locallyConstant _ f hf), GlobalTheory.T.partialFourierHermitianBlock_hasCompactSupport F E r M ψ hψ htr f hf (GlobalTheory.T.exists_nhds_zero_translation_invariant_of_locallyConstant _ f hf)⟩,
    GlobalTheory.T.unitIndicatorGLBlock_isLocallyConstantCompactSupport F r, GlobalTheory.T.isTest_unitIndicatorHermitianBlock F E r hU.norm_star, GlobalTheory.T.partialFourierGLBlock_unitIndicator F E r M ψ hψ, GlobalTheory.T.partialFourierHermitianBlock_unitIndicator F E r M ψ hψ htr (GlobalTheory.T.exists_integral_trace_unit_unramifiedQuadratic F E htr)⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialFourierPreservesTestFixesUnitStatement

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.partialFourier_preserves_test_fixes_unit : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → (∀ f', IsTest f' → IsTest (fourG M ψ f')) ∧ (∀ f, IsTest f → IsTest (fourU M ψ f)) ∧ IsTest (unitG r F) ∧ IsTest (unitU r F E) ∧ fourG M ψ (unitG r F) = unitG r F ∧ fourU M ψ (unitU r F E) = unitU r F E := by
  first | exact @GlobalTheory.fourier_test_unit | exact GlobalTheory.fourier_test_unit | (intros; apply GlobalTheory.fourier_test_unit <;> assumption)
end
end
