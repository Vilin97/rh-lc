module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.CalcSteps
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsoluteCutoffBoundStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsoluteFourierCoefficientsStatement
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasimirOperatorFormula
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosureOperatorFacts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactSobolevEmbeddingStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConcentrationTimeBoundStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenseDomainFactsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FriedrichsExtensionFactsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalCalculusCurve
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalCalculusFirstAssumption
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalCalculusJointCurve
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelLocalizationStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelRegularity
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelWeightFacts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PaleyWienerDecayStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionNormBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothOperatorFactsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevIntegrationByPartsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevOperatorFacts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevSpacePreserved
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WvAlg

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasimirOperatorFormulaStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.casimir_operator_formula : PositivityTheory.RgBcC.Fc.OmFormula := by
  first | exact @GlobalTheory.CompanionTheory.Casimir.omFormula | exact GlobalTheory.CompanionTheory.Casimir.omFormula | (intros; apply GlobalTheory.CompanionTheory.Casimir.omFormula <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosureOperatorFactsStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.closure_operator_facts : PositivityTheory.RgBcC.Fc.ClsFacts := by
  first | exact @GlobalTheory.CompanionTheory.FcCls.clsFacts | exact GlobalTheory.CompanionTheory.FcCls.clsFacts | (intros; apply GlobalTheory.CompanionTheory.FcCls.clsFacts <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalCalculusCurveStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.functional_calculus_curve : PositivityTheory.RgBcC.Fc.Fcurve := by
  first | exact @GlobalTheory.CompanionTheory.WaveCurve.fcurve | exact GlobalTheory.CompanionTheory.WaveCurve.fcurve | (intros; apply GlobalTheory.CompanionTheory.WaveCurve.fcurve <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalCalculusFirstAssumptionStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.functional_calculus_first_assumption : PositivityTheory.RgBcC.Fc.Asm1 := by
  first | exact @GlobalTheory.CompanionTheory.WaveFc.Asm.asm1 | exact GlobalTheory.CompanionTheory.WaveFc.Asm.asm1 | (intros; apply GlobalTheory.CompanionTheory.WaveFc.Asm.asm1 <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalCalculusJointCurveStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.functional_calculus_joint_curve : PositivityTheory.RgBcC.Fc.CurveJoint := by
  first | exact @GlobalTheory.CompanionTheory.CurveJ.curveJoint | exact GlobalTheory.CompanionTheory.CurveJ.curveJoint | (intros; apply GlobalTheory.CompanionTheory.CurveJ.curveJoint <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelRegularityStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.kernel_regularity : PositivityTheory.RgBcC.Fc.KerCore := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.kerCore | exact GlobalTheory.CompanionTheory.KerFc.kerCore | (intros; apply GlobalTheory.CompanionTheory.KerFc.kerCore <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelWeightFactsStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.kernel_weight_facts : PositivityTheory.RgBcC.Fc.KerW := by
  first | exact @GlobalTheory.CompanionTheory.KerWord.kerW | exact GlobalTheory.CompanionTheory.KerWord.kerW | (intros; apply GlobalTheory.CompanionTheory.KerWord.kerW <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionNormBoundStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.section_norm_bound : PositivityTheory.RgBcC.Fc.SecBound := by
  first | exact @GlobalTheory.CompanionTheory.SecBd.secBound_main | exact GlobalTheory.CompanionTheory.SecBd.secBound_main | (intros; apply GlobalTheory.CompanionTheory.SecBd.secBound_main <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevOperatorFactsStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.sobolev_operator_facts : PositivityTheory.RgBcC.Fc.SobOps := by
  first | exact @GlobalTheory.CompanionTheory.SobOpsPf.sobOps | exact GlobalTheory.CompanionTheory.SobOpsPf.sobOps | (intros; apply GlobalTheory.CompanionTheory.SobOpsPf.sobOps <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevSpacePreservedStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.sobolev_space_preserved : PositivityTheory.RgBcC.Fc.PresSob := by
  first | exact @GlobalTheory.CompanionTheory.PresSobA.presSob | exact GlobalTheory.CompanionTheory.PresSobA.presSob | (intros; apply GlobalTheory.CompanionTheory.PresSobA.presSob <;> assumption)
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.AsmKerOneOfSteps

section

@[expose] public section

namespace PositivityTheory.RgBcC.Fc

open PositivityTheory.RgBcC

theorem asmKerOne_of_steps (hC : AsmCpt) (hS : CalcSteps) (hO : SmoothOp) (hP : PWdecay) (hK : KerCore)
    (hL : KerLoc) (hW : KerW) : AsmKerOne := by
  intro h1 h2 h3 h4 h5 h6 n _ _ μ _ E w g T hg
  have hWC : WaveCpt := hC h1 h2 h3 h4
  apply hW n μ E w g h1 h2 h3
  obtain ⟨k, hk1, hk2, hk3, hk4⟩ := hK n μ E g T hg h1 h2 h3 h4 h5 h6 hWC hS hO hP
  exact ⟨k, hL n μ E g T k hg h1 h2 h3 h6 hWC hk1 hk2 hk3 hk4⟩

end PositivityTheory.RgBcC.Fc
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.AsmKerOne

section

@[expose] public section

namespace PositivityTheory.RgBcC.Fc

open PositivityTheory.RgBcC

theorem calcSteps : CalcSteps :=
  ⟨GlobalTheory.T.absolute_fourier_coefficients, GlobalTheory.T.absolute_cutoff_bound, GlobalTheory.T.functional_calculus_curve, GlobalTheory.CompanionTheory.WaveFc.wvAlg, GlobalTheory.T.closure_operator_facts, GlobalTheory.T.sobolev_operator_facts, GlobalTheory.T.compact_sobolev_embedding,
    GlobalTheory.T.section_norm_bound, GlobalTheory.T.sobolev_space_preserved, GlobalTheory.T.concentration_time_bound, GlobalTheory.T.functional_calculus_joint_curve, GlobalTheory.T.friedrichs_extension_facts, GlobalTheory.T.casimir_operator_formula, GlobalTheory.T.sobolev_integration_by_parts,
    GlobalTheory.T.dense_domain_facts⟩

theorem asmCpt : AsmCpt :=
  GlobalTheory.T.functional_calculus_first_assumption GlobalTheory.T.absolute_fourier_coefficients GlobalTheory.T.absolute_cutoff_bound GlobalTheory.T.functional_calculus_curve GlobalTheory.CompanionTheory.WaveFc.wvAlg GlobalTheory.T.closure_operator_facts GlobalTheory.T.sobolev_operator_facts GlobalTheory.T.compact_sobolev_embedding
    GlobalTheory.T.section_norm_bound GlobalTheory.T.sobolev_space_preserved GlobalTheory.T.concentration_time_bound GlobalTheory.T.functional_calculus_joint_curve GlobalTheory.T.friedrichs_extension_facts GlobalTheory.T.casimir_operator_formula GlobalTheory.T.sobolev_integration_by_parts GlobalTheory.T.dense_domain_facts

theorem asmKerOne : AsmKerOne :=
  asmKerOne_of_steps asmCpt calcSteps GlobalTheory.T.smooth_operator_facts GlobalTheory.T.paley_wiener_decay GlobalTheory.T.kernel_regularity GlobalTheory.T.kernel_localization GlobalTheory.T.kernel_weight_facts

end PositivityTheory.RgBcC.Fc
end
end
