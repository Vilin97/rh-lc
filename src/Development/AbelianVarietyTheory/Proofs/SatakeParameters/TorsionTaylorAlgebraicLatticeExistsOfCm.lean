module

public import Formalism.LocalToGlobal.InertKernelTheory.DefsRepDict
public import Formalism.LocalToGlobal.InertKernelTheory.GenusOneModelExistsLattice
public import Formalism.LocalToGlobal.InertKernelTheory.StatementAlgT
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlgTAll
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.CM4
public import Formalism.LocalToGlobal.InertKernelTheory.DefsBeCob
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSq
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
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.ExistsWittSeriesInverseFormalGroupIso
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoboundaryIntegralLawRespectsSimeqStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CurveLatticeSigmaTwoAlgebraicOfInvariantsAlgebraStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InverseSeriesFormalGroupIsoIntegral
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicNormTwoHundredSixteenEqOneOfFiveLe
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.Joints
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicNormTwoHundredSixteenEqOneOfFiveLe
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhEquivShortWeierstrassModel
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaUnitFunctionShortModelIntegralStatement
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementW
public import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSp
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemClosureRootsOfUnity
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalC
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.ChordEquation
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.FlowTwoTorsionWp
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.BeWInertOfSigma
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRingEquivTranscendental
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgStatus
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorStatus

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.BetaModelCoefficientsInvertL

section

@[expose] public section

noncomputable section

namespace GlobalTheory.BeCoefficients

open Formalism.MainNotions.FormalGroupSystem
open Formalism.MainNotions.GL3Theta (G1 ModelOverW)
open Formalism.L2.G.Pend (k0ToC)

theorem beCoef : Formalism.L2.KerInert.BeCob.BeCoef := by
  apply _root_.Formalism.L2.KerInert.BeCob.beta_coefficients <;> assumption

end GlobalTheory.BeCoefficients
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.BetaModelCoefficientsInvertLStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.beta_model_coefficients_invert_l : Formalism.L2.KerInert.BeCob.BeCoef := by
  first | exact @GlobalTheory.BeCoefficients.beCoef | exact GlobalTheory.BeCoefficients.beCoef | (intros; apply GlobalTheory.BeCoefficients.beCoef <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.InverseSeriesFormalGroupIsoIntegralStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.inverse_series_formalGroup_iso_integral : ∀ (l : ℕ) [Fact l.Prime] (g : Formalism.MainNotions.GL3Theta.G1 l), g.Ok → ∀ (hLT : Formalism.L2.G.Pend.LTIso g) (n : ℕ), ‖PowerSeries.coeff n (Formalism.L2.KerInert.BeCob.vLT hLT)‖ ≤ 1 := by
  first | exact @GlobalTheory.InverseSeriesIntegral.v_integral | exact GlobalTheory.InverseSeriesIntegral.v_integral | (intros; apply GlobalTheory.InverseSeriesIntegral.v_integral <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LogCoordinatesExponentIsCoboundary

section

@[expose] public section

noncomputable section

namespace GlobalTheory.CobExactProof

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D
open Formalism.MainNotions.GL3Theta (G1)
open Formalism.L2.G.Pend (k0ToC wToC LTIso beLT epOf BeRat)
open Formalism.InvariantFactorPaths.G7 (cob lgF IsLawOfLog at1)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.KerInert.BeCob (eLT vLT psiLT)
open GlobalTheory.CurveDictionary (map_cob lgF_eq_logF cc_lgF')

theorem cobExact : Formalism.L2.KerInert.BeCob.CobExact := by
  apply _root_.Formalism.L2.KerInert.BeCob.coboundary_exact <;> assumption

end GlobalTheory.CobExactProof
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LogCoordinatesExponentIsCoboundaryStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.log_coordinates_exponent_is_coboundary : Formalism.L2.KerInert.BeCob.CobExact := by
  first | exact @GlobalTheory.CobExactProof.cobExact | exact GlobalTheory.CobExactProof.cobExact | (intros; apply GlobalTheory.CobExactProof.cobExact <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhEquivShortWeierstrassModelStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.phEquiv_shortWeierstrassModel : Formalism.L2.KerInert.BeCob.PhTie := by
  first | exact @GlobalTheory.ShortModelTie.phTie | exact GlobalTheory.ShortModelTie.phTie | (intros; apply GlobalTheory.ShortModelTie.phTie <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedWeierstrassCurveTransformCoefficientsW

section

@[expose] public section

noncomputable section

namespace GlobalTheory.CoefWfUnram

open Formalism.MainNotions.GL3Theta

variable {p : ℕ} [Fact p.Prime]

theorem inWf_of_kur {x : ℂ_[p]} (hx : x ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) : InWf x := by
  first
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact @_root_.GlobalTheory.WittRootsOfUnity.inWf_of_mem_Kur
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact _root_.GlobalTheory.WittRootsOfUnity.inWf_of_mem_Kur
  | exact @_root_.GlobalTheory.WittRootsOfUnity.inWf_of_mem_Kur
  | exact _root_.GlobalTheory.WittRootsOfUnity.inWf_of_mem_Kur
  | (apply _root_.GlobalTheory.WittRootsOfUnity.inWf_of_mem_Kur <;> assumption)
  | (intros; apply _root_.GlobalTheory.WittRootsOfUnity.inWf_of_mem_Kur <;> assumption)
  | (intros; apply @_root_.GlobalTheory.WittRootsOfUnity.inWf_of_mem_Kur <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.WittRootsOfUnity.inWf_of_mem_Kur ..)

theorem coefWf_phW_of_kur (W : WeierstrassCurve ℂ_[p]) (h1 : W.a₁ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p)
    (h2 : W.a₂ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) (h3 : W.a₃ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) (h4 : W.a₄ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p)
    (h6 : W.a₆ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) {s2 : ℂ_[p]} (hs : s2 ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) :
    CoefWf (Formalism.L2.Th1.B.phW W s2 : MvPowerSeries Unit ℂ_[p]) := by
  apply _root_.Formalism.L2.KerInert.Dict.coefWf_phW <;> assumption

theorem coefWf_phW : ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]), W.a₁ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → W.a₂ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → W.a₃ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → W.a₄ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → W.a₆ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → ∀ s2 : ℂ_[p], s2 ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → Formalism.MainNotions.GL3Theta.CoefWf (Formalism.L2.Th1.B.phW W s2 : MvPowerSeries Unit ℂ_[p]) :=
  fun _ _ W h1 h2 h3 h4 h6 _ hs => coefWf_phW_of_kur W h1 h2 h3 h4 h6 hs

end GlobalTheory.CoefWfUnram
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedWeierstrassCurveTransformCoefficientsWStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.unramifiedWeierstrassCurve_transform_coefficients_wellFormed : ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]), W.a₁ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → W.a₂ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → W.a₃ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → W.a₄ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → W.a₆ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → ∀ s2 : ℂ_[p], s2 ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → Formalism.MainNotions.GL3Theta.CoefWf (Formalism.L2.Th1.B.phW W s2 : MvPowerSeries Unit ℂ_[p]) := by
  first | exact @GlobalTheory.CoefWfUnram.coefWf_phW | exact GlobalTheory.CoefWfUnram.coefWf_phW | (intros; apply GlobalTheory.CoefWfUnram.coefWf_phW <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.CurveDictOfCm

section

@[expose] public section

namespace GlobalTheory.CurveDictionary

theorem curveDict_of_cm : Formalism.L2.Th1.CM.CM2 → Formalism.L2.Th1.CM.CM3 → Formalism.L2.Th1.CM.CM4 →
    Formalism.L2.KerInert.Rep.CurveDict := fun hGood _ hTor =>
  curveDict_of_inputs hGood hTor GlobalTheory.T.curveLattice_sigmaTwo_algebraic_of_invariants_algebraic GlobalTheory.T.unramifiedWeierstrassCurve_transform_coefficients_wellFormed GlobalTheory.T.beta_model_coefficients_invert_l GlobalTheory.T.log_coordinates_exponent_is_coboundary GlobalTheory.T.coboundary_integral_law_respects_simeq
    GlobalTheory.T.phEquiv_shortWeierstrassModel GlobalTheory.T.thetaUnitFunction_shortModel_integral GlobalTheory.T.inverse_series_formalGroup_iso_integral

end GlobalTheory.CurveDictionary
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TorsionTaylorAlgebraicLatticeExistsOfCm

section

@[expose] public section

namespace GlobalTheory.CurveThetaInert

theorem torsionTaylorAlgebraic_latticeExists_of_cm (h2 : Formalism.L2.Th1.CM.CM2) :
    Formalism.L2.KerInert.AlgTAll ∧ Formalism.L2.KerInert.GenusOneModelExistsLattice ∧ Formalism.L2.KerInert.Rep.CurveDict :=
  ⟨GlobalTheory.ThLoc.algTAll,
    GlobalTheory.InertGenusOne.datum_exists_lattice h2 ReciprocityTheory.ChartRestriction.L1.cmIntegralityThree ReciprocityTheory.ChartRestriction.L1.cm4,
    GlobalTheory.CurveDictionary.curveDict_of_cm h2 ReciprocityTheory.ChartRestriction.L1.cmIntegralityThree ReciprocityTheory.ChartRestriction.L1.cm4⟩

end GlobalTheory.CurveThetaInert
end
end
