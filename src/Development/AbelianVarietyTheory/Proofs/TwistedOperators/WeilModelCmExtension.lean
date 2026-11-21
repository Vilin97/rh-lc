import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzOneParameterGroupFormula
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSymplecticLieEqExpOneParamStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetaplecticTransfer
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionUnitaryCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchActOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanWeilOperatorsLinearOneMulStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanWeilOperatorIntertwinesSchroedingerStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryArchimedeanCoordinateActionLinearMulStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryArchimedeanCoordinateActionSymplecticStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousOneParameterUnitaryCoordinateActionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousOneParameterArchimedeanWeilOperatorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchWeilOperatorUnitaryWLintegralNormEqStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Filter Topology
open GlobalTheory.AdelicU
open scoped Classical

namespace GlobalTheory.Twist.SmoothLine

theorem finprod_add_of_at {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F v) → ℂ) (x z : κ → AF F) (hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evI F) z) :
    (∏ᶠ v, φ v fun i => evFin F v ((x + z) i)) = ∏ᶠ v, φ v fun i => evFin F v (x i) := by
  refine finprod_congr fun v => ?_
  have hv : (fun i => evFin F v ((x + z) i)) = fun i => evFin F v (x i) := by
    funext i
    rw [Pi.add_apply, map_add, GlobalTheory.ThK.EvUniqInf.evFin_eq_zero_of_at z hz v i, add_zero]
  rw [hv]

end GlobalTheory.Twist.SmoothLine
