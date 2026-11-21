import Mathlib
import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.SegTwo
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ZelevinskyClassification.ZelevinskySegments.SegDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EquivOfMultiplicityOneUniqueFactor
import CompanionTheory.AutomorphicTheory.SegmentRepresentations.IrreducibleSegments.IsIrreduciblePiTensorSegTerm
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SocleOfMultiplicityOne
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.GlobalTheory.BernsteinZelevinskyFiniteness
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIrrRepInjective
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.JacquetMultiplicityPosOfSocle
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.Published GlobalTheory.SegmentRepModel

namespace CompanionTheory.Pf1.SegRepC.SegTwo

def RhoNuRhoReducible : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (d : ℕ), 0 < d → ∀ σ : IrrRep (GL (Fin d) k), IsCuspidal σ.ρ →
      ¬ (multiProd (consecBlocks 2 d) (segTerm σ.ρ 2)).IsIrreducible

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def revTensor {d : ℕ} (σ : IrrRep (GL (Fin d) k)) :=
  piTensor fun a : Fin 2 => segTerm σ.ρ 2 a.rev

set_option synthInstance.maxHeartbeats 400000 in

set_option synthInstance.maxHeartbeats 400000 in

end CompanionTheory.Pf1.SegRepC.SegTwo

end
