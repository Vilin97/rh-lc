import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InducedSectionZFinite
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CommutingAlgebrasFiniteSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineDerivativeAdditive
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOfIsSm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GelfandTransposeEqOfInvariantWords
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QdetPolyMapMonic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffMemSubmoduleOfComplexPolyValuesMemStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CommuteGelfandInvariantMatrixUnitsOfGlRel
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QminorPolyMap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QdetAddOneSubEqSumQminorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TracedQminorComatrixTruncatedInverseStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QdetPolyMapMonicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicFactorFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatBoundTuple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedUnip
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicFactorFiniteMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteModuleGradedQuantumDet
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

noncomputable section

namespace GlobalTheory.LeviHC

open GlobalTheory.SmoothForms (gelfA)
open Formalism.REAL (GlRel qdet)

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem qdet_mem {B : Type} [Ring B] [Algebra ℂ B] {m : ℕ} (X : Fin m → Fin m → B) (S : Subalgebra ℂ B)
    (hS : ∀ a b, X a b ∈ S) (u : ℂ) : qdet X u ∈ S := by
  unfold qdet Formalism.REAL.qminor
  refine S.sum_mem fun π _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  unfold Formalism.REAL.Tm
  refine S.add_mem ?_ (hS _ _)
  split_ifs
  exacts [S.algebraMap_mem _, S.zero_mem]

end General

end GlobalTheory.LeviHC

end
