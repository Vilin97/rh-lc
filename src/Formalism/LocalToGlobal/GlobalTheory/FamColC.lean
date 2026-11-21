import Formalism.LocalToGlobal.GlobalTheory.FamCol
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.Divisibility.LiftLat
import Formalism.SizeWindowBrackets.Chain2aCoreNoAnalytic
import Formalism.LandauZeroFreeBounds.SiegelWalfiszAP
import Formalism.ZeroFreeRegion.Statement
import Formalism.LandauZeroFreeBounds.LogDerivRegionChiOf
import Formalism.SizeWindowBrackets.ChainSlopeWindows.GaloisMapComplexConjugation
import Formalism.LandauZeroFreeBounds.SiegelWalfiszAPOfSiegelLower
import Formalism.SizeWindowBrackets.SlopesFromSizeAndCount
import Formalism.SizeWindowBrackets.ChainSlopeWindows.PChain
import Formalism.SizeWindowBrackets.ClaimGaFree
import Formalism.SizeWindowBrackets.QuotientSlopeBoundsWith
import Formalism.SizeWindowBrackets.FrameTraceRatioFinEquiv
import Formalism.SizeWindowBrackets.SlopesHypothesisFinitePlaces
import Formalism.SizeWindowBrackets.ChainSlopeWindows.WeightedSlopeExcessDecomposition
import Formalism.SizeWindowBrackets.ChainSlopeWindows.LevelOfCongruence
import Formalism.SizeWindowBrackets.ChainSlopeWindows.JointDModelAppliesUnitLattice
import Formalism.SizeWindowBrackets.ChainSlopeWindows.ExistsNsmulMem
import Formalism.SizeWindowBrackets.ChainSlopeWindows.AdmissibleSchurLemma
import Formalism.SizeWindowBrackets.ChainSlopeWindows.OneLeThresholdMulPowers
import Formalism.SizeWindowBrackets.ChainSlopeWindows.StronglyIrreducible
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SlopeIneqMean
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HtGram
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.PolygonSlopeSum
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SizeMu
import Formalism.SizeWindowBrackets.SBrDiv
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DualPl
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Rerealize
import Formalism.SizeWindowBrackets.ErrorFormsWeakWindowsFalse
import Formalism.LogVandermondeBounds.LogRatioUpperBound
import Formalism.SizeWindowBrackets.ChainSlopeWindows.SubThreeMulLogTwoLe
import Formalism.LogVandermondeBounds.HookGammaAmgmMultinomialBounds
import Formalism.SizeWindowBrackets.TraceSquareAndDiagBounds
import Formalism.SizeWindowBrackets.ChainSlopeWindows.TraceConjTransposeMulSelf
import Formalism.SizeWindowBrackets.GaloisToProductIsIso
import Formalism.SizeWindowBrackets.GrowthBoundGivesRiemannHypothesis
import Formalism.SizeWindowBrackets.SecondKindBucket
import Formalism.SizeWindowBrackets.SlopeExcessBoundExponentZero
import Formalism.SizeWindowBrackets.ChainSlopeWindows.LipschitzWeightAndMinimum
import Formalism.SizeWindowBrackets.RealSlopeBoundsSplit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.BigOperators
import Formalism.RankGapBounds.RankGapProofs.WeightedMeanData
import Mathlib
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ZetaNegReal
import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.DzDifferentiableOn
import Formalism.GL3MeanSquares.HookFormulaTorsion.SmoothedRemainderRealIntegralFormula
import Formalism.GL3MeanSquares.SmoothedRemainderRealIntegralFormula
import Formalism.GL3MeanSquares.HookFormulaTorsion.PrimesInProgressionCountLowerBound
import Formalism.GL3MeanSquares.HookFormulaTorsion.PsiZeroIntegral
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Formalism.GL3MeanSquares.HookFormulaTorsion.NumericalZeroDensityBound
import Formalism.GL3MeanSquares.HookFormulaTorsion.CharacterEstimateOfHypothesis
import Formalism.GL3MeanSquares.SecondEstimateOfIntervalHypothesis
import Formalism.GL3MeanSquares.HookFormulaTorsion.TwistIsPrimitiveCharacter
import Formalism.GL3MeanSquares.HookFormulaTorsion.WeightedVonMangoldtSumIdentity
import Formalism.GL3MeanSquares.OrbitPointsDistinct
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Formalism.GL3MeanSquares.HookFormulaTorsion.DifferentIdealConditions
import Formalism.TameInertiaTowers.TowerFieldFoundations
import Formalism.ZetaRealNonvanish
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.TailContour
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.TailDiff
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.TailMertens
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.TailNum
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountSt
import Formalism.LocalToGlobal.GlobalTheory.GL2.Statement
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZAll
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqMain
import Formalism.SizeWindowBrackets.PrimeClassLossHypothesesSatisfiable
import Formalism.SizeWindowBrackets.ChainSlopeWindows.DiscriminantSettingSatisfied
import Formalism.StatementOC
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTFinal

open Module NumberField IsDedekindDomain Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.FamColC

open Formalism Formalism.HN Formalism.LFunctionChainParameters Formalism.L2.Col Formalism.L2.GlobalTheoryTheory.FamCol

section Obj

variable {K : Type} [Field K] [NumberField K] [StarRing K] {I : Type}

structure RowTr [Fintype I] (C : ColObj K I) (R : RowArg C) (x ε : ℝ) : Prop where
  X' : ∀ w, IsUnit (R.X' w).det
  Y : ∀ u, IsUnit (R.Y u).det
  Y' : IsUnit R.Y'.det
  cc_fg : R.cc.FG
  cc_span : Submodule.span K (R.cc : Set R.Wd) = ⊤
  into : ∀ u, (C.Npr u).map ((R.B u).restrictScalars (𝓞 K)) ≤ R.cc
  ht : ∀ u, R.B u ≠ 0 → htMap (C.M u).b (C.M u).X R.b' R.X' (R.B u) ≤ R.h u
  block : ∀ u (k : R.κ) (j : (C.M u).ι), R.Ball u (Sum.inl k) j =
    (R.Y'⁻¹ * (LinearMap.toMatrix (C.M u).b R.b' (R.B u)).map R.v.embedding * R.Y u) k j
  γ : ∀ u, 0 < R.γ u
  Ball : ∀ u, R.Ball u = R.Bf u * C.Vr u R.v
  η0_ge : -1 ≤ R.η0
  η0_le : R.η0 ≤ LChain6.E8 x ε
  η1_le : R.η1 ≤ LChain6.E8 x ε
  exponent_bound_ter : 0 ≤ R.e0
  sqrt_error_le_half : Real.sqrt R.e0 ≤ LChain6.E8 x ε
  inputS : MatrixLatticeEstimates.InputSG R.Bf R.γ C.Dstar R.η0 R.η1 R.e0
  irr : (1 - LChain6.E7 x ε) * (Fintype.card (R.κ ⊕ R.κ₁) : ℝ) ≤ (Fintype.card R.κ : ℝ)

end Obj

section Fam7

variable {H : Type} {W : H → Type}

end Fam7

section Collected

open Formalism.L2.Indef Formalism.L2.DIV Formalism.DivisionValues Formalism.L2.GlobalTheoryTheory.FamRows

variable {K : Type} [Field K] [NumberField K] [StarRing K] {I : Type}
  {Bs : DefBase K} {Df : DefSide Bs} {Dc : DefCols Df} {Sp : SPer Dc} {N : IndefNum Bs}

end Collected

section Family

open Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
  Formalism.LFunctionChainParameters.LChain2 Formalism.LFunctionChainParameters.LHost Formalism.LFunctionChainParameters.LBr2 Formalism.LFunctionChainParameters.LBrDiv Formalism.LFunctionChainParameters.SectionsFourToSixTransfer Formalism.LFunctionChainParameters.LChain6
  Formalism.LFunctionChainParameters.LChain7

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}

end Family

section Core

open Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
  Formalism.LFunctionChainParameters.LChain2 Formalism.LFunctionChainParameters.LHost Formalism.LFunctionChainParameters.LBr2 Formalism.LFunctionChainParameters.LBrDiv Formalism.LFunctionChainParameters.SectionsFourToSixTransfer Formalism.LFunctionChainParameters.LChain6
  Formalism.LFunctionChainParameters.LChain7 Formalism.L2.GlobalTheoryTheory.MergeGL2 Formalism.L2.GlobalTheoryTheory.MergeGL2c

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}

end Core

end Formalism.L2.GlobalTheoryTheory.FamColC

end
