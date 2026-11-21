import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsLgOfLnSymUpdateSubLe
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLeOfIsAlgebraic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommonRefinementCovers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsPullbackAlongCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverRefinementGenericDegree
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumLogEmbeddingAddFinsumLogAdicAbvEqZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericallySmoothModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CombPowIsometric
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqGenericPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AnalyticWeightLinearComb
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValAtAlgebraMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosedPointGeometricFibresFinite
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTangent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RatIsomOfInducedHermitianBundles
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDiscreteValuationRingAndFiniteResidueFieldValu
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.BcField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameBaseChangeRingHom
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIsoOfIsProperOfExistsUniqueFieldPointOfIsInteg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalisedGraphClosure
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLiftOfRangeSubset
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartDenseProOpen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoOfDensePartOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsJoinNormalProjectiveModels
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegralFlagCellOfValuedFieldStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothBaseAndNormalCoordinateRing
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAffineLieBasisBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CocycleTrivialOnProjectiveCover
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineEigenframeNearImage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LetterConjugation
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjOverCompFinite
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPluckerFlagEmbeddingOfProjectiveBaseStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagCellsGlueLocallyClosedPluckerProductStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompactNormalNoetherianOfFlagCellCoverStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreimageIUnionOpensEqRangeFlagCellsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSpanOfPluckerProportional
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PluckerVectorBlockTriangularFrameChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreModelChartFrame
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIntegralPivotDecomposition
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyAdaptedOfIntStep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyClosureOfEmbedding
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrNormPush
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DividesOfNormBoundedPoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdealSheafAwayFromP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTanBasisOfUniqueCombination
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.PadicValNatAbsNormEqZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentBasisOfSplitTorsion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameCombinationCoeffUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GradedLineBundleExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelOfLocMax
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjFsBasisOfUnitary
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineEigenframeFlag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalEquationComplexPoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenMetricOnSet
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.DifferentiableAtChart
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernIntegralEqDegree
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformizedFamilyChartIndex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodFamilyChartDomain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramedComplexPointOfEigenFrameOffBoundaryStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramSmoothOfHolomorphicFrames
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsExponentialModelFiberOfUniformisationExp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpCoordinatesTangentFieldHolomorphicPeriodMapStatement
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelNeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverFunctionFieldMapEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommonRefinementOfCoverAndModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsCompModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntersectionNumberFinitePushforward
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalHeightBoundedByPrimeWeights
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation
import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFrobGBaseChange
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsFormOfEqRatioPowMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationLtOneOfInvNotMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ScaleZeroComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegVanishingNumberFieldTwist
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsOpenChartFramedPointTestRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsTransitionUnique
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsPrimitiveRootArcRoot
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModelsOfSemistableReduction
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EgaHolds
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LinearUniformisationTriplesTorsionStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationCompleteDVR
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelUniformisationOfAbelianLocusDirectImageStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHoldStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModuliConsequenceOfAbelianSchemeLawsStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelGoodAtAllPrimesAndIdx
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralPointPullbackComparison
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothRelativeDimOfTrdeg
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ObjMapUniqueOfIsDominant
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyOfModToModIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankEqZeroIff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsEmbeddingCompleteAlgClosedFixedCarrier
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemBasesNonempty
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueConstantTangentVectorsAlongArc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Formalism.LocalToGlobal.ProjectiveLattices.ArcTheta
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PmapsOfGenRelR
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsoEqOfMapsAlongSection
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsPChartOfFramedPoint
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ModelChartLiftCoordsGeneratorIndep
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantLieBasisArcGroup
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantArcEigenbasisFlatBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsArcBasisBaseChange
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimGen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceDimensionEqSumChoose
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FormsOver
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
import Formalism.LocalToGlobal.ProjectiveLattices.HostRank
import Development.AutomorphicArithmetic.LocalEmbeddings.VertCmp
import Development.AutomorphicArithmetic.DivisorFrames.PdegEqOfIsDeg
import Development.AutomorphicArithmetic.DivisorFrames.GenericIsoSectionsLog
import Development.AutomorphicArithmetic.DivisorFrames.ExistsMetricGenericOpen
import Development.AutomorphicArithmetic.DivisorFrames.ArithmeticFunctionInducedBound
import Development.AutomorphicArithmetic.DivisorFrames.AdmissiblePointDiscreteValuation
import Development.AutomorphicArithmetic.DivisorFrames.FlagCarriesEigenframe
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmHostRootComplexEqPmSqrt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSemiAbelianTripleMapExtendingModelMap
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueLiftOfDensePart
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SemiAbelianHomExtensionDvr
import Development.AutomorphicArithmetic.DivisorFrames.NormalModelComplexCompatAlt
import Development.AutomorphicArithmetic.DivisorFrames.AdmissiblePointLatticeNorm
import Development.AutomorphicArithmetic.DivisorFrames.AdmissiblePointHeightCompat
import Development.AutomorphicArithmetic.LocalEmbeddings.CovCmpMain
import Development.AutomorphicArithmetic.DivisorFrames.NormsGiveRationalSections
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.LocM
open GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx
open GlobalTheory.PairTerm
open Classical

open private place from Development.AutomorphicArithmetic.LocalEmbeddings.PairMain

private theorem vertNum_eq {F : Type} [Field F] [NumberField F] {Y : Var F} (p : ℕ) [Fact p.Prime] (V : Cover Y) (n : ℕ)
    (N : Fin n → HermLB V.p) (z : V.X) : vertNum p V n N z = (VertCmp.pdeg p (fun j => (N j).B) z : ℝ) := by
  rw [vertNum]
  split_ifs with h
  · rw [UpperTheory.pdeg_eq_of_isDeg p V.X n _ (fun j => (N j).isLB) z _
      ⟨h.some.Z, h.some.i, h.some.imm, h.some.int, h.some.alg, h.some.gen, h.some.dim, rfl⟩]
  · rw [VertCmp.pdeg, dite_eq_right fun ⟨_, Z, i, a₁, a₂, a₃, a₄, a₅, _⟩ => h ⟨⟨Z, i, a₁, a₂, a₃, a₄, a₅⟩⟩, Int.cast_zero]

private theorem one_comp {F : Type} [Field F] [NumberField F] {Y : Var F} {C : CxSt F} (p : ℕ) [Fact p.Prime]
    (v : HeightOneSpectrum (𝓞 F)) (hp : (p : 𝓞 F) ∈ v.asIdeal) {d : ℕ} (hd : Y.dim = d) (A : Bool ⊕ Fin d → Adl C Y)
    (hD : (A (.inl true)).D = (A (.inl false)).D) (V : Cover Y) (L : Bool ⊕ Fin d → HermLB V.p) (m : ℕ) (hm : m ≠ 0)
    (hL : ∀ i, Norms V (L i) (fun y => genAt (A i).D y ^ m) (fun σ y => (m : ℝ) * lnAdl (A i) σ y)
      (fun v e y => (m : ℝ) * (A i).lg v e y))
    (r : ((L (.inl false)).tens (L (.inl true)).dual).B.ι → V.X.functionFieldˣ)
    (hr : IsRatSec ((L (.inl false)).tens (L (.inl true)).dual).B r)
    (hrn : RatNorms V ((L (.inl false)).tens (L (.inl true)).dual) r
      (fun v e y => (m : ℝ) * ((A (.inl false)).lg v e y - (A (.inl true)).lg v e y)))
    (Q : TrueGeo.Model Y) [IsIntegral Q.X] [IsLocallyNoetherian Q.X] (hQ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Q.X)
    (m' : ℕ) (hm' : m' ≠ 0) (N : Bool ⊕ Fin d → LB Q.X) (hN : ∀ k, (N k).IsLB)
    (t : ∀ k, (N k).ι → Q.X.functionFieldˣ)
    (ht : ∀ v k, VertCmp.GReads Q v (N k) (t k) fun e y => (m' : ℝ) * VertCmp.lam (A k) v e y)
    (M : LB Q.X) (hM : M.IsLB) (s : M.ι → Q.X.functionFieldˣ) (hs : IsRatSec M s)
    (hMs : ∀ v, VertCmp.GReads Q v M s fun e y =>
      (m' : ℝ) * (VertCmp.lam (A (.inl false)) v e y - VertCmp.lam (A (.inl true)) v e y)) :
    (∑ᶠ y, if LiesOverPl V v y then (haveI := V.ar.isLocallyNoetherian;
      ((((L (.inl false)).tens (L (.inl true)).dual).div hr).mult y : ℝ)) *
        vertNum p V d (fun j => L (.inr j)) y else 0) / ((V.deg : ℝ) * (m : ℝ) ^ (d + 1)) =
    (∑ᶠ y : Q.X, if (Q.p y).asIdeal = v.asIdeal then
      (((divOfRatSec hM hs).mult y * VertCmp.pdeg p (fun k => N (.inr k)) y : ℤ) : ℝ) else 0) / (m' : ℝ) ^ (d + 1) := by
  choose u hu using fun k => UpperTheory.norms_give_rational_sections F Y C (A (.inr k)) V (L (.inr k)) m _ (hL (.inr k))
  have key := CovCmp.vsum_cmp V (Cover.ofModel Q hQ) v p hp hd m m' hm hm'
    (fun v e y => VertCmp.lam (A (.inl false)) v e y - VertCmp.lam (A (.inl true)) v e y)
    (fun k => VertCmp.lam (A (.inr k))) (fun k => (L (.inr k)).isLB) u hu
    ((L (.inl false)).tens (L (.inl true)).dual).isLB hr
    (fun v => ⟨hr, ⊤, trivial, fun e y z yt i _ a₁ a₂ a₃ _ => by
      refine (hrn v e y z yt i a₁ a₂ a₃).symm.trans ?_
      simp only [VertCmp.lam, hD]
      ring⟩)
    (N₂ := fun k => N (.inr k)) (fun k => hN (.inr k)) (fun k => t (.inr k))
    (fun k v => CovCmp.cRead_of_gReads Q hQ (ht v (.inr k))) hM hs (fun v => CovCmp.cRead_of_gReads Q hQ (hMs v))
  rw [Cover.deg_ofModel, Nat.cast_one, one_mul] at key
  refine Eq.trans ?_ key
  congr 1
  refine finsum_congr fun y => ?_
  rw [vertNum_eq, Int.cast_mul]
  exact if_congr Iff.rfl rfl rfl

set_option maxHeartbeats 1000000 in
