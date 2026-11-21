import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsHorizontalGeneratorOfCharts
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactification
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateSandwichOfPrismaticDieudonne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilCharSurjectiveAndMapRangeAl
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCobOneOfIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateInclusionRaynaudExtensionAlgebraicPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicCompleteOfFiniteBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteDualNumber
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LePreimageOfClosedPoint
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicCompleteOfPowLeOfPowLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreNotInClosureOfValuationRing
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RigidifiedOfChart
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ValuationRingHenselianAndSmoothPointsLift
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.WeilRos
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteAlgebrasOverHenselianAndComplete
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowEqScaleAndExistsUniqueTorsion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullbackBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoToBidualOfLocalFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiSqZeroNaturality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqZeroPointEqOfCotangentFormEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteProjectiveCotangentGlobalSectionsGroupScheStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCotangentFrameSmoothGroupSchemeStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyTorusExtensionOfIsGt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusExtensionPointsDivisible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupOmegaFiniteFreeAndPSqMemDlogSpanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTatePairingSandwich
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegrallyClosedInOfIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaFreeFiniteBijectiveOfSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTorusLeLieSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StAvDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.RosatiAdj
import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CotangentBidualToTangentFunctionInjective
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedOfIsPullbackOfSurjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyPadicIntRingHomOfIsAdicComplete
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomProperTrivialLocal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EigenvectorLieDegree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SpecialFibreUnits
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GlobalFunctionsDvrOpen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularOfRegularAtCodimOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedSpecialFibreGlobalField
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliSchemeLevelMapsHeckePointsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompactifiedModuliPartOneStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsValuationSubringComplexComapValEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelOfSplitAndLevelCoeffExist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentGeometricallyIrreducible
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemBasesNonempty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelChangeMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartStatementHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectionStatementHolds
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsIsComplEigenSubOfValuationRing
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DetCondTensorDefinite
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.PadicValNatAbsNormEqZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentBasisOfSplitTorsion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameCombinationCoeffUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GradedLineBundleExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTangentPresentationPrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationSubringDedekindOpenImmersion
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocallyOfFiniteTypeKer
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsCommVOfLe
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionSectionCoordsThetaTimesRoots
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.WeilIsGrpPullbackIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DvrArcExtensionMonoBase
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecialisationWithThetaPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PtMapDualBCLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisFrameMapImports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateMapPowEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateMapOpenImmersionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateSchemeFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateSchemeFlatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateDifferenceSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateGluedSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PropertyOfCodimOneLocalUnits
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralPointPullbackComparison
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentFrameBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionFrameInvariance
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtGMulVec
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFrameChangeByMatrices
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstLengthArchSectionEqSmulOfSameWeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadsZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModelRuleSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatWeightRuleReadsNonvanishingDetSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantLengthOfReadingHorizontalSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RuleSectionNowhereVanishingReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrOverHeightOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntFrExtension
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModuliPointIntegralFrameAfterFiniteExtension
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
import Formalism.LocalToGlobal.ProjectiveLattices.SatLeaves
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartFlagBaseHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointModelOverDvr
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ExistsNotIntegralLie
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SemiAbelianDvrExtensionsIsoCompatible
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericPointMemModuliOfMeetsAbelianLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHTFrameCpAndNonempty
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsUniformisedChartAfterValuationRingExt
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsCdvrFiniteExtension
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralFramedPointBaseChangeStable
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SupCLeISupGeneric
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.VVAlgebraMapNonneg
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcFamilyFourthConditionInvertiblePushforward
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteGaloisInertiaLiftsAbsoluteInertiaRat
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSubextensionPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteDvrExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PluckerMinorsProportional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundStatementHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelPAdicOverInclusion
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreConnectedOfProper
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIntegralPointThrough
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIsMaximalTensorProductOfIsLocalHom
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.InjectiveAlgebraMapOfDvrOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEmbeddingPadicComplexInt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEighthPowerPrincipalSiegelOfDenseStatement
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RangeSubsetAbLocusOfIsProper
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjOverLocallyOfFiniteTypeStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsIntegralCoeffZeroMulOfAevalInv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalPointFactorsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDvrIntegralClosureFinite

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

section Local

variable {l l' : Level H} {Xo : Moduli Dw l} {Xo' : Moduli Dw l'} {c : Coeff l} {c' : Coeff l'} {W : ValuationSubring ℂ}
  {Y : Model Xo' c' (c'.V W).subtype} {r : Xo'.XF c' ⟶ Xo.XF c} {ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)}
  {hle : c.F ≤ c'.F} {r₀ : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r₀} {x : ℝ} {Z : Comp Xo c} {τ : Psi H}
  {la : HeightOneSpectrum (𝓞 c.F)} {p : ℕ} [Fact p.Prime] {Xw : Y.X.Opens}

theorem exists_unit (hG : GenSt) (hL : Laws U x) (s : ArchSec U x Z (flatWt Dw τ)) (hc : IsCover Y r hle Z la p Xw)
    {R : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] {ξ : Sp R ⟶ Y.X} [IsOpenImmersion ξ] {β : c'.V W →+* R}
    (hβ : ξ ≫ Y.s = spMap β) (hξ : ξ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ∈ Xw) {g : ℕ}
    {e : Fin g → (Sp (DualNumber R) ⟶ Y.t.G.left)} (he : IsTanBasis Y.t ξ e) {U₁ U₂ : Fin g → Fin g → R}
    (h₁ : EigFam Y.t ξ (β.comp (embV c' W τ.1)) e U₁) (h₂ : EigFam Y.t ξ (β.comp (embV c' W (conjEmb τ.1))) e U₂)
    (K₁ : Fin (Dw.mult τ.1) → Fin g) (K₂ : Fin (Dw.mult (conjEmb τ.1)) → Fin g) (a₁ : Fin (Dw.mult τ.1) → Fin g → R)
    (a₂ : Fin (Dw.mult (conjEmb τ.1)) → Fin g → R) (ε : ℤˣ) :
    ∃ u : (Localization.Away ((p : R) * (pairDet a₁ (U₁ ∘ K₁) * pairDet a₂ (U₂ ∘ K₂))))ˣ,
      ∀ (k : Type) [Field k] [Algebra c.F k] (ψ : Localization.Away ((p : R) * (pairDet a₁ (U₁ ∘ K₁) * pairDet a₂ (U₂ ∘ K₂))) →+* k) (yy : Sp k ⟶ Xo'.XF c'),
        yy ≫ Y.j = spMap (ψ.comp (algebraMap R _)) ≫ ξ → ∃ fv : k,
          GVal Y r ν τ.1 s.sig yy (bcV Y.t (ψ.comp (algebraMap R _)) e) (fun i b => ψ (algebraMap R _ (U₁ (K₁ i) b)))
            (fun i b => ψ (algebraMap R _ (U₂ (K₂ i) b))) fv ∧
          ψ u = fv * ((ε : ℤ) : k) * ψ (algebraMap R _ (pairDet a₁ (U₁ ∘ K₁))) / ψ (algebraMap R _ (pairDet a₂ (U₂ ∘ K₂))) := by
  set q : R := (p : R) * (pairDet a₁ (U₁ ∘ K₁) * pairDet a₂ (U₂ ∘ K₂)) with hq
  have hu : IsUnit (algebraMap R (Localization.Away q) q) := IsLocalization.Away.algebraMap_isUnit q
  by_cases h0 : q = 0
  · refine ⟨1, fun k _ _ ψ _ _ => ?_⟩
    have := hu.map ψ
    rw [show algebraMap R (Localization.Away q) q = 0 from (congrArg _ h0).trans (map_zero _), map_zero] at this
    exact absurd this not_isUnit_zero
  have hle' : Submonoid.powers q ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors h0
  haveI : IsDomain (Localization.Away q) := IsLocalization.isDomain_localization hle'
  haveI : IsIntegrallyClosed (Localization.Away q) := isIntegrallyClosed_of_isLocalization _ _ hle'
  have hinj : Function.Injective (algebraMap R (Localization.Away q)) := IsLocalization.injective _ hle'
  let ρ := algebraMap R (Localization.Away q)
  have hu' : IsUnit ((p : Localization.Away q) * (ρ (pairDet a₁ (U₁ ∘ K₁)) * ρ (pairDet a₂ (U₂ ∘ K₂)))) := by
    rw [← map_natCast ρ, ← map_mul, ← map_mul]; exact hu
  have u₁ := isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_right hu')
  have u₂ := isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_right hu')
  have mp : ∀ {m : ℕ} (a V : Fin m → Fin g → R), ρ (pairDet a V) = pairDet (fun i b => ρ (a i b)) fun i b => ρ (V i b) :=
    fun a V => by
      rw [pairDet, pairDet, RingHom.map_det]
      congr 1
      ext i j
      simp [map_sum]
  haveI : IsOpenImmersion (spMap ρ) := IsOpenImmersion.of_isLocalization q
  obtain ⟨f, hf⟩ := hG E H Dw l l' Xo Xo' c c' W Y r ν hle r₀ U x hL Z τ s la p Xw Fact.out hc (Localization.Away q)
    (spMap ρ ≫ ξ) (ρ.comp β) inferInstance (by rw [Category.assoc, hβ, spMap_spMap]) (isUnit_of_mul_isUnit_left hu')
    (by rw [bot_map hinj]; exact hξ) g (bcV Y.t ρ e) (fun i b => ρ (U₁ (K₁ i) b)) (fun i b => ρ (a₁ i b))
    (fun i b => ρ (U₂ (K₂ i) b)) (fun i b => ρ (a₂ i b)) (isTanBasis_bc he ρ)
    (fun S _ φ => by
      rw [sp_sp, bcV_bcV]
      exact ⟨fun i => (h₁ S (φ.comp ρ)).1 (K₁ i), fun i => (h₂ S (φ.comp ρ)).1 (K₂ i)⟩)
    (mp a₁ _ ▸ u₁) (mp a₂ _ ▸ u₂)
  refine ⟨f * Units.map (Int.castRingHom _).toMonoidHom ε * u₁.unit * u₂.unit⁻¹, fun k _ _ ψ yy hy => ⟨ψ f, ?_, ?_⟩⟩
  · have := hf k ψ yy (by rw [sp_sp]; exact hy)
    rwa [bcV_bcV] at this
  · rw [eq_div_iff (u₂.map ψ).ne_zero, ← map_mul]
    change ψ (_ * (u₂.unit : Localization.Away q)) = _
    rw [← Units.val_mul, inv_mul_cancel_right]
    simp [ρ]

end Local

section Charts

variable {l l' : Level H} {Xo : Moduli Dw l} {Xo' : Moduli Dw l'} {c : Coeff l} {c' : Coeff l'} {W : ValuationSubring ℂ}
  {Y : Model Xo' c' (c'.V W).subtype} {r : Xo'.XF c' ⟶ Xo.XF c} {ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)}
  {hle : c.F ≤ c'.F} {r₀ : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r₀} {x : ℝ} {Z : Comp Xo c} {τ : Psi H}
  {la : HeightOneSpectrum (𝓞 c.F)} {p : ℕ} [Fact p.Prime] {Xw : Y.X.Opens} [StarRing (𝓞 E)]

variable (Y r ν) in

end Charts

section Top

variable {l l' : Level H} {Xo : Moduli Dw l} {Xo' : Moduli Dw l'} {c : Coeff l} {c' : Coeff l'} {W : ValuationSubring ℂ}
  {Y : Model Xo' c' (c'.V W).subtype} {r : Xo'.XF c' ⟶ Xo.XF c} {ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)}
  {hle : c.F ≤ c'.F} {r₀ : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r₀} {x : ℝ} {Z : Comp Xo c} {τ : Psi H}
  {la : HeightOneSpectrum (𝓞 c.F)} {p : ℕ} [Fact p.Prime] {Xw : Y.X.Opens}

end Top

open Module Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits in

open Module Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits in

end GlobalTheory.FlatModel

end
