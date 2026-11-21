import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRootOfUnityFixedDvdWeilGroupDegree
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ConclusionFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapTop
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinExistsHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlobalArtinReciprocityHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousExtensionAdicCompletion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormEmbeddingIntegerLeOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedCharIsCrystallineHodgeTateZero
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsCrystallineJumpsOfIsIsoMatrixGaloisRepresentat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineTwistCrystallineCharacterJumpsShift
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysInvAndHodgeTateJumpsNeg
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSumOfIsCrys
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodRingsRegularPhiSurjectiveFil
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsAlgebraicVectorSpanningSubspace
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AinfActionTiltFixedOfFrobeniusRelation
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowEqOfRoot
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
import GroundTheory.LocalFields.FormalGroups.LubinTateGroup
import Development.AbelianVarietyTheory.CrystallinePeriods.AdicMaps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharZeroAdicCompletion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecompositionGroupLocalGaloisIso
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import GroundTheory.LocalFields.ConductorReciprocity
import GroundTheory.LocalFields.LubinTateReciprocity
import GroundTheory.LocalFields.Existence
import GroundTheory.LocalFields.KroneckerWeber
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinFrobeniusAction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalEmbeddingWeilActionFiniteExtension
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.IsAdicCompleteOfLe
import GroundTheory.LocalFields.LubinTateLimitGalois
import GroundTheory.LocalFields.LubinTateUnramified
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMaps
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocF
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FKEqResDeg
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdSubOfDvdSubX
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPlaceEmb
import GroundTheory.LocalFields.MaximalUnramified
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineCharacterJumpsOfExactDegree
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AwayOfInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyLocalPeriodRingsData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisToBdRPlusInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusIsDomainBdRIsField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PadicIntHomUnique
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisLoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalPeriodRingsDataUnramifiedLaws
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalPeriodRingsSectionEqAinfToBdRPlus
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPrescribedUnramifiedKummer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFilPIffEvPt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JMemFilPOfApprox
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusPeriodRingInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEmbOfFixed
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisIncl
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnramifiedPeriodAinfUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyClosureHomTiltField
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisLinearDisjointStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemMaxUnramifiedOfCrystallineRatioStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvFilD
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsBisExtra
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffEqZeroOfStable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusEigenFilOneIsUnitExactDegree
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineTIsUnitBcrisAndUniformizerBdRPlus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneRelUnique
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotSemistableOfPotCrystallineDecompositionGroup
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IdealValuations.LocComplY
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPotCrysAtOfMono0
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamPotentiallySemistable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterCrystalline
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.MetAndHolds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeLAdicCharacterAboveOfPublished
import Development.AutomorphicArithmetic.ThetaCorrespondence.AlgebraicCharacters.AlgebraicCharacterWD
import Development.AutomorphicArithmetic.ThetaCorrespondence.GaloisRepresentations.HeckeDeRham

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.LocLanglands GlobalTheory.WeilDeligne GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LocGL
open GlobalTheory GlobalTheory.Published

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Int.Inp

theorem pst : GlobalTheory.Published.DeRhamPotSemistable := GlobalTheory.deRham_potentiallySemistable

theorem alg : GlobalTheory.Published.AlgebraicCharacterWD :=
  UpperTheory.Lit.CharWD.algebraicCharacterWD GlobalTheory.globalArtinReciprocity_holds UpperTheory.Lit.heckeLAdicCharacterDeRham pst

theorem crys : GlobalTheory.Published.HeckeLAdicCharacterCrystalline := by
  have hD := UpperTheory.Lit.heckeLAdicCharacterDeRham
  have hB := pst
  have hW := alg
  intro E Ω _ _ _ _ _ l _ P AI hT ι art ha χ n μ h1 h2 h3 w A h O _ _ _ Bw hj hu
  obtain ⟨a, ha'⟩ := GlobalTheory.localArtinExists_holds E Ω A w h
  have hξ := ParamAboveModel.isComp_loc (w := w) χ
  have hc : Continuous fun g : ↥(ReciprocityTheory.Gal.Dec (F := E) A) =>
      (((rk1 μ).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l)) := by
    refine continuous_matrix fun i j => ?_
    have e : (fun g : ↥(ReciprocityTheory.Gal.Dec (F := E) A) =>
      (((rk1 μ).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l)) i j) =
      fun g : ↥(ReciprocityTheory.Gal.Dec (F := E) A) => ((μ g : (Om l)ˣ) : Om l) := by
      funext g
      rw [Subsingleton.elim i j]
      simp [rk1]
    rw [e]
    exact Units.continuous_val.comp (h2.comp continuous_subtype_val)
  have hr := DeRhamPotSemistable.isPstAt hB hT.some Bw _ hc (hD E Ω l P AI hT ι art ha χ n μ h1 h2 h3 w A h O Bw hj).1
  rw [← GlobalTheory.PstLaws.unr_wdAt_iff Bw h hj P ι _ hr,
    hW E Ω l P AI hT ι art ha χ n μ h1 h2 h3 w A h O Bw hj _ hξ a ha',
    GlobalTheory.LocLanglands.Test.unr_lpOfChar_iff ha' hξ.1]
  exact (GlobalTheory.Published.CharCrysModel.isUnram_iff χ w).2 hu

theorem hk : GlobalTheory.Published.HeckeLAdicCharacterAbove :=
  GlobalTheory.HeckeAboveBridge.heckeLAdicCharacterAbove_of_potSemistable UpperTheory.Lit.heckeLAdicCharacterDeRham crys pst

end UpperTheory.Gal.Int.Inp
