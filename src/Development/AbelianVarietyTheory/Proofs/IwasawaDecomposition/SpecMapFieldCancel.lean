import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GradedLineBundleExists
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsoEqOfMapsAlongSection
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsPChartOfFramedPoint
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ModelChartLiftCoordsGeneratorIndep
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantLieBasisArcGroup
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantArcEigenbasisFlatBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsArcBasisBaseChange
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TangentVectorsThetaSectionArcWitnessBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.AdmissibleBasePowerSeriesSpanX
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameBaseChangeRingHom
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDiscreteValuationRingAndFiniteResidueFieldValu
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.BcField
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PullQkSurjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBimultOfIsPullDeg
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFiniteCubeInduction
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.PhiPow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsFamRep
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ZeroFLeftExt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PullTopZFConstUnit
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulEllTheta
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.RosatiAdjOfPoints
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsEllipticCurveTwoAdic
import Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.MapPowLeOfIsPullUnif
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsPullCubicalId
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CohenStructureFiniteOverNormalCompleteSubring
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LocM.FJ
open GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)

theorem GlobalTheory.spec_map_field_cancel {K C : Type} [Field K] [Field C] (gam : K →+* C) {X : Scheme} (y y' : Sp K ⟶ X)
    (h : spMap gam ≫ y = spMap gam ≫ y') : y = y' := by
  obtain ⟨⟨p, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y
  obtain ⟨⟨p', φ'⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y'
  simp only [Scheme.SpecToEquivOfField_symm_apply] at h ⊢
  have e : ∀ (q : X) (ψ : X.residueField q ⟶ CommRingCat.of K),
      spMap gam ≫ (Spec.map ψ ≫ X.fromSpecResidueField q) =
        (Scheme.SpecToEquivOfField C X).symm ⟨q, ψ ≫ CommRingCat.ofHom gam⟩ := by
    intro q ψ
    simp only [Scheme.SpecToEquivOfField_symm_apply, spMap, Spec.map_comp, Category.assoc]
  rw [e, e] at h
  have h2 := (Scheme.SpecToEquivOfField C X).symm.injective h
  simp only [Sigma.mk.inj_iff] at h2
  obtain ⟨rfl, h3⟩ := h2
  have h4 : φ = φ' := by
    have h5 : φ ≫ CommRingCat.ofHom gam = φ' ≫ CommRingCat.ofHom gam := eq_of_heq h3
    ext x
    apply gam.injective
    have := congrArg (fun f => f.hom x) h5
    simpa using this
  rw [h4]
