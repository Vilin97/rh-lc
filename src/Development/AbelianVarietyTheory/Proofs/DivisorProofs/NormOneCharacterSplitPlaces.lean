module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongApproximationSplitPlaceSkewHermitianUnitar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPlaceSplitsCompletelyNotMemEmbedding
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNormOneIdeles
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousInfiniteAdeleMap
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DegOneIffSurjective
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CountableIdealSummableAbsNormRpow
public import GroundTheory.GlobalFields.TateThesis.DegreeOneDensity
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeLEntireAndNonzeroAtOneHolds
public import GroundTheory.GlobalFields.TateThesis.PrimeZetaPole
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Hilbert90AdeleRingTensorQuadratic
public import Development.AutomorphicArithmetic.DivisorFrames.FiniteAdeleUnitsOpenSubgroupBasis

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LiftConst



private noncomputable def quo {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : (AE F E)ˣ →* GlobalTheory.NormOneIdele.N1 F E σ :=
  MonoidHom.codRestrict (MonoidHom.id _ / Units.map (cA σ : AE F E →* AE F E)) _ fun y => by
    have hc : ∀ z, cA σ (cA σ z) = z := GlobalTheory.UnitaryHeckeBaseChange.cA_cA h
    rw [GlobalTheory.NormOneIdele.mem_normOneIdeles]
    change ((y : AE F E) * cA σ (y⁻¹ : (AE F E)ˣ)) * cA σ ((y : AE F E) * cA σ (y⁻¹ : (AE F E)ˣ)) = 1
    rw [map_mul, hc]
    calc _ = ((y : AE F E) * (y⁻¹ : (AE F E)ˣ)) * cA σ ((y : AE F E) * (y⁻¹ : (AE F E)ˣ)) := by
          rw [map_mul]; ring
      _ = 1 := by rw [Units.mul_inv, map_one, mul_one]

private theorem continuous_quo {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : Continuous (quo h) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hc : Continuous (cA σ : AE F E → AE F E) :=
    IsModuleTopology.continuous_of_linearMap (cA σ : AE F E →ₐ[AF F] AE F E).toLinearMap
  exact (continuous_id.div' (Continuous.units_map (cA σ : AE F E →* AE F E) hc)).subtype_mk _
