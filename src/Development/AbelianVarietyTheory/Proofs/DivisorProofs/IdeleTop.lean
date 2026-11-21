module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatHomOfGAdSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfSig
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativelyCompactStabilizerStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedAdelicLatticeClosureStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarMeasureClosedCompactDecomp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingMultiplicativeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalClosedNonzero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousCA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmatMulVec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddHaarLeftRightMulAdelicMatricesModule
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRestrictScalarsMatrixLeftRightMulAdeleTens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarCharMulConjEqAbs

@[expose] public section

noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.IwInt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem ideleTop : IsTopologicalGroup (AE F E)ˣ ∧ LocallyCompactSpace (AE F E)ˣ ∧ SecondCountableTopology (AE F E)ˣ ∧
    T2Space (AE F E)ˣ := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E) := e.secondCountableTopology
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  haveI : LocallyCompactSpace (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact ⟨inferInstance, Units.isClosedEmbedding_embedProduct.locallyCompactSpace,
    Units.isEmbedding_embedProduct.secondCountableTopology, inferInstance⟩


end GlobalTheory.IwInt
