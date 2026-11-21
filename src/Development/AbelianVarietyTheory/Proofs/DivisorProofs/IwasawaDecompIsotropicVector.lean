module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLines
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanAdeleCMPrescribedEmbeddingValue
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)

open scoped TensorProduct NNReal Matrix

noncomputable section

namespace GlobalTheory.IwaAdelicIso

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


theorem piInf_inclR {w : InfinitePlace F} (τ : EmbOver E w) (e : E) : piInf τ (inclR (F := F) (AF F) e) = τ.1 e := by
  rw [show inclR (F := F) (AF F) e = (1 : AF F) ⊗ₜ[F] e from rfl, GlobalTheory.RealLift.KLineProof.piInf_tmul, map_one, map_one, one_mul]

end GlobalTheory.IwaAdelicIso

namespace GlobalTheory.IwaAdelicIso

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end GlobalTheory.IwaAdelicIso
