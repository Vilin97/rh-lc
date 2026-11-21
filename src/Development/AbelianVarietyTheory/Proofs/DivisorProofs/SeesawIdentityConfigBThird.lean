module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingConfigurationLeviIntegralImports
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAStabilizerThetaReal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAStabilizerThetaFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAStabilizerThetaGlobal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SobolevBoundFiniteFamily

@[expose] public section

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.XTermBoundQ

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Decay

open GlobalTheory.XTermDecay

end Decay

end GlobalTheory.XTermBoundQ

end
