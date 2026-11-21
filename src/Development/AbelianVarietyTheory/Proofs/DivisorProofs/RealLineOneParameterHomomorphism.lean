module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdeleCharacterEqOneIntegralUnitsUnramifiedAdelic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormallyUnramifiedRingOfIntegersIffDifferentIdea

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UnrEuler Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped nonZeroDivisors
open Formalism.L2.Host (aboveF)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.UnrEuler

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

open Classical in

end GlobalTheory.UnrEuler
