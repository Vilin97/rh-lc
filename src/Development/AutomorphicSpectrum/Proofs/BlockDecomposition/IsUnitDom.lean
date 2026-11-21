import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.WeilM Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ContDiff

namespace GlobalTheory.CompanionTheory.ThetaCoord

variable {F : Type} [Field F] [NumberField F] {κ : Type}

variable (F κ) in

variable (F κ) in

def finOf (a : κ → AF F) : κ → FiniteAdeleRing (𝓞 F) F := fun i => (a i).2

def infOf (a : κ → AF F) : κ → mixedEmbedding.mixedSpace F :=
  fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (a i).1

end GlobalTheory.CompanionTheory.ThetaCoord

end
