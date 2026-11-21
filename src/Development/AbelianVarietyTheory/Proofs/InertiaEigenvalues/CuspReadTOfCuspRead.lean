import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CGTrue
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RecTExists
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecTExistsIff
import CompanionTheory.EightfoldTheory.ZeroLevelTheory.LocalLanglands.Imports
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Nontrivial
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitaryOfIsCsd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
open GlobalTheory.CuspRep GlobalTheory.HeightCounting

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RecT

abbrev RecFam : Type 1 :=
  ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω}
    {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w), IrrGL (w.adicCompletion E) → WD h

set_option synthInstance.maxHeartbeats 400000

variable {R : Ranks} {H : Formalism.BasicNotions.Host R}

variable {Ω : Type} [Field Ω] [Algebra H.E Ω] [IsAlgClosure H.E Ω]

end GlobalTheory.RecT

namespace GlobalTheory.RecT

open GlobalTheory.RowTie

variable {rc : RecFam} {D : D7} {T : WDTie D.nd D.naut}

set_option maxHeartbeats 2000000 in

section Read

open Formalism.MainNotions Formalism.MainNotions.N ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC

end Read

end GlobalTheory.RecT

namespace GlobalTheory.RecT

open GlobalTheory.RowTie

end GlobalTheory.RecT

end
