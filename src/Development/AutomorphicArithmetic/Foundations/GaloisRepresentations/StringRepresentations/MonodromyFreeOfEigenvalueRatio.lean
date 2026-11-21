import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.WeightsConj
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilRepEquivOfCharpolyEq
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PstAndWdAtOfIsRegAlg
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RankOneLocalComponentDet
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdmissibleOfRankOneUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormEqOfSamePlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRecLawsSuppUnitSurj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IrreducibleWdEigenEqualNorm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedDirectSum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RootsCharpolySmulMatrix
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.LocalGlobalOfIwahori
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial Module
open GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

namespace UpperTheory.GalN

section Lin
variable {V : Type} [AddCommGroup V] [Module ℂ V]

end Lin

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']

def EV (a : WDRep h V) (χ : ↥(Ine (F := E) A) → ℂ) (v : V) : Prop := ∀ s, a.ρ (ineIncl h s) v = χ s • v

def Win (a : WDRep h V) (S : Set ℝ) : Prop :=
  ∀ χ, (∀ v, EV a χ v → a.N v = 0) → ∀ r v, EV a χ v → v ∈ absSpace (a.ρ (frob h)) r → v ≠ 0 → r ∈ S

end UpperTheory.GalN
