import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.RecPJThAllNeBot
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpBijectiveUniformisation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifPowOf3
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSumReindex
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsSymmetricOfSymmetryGenerator
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowOActOfGlobalFns
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StarRingExtOfStar
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StalkMapInjectiveOfFlat
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaValueNaturalField
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionIsoOfLinearUniformisationTriple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ThetaGrpActIterateEqOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsUUOver
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaValueExistsUniqueOfChartIndependence
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGenMoveBack
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullGenLBIsGen
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SymmetricLiftActsRootOfUnityOnExpansions
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HasGenPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueThetaConst
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SecLinIffComb
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ExistsUniquePullExpands
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalisedPullbackSectionExpandsFamily
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GeneratorsCompare

open GlobalTheory.IndefiniteRowSideFullHecke Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS)

section Trans

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {D : DegData V (maximalIdeal V)}
  {A : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G : Over (Spec (CommRingCat.of V))} [GrpObj G]
  [IsCommMonObj G] (F : Type) [Field F] [Algebra (FractionRing V) F]

variable {F}

end Trans

section PEL

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V]
  [CharZero V] {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem torsionIso {t : SAB H (Sp V)} (P : PELUnif (maximalIdeal V) t) : P.TorsionIso := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := GlobalTheory.lawsAndExpansions
  exact GlobalTheory.UT.torsionIso_of_pelUnif h₁ h₂ h₃ h₄ h₅ E H _ _
    ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩ t P

end PEL

section Concl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

variable [StarRing (𝓞 E)] {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

variable (nab : NabV Xo c) (y) (F : Type) [Field F] [Algebra T.Fr F] (v : AddValuation F (WithTop ℚ)) (ν : c.F)
  (a : (E →+* ℂ) × ℕ → ℕ) {n : ℕ} (val : MvPolynomial (LtN Dw n) c.F → F)

variable {nab y F v ν a val}

end Concl

section Germs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}
  (C : IntegralChartA3 Xo c T io y) (P : PELUnif (maximalIdeal T.V) C.I.G) (Q : P.D.toPre.X → ℤ) {n : ℕ}
  {D' : DegData T.V (maximalIdeal T.V)} {A' : PolAV (Spec (CommRingCat.of T.Fr))} {G' : Over (Sp T.V)} [GrpObj G']
  [IsCommMonObj G'] {pD : IsPowDeg D'.toPre P.D.toPre n} {pA : IsPowPolAV A' P.A n} {pG : IsPowGrp G' C.I.G.G n}
  {U' : Unif (maximalIdeal T.V) D' A' G'} (PU : UnifPowOf3 pD pA pG U' P.U)
  (F : Type) [Field F] [Algebra T.Fr F] [Algebra T.V F] (v : AddValuation F (WithTop ℚ))

end Germs

end GlobalTheory.GeneratorsCompare
