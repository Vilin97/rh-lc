import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatOfIsFiniteOfFlatGeometricFibres
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralNthRootTestModelPoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CardTorsionTranslateZerosLt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsUnitNatCastSections
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LocallyQuasiFiniteOfFiniteGeometricPoints
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteTorsionSemiAbelian
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueOfIsAdicComplete
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniversalTorsionPairPolAV
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EqOneOfPowEqOneOfCompEqOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegrallyClosedInFractionFieldPowerSeries
import Formalism.LocalToGlobal.ProjectiveLattices.TowerOfAt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsQProjOverOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionCharacterCocycleDescent

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsCharExt

section Ring

variable (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C]

end Ring

theorem sp_id (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := Spec.map_id _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

def pull {S S' : Scheme.{0}} {a : S ⟶ X} {a' : S' ⟶ X} (g : S' ⟶ S) (h : g ≫ a = a') :
    (Over.mk a ⟶ t.G) →* (Over.mk a' ⟶ t.G) where
  toFun w := (Over.homMk g h : Over.mk a' ⟶ Over.mk a) ≫ w
  map_one' := MonObj.comp_one _
  map_mul' _ _ := MonObj.comp_mul _ _ _

end GlobalTheory.TorsCharExt
