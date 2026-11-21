import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPointResidueNonzero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimensionOfDominantFlatCover

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} [IsIntegral X]
  {E : X.Modules} {r : ℕ} {h : VMetric p E r}

omit [IsIntegral X] in

theorem charZero_residueField_genericPoint (Y : Scheme.{0}) [IsIntegral Y] (hc : CharZero Γ(Y, ⊤)) :
    CharZero (Y.residueField (genericPoint Y)) := by
  have h₁ : CharZero Y.functionField := charZero_of_injective_ringHom
    (f := (Y.presheaf.germ ⊤ (genericPoint Y) trivial).hom) (germ_injective_of_isIntegral _ _ _)
  let f : Y.functionField →+* Y.residueField (genericPoint Y) := (Y.residue (genericPoint Y)).hom
  exact charZero_of_injective_ringHom f.injective

end GlobalTheory
