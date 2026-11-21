module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometricOfSameNorms
public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelNeg
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverFunctionFieldMapEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsZeroOfInvOfNotRegularNormal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtPlaceOfNeZeroMaximalStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtPointSpecializingOutsideBasicOpen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularOfValuationBoundedAtPoints
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentOfCutSec

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
open GlobalTheory.Cartier

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VertOrd

section Ord

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]

theorem ord_pow' {f : X.functionField} (h0 : f ≠ 0) (z : X) (n : ℕ) :
    Scheme.ord (f ^ n) z = n * Scheme.ord f z := by
  induction n with
  | zero => simpa using (unitAt_one z).ord_eq_zero
  | succ n ih =>
    rw [pow_succ, Scheme.ord_mul (pow_ne_zero _ h0) h0, ih]
    push_cast
    ring

end Ord

open GlobalTheory.CoverNorm.Isom in

end GlobalTheory.VertOrd
