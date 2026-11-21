import Mathlib
import Development.AutomorphicArithmetic.DivisorFrames.ExistsExponentialUniformization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricFrameEqRiemannFormAtInteriorPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiFibrationLieLatticeFullStatement
import Development.AutomorphicArithmetic.DivisorFrames.HodgeGramEqPiMulHermFormOfExponential
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameCombinationCoeffUnique
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.Cartier
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LieHt GlobalTheory.LieRead GlobalTheory.GradedNorm GlobalTheory.Mean4O
open scoped ComplexOrder

private theorem below_map {K K' : Type} [Field K] [Field K'] (ι : K →+* K') {X : Scheme.{0}} (q : Sp K ⟶ X) :
    below (spMap ι ≫ q) = below q := by
  show q ((spMap ι) (IsLocalRing.closedPoint K')) = q _
  rw [Subsingleton.elim ((spMap ι) (IsLocalRing.closedPoint K')) (IsLocalRing.closedPoint K)]

private theorem sp_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

private theorem dual_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap (Chart.dualMapR (g.comp f)) = spMap (dualMap g) ≫ spMap (Chart.dualMapR f) := by
  rw [← sp_comp]
  congr 1
  ext r <;> simp [dualMap, Chart.dualMapR]
