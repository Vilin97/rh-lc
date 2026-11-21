import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceFormLinearIsometryEqMulNormOneTorus
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelPurity
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelCohomologicalModel
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CuspidalMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BorelCasselman
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMatInjective
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traceForm_linearIsometry_eq_mul_normOneTorus : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (u β : B.A), B.σ β = β * ((-1) ^ n * u) → Algebra.adjoin K.E {u} = ⊤ → (∀ y, (∀ z, B.herm β y z = 0) → y = 0) → ∀ f : B.A →ₗ[K.E] B.A, Function.Surjective f → (∀ y z, B.herm β (f y) (f z) = B.herm β y z) → ∃ a : B.Aˣ, a ∈ B.T ∧ ∀ y, f y = (a : B.A) * y := by
  first | exact @GlobalTheory.IsomMulTorus.isom_eq_mul | exact GlobalTheory.IsomMulTorus.isom_eq_mul | (intros; apply GlobalTheory.IsomMulTorus.isom_eq_mul <;> assumption)
