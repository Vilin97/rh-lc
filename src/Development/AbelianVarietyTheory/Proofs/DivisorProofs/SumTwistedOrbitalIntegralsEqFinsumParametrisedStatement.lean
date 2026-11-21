import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTwistedOrbitalIntegralsEqFinsumParametrised
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
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_twistedOrbitalIntegrals_eq_finsum_parametrised : ∀ (G : Type) [Group G] [TopologicalSpace G] (θ : G →* G) (Kg : Subgroup G) (S : Set G) (f : G → ℂ) (C : Type) (ι : C → G) (N : C → ℂ), (∀ c, ι c ∈ S) → (∀ y ∈ S, ∃ c g, y = g⁻¹ * ι c * θ g) → (∀ c c', (∃ g, ι c' = g⁻¹ * ι c * θ g) → c = c') → (∀ y g, g⁻¹ * y * θ g ∈ S ↔ y ∈ S) → (∀ y g, twOrb θ Kg (g⁻¹ * y * θ g) f = twOrb θ Kg y f) → (∀ c, twOrb θ Kg (ι c) f = N c) → clSum θ Kg S (fun _ => 1) f = ∑ᶠ c, N c := by
  first | exact @GlobalTheory.BCT.ClSumParam.clSum_eq_finsum_param | exact GlobalTheory.BCT.ClSumParam.clSum_eq_finsum_param | (intros; apply GlobalTheory.BCT.ClSumParam.clSum_eq_finsum_param <;> assumption)
