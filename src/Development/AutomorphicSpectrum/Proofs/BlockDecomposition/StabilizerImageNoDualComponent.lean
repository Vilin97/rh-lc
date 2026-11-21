import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
import Formalism.LocalToGlobal.ProjectiveLattices.UnramBridgeHolds
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContinuesConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine
import Development.AbelianVarietyTheory.Definitions.Foundations.AnalyticOnNhdTsumNpow
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinContinuationOfDoublingMethod
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelWeilLagrangianTermsAbsTsumLeHeightPoly
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAdelicHeightOrthogonalEmbeddingLePow
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StabilizerInductionLaw
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonarchimedeanGroupOfIsCompactIsOpen
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsClosedEmbeddingOfLocallyCompact
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.Garding
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InducedSectionZFinite
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAdelicUnitaryConjSelfDualMajorantLevelsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuesWithModerateGrowthShiftTranslatePowStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AnisotropicCoreWittFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledSpaceMaximalLevelLattice
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.ExistsNotEisContinues
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GodementSectionInvariantConvergent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FirstTermExistenceOfUniversal

noncomputable section

open scoped NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.RegSW PositivityTheory.RegularEisensteinLemmas
open GlobalTheory.Core.Rk.SWLaw (zeroSp)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.HyperbolicDecompositionLaw

variable {D : D7} {T T₀ T' : HSp D} {r : ℕ}

theorem mul_eq_one_of_gram {R : Type} [CommRing R] {c x G Gi : R} (hg : G * Gi = 1) (h : c * (G * x) = G) : c * x = 1 := by
  linear_combination Gi * h + (1 - c * x) * hg

theorem nnreal_eq_one_of_sq {x : ℝ≥0} (h : x * x = 1) : x = 1 := by
  rw [← sq] at h
  exact (pow_eq_one_iff_of_nonneg zero_le (n := 2) (by norm_num)).1 h

theorem absA_eq_one_of_conj (u : (AE D)ˣ) (h : conjUnit D.sp.cm.sig u * u = 1) : absA D u = 1 := by
  have h3 := congrArg (absE D.host.F D.host.E) h
  rw [map_mul, absE_conjUnit, map_one] at h3
  exact nnreal_eq_one_of_sq h3

theorem absA_det_matHom (g : GA D T₀) : absA D (Matrix.GeneralLinearGroup.det (matHom T₀ g)) = 1 := by
  have hg : (gA T₀).det * (giA T₀).det = 1 := by rw [← Matrix.det_mul, gA_mul_giA, Matrix.det_one]
  have h := congrArg Matrix.det (mt_unitary T₀ g)
  rw [Matrix.det_mul, Matrix.det_mul] at h
  have hadj : (adj (mt T₀ g)).det = cA D (mt T₀ g).det := by
    rw [adj, Matrix.det_transpose, RingHom.map_det]; rfl
  rw [hadj] at h
  have h2 : conjUnit D.sp.cm.sig (Matrix.GeneralLinearGroup.det (matHom T₀ g)) *
      Matrix.GeneralLinearGroup.det (matHom T₀ g) = 1 := Units.ext (mul_eq_one_of_gram hg h)
  exact absA_eq_one_of_conj _ h2

section Blocks

variable {R : Type} [CommRing R] {n a b : ℕ}

end Blocks

end GlobalTheory.CompanionTheory.HyperbolicDecompositionLaw

end
