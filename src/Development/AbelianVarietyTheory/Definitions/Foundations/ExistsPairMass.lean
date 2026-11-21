import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfIdem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90IntegralIdelesOfMovedPrimes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmFiniteAdeleIntegralSeparatedComplete
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitaryExtension
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPeriodPairIdealCurveLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTermsNormsIndependentRepresenta
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryDoubleCosetClassesFiniteCardLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryRationalConjIntersectionCardDvdInvariant

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

namespace GlobalTheory.NormSum.Model

theorem vac_mem_TT {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : Crv D cc δ) {a d : ℕ} {e0 : VC D a d → ℂ}
    (he : e0 ∈ Th D (tor0 D cc δ) (stdL D a) (stdL D d)) : e0 ∈ TT D (tor0 D cc δ) a d := by
  obtain ⟨-, hW, -⟩ := GlobalTheory.T.theta_space_selfDual_pair_at_most_line D (GlobalTheory.InducedType.induced_type D).1 cc δ hc a d (La0 D (tor0 D cc δ) a d)
    (Or.inr ⟨_, _, RepInv.sd_std D _, RepInv.sd_std D _, rfl⟩)
  refine ⟨he.1, 1, one_pos, fun x hx => ?_⟩
  rw [one_smul, hW x hx]
  funext w
  exact he.2 x hx w

end GlobalTheory.NormSum.Model
