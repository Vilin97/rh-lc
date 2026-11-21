import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SegreLiftVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver intNum IsMultiProjPrime)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def SegreLiftComap.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (W' : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F (segreIdx ι))), IsMultiProjPrime W' →
      segreRels ι F ⊆ W' →
      IsMultiProjPrime (W'.comap (segreIncl ι F)) ∧ W' = segreLift ι F (W'.comap (segreIncl ι F))

theorem SegreLiftComap.hyps :
    IsMultiProjPrime (⊥ : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver ℚ (segreIdx (fun _ : Unit => Fin 1)))) ∧
      segreRels (fun _ : Unit => Fin 1) ℚ ⊆
        ((⊥ : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver ℚ (segreIdx (fun _ : Unit => Fin 1)))) : Set _) := by
  have : ∀ k, Nonempty (segreIdx (fun _ : Unit => Fin 1) k) := fun k => by
    rcases k with _ | _
    · exact ⟨fun _ => (0 : Fin 1)⟩
    · exact ⟨(0 : Fin 1)⟩
  refine ⟨NumbersDVR.isMultiProjPrime_bot, ?_⟩
  rintro g ⟨c, d, rfl⟩
  obtain rfl : c = d := Subsingleton.elim _ _
  simp

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
