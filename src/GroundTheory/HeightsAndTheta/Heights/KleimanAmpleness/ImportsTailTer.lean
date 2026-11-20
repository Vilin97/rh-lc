import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SegreLiftVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver intNum IsMultiProjPrime)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def SegreLiftRelDim.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)), IsMultiProjPrime W →
      relDim (segreLift ι F W) = relDim W

theorem SegreLiftRelDim.hyps : IsMultiProjPrime (⊥ : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver ℚ (fun _ : Unit => Fin 2))) :=
  NumbersDVR.isMultiProjPrime_bot

example (h : SegreLiftRelDim.Statement) := h ℚ Unit (fun _ => Fin 2) ⊥ SegreLiftRelDim.hyps

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
