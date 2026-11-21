import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SegreLiftVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver intNum IsMultiProjPrime)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def SegreLiftPrime.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)), IsMultiProjPrime W →
      IsMultiProjPrime (segreLift ι F W)

theorem SegreLiftPrime.hyps : IsMultiProjPrime (⊥ : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver ℚ (fun _ : Unit => Fin 2))) :=
  NumbersDVR.isMultiProjPrime_bot

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
