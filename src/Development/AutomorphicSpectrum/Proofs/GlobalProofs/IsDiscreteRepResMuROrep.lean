import Mathlib
import ReciprocityTheory.Hypotheses.GalCoh
import GroundTheory.ProfiniteCohomology.RestrictedRamification.IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import GroundTheory.ProfiniteCohomology.RestrictedRamification.LocalMaps
import GroundTheory.ProfiniteCohomology.CohomologicalDimension.Subgroup
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.EqZeroOfBrauerLocalApplyEqZero
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.OpenSubgroups
import GroundTheory.ProfiniteCohomology.LocalClassFormation.FiniteVanishing.Vanishing
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.GSCd

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global FiniteSubfield
open GroundTheory.Global.IdeleGroup GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open scoped DirectSum

noncomputable section

attribute [local instance 2000] Rep.hV2

variable (K : FiniteSubfield) (S : Finset (HeightOneSpectrum (𝓞 K.1)))

abbrev Gs : Type := galUnramifiedOutside K.1 ℚ̄ (S : Set (HeightOneSpectrum (𝓞 K.1)))

end
end GlobalTheory.CompanionTheory.GSCd
