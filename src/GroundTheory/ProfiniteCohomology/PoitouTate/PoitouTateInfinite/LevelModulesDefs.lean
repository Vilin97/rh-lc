import Mathlib
import GroundTheory.ProfiniteCohomology.InflationRestriction.CohomologyResMemCohomologyConjInvariants
import GroundTheory.ProfiniteCohomology.Factor
import GroundTheory.ProfiniteCohomology.PoitouTate.PoitouTateInfinite.Restrict
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BrauerFrob
import GroundTheory.ProfiniteCohomology.RestrictedRamification.ClassFieldGSUnram
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleCohomology.Ramified
import GroundTheory.ProfiniteCohomology.InflationRestriction.DegreeOne
import GroundTheory.ProfiniteCohomology.Procyclic
import GroundTheory.ProfiniteCohomology.CupProducts.Functoriality
import GroundTheory.ProfiniteCohomology.CupProducts.Pairing
import GroundTheory.LocalFields.TameExtension
import GroundTheory.ProfiniteCohomology.IsProPGroupSubgroupIffIsPGroupMap
import GroundTheory.ProfiniteCohomology.NotDvdSuperIndexIffMap
import GroundTheory.ProfiniteCohomology.GaloisModules.FixedField
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseChangeMackey
import GroundTheory.ProfiniteCohomology.RestrictedRamification.Brauer
import GroundTheory.ProfiniteCohomology.RestrictedRamification.HighDecomp
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain CategoryTheory GroundTheory.Global

attribute [local instance 2000] Rep.hV2

noncomputable section

variable {K : FiniteSubfield} {S : Set (HeightOneSpectrum (𝓞 K.1))}

theorem isOpen_ker_ρ {k G : Type*} [CommRing k] [Group G] [TopologicalSpace G] (A : Rep k G) [IsDiscreteRep A]
    [Finite A] : IsOpen ((A.ρ.ker : Subgroup G) : Set G) := by
  have e : ((A.ρ.ker : Subgroup G) : Set G) = ⋂ a : A, (stabilizer A.ρ a : Set G) := by
    ext g
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter]
    constructor
    · intro h a
      change A.ρ g a = a
      rw [h, Module.End.one_apply]
    · intro h
      exact LinearMap.ext fun a => h a
  rw [e]
  exact isOpen_iInter_of_finite fun a => isOpen_stabilizer A a

variable {T : Set (HeightOneSpectrum (𝓞 K.1))} (h : T ⊆ S)

variable (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S))
  (hM : ∀ g, gsResCont (Ω := ℚ̄) h g = 1 → M.ρ g = 1)

end

end GroundTheory.ProfCoh
