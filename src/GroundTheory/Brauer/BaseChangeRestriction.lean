import Mathlib
import GroundTheory.Brauer.SkolemNoether
import GroundTheory.Brauer.IsBrauerEquivalentIffNonemptyAlgEquiv
import GroundTheory.Brauer.TensorSimple
import GroundTheory.Brauer.BaseChangeCSA
import GroundTheory.Brauer.DoubleCentralizer
import GroundTheory.Brauer.Degree
import GroundTheory.ProfiniteCohomology.Colimit
import GroundTheory.ProfiniteCohomology.GaloisCohomology.UnitsInflationCochainsFHomApply
import GroundTheory.ProfiniteCohomology.GaloisCohomology.IsZeroGroupCohomologyQuotientToInvariantsGalAdd
import GroundTheory.ProfiniteCohomology.CohomologyFunctoriality
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Brauer

open CategoryTheory groupCohomology GroundTheory.ProfCoh

universe u

section Cocycles

variable {k : Type u} [CommRing k] {H : Type u} [Group H] [TopologicalSpace H]
  [IsTopologicalGroup H] {B : Rep.{u} k H} [IsDiscreteRep B]

end Cocycles

section Topology

variable {K Ks : Type u} [Field K] [Field Ks] [Algebra K Ks]

end Topology

section Main

variable {K Ks : Type u} [Field K] [Field Ks] [Algebra K Ks] [IsSepClosure K Ks]

instance isSepClosure_intermediateField (E : IntermediateField K Ks) : IsSepClosure E Ks :=
  ⟨IsSepClosure.sep_closed K, Algebra.isSeparable_tower_top_of_isSeparable K E Ks⟩

variable (E : IntermediateField K Ks)

end Main

end GroundTheory.Brauer
