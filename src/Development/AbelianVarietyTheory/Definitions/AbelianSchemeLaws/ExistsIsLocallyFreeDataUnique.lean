import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.BijectiveToPushforwardComp
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.TwistingSheafQuasicoherentLocallyFree

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
noncomputable section
namespace GlobalTheory.AbLaw
open GlobalTheory.LB
variable {X X' : Scheme.{0}}

abbrev lbSheaf (M : LB X) : X.Modules := toMod M

namespace lbSheaf

variable {M M' : LB X} {V W : X.Opens}

variable (M V) in

theorem exists_restrict_iso (hM : M.IsLB) (x : X) :
    ∃ (U : X.Opens) (_ : x ∈ U), Nonempty (unitMod U.toScheme ≅ (lbSheaf M).restrict U.ι) := by
  have hx : x ∈ ⨆ i, M.U i := by rw [hM.cover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  exact ⟨M.U i, hi, ⟨GlobalTheory.LB.chartIso hM i⟩⟩

def unitIso (hM : M.IsLB) (t : LB.Gen M) (ht : t.IsGen) :
    unitMod X ≅ lbSheaf M := GlobalTheory.LB.unitIso hM t ht

theorem triv_iff (hM : M.IsLB) :
    Triv M ↔ Nonempty (lbSheaf M ≅ unitMod X) :=
  (exists_isGen_iff_nonempty_iso hM).trans ⟨fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ => ⟨e.symm⟩⟩

def pullbackIso (hM : M.IsLB) (π : X' ⟶ X) :
    (Scheme.Modules.pullback π).obj (lbSheaf M) ≅ lbSheaf (M.pull π) := GlobalTheory.LB.pullbackIso hM π

theorem triv_pull_iff (hM : M.IsLB) (π : X' ⟶ X) :
    Triv (M.pull π) ↔
      Nonempty ((Scheme.Modules.pullback π).obj (lbSheaf M) ≅ unitMod X') :=
  (triv_iff (LB.isLB_pull hM π)).trans
    ⟨fun ⟨e⟩ => ⟨pullbackIso hM π ≪≫ e⟩, fun ⟨e⟩ => ⟨(pullbackIso hM π).symm ≪≫ e⟩⟩

end lbSheaf

end GlobalTheory.AbLaw
