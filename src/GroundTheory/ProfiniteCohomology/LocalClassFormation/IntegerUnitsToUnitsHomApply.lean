module

public import Mathlib
public import GroundTheory.ProfiniteCohomology.GaloisModules.CoeGalRootsOfUnityHomApply
public import GroundTheory.LocalFields.HerbrandLocalBase
public import GroundTheory.LocalFields.UnitsGalois
public import GroundTheory.TateCohomology.Characters

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory GroundTheory.LocalField ValuativeRel

variable (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

noncomputable abbrev galIntegerUnitsZ : Rep ℤ Gal(L/K) :=
  Rep.ofMulDistribMulAction Gal(L/K) 𝒪[L]ˣ

noncomputable def integerUnitsToUnits : galIntegerUnitsZ K L ⟶ galUnitsZ K L :=
  Rep.ofHom ⟨(MonoidHom.toAdditive (unitsIncl L)).toIntLinearMap, fun σ => by
    ext x
    rfl⟩

noncomputable def unitsValuation : galUnitsZ K L ⟶ Rep.trivial ℤ Gal(L/K) ℤ :=
  Rep.ofHom ⟨(unitsOrd L).toIntLinearMap, fun σ => by
    ext x
    exact unitsOrd_smul σ x.toMul⟩

@[simp]
theorem unitsValuation_hom_apply (x : Additive Lˣ) :
    (unitsValuation K L).hom x = ord ((x.toMul : Lˣ) : L) :=
  rfl

noncomputable def unitsValuationSES : ShortComplex (Rep ℤ Gal(L/K)) :=
  ShortComplex.mk (integerUnitsToUnits K L) (unitsValuation K L) (by
    ext x
    exact ord_unit (K := L) x.toMul)

theorem unitsValuationSES_shortExact : (unitsValuationSES K L).ShortExact where
  exact := GroundTheory.GroupCoh.shortComplex_exact_of_forall fun x hx =>
    (exact_unitsIncl_unitsOrd (L := L) x).1 hx
  mono_f := (Rep.mono_iff_injective _).2 fun _ _ h =>
    Additive.toMul.injective (unitsIncl_injective (K := L) (congrArg Additive.toMul h))
  epi_g := (Rep.epi_iff_surjective _).2 (unitsOrd_surjective (L := L))

end GroundTheory.ProfCoh
