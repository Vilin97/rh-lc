module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexPointsNonemptyDenseVariety

@[expose] public section

open NumberField CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

section
open GlobalTheory.Cartier GlobalTheory.CxPts ReciprocityTheory.ChartRestriction.G.DVR.FlatBC

private theorem ratVal_add' {k : Type} [CommRing k] {Z : Scheme.{0}} [AlgebraicGeometry.IsIntegral Z]
    {q : Z ⟶ Sp k} {σ : k →+* ℂ} {y : GlobalTheory.CxPts q σ} {f g : Z.functionField}
    (hf : RegAt (under y) f) (hg : RegAt (under y) g) :
    ratVal (f + g) y = ratVal f y + ratVal g y := by
  obtain ⟨U, hU, a, rfl⟩ := hf.exists_fnOf
  obtain ⟨W, hW, b, rfl⟩ := hg.exists_fnOf
  have hy : y ∈ ptsIn q σ (U ⊓ W) := mem_ptsIn.2 ⟨hU, hW⟩
  rw [← fnOf_resG (inf_le_left : U ⊓ W ≤ U) (gen_mem (memInf hU hW)),
    ← fnOf_resG (inf_le_right : U ⊓ W ≤ W) (gen_mem (memInf hU hW)), ← map_add,
    ratVal_fnOf hy, ratVal_fnOf hy, ratVal_fnOf hy, ev_add]

end

open GlobalTheory.Cartier GlobalTheory.CxPts in
