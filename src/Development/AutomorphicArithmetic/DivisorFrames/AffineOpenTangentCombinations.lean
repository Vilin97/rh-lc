module

public import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverFunctionFieldMapEq

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.RootFrame

private theorem regAt_pull {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y) {x : V.G} {f : Y.Fn}
    (h : RegAt (V.π x) f) : RegAt x (V.φ f) := by
  obtain ⟨hη, e⟩ := V.φ_eq_fnMap
  rw [e]
  obtain ⟨U, hx, s, rfl⟩ := h.exists_fnOf
  have hy : x ∈ V.π ⁻¹ᵁ U := hx
  rw [SmallSec.fnMap_fnOf V.π hη _ (gen_mem hy)]
  exact regAt_fnOf hy _ _
