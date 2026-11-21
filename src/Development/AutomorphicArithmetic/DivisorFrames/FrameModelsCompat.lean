module

public import Mathlib
public import Development.AutomorphicArithmetic.LocalEmbeddings.VertCmp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisor
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.Toroidal
open GlobalTheory.VertCmp
open scoped Classical

section
open GlobalTheory.ShFam.Pad.Pull GlobalTheory.LieMet MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv actR)

attribute [local instance] Over.cartesianMonoidalCategory

private theorem frame_pull {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {l : Level H} {c : Coeff l}
    {g : X' ⟶ X} (mu : SABMap t' t g) {R : Type} [CommRing R] {x' : Sp R ⟶ X'} {x : Sp R ⟶ X} (hx : x' ≫ g = x)
    {f : c.F →+* R} {u : Vecs Dw t R} (h : GlobalTheory.LocM.IsFrame t f x u) :
    ∃ v : Vecs Dw t' R, GlobalTheory.LocM.IsFrame t' f x' v ∧ ∀ τ i, v τ i ≫ mu.φ = u τ i := by
  have ex : ∀ τ i, ∃ V : TanM x' t'.G, pushE mu x' hx V = tanOf (h.1 τ i).1 := fun τ i =>
    (pushE mu x' hx).surjective _
  choose V hV using ex
  have e : ∀ τ i, (tv (V τ i)).left ≫ mu.φ = u τ i := fun τ i => congrArg (fun z => (tv z).left) (hV τ i)
  refine ⟨fun τ i => (tv (V τ i)).left, ⟨fun τ i => ⟨isTan_tv _, fun a => ?_⟩, fun τ w hw he => ?_⟩, e⟩
  · refine (eig_iff (V τ i) a _).2 ((pushE mu x' hx).injective ?_)
    rw [pushE_act, map_smul, hV]
    exact (eig_iff _ a _).1 ((h.1 τ i).2 a)
  · have := h.2 τ (w ≫ mu.φ) (isTan_push mu x' hx hw) fun a => by
      rw [Category.assoc, ← mu.act, ← Category.assoc, he, Category.assoc]
    refine (existsUnique_congr fun cf => comb_push mu hx (fun i => isTan_tv (V τ i)) hw cf).1 ?_
    simpa only [e] using this

end
