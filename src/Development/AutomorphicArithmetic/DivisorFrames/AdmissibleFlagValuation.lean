module

public import Mathlib
public import Development.AutomorphicArithmetic.LocalEmbeddings.VertCmp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisor
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
public import Development.AutomorphicArithmetic.DivisorFrames.ExistsStalkPointLift
public import Development.AutomorphicArithmetic.DivisorFrames.FrameModelsCompat
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.Toroidal
open GlobalTheory.VertCmp
open scoped Classical

private theorem bc_comp {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {X : Scheme.{0}} {t : SAB H X} {A R S : Type} [CommRing A] [CommRing R] [CommRing S]
    (ρ : A →+* R) (χ : R →+* S) (u : Vecs Dw t A) : u.bc (χ.comp ρ) = (u.bc ρ).bc χ := by
  funext σ j
  rw [Vecs.bc, Vecs.bc, Vecs.bc, ← Category.assoc, ModelRelProbe.spMap_comp]
  congr 2
  ext z <;> simp [dualMap]

private theorem core {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {X : Scheme.{0}} {t : SAB H X} {l : Level H} {c : Coeff l} {R K k : Type} [CommRing R] [Field K]
    [Field k] {f : c.F →+* R} {x : Sp R ⟶ X} {G U : Vecs Dw t R} (hG : LocM.IsFrame t f x G)
    (hU : LocM.IsFrame t f x U) (ι : R →+* K) (hι : Function.Injective ι) (ev : R →+* k)
    (h : ∀ σ, Pull.Tri t (spMap ι ≫ x) (G.bc ι σ) (U.bc ι σ)) :
    (∀ σ, Pull.Tri t (spMap ev ≫ x) (G.bc ev σ) (U.bc ev σ)) ∧
      ∀ σ m, ∃ cf : Fin (Dw.mult σ) → R, IsCombAtG t x (G σ) cf (U σ m) ∧ ev (cf m) ≠ 0 := by
  have ex : ∀ σ m, ∃ cf : Fin (Dw.mult σ) → R, IsCombAtG t x (G σ) cf (U σ m) := fun σ m =>
    (hG.2 σ _ (hU.1 σ m).1 (hU.1 σ m).2).exists
  choose cf hcf using ex
  have tri : ∀ σ, Pull.Tri t (spMap ev ≫ x) (G.bc ev σ) (U.bc ev σ) := fun σ m => by
    obtain ⟨d, hd, hd'⟩ := h σ m
    have e : (fun i => ι (cf σ m i)) = d :=
      (Pull.frame_ind (GlobalTheory.T.isFrame_compose_ringHom_baseChange E H Dw _ _ _ _ _ _ _ ι _ _ hG) σ).2 _ _ _
        (GlobalTheory.LatDRFree.comb_map t ι (hcf σ m)) hd'
    refine ⟨fun i => ev (cf σ m i), fun i hi => ?_, GlobalTheory.LatDRFree.comb_map t ev (hcf σ m)⟩
    have : cf σ m i = 0 := hι ((congrFun e i).trans ((hd i hi).trans (map_zero ι).symm))
    exact (congrArg ev this).trans (map_zero ev)
  refine ⟨tri, fun σ m => ⟨cf σ m, hcf σ m, ?_⟩⟩
  exact ((tri σ).diag (Pull.frame_ind (GlobalTheory.T.isFrame_compose_ringHom_baseChange E H Dw _ _ _ _ _ _ _ ev _ _ hG) σ)
    (Pull.frame_ind (GlobalTheory.T.isFrame_compose_ringHom_baseChange E H Dw _ _ _ _ _ _ _ ev _ _ hU) σ) (GlobalTheory.LatDRFree.comb_map t ev (hcf σ m))).1
