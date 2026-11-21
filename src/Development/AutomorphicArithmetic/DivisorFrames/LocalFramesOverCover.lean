module

public import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.RootFrame

section SlopeTestRemainingChoices

private theorem sp_comp {S T U : Type} [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) :
    spMap (ψ.comp φ) = spMap ψ ≫ spMap φ := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

private theorem sp_dual_comp {S T U : Type} [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) :
    spMap (dualMap (ψ.comp φ)) = spMap (dualMap ψ) ≫ spMap (dualMap φ) := by
  rw [← sp_comp]
  congr 1
  exact RingHom.ext fun x => by ext <;> simp [dualMap]

private theorem sp_inj {S T : Type} [CommRing S] [CommRing T] {φ ψ : S →+* T} (h : spMap φ = spMap ψ) : φ = ψ :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

private theorem exists_germ {G Z : Scheme.{0}} (j : G ⟶ Z) {U : Z.Opens} (hU : IsAffineOpen U) (z : G) (hz : j z ∈ U) :
    ∃ α : Γ(Z, U) →+* G.presheaf.stalk z, spMap α ≫ hU.fromSpec = G.fromSpecStalk z ≫ j := by
  refine ⟨(j.stalkMap z).hom.comp (Z.presheaf.germ U (j z) hz).hom, ?_⟩
  rw [sp_comp, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← hU.fromSpecStalk_eq_fromSpecStalk hz]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

private theorem core {X : Scheme.{0}} {t : SAB H X} {R S K B L : Type} [CommRing R] [CommRing S] [CommRing K]
    [CommRing B] [CommRing L] {x : Sp R ⟶ X} {y : Sp B ⟶ X} (α : R →+* S) (io : S →+* K) (s : B →+* S) (κ : B →+* L)
    (φ : L →+* K) (hc : io.comp s = φ.comp κ) (hy : spMap s ≫ y = spMap α ≫ x) {g m : ℕ}
    {e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)} (he : IsTanBasis t x e)
    {f : Fin m → (Sp (DualNumber B) ⟶ t.G.left)} (hf : ∀ i, IsTanAtG t y (f i))
    {u : Fin m → (Sp (DualNumber L) ⟶ t.G.left)} (T : Matrix (Fin m) (Fin m) L)
    (hu : ∀ i, IsCombAtG t (spMap κ ≫ y) (fun k => spMap (dualMap κ) ≫ f k) (fun k => T k i) (u i)) :
    ∃ a : Fin m → Fin g → S,
      (∀ i, IsCombAtG t (spMap α ≫ x) (fun k => spMap (dualMap α) ≫ e k) (a i) (spMap (dualMap s) ≫ f i)) ∧
      ∀ i, IsCombAtG t (spMap (io.comp α) ≫ x) (fun k => spMap (dualMap (io.comp α)) ≫ e k)
        (fun k => ∑ l, io (a l k) * φ (T l i)) (spMap (dualMap φ) ≫ u i) := by
  choose a ha using fun i => (he.2 S α _ (GlobalTheory.LieMet.isTan_map s hy (hf i))).exists
  refine ⟨a, ha, fun i => ?_⟩
  have h1 := fun l => GlobalTheory.LatDRFree.comb_map t io (ha l)
  have h2 := GlobalTheory.LatDRFree.comb_map t φ (hu i)
  have e1 : spMap φ ≫ spMap κ ≫ y = spMap (io.comp α) ≫ x := by
    rw [← Category.assoc, ← sp_comp, ← hc, sp_comp, sp_comp, Category.assoc, Category.assoc, hy]
  simp only [← Category.assoc, ← sp_dual_comp] at h1
  rw [← sp_comp] at h1
  rw [e1] at h2
  simp only [← Category.assoc, ← sp_dual_comp, ← hc] at h2
  exact tanLinG _ (fun k => GlobalTheory.LieMet.isTan_map (io.comp α) rfl (he.1 k)) _ (Matrix.of fun k l => io (a l k))
    (fun l => φ (T l i)) _ h1 h2

end SlopeTestRemainingChoices
