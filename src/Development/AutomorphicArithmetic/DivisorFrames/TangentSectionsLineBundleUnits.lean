module

public import Mathlib
public import Development.AutomorphicArithmetic.LocalEmbeddings.TriFrDefs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentSectionsOnNormalModel
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.LineNorm GlobalTheory.Mean4O
attribute [local instance] Over.cartesianMonoidalCategory

private theorem tri_alg {K : Type} [Field K] {n : ℕ} (T : Fin n → Fin n → K) (v C : Fin n → K) (m : Fin n)
    (hd : ∀ l, T l l ≠ 0) (hT : ∀ l k, l < k → T l k = 0) (hv : ∀ k, m < k → v k = 0)
    (h : v = ∑ l, C l • T l) : (∀ l, m < l → C l = 0) ∧ v m = C m * T m m := by
  have key : ∀ l, (∀ k, l < k → C k = 0) → v l = C l * T l l := by
    intro l hl
    rw [h, Finset.sum_apply, Finset.sum_eq_single l]
    · rfl
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with hk | hk
      · simp [hT k l hk]
      · simp [hl k hk]
    · simp
  have h0 : ∀ l, m < l → C l = 0 := by
    intro l
    induction l using WellFoundedGT.induction with
    | ind l ih =>
      intro hl
      have := key l fun k hk => ih k hk (hl.trans hk)
      rw [hv l hl] at this
      exact (mul_eq_zero.1 this.symm).resolve_right (hd l)
  exact ⟨h0, key m h0⟩

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {A : Type} [CommRing A] {s : X ⟶ Sp A} {ε : 𝓞 E →+* A} {n : ℕ}

private theorem tri_comb {S K : Type} [CommRing S] [Field K] {y : Sp S ⟶ X} (φ : S →+* K) (hφ : Function.Injective φ)
    {u : Fin n → (Sp (DualNumber K) ⟶ t.G.left)} (hu : ∀ m, IsTanAtG t (spMap φ ≫ y) (u m))
    (hi : IsIndep t (spMap φ ≫ y) u) {w w' : Fin n → (Sp (DualNumber S) ⟶ t.G.left)} {d d' : Fin n → K}
    (hd : ∀ l, d l ≠ 0) (h : GlobalTheory.TriFlag.IsTriOf t (spMap φ ≫ y) u d fun l => spMap (dualMap φ) ≫ w l)
    (h' : GlobalTheory.TriFlag.IsTriOf t (spMap φ ≫ y) u d' fun l => spMap (dualMap φ) ≫ w' l) {m : Fin n} {C : Fin n → S}
    (hC : IsCombAtG t y w C (w' m)) {g : S} (hg : φ g * d m = d' m) : C m = g ∧ ∀ l, m < l → C l = 0 := by
  choose T hT1 hT2 hT3 using h
  obtain ⟨v, hv1, hv2, hv3⟩ := h' m
  have := hi _ _ _ hv3 (GlobalTheory.LineNorm.Chart.comb_comb hu hT3 (GlobalTheory.LatDRFree.comb_map t φ hC))
  obtain ⟨h1, h2⟩ := tri_alg T v _ m (fun l => (hT1 l).symm ▸ hd l) hT2 hv2 this
  refine ⟨hφ (mul_right_cancel₀ (hd m) ?_), fun l hl => hφ ((h1 l hl).trans (map_zero φ).symm)⟩
  rw [hg, ← hv1, h2, hT1]

end
