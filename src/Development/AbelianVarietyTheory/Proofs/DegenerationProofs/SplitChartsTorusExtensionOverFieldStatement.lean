module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitChartsTorusExtensionOverField
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitCharts_torus_extension_over_field : ∀ (K : Type) [Field K] (H : Over (Sp K)) [GrpObj H] [IsCommMonObj H] [Smooth H.hom] [IsSeparated H.hom] [QuasiCompact H.hom] (C : Charts H.left) (d : ℕ) (c : Fin d → C.Cl) (i : splitTorus (Sp K) (Fin d → ℤ) ⟶ H), GeometricallyConnected H.hom → C.Torus c i → ∃ (B : Over (Sp K)) (_ : GrpObj B) (q : H ⟶ B), IsAbelianScheme B ∧ IsMonHom q ∧ Flat q.left ∧ Surjective q.left ∧ IsAffineHom q.left ∧ IsPullback i (toUnit _) q (η[B]) ∧ ∀ a, ∃ (V : B.left.Opens) (h : C.W a = q.left ⁻¹ᵁ V), IsAffineOpen V ∧ ∀ u, HasWt i (C.W a) u 0 ↔ u ∈ Set.range (q.left.appLE V (C.W a) h.le).hom := by
  intro K _ H _ _ _ _ _ C d c i hc hT
  haveI : Subsingleton Γ(H.left, (⊥ : H.left.Opens)) :=
    ⟨fun a b => TopCat.Sheaf.eq_of_locally_eq' H.left.sheaf (fun e : Empty => e.elim) ⊥
      (fun e : Empty => e.elim) bot_le a b (fun e : Empty => e.elim)⟩
  have hzero : ∀ a : Γ(H.left, (𝟙 H.left : H.left ⟶ H.left) ⁻¹ᵁ (⊥ : H.left.Opens)),
      GlobalTheory.UU.IsWt i _ a 0 ↔ ∃ c, ((𝟙 H.left : H.left ⟶ H.left).app ⊥).hom c = a := by
    simp only [Scheme.Hom.preimage_bot]
    intro a
    constructor
    · intro _
      exact ⟨0, Subsingleton.elim _ _⟩
    · intro _
      have : a = 0 := Subsingleton.elim _ _
      rw [this]
      exact GlobalTheory.UU.isWt_zero 0
  have hstable : Stable i ((𝟙 H.left : H.left ⟶ H.left) ⁻¹ᵁ (⊥ : H.left.Opens)) := by
    simp only [Scheme.Hom.preimage_bot]
    intro Y t g h
    simpa only [Scheme.Hom.preimage_bot] using h
  exact @GlobalTheory.SplitChartsField.main (Sp K) (Fin d → ℤ) _ H _ H.left i (𝟙 H.left : H.left ⟶ H.left) _ ⊥
    hT.hom (isAffineOpen_bot _) hzero hstable K _ H _ _ _ _ _ C d c i hc hT
