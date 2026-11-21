module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTangent
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.Cartier.CartierDiv GlobalTheory.ProjVar GlobalTheory.ProjSpace Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.CutModel

theorem valAt_algebraMap {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] (y : Sp K ⟶ Z)
    (a : Z.presheaf.stalk (below y)) :
    valAt y (algebraMap _ Z.functionField a) = (Scheme.stalkClosedPointTo y).hom a := by
  have h : RegAt (below y) (algebraMap _ Z.functionField a) := ⟨a, rfl⟩
  rw [valAt, dite_eq_left h, IsFractionRing.injective _ Z.functionField h.choose_spec]

theorem valAt_eq_zero_iff {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] (y : Sp K ⟶ Z)
    {f : Z.functionField} (h : RegAt (below y) f) : valAt y f = 0 ↔ ¬ UnitAt (below y) f := by
  obtain ⟨a, rfl⟩ := h
  have := Scheme.isLocalHom_stalkClosedPointTo' (R := K) y
  rw [valAt_algebraMap, ← not_iff_not, not_not, ← ne_eq, ← isUnit_iff_ne_zero, isUnit_map_iff]
  refine ⟨fun h => ⟨a, h, rfl⟩, fun ⟨b, hb, e⟩ => ?_⟩
  exact IsFractionRing.injective _ Z.functionField e ▸ hb

theorem valAt_mul {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] (y : Sp K ⟶ Z)
    {f g : Z.functionField} (h : RegAt (below y) f) (h' : RegAt (below y) g) :
    valAt y (f * g) = valAt y f * valAt y g := by
  obtain ⟨a, rfl⟩ := h
  obtain ⟨b, rfl⟩ := h'
  rw [← map_mul, valAt_algebraMap, valAt_algebraMap, valAt_algebraMap, map_mul]

variable {F : Type} [Field F] [NumberField F] (Y : Var F) (E : Type) [Field E] [NumberField E] [Algebra F E] {n : ℕ}
  (w : Fin n → Y.Fn) (c : Fin Y.dim → Fin n → 𝓞 E)






section Proj

variable (F) (N : ℕ)














end Proj


end GlobalTheory.TrueGeo.CutModel
