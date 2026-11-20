import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsRename
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.IntNumRelabel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem map_comap_renameEquiv {F : Type u} [Field F] {S K' : Type} {κ : S → Type}
    {ι' : K' → Type} (σ : (Σ s, κ s) ≃ (Σ k', ι' k')) (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι')) :
    (P.comap (rename σ)).map (renameEquiv F σ) = P := by
  have h : P.comap (rename σ) = P.comap (renameEquiv F σ) := rfl
  rw [h]
  exact Ideal.map_comap_of_surjective _ (renameEquiv F σ).surjective P

theorem RenameHilbFn.proof : RenameHilbFn.Statement.{u} := by
  intro F _ S K' _ _ κ ι' E σ hσ P m
  have h := Relabel.hilbFn_map_rename E σ hσ (P.comap (rename σ)) (m ∘ E.symm)
  rw [map_comap_renameEquiv σ P] at h
  rw [h]
  congr 1

end

end GroundTheory.Heights₂.Heights.FieldNumbers
