module

public import Mathlib

@[expose] public section

open Matrix in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_field_stableRange_one_det_ne_zero :
    ∀ (κ : Type) [Field κ] (n : ℕ) (c d p q : Matrix (Fin n) (Fin n) κ),
      c * p + d * q = 1 → ∃ y : Matrix (Fin n) (Fin n) κ, (c * y + d).det ≠ 0 := by
  classical
  intro κ _ n c d p q h
  let C := Matrix.toLin' c
  let D := Matrix.toLin' d
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl (LinearMap.range D)
  let π := W.projectionOnto (LinearMap.range D) hW.symm
  have hπD (v : Fin n → κ) : π (D v) = 0 :=
    Submodule.projectionOnto_apply_of_mem_right hW.symm (LinearMap.mem_range_self D v)
  have hsurj : Function.Surjective (π ∘ₗ C) := by
    intro w
    refine ⟨p *ᵥ (w : Fin n → κ), ?_⟩
    have hdec : C (p *ᵥ (w : Fin n → κ)) + D (q *ᵥ (w : Fin n → κ)) = w := by
      simp only [C, D, Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, h,
        Matrix.one_mulVec]
    have hπW : π (w : Fin n → κ) = w := Submodule.projectionOnto_apply_left hW.symm w
    have hw := congrArg π hdec
    rwa [map_add, hπD, add_zero, hπW] at hw
  obtain ⟨g, hg⟩ := (π ∘ₗ C).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hsurj)
  have hdim : Module.finrank κ (LinearMap.ker D) = Module.finrank κ W := by
    have hker := LinearMap.finrank_range_add_finrank_ker D
    have hcompl := Submodule.finrank_add_eq_of_isCompl hW
    omega
  let e := LinearEquiv.ofFinrankEq _ _ hdim
  obtain ⟨K', hK⟩ := Submodule.exists_isCompl (LinearMap.ker D)
  let projK := (LinearMap.ker D).projectionOnto K' hK
  let Y : (Fin n → κ) →ₗ[κ] (Fin n → κ) := g ∘ₗ e.toLinearMap ∘ₗ projK
  refine ⟨LinearMap.toMatrix' Y, ?_⟩
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hM : (c * LinearMap.toMatrix' Y + d) *ᵥ v = C (Y v) + D v := by
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec]
    rfl
  rw [hM] at hv
  have hp : π (C (Y v)) = e (projK v) := LinearMap.congr_fun hg (e (projK v))
  have he : e (projK v) = 0 := by
    have hπv := congrArg π hv
    rwa [map_add, hπD, add_zero, hp, map_zero] at hπv
  have hk : projK v = 0 := e.map_eq_zero_iff.mp he
  have hY : Y v = 0 := by
    change g (e.toLinearMap (projK v)) = 0
    rw [hk, map_zero, map_zero]
  have hvK : v ∈ LinearMap.ker D := by
    rwa [hY, map_zero, zero_add] at hv
  have hvK0 : (⟨v, hvK⟩ : LinearMap.ker D) = 0 :=
    (Submodule.projectionOnto_apply_of_mem_left hK hvK).symm.trans hk
  exact hv0 (congrArg Subtype.val hvK0)
