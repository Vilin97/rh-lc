module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaneZeroInsertionLinearApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdeles

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.PlaneEv

namespace GlobalTheory.ThK.FrameDet

theorem frame_det_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (d₁ r' s' i₀ i₁ : ℕ) (W : Spc F E (d₁ + 2)) (W₁ : Spc F E d₁) (H' : Plane E (d₁ + 2) d₁)
    (Q : Matrix (Fin (d₁ + 2)) (Fin (d₁ + 2)) E), W.IsSkew σ B r' s' → H'.IsAdapted σ B W W₁ i₀ i₁ →
    (∀ r a, Q r (Fin.castAdd 2 a) = H'.ι r a) → (∀ r, Q r (Fin.natAdd d₁ 0) = H'.x r) →
    (∀ r, Q r (Fin.natAdd d₁ 1) = H'.y r) → Q.det ≠ 0 := by
  intro F E _ _ _ _ _ σ B d₁ r' s' i₀ i₁ W W₁ H' Q hW hH hι hx hy
  have hfull : Submodule.span E (W.L : Set (Fin (d₁ + 2) → E)) = ⊤ := by
    let S := Submodule.span E (W.L : Set (Fin (d₁ + 2) → E))
    change S = ⊤
    by_contra hS
    let g : (Fin (d₁ + 2) → E) →ₗ[E] Module.Dual E S :=
      ((dotProductBilin E E).compl₂ (Matrix.mulVecLin W.Jᵀ)).domRestrict₂ S
    have hdim : Module.finrank E (Module.Dual E S) < Module.finrank E (Fin (d₁ + 2) → E) := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt hS
    obtain ⟨y, hy, hy₀⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
    let z : Fin (d₁ + 2) → E := fun i => σ (y i)
    have hz₀ : z ≠ 0 := by
      intro hz
      apply hy₀
      exact funext fun i => σ.injective ((congrFun hz i).trans (map_zero σ).symm)
    have horth (x : Fin (d₁ + 2) → E) (hx : x ∈ W.L) : form σ W.J z x = 0 := by
      have h := congrArg (fun f : Module.Dual E S => f ⟨x, Submodule.subset_span hx⟩)
        (LinearMap.mem_ker.mp hy)
      change y ⬝ᵥ W.Jᵀ *ᵥ x = 0 at h
      have h' := congrArg σ h
      simp only [map_zero, dotProduct, Matrix.mulVec, map_sum, map_mul, Matrix.transpose_apply,
        hW.skew, neg_mul, mul_neg, Finset.sum_neg_distrib] at h'
      simp only [form, z, dotProduct, Matrix.mulVec]
      exact neg_eq_zero.mp h' 
    have hline (a : E) : a • z ∈ W.L := by
      apply (hW.dual _).2
      intro x hx o
      have hz : form σ W.J (a • z) x = 0 := by
        simpa only [form, smul_dotProduct, smul_eq_mul] using
          (show a * form σ W.J z x = 0 by rw [horth x hx, mul_zero])
      rw [hz, mul_zero, map_zero]
      exact isIntegral_zero
    let i : E →ₗ[𝓞 E] W.L :=
      ((LinearMap.toSpanSingleton E _ z).restrictScalars (𝓞 E)).codRestrict W.L hline
    let : Module.Finite (𝓞 E) W.L := Module.Finite.iff_fg.mpr hW.lat.fg
    let : Module.Finite (𝓞 E) E := Module.Finite.of_injective i fun a b hab =>
      smul_left_injective E hz₀ (congrArg Subtype.val hab)
    exact RingOfIntegers.not_isField E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))
  have hrange : LinearMap.range Q.mulVecLin = ⊤ := by
    rw [eq_top_iff, ← hfull, Submodule.span_le]
    intro z hz
    obtain ⟨s, t, u, -, -, -, rfl⟩ := hH.split z hz
    refine ⟨Fin.addCases u ![s, t], ?_⟩
    ext r
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_add, Fin.addCases_left,
      Fin.addCases_right, Fin.sum_univ_two, hι, hx, hy, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hsurj : Function.Surjective Q.mulVec := by
    intro z
    obtain ⟨v, hv⟩ : z ∈ LinearMap.range Q.mulVecLin := hrange ▸ Submodule.mem_top
    exact ⟨v, hv⟩
  exact ((Matrix.isUnit_iff_isUnit_det Q).mp (Matrix.mulVec_surjective_iff_isUnit.mp hsurj)).ne_zero

end GlobalTheory.ThK.FrameDet
