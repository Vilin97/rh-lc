module

public import Mathlib

@[expose] public section

open TensorProduct

namespace GlobalTheory

theorem split_injective_of_forall_prime_baseChange_field_injective :
    ∀ (R : Type) [CommRing R] (M : Type 1) [AddCommGroup M] [Module R M] [Module.Finite R M]
      [Module.Projective R M] (N : Type 1) [AddCommGroup N] [Module R N] [Module.Finite R N]
      [Module.Projective R N] (f : M →ₗ[R] N),
      (∀ P : PrimeSpectrum R, ∃ (k : Type) (_ : Field k) (_ : Algebra R k),
        RingHom.ker (algebraMap R k) = P.asIdeal ∧ Function.Injective (f.baseChange k)) →
      ∃ g : N →ₗ[R] M, g ∘ₗ f = LinearMap.id := by
  intro R _ M _ _ _ _ N _ _ _ _ f h
  have hres : ∀ (m : Ideal R) [m.IsMaximal], Function.Injective (f.lTensor m.ResidueField) := by
    intro m hm
    obtain ⟨k, _, _, hk, hinj⟩ := h ⟨m, hm.isPrime⟩
    change RingHom.ker (algebraMap R k) = m at hk
    let φ : m.ResidueField →ₐ[R] k := Ideal.ResidueField.liftₐ m (Algebra.ofId R k) hk.ge (by
      intro x hx
      simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff, isUnit_iff_ne_zero]
      intro h0
      exact hx (hk ▸ h0))
    let : Algebra m.ResidueField k := φ.toRingHom.toAlgebra
    have : IsScalarTower R m.ResidueField k :=
      IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
    have e : (AlgebraTensorModule.cancelBaseChange R m.ResidueField m.ResidueField k N) ∘
          ((f.baseChange m.ResidueField).lTensor k) =
        (f.lTensor k) ∘ (AlgebraTensorModule.cancelBaseChange R
          m.ResidueField m.ResidueField k M) := by
      funext x
      exact (LinearMap.congr_fun (AlgebraTensorModule.lTensor_comp_cancelBaseChange R
        m.ResidueField m.ResidueField (M := k) f) x).symm
    have h1 : Function.Injective ((f.baseChange m.ResidueField).lTensor k) :=
      Function.Injective.of_comp (e ▸ (hinj.comp (LinearEquiv.injective _)))
    exact (Module.FaithfullyFlat.lTensor_injective_iff_injective m.ResidueField k _).1 h1
  have hloc : ∀ (m : Ideal R) [m.IsMaximal], Function.Injective
      ((f.baseChange (Localization.AtPrime m)).lTensor m.ResidueField) := by
    intro m _
    have e : (AlgebraTensorModule.cancelBaseChange R (Localization.AtPrime m)
          (Localization.AtPrime m) m.ResidueField N) ∘
          ((f.baseChange (Localization.AtPrime m)).lTensor m.ResidueField) =
        (f.lTensor m.ResidueField) ∘ (AlgebraTensorModule.cancelBaseChange R
          (Localization.AtPrime m) (Localization.AtPrime m) m.ResidueField M) := by
      funext x
      exact (LinearMap.congr_fun (AlgebraTensorModule.lTensor_comp_cancelBaseChange R
        (Localization.AtPrime m) (Localization.AtPrime m) (M := m.ResidueField) f) x).symm
    exact Function.Injective.of_comp (e ▸ (hres m).comp (LinearEquiv.injective _))
  have hfree : ∀ (m : Ideal R) [m.IsMaximal],
      Module.Free (Localization.AtPrime m) (Localization.AtPrime m ⊗[R] N) := fun m _ =>
    Module.free_of_flat_of_isLocalRing
  have hinj : Function.Injective f := by
    intro x y hxy
    refine Module.eq_of_localization_maximal (R := R)
      (fun m _ => Localization.AtPrime m ⊗[R] M)
      (fun m _ => TensorProduct.mk R (Localization.AtPrime m) M 1) x y (fun m _ => ?_)
    obtain ⟨g, hg⟩ := (IsLocalRing.split_injective_iff_lTensor_residueField_injective
      (f.baseChange (Localization.AtPrime m))).2 (hloc m)
    have hinj : Function.Injective (f.baseChange (Localization.AtPrime m)) :=
      Function.HasLeftInverse.injective ⟨g, LinearMap.congr_fun hg⟩
    exact hinj (by simp [hxy])
  have : Module.FinitePresentation R N := Module.finitePresentation_of_projective R N
  have : Module.FinitePresentation R (N ⧸ LinearMap.range f) :=
    Module.finitePresentation_of_surjective (LinearMap.range f).mkQ (Submodule.mkQ_surjective _)
      (by rw [Submodule.ker_mkQ, LinearMap.range_eq_map]; exact Module.Finite.fg_top.map f)
  have : Module.Projective R (N ⧸ LinearMap.range f) := by
    refine Module.projective_of_localization_maximal' (fun m _ => Localization.AtPrime m)
      (fun m _ => Localization.AtPrime m ⊗[R] (N ⧸ LinearMap.range f))
      (fun m _ => TensorProduct.mk R (Localization.AtPrime m) _ 1) (fun m _ => ?_)
    have := Module.free_of_lTensor_residueField_injective
      (f.baseChange (Localization.AtPrime m))
      ((LinearMap.range f).mkQ.baseChange (Localization.AtPrime m))
      (LinearMap.lTensor_surjective _ (Submodule.mkQ_surjective _))
      (lTensor_exact _ f.exact_map_mkQ_range (Submodule.mkQ_surjective _)) (hloc m)
    infer_instance
  have hsplit := (Function.Exact.split_tfae f.exact_map_mkQ_range hinj
    (Submodule.mkQ_surjective _)).out 1 2
  exact hsplit.mp (Module.projective_lifting_property _ _ (Submodule.mkQ_surjective _))

end GlobalTheory
