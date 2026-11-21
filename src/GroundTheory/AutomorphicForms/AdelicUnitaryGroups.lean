module

public import Mathlib
public import GroundTheory.AutomorphicForms.AdelicUnitaryGroups.Restricted
public import GroundTheory.AutomorphicForms.AdelicUnitaryGroups.LatticeCompact
public import GroundTheory.AutomorphicForms.AdelicUnitaryGroups.Anisotropic
public import GroundTheory.GlobalFields.Adele.Discrete
public import GroundTheory.GlobalFields.Adele.Topology

@[expose] public section

namespace GroundTheory.Automorphic

open Module Matrix TensorProduct Topology Filter IsDedekindDomain NumberField
open scoped RestrictedProduct NumberField.AdeleRing

noncomputable section

variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)

section Congr

variable {R S : Type*} [CommRing R] [Algebra K R] [TopologicalSpace R] [IsTopologicalRing R]
  [CommRing S] [Algebra K S] [TopologicalSpace S] [IsTopologicalRing S]

attribute [local instance] tensorTopology

def unitaryCongr (e : R ≃ₐ[K] S) (he : Continuous e) (he' : Continuous e.symm) :
    unitaryPoints K E H R ≃ₜ* unitaryPoints K E H S := by
  let b := Module.finBasis K E
  let f := unitaryMap (H := H) e.toAlgHom
  let f' := unitaryMap (H := H) e.symm.toAlgHom
  have hrepr :
      (∀ z : R ⊗[K] E, ∀ k,
        (Algebra.TensorProduct.basis S b).repr (tensorMap e.toAlgHom z) k =
          e ((Algebra.TensorProduct.basis R b).repr z k)) ∧
      (∀ z : S ⊗[K] E, ∀ k,
        (Algebra.TensorProduct.basis R b).repr (tensorMap e.symm.toAlgHom z) k =
          e.symm ((Algebra.TensorProduct.basis S b).repr z k)) := by
    constructor <;> intro z k <;> induction z using TensorProduct.inductionOn with
    | zero => simp
    | tmul r x => simp [Algebra.TensorProduct.basis_repr_tmul, Finsupp.mapRange_apply]
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  have hcoords :
      (∀ g p, unitaryCoords H S b (f g) p = e (unitaryCoords H R b g p)) ∧
      (∀ g p, unitaryCoords H R b (f' g) p = e.symm (unitaryCoords H S b g p)) := by
    exact ⟨fun g ⟨i, j, k⟩ => hrepr.1 (unitaryMat g i j) k,
      fun g ⟨i, j, k⟩ => hrepr.2 (unitaryMat g i j) k⟩
  have htensor :
      Continuous (tensorMap (E := E) e.toAlgHom) ∧
        Continuous (tensorMap (E := E) e.symm.toAlgHom) := by
    constructor
    · apply (tensorCoordsHomeomorph S b).isEmbedding.continuous_iff.mpr
      refine continuous_pi fun k => ?_
      simpa only [Function.comp_apply, tensorCoordsHomeomorph_apply, hrepr.1] using
        he.comp ((continuous_apply k).comp (tensorCoordsHomeomorph R b).continuous)
    · apply (tensorCoordsHomeomorph R b).isEmbedding.continuous_iff.mpr
      refine continuous_pi fun k => ?_
      simpa only [Function.comp_apply, tensorCoordsHomeomorph_apply, hrepr.2] using
        he'.comp ((continuous_apply k).comp (tensorCoordsHomeomorph S b).continuous)
  refine
    { toFun := f
      invFun := f'
      left_inv := ?_
      right_inv := ?_
      map_mul' := map_mul f
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · intro g
    apply unitaryCoords_injective H R b
    funext p
    rw [hcoords.2, hcoords.1, e.symm_apply_apply]
  · intro g
    apply unitaryCoords_injective H S b
    funext p
    rw [hcoords.1, hcoords.2, e.apply_symm_apply]
  · have hm : Continuous fun M : Matrix ι ι (R ⊗[K] E) => M.map (tensorMap e.toAlgHom) :=
      continuous_id.matrix_map htensor.1
    apply continuous_induced_rng.2
    rw [Units.continuous_iff]
    refine ⟨hm.comp (Units.continuous_val.comp continuous_subtype_val), ?_⟩
    simpa only [Function.comp_apply, map_inv, Subgroup.coe_inv] using
      hm.comp (Units.continuous_val.comp (continuous_subtype_val.comp continuous_inv :
        Continuous fun g : unitaryPoints K E H R => ((g⁻¹ : unitaryPoints K E H R) : GL ι _)))
  · have hm : Continuous fun M : Matrix ι ι (S ⊗[K] E) => M.map (tensorMap e.symm.toAlgHom) :=
      continuous_id.matrix_map htensor.2
    apply continuous_induced_rng.2
    rw [Units.continuous_iff]
    refine ⟨hm.comp (Units.continuous_val.comp continuous_subtype_val), ?_⟩
    simpa only [Function.comp_apply, map_inv, Subgroup.coe_inv] using
      hm.comp (Units.continuous_val.comp (continuous_subtype_val.comp continuous_inv :
        Continuous fun g : unitaryPoints K E H S => ((g⁻¹ : unitaryPoints K E H S) : GL ι _)))

theorem unitaryCongr_apply (e : R ≃ₐ[K] S) (he : Continuous e) (he' : Continuous e.symm)
    (g : unitaryPoints K E H R) :
    unitaryCongr H e he he' g = unitaryMap (H := H) e.toAlgHom g := rfl

end Congr

variable [NumberField K]

variable (K) in
def adeleRingEquivProd : 𝔸[K] ≃ₐ[K] InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K :=
  AlgEquiv.refl

variable (K) in
def infiniteAdeleRingEquivPi : InfiniteAdeleRing K ≃ₐ[K] ∀ w : InfinitePlace K, w.Completion :=
  AlgEquiv.refl

variable (K) in
def adeleInfiniteEval (w : InfinitePlace K) : 𝔸[K] →ₐ[K] w.Completion :=
  ((Pi.evalAlgHom K (fun w : InfinitePlace K => w.Completion) w).comp
    (infiniteAdeleRingEquivPi K).toAlgHom).comp
    ((AlgHom.fst K _ _).comp (adeleRingEquivProd K).toAlgHom)

variable (K) in
def adeleFiniteEval (v : HeightOneSpectrum (𝓞 K)) : 𝔸[K] →ₐ[K] v.adicCompletion K :=
  (finiteAdeleEval v).comp ((AlgHom.snd K _ _).comp (adeleRingEquivProd K).toAlgHom)

variable {κ : Type*} [Fintype κ] (b : Basis κ K E)

theorem locallyCompactSpace_unitaryPoints_adele (hH : IsUnit H.det) :
    LocallyCompactSpace (unitaryPoints K E H 𝔸[K]) :=
  locallyCompactSpace_unitaryPoints H 𝔸[K] hH

variable (K) in
def unitaryDiagonal : unitaryPoints K E H K →* unitaryPoints K E H 𝔸[K] :=
  unitaryMap (H := H) (Algebra.ofId K 𝔸[K])

section Hermitian

variable {V : Type*} [AddCommGroup V] [Module E V] (h : HermitianForm K E V) (v : Basis ι E V)

def hermitianDiagonal : h.unitaryGroup →* unitaryPoints K E (gram h.toSesq v) 𝔸[K] :=
  (unitaryDiagonal K (gram h.toSesq v)).comp
    (unitaryPointsRationalEquivHermitian h v).symm.toMonoidHom

end Hermitian

end

end GroundTheory.Automorphic
