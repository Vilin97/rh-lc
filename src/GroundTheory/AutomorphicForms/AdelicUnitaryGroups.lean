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

def unitaryCongr (e : R ≃ₐ[K] S) (he : Continuous e) (he' : Continuous e.symm) :
    unitaryPoints K E H R ≃ₜ* unitaryPoints K E H S where
  toFun := unitaryMap K E H (e : R →ₐ[K] S)
  invFun := unitaryMap K E H (e.symm : S →ₐ[K] R)
  left_inv g := by
    let b := Module.finBasis K E
    apply unitaryCoords_injective H R b
    rw [unitaryCoords_unitaryMap, unitaryCoords_unitaryMap]
    funext p
    simp
  right_inv g := by
    let b := Module.finBasis K E
    apply unitaryCoords_injective H S b
    rw [unitaryCoords_unitaryMap, unitaryCoords_unitaryMap]
    funext p
    simp
  map_mul' := map_mul _
  continuous_toFun := continuous_unitaryMap _ he
  continuous_invFun := continuous_unitaryMap _ he'

theorem unitaryCongr_apply (e : R ≃ₐ[K] S) (he : Continuous e) (he' : Continuous e.symm)
    (g : unitaryPoints K E H R) :
    unitaryCongr H e he he' g = unitaryMap K E H (e : R →ₐ[K] S) g := rfl

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
  (finiteAdeleEval K v).comp ((AlgHom.snd K _ _).comp (adeleRingEquivProd K).toAlgHom)

variable {κ : Type*} [Fintype κ] (b : Basis κ K E)

theorem locallyCompactSpace_unitaryPoints_adele (hH : IsUnit H.det) :
    LocallyCompactSpace (unitaryPoints K E H 𝔸[K]) :=
  locallyCompactSpace_unitaryPoints H 𝔸[K] hH

variable (K) in

def unitaryDiagonal : unitaryPoints K E H K →* unitaryPoints K E H 𝔸[K] :=
  unitaryMap K E H (Algebra.ofId K 𝔸[K])

section Hermitian

variable {V : Type*} [AddCommGroup V] [Module E V] (h : HermitianForm K E V) (v : Basis ι E V)

def hermitianDiagonal : h.unitaryGroup →* unitaryPoints K E (gram h.toSesq v) 𝔸[K] :=
  (unitaryDiagonal K (gram h.toSesq v)).comp
    (unitaryPointsRationalEquivHermitian K E h v).symm.toMonoidHom

end Hermitian

end

end GroundTheory.Automorphic
