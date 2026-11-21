module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafOfRingFunctorSectionsLocallyBijective
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleSheafOfRingFunctor_sections_locally_bijective : ∀ (R : Type) [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) (U : Scheme.{0}), (∀ (x : Sec (ofRings R M) U) (u : U), ∃ (V : Scheme.{0}) (j : V ⟶ U) (v : V) (m : M.obj Γ(V, ⊤)), IsAffine V ∧ Etale j ∧ j v = u ∧ ofRings.sec R M V m = Sec.res j x) ∧ (∀ m : M.obj Γ(U, ⊤), ofRings.sec R M U m = 0 → ∀ u : U, ∃ (V : Scheme.{0}) (j : V ⟶ U) (v : V), IsAffine V ∧ Etale j ∧ j v = u ∧ (M.map j.appTop).hom m = 0) ∧ ∀ (V : Scheme.{0}) (j : V ⟶ U) (m : M.obj Γ(U, ⊤)), Sec.res j (ofRings.sec R M U m) = ofRings.sec R M V ((M.map j.appTop).hom m) := by
  exact @GlobalTheory.ofRings_loc
