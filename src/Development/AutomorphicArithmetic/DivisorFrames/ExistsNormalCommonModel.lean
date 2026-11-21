module

public import Mathlib
public import Development.AutomorphicArithmetic.LocalEmbeddings.ConsAgree
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ChiLenPicPushforwardOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ConsGeo

private theorem exists_spMap_of_eq {F : Type} [Field F] {X : Scheme.{0}} (f : Sp F ⟶ X) (y : X)
    (hy : f (closedPoint F) = y) :
    ∃ φ : X.presheaf.stalk y ⟶ CommRingCat.of F, Spec.map φ ≫ X.fromSpecStalk y = f := by
  subst hy
  exact ⟨_, Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of F) f⟩

private theorem gpt_apply (X : Scheme.{0}) [IsIntegral X] (x : Sp X.functionField) :
    gpt X x = genericPoint X := by
  obtain rfl : x = closedPoint X.functionField := Subsingleton.elim _ _
  exact Scheme.fromSpecStalk_closedPoint

private theorem apply_eq_genericPoint {F : Type} [Field F] {X : Scheme.{0}} [IsIntegral X]
    (f : Sp F ⟶ X) [IsDominant f] (x : Sp F) : f x = genericPoint X := by
  refine IsGenericPoint.eq ?_ (genericPoint_spec _)
  rw [isGenericPoint_def, ← f.denseRange.closure_range]
  congr 1
  ext y
  exact ⟨fun hy => ⟨x, hy.symm⟩, fun ⟨x', hy⟩ => by rw [← hy, Subsingleton.elim x' x]; rfl⟩

private theorem exists_equiv {X W : Scheme.{0}} [IsIntegral X] [IsIntegral W]
    (t : Sp X.functionField ⟶ W) [IsDominant t] (p : W ⟶ X) (h : t ≫ p = gpt X) :
    ∃ ε : X.functionField ≃+* W.functionField, gpt W = spMap ε.toRingHom ≫ t := by
  obtain ⟨φ, hφ⟩ := exists_spMap_of_eq t _ (apply_eq_genericPoint t _)
  have hp : p (genericPoint W) = genericPoint X := by
    obtain ⟨x⟩ : Nonempty (Sp X.functionField) := inferInstance
    rw [← apply_eq_genericPoint t x, ← Scheme.Hom.comp_apply, h, gpt_apply]
  obtain ⟨ψ, hψ⟩ := exists_spMap_of_eq (gpt W ≫ p) (genericPoint X)
    ((Scheme.Hom.comp_apply _ _ _).trans ((congrArg p (gpt_apply W _)).trans hp))
  have e : Spec.map (ψ ≫ φ) = Spec.map (𝟙 _) := by
    rw [← cancel_mono (X.fromSpecStalk (genericPoint X)), Spec.map_comp, Category.assoc]
    erw [hψ]
    rw [Spec.map_id, Category.id_comp, ← Category.assoc]
    erw [hφ]
    exact h
  have e' : ψ ≫ φ = 𝟙 _ := Spec.map_injective e
  have e₁ : ∀ a, φ.hom (ψ.hom a) = a := fun a => congrArg (fun u => u.hom a) e'
  have hinj : Function.Injective (show W.functionField →+* X.functionField from φ.hom) :=
    RingHom.injective _
  have e₂ : ∀ a, ψ.hom (φ.hom a) = a := fun a => hinj (e₁ _)
  let ε : X.functionField ≃+* W.functionField :=
    RingEquiv.ofRingHom ψ.hom φ.hom (RingHom.ext e₂) (RingHom.ext e₁)
  refine ⟨ε, ?_⟩
  have e₃ : φ ≫ ψ = 𝟙 _ := CommRingCat.hom_ext (RingHom.ext e₂)
  rw [← hφ]
  change _ = Spec.map ψ ≫ Spec.map φ ≫ _
  rw [← Spec.map_comp_assoc, e₃, Spec.map_id]
  exact (Category.id_comp _).symm
