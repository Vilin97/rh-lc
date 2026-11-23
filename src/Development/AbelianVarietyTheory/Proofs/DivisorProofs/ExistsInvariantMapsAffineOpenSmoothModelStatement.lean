module

public import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningOpenImmersionPullbackSquareStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningPreimageEqClosedImmersionPreimageStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineOpenSmoothSchemeIsSpecSmoothAlgebra

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem affineChart_smooth : ∀ (R : Type) [CommRing R] (Y : Over (Sp R)), Smooth Y.hom → ∀ (W : Y.left.Opens), IsAffineOpen W → ∃ (O : Type) (_ : CommRing O) (_ : Algebra R O) (k : Sp O ⟶ Y.left) (_ : IsOpenImmersion k), k.opensRange = W ∧ k ≫ Y.hom = spMap (algebraMap R O) ∧ Algebra.Smooth R O := by
  intro R _ Y hY W hW
  let alg : R →+* Γ(Y.left, W) :=
    (Y.hom.appLE ⊤ W (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  letI : Algebra R Γ(Y.left, W) := alg.toAlgebra
  have s₀ : hW.fromSpec ≫ Y.hom = spMap alg := by
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec Y.hom (isAffineOpen_top _) hW (fun _ _ => trivial),
      IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]; rfl
  have h1 : RingHom.Smooth (Y.hom.appLE ⊤ W (fun _ _ => trivial)).hom :=
    HasRingHomProperty.appLE @Smooth Y.hom hY ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ (fun _ _ => trivial)
  have h2 : RingHom.Smooth alg :=
    RingHom.Smooth.respectsIso.2 _ (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv h1
  exact ⟨Γ(Y.left, W), inferInstance, inferInstance, hW.fromSpec, inferInstance, hW.opensRange_fromSpec, s₀, h2⟩

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineOpenSmoothSchemeIsSpecSmoothAlgebraStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.affineOpen_smoothScheme_isSpec_smoothAlgebra : ∀ (R : Type) [CommRing R] (Y : Over (Sp R)), Smooth Y.hom → ∀ (W : Y.left.Opens), IsAffineOpen W → ∃ (O : Type) (_ : CommRing O) (_ : Algebra R O) (k : Sp O ⟶ Y.left) (_ : IsOpenImmersion k), k.opensRange = W ∧ k ≫ Y.hom = spMap (algebraMap R O) ∧ Algebra.Smooth R O := by
  first | exact @GlobalTheory.Mum.affineChart_smooth | exact GlobalTheory.Mum.affineChart_smooth | (intros; apply GlobalTheory.Mum.affineChart_smooth <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorProductSurjectiveKerOfAffinePullback

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem tensor_of_pullback_surj_ker : ∀ {R O R' Q : Type} [CommRing R] [CommRing O] [CommRing R'] [CommRing Q] [Algebra R O] [Algebra R R'] [Algebra R Q] (I : Ideal R') (a : O →ₐ[R] Q) (b : R' ⧸ I →ₐ[R] Q), IsPullback (spMap (a : O →+* Q)) (spMap (b : R' ⧸ I →+* Q)) (spMap (algebraMap R O)) (spMap (algebraMap R (R' ⧸ I))) → Function.Surjective (Algebra.TensorProduct.lift a (b.comp (Ideal.Quotient.mkₐ R I)) fun _ _ => Commute.all _ _) ∧ RingHom.ker (Algebra.TensorProduct.lift a (b.comp (Ideal.Quotient.mkₐ R I)) fun _ _ => Commute.all _ _) = I.map (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R O R') := by
  intro R O R' Q _ _ _ _ _ _ _ I a b hP
  set t : TensorProduct R O (R' ⧸ I) →ₐ[R] Q := Algebra.TensorProduct.lift a b fun _ _ => Commute.all _ _ with ht
  have H0 := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R O (R' ⧸ I))
  have e1 : Spec.map (CommRingCat.ofHom (t : TensorProduct R O (R' ⧸ I) →+* Q)) ≫
      Spec.map (CommRingCat.ofHom (S := TensorProduct R O (R' ⧸ I)) Algebra.TensorProduct.includeLeftRingHom) =
      spMap (a : O →+* Q) := by
    rw [← Spec.map_comp]; congr 1; ext x; simp [ht]
  have e2 : Spec.map (CommRingCat.ofHom (t : TensorProduct R O (R' ⧸ I) →+* Q)) ≫
      Spec.map (CommRingCat.ofHom (S := TensorProduct R O (R' ⧸ I)) Algebra.TensorProduct.includeRight.toRingHom) =
      spMap (b : R' ⧸ I →+* Q) := by
    rw [← Spec.map_comp]; congr 1; ext x; simp [ht]
  have hiso : IsIso (Spec.map (CommRingCat.ofHom (t : TensorProduct R O (R' ⧸ I) →+* Q))) := by
    have : Spec.map (CommRingCat.ofHom (t : TensorProduct R O (R' ⧸ I) →+* Q)) = (hP.isoIsPullback _ _ H0).hom := by
      apply H0.hom_ext
      · rw [e1, IsPullback.isoIsPullback_hom_fst]
      · rw [e2, IsPullback.isoIsPullback_hom_snd]
    rw [this]; infer_instance
  rw [isIso_SpecMap_iff] at hiso
  have hbij : Function.Bijective t := hiso
  have hcomp : (Algebra.TensorProduct.lift a (b.comp (Ideal.Quotient.mkₐ R I)) fun _ _ => Commute.all _ _) =
      t.comp (Algebra.TensorProduct.map (AlgHom.id R O) (Ideal.Quotient.mkₐ R I)) := by
    apply Algebra.TensorProduct.ext'
    intro x y
    simp [ht]
  have hmk : Function.Surjective (Ideal.Quotient.mkₐ R I) := Ideal.Quotient.mkₐ_surjective R I
  rw [hcomp]
  refine ⟨hbij.2.comp (LinearMap.lTensor_surjective O hmk), ?_⟩
  have : RingHom.ker (t.comp (Algebra.TensorProduct.map (AlgHom.id R O) (Ideal.Quotient.mkₐ R I))) =
      RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R O) (Ideal.Quotient.mkₐ R I)) := by
    ext x
    simp only [RingHom.mem_ker, AlgHom.comp_apply]
    constructor
    · intro h; exact hbij.1 (by rw [h, map_zero])
    · intro h; rw [h, map_zero]
  rw [this, Algebra.TensorProduct.lTensor_ker _ hmk]
  congr 1
  ext x
  simp [Ideal.Quotient.eq_zero_iff_mem]

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorProductSurjectiveKerOfAffinePullbackStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.tensorProduct_surjective_ker_of_affine_pullback : ∀ {R O R' Q : Type} [CommRing R] [CommRing O] [CommRing R'] [CommRing Q] [Algebra R O] [Algebra R R'] [Algebra R Q] (I : Ideal R') (a : O →ₐ[R] Q) (b : R' ⧸ I →ₐ[R] Q), IsPullback (spMap (a : O →+* Q)) (spMap (b : R' ⧸ I →+* Q)) (spMap (algebraMap R O)) (spMap (algebraMap R (R' ⧸ I))) → Function.Surjective (Algebra.TensorProduct.lift a (b.comp (Ideal.Quotient.mkₐ R I)) fun _ _ => Commute.all _ _) ∧ RingHom.ker (Algebra.TensorProduct.lift a (b.comp (Ideal.Quotient.mkₐ R I)) fun _ _ => Commute.all _ _) = I.map (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R O R') := by
  first | exact @GlobalTheory.Mum.tensor_of_pullback_surj_ker | exact GlobalTheory.Mum.tensor_of_pullback_surj_ker | (intros; apply GlobalTheory.Mum.tensor_of_pullback_surj_ker <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantMapsAffineOpenSmoothModel

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem exists_invariant_maps_of_affine_open : ∀ (R : Type) [CommRing R] (R' : Type) [CommRing R'] [IsLocalRing R'] [Algebra R R'] (G' : Over (Sp R')) (act : Gal (algebraMap R R') → (G'.left ⟶ G'.left)), ∀ (Y : Over (Sp R)) (φ : ∀ e : ℕ, (thickObj R' (maximalIdeal R') e G').left ⟶ Y.left), Smooth Y.hom → (∀ e, IsPullback (φ e) (thickObj R' (maximalIdeal R') e G').hom Y.hom (thick R' (maximalIdeal R') e ≫ spMap (algebraMap R R'))) → (∀ e, thickMap R' (maximalIdeal R') e G' ≫ φ (e + 1) = φ e) → (∀ e σ, ∃ h : (thickObj R' (maximalIdeal R') e G').left ⟶ (thickObj R' (maximalIdeal R') e G').left, h ≫ (pullback.fst G'.hom (thick R' (maximalIdeal R') e)) = (pullback.fst G'.hom (thick R' (maximalIdeal R') e)) ≫ act σ ∧ h ≫ φ e = φ e) → ∀ (C' : Type) [CommRing C'] [Algebra R C'] [Algebra R' C'] [IsScalarTower R R' C'] (actC : Gal (algebraMap R R') →* (C' ≃ₐ[R] C')) (j : Sp C' ⟶ G'.left) [IsOpenImmersion j], j ≫ G'.hom = spMap (algebraMap R' C') → (∀ σ, spMap (actC σ : C' →+* C') ≫ j = j ≫ act σ) → ∀ W : Y.left.Opens, IsAffineOpen W → φ 0 ⁻¹ᵁ W = (pullback.fst G'.hom (thick R' (maximalIdeal R') 0)) ⁻¹ᵁ j.opensRange → ∃ (O : Type) (_ : CommRing O) (_ : Algebra R O) (i : ∀ e : ℕ, O →ₐ[R] C' ⧸ (maximalIdeal R' ^ (e + 1)).map (algebraMap R' C')), Algebra.Smooth R O ∧ (∀ e x y, Ideal.Quotient.mk _ y = i (e + 1) x → Ideal.Quotient.mk _ y = i e x) ∧ (∀ e σ x y, Ideal.Quotient.mk _ y = i e x → Ideal.Quotient.mk _ (actC σ y) = i e x) ∧ (∀ e, Function.Surjective (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) ∧ RingHom.ker (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) = (maximalIdeal R' ^ (e + 1)).map (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R O R')) := by
  intro R _ R' _ _ _ G' act Y φ hsm hpb hcomp hact C' _ _ _ _ actC j _ hj hjσ W hW h0
  obtain ⟨O, _, _, k, _, hkW, hkY, hOsm⟩ := GlobalTheory.T.affineOpen_smoothScheme_isSpec_smoothAlgebra R Y hsm W hW
  have hopen := GlobalTheory.T.thickening_preimage_eq_closedImmersion_preimage R' (maximalIdeal R') G' Y.left φ hcomp j.opensRange W h0
  have hB := fun e => GlobalTheory.T.thickening_open_immersion_pullback_square R' (maximalIdeal R') G' C' j hj e
  choose je hjeo hjer hjep hjeh using hB
  have hi : ∀ e, ∃ i : O →ₐ[R] C' ⧸ (maximalIdeal R' ^ (e + 1)).map (algebraMap R' C'),
      spMap (i : O →+* _) ≫ k = je e ≫ φ e := by
    intro e
    have hr : Set.range (je e ≫ φ e) ⊆ Set.range k := by
      rintro _ ⟨z, rfl⟩
      have h1 : je e z ∈ (je e).opensRange := ⟨z, rfl⟩
      rw [hjer, ← hopen, ← hkW] at h1
      exact h1
    obtain ⟨f, hf⟩ := Spec.map_surjective (IsOpenImmersion.lift k (je e ≫ φ e) hr)
    have hf' : Spec.map f ≫ k = je e ≫ φ e := by rw [hf]; exact IsOpenImmersion.lift_fac _ _ _
    have hc : CommRingCat.ofHom (algebraMap R O) ≫ f =
        CommRingCat.ofHom (algebraMap R (C' ⧸ (maximalIdeal R' ^ (e + 1)).map (algebraMap R' C'))) := by
      apply Spec.map_injective
      rw [Spec.map_comp]
      change Spec.map f ≫ spMap (algebraMap R O) = _
      rw [← hkY, ← Category.assoc, hf', Category.assoc, (hpb e).w, ← Category.assoc, hjeh]
      simp only [thick, spMap, ← Spec.map_comp]
      congr 1
      ext r
      simp [Ideal.quotientMap_mk, IsScalarTower.algebraMap_apply R R' C', Ideal.Quotient.algebraMap_eq]
      exact (IsScalarTower.algebraMap_apply _ _ _ _).symm
    refine ⟨{ f.hom with commutes' := fun r => congrArg (fun g => g.hom r) hc }, ?_⟩
    exact hf'
  choose i hi using hi
  refine ⟨O, inferInstance, inferInstance, i, hOsm, ?_, ?_, ?_⟩
  · intro e x y hxy
    have hle : (maximalIdeal R' ^ (e + 1 + 1)).map (algebraMap R' C') ≤
        (maximalIdeal R' ^ (e + 1)).map (algebraMap R' C') :=
      Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_succ _))
    have hsq : spMap (Ideal.Quotient.factor hle) ≫ je (e + 1) = je e ≫ thickMap R' (maximalIdeal R') e G' := by
      apply pullback.hom_ext
      · simp only [Category.assoc, thickMap, pullback.map, pullback.lift_fst, Category.comp_id]
        rw [(hjep (e + 1)).w, (hjep e).w, ← Category.assoc]
        congr 1
        simp only [spMap, ← Spec.map_comp]
        congr 1
      · have h1 := hjeh (e + 1)
        have h2 := hjeh e
        simp only [thickObj, Over.pullback_obj_hom] at h1 h2
        simp only [Category.assoc, thickMap, pullback.map, pullback.lift_snd]
        rw [h1, ← Category.assoc, h2]
        simp only [spMap, thickTrans, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        congr 2
        ext z
        simp only [RingHom.coe_comp, Function.comp_apply, Ideal.quotientMap_mk, Ideal.Quotient.factor_mk]
    have hsp : spMap (i e : O →+* _) = spMap ((Ideal.Quotient.factor hle).comp (i (e + 1) : O →+* _)) := by
      rw [← cancel_mono k, hi, ← hcomp e, ← Category.assoc, ← hsq, Category.assoc, ← hi]
      simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    have hr := congrArg (fun g => g.hom x) (Spec.map_injective hsp)
    simp only [CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply] at hr
    have hr' : i e x = Ideal.Quotient.factor hle (i (e + 1) x) := hr
    rw [hr', ← hxy, Ideal.Quotient.factor_mk]
  · intro e σ x y hxy
    obtain ⟨h, hh1, hh2⟩ := hact e σ
    have w : (je e ≫ h) ≫ pullback.fst G'.hom (thick R' (maximalIdeal R') e) =
        (spMap (Ideal.Quotient.mk ((maximalIdeal R' ^ (e + 1)).map (algebraMap R' C'))) ≫
          spMap (actC σ : C' →+* C')) ≫ j := by
      rw [Category.assoc, hh1, ← Category.assoc, (hjep e).w, Category.assoc, Category.assoc, hjσ]
    have hκ1 := (hjep e).lift_fst _ _ w
    have hκ2 := (hjep e).lift_snd _ _ w
    have hκi : (hjep e).lift _ _ w ≫ spMap (i e : O →+* _) = spMap (i e : O →+* _) := by
      rw [← cancel_mono k, Category.assoc, hi, ← Category.assoc, hκ1, Category.assoc, hh2]
    obtain ⟨κ', hκ'⟩ := Spec.map_surjective ((hjep e).lift _ _ w)
    rw [← hκ'] at hκ2 hκi
    simp only [spMap, ← Spec.map_comp] at hκ2 hκi
    have r1 := congrArg (fun g => g.hom y) (Spec.map_injective hκ2)
    have r2 := congrArg (fun g => g.hom x) (Spec.map_injective hκi)
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply] at r1 r2
    have r1' : κ'.hom (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ (actC σ y) := r1
    have r2' : κ'.hom (i e x) = i e x := r2
    rw [← hxy] at r2' ⊢
    rw [← r1', r2']
  · intro e
    have hpbO : IsPullback (spMap (i e : O →+* _)) (je e) k (φ e) :=
      IsOpenImmersion.isPullback _ _ _ _ (hi e).symm (by rw [hkW, hopen, hjer])
    have hp2 := hpbO.paste_vert (hpb e)
    rw [hjeh, hkY] at hp2
    have hthick : thick R' (maximalIdeal R') e ≫ spMap (algebraMap R R') =
        spMap (algebraMap R (R' ⧸ maximalIdeal R' ^ (e + 1))) := by
      simp only [thick, spMap, ← Spec.map_comp]
      rfl
    rw [hthick] at hp2
    let b : R' ⧸ maximalIdeal R' ^ (e + 1) →ₐ[R] C' ⧸ (maximalIdeal R' ^ (e + 1)).map (algebraMap R' C') :=
      { Ideal.quotientMap ((maximalIdeal R' ^ (e + 1)).map (algebraMap R' C')) (algebraMap R' C')
          Ideal.le_comap_map with
        commutes' := fun r => by
          simp [Ideal.quotientMap_mk, Ideal.Quotient.algebraMap_eq, IsScalarTower.algebraMap_apply R R' C']
          exact (IsScalarTower.algebraMap_apply _ _ _ _).symm }
    have hb : (Ideal.Quotient.mkₐ R ((maximalIdeal R' ^ (e + 1)).map (algebraMap R' C'))).comp
        (IsScalarTower.toAlgHom R R' C') = b.comp (Ideal.Quotient.mkₐ R _) := by
      ext r
      simp [b, Ideal.quotientMap_mk]
    rw [hb]
    exact GlobalTheory.T.tensorProduct_surjective_ker_of_affine_pullback (maximalIdeal R' ^ (e + 1)) (i e) b hp2

end GlobalTheory.Mum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantMapsAffineOpenSmoothModelStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_invariant_maps_affineOpen_smoothModel : ∀ (R : Type) [CommRing R] (R' : Type) [CommRing R'] [IsLocalRing R'] [Algebra R R'] (G' : Over (Sp R')) (act : Gal (algebraMap R R') → (G'.left ⟶ G'.left)), ∀ (Y : Over (Sp R)) (φ : ∀ e : ℕ, (thickObj R' (maximalIdeal R') e G').left ⟶ Y.left), Smooth Y.hom → (∀ e, IsPullback (φ e) (thickObj R' (maximalIdeal R') e G').hom Y.hom (thick R' (maximalIdeal R') e ≫ spMap (algebraMap R R'))) → (∀ e, thickMap R' (maximalIdeal R') e G' ≫ φ (e + 1) = φ e) → (∀ e σ, ∃ h : (thickObj R' (maximalIdeal R') e G').left ⟶ (thickObj R' (maximalIdeal R') e G').left, h ≫ (pullback.fst G'.hom (thick R' (maximalIdeal R') e)) = (pullback.fst G'.hom (thick R' (maximalIdeal R') e)) ≫ act σ ∧ h ≫ φ e = φ e) → ∀ (C' : Type) [CommRing C'] [Algebra R C'] [Algebra R' C'] [IsScalarTower R R' C'] (actC : Gal (algebraMap R R') →* (C' ≃ₐ[R] C')) (j : Sp C' ⟶ G'.left) [IsOpenImmersion j], j ≫ G'.hom = spMap (algebraMap R' C') → (∀ σ, spMap (actC σ : C' →+* C') ≫ j = j ≫ act σ) → ∀ W : Y.left.Opens, IsAffineOpen W → φ 0 ⁻¹ᵁ W = (pullback.fst G'.hom (thick R' (maximalIdeal R') 0)) ⁻¹ᵁ j.opensRange → ∃ (O : Type) (_ : CommRing O) (_ : Algebra R O) (i : ∀ e : ℕ, O →ₐ[R] C' ⧸ (maximalIdeal R' ^ (e + 1)).map (algebraMap R' C')), Algebra.Smooth R O ∧ (∀ e x y, Ideal.Quotient.mk _ y = i (e + 1) x → Ideal.Quotient.mk _ y = i e x) ∧ (∀ e σ x y, Ideal.Quotient.mk _ y = i e x → Ideal.Quotient.mk _ (actC σ y) = i e x) ∧ (∀ e, Function.Surjective (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) ∧ RingHom.ker (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) = (maximalIdeal R' ^ (e + 1)).map (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R O R')) := by
  first | exact @GlobalTheory.Mum.exists_invariant_maps_of_affine_open | exact GlobalTheory.Mum.exists_invariant_maps_of_affine_open | (intros; apply GlobalTheory.Mum.exists_invariant_maps_of_affine_open <;> assumption)
end
end
