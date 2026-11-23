module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentInFibreIffOfIsPullbackStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenConnectedComponentOfIsLocallyNoetherianStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenIsIrreducibleComponentOfRationalPointSmootStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionComponentsPreimageOfIsPullbackStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Fiber
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenFibresPreirreducibleSmoothStatement
public import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineChartPreirreducibleFiber

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem exists_open_inter_fiber_subset_sectionComponent (X S : Scheme.{0}) (f : X ⟶ S) (e : S ⟶ X)
    (hf : Smooth f) (he : e ≫ f = 𝟙 _) (s : S) :
    ∃ W₁ : X.Opens, e s ∈ W₁ ∧ ∀ x : X, x ∈ W₁ → f x = s →
      x ∈ connectedComponentIn (f ⁻¹' {s}) (e s) := by
  have hes : f (e s) = s := by
    rw [← Scheme.Hom.comp_apply, he]; rfl
  have hrange : Set.range (f.fiberι s) = f ⁻¹' {s} := f.range_fiberι s
  obtain ⟨y₀, hy₀⟩ : e s ∈ Set.range (f.fiberι s) := by rw [hrange]; exact hes
  have hpb : IsPullback (f.fiberι s) (f.fiberToSpecResidueField s) f (S.fromSpecResidueField s) :=
    IsPullback.of_hasPullback _ _
  have hft : LocallyOfFiniteType (f.fiberToSpecResidueField s) :=
    MorphismProperty.of_isPullback hpb inferInstance
  have hN : IsLocallyNoetherian (f.fiber s) :=
    LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField s)
  have hopen := GlobalTheory.T.isOpen_connectedComponent_of_isLocallyNoetherian' _ hN y₀
  obtain ⟨U, hU, hUe⟩ := (f.fiberι s).isEmbedding.isInducing.isOpen_iff.mp hopen
  refine ⟨⟨U, hU⟩, ?_, ?_⟩
  · change e s ∈ U
    rw [← hy₀]
    have : y₀ ∈ connectedComponent y₀ := mem_connectedComponent
    rw [← hUe] at this
    exact this
  · intro x hx hxs
    obtain ⟨y, rfl⟩ : x ∈ Set.range (f.fiberι s) := by rw [hrange]; exact hxs
    refine (GlobalTheory.T.mem_connectedComponentIn_fibre_iff_of_isPullback X S f e s _ _ _ y₀ hpb hy₀ y).mpr ?_
    rw [← hUe]
    exact hx

theorem exists_affine_chart_preirreducible_fiber : ∀ (X S : Scheme.{0}) (f : X ⟶ S) (e : S ⟶ X), Smooth f → e ≫ f = 𝟙 _ → ∀ s : S, ∃ (V : S.Opens) (W : X.Opens) (_ : W ≤ f ⁻¹ᵁ V), IsAffineOpen V ∧ IsAffineOpen W ∧ e s ∈ W ∧ ∀ (k : Type) [Field k] (p : Spec (CommRingCat.of k) ⟶ S), p (IsLocalRing.closedPoint k) = s → PreirreducibleSpace ↥(pullback (W.ι ≫ f) p) := by
  intro X S f e hf he s
  have hes : f (e s) = s := by
    rw [← Scheme.Hom.comp_apply, he]; rfl
  obtain ⟨W₁, hW₁, hW₁'⟩ := exists_open_inter_fiber_subset_sectionComponent X S f e hf he s
  obtain ⟨_, ⟨V, hV, rfl⟩, hsV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ s) isOpen_univ
  have hmem : e s ∈ ((W₁ ⊓ f ⁻¹ᵁ V : X.Opens) : Set X) := ⟨hW₁, by
    change f (e s) ∈ (V : Set S)
    rw [hes]; exact hsV⟩
  obtain ⟨_, ⟨W : X.Opens, hW, rfl⟩, hsW, hle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hmem (W₁ ⊓ f ⁻¹ᵁ V).isOpen
  refine ⟨V, W, fun x hx => (hle hx).2, hV, hW, hsW, ?_⟩
  intro k _ p hp
  let e' : Spec (CommRingCat.of k) ⟶ pullback f p :=
    pullback.lift (p ≫ e) (𝟙 _) (by simp [he])
  have he' : e' ≫ pullback.snd f p = 𝟙 _ := pullback.lift_snd _ _ _
  have he'' : e' ≫ pullback.fst f p = p ≫ e := pullback.lift_fst _ _ _
  have h1 := GlobalTheory.T.preimage_section_connectedComponentIn_of_isPullback X S _ _ f (pullback.snd f p) p (pullback.fst f p) e e' hf
    (IsPullback.of_hasPullback f p) he he' he''
  have h2 := (GlobalTheory.T.isOpen_isIrreducible_componentOfRationalPoint_smooth k _ (pullback.snd f p) e' inferInstance he').2
  rw [← h1] at h2
  let j : pullback (W.ι ≫ f) p ⟶ pullback f p :=
    pullback.map _ _ _ _ W.ι (𝟙 _) (𝟙 _) (by simp) (by simp)
  have hj : IsOpenImmersion j := inferInstance
  have hjf : j ≫ pullback.fst f p = pullback.fst _ _ ≫ W.ι := pullback.lift_fst _ _ _
  have h3 := h2.isPreirreducible.preimage j.isOpenEmbedding
  constructor
  convert h3 using 1
  symm
  rw [Set.eq_univ_iff_forall]
  intro y
  have hx : f (pullback.fst f p (j y)) = s := by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, ← hp]
    congr 1
    exact Subsingleton.elim (α := PrimeSpectrum k) _ _
  change pullback.fst f p (j y) ∈ connectedComponentIn (f ⁻¹' {f (pullback.fst f p (j y))})
    (e (f (pullback.fst f p (j y))))
  rw [hx]
  refine hW₁' _ ?_ hx
  rw [← Scheme.Hom.comp_apply, hjf, Scheme.Hom.comp_apply]
  exact (hle (pullback.fst (W.ι ≫ f) p y).2).1

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineChartPreirreducibleFiberStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_affine_chart_preirreducible_fiber' : ∀ (X S : Scheme.{0}) (f : X ⟶ S) (e : S ⟶ X), Smooth f → e ≫ f = 𝟙 _ → ∀ s : S, ∃ (V : S.Opens) (W : X.Opens) (_ : W ≤ f ⁻¹ᵁ V), IsAffineOpen V ∧ IsAffineOpen W ∧ e s ∈ W ∧ ∀ (k : Type) [Field k] (p : Spec (CommRingCat.of k) ⟶ S), p (IsLocalRing.closedPoint k) = s → PreirreducibleSpace ↥(pullback (W.ι ≫ f) p) := by
  first | exact @GlobalTheory.exists_affine_chart_preirreducible_fiber | exact GlobalTheory.exists_affine_chart_preirreducible_fiber | (intros; apply GlobalTheory.exists_affine_chart_preirreducible_fiber <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreirreducibleSpaceTensorOfPullback

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem isPullback_comp_mono_right_of_isPullback {𝒞 : Type*} [Category 𝒞] {P X Y Z Z' : 𝒞} {fst : P ⟶ X} {snd : P ⟶ Y}
    {a : X ⟶ Z} {b : Y ⟶ Z} (m : Z ⟶ Z') [Mono m] (h : IsPullback fst snd a b) :
    IsPullback fst snd (a ≫ m) (b ≫ m) :=
  ⟨⟨by rw [← Category.assoc, h.w, Category.assoc]⟩, ⟨PullbackCone.IsLimit.mk _
    (fun c ↦ h.lift c.fst c.snd (by rw [← cancel_mono m]; simpa using c.condition))
    (fun c ↦ h.lift_fst _ _ _) (fun c ↦ h.lift_snd _ _ _)
    (fun c n h₁ h₂ ↦ h.hom_ext (by rw [h.lift_fst, h₁]) (by rw [h.lift_snd, h₂]))⟩⟩

theorem preirreducibleSpace_tensor_of_pullback :
    ∀ (X S : Scheme.{0}) (f : X ⟶ S) (V : S.Opens) (W : X.Opens) (h : W ≤ f ⁻¹ᵁ V)
      (hV : IsAffineOpen V) (hW : IsAffineOpen W) (k : Type) [Field k] [Algebra Γ(S, V) k]
      [Algebra Γ(S, V) Γ(X, W)], algebraMap Γ(S, V) Γ(X, W) = (f.appLE V W h).hom →
      PreirreducibleSpace ↥(pullback (W.ι ≫ f)
        (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) k)) ≫ hV.fromSpec)) →
      PreirreducibleSpace (PrimeSpectrum (k ⊗[Γ(S, V)] Γ(X, W))) := by
  intro X S f V W h hV hW k _ _ _ hA hP
  have sq := (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct Γ(S, V) k Γ(X, W))).flip
  have sq2 := sq.of_iso (fst' := Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) ≫
      hW.isoSpec.inv) (snd' := Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom))
    (f' := hW.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Γ(X, W))))
    (g' := Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) k)))
    (Iso.refl _) hW.isoSpec.symm (Iso.refl _) (Iso.refl _)
    (by simp) (by simp) (by simp) (by simp)
  have sq3 := isPullback_comp_mono_right_of_isPullback hV.fromSpec sq2
  have e : (hW.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Γ(X, W)))) ≫
      hV.fromSpec = W.ι ≫ f := by
    rw [hA, CommRingCat.ofHom_hom, Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec f hV hW h,
      ← hW.isoSpec_inv_ι, Category.assoc, Iso.hom_inv_id_assoc]
  rw [e] at sq3
  let φ := sq3.isoPullback
  have hsurj : Function.Surjective (Scheme.homeoOfIso φ.symm) := (Scheme.homeoOfIso φ.symm).surjective
  refine ⟨?_⟩
  have := (PreirreducibleSpace.isPreirreducible_univ (X := ↥(pullback (W.ι ≫ f)
        (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) k)) ≫ hV.fromSpec)))).image
    (Scheme.homeoOfIso φ.symm) (Scheme.homeoOfIso φ.symm).continuous.continuousOn
  rw [Set.image_univ_of_surjective hsurj] at this
  exact this

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreirreducibleSpaceTensorOfPullbackStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.preirreducibleSpace_tensor_of_pullback' : ∀ (X S : Scheme.{0}) (f : X ⟶ S) (V : S.Opens) (W : X.Opens) (h : W ≤ f ⁻¹ᵁ V) (hV : IsAffineOpen V) (hW : IsAffineOpen W) (k : Type) [Field k] [Algebra Γ(S, V) k] [Algebra Γ(S, V) Γ(X, W)], algebraMap Γ(S, V) Γ(X, W) = (f.appLE V W h).hom → PreirreducibleSpace ↥(pullback (W.ι ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) k)) ≫ hV.fromSpec)) → PreirreducibleSpace (PrimeSpectrum (k ⊗[Γ(S, V)] Γ(X, W))) := by
  first | exact @GlobalTheory.preirreducibleSpace_tensor_of_pullback | exact GlobalTheory.preirreducibleSpace_tensor_of_pullback | (intros; apply GlobalTheory.preirreducibleSpace_tensor_of_pullback <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenNbhdSectionFibreIsPreirreducible

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem affineOpen_fromSpec_mem_basicOpen_iff {Y : Scheme.{0}} {U : Y.Opens} (hU : IsAffineOpen U)
    (c : Γ(Y, U)) (P : PrimeSpectrum Γ(Y, U)) : hU.fromSpec P ∈ Y.basicOpen c ↔ c ∉ P.asIdeal :=
  SetLike.ext_iff.1 (hU.fromSpec_preimage_basicOpen c) P

theorem exists_open_nbhd_section_fibre_isPreirreducible : ∀ (X S : Scheme.{0}) (f : X ⟶ S) (e : S ⟶ X),
    Smooth f → e ≫ f = 𝟙 _ → ∀ s : S, ∃ (U : X.Opens) (V₀ V : S.Opens) (I : Finset Γ(S, V)),
      V₀ ≤ V ∧ s ∈ V₀ ∧ e s ∈ U ∧ (∀ c ∈ I, s ∉ S.basicOpen c) ∧
      ∀ t ∈ V₀, (∀ c ∈ I, t ∉ S.basicOpen c) → IsPreirreducible ((U : Set X) ∩ f ⁻¹' {t}) := by
  intro X S f e hf hef s
  obtain ⟨V, W, hWV, hV, hW, hes, hirr⟩ := GlobalTheory.T.exists_affine_chart_preirreducible_fiber' X S f e hf hef s
  have hfes : f (e s) = s := by rw [← Scheme.Hom.comp_apply, hef]; rfl
  have hsV : s ∈ V := by have h := hWV hes; rwa [Scheme.Hom.mem_preimage, hfes] at h
  letI : Algebra Γ(S, V) Γ(X, W) := (f.appLE V W hWV).hom.toAlgebra
  have hsm : Algebra.Smooth Γ(S, V) Γ(X, W) :=
    RingHom.smooth_algebraMap.mp (HasRingHomProperty.appLE @Smooth f hf ⟨V, hV⟩ ⟨W, hW⟩ hWV)

  have hcomap : ∀ (x : X) (hxW : x ∈ W) (hxV : f x ∈ V),
      (hW.primeIdealOf ⟨x, hxW⟩).asIdeal.comap (algebraMap Γ(S, V) Γ(X, W)) =
        (hV.primeIdealOf ⟨f x, hxV⟩).asIdeal := fun x hxW hxV =>
    congrArg PrimeSpectrum.asIdeal (IsAffineOpen.comap_primeIdealOf_appLE V hV W hW hWV hxW)
  have hfx : ∀ r : Spec Γ(X, W), f (hW.fromSpec r) =
      hV.fromSpec (Spec.map (f.appLE V W hWV) r) := fun r => by
    show (hW.fromSpec ≫ f) r = (Spec.map (f.appLE V W hWV) ≫ hV.fromSpec) r
    rw [IsAffineOpen.SpecMap_appLE_fromSpec f hV hW hWV]
  set q := hW.primeIdealOf ⟨e s, hes⟩ with hqdef
  set p₀ := hV.primeIdealOf ⟨s, hsV⟩ with hp₀def
  have hq : q.asIdeal.comap (algebraMap Γ(S, V) Γ(X, W)) = p₀.asIdeal := by
    rw [hqdef, hcomap (e s) hes (hWV hes)]
    congr 2; exact Subtype.ext hfes
  let Ω := AlgebraicClosure p₀.asIdeal.ResidueField
  have hker : RingHom.ker (algebraMap Γ(S, V) Ω) = p₀.asIdeal := by
    rw [IsScalarTower.algebraMap_eq Γ(S, V) p₀.asIdeal.ResidueField Ω, ← RingHom.comap_ker,
      (RingHom.injective_iff_ker_eq_bot _).mp (algebraMap p₀.asIdeal.ResidueField Ω).injective]
    exact Ideal.ker_algebraMap_residueField _
  have hpt : (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Ω)) ≫ hV.fromSpec)
      (IsLocalRing.closedPoint Ω) = s := by
    have : Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Ω)) (IsLocalRing.closedPoint Ω) = p₀ := by
      apply PrimeSpectrum.ext
      change Ideal.comap (algebraMap Γ(S, V) Ω) (IsLocalRing.maximalIdeal Ω) = p₀.asIdeal
      rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot, hker]
    show hV.fromSpec (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Ω)) (IsLocalRing.closedPoint Ω)) = s
    rw [this, hp₀def, hV.fromSpec_primeIdealOf]
  have h1 := hirr Ω _ hpt
  have h2 := GlobalTheory.T.preirreducibleSpace_tensor_of_pullback' X S f V W hWV hV hW Ω rfl h1
  obtain ⟨b, a, I, hb, ha, hI, hmain⟩ := GlobalTheory.T.exists_basicOpen_fibres_preirreducible_smooth Γ(S, V) Γ(X, W) hsm q Ω (hq.trans hker.symm) h2
  refine ⟨X.basicOpen b, S.basicOpen a, V, I, S.basicOpen_le a, ?_, ?_, ?_, ?_⟩
  · have h := (affineOpen_fromSpec_mem_basicOpen_iff hV a p₀).mpr (by rw [← hq]; exact ha)
    rwa [hp₀def, hV.fromSpec_primeIdealOf] at h
  · have h := (affineOpen_fromSpec_mem_basicOpen_iff hW b q).mpr hb
    rwa [hqdef, hW.fromSpec_primeIdealOf] at h
  · intro c hc hsc
    have h := (affineOpen_fromSpec_mem_basicOpen_iff hV c p₀).mp
      (by rw [hp₀def, hV.fromSpec_primeIdealOf]; exact hsc)
    exact h (by rw [← hq]; exact hI c hc)
  · intro t htV₀ htI
    have htV : t ∈ V := S.basicOpen_le a htV₀
    set t' := hV.primeIdealOf ⟨t, htV⟩ with ht'def
    have hft' : hV.fromSpec t' = t := hV.fromSpec_primeIdealOf _
    have ha' : a ∉ t'.asIdeal :=
      (affineOpen_fromSpec_mem_basicOpen_iff hV a t').mp (by rw [hft']; exact htV₀)
    have hc' : ∀ c ∈ I, c ∈ t'.asIdeal := fun c hc => by
      by_contra hnc
      exact htI c hc (hft' ▸ (affineOpen_fromSpec_mem_basicOpen_iff hV c t').mpr hnc)
    have hZ := hmain t' ha' hc'
    have heq : ((X.basicOpen b : X.Opens) : Set X) ∩ f ⁻¹' {t} = hW.fromSpec ''
        {r : PrimeSpectrum Γ(X, W) | r.asIdeal.comap (algebraMap Γ(S, V) Γ(X, W)) = t'.asIdeal ∧
          b ∉ r.asIdeal} := by
      ext x
      constructor
      · rintro ⟨hxU, hxt⟩
        have hxW : x ∈ W := X.basicOpen_le b hxU
        have hxt' : f x = t := hxt
        refine ⟨hW.primeIdealOf ⟨x, hxW⟩, ⟨?_, ?_⟩, hW.fromSpec_primeIdealOf _⟩
        · rw [hcomap x hxW (hWV hxW), ht'def]
          congr 2; exact Subtype.ext hxt'
        · exact (affineOpen_fromSpec_mem_basicOpen_iff hW b _).mp
            (by rw [hW.fromSpec_primeIdealOf]; exact hxU)
      · rintro ⟨r, ⟨hr1, hr2⟩, rfl⟩
        refine ⟨(affineOpen_fromSpec_mem_basicOpen_iff hW b r).mpr hr2, ?_⟩
        show f (hW.fromSpec r) = t
        have : Spec.map (f.appLE V W hWV) r = t' := PrimeSpectrum.ext hr1
        rw [hfx, this, hft']
    rw [heq]
    exact hZ.image _ (Scheme.Hom.continuous _).continuousOn

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenNbhdSectionFibreIsPreirreducibleStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_open_nbhd_section_fiber_isPreirreducible : ∀ (X S : Scheme.{0}) (f : X ⟶ S) (e : S ⟶ X), Smooth f → e ≫ f = 𝟙 _ → ∀ s : S, ∃ (U : X.Opens) (V₀ V : S.Opens) (I : Finset Γ(S, V)), V₀ ≤ V ∧ s ∈ V₀ ∧ e s ∈ U ∧ (∀ c ∈ I, s ∉ S.basicOpen c) ∧ ∀ t ∈ V₀, (∀ c ∈ I, t ∉ S.basicOpen c) → IsPreirreducible ((U : Set X) ∩ f ⁻¹' {t}) := by
  first | exact @GlobalTheory.exists_open_nbhd_section_fibre_isPreirreducible | exact GlobalTheory.exists_open_nbhd_section_fibre_isPreirreducible | (intros; apply GlobalTheory.exists_open_nbhd_section_fibre_isPreirreducible <;> assumption)
end
end
