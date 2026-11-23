module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.ResidueField
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.LocalSubring
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionComponentsPreimageOfIsPullbackStatement
public import Mathlib.Order.CompletePartialOrder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenConnectedComponentOfIsLocallyNoetherianStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothGenericFibreClosurePartitionStatement
public import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsValuationRingDominatingSpecialization

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory


set_option backward.isDefEq.respectTransparency.types false in
theorem exists_valuationRing_of_specializes (X : Scheme.{0}) (x' x : X) (h : x' ⤳ x) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : ValuationRing V)
      (g : Spec (CommRingCat.of V) ⟶ X),
      g (IsLocalRing.closedPoint V) = x ∧ g (⊥ : PrimeSpectrum V) = x' := by
  let φ : X.presheaf.stalk x ⟶ X.residueField x' :=
    X.presheaf.stalkSpecializes h ≫ X.residue x'
  obtain ⟨A, hA, hA_local⟩ := IsLocalRing.exists_factor_valuationRing φ.hom
  let ψ : X.presheaf.stalk x ⟶ .of A := CommRingCat.ofHom (φ.hom.codRestrict _ hA)
  have w : X.fromSpecResidueField x' =
      Spec.map (CommRingCat.ofHom (algebraMap A (X.residueField x'))) ≫
        Spec.map ψ ≫ X.fromSpecStalk x := by
    rw [Scheme.fromSpecResidueField, ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk h]
    simp_rw [← Spec.map_comp_assoc]
    rfl
  refine ⟨A, inferInstance, inferInstance, inferInstance, Spec.map ψ ≫ X.fromSpecStalk x, ?_, ?_⟩
  · simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply]
    have : Spec.map ψ (IsLocalRing.closedPoint A) =
        IsLocalRing.closedPoint (X.presheaf.stalk x) :=
      IsLocalRing.comap_closedPoint (S := A) (φ.hom.codRestrict A.toSubring hA)
    rw [this, X.fromSpecStalk_closedPoint]
  · have h1 : Spec.map (CommRingCat.ofHom (algebraMap A (X.residueField x')))
        (IsLocalRing.closedPoint (X.residueField x')) = (⊥ : PrimeSpectrum A) := by
      apply PrimeSpectrum.ext
      change Ideal.comap (algebraMap A (X.residueField x'))
        (IsLocalRing.maximalIdeal (X.residueField x')) = ⊥
      rw [IsLocalRing.maximalIdeal_eq_bot]
      exact Ideal.comap_bot_of_injective _ Subtype.val_injective
    rw [← h1, ← Scheme.Hom.comp_apply, ← w, Scheme.fromSpecResidueField_apply]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsValuationRingDominatingSpecializationStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_valuationRing_dominating_specialization : ∀ (X : Scheme.{0}) (x' x : X), x' ⤳ x → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : ValuationRing V) (g : Spec (CommRingCat.of V) ⟶ X), g (IsLocalRing.closedPoint V) = x ∧ g (⊥ : PrimeSpectrum V) = x' := by
  first | exact @GlobalTheory.exists_valuationRing_of_specializes | exact GlobalTheory.exists_valuationRing_of_specializes | (intros; apply GlobalTheory.exists_valuationRing_of_specializes <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionMemComponentGenericOfClosedValuation

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem separated_of_isOpen_component_subtype {X : Type*} [TopologicalSpace X] (F : Set X) (a : X)
    (ha : a ∈ F) (ho : IsOpen (connectedComponent (⟨a, ha⟩ : F))) :
    Disjoint (connectedComponentIn F a) (closure (F \ connectedComponentIn F a)) ∧
      Disjoint (closure (connectedComponentIn F a)) (F \ connectedComponentIn F a) := by
  have hC : connectedComponentIn F a = Subtype.val '' connectedComponent (⟨a, ha⟩ : F) :=
    connectedComponentIn_eq_image ha
  have hmem : ∀ y : F, (y : X) ∈ connectedComponentIn F a ↔ y ∈ connectedComponent (⟨a, ha⟩ : F) := by
    intro y
    rw [hC]
    exact Subtype.val_injective.mem_set_image
  obtain ⟨U, hU, hUe⟩ := isOpen_induced_iff.1 ho
  obtain ⟨Z, hZ, hZe⟩ := isClosed_induced_iff.1
    (isClosed_connectedComponent : IsClosed (connectedComponent (⟨a, ha⟩ : F)))
  constructor
  · have h1 : closure (F \ connectedComponentIn F a) ⊆ Uᶜ := by
      refine closure_minimal ?_ hU.isClosed_compl
      rintro y ⟨hyF, hy⟩ hyU
      apply hy
      refine (hmem ⟨y, hyF⟩).2 ?_
      rw [← hUe]
      exact hyU
    refine Set.disjoint_left.2 fun y hy hy' => h1 hy' ?_
    have := (hmem ⟨y, connectedComponentIn_subset F a hy⟩).1 hy
    rw [← hUe] at this
    exact this
  · have h1 : closure (connectedComponentIn F a) ⊆ Z := by
      refine closure_minimal ?_ hZ
      intro y hy
      have := (hmem ⟨y, connectedComponentIn_subset F a hy⟩).1 hy
      rw [← hZe] at this
      exact this
    refine Set.disjoint_left.2 fun y hy hy' => hy'.2 ?_
    refine (hmem ⟨y, hy'.1⟩).2 ?_
    rw [← hZe]
    exact h1 hy

theorem isOpen_component_fibre_subtype {X S : Scheme.{0}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (s : S) (a : (f ⁻¹' {s} : Set X)) : IsOpen (connectedComponent a) := by
  have : LocallyOfFiniteType (f.fiberToSpecResidueField s) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd f (S.fromSpecResidueField s)))
  have hn : IsLocallyNoetherian (f.fiber s) :=
    LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField s)
  have ho := GlobalTheory.T.isOpen_connectedComponent_of_isLocallyNoetherian' _ hn ((f.fiberHomeo s).symm a)
  have h := (f.fiberHomeo s).isOpenMap _ ho
  have h2 : (f.fiberHomeo s) '' connectedComponent ((f.fiberHomeo s).symm a)
      = connectedComponent a := by
    have := (f.fiberHomeo s).image_connectedComponentIn (s := Set.univ)
      (x := (f.fiberHomeo s).symm a) (Set.mem_univ _)
    simpa [connectedComponentIn_univ, (f.fiberHomeo s).surjective.range_eq] using this
  rwa [h2] at h

theorem section_mem_component_generic_of_closed :
    ∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of V)) (e σ : Spec (CommRingCat.of V) ⟶ X), Smooth f → e ≫ f = 𝟙 _ → σ ≫ f = 𝟙 _ → σ (IsLocalRing.closedPoint V) ∈ {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} → σ (⊥ : PrimeSpectrum V) ∈ {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} := by
  intro V _ _ _ X f e σ hf he hσ hm
  have hfe : ∀ p : (Spec (CommRingCat.of V) : Scheme.{0}), f (e p) = p := fun p => by
    rw [← Scheme.Hom.comp_apply, he]; rfl
  have hfσ : ∀ p : (Spec (CommRingCat.of V) : Scheme.{0}), f (σ p) = p := fun p => by
    rw [← Scheme.Hom.comp_apply, hσ]; rfl
  let g₀ : (Spec (CommRingCat.of V) : Scheme.{0}) := (⊥ : PrimeSpectrum V)
  let m : (Spec (CommRingCat.of V) : Scheme.{0}) := IsLocalRing.closedPoint V
  change σ m ∈ connectedComponentIn (f ⁻¹' {f (σ m)}) (e (f (σ m))) at hm
  change σ g₀ ∈ connectedComponentIn (f ⁻¹' {f (σ g₀)}) (e (f (σ g₀)))
  rw [hfσ] at hm ⊢
  have hsp : g₀ ⤳ m := IsLocalRing.specializes_closedPoint (R := V) ⊥
  have ha : e g₀ ∈ f ⁻¹' {g₀} := hfe g₀
  obtain ⟨h1, h2⟩ := separated_of_isOpen_component_subtype (f ⁻¹' {g₀}) (e g₀) ha
    (isOpen_component_fibre_subtype f g₀ ⟨e g₀, ha⟩)
  obtain ⟨hd, hu⟩ := GlobalTheory.T.disjoint_closure_and_union_eq_univ_of_genericFibre_partition V X f hf (connectedComponentIn (f ⁻¹' {g₀}) (e g₀))
    (f ⁻¹' {g₀} \ connectedComponentIn (f ⁻¹' {g₀}) (e g₀))
    (Set.union_diff_cancel (connectedComponentIn_subset _ _)) h1 h2
  by_contra hne
  have hσ' : σ m ∈ closure (f ⁻¹' {g₀} \ connectedComponentIn (f ⁻¹' {g₀}) (e g₀)) :=
    (hsp.map σ.continuous).mem_closed isClosed_closure (subset_closure ⟨hfσ g₀, hne⟩)
  have he' : e m ∈ closure (connectedComponentIn (f ⁻¹' {g₀}) (e g₀)) :=
    (hsp.map e.continuous).mem_closed isClosed_closure
      (subset_closure (mem_connectedComponentIn ha))
  have hclopen : IsClopen (closure (connectedComponentIn (f ⁻¹' {g₀}) (e g₀))) := by
    refine ⟨isClosed_closure, ?_⟩
    have : closure (connectedComponentIn (f ⁻¹' {g₀}) (e g₀))
        = (closure (f ⁻¹' {g₀} \ connectedComponentIn (f ⁻¹' {g₀}) (e g₀)))ᶜ :=
      (IsCompl.eq_compl ⟨hd, codisjoint_iff.2 hu⟩)
    rw [this]
    exact isClosed_closure.isOpen_compl
  have hsub := (isPreconnected_connectedComponentIn (x := e m) (F := f ⁻¹' {m})).subset_isClopen
    hclopen ⟨e m, mem_connectedComponentIn (hfe m), he'⟩
  exact Set.disjoint_left.1 hd (hsub hm) hσ'

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionMemComponentGenericOfClosedValuationStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.section_mem_component_generic_of_closed_valuation : ∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of V)) (e σ : Spec (CommRingCat.of V) ⟶ X), Smooth f → e ≫ f = 𝟙 _ → σ ≫ f = 𝟙 _ → σ (IsLocalRing.closedPoint V) ∈ {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} → σ (⊥ : PrimeSpectrum V) ∈ {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} := by
  first | exact @GlobalTheory.section_mem_component_generic_of_closed | exact GlobalTheory.section_mem_component_generic_of_closed | (intros; apply GlobalTheory.section_mem_component_generic_of_closed <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableUnderGeneralizationSectionComponents

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem stableUnderGeneralization_sectionComponents :
    ∀ (X S : Scheme.{0}) (f : X ⟶ S) (e : S ⟶ X), Smooth f → e ≫ f = 𝟙 _ →
      StableUnderGeneralization {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} := by
  intro X S f e hf hef x x' hxx' hx
  obtain ⟨V, _, _, _, g, hgc, hgb⟩ := GlobalTheory.T.exists_valuationRing_dominating_specialization X x' x hxx'
  set p : Spec (CommRingCat.of V) ⟶ S := g ≫ f with hp
  have hpb : IsPullback (pullback.fst f p) (pullback.snd f p) f p := IsPullback.of_hasPullback f p
  let σ : Spec (CommRingCat.of V) ⟶ pullback f p := pullback.lift g (𝟙 _) (by simp [hp])
  let e' : Spec (CommRingCat.of V) ⟶ pullback f p :=
    pullback.lift (p ≫ e) (𝟙 _) (by simp [Category.assoc, hef])
  have hσf : σ ≫ pullback.snd f p = 𝟙 _ := pullback.lift_snd _ _ _
  have hσq : σ ≫ pullback.fst f p = g := pullback.lift_fst _ _ _
  have he'f : e' ≫ pullback.snd f p = 𝟙 _ := pullback.lift_snd _ _ _
  have he'q : e' ≫ pullback.fst f p = p ≫ e := pullback.lift_fst _ _ _
  haveI : Smooth f := hf
  have hf' : Smooth (pullback.snd f p) := inferInstance
  have key := GlobalTheory.T.preimage_section_connectedComponentIn_of_isPullback X S (pullback f p) (Spec (CommRingCat.of V)) f (pullback.snd f p) p
    (pullback.fst f p) e e' hf hpb hef he'f he'q
  have hc : σ (IsLocalRing.closedPoint V) ∈ {y : ↥(pullback f p) | y ∈ connectedComponentIn
      (pullback.snd f p ⁻¹' {pullback.snd f p y}) (e' (pullback.snd f p y))} := by
    rw [← key]
    rw [Set.mem_preimage]
    have h1 : (pullback.fst f p) (σ (IsLocalRing.closedPoint V)) = x := by
      rw [← hgc, ← hσq]
      rfl
    rw [h1]
    exact hx
  have hb := GlobalTheory.T.section_mem_component_generic_of_closed_valuation V (pullback f p) (pullback.snd f p) e' σ hf' he'f hσf hc
  rw [← key] at hb
  have : (pullback.fst f p) (σ (⊥ : PrimeSpectrum V)) = x' := by
    rw [← hgb, ← hσq]
    rfl
  rw [← this]
  exact hb

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableUnderGeneralizationSectionComponentsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.stableUnderGeneralization_section_connectedComponentIn : ∀ (X S : Scheme.{0}) (f : X ⟶ S) (e : S ⟶ X), Smooth f → e ≫ f = 𝟙 _ → StableUnderGeneralization {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} := by
  first | exact @GlobalTheory.stableUnderGeneralization_sectionComponents | exact GlobalTheory.stableUnderGeneralization_sectionComponents | (intros; apply GlobalTheory.stableUnderGeneralization_sectionComponents <;> assumption)
end
end
