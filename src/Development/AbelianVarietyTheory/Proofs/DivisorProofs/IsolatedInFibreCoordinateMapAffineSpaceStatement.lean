module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.AlgebraicGeometry.Modules.Sheaf

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenRangeEqInterPreimageEtaleUnivOpen

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem isOpen_range_of_etale_of_universallyOpen_comp {Y Z T : Scheme.{0}} (i' : Z ⟶ Y) (h : Y ⟶ T)
    [Etale h] (hu : UniversallyOpen (i' ≫ h)) : IsOpen (Set.range i') := by
  have s_open : IsOpenImmersion (pullback.lift (𝟙 Z) i' (by simp) : Z ⟶ pullback (i' ≫ h) h) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (pullback_lift_diagonal_isPullback i' h) inferInstance
  have e : Set.range i' = (pullback.snd (i' ≫ h) h) '' Set.range (pullback.lift (𝟙 Z) i' (by simp) : Z ⟶ pullback (i' ≫ h) h) := by
    rw [← Set.range_comp]
    congr 1
    ext z
    rw [Function.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_snd]
  rw [e]
  exact (pullback.snd (i' ≫ h) h).isOpenMap _ (pullback.lift (𝟙 Z) i' _).isOpenEmbedding.isOpen_range

theorem exists_opens_range_eq_of_etale {X B T Z : Scheme.{0}} (c : X ⟶ B) (j : T ⟶ B) (i : Z ⟶ X) (φ : Z ⟶ T)
    (hc : Etale c) (hj : IsPreimmersion j) (hφ : UniversallyOpen φ) (w : i ≫ c = φ ≫ j) :
    ∃ W : X.Opens, Set.range i = (W : Set X) ∩ c ⁻¹' Set.range j := by
  let i' : Z ⟶ pullback c j := pullback.lift i φ w
  have hi' : i' ≫ pullback.snd c j = φ := pullback.lift_snd _ _ _
  have ho : IsOpen (Set.range i') :=
    isOpen_range_of_etale_of_universallyOpen_comp i' (pullback.snd c j) (by rw [hi']; exact hφ)
  have hemb := IsPreimmersion.isEmbedding (pullback.fst c j)
  obtain ⟨U, hU, hpre⟩ := hemb.isInducing.isOpen_iff.1 ho
  refine ⟨⟨U, hU⟩, ?_⟩
  have hr : Set.range i = (pullback.fst c j) '' Set.range i' := by
    rw [← Set.range_comp]
    congr 1
    ext z
    rw [Function.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_fst]
  rw [hr, ← hpre, Set.image_preimage_eq_inter_range, Scheme.Pullback.range_fst]
  rfl

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenRangeEqInterPreimageEtaleUnivOpenStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_open_range_eq_inter_preimage_etale_univOpen : ∀ (X B T Z : Scheme.{0}) (c : X ⟶ B) (j : T ⟶ B) (i : Z ⟶ X) (φ : Z ⟶ T), Etale c → IsPreimmersion j → UniversallyOpen φ → i ≫ c = φ ≫ j → ∃ W : X.Opens, Set.range i = (W : Set X) ∩ c ⁻¹' Set.range j := by
  first | exact @GlobalTheory.Mum.exists_opens_range_eq_of_etale | exact GlobalTheory.Mum.exists_opens_range_eq_of_etale | (intros; apply GlobalTheory.Mum.exists_opens_range_eq_of_etale <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperSurjectiveAffineChartBijectiveSections

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.FibOpen

theorem universallyOpen_of {X Y : Scheme.{0}} (f : X ⟶ Y) [UniversallyClosed f] [UniversallyInjective f]
    [Surjective f] : UniversallyOpen f := by
  constructor
  intro X' Y' i₁ i₂ f' hf
  have h1 : UniversallyClosed f' := MorphismProperty.of_isPullback hf.flip inferInstance
  have h2 : UniversallyInjective f' := MorphismProperty.of_isPullback hf.flip inferInstance
  have h3 : Surjective f' := MorphismProperty.of_isPullback hf.flip inferInstance
  have hb : Function.Bijective f' := ⟨f'.injective, f'.surjective⟩
  show IsOpenMap f'
  intro U hU
  have e : f' '' U = (f' '' Uᶜ)ᶜ := by rw [Set.image_compl_eq hb, compl_compl]
  rw [e]
  exact (f'.isClosedMap _ hU.isClosed_compl).isOpen_compl

theorem fiber_hom_ext {X Y T : Scheme.{0}} (f : X ⟶ Y) (y : Y) {u v : T ⟶ f.fiber y}
    (h₁ : u ≫ f.fiberι y = v ≫ f.fiberι y)
    (h₂ : u ≫ f.fiberToSpecResidueField y = v ≫ f.fiberToSpecResidueField y) : u = v :=
  pullback.hom_ext h₁ h₂

@[reassoc]
theorem fiber_condition {X Y : Scheme.{0}} (f : X ⟶ Y) (y : Y) :
    f.fiberι y ≫ f = f.fiberToSpecResidueField y ≫ Y.fromSpecResidueField y :=
  pullback.condition

def fiberLift {X Y T : Scheme.{0}} (f : X ⟶ Y) (y : Y) (u : T ⟶ X) (v : T ⟶ Spec (Y.residueField y))
    (h : u ≫ f = v ≫ Y.fromSpecResidueField y) : T ⟶ f.fiber y :=
  pullback.lift u v h

@[reassoc (attr := simp)]
theorem fiberLift_ι {X Y T : Scheme.{0}} (f : X ⟶ Y) (y : Y) (u : T ⟶ X) (v : T ⟶ Spec (Y.residueField y))
    (h : u ≫ f = v ≫ Y.fromSpecResidueField y) : fiberLift f y u v h ≫ f.fiberι y = u :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem fiberLift_snd {X Y T : Scheme.{0}} (f : X ⟶ Y) (y : Y) (u : T ⟶ X) (v : T ⟶ Spec (Y.residueField y))
    (h : u ≫ f = v ≫ Y.fromSpecResidueField y) : fiberLift f y u v h ≫ f.fiberToSpecResidueField y = v :=
  pullback.lift_snd _ _ _

theorem range_comp_fromSpecResidueField {X T : Scheme.{0}} [Nonempty T] (x : X) (t : T ⟶ Spec (X.residueField x)) :
    Set.range (t ≫ X.fromSpecResidueField x) = {x} := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
    rfl
  · rintro rfl
    obtain ⟨z⟩ := ‹Nonempty T›
    exact ⟨z, by rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]⟩

theorem comp_fromSpecResidueField_apply {Y T : Scheme.{0}} (y : Y) (t : T ⟶ Spec (Y.residueField y)) (z : T) :
    (t ≫ Y.fromSpecResidueField y) z = y := by
  rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]

end GlobalTheory.FibOpen
end


set_option backward.isDefEq.respectTransparency.types false in
theorem GlobalTheory.FibOpen.fibre_universallyOpen : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S X : Scheme.{0}) (π : S ⟶ Sp R) (U : Over (Sp R)) (a : X ⟶ U.left) (b : X ⟶ S) (g : ℕ) (τ : U.left ⟶ 𝔸(Fin g; Sp R)) (c : X ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) π), IsProper π → Surjective π → Function.Bijective π.appTop.hom → LocallyOfFiniteType U.hom → IsSeparated U.hom → IsProper a → (∀ V : U.left.Opens, Function.Bijective (a.app V).hom) → τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = U.hom → c ≫ pullback.fst _ _ = a ≫ τ → c ≫ pullback.snd _ _ = b → Etale c → ∀ x : U.left, IsClosed ({x} : Set U.left) → U.hom x = closedPoint R → (∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ X), Set.range (p ≫ a) = {x} → p ≫ a = p' ≫ a → p ≫ b = p' ≫ b → p = p') → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ U.left) (s : Sp Ω ⟶ S), Set.range ξ = {x} → ξ ≫ U.hom = s ≫ π → ∃ p : Sp Ω ⟶ X, p ≫ a = ξ ∧ p ≫ b = s) → ∀ φ : a.fiber x ⟶ (pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiber (τ x), φ ≫ (pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberι (τ x) = a.fiberι x ≫ c → φ ≫ (pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberToSpecResidueField (τ x) = a.fiberToSpecResidueField x ≫ Spec.map (τ.residueFieldMap x) → UniversallyOpen φ := by
  intro R _ _ _ _ S X π U a b g τ c hπp hπs hΓ hlft hsep hap haO hτ hc₁ hc₂ het x hxc hxcl hinj hsurj φ hφ₁ hφ₂
  let ψ : a.fiber x ⟶ pullback ((pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberToSpecResidueField (τ x)) (Spec.map (τ.residueFieldMap x)) :=
    pullback.lift φ (a.fiberToSpecResidueField x) hφ₂
  have hψ₁ : ψ ≫ pullback.fst _ _ = φ := pullback.lift_fst _ _ _
  have hψ₂ : ψ ≫ pullback.snd _ _ = a.fiberToSpecResidueField x := pullback.lift_snd _ _ _
  have hSx : pullback.fst ((pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberToSpecResidueField (τ x)) (Spec.map (τ.residueFieldMap x)) ≫ (pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberToSpecResidueField (τ x) =
      pullback.snd _ _ ≫ (Spec.map (τ.residueFieldMap x)) := pullback.condition
  have hres : U.left.fromSpecResidueField x ≫ τ = (Spec.map (τ.residueFieldMap x)) ≫ 𝔸(Fin g; Sp R).fromSpecResidueField (τ x) :=
    (τ.SpecMap_residueFieldMap_fromSpecResidueField x).symm
  have hFc : (pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π) ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = pullback.snd (𝔸(Fin g; Sp R) ↘ Sp R) π ≫ π := pullback.condition
  have hb : a.fiberι x ≫ b = φ ≫ (pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberι (τ x) ≫ pullback.snd _ _ := by
    rw [← hc₂, ← Category.assoc, ← hφ₁, Category.assoc]
  suffices h : UniversallyOpen ψ by
    rw [← hψ₁]; infer_instance
  haveI : IsProper a := hap
  haveI : IsProper π := hπp
  haveI : IsProper (a.fiberToSpecResidueField x) :=
    MorphismProperty.pullback_snd (P := @IsProper) _ _ hap
  haveI : IsSeparated (pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π) := MorphismProperty.pullback_fst (P := @IsSeparated) _ _ inferInstance
  haveI : IsSeparated ((pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberToSpecResidueField (τ x)) :=
    MorphismProperty.pullback_snd (P := @IsSeparated) _ _ inferInstance
  haveI : IsProper (ψ ≫ pullback.snd _ _) := by rw [hψ₂]; infer_instance
  haveI : IsProper ψ := IsProper.of_comp ψ (pullback.snd ((pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberToSpecResidueField (τ x)) (Spec.map (τ.residueFieldMap x)))
  haveI : UniversallyInjective ψ := by
    refine ((tfae_universallyInjective ψ).out 1 2).mpr ?_
    intro K _ q q' hq
    simp only at hq
    have e₂ : q ≫ a.fiberToSpecResidueField x = q' ≫ a.fiberToSpecResidueField x := by
      rw [← hψ₂, ← Category.assoc, hq, Category.assoc]
    have e₃ : q ≫ φ = q' ≫ φ := by rw [← hψ₁, ← Category.assoc, hq, Category.assoc]
    have ea : ∀ q : Spec (.of K) ⟶ a.fiber x, (q ≫ a.fiberι x) ≫ a =
        (q ≫ a.fiberToSpecResidueField x) ≫ U.left.fromSpecResidueField x := fun q => by
      rw [Category.assoc, Category.assoc, GlobalTheory.FibOpen.fiber_condition]
    have key := hinj K (q ≫ a.fiberι x) (q' ≫ a.fiberι x)
      (by rw [ea]; exact GlobalTheory.FibOpen.range_comp_fromSpecResidueField x _) (by rw [ea, ea, e₂])
      (by rw [Category.assoc, Category.assoc, hb, ← Category.assoc q, e₃, Category.assoc])
    exact GlobalTheory.FibOpen.fiber_hom_ext a x key e₂
  haveI : Surjective ψ := by
    constructor
    intro y
    let Ω := AlgebraicClosure ((pullback ((pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberToSpecResidueField (τ x)) (Spec.map (τ.residueFieldMap x))).residueField y)
    let t : Sp Ω ⟶ pullback ((pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberToSpecResidueField (τ x)) (Spec.map (τ.residueFieldMap x)) :=
      Spec.map (CommRingCat.ofHom (algebraMap ((pullback ((pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberToSpecResidueField (τ x)) (Spec.map (τ.residueFieldMap x))).residueField y) Ω)) ≫
        (pullback ((pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberToSpecResidueField (τ x)) (Spec.map (τ.residueFieldMap x))).fromSpecResidueField y
    let ξ := (t ≫ pullback.snd _ _) ≫ U.left.fromSpecResidueField x
    let s := t ≫ pullback.fst _ _ ≫ (pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberι (τ x) ≫ pullback.snd (𝔸(Fin g; Sp R) ↘ Sp R) π
    have hξ : ξ ≫ U.hom = s ≫ π := by
      simp only [ξ, s, Category.assoc]
      rw [← hτ, ← hFc, reassoc_of% hres, GlobalTheory.FibOpen.fiber_condition_assoc, reassoc_of% hSx]
    obtain ⟨p, hp₁, hp₂⟩ := hsurj Ω ξ s (GlobalTheory.FibOpen.range_comp_fromSpecResidueField x _) hξ
    let q : Sp Ω ⟶ a.fiber x := GlobalTheory.FibOpen.fiberLift a x p (t ≫ pullback.snd _ _) (by rw [hp₁])
    have hqt : q ≫ ψ = t := by
      apply pullback.hom_ext
      · rw [Category.assoc, hψ₁]
        apply GlobalTheory.FibOpen.fiber_hom_ext
        · rw [Category.assoc, hφ₁, GlobalTheory.FibOpen.fiberLift_ι_assoc]
          apply pullback.hom_ext
          · simp only [Category.assoc]
            rw [hc₁, reassoc_of% hp₁]
            simp only [ξ, Category.assoc]
            rw [hres, GlobalTheory.FibOpen.fiber_condition, reassoc_of% hSx]
          · simp only [Category.assoc]
            rw [hc₂, hp₂]
        · rw [Category.assoc, hφ₂, GlobalTheory.FibOpen.fiberLift_snd_assoc]
          simp only [Category.assoc]
          rw [hSx]
      · rw [Category.assoc, hψ₂, GlobalTheory.FibOpen.fiberLift_snd]
    obtain ⟨z⟩ : Nonempty (Sp Ω) := inferInstance
    refine ⟨q z, ?_⟩
    rw [← Scheme.Hom.comp_apply, hqt]
    exact GlobalTheory.FibOpen.comp_fromSpecResidueField_apply y _ z
  exact GlobalTheory.FibOpen.universallyOpen_of ψ
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperSurjectiveAffineChartBijectiveSectionsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.proper_surjective_affine_chart_bijective_sections : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S X : Scheme.{0}) (π : S ⟶ Sp R) (U : Over (Sp R)) (a : X ⟶ U.left) (b : X ⟶ S) (g : ℕ) (τ : U.left ⟶ 𝔸(Fin g; Sp R)) (c : X ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) π), IsProper π → Surjective π → Function.Bijective π.appTop.hom → LocallyOfFiniteType U.hom → IsSeparated U.hom → IsProper a → (∀ V : U.left.Opens, Function.Bijective (a.app V).hom) → τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = U.hom → c ≫ pullback.fst _ _ = a ≫ τ → c ≫ pullback.snd _ _ = b → Etale c → ∀ x : U.left, IsClosed ({x} : Set U.left) → U.hom x = closedPoint R → (∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ X), Set.range (p ≫ a) = {x} → p ≫ a = p' ≫ a → p ≫ b = p' ≫ b → p = p') → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ U.left) (s : Sp Ω ⟶ S), Set.range ξ = {x} → ξ ≫ U.hom = s ≫ π → ∃ p : Sp Ω ⟶ X, p ≫ a = ξ ∧ p ≫ b = s) → ∀ φ : a.fiber x ⟶ (pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiber (τ x), φ ≫ (pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberι (τ x) = a.fiberι x ≫ c → φ ≫ (pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberToSpecResidueField (τ x) = a.fiberToSpecResidueField x ≫ Spec.map (τ.residueFieldMap x) → UniversallyOpen φ := by
  first | exact @GlobalTheory.FibOpen.fibre_universallyOpen | exact GlobalTheory.FibOpen.fibre_universallyOpen | (intros; apply GlobalTheory.FibOpen.fibre_universallyOpen <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsolatedInFibreCoordinateMapAffineSpace

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem surjective_of_isProper_of_app_injective : ∀ (X Y : Scheme.{0}) (a : X ⟶ Y), IsProper a → (∀ V : Y.Opens, Function.Injective (a.app V).hom) → Function.Surjective a := by
  intro X Y a ha hinj
  haveI := ha
  by_contra hne
  simp only [Function.Surjective, not_forall] at hne
  obtain ⟨y, hy⟩ := hne
  have hcl : IsClosed (Set.range a) := by
    simpa using a.isClosedMap _ isClosed_univ
  let V : Y.Opens := ⟨(Set.range a)ᶜ, hcl.isOpen_compl⟩
  haveI : Nonempty V := ⟨⟨y, fun ⟨p, hp⟩ => hy ⟨p, hp⟩⟩⟩
  have hV : a ⁻¹ᵁ V = ⊥ := by
    ext p
    simp [V]
  haveI : Subsingleton Γ(X, a ⁻¹ᵁ V) :=
    CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hV)
  have : Subsingleton Γ(Y, V) := (hinj V).subsingleton
  exact not_subsingleton Γ(Y, V) this

theorem isolated_in_coordinate_fibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S X : Scheme.{0}) (π : S ⟶ Sp R) (U : Over (Sp R)) (a : X ⟶ U.left) (b : X ⟶ S) (g : ℕ) (τ : U.left ⟶ 𝔸(Fin g; Sp R)) (c : X ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) π), IsProper π → Surjective π → Function.Bijective π.appTop.hom → LocallyOfFiniteType U.hom → IsSeparated U.hom → IsProper a → (∀ V : U.left.Opens, Function.Bijective (a.app V).hom) → τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = U.hom → c ≫ pullback.fst _ _ = a ≫ τ → c ≫ pullback.snd _ _ = b → Etale c → ∀ x : U.left, IsClosed ({x} : Set U.left) → U.hom x = closedPoint R → (∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ X), Set.range (p ≫ a) = {x} → p ≫ a = p' ≫ a → p ≫ b = p' ≫ b → p = p') → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ U.left) (s : Sp Ω ⟶ S), Set.range ξ = {x} → ξ ≫ U.hom = s ≫ π → ∃ p : Sp Ω ⟶ X, p ≫ a = ξ ∧ p ≫ b = s) → ∃ O : U.left.Opens, x ∈ O ∧ ∀ u ∈ O, τ u = τ x → u = x := by
  intro R _ _ _ hR S X π U a b g τ c hπp hπs hπΓ hUf hUs hap haV hτ hc1 hc2 hc x hxc hxR hinj hsurj
  set F := pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π with hF
  have hw : (a.fiberι x ≫ c) ≫ F = (a.fiberToSpecResidueField x ≫ Spec.map (τ.residueFieldMap x)) ≫
      (𝔸(Fin g; Sp R)).fromSpecResidueField (τ x) := by
    rw [Category.assoc, hF, hc1, ← Category.assoc, Scheme.Hom.fiber_fac, Category.assoc, Category.assoc,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  let φ : a.fiber x ⟶ F.fiber (τ x) := pullback.lift _ _ hw
  have hφ1 : φ ≫ F.fiberι (τ x) = a.fiberι x ≫ c := pullback.lift_fst _ _ _
  have hφ2 : φ ≫ F.fiberToSpecResidueField (τ x) = a.fiberToSpecResidueField x ≫ Spec.map (τ.residueFieldMap x) :=
    pullback.lift_snd _ _ _
  have hUO := GlobalTheory.T.proper_surjective_affine_chart_bijective_sections R hR S X π U a b g τ c hπp hπs hπΓ hUf hUs hap haV hτ hc1 hc2 hc x hxc hxR hinj hsurj φ hφ1 hφ2
  haveI : IsPreimmersion (F.fiberι (τ x)) := inferInstance
  obtain ⟨W, hW⟩ := GlobalTheory.T.exists_open_range_eq_inter_preimage_etale_univOpen X _ _ _ c (F.fiberι (τ x)) (a.fiberι x) φ hc inferInstance hUO hφ1.symm
  rw [Scheme.Hom.range_fiberι, Scheme.Hom.range_fiberι] at hW
  have hs := surjective_of_isProper_of_app_injective X U.left a hap (fun V => (haV V).1)
  haveI := hap
  refine ⟨⟨(a '' (W : Set X)ᶜ)ᶜ, (a.isClosedMap _ W.isOpen.isClosed_compl).isOpen_compl⟩, ?_, ?_⟩
  · rintro ⟨p, hp, hpx⟩
    have : p ∈ a ⁻¹' {x} := hpx
    rw [hW] at this
    exact hp this.1
  · intro u hu hτu
    obtain ⟨p, rfl⟩ := hs u
    by_cases hp : p ∈ W
    · have : p ∈ (W : Set X) ∩ c ⁻¹' (F ⁻¹' {τ x}) := by
        refine ⟨hp, ?_⟩
        show F (c p) = τ x
        rw [← Scheme.Hom.comp_apply, hF, hc1, Scheme.Hom.comp_apply, hτu]
      rw [← hW] at this
      exact this
    · exact absurd ⟨p, hp, rfl⟩ hu

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsolatedInFibreCoordinateMapAffineSpaceStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.isolated_in_fibre_coordinateMap_affineSpace : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S X : Scheme.{0}) (π : S ⟶ Sp R) (U : Over (Sp R)) (a : X ⟶ U.left) (b : X ⟶ S) (g : ℕ) (τ : U.left ⟶ 𝔸(Fin g; Sp R)) (c : X ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) π), IsProper π → Surjective π → Function.Bijective π.appTop.hom → LocallyOfFiniteType U.hom → IsSeparated U.hom → IsProper a → (∀ V : U.left.Opens, Function.Bijective (a.app V).hom) → τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = U.hom → c ≫ pullback.fst _ _ = a ≫ τ → c ≫ pullback.snd _ _ = b → Etale c → ∀ x : U.left, IsClosed ({x} : Set U.left) → U.hom x = closedPoint R → (∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ X), Set.range (p ≫ a) = {x} → p ≫ a = p' ≫ a → p ≫ b = p' ≫ b → p = p') → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ U.left) (s : Sp Ω ⟶ S), Set.range ξ = {x} → ξ ≫ U.hom = s ≫ π → ∃ p : Sp Ω ⟶ X, p ≫ a = ξ ∧ p ≫ b = s) → ∃ O : U.left.Opens, x ∈ O ∧ ∀ u ∈ O, τ u = τ x → u = x := by
  first | exact @GlobalTheory.Mum.isolated_in_coordinate_fibre | exact GlobalTheory.Mum.isolated_in_coordinate_fibre | (intros; apply GlobalTheory.Mum.isolated_in_coordinate_fibre <;> assumption)
end
end
