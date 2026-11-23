module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.SiegelFamilyZetaUnit
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrincipalObjectDescendsLargeSubfield
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Linter.Style
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.AdelicGL2ExtOfLocalComponents
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagonalBundleDescendsSubringStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidSymmetricBundleDescendsToSubringFinsetStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.CategoryTheory.ExtremalEpi
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.SiegelFamilyZetaUnit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectDataDescendsFiniteTypeSubringStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothGrpSchemeDescendsToFgSubring
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPolarizedLevelTripleOfSubringLe

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings

namespace GlobalTheory.SiegBaseChange

open GlobalTheory.CechPic

theorem spMap_subtype_comp_inclusion {R : Type} [CommRing R] {R₁ R₂ : Subring R} (h : R₁ ≤ R₂) :
    spMap R₂.subtype ≫ spMap (Subring.inclusion h) = spMap R₁.subtype := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem pullbackTriple_of_le : ∀ (R : Type) [CommRing R] (R₁ R₂ : Subring R) (h : R₁ ≤ R₂) (g M : ℕ) (A : Over (Sp R)) [GrpObj A] (P : LB (A ⊗ A).left) (lv : Std g M → (𝟙_ (Over (Sp R)) ⟶ A)) (A₁ : Over (Sp R₁)) [GrpObj A₁] (P₁ : LB (A₁ ⊗ A₁).left) (lv₁ : Std g M → (𝟙_ (Over (Sp R₁)) ⟶ A₁)), IsAbelianScheme A₁ → SmoothOfRelativeDimension g A₁.hom → P.IsLB → P₁.IsLB → IsPullbackTriple A P lv A₁ P₁ lv₁ (spMap R₁.subtype) → ∃ (A₂ : Over (Sp R₂)) (_ : GrpObj A₂) (lv₂ : Std g M → (𝟙_ (Over (Sp R₂)) ⟶ A₂)) (π : A₂.left ⟶ A₁.left) (π₂ : (A₂ ⊗ A₂).left ⟶ (A₁ ⊗ A₁).left), IsAbelianScheme A₂ ∧ SmoothOfRelativeDimension g A₂.hom ∧ IsGrpPullback A₂ A₁ (spMap (Subring.inclusion h)) π ∧ Geo.Tor.IsSquare π π₂ ∧ IsPullbackTriple A P lv A₂ (P₁.pull π₂) lv₂ (spMap R₂.subtype) := by
  intro R _ R₁ R₂ h g M A _ P lv A₁ _ P₁ lv₁ hab hsm hP hP₁ H
  haveI := hab.comm
  obtain ⟨φ, φ₂, hφ, s₁, s₂, iso, hl⟩ := H
  have e := spMap_subtype_comp_inclusion h
  have pb₂ := Pdiv.PullbackComparison.isGrpPullback (spMap (Subring.inclusion h)) A₁
  have sq₂ := Pdiv.PullbackComparison.isSquare (spMap (Subring.inclusion h)) A₁
  have hw : φ ≫ A₁.hom = (A.hom ≫ spMap R₂.subtype) ≫ spMap (Subring.inclusion h) := by
    rw [hφ.1.w, Category.assoc, e]
  let ψ : A.left ⟶ ((Over.pullback (spMap (Subring.inclusion h))).obj A₁).left := pb₂.1.lift φ _ hw
  have hψ₁ : ψ ≫ Pdiv.PullbackComparison.pφ (spMap (Subring.inclusion h)) A₁ = φ := pb₂.1.lift_fst _ _ _
  have hψ₂ : ψ ≫ ((Over.pullback (spMap (Subring.inclusion h))).obj A₁).hom = A.hom ≫ spMap R₂.subtype :=
    pb₂.1.lift_snd _ _ _
  have hψ : IsGrpPullback A ((Over.pullback (spMap (Subring.inclusion h))).obj A₁) (spMap R₂.subtype) ψ :=
    pb₂.cancel (by rw [hψ₁, e]; exact hφ) hψ₂
  obtain ⟨ψ₂, sqψ⟩ := GlobalTheory.SiegDesc.exists_isSquare hψ₂
  have hc : ψ₂ ≫ Pdiv.PullbackComparison.pφ₂ (spMap (Subring.inclusion h)) A₁ = φ₂ :=
    GlobalTheory.SiegDesc.isSquare_comp hψ₁ sqψ sq₂ ⟨s₁, s₂⟩
  refine ⟨(Over.pullback (spMap (Subring.inclusion h))).obj A₁, inferInstance,
    fun a => GlobalTheory.SiegelPull.secPull pb₂ (lv₁ a), Pdiv.PullbackComparison.pφ _ A₁, Pdiv.PullbackComparison.pφ₂ _ A₁, ?_, ?_, pb₂, sq₂,
    ψ, ψ₂, hψ, sqψ.1, sqψ.2, ?_, fun a => ?_⟩
  · exact
      { comm := inferInstance
        smooth := by have := hab.smooth; show Smooth (pullback.snd _ _); infer_instance
        proper := by have := hab.proper; show IsProper (pullback.snd _ _); infer_instance
        geomConnected := by
          have := hab.geomConnected
          show GeometricallyConnected (pullback.snd _ _); infer_instance }
  · exact (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback pb₂.1 hsm
  · have hP₂ := pull_isLB hP₁ (Pdiv.PullbackComparison.pφ₂ (spMap (Subring.inclusion h)) A₁)
    refine (cls_eq_iff hP (pull_isLB hP₂ ψ₂)).1 ?_
    rw [(cls_eq_iff hP (pull_isLB hP₁ φ₂)).2 iso, cls_pull hP₂ ψ₂, cls_pull hP₁ _ hP₂, ← pull_comp, hc]
    rfl
  · apply pb₂.1.hom_ext
    · rw [Category.assoc, hψ₁, hl a, Category.assoc, GlobalTheory.SiegelPull.secPull_left, ← Category.assoc, e]
    · rw [Category.assoc, hψ₂, ← Category.assoc, Over.w (lv a), Category.assoc, Over.w]
      rfl

end GlobalTheory.SiegBaseChange
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPolarizedLevelTripleOfSubringLeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings

theorem _root_.GlobalTheory.T.pullbackPolarizedLevelTriple_of_subring_le : ∀ (R : Type) [CommRing R] (R₁ R₂ : Subring R) (h : R₁ ≤ R₂) (g M : ℕ) (A : Over (Sp R)) [GrpObj A] (P : LB (A ⊗ A).left) (lv : Std g M → (𝟙_ (Over (Sp R)) ⟶ A)) (A₁ : Over (Sp R₁)) [GrpObj A₁] (P₁ : LB (A₁ ⊗ A₁).left) (lv₁ : Std g M → (𝟙_ (Over (Sp R₁)) ⟶ A₁)), IsAbelianScheme A₁ → SmoothOfRelativeDimension g A₁.hom → P.IsLB → P₁.IsLB → IsPullbackTriple A P lv A₁ P₁ lv₁ (spMap R₁.subtype) → ∃ (A₂ : Over (Sp R₂)) (_ : GrpObj A₂) (lv₂ : Std g M → (𝟙_ (Over (Sp R₂)) ⟶ A₂)) (π : A₂.left ⟶ A₁.left) (π₂ : (A₂ ⊗ A₂).left ⟶ (A₁ ⊗ A₁).left), IsAbelianScheme A₂ ∧ SmoothOfRelativeDimension g A₂.hom ∧ IsGrpPullback A₂ A₁ (spMap (Subring.inclusion h)) π ∧ Geo.Tor.IsSquare π π₂ ∧ IsPullbackTriple A P lv A₂ (P₁.pull π₂) lv₂ (spMap R₂.subtype) := by
  first | exact @GlobalTheory.SiegBaseChange.pullbackTriple_of_le | exact GlobalTheory.SiegBaseChange.pullbackTriple_of_le | (intros; apply GlobalTheory.SiegBaseChange.pullbackTriple_of_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsEqOfSpMapSubtypeCompEq

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings

namespace GlobalTheory

theorem sections_eq_of_spMap_subtype_comp_eq : ∀ (R : Type) [CommRing R] (R₀ : Subring R) (X : Scheme.{0})
    (p : X ⟶ Sp R₀) [IsSeparated p] (x y : Sp R₀ ⟶ X), x ≫ p = y ≫ p →
    spMap R₀.subtype ≫ x = spMap R₀.subtype ≫ y → x = y := by
  intro R _ R₀ X p _ x y hp hR
  let l : Sp R₀ ⟶ pullback p p := pullback.lift x y hp
  let c : pullback (pullback.diagonal p) l ⟶ Sp R₀ := pullback.snd _ _
  haveI : IsClosedImmersion c := inferInstance
  have e1 : l ≫ pullback.fst p p = x := pullback.lift_fst _ _ _
  have e2 : l ≫ pullback.snd p p = y := pullback.lift_snd _ _ _
  have hc : c ≫ x = c ≫ y := by
    have h1 : c ≫ l ≫ pullback.fst p p = c ≫ l ≫ pullback.snd p p := by
      rw [← Category.assoc c l, ← Category.assoc c l]
      change (pullback.snd (pullback.diagonal p) l ≫ l) ≫ _ = (pullback.snd (pullback.diagonal p) l ≫ l) ≫ _
      rw [← pullback.condition, Category.assoc, Category.assoc,
        pullback.diagonal_fst, pullback.diagonal_snd]
    rwa [e1, e2] at h1
  let k : Sp R ⟶ pullback (pullback.diagonal p) l :=
    pullback.lift (spMap R₀.subtype ≫ x) (spMap R₀.subtype) (by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, pullback.diagonal_fst, Category.comp_id, Category.assoc, e1]
      · rw [Category.assoc, Category.assoc, pullback.diagonal_snd, Category.comp_id, Category.assoc, e2, hR])
  have hk : k ≫ c = spMap R₀.subtype := pullback.lift_snd _ _ _
  obtain ⟨hZ, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine c
  have hinj0 : Function.Injective (spMap R₀.subtype).appTop := by
    have e := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom R₀.subtype)
    have : (spMap R₀.subtype).appTop = (Scheme.ΓSpecIso (CommRingCat.of R₀)).hom ≫
        CommRingCat.ofHom R₀.subtype ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).inv := by
      rw [← Category.assoc, ← e]; simp
    rw [this]
    intro a b hab
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at hab
    have := (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm.injective hab
    exact (Scheme.ΓSpecIso (CommRingCat.of R₀)).commRingCatIsoToRingEquiv.injective (Subtype.val_injective this)
  have hinj : Function.Injective c.appTop := by
    rw [← hk, Scheme.Hom.comp_appTop] at hinj0
    simp only [CommRingCat.hom_comp, RingHom.coe_comp] at hinj0
    exact hinj0.of_comp
  haveI : IsIso c.appTop := (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hinj, hsurj⟩
  haveI : IsIso c :=
    (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms _) (arrowIsoSpecΓOfIsAffine c)).mpr
      (inferInstanceAs (IsIso (Spec.map c.appTop)))
  rw [← cancel_epi c]
  exact hc

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsEqOfSpMapSubtypeCompEqStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings

theorem _root_.GlobalTheory.T.eq_of_spMap_subtype_comp_eq_of_isSeparated : ∀ (R : Type) [CommRing R] (R₀ : Subring R) (X : Scheme.{0}) (p : X ⟶ Sp R₀) [IsSeparated p] (x y : Sp R₀ ⟶ X), x ≫ p = y ≫ p → spMap R₀.subtype ≫ x = spMap R₀.subtype ≫ y → x = y := by
  first | exact @GlobalTheory.sections_eq_of_spMap_subtype_comp_eq | exact GlobalTheory.sections_eq_of_spMap_subtype_comp_eq | (intros; apply GlobalTheory.sections_eq_of_spMap_subtype_comp_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.Data

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings

namespace GlobalTheory.SiegFGData

theorem data : ∀ (g n : ℕ), 3 ≤ n → Odd n → ∀ (R : Type) [CommRing R] (β : cycAway n →+* R) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → ∃ (R₀ : Subring R) (β₀ : cycAway n →+* R₀) (A₀ : Over (Sp R₀)) (_ : GrpObj A₀) (P₀ : LB (A₀ ⊗ A₀).left) (lv₀ : Std g n → (𝟙_ (Over (Sp R₀)) ⟶ A₀)), Algebra.FiniteType ℤ R₀ ∧ R₀.subtype.comp β₀ = β ∧ IsSymmetricPair g A₀ P₀ ∧ (∀ a b, lv₀ (a + b) = lv₀ a * lv₀ b) ∧ Out.RelAmple A₀ (diagPull A₀ P₀) ∧ IsPullbackTriple c.A c.P (lvOf c) A₀ P₀ lv₀ (spMap R₀.subtype) := by
  intro g n hn _ R _ β c hc
  have h0 : n ≠ 0 := by omega
  obtain ⟨R₁, β₁, A₁, _, P₁, lv₁, hfg, hβ, hA₁, hd₁, hP₁, htr⟩ := GlobalTheory.T.siegelObject_data_descends_finiteType_subring g n hn R β c
  have htr' := htr
  obtain ⟨φ, φ₂, hφ, sq₁, sq₂, iso, hl⟩ := htr
  have : IsNoetherianRing R₁ := Algebra.FiniteType.isNoetherianRing ℤ R₁
  have hsym : IsSymmetricPair g c.A c.P := isSymmetricPair (ζ := (cycBase h0).ζ) (by omega) (isUnit_natCast h0) c
  have hlev : IsLevel c.A (lvOf c) := isLevel_lvOf (ζ := (cycBase h0).ζ) c
  obtain ⟨hAb, hdim, hPlb, hr1, hr2, hsy⟩ := hsym
  obtain ⟨F₅, H₅⟩ := GlobalTheory.T.rigidSymmetricBundle_descends_to_subring_finset R R₁ c.A c.P A₁ P₁ φ φ₂ hA₁ hPlb hP₁ hφ ⟨sq₁, sq₂⟩ iso hr1 hr2 hsy
  obtain ⟨F₂, H₂⟩ := GlobalTheory.T.relAmple_diagonal_bundle_descends_subring R R₁ c.A c.P A₁ P₁ φ φ₂ hA₁ hPlb hP₁ hφ ⟨sq₁, sq₂⟩ iso hc.1
  classical
  let S : Subalgebra R₁ R := Algebra.adjoin R₁ ((F₅ ∪ F₂ : Finset R) : Set R)
  let R₂ : Subring R := S.toSubring
  have h12 : R₁ ≤ R₂ := fun x hx => S.algebraMap_mem ⟨x, hx⟩
  have hF : ((F₅ ∪ F₂ : Finset R) : Set R) ⊆ R₂ := Algebra.subset_adjoin
  have hfg₂ : Algebra.FiniteType ℤ R₂ := GlobalTheory.SpreadGroup.finiteType_of_fg hfg (Subalgebra.fg_adjoin_finset _)
  obtain ⟨A₂, _, lv₂, π, π₂, hA₂, hd₂, hπ, sqπ, htr₂⟩ :=
    GlobalTheory.T.pullbackPolarizedLevelTriple_of_subring_le R R₁ R₂ h12 g n c.A c.P (lvOf c) A₁ P₁ lv₁ hA₁ hd₁ hPlb hP₁ htr'
  obtain ⟨t1, t2, t3⟩ := H₅ R₂ h12 (fun x hx => hF (by simp [hx])) A₂ π π₂ hπ sqπ
  have am := H₂ R₂ h12 (fun x hx => hF (by simp [hx])) A₂ π π₂ hπ sqπ
  refine ⟨R₂, (Subring.inclusion h12).comp β₁, A₂, inferInstance, P₁.pull π₂, lv₂, hfg₂, ?_,
    ⟨hA₂, hd₂, pull_isLB hP₁ _, t1, t2, t3⟩, ?_, am, htr₂⟩
  · rw [← hβ]
    rfl
  · intro a b
    obtain ⟨ψ, ψ₂, hψ, -, -, -, hl₂⟩ := htr₂
    have : IsSeparated A₂.hom := by have := hA₂.proper; infer_instance
    refine Over.OverMorphism.ext (GlobalTheory.T.eq_of_spMap_subtype_comp_eq_of_isSeparated R R₂ A₂.left A₂.hom _ _ ?_ ?_)
    · exact (Over.w (lv₂ (a + b))).trans (Over.w (lv₂ a * lv₂ b)).symm
    · let f := spMap R₂.subtype
      let u : Over.mk ((𝟙_ (Over (Sp R))).hom ≫ f) ⟶ 𝟙_ (Over (Sp R₂)) := toUnit _
      have hu : u.left = (𝟙_ (Over (Sp R))).hom ≫ f := Over.toUnit_left
      have hid : (𝟙_ (Over (Sp R))).hom = 𝟙 _ := rfl
      have m := hψ.2 (𝟙_ (Over (Sp R))) (lvOf c a) (lvOf c b) (u ≫ lv₂ a) (u ≫ lv₂ b)
        (by rw [Over.comp_left, hu, hid, Category.id_comp]; exact (hl₂ a).symm)
        (by rw [Over.comp_left, hu, hid, Category.id_comp]; exact (hl₂ b).symm)
      rw [← MonObj.comp_mul, Over.comp_left, hu, hid, Category.id_comp, ← hlev.1] at m
      exact (hl₂ (a + b)).symm.trans m.symm

end GlobalTheory.SiegFGData
end
end
