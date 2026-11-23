module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsIsoSpMapDnFst
public import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
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
import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsIsoSpMapDnFst
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRelAmpleOfIsProjBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIsProjectiveOverRingByChartsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDualRepresentativeOfRelAmpleNoetherianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeGrpPullbackIff
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionOfMonoOfSmoothOfRelativeDimension
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonoClassifyingOfInjectiveFamily

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon

theorem fam_ev_param {S : Scheme.{0}} {A T Y : Over S} [GrpObj A] {N : LB (A ⊗ T).left} (hN : Fam A N)
    (y : Y ⟶ T) : Fam A (ev N (fst A Y) (snd A Y ≫ y)) := by
  have h : (ev N (fst A Y) (snd A Y ≫ y)).IsLB := pull_isLB hN.isLB _
  refine ⟨h, (isAdditive_iff h).2 fun Z a a' t ↦ ?_⟩
  simp only [evc_ev hN.isLB, lift_fst, lift_snd_assoc]
  exact (isAdditive_iff hN.isLB).1 hN.add Z a a' (t ≫ y)

theorem classify_mono : ∀ (S : Scheme.{0}) (A B S' U : Over S) [GrpObj A] (b : B ⟶ S') (P : LB (A ⊗ B).left)
    (M : LB (A ⊗ U).left), Rep A b P → Fam A M → Inj A M →
    ∃ φ : U ⊗ S' ⟶ B, φ ≫ b = snd U S' ∧ Same A M P (fst U S') φ ∧ Mono φ.left := by
  intro S A B S' U _ b P M hP hM hI
  obtain ⟨φ, ⟨hb, hN⟩, -⟩ := hP.univ (U ⊗ S') (snd U S') _ (fam_ev_param hM (fst U S'))
  have hS : Same A M P (fst U S') φ := hN
  refine ⟨φ, hb, hS, ?_⟩
  have hm : Mono φ := ⟨fun {Y} a a' e ↦ by
    have e1 : Same A M P (a ≫ fst U S') (a ≫ φ) := by
      rw [same_iff hM.isLB hP.fam.isLB] at hS ⊢
      have := congrArg (CechPic.pull (lift (fst A Y) (snd A Y ≫ a)).left) hS
      simpa only [pull_evc, lift_fst, lift_snd_assoc, Category.assoc] using this
    have e2 : Same A M P (a' ≫ fst U S') (a' ≫ φ) := by
      rw [same_iff hM.isLB hP.fam.isLB] at hS ⊢
      have := congrArg (CechPic.pull (lift (fst A Y) (snd A Y ≫ a')).left) hS
      simpa only [pull_evc, lift_fst, lift_snd_assoc, Category.assoc] using this
    have e3 : Same A M M (a ≫ fst U S') (a' ≫ fst U S') := by
      rw [same_iff hM.isLB hP.fam.isLB] at e1 e2
      rw [same_iff hM.isLB hM.isLB, e1, e2, e]
    have ef := hI Y _ _ e3
    have es : a ≫ snd U S' = a' ≫ snd U S' := by rw [← hb, reassoc_of% e]
    exact CartesianMonoidalCategory.hom_ext _ _ ef es⟩
  exact Over.mono_left_of_mono φ
end DualCon
end GlobalTheory
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonoClassifyingOfInjectiveFamilyStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_mono_classifying_of_injective_family : ∀ (S : Scheme.{0}) (A B S' U : Over S) [GrpObj A] (b : B ⟶ S') (P : LB (A ⊗ B).left) (M : LB (A ⊗ U).left), Rep A b P → Fam A M → Inj A M → ∃ φ : U ⊗ S' ⟶ B, φ ≫ b = snd U S' ∧ Same A M P (fst U S') φ ∧ Mono φ.left := by
  first | exact @GlobalTheory.DualCon.classify_mono | exact GlobalTheory.DualCon.classify_mono | (intros; apply GlobalTheory.DualCon.classify_mono <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeFieldPoint

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.DualCon.FieldRep

theorem hasRep_field : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ g : ℕ,
    SmoothOfRelativeDimension g A.hom → ∀ (K : Type) [Field K] (s : Sp K ⟶ S), HasRep A g (Over.mk s) := by
  intro S A _ hA g hg K _ s
  have hA' : IsAbelianScheme ((Over.pullback s).obj A) := GlobalTheory.isAbelianScheme_pullback_obj s A hA
  have hg' : SmoothOfRelativeDimension g ((Over.pullback s).obj A).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hg
  obtain ⟨L, hL, hamp⟩ := GlobalTheory.ProjFinite.exists_relAmple_of_isProjBy (GlobalTheory.T.abelianVariety_isProjectiveOverRingByCharts K _ hA')
  have hAF : HasRepAF ((Over.pullback s).obj A) g (𝟙_ _) := GlobalTheory.T.hasDualRepresentative_of_relAmple_noetherian K _ g hA' hg' L hL hamp
  have h := (GlobalTheory.DualCon.hasRep_baseChange_iff S (Sp K) s A ((Over.pullback s).obj A) (pullback.fst A.hom s)
    (isGrpPullback_pullback A s) g (𝟙_ _)).1.1
  obtain ⟨B, b, P, hR, hG, -⟩ := hAF
  have h2 := h ⟨B, b, P, hR, hG⟩
  have e : (𝟙_ (Over (Sp K))).hom ≫ s = s := Category.id_comp s
  rw [e] at h2
  exact h2

end GlobalTheory.DualCon.FieldRep
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeFieldPointStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.hasProperSmoothDualRepresentative_fieldPoint : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ g : ℕ, SmoothOfRelativeDimension g A.hom → ∀ (K : Type) [Field K] (s : Sp K ⟶ S), HasRep A g (Over.mk s) := by
  first | exact @GlobalTheory.DualCon.FieldRep.hasRep_field | exact GlobalTheory.DualCon.FieldRep.hasRep_field | (intros; apply GlobalTheory.DualCon.FieldRep.hasRep_field <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionOfMonoOfSmoothOfRelativeDimensionStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isOpenImmersion_of_mono_of_smoothOfRelativeDimension' : ∀ (X Y Z : Scheme.{0}) (f : X ⟶ Y) (p : Y ⟶ Z) (g : ℕ), SmoothOfRelativeDimension g p → SmoothOfRelativeDimension g (f ≫ p) → Mono f → IsOpenImmersion f := by
  first | exact @GlobalTheory.isOpenImmersion_of_mono_of_smoothOfRelativeDimension | exact GlobalTheory.isOpenImmersion_of_mono_of_smoothOfRelativeDimension | (intros; apply GlobalTheory.isOpenImmersion_of_mono_of_smoothOfRelativeDimension <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenImmersionClassifyingFamilyChart

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.RepChart

theorem repChart : ∀ (S : Scheme.{0}) (A B S' U : Over S) [GrpObj A] (b : B ⟶ S') (P : LB (A ⊗ B).left) (M : LB (A ⊗ U).left), Rep A b P → Fam A M → ∀ φ : U ⊗ S' ⟶ B, φ ≫ b = snd U S' → Same A M P (fst U S') φ → IsOpenImmersion φ.left → ∀ (T : Over S) (_ : T ⟶ S') (N : LB (A ⊗ T).left), Fam A N → ChartAt A M N := by
  intro S A B S' U _ b P M hP hM φ hφb hsame hopen T t N hN
  have hP' := hP.fam.isLB
  have hM' := hM.isLB
  have hN' := hN.isLB
  obtain ⟨x, ⟨hxb, hxN⟩, -⟩ := hP.univ T t N hN
  have ex : cls N hN' = evc hP' (fst A T) (snd A T ≫ x) := (cls_eq_iff hN' (pull_isLB hP' _)).2 hxN
  have eφ : evc hM' (fst A (U ⊗ S')) (snd A (U ⊗ S') ≫ fst U S') = evc hP' (fst A (U ⊗ S')) (snd A (U ⊗ S') ≫ φ) :=
    (same_iff hM' hP' _ _).1 hsame
  have eY : ∀ (Y : Over S) (y : Y ⟶ T), evc hN' (fst A Y) (snd A Y ≫ y) = evc hP' (fst A Y) (snd A Y ≫ y ≫ x) := by
    intro Y y
    have e := congrArg (CechPic.pull (lift (fst A Y) (snd A Y ≫ y)).left) ex
    rw [pull_evc, lift_fst, lift_snd_assoc] at e
    exact e
  have eV : ∀ (Y : Over S) (v : Y ⟶ U ⊗ S'), evc hM' (fst A Y) (snd A Y ≫ v ≫ fst U S') =
      evc hP' (fst A Y) (snd A Y ≫ v ≫ φ) := by
    intro Y v
    have e := congrArg (CechPic.pull (lift (fst A Y) (snd A Y ≫ v)).left) eφ
    rw [pull_evc, pull_evc, lift_fst, lift_snd_assoc, lift_snd_assoc] at e
    exact e
  have uniq : ∀ (Y : Over S) (y : Y ⟶ T) (x₁ x₂ : Y ⟶ B), x₁ ≫ b = y ≫ t → x₂ ≫ b = y ≫ t →
      evc hP' (fst A Y) (snd A Y ≫ x₁) = evc hN' (fst A Y) (snd A Y ≫ y) →
      evc hP' (fst A Y) (snd A Y ≫ x₂) = evc hN' (fst A Y) (snd A Y ≫ y) → x₁ = x₂ := by
    intro Y y x₁ x₂ h₁ h₂ e₁ e₂
    have hL : (ev N (fst A Y) (snd A Y ≫ y)).IsLB := pull_isLB hN' _
    have hF : Fam A (ev N (fst A Y) (snd A Y ≫ y)) := by
      refine ⟨hL, (isAdditive_iff hL).2 fun Z a a' z ↦ ?_⟩
      simp only [evc_ev hN', lift_fst, lift_snd_assoc]
      exact (isAdditive_iff hN').1 hN.add Z a a' (z ≫ y)
    refine (hP.univ Y (y ≫ t) _ hF).unique ⟨h₁, (cls_eq_iff hL (pull_isLB hP' _)).1 ?_⟩
      ⟨h₂, (cls_eq_iff hL (pull_isLB hP' _)).1 ?_⟩
    · rw [cls_ev hN', cls_ev hP', e₁]
    · rw [cls_ev hN', cls_ev hP', e₂]
  refine ⟨x.left ⁻¹ᵁ φ.left.opensRange, fun Y y ↦ ⟨?_, ?_⟩⟩
  · rintro ⟨u, hu⟩
    rw [same_iff hN' hM'] at hu
    let v : Y ⟶ U ⊗ S' := lift u (y ≫ t)
    have hvx : v ≫ φ = y ≫ x := by
      refine uniq Y y _ _ ?_ ?_ ?_ (by rw [eY])
      · rw [Category.assoc, hφb, lift_snd]
      · rw [Category.assoc, hxb]
      · rw [← eV, lift_fst, hu]
    intro z
    have e := congrArg (fun q : Y ⟶ B ↦ q.left z) hvx
    simp only [Over.comp_left, Scheme.Hom.comp_apply] at e
    simp only [Scheme.Hom.mem_preimage, Scheme.Hom.mem_opensRange]
    exact ⟨_, e⟩
  · intro h
    have hr : Set.range (y.left ≫ x.left) ⊆ Set.range φ.left := by
      rintro _ ⟨z, rfl⟩
      have := h z
      simp only [Scheme.Hom.mem_preimage, Scheme.Hom.mem_opensRange] at this
      simpa [Scheme.Hom.comp_apply] using this
    let l := IsOpenImmersion.lift φ.left (y.left ≫ x.left) hr
    have hl : l ≫ φ.left = y.left ≫ x.left := IsOpenImmersion.lift_fac _ _ _
    let v : Y ⟶ U ⊗ S' := Over.homMk l (by
      rw [← Over.w φ, ← Category.assoc, hl, Category.assoc, Over.w x, Over.w y])
    have hvx : v ≫ φ = y ≫ x := Over.OverMorphism.ext (by simpa [v] using hl)
    refine ⟨v ≫ fst U S', (same_iff hN' hM' _ _).2 ?_⟩
    rw [eV, hvx, eY]

end GlobalTheory.RepChart
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenImmersionClassifyingFamilyChartStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.openImmersion_classifying_family_chart : ∀ (S : Scheme.{0}) (A B S' U : Over S) [GrpObj A] (b : B ⟶ S') (P : LB (A ⊗ B).left) (M : LB (A ⊗ U).left), Rep A b P → Fam A M → ∀ φ : U ⊗ S' ⟶ B, φ ≫ b = snd U S' → Same A M P (fst U S') φ → IsOpenImmersion φ.left → ∀ (T : Over S) (_ : T ⟶ S') (N : LB (A ⊗ T).left), Fam A N → ChartAt A M N := by
  first | exact @GlobalTheory.RepChart.repChart | exact GlobalTheory.RepChart.repChart | (intros; apply GlobalTheory.RepChart.repChart <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FieldChartOfInj

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualOpen

theorem fieldChart_of_inj : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ g : ℕ,
    SmoothOfRelativeDimension g A.hom → ∀ (U : Over S) (M : LB (A ⊗ U).left), SmoothOfRelativeDimension g U.hom →
    Fam A M → Inj A M → FieldChart A M := by
  intro S A _ hA g hg U M hU hM hI K _ _ s T t N hN
  obtain ⟨B, b, P, hP, hgood⟩ := GlobalTheory.T.hasProperSmoothDualRepresentative_fieldPoint S A hA g hg K s
  obtain ⟨φ, hφb, hφS, hφm⟩ := GlobalTheory.T.exists_mono_classifying_of_injective_family S A B (Over.mk s) U b P M hP hM hI
  have hpb : IsPullback (fst U (Over.mk s)).left (snd U (Over.mk s)).left U.hom (Over.mk s).hom :=
    .of_hasPullback _ _
  have hsnd : SmoothOfRelativeDimension g (snd U (Over.mk s)).left :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hpb hU
  have hcomp : SmoothOfRelativeDimension g (φ.left ≫ b.left) := by
    rw [← Over.comp_left, hφb]; exact hsnd
  have hopen : IsOpenImmersion φ.left :=
    GlobalTheory.T.isOpenImmersion_of_mono_of_smoothOfRelativeDimension' _ _ _ φ.left b.left g hgood.smooth hcomp hφm
  exact GlobalTheory.T.openImmersion_classifying_family_chart S A B (Over.mk s) U b P M hP hM φ hφb hφS hopen T t N hN

end GlobalTheory.DualOpen
end
end
end
