module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftsAlong
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FieldChartOfInj
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsIsoSpMapDnFst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveLineBundleFamilyCalculusRules
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveLineBundleFamilyCalculusRulesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleFamilyAgreeingSmallExtensionTang
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsIsoSpMapDnFst
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonSpectrumDualNumber

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftsAlongPrincipalSmallExtension

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualOpen

theorem liftsAlong_span_singleton : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (U : Over (Sp R)) (M : LB (A ⊗ U).left), Fam A M → SmallLift A M → ∀ (B : Type) [CommRing B] [IsLocalRing B] (t : B), t ∈ IsLocalRing.maximalIdeal B → IsLocalRing.maximalIdeal B * Ideal.span {t} = ⊥ → LiftsAlong A M B (Ideal.span {t}) := by
  intro R _ A _ U M hM hSL B _ _ t ht hmt T N hN y u₀ h₀
  have calc5 := ((GlobalTheory.FamCalc.famCalc (Sp R) A).2.2.2.2)
  have hkill : ∀ a ∈ IsLocalRing.maximalIdeal B, a * t = 0 := fun a ha ↦ by
    have : a * t ∈ IsLocalRing.maximalIdeal B * Ideal.span {t} :=
      Ideal.mul_mem_mul ha (Ideal.mem_span_singleton_self t)
    rwa [hmt, Ideal.mem_bot] at this
  let Y : Over (Sp R) := Over.mk (y ≫ T.hom)
  let yy : Y ⟶ T := Over.homMk y rfl
  have hN' : Fam A (ev N (fst A Y) (snd A Y ≫ yy)) := (GlobalTheory.FamCalc.famCalc (Sp R) A).1 T Y N yy hN
  have key : ptMap (y ≫ T.hom) (Ideal.Quotient.mk (Ideal.span {t})) ≫ yy =
      (Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {t}))) ≫ y) (by simp) :
        Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {t}))) ≫ y ≫ T.hom) ⟶ T) := by
    ext1; rfl
  have h₁ : Same A (ev N (fst A Y) (snd A Y ≫ yy)) M (ptMap (y ≫ T.hom) (Ideal.Quotient.mk (Ideal.span {t}))) u₀ := by
    rw [calc5 T U Y _ N M yy _ u₀ hN.isLB hM.isLB, key]
    exact h₀
  obtain ⟨u, hu⟩ := hSL B t ht hkill (y ≫ T.hom) _ hN' u₀ h₁
  refine ⟨u, ?_⟩
  have := (calc5 T U Y Y N M yy (𝟙 _) u hN.isLB hM.isLB).1 hu
  rwa [Category.id_comp] at this

end GlobalTheory.DualOpen
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftsAlongPrincipalSmallExtensionStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.liftsAlong_principal_small_extension : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (U : Over (Sp R)) (M : LB (A ⊗ U).left), Fam A M → SmallLift A M → ∀ (B : Type) [CommRing B] [IsLocalRing B] (t : B), t ∈ IsLocalRing.maximalIdeal B → IsLocalRing.maximalIdeal B * Ideal.span {t} = ⊥ → LiftsAlong A M B (Ideal.span {t}) := by
  first | exact @GlobalTheory.DualOpen.liftsAlong_span_singleton | exact GlobalTheory.DualOpen.liftsAlong_span_singleton | (intros; apply GlobalTheory.DualOpen.liftsAlong_span_singleton <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleFamilyAgreeingSmallExtensionTangStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_lineBundleFamily_agreeing_smallExtension_tangent : ∀ (S : Scheme.{0}) [IsAffine S] (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (U : Over S) (M : LB (A ⊗ U).left), Fam A M → Inj A M → TanLift A M → ∀ (C : Type) [CommRing C] [IsLocalRing C] (e : C), e ∈ IsLocalRing.maximalIdeal C → (∀ a ∈ IsLocalRing.maximalIdeal C, a * e = 0) → e ≠ 0 → ∀ (s : Sp C ⟶ S) (N : LB (A ⊗ Over.mk s).left), Fam A N → ∀ u' : Over.mk s ⟶ U, Same A N M (ptMap s (Ideal.Quotient.mk (Ideal.span {e}))) (ptMap s (Ideal.Quotient.mk (Ideal.span {e})) ≫ u') → ∃ u : Over.mk s ⟶ U, Same A N M (𝟙 _) u := by
  first | exact @GlobalTheory.DualOpen.exists_same_of_smallExt | exact GlobalTheory.DualOpen.exists_same_of_smallExt | (intros; apply GlobalTheory.DualOpen.exists_same_of_smallExt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothExistsPointLiftSquareZeroLocalRing

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SmoothPtLift

set_option autoImplicit false

theorem exists_lift (U S : Scheme.{0}) (p : U ⟶ S) [Smooth p] (C : Type) [CommRing C] [IsLocalRing C]
    (I : Ideal C) (hI : I ^ 2 = ⊥) (s : Sp C ⟶ S) (u₀ : Sp (C ⧸ I) ⟶ U)
    (hw : u₀ ≫ p = spMap (Ideal.Quotient.mk I) ≫ s) :
    ∃ u : Sp C ⟶ U, spMap (Ideal.Quotient.mk I) ≫ u = u₀ ∧ u ≫ p = s := by
  have hItop : I ≠ ⊤ := by
    rintro rfl
    have h1 : (1 : C) ∈ (⊤ : Ideal C) ^ 2 := by rw [Ideal.top_pow]; exact Submodule.mem_top
    rw [hI, Ideal.mem_bot] at h1
    exact one_ne_zero h1
  haveI : Nontrivial (C ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hItop
  haveI : IsLocalRing (C ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (Ideal.Quotient.mk I) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  let t₀ : Sp (C ⧸ I) := IsLocalRing.closedPoint (C ⧸ I)
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (p (u₀ t₀))) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
    U.isBasis_affineOpens.exists_subset_of_mem_open (a := u₀ t₀) hxW (W.2.preimage p.continuous)
  haveI : IsOpenImmersion hW.fromSpec := hW.isOpenImmersion_fromSpec
  haveI : IsOpenImmersion hV.fromSpec := hV.isOpenImmersion_fromSpec
  have hmap : (spMap (Ideal.Quotient.mk I)) t₀ = IsLocalRing.closedPoint C :=
    IsLocalRing.comap_closedPoint (Ideal.Quotient.mk I)
  have hsW : Set.range s ⊆ Set.range hW.fromSpec := by
    rw [hW.range_fromSpec]
    rintro _ ⟨z, rfl⟩
    have h1 : s (IsLocalRing.closedPoint C) ∈ W := by
      rw [← hmap, ← Scheme.Hom.comp_apply, ← hw, Scheme.Hom.comp_apply]
      exact hxW
    exact ((IsLocalRing.specializes_closedPoint z).map s.continuous).mem_open W.2 h1
  have hu₀V : Set.range u₀ ⊆ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]
    rintro _ ⟨z, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint z).map u₀.continuous).mem_open V.2 hxV
  obtain ⟨a, ha⟩ : ∃ a, Spec.map a = IsOpenImmersion.lift hW.fromSpec s hsW := ⟨_, Spec.map_preimage _⟩
  obtain ⟨b₀, hb₀⟩ : ∃ b, Spec.map b = IsOpenImmersion.lift hV.fromSpec u₀ hu₀V :=
    ⟨_, Spec.map_preimage _⟩
  have key : p.appLE W V hVW ≫ b₀ = a ≫ CommRingCat.ofHom (Ideal.Quotient.mk I) := by
    apply Spec.map_injective
    rw [← cancel_mono hW.fromSpec, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
      IsAffineOpen.SpecMap_appLE_fromSpec p hW hV hVW, hb₀, ha, IsOpenImmersion.lift_fac_assoc,
      IsOpenImmersion.lift_fac, hw]
  have hsm := p.smooth_appLE hW hV hVW
  algebraize [(p.appLE W V hVW).hom, a.hom]
  let g : Γ(U, V) →ₐ[Γ(S, W)] C ⧸ I :=
    { b₀.hom with
      commutes' := fun r => by
        have := congrArg (fun f => f.hom r) key
        exact this }
  let b := Algebra.FormallySmooth.lift I ⟨2, hI⟩ g
  refine ⟨Spec.map (CommRingCat.ofHom b.toRingHom) ≫ hV.fromSpec, ?_, ?_⟩
  · have e : CommRingCat.ofHom b.toRingHom ≫ CommRingCat.ofHom (Ideal.Quotient.mk I) = b₀ := by
      ext x
      exact Algebra.FormallySmooth.mk_lift I ⟨2, hI⟩ g x
    rw [← Category.assoc, ← Spec.map_comp, e, hb₀, IsOpenImmersion.lift_fac]
  · have e : p.appLE W V hVW ≫ CommRingCat.ofHom b.toRingHom = a := by
      ext r
      exact b.commutes r
    rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec p hW hV hVW, ← Category.assoc,
      ← Spec.map_comp, e, ha, IsOpenImmersion.lift_fac]

end GlobalTheory.SmoothPtLift
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothExistsPointLiftSquareZeroLocalRingStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.smooth_exists_point_lift_squareZero_localRing : ∀ (U S : Scheme.{0}) (p : U ⟶ S) [Smooth p] (C : Type) [CommRing C] [IsLocalRing C] (I : Ideal C), I ^ 2 = ⊥ → ∀ (s : Sp C ⟶ S) (u₀ : Sp (C ⧸ I) ⟶ U), u₀ ≫ p = spMap (Ideal.Quotient.mk I) ≫ s → ∃ u : Sp C ⟶ U, spMap (Ideal.Quotient.mk I) ≫ u = u₀ ∧ u ≫ p = s := by
  first | exact @GlobalTheory.SmoothPtLift.exists_lift | exact GlobalTheory.SmoothPtLift.exists_lift | (intros; apply GlobalTheory.SmoothPtLift.exists_lift <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftsAlongSmallExtensionOfDualNumberLifting

section

@[expose] public section

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualOpen

theorem smallLift_of_tanLift : ∀ (S : Scheme.{0}) [IsAffine S] (A : Over S) [GrpObj A], IsAbelianScheme A →
    ∀ (U : Over S) [Smooth U.hom] (M : LB (A ⊗ U).left), Fam A M → Inj A M → TanLift A M → SmallLift A M := by
  intro S _ A _ hA U _ M hM hI hT C _ _ e he hk s N hN u₀ h
  have hsq : (Ideal.span {e}) ^ 2 = ⊥ := by
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_eq_bot, sq]
    exact hk e he
  obtain ⟨v, hv, hp⟩ := GlobalTheory.T.smooth_exists_point_lift_squareZero_localRing U.left S U.hom C (Ideal.span {e}) hsq s u₀.left (Over.w u₀)
  let u' : Over.mk s ⟶ U := Over.homMk v hp
  have hu : u₀ = ptMap s (Ideal.Quotient.mk (Ideal.span {e})) ≫ u' := by
    ext1
    exact hv.symm
  by_cases h0 : e = 0
  · have hb : Function.Bijective (Ideal.Quotient.mk (Ideal.span {e})) := by
      refine ⟨?_, Ideal.Quotient.mk_surjective⟩
      rw [RingHom.injective_iff_ker_eq_bot, Ideal.mk_ker, Ideal.span_singleton_eq_bot]
      exact h0
    have : IsIso (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {e}))) :=
      (RingEquiv.ofBijective _ hb).toCommRingCatIso.isIso_hom
    have : IsIso (ptMap s (Ideal.Quotient.mk (Ideal.span {e}))).left :=
      inferInstanceAs (IsIso (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {e})))))
    have : IsIso ((Over.forget S).map (ptMap s (Ideal.Quotient.mk (Ideal.span {e})))) := this
    have : IsIso (ptMap s (Ideal.Quotient.mk (Ideal.span {e}))) := isIso_of_reflects_iso _ (Over.forget S)
    have h' := (GlobalTheory.T.additiveLineBundleFamily_calculus_rules S A).2.2.2.1 _ _ _ _ N M _ _ (inv (ptMap s (Ideal.Quotient.mk (Ideal.span {e}))))
      hN.isLB hM.isLB h
    rw [IsIso.inv_hom_id] at h'
    exact ⟨_, h'⟩
  · exact GlobalTheory.T.exists_lineBundleFamily_agreeing_smallExtension_tangent S A hA U M hM hI hT C e he hk h0 s N hN u' (hu ▸ h)

end GlobalTheory.DualOpen
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftsAlongSmallExtensionOfDualNumberLiftingStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.liftsAlong_smallExtension_of_dualNumber_lifting : ∀ (S : Scheme.{0}) [IsAffine S] (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (U : Over S) [Smooth U.hom] (M : LB (A ⊗ U).left), Fam A M → Inj A M → TanLift A M → SmallLift A M := by
  first | exact @GlobalTheory.DualOpen.smallLift_of_tanLift | exact GlobalTheory.DualOpen.smallLift_of_tanLift | (intros; apply GlobalTheory.DualOpen.smallLift_of_tanLift <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftsAlongOfSmoothInj

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualOpen

theorem liftsAlong_of_smooth_inj : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (U : Over (Sp R)) (M : LB (A ⊗ U).left), SmoothOfRelativeDimension g U.hom → Fam A M → Inj A M → ∀ (B : Type) [CommRing B] [IsLocalRing B] (t : B), t ∈ IsLocalRing.maximalIdeal B → IsLocalRing.maximalIdeal B * Ideal.span {t} = ⊥ → LiftsAlong A M B (Ideal.span {t}) := by
  intro R _ A _ g hA hg U M hU hM hI B _ _ t ht hsq
  have : Smooth U.hom := hU.smooth
  have : LocallyOfFiniteType U.hom := inferInstance
  have hF : FieldChart A M := fieldChart_of_inj _ A hA g hg U M hU hM hI
  have hT : TanLift A M := tanLift_of_fieldChart _ A hA U M hM hI hF
  have hS : SmallLift A M := GlobalTheory.T.liftsAlong_smallExtension_of_dualNumber_lifting _ A hA U M hM hI hT
  exact GlobalTheory.T.liftsAlong_principal_small_extension R A U M hM hS B t ht hsq

end GlobalTheory.DualOpen
end
end
end
