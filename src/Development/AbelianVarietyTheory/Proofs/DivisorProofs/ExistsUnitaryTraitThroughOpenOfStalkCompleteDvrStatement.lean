module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitModuliOfStalkCompleteDVR
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTraitThroughModuliGenericPoint
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUTraitOfStalkDvr

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem GlobalTheory.UPoinc.exists_uTrait_of_stalk_dvr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [CharZero Ω] (M : RatModel o' Ω) (y₀ : Sp Ω ⟶ Xo.XF c) (x : M.Z) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V], IsAdicComplete (maximalIdeal V) V → ∀ θ : M.Z.presheaf.stalk x →+* V, Function.Injective θ → ∃ (T : UTrait Xo c) (f : V →+* T.V) (γ : Ω →+* FractionRing T.V), Function.Injective f ∧ IsLocalHom f ∧ (∀ a, γ (M.stalkHom x a) = algebraMap T.V (FractionRing T.V) (f (θ a))) ∧ jK T.V ≫ spMap (f.comp θ) ≫ M.Z.fromSpecStalk x = spMap γ ≫ M.pt ∧ T.y = spMap γ ≫ y₀ := by
  intro E _ _ _ H Dw l Xo c o' Ω _ _ _ _ M y₀ x V _ _ _ hcomp θ hθ
  haveI : CharZero (M.Z.presheaf.stalk x) := (M.stalkHom x).charZero
  haveI : CharZero V := charZero_of_injective_ringHom hθ
  have hB : GlobalTheory.Mum.Base V := ⟨⟨inferInstance, inferInstance, inferInstance, hcomp⟩, inferInstance⟩
  let θ' : M.O x →+* FractionRing V :=
    ((algebraMap V (FractionRing V)).comp θ).comp (M.stalkEquiv x).symm.toRingHom
  have hθ' : Function.Injective θ' :=
    (IsFractionRing.injective V (FractionRing V)).comp (hθ.comp (M.stalkEquiv x).symm.injective)
  let γ₀ : Ω →+* FractionRing V := IsFractionRing.lift (A := M.O x) (K := Ω) hθ'
  have hγ₀ : ∀ a, γ₀ (M.stalkHom x a) = algebraMap V (FractionRing V) (θ a) := by
    intro a
    have h := IsFractionRing.lift_algebraMap (A := M.O x) (K := Ω) hθ' (M.stalkEquiv x a)
    rw [← RatModel.coe_stalkEquiv]
    refine h.trans ?_
    simp [θ']
  obtain ⟨T, f, fK, hfi, hfl, -, hc, hy⟩ :=
    GlobalTheory.UTraitExt.uTraitExtSt E H Dw l Xo c V hB inferInstance (spMap γ₀ ≫ y₀)
  refine ⟨T, f, fK.comp γ₀, hfi, hfl, ?_, ?_, ?_⟩
  · intro a
    rw [RingHom.comp_apply, hγ₀, hc]
  · have e : (algebraMap T.V (FractionRing T.V)).comp (f.comp θ) = (fK.comp γ₀).comp (M.stalkHom x) := by
      ext a
      simp only [RingHom.comp_apply, hγ₀, hc]
    rw [← GlobalTheory.Poinc.GenTrait.spMap_stalkHom_fromSpecStalk M x, ← Category.assoc, Formalism.L2.Pj.spMap_comp', e,
      ← Formalism.L2.Pj.spMap_comp', Category.assoc]
  · rw [hy, ← Category.assoc, Formalism.L2.Pj.spMap_comp']
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTraitThroughOpenOfStalkCompleteDvr

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

theorem GlobalTheory.UPoinc.exists_uTrait_through_open_of_stalk_dvr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE) (πY : Y.Z ⟶ X₁.M.Z), X₁.S.admitted Y U₀ → X₁.S.IsEE Y U₀ EE → X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY → ∀ (x : Y.Z) (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CharZero A], IsAdicComplete (maximalIdeal A) A → ∀ θ : Y.Z.presheaf.stalk x →+* A, Function.Injective θ → IsLocalHom θ → ∃ (T : UTrait Xo c) (f : A →+* T.V), Function.Injective f ∧ IsLocalHom f ∧ (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ (spMap (f.comp θ) ≫ Y.Z.fromSpecStalk x) ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) ∧ T.y ≫ C.i = jK T.V ≫ (spMap (f.comp θ) ≫ Y.Z.fromSpecStalk x) ≫ πY ≫ X₁.π := by
  intro E _ _ _ H Dw _ l Xo c C X₁ Y U₀ EE out πY hAdm _ hHom x A _ _ _ _ hcomp θ hθ _
  haveI : CharZero X₁.Ω₁ := X₁.ar.char
  obtain ⟨T, f, γ, hfi, hfl, -, hpt, hy⟩ :=
    GlobalTheory.UPoinc.exists_uTrait_of_stalk_dvr E H Dw l Xo c X₁.o₁ X₁.Ω₁ Y X₁.uΩ x A hcomp θ hθ
  have hsub : Set.range Y.pt ⊆ Set.range U₀.ι := by
    rw [Y.gen, Scheme.Opens.range_ι, Set.singleton_subset_iff]
    exact (genericPoint_spec Y.Z).mem_open_set_iff U₀.isOpen |>.2 (by simpa using hAdm.1.ne)
  let ξg : Sp X₁.Ω₁ ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι Y.pt hsub
  have hξg : ξg ≫ U₀.ι = Y.pt := IsOpenImmersion.lift_fac _ _ _
  have hu : ξg ≫ out.u₀ = spMap X₁.S.R.val.toRingHom := out.u₀_gen ξg hξg
  have hHom' : Y.pt ≫ πY = X₁.M.pt := by
    rw [hHom]
    show Spec.map (CommRingCat.ofHom (RingHom.id X₁.Ω₁)) ≫ _ = _
    rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  refine ⟨T, f, hfi, hfl, ⟨spMap γ ≫ ξg, ?_, ?_⟩, ?_⟩
  · rw [hpt, Category.assoc, hξg]
  · refine ⟨spMap γ ≫ spMap (ratHull X₁.S.R).val.toRingHom, ?_, ?_⟩
    · rw [Category.assoc, spMap_val_toRat, Category.assoc, hu]
    · rw [hy, Category.assoc]
  · rw [hy]
    simp only [Category.assoc] at hpt ⊢
    rw [reassoc_of% hpt, reassoc_of% hHom', X₁.comp]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTraitThroughOpenOfStalkCompleteDvrStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

theorem _root_.GlobalTheory.T.exists_unitaryTrait_through_open_of_stalk_complete_dvr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE) (πY : Y.Z ⟶ X₁.M.Z), X₁.S.admitted Y U₀ → X₁.S.IsEE Y U₀ EE → X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY → ∀ (x : Y.Z) (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CharZero A], IsAdicComplete (maximalIdeal A) A → ∀ θ : Y.Z.presheaf.stalk x →+* A, Function.Injective θ → IsLocalHom θ → ∃ (T : UTrait Xo c) (f : A →+* T.V), Function.Injective f ∧ IsLocalHom f ∧ (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ (spMap (f.comp θ) ≫ Y.Z.fromSpecStalk x) ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) ∧ T.y ≫ C.i = jK T.V ≫ (spMap (f.comp θ) ≫ Y.Z.fromSpecStalk x) ≫ πY ≫ X₁.π := by
  first | exact @GlobalTheory.UPoinc.exists_uTrait_through_open_of_stalk_dvr | exact GlobalTheory.UPoinc.exists_uTrait_through_open_of_stalk_dvr | (intros; apply GlobalTheory.UPoinc.exists_uTrait_through_open_of_stalk_dvr <;> assumption)
end
end
