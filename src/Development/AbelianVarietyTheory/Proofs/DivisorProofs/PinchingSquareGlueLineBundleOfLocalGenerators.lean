module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Glues
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Matched
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitOfPinchingSquareGluedUnitsStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Mathlib.Tactic.TypeStar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRatioUnitOfLineBundleGeneratorsOnOpens

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PinchLift

theorem exists_ratio_unit : ∀ (Y : Scheme.{0}) (L : LB Y), L.IsLB → ∀ (O₁ O₂ : Y.Opens) (s₁ : ∀ k, Γ(Y, L.U k ⊓ O₁)ˣ) (s₂ : ∀ k, Γ(Y, L.U k ⊓ O₂)ˣ), GlobalTheory.PinchLift.GenOn L O₁ s₁ → GlobalTheory.PinchLift.GenOn L O₂ s₂ → ∃ r : Γ(Y, O₁ ⊓ O₂)ˣ, ∀ (T : Scheme.{0}) (f : T ⟶ Y) (t : T) (k : L.ι), f t ∈ L.U k → f t ∈ O₁ → f t ∈ O₂ → gm f t (O₁ ⊓ O₂) r = gm f t (L.U k ⊓ O₁) (s₁ k) * (gm f t (L.U k ⊓ O₂) (s₂ k))⁻¹ := by
  intro Y L hL O₁ O₂ s₁ s₂ h₁ h₂
  have hW : ∀ k, L.U k ⊓ (O₁ ⊓ O₂) ≤ O₁ ⊓ O₂ := fun k => inf_le_right
  have hc : O₁ ⊓ O₂ ≤ ⨆ k, L.U k ⊓ (O₁ ⊓ O₂) := fun y hy => by
    obtain ⟨k, hk⟩ := exists_chart hL y
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hk, hy⟩
  have i₁ : ∀ k, L.U k ⊓ (O₁ ⊓ O₂) ≤ L.U k ⊓ O₁ := fun k => inf_le_inf_left _ inf_le_left
  have i₂ : ∀ k, L.U k ⊓ (O₁ ⊓ O₂) ≤ L.U k ⊓ O₂ := fun k => inf_le_inf_left _ inf_le_right
  let u : ∀ k, Γ(Y, L.U k ⊓ (O₁ ⊓ O₂))ˣ := fun k => res (i₁ k) (s₁ k) * (res (i₂ k) (s₂ k))⁻¹
  have hu : ∀ (T : Scheme.{0}) (f : T ⟶ Y) (t : T) (k : L.ι), f t ∈ L.U k ⊓ (O₁ ⊓ O₂) →
      gm f t (L.U k ⊓ (O₁ ⊓ O₂)) (u k) = gm f t (L.U k ⊓ O₁) (s₁ k) * (gm f t (L.U k ⊓ O₂) (s₂ k))⁻¹ := by
    intro T f t k hy
    simp only [u, map_mul, map_inv, gm_res f t (i₁ k) hy, gm_res f t (i₂ k) hy]
  obtain ⟨r, hr⟩ := glue_unit (O₁ ⊓ O₂) (fun k => L.U k ⊓ (O₁ ⊓ O₂)) hW hc u (by
    intro k l y hy
    have hk : y ∈ L.U k ⊓ (O₁ ⊓ O₂) := hy.1
    have hl : y ∈ L.U l ⊓ (O₁ ⊓ O₂) := hy.2
    show gm (𝟙 Y) y (L.U k ⊓ (O₁ ⊓ O₂)) (u k) = gm (𝟙 Y) y (L.U l ⊓ (O₁ ⊓ O₂)) (u l)
    rw [hu Y (𝟙 Y) y k hk, hu Y (𝟙 Y) y l hl, h₁ k l y hk.1 hl.1 hk.2.1, h₂ k l y hk.1 hl.1 hk.2.2,
      ← div_eq_mul_inv, ← div_eq_mul_inv, mul_div_mul_left_eq_div])
  refine ⟨r, fun T f t k hk ht₁ ht₂ => ?_⟩
  have hy : f t ∈ L.U k ⊓ (O₁ ⊓ O₂) := ⟨hk, ht₁, ht₂⟩
  rw [← gm_res f t (hW k) hy r, hr k, hu T f t k hy]

end GlobalTheory.PinchLift
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRatioUnitOfLineBundleGeneratorsOnOpensStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_ratio_unit_of_lineBundle_generators_on_opens : ∀ (Y : Scheme.{0}) (L : LB Y), L.IsLB → ∀ (O₁ O₂ : Y.Opens) (s₁ : ∀ k, Γ(Y, L.U k ⊓ O₁)ˣ) (s₂ : ∀ k, Γ(Y, L.U k ⊓ O₂)ˣ), GlobalTheory.PinchLift.GenOn L O₁ s₁ → GlobalTheory.PinchLift.GenOn L O₂ s₂ → ∃ r : Γ(Y, O₁ ⊓ O₂)ˣ, ∀ (T : Scheme.{0}) (f : T ⟶ Y) (t : T) (k : L.ι), f t ∈ L.U k → f t ∈ O₁ → f t ∈ O₂ → gm f t (O₁ ⊓ O₂) r = gm f t (L.U k ⊓ O₁) (s₁ k) * (gm f t (L.U k ⊓ O₂) (s₂ k))⁻¹ := by
  first | exact @GlobalTheory.PinchLift.exists_ratio_unit | exact GlobalTheory.PinchLift.exists_ratio_unit | (intros; apply GlobalTheory.PinchLift.exists_ratio_unit <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoPullbackOfLocalUnitGenerators

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PinchLift

theorem lbIso_pull_of_genOn (X Y : Scheme.{0}) (f : Y ⟶ X) (L : LB Y) (J : Type) (W : J → X.Opens)
    (g : ∀ x y, Γ(X, W x ⊓ W y)ˣ) (s : ∀ x k, Γ(Y, L.U k ⊓ f ⁻¹ᵁ W x)ˣ)
    (hs : ∀ x, GlobalTheory.PinchLift.GenOn L (f ⁻¹ᵁ W x) (s x))
    (hg : ∀ x y (t : Y) (k : L.ι), f t ∈ W x → f t ∈ W y → t ∈ L.U k →
      gm f t (W x ⊓ W y) (g x y) =
        gm (𝟙 Y) t (L.U k ⊓ f ⁻¹ᵁ W y) (s y k) * (gm (𝟙 Y) t (L.U k ⊓ f ⁻¹ᵁ W x) (s x k))⁻¹) :
    LBIso L ((⟨J, W, g⟩ : LB X).pull f) := by
  have le : ∀ p : (PUnit → J) × L.ι, ((⟨J, W, g⟩ : LB X).pull f).U p.1 ⊓ L.U p.2 ≤
      L.U p.2 ⊓ f ⁻¹ᵁ W (p.1 PUnit.unit) := fun p y h =>
    ⟨h.2, (mem_pull (L := (⟨J, W, g⟩ : LB X)) (F := f)).1 h.1⟩
  refine ⟨⟨fun p => res (le p) (s (p.1 PUnit.unit) p.2)⁻¹⟩, (isGen_iff_germ _).2 fun y p q hp hq => ?_⟩
  have v : ∀ p : (PUnit → J) × L.ι, y ∈ ((⟨J, W, g⟩ : LB X).pull f).U p.1 ⊓ L.U p.2 →
      gm (𝟙 Y) y _ (res (le p) (s (p.1 PUnit.unit) p.2)⁻¹) =
        (gm (𝟙 Y) y (L.U p.2 ⊓ f ⁻¹ᵁ W (p.1 PUnit.unit)) (s (p.1 PUnit.unit) p.2))⁻¹ := fun p hp =>
    (gm_res _ y _ hp _).trans (map_inv _ _)
  have hp' := le p hp
  have hq' := le q hq
  have e1 := gm_pull_g (⟨J, W, g⟩ : LB X) f (𝟙 Y) y p.1 q.1 hp.1 hq.1
  have e2 : gm (𝟙 Y ≫ f) y (W (p.1 PUnit.unit) ⊓ W (q.1 PUnit.unit)) (g _ _) =
      gm f y (W (p.1 PUnit.unit) ⊓ W (q.1 PUnit.unit)) (g _ _) := by
    rw [Category.id_comp]
  have e3 := hg (p.1 PUnit.unit) (q.1 PUnit.unit) y p.2 hp'.2 hq'.2 hp'.1
  have e4 := hs (q.1 PUnit.unit) p.2 q.2 y hp'.1 hq'.1 hq'.2
  have e5 := (e1.trans e2).trans (e3.trans (congrArg (· * _) e4))
  refine (v p hp).trans (Eq.trans ?_ (congrArg₂ (· * ·)
    ((gm_div' ((⟨J, W, g⟩ : LB X).pull f) L (𝟙 Y) y p q hp hq).trans (congrArg (· * _) e5)) (v q hq)).symm)
  have key : ∀ {G : Type} [CommGroup G] (a b c : G), c⁻¹ = a * b * c⁻¹ * a⁻¹ * b⁻¹ := by
    intro G _ a b c
    rw [mul_assoc (a * b * c⁻¹), ← mul_inv, mul_right_comm, mul_inv_cancel, _root_.one_mul]
  exact key _ _ _

end GlobalTheory.PinchLift
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoPullbackOfLocalUnitGeneratorsStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.lineBundle_iso_pullback_of_local_unit_generators : ∀ (X Y : Scheme.{0}) (f : Y ⟶ X) (L : LB Y) (J : Type) (W : J → X.Opens) (g : ∀ x y, Γ(X, W x ⊓ W y)ˣ) (s : ∀ x k, Γ(Y, L.U k ⊓ f ⁻¹ᵁ W x)ˣ), (∀ x, GlobalTheory.PinchLift.GenOn L (f ⁻¹ᵁ W x) (s x)) → (∀ x y (t : Y) (k : L.ι), f t ∈ W x → f t ∈ W y → t ∈ L.U k → gm f t (W x ⊓ W y) (g x y) = gm (𝟙 Y) t (L.U k ⊓ f ⁻¹ᵁ W y) (s y k) * (gm (𝟙 Y) t (L.U k ⊓ f ⁻¹ᵁ W x) (s x k))⁻¹) → LBIso L ((⟨J, W, g⟩ : LB X).pull f) := by
  first | exact @GlobalTheory.PinchLift.lbIso_pull_of_genOn | exact GlobalTheory.PinchLift.lbIso_pull_of_genOn | (intros; apply GlobalTheory.PinchLift.lbIso_pull_of_genOn <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitEqOfGermsPinchingSquare

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PinchLift

theorem unit_eq_of_germs_glues : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), i' ≫ p = p' ≫ i → GlobalTheory.PinchLift.Glues p i i' p' → ∀ (V : X.Opens) (u v : Γ(X, V)ˣ), (∀ x' : X', p x' ∈ V → gm p x' V u = gm p x' V v) → (∀ z : Z, i z ∈ V → gm i z V u = gm i z V v) → u = v := by
  intro X X' Z Z' p i i' p' hc hG V u v hp hi
  have ep : (p.app V).hom u.val = (p.app V).hom v.val := by
    apply TopCat.Presheaf.section_ext X'.sheaf (p ⁻¹ᵁ V)
    intro x hx
    have h := congrArg Units.val (hp x hx)
    rwa [gm_val _ x V hx, gm_val _ x V hx] at h
  have ei : (i.app V).hom u.val = (i.app V).hom v.val := by
    apply TopCat.Presheaf.section_ext Z.sheaf (i ⁻¹ᵁ V)
    intro z hz
    have h := congrArg Units.val (hi z hz)
    rwa [gm_val _ z V hz, gm_val _ z V hz] at h
  have key : ∀ (f g : Z' ⟶ X) (_ : f = g) (O : Z'.Opens) (e : O ≤ f ⁻¹ᵁ V) (e' : O ≤ g ⁻¹ᵁ V),
      f.appLE V O e = g.appLE V O e' := by
    intro f g hfg O e e'; subst hfg; rfl
  have hag : (i'.appLE (p ⁻¹ᵁ V) (i' ⁻¹ᵁ (p ⁻¹ᵁ V) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ V)) inf_le_left).hom ((p.app V).hom u.val) =
      (p'.appLE (i ⁻¹ᵁ V) (i' ⁻¹ᵁ (p ⁻¹ᵁ V) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ V)) inf_le_right).hom ((i.app V).hom u.val) := by
    have e1 := Scheme.Hom.comp_appLE i' p V (i' ⁻¹ᵁ (p ⁻¹ᵁ V) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ V)) inf_le_left
    have e2 := Scheme.Hom.comp_appLE p' i V (i' ⁻¹ᵁ (p ⁻¹ᵁ V) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ V)) inf_le_right
    have e3 := key _ _ hc (i' ⁻¹ᵁ (p ⁻¹ᵁ V) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ V)) inf_le_left inf_le_right
    rw [e1, e2] at e3
    have := congrArg (fun f => f.hom u.val) e3
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using this
  exact Units.ext ((hG V _ _ hag).unique ⟨rfl, rfl⟩ ⟨ep.symm, ei.symm⟩)

end GlobalTheory.PinchLift
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitEqOfGermsPinchingSquareStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.unit_eq_of_germs_pinching_square : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), i' ≫ p = p' ≫ i → GlobalTheory.PinchLift.Glues p i i' p' → ∀ (V : X.Opens) (u v : Γ(X, V)ˣ), (∀ x' : X', p x' ∈ V → gm p x' V u = gm p x' V v) → (∀ z : Z, i z ∈ V → gm i z V u = gm i z V v) → u = v := by
  first | exact @GlobalTheory.PinchLift.unit_eq_of_germs_glues | exact GlobalTheory.PinchLift.unit_eq_of_germs_glues | (intros; apply GlobalTheory.PinchLift.unit_eq_of_germs_glues <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PinchingSquareGlueLineBundleOfLocalGenerators

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PinchLift

theorem ratio_tele {G : Type*} [CommGroup G] (a b c : G) : a * b⁻¹ * (c * a⁻¹) = c * b⁻¹ := by
  rw [mul_comm c, ← _root_.mul_assoc, mul_comm a b⁻¹, mul_inv_cancel_right, mul_comm]

theorem ratio_cancel_left {G : Type*} [CommGroup G] (w a b : G) : a * b⁻¹ = w * a * (w * b)⁻¹ := by
  rw [mul_inv, ← _root_.mul_assoc, mul_comm w a, mul_inv_cancel_right]

theorem assemble : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), IsPullback i' p' p i → GlobalTheory.PinchLift.Glues p i i' p' → ∀ (L' : LB X') (LZ : LB Z) (hL' : L'.IsLB) (hLZ : LZ.IsLB) (w : LB.Iso (L'.pull i') (LZ.pull p')), w.IsGen → (∀ x : X, ∃ (W : X.Opens) (s' : ∀ k, Γ(X', L'.U k ⊓ p ⁻¹ᵁ W)ˣ) (sZ : ∀ j, Γ(Z, LZ.U j ⊓ i ⁻¹ᵁ W)ˣ), x ∈ W ∧ GlobalTheory.PinchLift.GenOn L' (p ⁻¹ᵁ W) s' ∧ GlobalTheory.PinchLift.GenOn LZ (i ⁻¹ᵁ W) sZ ∧ GlobalTheory.PinchLift.Matched i' p' L' LZ w (p ⁻¹ᵁ W) (i ⁻¹ᵁ W) s' sZ) → ∃ e : Pic X, GlobalTheory.CechPic.pull p e = cls L' hL' ∧ GlobalTheory.CechPic.pull i e = cls LZ hLZ := by
  intro X X' Z Z' p i i' p' hsq hG L' LZ hL' hLZ w _ hloc
  have hc : i' ≫ p = p' ≫ i := hsq.w
  have hpt : ∀ z : Z', i (p' z) = p (i' z) := fun z => (congrArg (fun q => q z) hc).symm
  choose W s' sZ hxW hs' hsZ hM using hloc
  have r'e := fun x y => GlobalTheory.T.exists_ratio_unit_of_lineBundle_generators_on_opens _ L' hL' _ _ (s' y) (s' x) (hs' y) (hs' x)
  choose r' hr' using r'e
  have rZe := fun x y => GlobalTheory.T.exists_ratio_unit_of_lineBundle_generators_on_opens _ LZ hLZ _ _ (sZ y) (sZ x) (hsZ y) (hsZ x)
  choose rZ hrZ using rZe
  have le' : ∀ x y : X, p ⁻¹ᵁ (W x ⊓ W y) ≤ p ⁻¹ᵁ W y ⊓ p ⁻¹ᵁ W x := fun x y _ h => ⟨h.2, h.1⟩
  have leZ : ∀ x y : X, i ⁻¹ᵁ (W x ⊓ W y) ≤ i ⁻¹ᵁ W y ⊓ i ⁻¹ᵁ W x := fun x y _ h => ⟨h.2, h.1⟩
  have ge := fun x y => GlobalTheory.T.exists_unit_of_pinchingSquare_glued_units _ _ _ _ p i i' p' hc hG (W x ⊓ W y) (res (le' x y) (r' x y)) (res (leZ x y) (rZ x y)) (by
    intro z hz
    have hz' : i (p' z) ∈ W x ⊓ W y := (hpt z).symm ▸ hz
    obtain ⟨k, hk⟩ := exists_chart hL' (i' z)
    obtain ⟨j, hj⟩ := exists_chart hLZ (p' z)
    rw [gm_res _ z _ hz, gm_res _ z _ hz', hr' x y Z' i' z k hk hz.2 hz.1, hrZ x y Z' p' z j hj hz'.2 hz'.1,
      hM y z j k hj hk hz'.2 hz.2, hM x z j k hj hk hz'.1 hz.1]
    exact ratio_cancel_left _ _ _)
  choose g hgp hgi using ge
  have Gp : ∀ x y (t : X') (k : L'.ι), p t ∈ W x → p t ∈ W y → t ∈ L'.U k →
      gm p t (W x ⊓ W y) (g x y) = gm (𝟙 X') t (L'.U k ⊓ p ⁻¹ᵁ W y) (s' y k) * (gm (𝟙 X') t (L'.U k ⊓ p ⁻¹ᵁ W x) (s' x k))⁻¹ := by
    intro x y t k hx hy hk
    rw [hgp x y t ⟨hx, hy⟩, gm_res _ t _ (show t ∈ p ⁻¹ᵁ (W x ⊓ W y) from ⟨hx, hy⟩), hr' x y X' (𝟙 X') t k hk hy hx]
  have Gi : ∀ x y (t : Z) (k : LZ.ι), i t ∈ W x → i t ∈ W y → t ∈ LZ.U k →
      gm i t (W x ⊓ W y) (g x y) = gm (𝟙 Z) t (LZ.U k ⊓ i ⁻¹ᵁ W y) (sZ y k) * (gm (𝟙 Z) t (LZ.U k ⊓ i ⁻¹ᵁ W x) (sZ x k))⁻¹ := by
    intro x y t k hx hy hk
    rw [hgi x y t ⟨hx, hy⟩, gm_res _ t _ (show t ∈ i ⁻¹ᵁ (W x ⊓ W y) from ⟨hx, hy⟩), hrZ x y Z (𝟙 Z) t k hk hy hx]
  let E : LB X := ⟨X, W, g⟩
  have hE : E.IsLB := by
    refine ⟨eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxW x⟩, fun x => ?_, fun x y z => ?_⟩
    · refine GlobalTheory.T.unit_eq_of_germs_pinching_square _ _ _ _ p i i' p' hc hG _ _ _ (fun t ht => ?_) (fun t ht => ?_)
      · obtain ⟨k, hk⟩ := exists_chart hL' t
        rw [map_one, gm_res _ t _ ht]
        exact (Gp x x t k ht ht hk).trans (mul_inv_cancel _)
      · obtain ⟨k, hk⟩ := exists_chart hLZ t
        rw [map_one, gm_res _ t _ ht]
        exact (Gi x x t k ht ht hk).trans (mul_inv_cancel _)
    · refine GlobalTheory.T.unit_eq_of_germs_pinching_square _ _ _ _ p i i' p' hc hG _ _ _ (fun t ht => ?_) (fun t ht => ?_)
      · obtain ⟨k, hk⟩ := exists_chart hL' t
        rw [map_mul, gm_res _ t _ ht, gm_res _ t _ ht, gm_res _ t _ ht]
        show gm p t (W x ⊓ W y) (g x y) * gm p t (W y ⊓ W z) (g y z) = gm p t (W x ⊓ W z) (g x z)
        rw [Gp x y t k ht.1.1 ht.1.2 hk, Gp y z t k ht.1.2 ht.2 hk, Gp x z t k ht.1.1 ht.2 hk]
        exact ratio_tele _ _ _
      · obtain ⟨k, hk⟩ := exists_chart hLZ t
        rw [map_mul, gm_res _ t _ ht, gm_res _ t _ ht, gm_res _ t _ ht]
        show gm i t (W x ⊓ W y) (g x y) * gm i t (W y ⊓ W z) (g y z) = gm i t (W x ⊓ W z) (g x z)
        rw [Gi x y t k ht.1.1 ht.1.2 hk, Gi y z t k ht.1.2 ht.2 hk, Gi x z t k ht.1.1 ht.2 hk]
        exact ratio_tele _ _ _
  refine ⟨cls E hE, ?_, ?_⟩
  · rw [← cls_pull hE p (pull_isLB hE p)]
    exact (cls_eq_iff _ _).2 (LBIso.symm (GlobalTheory.T.lineBundle_iso_pullback_of_local_unit_generators _ _ p L' X W g s' hs' Gp))
  · rw [← cls_pull hE i (pull_isLB hE i)]
    exact (cls_eq_iff _ _).2 (LBIso.symm (GlobalTheory.T.lineBundle_iso_pullback_of_local_unit_generators _ _ i LZ X W g sZ hsZ Gi))

end GlobalTheory.PinchLift
end
end
end
