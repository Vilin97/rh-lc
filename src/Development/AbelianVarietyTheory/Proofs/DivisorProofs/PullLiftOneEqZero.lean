module

public import Development.AbelianVarietyTheory.Definitions.Divisors.WhiskerLeftEqLift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedPicardClassZeroOfLocallyZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhiskerLeftIsOpenImmersionRange
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueRigidifiedLineBundleClassesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPreimageSectionsBijectiveAbelianSchemeSndStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditivePicClassOfLocallyAdditive

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

variable {S : Scheme.{0}}

theorem pull_pull_over {X Y Z : Over S} (u : Z ⟶ Y) (v : Y ⟶ X) (c : Pic X.left) :
    CechPic.pull u.left (CechPic.pull v.left c) = CechPic.pull (u ≫ v).left c := by
  rw [Over.comp_left, pull_comp]

def addDefect (A T : Over S) [GrpObj A] (c : Pic (A ⊗ T).left) : Pic (A ⊗ (A ⊗ T)).left :=
  CechPic.pull (lift (fst A (A ⊗ T) * (snd A (A ⊗ T) ≫ fst A T)) (snd A (A ⊗ T) ≫ snd A T)).left c -
    CechPic.pull (lift (fst A (A ⊗ T)) (snd A (A ⊗ T) ≫ snd A T)).left c -
    CechPic.pull (lift (snd A (A ⊗ T) ≫ fst A T) (snd A (A ⊗ T) ≫ snd A T)).left c

theorem pull_addDefect (A T : Over S) [GrpObj A] (c : Pic (A ⊗ T).left) {Z : Over S} (u : Z ⟶ A ⊗ (A ⊗ T)) :
    CechPic.pull u.left (addDefect A T c) =
      CechPic.pull (lift ((u ≫ fst _ _) * (u ≫ snd _ _ ≫ fst _ _)) (u ≫ snd _ _ ≫ snd _ _)).left c -
      CechPic.pull (lift (u ≫ fst _ _) (u ≫ snd _ _ ≫ snd _ _)).left c -
      CechPic.pull (lift (u ≫ snd _ _ ≫ fst _ _) (u ≫ snd _ _ ≫ snd _ _)).left c := by
  simp only [addDefect, map_sub, pull_pull_over, comp_lift, MonObj.comp_mul]

theorem addCls_of_locally : ∀ (S : Scheme.{0}) (A T : Over S) [GrpObj A], IsAbelianScheme A →
    ∀ c : Pic (A ⊗ T).left, GlobalTheory.CechPic.pull (lift (1 : T ⟶ A) (𝟙 T)).left c = 0 →
    (∀ p : T.left, ∃ (Z : Over S) (z : Z ⟶ T), IsOpenImmersion z.left ∧ p ∈ Set.range z.left ∧
      AddCls A (GlobalTheory.CechPic.pull (A ◁ z).left c)) → AddCls A c := by
  intro S A T _ hA c h0 hloc
  have hd : addDefect A T c = 0 := by
    refine GlobalTheory.T.rigidified_picard_class_zero_of_locally_zero S A (A ⊗ T) hA _ ?_ fun p ↦ ?_
    · rw [pull_addDefect]
      have h1 : lift (1 : A ⊗ T ⟶ A) (snd A T) = snd A T ≫ lift (1 : T ⟶ A) (𝟙 T) := by
        rw [comp_lift, MonObj.comp_one, Category.comp_id]
      simp only [lift_fst, lift_snd_assoc, Category.id_comp, _root_.one_mul]
      rw [h1, ← pull_pull_over, h0, map_zero, sub_zero, sub_self]
    · obtain ⟨Z, z, hz, hp, hadd⟩ := hloc ((snd A T).left p)
      obtain ⟨ho, hr⟩ := GlobalTheory.whiskerLeft_isOpenImmersion_range S A T Z z hz
      refine ⟨A ⊗ Z, A ◁ z, ho, (hr p).2 hp, ?_⟩
      have h2 := hadd (A ⊗ (A ⊗ Z)) (fst _ _) (snd _ _ ≫ fst _ _) (snd _ _ ≫ snd _ _)
      simp only [pull_pull_over, lift_whiskerLeft, Category.assoc] at h2
      rw [pull_addDefect]
      simp only [whiskerLeft_fst, whiskerLeft_snd_assoc, whiskerLeft_snd]
      rw [h2]
      abel
  intro Z a a' t
  have h3 := pull_addDefect A T c (lift a (lift a' t))
  rw [hd, map_zero] at h3
  simp only [lift_fst, lift_snd_assoc, lift_snd] at h3
  rw [sub_sub] at h3
  exact sub_eq_zero.1 h3.symm

end GlobalTheory.PicGlue
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditivePicClassOfLocallyAdditiveStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.additive_picClass_of_locally_additive : ∀ (S : Scheme.{0}) (A T : Over S) [GrpObj A], IsAbelianScheme A → ∀ c : Pic (A ⊗ T).left, GlobalTheory.CechPic.pull (lift (1 : T ⟶ A) (𝟙 T)).left c = 0 → (∀ p : T.left, ∃ (Z : Over S) (z : Z ⟶ T), IsOpenImmersion z.left ∧ p ∈ Set.range z.left ∧ AddCls A (GlobalTheory.CechPic.pull (A ◁ z).left c)) → AddCls A c := by
  first | exact @GlobalTheory.PicGlue.addCls_of_locally | exact GlobalTheory.PicGlue.addCls_of_locally | (intros; apply GlobalTheory.PicGlue.addCls_of_locally <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullLiftOneEqZero

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem AddCls.pull_lift_one_eq_zero {T : Over S} {c : Pic (A ⊗ T).left} (h : AddCls A c) {Y : Over S} (t : Y ⟶ T) :
    CechPic.pull (lift (1 : Y ⟶ A) t).left c = 0 := by
  have h1 := h Y 1 1 t
  rw [_root_.mul_one] at h1
  exact left_eq_add.1 h1

theorem AddCls.pull_eq_zero_of_unit {T Z : Over S} (z : Z ⟶ T) {c : Pic (A ⊗ Z).left} (h : AddCls A c)
    {T' : Scheme.{0}} (t : T' ⟶ (A ⊗ Z).left) (s : T' ⟶ T.left)
    (hts : t ≫ (A ◁ z).left = s ≫ (lift (1 : T ⟶ A) (𝟙 T)).left) : CechPic.pull t c = 0 := by
  let Y : Over S := Over.mk (t ≫ (A ⊗ Z).hom)
  let t' : Y ⟶ A ⊗ Z := Over.homMk t rfl
  have hs : s ≫ T.hom = t ≫ (A ⊗ Z).hom := by
    rw [← Over.w (A ◁ z), ← Category.assoc, hts, Category.assoc, Over.w]
  let s' : Y ⟶ T := Over.homMk s hs
  have h1 : t' ≫ A ◁ z = s' ≫ lift (1 : T ⟶ A) (𝟙 T) := Over.OverMorphism.ext hts
  have h2 : t' ≫ fst A Z = 1 := by
    have h3 := congrArg (· ≫ fst A T) h1
    simpa only [Category.assoc, whiskerLeft_fst, lift_fst, MonObj.comp_one] using h3
  have h4 : t' = lift (1 : Y ⟶ A) (t' ≫ snd A Z) := by
    rw [← h2, lift_comp_fst_snd]
  have h5 := h.pull_lift_one_eq_zero (t' ≫ snd A Z)
  rw [← h4] at h5
  exact h5

theorem pull_eq_of_compat {T Z Z' : Over S} (z : Z ⟶ T) (z' : Z' ⟶ T) (y : (addF A).obj (op Z))
    (y' : (addF A).obj (op Z'))
    (h : ∀ (Y : Over S) (a : Y ⟶ Z) (b : Y ⟶ Z'), a ≫ z = b ≫ z' → (addF A).map a.op y = (addF A).map b.op y')
    {T' : Scheme.{0}} (a : T' ⟶ (A ⊗ Z).left) (b : T' ⟶ (A ⊗ Z').left)
    (hab : a ≫ (A ◁ z).left = b ≫ (A ◁ z').left) : CechPic.pull a y.1 = CechPic.pull b y'.1 := by
  let Y : Over S := Over.mk (a ≫ (A ⊗ Z).hom)
  let a' : Y ⟶ A ⊗ Z := Over.homMk a rfl
  have hb : b ≫ (A ⊗ Z').hom = a ≫ (A ⊗ Z).hom := by
    rw [← Over.w (A ◁ z), ← Over.w (A ◁ z'), ← Category.assoc, ← hab, Category.assoc]
  let b' : Y ⟶ A ⊗ Z' := Over.homMk b hb
  have h1 : a' ≫ A ◁ z = b' ≫ A ◁ z' := Over.OverMorphism.ext hab
  have h2 : a' ≫ fst A Z = b' ≫ fst A Z' := by
    have h3 := congrArg (· ≫ fst A T) h1
    simpa only [Category.assoc, whiskerLeft_fst] using h3
  have h3 : (a' ≫ snd A Z) ≫ z = (b' ≫ snd A Z') ≫ z' := by
    have h3 := congrArg (· ≫ snd A T) h1
    simpa only [Category.assoc, whiskerLeft_snd] using h3
  have h4 := congrArg Subtype.val (h Y _ _ h3)
  rw [addF_map_val, addF_map_val] at h4
  have ha' : a' = lift (a' ≫ fst A Z) (𝟙 Y) ≫ A ◁ (a' ≫ snd A Z) := by
    rw [lift_whiskerLeft, Category.id_comp, lift_comp_fst_snd]
  have hb' : b' = lift (a' ≫ fst A Z) (𝟙 Y) ≫ A ◁ (b' ≫ snd A Z') := by
    rw [lift_whiskerLeft, Category.id_comp, h2, lift_comp_fst_snd]
  have h5 := congrArg (CechPic.pull (lift (a' ≫ fst A Z) (𝟙 Y)).left) h4
  rw [← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, ← ha', ← hb'] at h5
  exact h5

theorem addF_glue : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → (∀ (T : Over S) (J : Type) (Z : J → Over S) (z : ∀ i, Z i ⟶ T) (y : ∀ i, (addF A).obj (op (Z i))), (∀ i, IsOpenImmersion (z i).left) → (∀ p : T.left, ∃ i, p ∈ Set.range (z i).left) → (∀ (i k : J) (Y : Over S) (a : Y ⟶ Z i) (b : Y ⟶ Z k), a ≫ z i = b ≫ z k → (addF A).map a.op (y i) = (addF A).map b.op (y k)) → ∃ y₀ : (addF A).obj (op T), ∀ i, (addF A).map (z i).op y₀ = y i) := by
  intro S A _ hA T J Z z y hz hcov hc
  have he : (lift (1 : T ⟶ A) (𝟙 T)).left ≫ (snd A T).left = 𝟙 T.left := by
    rw [← Over.comp_left, lift_snd, Over.id_left]
  obtain ⟨c₀, h0, hc₀⟩ := GlobalTheory.T.exists_glue_rigidified_line_bundle_classes (A ⊗ T).left T.left (snd A T).left (lift (1 : T ⟶ A) (𝟙 T)).left he
    (GlobalTheory.T.isPreimageSectionsBijective_abelianScheme_snd S A T hA) J (fun i ↦ (A ⊗ Z i).left) (fun i ↦ (A ◁ z i).left)
    (fun i ↦ haveI := hz i; (z i).left.opensRange) (fun i ↦ (y i).1)
    (fun i ↦ (GlobalTheory.whiskerLeft_isOpenImmersion_range S A T (Z i) (z i) (hz i)).1)
    (fun i x ↦ (GlobalTheory.whiskerLeft_isOpenImmersion_range S A T (Z i) (z i) (hz i)).2 x)
    (fun p ↦ hcov p)
    (fun i T' t s hts ↦ AddCls.pull_eq_zero_of_unit (z i) (y i).2 t s hts)
    (fun i k T' a b hab ↦ pull_eq_of_compat (z i) (z k) (y i) (y k) (hc i k) a b hab)
  refine ⟨⟨c₀, GlobalTheory.T.additive_picClass_of_locally_additive S A T hA c₀ h0 fun p ↦ ?_⟩, fun i ↦ Subtype.ext (hc₀ i)⟩
  obtain ⟨i, hi⟩ := hcov p
  refine ⟨Z i, z i, hz i, hi, ?_⟩
  rw [hc₀ i]
  exact (y i).2

end GlobalTheory.PicGlue
end
end
end
