module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecBaseChangeOfPerf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentDatumAdditiveLineBundleIsogenyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleDescentFiniteFlatStatement
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfTrivAxes
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveLineBundleDescendsAlongIsogenyTorsor

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PoincareDescent

theorem descend_torsor : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' B N : Over (Sp K)) [GrpObj A] [GrpObj A'] [GrpObj B] [GrpObj N] (P : LB (A ⊗ B).left) (i : N ⟶ A) (q : A ⟶ A'), IsAbelianScheme A → IsAbelianScheme A' → IsAbelianScheme B → P.IsLB → IsAdditive P → Triv (ev P (𝟙 A) (1 : A ⟶ B)) → IsMonHom i → IsMonHom q → IsFinite q.left → Flat q.left → Surjective q.left → IsPullback (fst A N) (fst A N * (snd A N ≫ i)) q q → Triv (ev P (fst N B ≫ i) (snd N B)) → ∃ P₀ : LB (A' ⊗ B).left, P₀.IsLB ∧ LBIso (ev P₀ (fst A B ≫ q) (snd A B)) P := by
  intro K _ _ A A' B N _ _ _ _ P i q hA hA' hB hP hadd hzero hi hq hfin hflat hsurj hsq hN
  haveI : IsFinite q.left := hfin
  haveI : Flat q.left := hflat
  haveI : Surjective q.left := hsurj
  have hpb := GlobalTheory.AbLaw.SecBC.isPullback_whisker (A := B) q
  haveI : IsFinite (q ▷ B).left := MorphismProperty.of_isPullback hpb.flip hfin
  haveI : Flat (q ▷ B).left := MorphismProperty.of_isPullback hpb.flip hflat
  haveI : Surjective (q ▷ B).left := MorphismProperty.of_isPullback hpb.flip hsurj
  haveI : IsLocallyNoetherian (A' ⊗ B).left := by
    haveI := hA'.smooth
    haveI := hB.smooth
    haveI : LocallyOfFiniteType (A' ⊗ B).hom := by
      show LocallyOfFiniteType (pullback.fst A'.hom B.hom ≫ A'.hom)
      infer_instance
    exact LocallyOfFiniteType.isLocallyNoetherian (A' ⊗ B).hom
  have hker : ∀ (T : Over (Sp K)) (x : T ⟶ A), x ≫ q = 1 → Triv (ev P (fst T B ≫ x) (snd T B)) := by
    intro T x hx
    have e : (1 : T ⟶ A) ≫ q = x ≫ q := by rw [hx, MonObj.one_comp]
    have hx' : x = (hsq.lift 1 x e ≫ snd A N) ≫ i := by
      have h2 := hsq.lift_snd 1 x e
      rw [MonObj.comp_mul, hsq.lift_fst, _root_.one_mul, ← Category.assoc] at h2
      exact h2.symm
    obtain ⟨n, rfl⟩ : ∃ n : T ⟶ N, x = n ≫ i := ⟨_, hx'⟩
    rw [triv_ev_iff hP]
    have z := congrArg (CechPic.pull (lift (fst T B ≫ n) (snd T B)).left) ((triv_ev_iff hP _ _).1 hN)
    rw [pull_evc, map_zero, lift_fst_assoc, lift_snd, Category.assoc] at z
    exact z
  obtain ⟨φ, hc, hco⟩ := GlobalTheory.T.exists_descentDatum_additive_lineBundle_isogeny K A A' B q P hA hA' hB hq hfin hflat hsurj hP hadd hzero hker
  obtain ⟨P₀, hP₀, hiso⟩ := GlobalTheory.T.exists_lineBundle_descent_finiteFlat _ _ (q ▷ B).left P hP φ hc hco
  refine ⟨P₀, hP₀, (cls_eq_iff (pull_isLB hP₀ _) hP).1 ?_⟩
  refine Eq.trans ?_ ((cls_eq_iff hP (pull_isLB hP₀ _)).2 hiso).symm
  rw [cls_ev hP₀, evc, cls_pull hP₀, ← lift_whiskerRight, lift_fst_snd, Category.id_comp]

end GlobalTheory.PoincareDescent
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveLineBundleDescendsAlongIsogenyTorsorStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.additive_lineBundle_descends_along_isogeny_torsor : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' B N : Over (Sp K)) [GrpObj A] [GrpObj A'] [GrpObj B] [GrpObj N] (P : LB (A ⊗ B).left) (i : N ⟶ A) (q : A ⟶ A'), IsAbelianScheme A → IsAbelianScheme A' → IsAbelianScheme B → P.IsLB → IsAdditive P → Triv (ev P (𝟙 A) (1 : A ⟶ B)) → IsMonHom i → IsMonHom q → IsFinite q.left → Flat q.left → Surjective q.left → IsPullback (fst A N) (fst A N * (snd A N ≫ i)) q q → Triv (ev P (fst N B ≫ i) (snd N B)) → ∃ P₀ : LB (A' ⊗ B).left, P₀.IsLB ∧ LBIso (ev P₀ (fst A B ≫ q) (snd A B)) P := by
  first | exact @GlobalTheory.PoincareDescent.descend_torsor | exact GlobalTheory.PoincareDescent.descend_torsor | (intros; apply GlobalTheory.PoincareDescent.descend_torsor <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorSquare

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace GlobalTheory.PoincareDescent

theorem torsor_square {C : Type*} [Category C] [CartesianMonoidalCategory C] {A A' N : C} [GrpObj A] [GrpObj A']
    [GrpObj N] (i : N ⟶ A) (q : A ⟶ A') [IsMonHom q] (h : IsPullback i (toUnit N) q η[A']) :
    IsPullback (fst A N) (fst A N * (snd A N ≫ i)) q q := by
  have hiq : i ≫ q = 1 := by
    rw [h.w]; rfl
  have hdiff : ∀ {W : C} (x y : W ⟶ A), x ≫ q = y ≫ q → (x⁻¹ * y) ≫ q = toUnit W ≫ η[A'] := by
    intro W x y e
    rw [MonObj.mul_comp, GrpObj.inv_comp, e, inv_mul_cancel]; rfl
  refine ⟨⟨?_⟩, ⟨PullbackCone.IsLimit.mk _ (fun s ↦ lift s.fst (h.lift (s.fst⁻¹ * s.snd) (toUnit _)
      (hdiff _ _ s.condition))) (fun s ↦ lift_fst _ _) (fun s ↦ ?_) (fun s m h₁ h₂ ↦ ?_)⟩⟩
  · rw [MonObj.mul_comp, Category.assoc, hiq, MonObj.comp_one, _root_.mul_one]
  · rw [MonObj.comp_mul, lift_fst, lift_snd_assoc, h.lift_fst, mul_inv_cancel_left]
  · have e₁ : m ≫ fst A N = s.fst := h₁
    refine CartesianMonoidalCategory.hom_ext _ _ (by rw [e₁, lift_fst]) ?_
    rw [lift_snd]
    refine h.hom_ext ?_ (toUnit_unique _ _)
    rw [h.lift_fst, ← h₂, MonObj.comp_mul, e₁, Category.assoc, inv_mul_cancel_left]

end GlobalTheory.PoincareDescent
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareBundleDescendsQuotientFiniteSubgroup

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PoincareDescent

theorem descends : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' B N : Over (Sp K)) [GrpObj A] [GrpObj A']
    [GrpObj B] [GrpObj N] (P : LB (A ⊗ B).left) (i : N ⟶ A) (q : A ⟶ A'), IsAbelianScheme A →
    IsAbelianScheme A' → IsAbelianScheme B → IsDual A B P → IsMonHom i → IsMonHom q → IsFinite q.left →
    Flat q.left → Surjective q.left → IsPullback i (toUnit N) q η[A'] → Triv (ev P (fst N B ≫ i) (snd N B)) →
    ∃ P' : LB (A' ⊗ B).left, P'.IsLB ∧ IsAdditive P' ∧ LBIso (ev P' (fst A B ≫ q) (snd A B)) P := by
  intro K _ _ A A' B N _ _ _ _ P i q hA hA' hB hD hi hq hfin hfl hsurj hker hN
  obtain ⟨P₀, hP₀, e⟩ := GlobalTheory.T.additive_lineBundle_descends_along_isogeny_torsor K A A' B N P i q hA hA' hB hD.isLB hD.additive hD.zero hi hq hfin hfl
    hsurj (torsor_square i q hker) hN
  have key : ∀ (Y : Over (Sp K)) (a : Y ⟶ A) (b : Y ⟶ B), evc hP₀ (a ≫ q) b = evc hD.isLB a b := by
    intro Y a b
    have c := congrArg (CechPic.pull (lift a b).left) ((cls_eq_iff (pull_isLB hP₀ _) hD.isLB).2 e)
    rw [cls_ev hP₀, pull_evc, lift_fst_assoc, lift_snd] at c
    exact c
  let φ : Fin 2 → ((A' ⊗ B).left ⟶ (A' ⊗ B).left) :=
    ![(lift (fst A' B) (snd A' B)).left, (lift (fst A' B) (1 : A' ⊗ B ⟶ B)).left]
  have hP' : (LB.LinComb P₀ φ ![1, -1]).IsLB := LB.isLB_linComb hP₀ _ _
  have ev' : ∀ (Y : Over (Sp K)) (a : Y ⟶ A') (b : Y ⟶ B), evc hP' a b = evc hP₀ a b - evc hP₀ a 1 := by
    intro Y a b
    rw [evc, cls_linComb hP₀, Fin.sum_univ_two, map_add (f := _), map_zsmul, map_zsmul, ← pull_comp, ← pull_comp]
    simp only [φ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, ← Over.comp_left, comp_lift,
      lift_fst, lift_snd, MonObj.comp_one, one_smul, neg_smul, evc, sub_eq_add_neg]
  have one : ∀ (Y : Over (Sp K)) (b : Y ⟶ B), evc hP₀ (1 : Y ⟶ A') b = 0 := fun Y b ↦ by
    have : (1 : Y ⟶ A) ≫ q = 1 := by simp
    rw [← this, key]
    exact hD.additive.evc_one hD.isLB b
  refine ⟨_, hP', CubeNoeth.isAdditive_of_triv_axes hA' hB hP' ?_ ?_, ?_⟩
  · rw [triv_ev_iff hP', ev', one, one, sub_self]
  · rw [triv_ev_iff hP', ev', sub_self]
  · refine (cls_eq_iff (pull_isLB hP' _) hD.isLB).1 ?_
    rw [cls_ev hP', ev', key, key, evc_one_right hD.isLB hD.zero, sub_zero, evc, lift_fst_snd, Over.id_left,
      pull_id]

end GlobalTheory.PoincareDescent
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareBundleDescendsQuotientFiniteSubgroupStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.poincareBundle_descends_quotient_finiteSubgroup : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' B N : Over (Sp K)) [GrpObj A] [GrpObj A'] [GrpObj B] [GrpObj N] (P : LB (A ⊗ B).left) (i : N ⟶ A) (q : A ⟶ A'), IsAbelianScheme A → IsAbelianScheme A' → IsAbelianScheme B → IsDual A B P → IsMonHom i → IsMonHom q → IsFinite q.left → Flat q.left → Surjective q.left → IsPullback i (toUnit N) q η[A'] → Triv (ev P (fst N B ≫ i) (snd N B)) → ∃ P' : LB (A' ⊗ B).left, P'.IsLB ∧ IsAdditive P' ∧ LBIso (ev P' (fst A B ≫ q) (snd A B)) P := by
  first | exact @GlobalTheory.PoincareDescent.descends | exact GlobalTheory.PoincareDescent.descends | (intros; apply GlobalTheory.PoincareDescent.descends <;> assumption)
end
end
