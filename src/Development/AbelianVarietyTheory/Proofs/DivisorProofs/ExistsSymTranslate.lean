module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsGenThetaOfIsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusExtensionPointsDivisible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointPicardClassEqTranslateOfTrivialLambda
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
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRigidTranslatePrincipalPolarisationOrderTw
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelTrivialRigidTranslateLineBundle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleRigidTranslateLineBundleRationalPoint
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.RigidifiedSymDescendToSubring
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointPrimitiveBundleEqTranslatePpav
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolarisationFormIntPolynomialBundles
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointPrimitiveBundleEqTranslatePpav
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointPicardClassEqTranslateOfTrivialLambdaStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open MonoidalCategory CartesianMonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic (Pic cls lam)

theorem _root_.GlobalTheory.T.exists_point_picardClass_eq_translate_of_trivial_lambda : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ (L : LB B.left) (hL : L.IsLB), Out.KTriv B L → ∀ (O : LB B.left) (hO : O.IsLB), lam (cls O hO) (fst B B) (snd B B) = 0 → ∃ x : 𝟙_ (Over (Sp K)) ⟶ B, cls O hO = lam (cls L hL) (toUnit B ≫ x) (𝟙 B) := by
  first | exact @GlobalTheory.PointTranslate.exists_point_cls_eq_lam | exact GlobalTheory.PointTranslate.exists_point_cls_eq_lam | (intros; apply GlobalTheory.PointTranslate.exists_point_cls_eq_lam <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelTrivialRigidTranslateLineBundleStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open MonoidalCategory CartesianMonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic (Pic cls lam)

theorem _root_.GlobalTheory.T.kernelTrivial_rigidTranslateLineBundle : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (L : LB A.left), L.IsLB → ∀ a : 𝟙_ (Over S) ⟶ A, Out.KTriv A L → Out.KTriv A (GlobalTheory.RigidTranslate.rigTransl L a) := by
  first | exact @GlobalTheory.RigidTranslate.kTriv_rigTransl_any | exact GlobalTheory.RigidTranslate.kTriv_rigTransl_any | (intros; apply GlobalTheory.RigidTranslate.kTriv_rigTransl_any <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleRigidTranslateLineBundleRationalPointStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open MonoidalCategory CartesianMonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic (Pic cls lam)

theorem _root_.GlobalTheory.T.relAmple_rigidTranslateLineBundle_rationalPoint : ∀ (K : Type) [Field K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ (L : LB B.left), L.IsLB → ∀ a : 𝟙_ (Over (Sp K)) ⟶ B, Out.RelAmple B L → Out.RelAmple B (GlobalTheory.RigidTranslate.rigTransl L a) := by
  first | exact @GlobalTheory.RigidTranslate.relAmple_rigTransl_point | exact GlobalTheory.RigidTranslate.relAmple_rigTransl_point | (intros; apply GlobalTheory.RigidTranslate.relAmple_rigTransl_point <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricRigidTranslateLineBundleOfSquareDefect

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open MonoidalCategory CartesianMonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic (Pic cls lam)

noncomputable section

namespace GlobalTheory.SymTranslate

theorem sym_rigTransl_of_sq : ∀ (K : Type) [Field K] (B : Over (Sp K)) [GrpObj B] [IsCommMonObj B] (L : LB B.left) (hL : L.IsLB), (∃ t : LB.Gen (Theta B L), t.IsGen) → ∀ a : 𝟙_ (Over (Sp K)) ⟶ B, CechPic.pull (GrpObj.inv : B ⟶ B).left (cls L hL) - cls L hL = lam (cls L hL) (toUnit B ≫ a ^ 2) (𝟙 B) → Out.Sym B (GlobalTheory.RigidTranslate.rigTransl L a) := by
  intro K _ B _ _ L hL _ a h
  have hc : ∀ x : 𝟙_ (Over (Sp K)) ⟶ B, CechPic.pull (toUnit B ≫ x).left (cls L hL) = 0 := fun x => by
    rw [Over.comp_left, CechPic.pull_comp,
      GlobalTheory.PrimitiveOverField.pic_field (CechPic.pull x.left (cls L hL))]
    exact map_zero _
  have h1 : CechPic.pull (1 : B ⟶ B).left (cls L hL) = 0 := hc _
  have h2 : CechPic.pull (GrpObj.inv : B ⟶ B).left (cls L hL) =
      CechPic.pull ((toUnit B ≫ a ^ 2) * 𝟙 B).left (cls L hL) := by
    rw [lam, hc, h1, Over.id_left, CechPic.pull_id, sub_zero, add_zero] at h
    exact sub_left_injective h
  have h3 := congrArg (CechPic.pull (𝟙 B * (toUnit B ≫ a)⁻¹).left) h2
  rw [← CechPic.pull_comp, ← CechPic.pull_comp, ← Over.comp_left, ← Over.comp_left] at h3
  have e1 : (𝟙 B * (toUnit B ≫ a)⁻¹) ≫ (GrpObj.inv : B ⟶ B) =
      (GrpObj.inv : B ⟶ B) ≫ (𝟙 B * (toUnit B ≫ a)) := by
    rw [← Hom.inv_def, MonObj.comp_mul, ← Category.assoc, comp_toUnit, Category.comp_id, mul_inv, inv_inv,
      Hom.inv_def, Category.id_comp]
  have e2 : (𝟙 B * (toUnit B ≫ a)⁻¹) ≫ ((toUnit B ≫ a ^ 2) * 𝟙 B) = 𝟙 B * (toUnit B ≫ a) := by
    rw [MonObj.comp_mul, ← Category.assoc, comp_toUnit, Category.comp_id, MonObj.comp_pow, sq,
      _root_.mul_comm (𝟙 B), _root_.mul_comm (𝟙 B), _root_.mul_assoc, mul_inv_cancel_left]
  rw [e1, e2, Over.comp_left, CechPic.pull_comp] at h3
  have hL' : (GlobalTheory.RigidTranslate.rigTransl L a).IsLB := LB.isLB_linComb hL _ _
  have h4 : cls _ hL' = CechPic.pull (𝟙 B * (toUnit B ≫ a)).left (cls L hL) := by
    rw [CechPic.cls_linComb hL, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hc, smul_zero, add_zero, one_smul]
    rfl
  exact GlobalTheory.RigSymSubring.sym_of_cls hL' (by rw [h4]; exact h3)

end GlobalTheory.SymTranslate
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricRigidTranslateLineBundleOfSquareDefectStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open MonoidalCategory CartesianMonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic (Pic cls lam)

theorem _root_.GlobalTheory.T.symmetric_rigidTranslateLineBundle_of_square_defect : ∀ (K : Type) [Field K] (B : Over (Sp K)) [GrpObj B] [IsCommMonObj B] (L : LB B.left) (hL : L.IsLB), (∃ t : LB.Gen (Theta B L), t.IsGen) → ∀ a : 𝟙_ (Over (Sp K)) ⟶ B, CechPic.pull (GrpObj.inv : B ⟶ B).left (cls L hL) - cls L hL = lam (cls L hL) (toUnit B ≫ a ^ 2) (𝟙 B) → Out.Sym B (GlobalTheory.RigidTranslate.rigTransl L a) := by
  first | exact @GlobalTheory.SymTranslate.sym_rigTransl_of_sq | exact GlobalTheory.SymTranslate.sym_rigTransl_of_sq | (intros; apply GlobalTheory.SymTranslate.sym_rigTransl_of_sq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymTranslate

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

open MonoidalCategory CartesianMonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic (Pic cls lam)
noncomputable section
namespace GlobalTheory.RiemannExists

theorem exists_sym_translate : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ (L : LB B.left) (hL : L.IsLB), Out.RelAmple B L → Out.KTriv B L → ∃ (L' : LB B.left) (hL' : L'.IsLB), Out.Rigidified B L' ∧ Out.Sym B L' ∧ Out.RelAmple B L' ∧ Out.KTriv B L' ∧ lam (cls L' hL') (fst B B) (snd B B) = lam (cls L hL) (fst B B) (snd B B) := by
  intro K _ _ B _ hB L hL ha hk
  have := hB.comm
  obtain ⟨c, hc⟩ := exists_gen_theta_of_isAbelianScheme K B hB L hL
  have hΘ : ∃ t : LB.Gen (Theta B L), t.IsGen := ⟨c, hc⟩
  obtain ⟨O, hO, eO⟩ := CechPic.cls_surj (CechPic.pull (GrpObj.inv : B ⟶ B).left (cls L hL) - cls L hL)
  have hlam : lam (cls O hO) (fst B B) (snd B B) = 0 := by
    rw [eO, PrimitiveOverField.lam_sub, CechPic.lam_pull, ← Hom.inv_def, ← Hom.inv_def,
      FormPoly.lam_inv_left hL hΘ, FormPoly.lam_inv_right hL hΘ, neg_neg, sub_self]
  obtain ⟨b, hb⟩ := GlobalTheory.T.exists_point_picardClass_eq_translate_of_trivial_lambda K B hB L hL hk O hO hlam
  obtain ⟨a, hab⟩ := SS.SemiDivisible.pow_surj_abelian K B hB (n := 2) (by norm_num) b
  have hL' : (RigidTranslate.rigTransl L a).IsLB := DVR.linComb_isLB _ hL _ _
  refine ⟨_, hL', RigidTranslate.rigidified_rigTransl hL, GlobalTheory.T.symmetric_rigidTranslateLineBundle_of_square_defect K B L hL hΘ a (by rw [← eO, hb, hab]),
    GlobalTheory.T.relAmple_rigidTranslateLineBundle_rationalPoint K B hB L hL a ha, GlobalTheory.T.kernelTrivial_rigidTranslateLineBundle _ B L hL a hk, ?_⟩
  have e := (CechPic.cls_eq_iff (LB.isLB_linComb hL' _ _) (pull_isLB (LB.isLB_linComb hL _ _) _)).2
    (RigidTranslate.lam_rigTransl (t := a) hL c hc)
  rw [CechPic.cls_pull (LB.isLB_linComb hL _ _), CechPic.pull_id] at e
  exact (CechPic.cls_cube_two hL' _ _ _).symm.trans (e.trans (CechPic.cls_cube_two hL _ _ _))

end GlobalTheory.RiemannExists
end
end
end
