module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyMumfordClassSymmNaturalAdditive

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV

theorem lam_symm_nat_add : ∀ (K : Type) [Field K] (A B : AbVar K) (c c' : Pic A.X.left) (d : Pic B.X.left) (f : A ⟶ B) (Y Z : Over (Sp K)) (u : Z ⟶ Y) (x y : Y ⟶ A.X), AbVar.lam c x y = AbVar.lam c y x ∧ CechPic.pull u.left (AbVar.lam c x y) = AbVar.lam c (u ≫ x) (u ≫ y) ∧ AbVar.lam d (x ≫ f.hom) (y ≫ f.hom) = AbVar.lam (CechPic.pull f.hom.left d) x y ∧ AbVar.lam (c + c') x y = AbVar.lam c x y + AbVar.lam c' x y := by
  intro K _ A B c c' d f Y Z u x y
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [AbVar.lam_eq, AbVar.lam_eq]; exact CechPic.lam_comm c x y
  · rw [AbVar.lam_eq, AbVar.lam_eq]; exact CechPic.pull_lam u c x y
  · rw [AbVar.lam_eq, AbVar.lam_eq]; exact (CechPic.lam_pull f.hom d x y).symm
  · simp only [AbVar.lam, map_add (f := _)]; abel

end GlobalTheory.AV
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyMumfordClassSymmNaturalAdditiveStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianVarietyMumfordClass_symm_natural_additive : ∀ (K : Type) [Field K] (A B : AbVar K) (c c' : Pic A.X.left) (d : Pic B.X.left) (f : A ⟶ B) (Y Z : Over (Sp K)) (u : Z ⟶ Y) (x y : Y ⟶ A.X), AbVar.lam c x y = AbVar.lam c y x ∧ CechPic.pull u.left (AbVar.lam c x y) = AbVar.lam c (u ≫ x) (u ≫ y) ∧ AbVar.lam d (x ≫ f.hom) (y ≫ f.hom) = AbVar.lam (CechPic.pull f.hom.left d) x y ∧ AbVar.lam (c + c') x y = AbVar.lam c x y + AbVar.lam c' x y := by
  first | (exact @GlobalTheory.AV.lam_symm_nat_add) | (exact GlobalTheory.AV.lam_symm_nat_add) | (intros; apply GlobalTheory.AV.lam_symm_nat_add  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointUniqueAdditiveScalar

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar.AdjCalc

variable {K : Type} [Field K]

theorem comp_zpow' {X Y G : Over (Sp K)} [GrpObj G] (f : X ⟶ Y) (g : Y ⟶ G) (m : ℤ) :
    f ≫ g ^ m = (f ≫ g) ^ m :=
  map_zpow (MonoidHom.mk' (fun g : Y ⟶ G => f ≫ g) (MonObj.comp_mul f)) g m

theorem isAdj_pt {A B : AbVar K} {c : Pic A.X.left} {d : Pic B.X.left} {f : A ⟶ B} {n : ℤ} {h : B ⟶ A}
    (H : IsAdj c d f n h) {Y : Over (Sp K)} (x : Y ⟶ A.X) (y : Y ⟶ B.X) :
    n • lam d (x ≫ f.hom) y = lam c x (y ≫ h.hom) := by
  have H' := congrArg (CechPic.pull (lift x y).left) H
  rw [map_zsmul, (GlobalTheory.T.abelianVarietyMumfordClass_symm_natural_additive K A A c c c (𝟙 A) _ Y (lift x y) _ _).2.1,
    (GlobalTheory.T.abelianVarietyMumfordClass_symm_natural_additive K B B d d d (𝟙 B) _ Y (lift x y) _ _).2.1] at H'
  simpa only [lift_fst_assoc, lift_snd_assoc, lift_fst, lift_snd] using H'

end GlobalTheory.AV.AbVar.AdjCalc
end
end
