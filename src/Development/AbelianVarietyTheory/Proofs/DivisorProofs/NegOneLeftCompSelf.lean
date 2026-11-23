module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyExistsAmpleClass
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
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyAmpleClassCechPicardClassIffAmpleStatement
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyExistsAmpleClassStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianVariety_exists_ampleClass : ∀ (K : Type) [Field K] (A : AbVar K), ∃ c : Pic A.X.left, IsAmpleCls c := by
  first | exact @GlobalTheory.AV.exists_isAmpleCls | exact GlobalTheory.AV.exists_isAmpleCls | (intros; apply GlobalTheory.AV.exists_isAmpleCls <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianVarietyAmpleClassAdd

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV

theorem isAmpleCls_add : ∀ (K : Type) [Field K] (A : AbVar K) (c d : Pic A.X.left),
    IsAmpleCls c → IsAmpleCls d → IsAmpleCls (c + d) := by
  intro K _ A c d hc hd
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  obtain ⟨M, hM, rfl⟩ := cls_surj d
  have hA : IsAmpleLB L := (GlobalTheory.T.abelianVarietyAmpleClass_cechPicardClass_iff_ample K A L hL).1 hc
  have hB : IsAmpleLB M := (GlobalTheory.T.abelianVarietyAmpleClass_cechPicardClass_iff_ample K A M hM).1 hd
  have hN : (tens L M).IsLB := isLB_tens hL hM
  have hT : IsAmpleLB (tens L M) := by
    refine hA.tensor hB hN ((cls_eq_zero_iff (LB.isLB_div (LB.isLB_div hN hL) hM)).1 ?_)
    rw [cls_div (LB.isLB_div hN hL) hM, cls_div hN hL, cls_tens hL hM]
    abel
  rw [← cls_tens hL hM hN]
  exact (GlobalTheory.T.abelianVarietyAmpleClass_cechPicardClass_iff_ample K A (tens L M) hN).2 hT

end GlobalTheory.AV
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianVarietyAmpleClassAddStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isAbelianVarietyAmpleClass_add : ∀ (K : Type) [Field K] (A : AbVar K) (c d : Pic A.X.left), IsAmpleCls c → IsAmpleCls d → IsAmpleCls (c + d) := by
  first | exact @GlobalTheory.AV.isAmpleCls_add | exact GlobalTheory.AV.isAmpleCls_add | (intros; apply GlobalTheory.AV.isAmpleCls_add <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianVarietyAmpleClassPullbackOfIsFinite

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem isAmpleCls_pull_of_isFinite : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B) (d : Pic B.X.left),
    IsFinite f.hom.left → IsAmpleCls d → IsAmpleCls (CechPic.pull f.hom.left d) := by
  intro K _ A B f d hf hd
  obtain ⟨L, hL, hrel, rfl⟩ := hd
  have hB : IsAmpleLB L := (GlobalTheory.T.abelianVarietyAmpleClass_cechPicardClass_iff_ample K B L hL).1 ⟨L, hL, hrel, rfl⟩
  have hA : IsAmpleLB (L.pull f.hom.left) := hB.pull_of_isAffineHom f.hom.left
  have h := (GlobalTheory.T.abelianVarietyAmpleClass_cechPicardClass_iff_ample K A (L.pull f.hom.left) hA.isLB).2 hA
  rwa [cls_pull hL f.hom.left hA.isLB] at h

end GlobalTheory.AV.AbVar
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianVarietyAmpleClassPullbackOfIsFiniteStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isAbelianVarietyAmpleClass_pullback_of_isFinite : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B) (d : Pic B.X.left), IsFinite f.hom.left → IsAmpleCls d → IsAmpleCls (CechPic.pull f.hom.left d) := by
  first | exact @GlobalTheory.AV.AbVar.isAmpleCls_pull_of_isFinite | exact GlobalTheory.AV.AbVar.isAmpleCls_pull_of_isFinite | (intros; apply GlobalTheory.AV.AbVar.isAmpleCls_pull_of_isFinite <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegOneLeftCompSelf

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem neg_one_left_comp_self {K : Type} [Field K] (A : AbVar K) :
    (Hom.hom (-(𝟙 A))).left ≫ (Hom.hom (-(𝟙 A))).left = 𝟙 A.X.left := by
  have h : (-(𝟙 A)) ≫ (-(𝟙 A)) = 𝟙 A := by
    rw [Preadditive.neg_comp, Preadditive.comp_neg, neg_neg, Category.id_comp]
  have h2 := congrArg (fun g : A ⟶ A => (Hom.hom g).left) h
  simpa only [comp_hom, Over.comp_left, id_hom, Over.id_left] using h2

theorem exists_symm_ample :
    ∀ (K : Type) [Field K] (A : AbVar K), ∃ c : Pic A.X.left, IsAmpleCls c ∧ CechPic.pull (Hom.hom (-(𝟙 A))).left c = c := by
  intro K _ A
  obtain ⟨c₀, hc₀⟩ := GlobalTheory.T.abelianVariety_exists_ampleClass K A
  set f : A.X.left ⟶ A.X.left := (Hom.hom (-(𝟙 A))).left with hf
  have hff : f ≫ f = 𝟙 A.X.left := neg_one_left_comp_self A
  have hiso : IsIso f := ⟨⟨f, hff, hff⟩⟩
  have hfin : IsFinite (Hom.hom (-(𝟙 A))).left := by
    rw [← hf]; infer_instance
  refine ⟨c₀ + CechPic.pull f c₀, GlobalTheory.T.isAbelianVarietyAmpleClass_add K A _ _ hc₀ (GlobalTheory.T.isAbelianVarietyAmpleClass_pullback_of_isFinite K A A (-(𝟙 A)) c₀ hfin hc₀), ?_⟩
  rw [map_add (f := _), ← CechPic.pull_comp, hff, CechPic.pull_id, add_comm]

end GlobalTheory.AV.AbVar
end
end
