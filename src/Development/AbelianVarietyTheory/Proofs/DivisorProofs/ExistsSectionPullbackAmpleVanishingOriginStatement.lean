module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleSectionsVanishingOriginSeparatingStatement
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
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

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyHomExtPoints

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem ext_of_pt_eq : ∀ (K : Type) [Field K] (A B : AbVar K) (f g : A ⟶ B),
    (∀ x : A.Pt, x ≫ f.hom = x ≫ g.hom) → f = g := by
  intro K _ A B f g h
  have := A.ab.smooth
  have := B.ab.proper
  have : IsReduced A.X.left := GlobalTheory.isReduced_of_smooth_of_isReduced A.X.hom
  let Ω := AlgebraicClosure K
  let q : Sp Ω ⟶ Sp K := spMap (algebraMap K Ω)
  have : Surjective q := ⟨fun x => ⟨IsLocalRing.closedPoint Ω, Subsingleton.elim _ _⟩⟩
  have : JacobsonSpace ↥(pullback A.X.hom q) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.snd A.X.hom q)
  have hd : Dense (closedPoints ↥(pullback A.X.hom q)) := dense_iff_closure_eq.2 closure_closedPoints
  have hD := (pullback.fst A.X.hom q).surjective.denseRange.dense_image
    (pullback.fst A.X.hom q).continuous hd
  have hdom : IsDominant (equalizer.ι f.hom.left g.hom.left) := by
    refine ⟨hD.mono ?_⟩
    rintro _ ⟨w, hw₀, rfl⟩
    have hw : IsClosed ({w} : Set ↥(pullback A.X.hom q)) := hw₀
    let y : Sp Ω ⟶ A.X.left :=
      pointOfClosedPoint (pullback.snd A.X.hom q) w hw ≫ pullback.fst A.X.hom q
    have hy : y ≫ A.X.hom = q := by
      simp only [y, Category.assoc, pullback.condition]
      rw [← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]
    let x : A.Pt := Over.homMk y hy
    have hx : y ≫ f.hom.left = y ≫ g.hom.left := congrArg CommaMorphism.left (h x)
    refine ⟨equalizer.lift y hx (IsLocalRing.closedPoint Ω), ?_⟩
    change (equalizer.lift y hx ≫ equalizer.ι f.hom.left g.hom.left) (IsLocalRing.closedPoint Ω) = _
    rw [equalizer.lift_ι]
    exact congrArg (pullback.fst A.X.hom q) (pointOfClosedPoint_apply (pullback.snd A.X.hom q) w hw _)
  have : IsDominant (equalizer.ι f.hom.left g.hom.left) := hdom
  have heq : f.hom = g.hom := Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated B.X.hom
    ((Over.w f.hom).trans (Over.w g.hom).symm) (equalizer.ι _ _) (equalizer.condition _ _))
  exact Subtype.ext heq

end GlobalTheory.AV.AbVar
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApplyNeOrigin

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem eq_comp_section_of_apply_eq {K L : Type} [Field K] [Field L] {X : Scheme.{0}} (t : X ⟶ Sp K)
    (e : Sp K ⟶ X) (he : e ≫ t = 𝟙 _) (q : Sp L ⟶ Sp K) (y : Sp L ⟶ X) (hy : y ≫ t = q)
    (p : Sp L) (p' : Sp K) (h : y p = e p') : y = q ≫ e := by
  obtain ⟨⟨z, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField L X).symm.surjective y
  obtain ⟨⟨z', α⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective e
  simp only [Scheme.SpecToEquivOfField_symm_apply] at he hy h ⊢
  have hz : z = z' := by simpa using h
  subst hz
  obtain ⟨c, hc⟩ := Spec.map_surjective (X.fromSpecResidueField z ≫ t)
  rw [Category.assoc, ← hc, ← Spec.map_comp, ← Spec.map_id] at he
  rw [Category.assoc, ← hc, ← Spec.map_comp] at hy
  have h₁ := Spec.map_injective he
  have e₁ : ∀ k, α.hom (c.hom k) = k := fun k => congrArg (fun r => r.hom k) h₁
  subst hy
  rw [← Category.assoc, ← Spec.map_comp]
  congr 1
  congr 1
  ext w
  have e₂ : c.hom (α.hom w) = w := α.hom.injective (e₁ _)
  simp [e₂]

theorem exists_apply_ne_origin : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), f ≠ 0 →
    ∃ a : A.X.left, f.hom.left a ≠ B.origin := by
  intro K _ A B f hf
  by_contra hcon
  push_neg at hcon
  apply hf
  refine ext_of_pt_eq K A B f 0 fun x => ?_
  rw [zero_hom]
  let e : Sp K ⟶ B.X.left := (1 : Over.mk (𝟙 (Sp K)) ⟶ B.X).left
  have he : e ≫ B.X.hom = 𝟙 _ := Over.w (1 : Over.mk (𝟙 (Sp K)) ⟶ B.X)
  have h1 : (x ≫ (1 : A.X ⟶ B.X)).left = (ptOver K (AlgebraicClosure K)).hom ≫ e := by
    have hP : (toUnit (ptOver K (AlgebraicClosure K))).left = (ptOver K (AlgebraicClosure K)).hom := by
      simpa using Over.w (toUnit (ptOver K (AlgebraicClosure K)))
    have hU : toUnit (Over.mk (𝟙 (Sp K))) = 𝟙 _ := toUnit_unique _ _
    simp only [e, Hom.one_def, ← Category.assoc, comp_toUnit, hU, Category.id_comp, Over.comp_left, hP]
  apply Over.OverMorphism.ext
  rw [h1]
  exact eq_comp_section_of_apply_eq B.X.hom e he _ _ (Over.w (x ≫ f.hom))
    (IsLocalRing.closedPoint _) (IsLocalRing.closedPoint K) (hcon _)

end GlobalTheory.AV.AbVar
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApplyNeOriginStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_apply_ne_origin' : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), f ≠ 0 → ∃ a : A.X.left, f.hom.left a ≠ B.origin := by
  first | exact @GlobalTheory.AV.AbVar.exists_apply_ne_origin | exact GlobalTheory.AV.AbVar.exists_apply_ne_origin | (intros; apply GlobalTheory.AV.AbVar.exists_apply_ne_origin <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPullbackAmpleVanishingOrigin

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem hom_left_origin {K : Type} [Field K] {A B : AbVar K} (f : A ⟶ B) : f.hom.left A.origin = B.origin := by
  have e : (1 : Over.mk (𝟙 (Sp K)) ⟶ A.X) ≫ f.hom = 1 := by
    rw [CategoryTheory.Hom.one_def, CategoryTheory.Hom.one_def, Category.assoc, IsMonHom.one_hom]
  unfold origin
  rw [← e, Over.comp_left]
  rfl

theorem exists_sec_pull_ample_vanish_origin : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B) (d : Pic B.X.left),
    IsAmpleCls d → f ≠ 0 → ∃ (m : ℕ) (M : LB A.X.left) (hM : M.IsLB) (s : LB.Sec M), 0 < m ∧
      cls M hM = m • CechPic.pull f.hom.left d ∧ Out.nonzeroLocus s ≠ ⊥ ∧ A.origin ∉ Out.nonzeroLocus s := by
  intro K _ A B f d hd hf
  obtain ⟨L, hL, amp, rfl⟩ := hd
  obtain ⟨N, hN, M, t, h0, h1⟩ := GlobalTheory.T.exists_ampleSections_vanishing_origin_separating K B L hL amp
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_apply_ne_origin' K A B f hf
  let ιB := (B.X.hom ⁻¹ᵁ ⊤).ι
  let h : A.X.left ⟶ (B.X.hom ⁻¹ᵁ ⊤).toScheme := IsOpenImmersion.lift ιB f.hom.left (by
    rw [Scheme.Opens.range_ι]; intro x _; trivial)
  have hh : h ≫ ιB = f.hom.left := IsOpenImmersion.lift_fac _ _ _
  have hpt : ∀ x, ιB (h x) = f.hom.left x := fun x => by rw [← hh]; rfl
  obtain ⟨j, hj⟩ := h1 (h a) (by rw [hpt]; exact ha)
  let s := ReciprocityTheory.ChartRestriction.G.DVR.pullSec L (fun _ : Fin N => ιB) (fun _ => 1) (t j) h
  have hs : Out.nonzeroLocus s = h ⁻¹ᵁ Out.nonzeroLocus (t j) := GlobalTheory.nonzeroLocus_pullSec _ _ (t j) h
  refine ⟨N, _, LB.isLB_linComb hL _ _, s, hN, ?_, ?_, ?_⟩
  · rw [cls_linComb hL]
    simp only [hh, one_zsmul, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  · intro e
    have : a ∈ Out.nonzeroLocus s := by rw [hs]; exact hj
    rw [e] at this; exact this
  · intro ho
    rw [hs] at ho
    exact h0 j (h A.origin) (by rw [hpt, hom_left_origin]) ho

end GlobalTheory.AV.AbVar
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPullbackAmpleVanishingOriginStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_section_pullbackAmple_vanishing_origin : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B) (d : Pic B.X.left), IsAmpleCls d → f ≠ 0 → ∃ (m : ℕ) (M : LB A.X.left) (hM : M.IsLB) (s : LB.Sec M), 0 < m ∧ cls M hM = m • CechPic.pull f.hom.left d ∧ Out.nonzeroLocus s ≠ ⊥ ∧ A.origin ∉ Out.nonzeroLocus s := by
  first | (exact @GlobalTheory.AV.AbVar.exists_sec_pull_ample_vanish_origin) | (exact GlobalTheory.AV.AbVar.exists_sec_pull_ample_vanish_origin) | (intros; apply GlobalTheory.AV.AbVar.exists_sec_pull_ample_vanish_origin  <;> assumption)
end
end
