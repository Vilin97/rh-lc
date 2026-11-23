module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftAt
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecHomExtOfLocalizationAwaySpanEqTop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareZeroLocalLiftsCorrectedAgreeOnOverlapsStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueSpecLocalizationAwayMorphisms

section

@[expose] public section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.SecGlue


open Limits in
theorem glue_away : ∀ (S : Type) [CommRing S] (ι : Type) (s : ι → S), Ideal.span (Set.range s) = ⊤ →
    ∀ (Y : Scheme.{0}) (e : ∀ i, Sp (Localization.Away (s i)) ⟶ Y),
    (∀ i j, spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (s i * s j)) (s i) (s j)) ≫ e i =
      spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (s i * s j)) (s j) (s i)) ≫ e j) →
    ∃ a : Sp S ⟶ Y, ∀ i, spMap (algebraMap S (Localization.Away (s i))) ≫ a = e i := by
  intro S _ ι s hs Y e he
  let 𝒰 := (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of S) s hs).openCover
  have hf : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ e i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ e j := by
    intro i j
    refine Scheme.Cover.hom_ext (pullback (𝒰.f i) (𝒰.f j)).affineOpenCover.openCover _ _ fun k => ?_
    let a : Spec ((pullback (𝒰.f i) (𝒰.f j)).affineOpenCover.X k) ⟶ pullback (𝒰.f i) (𝒰.f j) :=
      (pullback (𝒰.f i) (𝒰.f j)).affineOpenCover.f k
    let T := (pullback (𝒰.f i) (𝒰.f j)).affineOpenCover.X k
    let A : CommRingCat.of (Localization.Away (s i)) ⟶ T := Spec.preimage (a ≫ pullback.fst (𝒰.f i) (𝒰.f j))
    let B : CommRingCat.of (Localization.Away (s j)) ⟶ T := Spec.preimage (a ≫ pullback.snd (𝒰.f i) (𝒰.f j))
    have ea : Spec.map A = a ≫ pullback.fst (𝒰.f i) (𝒰.f j) := Spec.map_preimage _
    have eb : Spec.map B = a ≫ pullback.snd (𝒰.f i) (𝒰.f j) := Spec.map_preimage _
    have e1 : Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (s i))) ≫ A) =
        Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (s j))) ≫ B) := by
      rw [Spec.map_comp, Spec.map_comp, ea, eb]
      exact (Category.assoc _ _ _).trans ((congrArg (a ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm)
    have key : A.hom.comp (algebraMap S (Localization.Away (s i))) =
        B.hom.comp (algebraMap S (Localization.Away (s j))) :=
      congrArg CommRingCat.Hom.hom (Spec.map_injective e1)
    have hu : IsUnit ((A.hom.comp (algebraMap S (Localization.Away (s i)))) (s i * s j)) := by
      rw [map_mul]
      refine IsUnit.mul ?_ ?_
      · exact (IsLocalization.Away.algebraMap_isUnit (s i)).map A.hom
      · rw [key]; exact (IsLocalization.Away.algebraMap_isUnit (s j)).map B.hom
    let L : Localization.Away (s i * s j) →+* T := IsLocalization.Away.lift (s i * s j) hu
    have hL : L.comp (algebraMap S (Localization.Away (s i * s j))) =
        A.hom.comp (algebraMap S (Localization.Away (s i))) := IsLocalization.Away.lift_comp _ _
    have hLA : L.comp (IsLocalization.Away.awayToAwayRight (P := Localization.Away (s i * s j)) (s i) (s j)) = A.hom := by
      refine IsLocalization.ringHom_ext (Submonoid.powers (s i)) (RingHom.ext fun x => ?_)
      have := congrArg (fun f => f x) hL
      simp only [RingHom.comp_apply] at this ⊢
      rw [IsLocalization.Away.awayToAwayRight_eq, this]
    have hLB : L.comp (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (s i * s j)) (s j) (s i)) = B.hom := by
      refine IsLocalization.ringHom_ext (Submonoid.powers (s j)) (RingHom.ext fun x => ?_)
      have := congrArg (fun f => f x) (hL.trans key)
      simp only [RingHom.comp_apply] at this ⊢
      rw [IsLocalization.Away.awayToAwayLeft_eq, this]
    have hA : Spec.map A = Spec.map (CommRingCat.ofHom L) ≫
        spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (s i * s j)) (s i) (s j)) := by
      rw [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hLA]; rfl
    have hB : Spec.map B = Spec.map (CommRingCat.ofHom L) ≫
        spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (s i * s j)) (s j) (s i)) := by
      rw [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hLB]; rfl
    have h2 : Spec.map A ≫ e i = Spec.map B ≫ e j := by
      rw [hA, hB, Category.assoc, Category.assoc, he i j]
    rw [ea, eb] at h2
    exact (Category.assoc _ _ _).symm.trans (h2.trans (Category.assoc _ _ _))
  exact ⟨𝒰.glueMorphisms e hf, fun i => Scheme.Cover.ι_glueMorphisms 𝒰 e hf i⟩

end GlobalTheory.SecGlue
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueSpecLocalizationAwayMorphismsStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_glue_spec_localizationAway_morphisms : ∀ (S : Type) [CommRing S] (ι : Type) (s : ι → S), Ideal.span (Set.range s) = ⊤ →
    ∀ (Y : Scheme.{0}) (e : ∀ i, Sp (Localization.Away (s i)) ⟶ Y),
    (∀ i j, spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (s i * s j)) (s i) (s j)) ≫ e i =
      spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (s i * s j)) (s j) (s i)) ≫ e j) →
    ∃ a : Sp S ⟶ Y, ∀ i, spMap (algebraMap S (Localization.Away (s i))) ≫ a = e i := by
  first | exact @GlobalTheory.SecGlue.glue_away | exact GlobalTheory.SecGlue.glue_away | (intros; apply GlobalTheory.SecGlue.glue_away <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecHomExtOfLocalizationAwaySpanEqTopStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.specHom_ext_of_localizationAway_span_eq_top : ∀ (S : Type) [CommRing S] (ι : Type) (s : ι → S), Ideal.span (Set.range s) = ⊤ →
    ∀ (Y : Scheme.{0}) (a b : Sp S ⟶ Y),
    (∀ i, spMap (algebraMap S (Localization.Away (s i))) ≫ a = spMap (algebraMap S (Localization.Away (s i))) ≫ b) →
    a = b := by
  first | exact @GlobalTheory.SecGlue.hom_ext_of_span_eq_top | exact GlobalTheory.SecGlue.hom_ext_of_span_eq_top | (intros; apply GlobalTheory.SecGlue.hom_ext_of_span_eq_top <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalLiftOfChartLocalLiftsSquareZero

section

@[expose] public section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SecGlue

theorem exists_lift_of_chart_lifts : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ →
    ∀ (X : Over (Sp R)), Smooth X.hom → ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ (κ : Type) [Finite κ] (f : κ → R), Ideal.span (Set.range f) = ⊤ → ∀ V : κ → X.left.Opens, (∀ k, IsAffineOpen (V k)) →
    (∀ k, GlobalTheory.SecLift.LiftIn π X g₀ (f k) (V k)) → ∃ e : Sp R ⟶ X.left, e ≫ X.hom = 𝟙 _ ∧ spMap π ≫ e = g₀ := by
  intro R R₀ _ _ π hπ hI X hX g₀ hg₀ κ _ f hf V hV hL
  obtain ⟨e, he1, he2, he3⟩ := GlobalTheory.T.squareZero_local_lifts_corrected_agree_on_overlaps R R₀ π hπ hI X hX g₀ hg₀ κ f hf V hV hL
  obtain ⟨E, hE⟩ := GlobalTheory.T.exists_glue_spec_localizationAway_morphisms R κ f hf X.left e he3
  refine ⟨E, ?_, ?_⟩
  · refine GlobalTheory.T.specHom_ext_of_localizationAway_span_eq_top R κ f hf (Sp R) _ _ (fun k => ?_)
    rw [← Category.assoc, hE k, he1 k, Category.comp_id]
  · have hf₀ : Ideal.span (Set.range (fun k => π (f k))) = ⊤ := by
      rw [show (fun k => π (f k)) = π ∘ f from rfl, Set.range_comp, ← Ideal.map_span, hf, Ideal.map_top]
    refine GlobalTheory.T.specHom_ext_of_localizationAway_span_eq_top R₀ κ (fun k => π (f k)) hf₀ X.left _ _ (fun k => ?_)
    rw [← he2 k, ← hE k, ← Category.assoc, ← Category.assoc]
    congr 1
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact (IsLocalization.map_comp _).symm

end GlobalTheory.SecGlue
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalLiftOfChartLocalLiftsSquareZeroStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_global_lift_of_chartLocal_lifts_squareZero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ →
    ∀ (X : Over (Sp R)), Smooth X.hom → ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ (κ : Type) [Finite κ] (f : κ → R), Ideal.span (Set.range f) = ⊤ → ∀ V : κ → X.left.Opens, (∀ k, IsAffineOpen (V k)) →
    (∀ k, GlobalTheory.SecLift.LiftIn π X g₀ (f k) (V k)) → ∃ e : Sp R ⟶ X.left, e ≫ X.hom = 𝟙 _ ∧ spMap π ≫ e = g₀ := by
  first | exact @GlobalTheory.SecGlue.exists_lift_of_chart_lifts | exact GlobalTheory.SecGlue.exists_lift_of_chart_lifts | (intros; apply GlobalTheory.SecGlue.exists_lift_of_chart_lifts <;> assumption)
end
end
