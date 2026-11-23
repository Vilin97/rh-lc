module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecRatioEqRefl
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningMorphismsAgreeBeyondThresholdStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermRatioAgreeSelf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSectionRatioEqNearThickeningPointStatement
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfIsDominant

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupMorphismsAgreeNearPoint

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.LocAgree

theorem gs_prod {X Y : Scheme.{0}} {L : LB X} {k : ℕ} (u v : Y ⟶ X) (i i' : Fin 1 → L.ι) (y : Y)
    (hi : u y ∈ secChart L i) (hi' : v y ∈ secChart L i') (s t : H0 L k) :
    gs (𝟙 Y) y (u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i')
        ((Y.presheaf.map (homOfLE (inf_le_left : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤ u ⁻¹ᵁ secChart L i)).op).hom
          ((u.app (secChart L i)).hom (s.f i)) *
        (Y.presheaf.map (homOfLE (inf_le_right : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤ v ⁻¹ᵁ secChart L i')).op).hom
          ((v.app (secChart L i')).hom (t.f i'))) = secGerm u y s i * secGerm v y t i' := by
  have hy : (𝟙 Y : Y ⟶ Y) y ∈ u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' := ⟨hi, hi'⟩
  rw [gs_mul _ _ _ hy, gs_res _ _ _ hy, gs_res _ _ _ hy]
  exact congrArg₂ (· * ·) (gs_pull (𝟙 Y) u y _ hi _) (gs_pull (𝟙 Y) v y _ hi' _)

theorem gs_nbhd {Z : Scheme.{0}} {O : Z.Opens} (a b : Γ(Z, O)) (z : Z) (hz : z ∈ O)
    (h : gs (𝟙 Z) z O a = gs (𝟙 Z) z O b) :
    ∃ V : Z.Opens, z ∈ V ∧ V ≤ O ∧ ∀ x ∈ V, gs (𝟙 Z) x O a = gs (𝟙 Z) x O b := by
  rw [gs_eq _ z O hz, gs_eq _ z O hz] at h
  obtain ⟨V, hzV, iU, iV, e⟩ := TopCat.Presheaf.germ_eq Z.presheaf z hz hz _ _ h
  refine ⟨V, hzV, leOfHom iU, fun x hx => ?_⟩
  have hxO : (𝟙 Z : Z ⟶ Z) x ∈ O := leOfHom iU hx
  rw [gs_eq _ x O hxO, gs_eq _ x O hxO]
  exact (TopCat.Presheaf.germ_res_apply Z.presheaf iU x hx _).symm.trans
    ((congrArg (Z.presheaf.germ V x hx).hom e).trans (TopCat.Presheaf.germ_res_apply Z.presheaf iV x hx _))

end GlobalTheory.Mum.LocAgree

namespace GlobalTheory.Mum.LocAgree

theorem locAgree : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∀ (e k : ℕ), k₀ ≤ k → ∀ (Z : Scheme.{0}) (u u' : Z ⟶ (thickObj R (maximalIdeal R) e G).left), u ≫ (thickObj R (maximalIdeal R) e G).hom = u' ≫ (thickObj R (maximalIdeal R) e G).hom → ∀ (s₀ : H0 U.LG.L k) (i i'' : Fin 1 → U.LG.L.ι) (z : Z), GermRatioAgree (u ≫ (fstG (maximalIdeal R) e G).left) (u' ≫ (fstG (maximalIdeal R) e G).left) s₀ i i'' z → u z = u' z → ∃ W : Z.Opens, z ∈ W ∧ W.ι ≫ u = W.ι ≫ u' := by
  intro R _ _ _ hB D A G _ _ hG U
  obtain ⟨k₀, hk₀, hK⟩ := GlobalTheory.T.eq_of_sectionRatio_eq_near_thickening_point R hB D A G hG U
  refine ⟨k₀, hk₀, fun e k hk Z u u' hu s₀ i i'' z hg hz => ?_⟩
  obtain ⟨hi, hi'', hunit, hunit', hall⟩ := hg
  set p := (fstG (maximalIdeal R) e G).left with hp
  have hiw : p (u z) ∈ secChart U.LG.L i := hi
  have hunitw : IsUnit (secGerm p (u z) s₀ i) := by
    rw [secGerm_comp u p z s₀ hiw] at hunit
    exact (isUnit_map_iff (u.stalkMap z).hom _).1 hunit
  obtain ⟨N, m, σ, hwN, hmono⟩ := hK e k hk s₀ i (u z) hiw hunitw

  have hz' : z ∈ (u ≫ p) ⁻¹ᵁ secChart U.LG.L i ⊓ (u' ≫ p) ⁻¹ᵁ secChart U.LG.L i'' := ⟨hi, hi''⟩
  have hV : ∀ l, ∃ V : Z.Opens, z ∈ V ∧ V ≤ (u ≫ p) ⁻¹ᵁ secChart U.LG.L i ⊓ (u' ≫ p) ⁻¹ᵁ secChart U.LG.L i'' ∧
      ∀ x ∈ V, secGerm (u ≫ p) x (σ l) i * secGerm (u' ≫ p) x s₀ i'' =
        secGerm (u ≫ p) x s₀ i * secGerm (u' ≫ p) x (σ l) i'' := by
    intro l
    obtain ⟨V, hzV, hVO, hx⟩ := gs_nbhd _ _ z hz'
      ((gs_prod (u ≫ p) (u' ≫ p) i i'' z hi hi'' (σ l) s₀).trans ((hall (σ l)).trans
        (gs_prod (u ≫ p) (u' ≫ p) i i'' z hi hi'' s₀ (σ l)).symm))
    refine ⟨V, hzV, hVO, fun x hxV => ?_⟩
    have hxO := hVO hxV
    rw [← gs_prod (u ≫ p) (u' ≫ p) i i'' x hxO.1 hxO.2, ← gs_prod (u ≫ p) (u' ≫ p) i i'' x hxO.1 hxO.2]
    exact hx x hxV
  choose V hzV hVO hVx using hV
  let W : Z.Opens := ⟨(⋂ l, (V l : Set Z)) ∩ ((u ≫ p) ⁻¹ᵁ secChart U.LG.L i ⊓ (u' ≫ p) ⁻¹ᵁ secChart U.LG.L i'' : Z.Opens)
      ∩ (u ⁻¹ᵁ N : Set Z) ∩ (u' ⁻¹ᵁ N : Set Z),
    (((isOpen_iInter_of_finite fun l => (V l).isOpen).inter (TopologicalSpace.Opens.isOpen _)).inter (TopologicalSpace.Opens.isOpen _)).inter
      (TopologicalSpace.Opens.isOpen _)⟩
  have hzW : z ∈ W := ⟨⟨⟨Set.mem_iInter.2 hzV, hz'⟩, hwN⟩, show u' z ∈ N from hz ▸ hwN⟩
  refine ⟨W, hzW, ?_⟩
  have hmem : ∀ x : W.toScheme, W.ι x ∈ W := fun x => by
    have h : W.ι x ∈ Set.range W.ι := ⟨x, rfl⟩
    rwa [Scheme.Opens.range_ι] at h
  apply hmono W.toScheme (W.ι ≫ u) (W.ι ≫ u')
  · simp only [Category.assoc, hu]
  · intro x; exact (hmem x).1.2
  · intro x; exact (hmem x).2
  · intro l
    refine secRatioEq_of_exists_germ fun x => ⟨i, i'', (hmem x).1.1.2.1, (hmem x).1.1.2.2, ?_⟩
    simp only [Category.assoc]
    rw [secGerm_comp W.ι (u ≫ p) x _ (hmem x).1.1.2.1, secGerm_comp W.ι (u ≫ p) x _ (hmem x).1.1.2.1,
      secGerm_comp W.ι (u' ≫ p) x _ (hmem x).1.1.2.2, secGerm_comp W.ι (u' ≫ p) x _ (hmem x).1.1.2.2,
      ← map_mul, ← map_mul, hVx l _ (Set.mem_iInter.1 (hmem x).1.1.1 l)]

end GlobalTheory.Mum.LocAgree
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupMorphismsAgreeNearPointStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.uniformisedGroup_morphisms_agree_near_point : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∀ (e k : ℕ), k₀ ≤ k → ∀ (Z : Scheme.{0}) (u u' : Z ⟶ (thickObj R (maximalIdeal R) e G).left), u ≫ (thickObj R (maximalIdeal R) e G).hom = u' ≫ (thickObj R (maximalIdeal R) e G).hom → ∀ (s₀ : H0 U.LG.L k) (i i'' : Fin 1 → U.LG.L.ι) (z : Z), GermRatioAgree (u ≫ (fstG (maximalIdeal R) e G).left) (u' ≫ (fstG (maximalIdeal R) e G).left) s₀ i i'' z → u z = u' z → ∃ W : Z.Opens, z ∈ W ∧ W.ι ≫ u = W.ι ≫ u' := by
  first | exact @GlobalTheory.Mum.LocAgree.locAgree | exact GlobalTheory.Mum.LocAgree.locAgree | (intros; apply GlobalTheory.Mum.LocAgree.locAgree <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupMorphismsAgreeOfSectionRatios

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem agree_near_of_ratios : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∀ (e k k' : ℕ), k₀ ≤ k → ∀ (x x' : thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G) (T : H0 U.LG.L k → H0 U.LG.L k'), (∀ s₁ s₂ : H0 U.LG.L k, SecRatioEq U.LG.L (x.left ≫ (fstG (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left s₁ s₂ (T s₁) (T s₂)) → (∀ s₁ s₂ : H0 U.LG.L k, SecRatioEq U.LG.L (x'.left ≫ (fstG (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left s₁ s₂ (T s₁) (T s₂)) → ∀ (y : (thickObj R (maximalIdeal R) e G).left) (s₀ : H0 U.LG.L k) (i i' i'' : Fin 1 → U.LG.L.ι), y ∈ (thickObj R (maximalIdeal R) e G).left.basicOpen ((((x).left ≫ (fstG (maximalIdeal R) e G).left).app (secChart U.LG.L i)).hom (s₀.f i)) → y ∈ (thickObj R (maximalIdeal R) e G).left.basicOpen (((fstG (maximalIdeal R) e G).left.app (secChart U.LG.L i')).hom ((T s₀).f i')) → y ∈ (thickObj R (maximalIdeal R) e G).left.basicOpen ((((x').left ≫ (fstG (maximalIdeal R) e G).left).app (secChart U.LG.L i'')).hom (s₀.f i'')) → ∃ W : (thickObj R (maximalIdeal R) e G).left.Opens, y ∈ W ∧ W.ι ≫ x.left = W.ι ≫ x'.left := by

  intro R _ _ _ hB D A G _ _ hG U
  obtain ⟨k₁, hk₁, H₁⟩ := GlobalTheory.T.thickening_morphisms_agree_beyond_threshold R hB D A G hG U
  obtain ⟨k₂, -, H₂⟩ := GlobalTheory.T.uniformisedGroup_morphisms_agree_near_point R hB D A G hG U
  refine ⟨max k₁ k₂, le_trans hk₁ (le_max_left _ _), ?_⟩
  intro e k k' hk x x' T hx hx' y s₀ i i' i'' hy₁ hy₂ hy₃
  have m₁ : (x.left ≫ (fstG (maximalIdeal R) e G).left) y ∈ secChart U.LG.L i :=
    (thickObj R (maximalIdeal R) e G).left.basicOpen_le _ hy₁
  have m₂ : (fstG (maximalIdeal R) e G).left y ∈ secChart U.LG.L i' :=
    (thickObj R (maximalIdeal R) e G).left.basicOpen_le _ hy₂
  have m₃ : (x'.left ≫ (fstG (maximalIdeal R) e G).left) y ∈ secChart U.LG.L i'' :=
    (thickObj R (maximalIdeal R) e G).left.basicOpen_le _ hy₃
  have u₁ : IsUnit (secGerm (x.left ≫ (fstG (maximalIdeal R) e G).left) y s₀ i) := by
    exact (congrArg IsUnit (gs_eq _ _ _ m₁ _)).mpr ((Scheme.mem_basicOpen (thickObj R (maximalIdeal R) e G).left _ y m₁).1 hy₁)
  have u₂ : IsUnit (secGerm (fstG (maximalIdeal R) e G).left y (T s₀) i') := by
    exact (congrArg IsUnit (gs_eq _ _ _ m₂ _)).mpr ((Scheme.mem_basicOpen (thickObj R (maximalIdeal R) e G).left _ y m₂).1 hy₂)
  have u₃ : IsUnit (secGerm (x'.left ≫ (fstG (maximalIdeal R) e G).left) y s₀ i'') := by
    exact (congrArg IsUnit (gs_eq _ _ _ m₃ _)).mpr ((Scheme.mem_basicOpen (thickObj R (maximalIdeal R) e G).left _ y m₃).1 hy₃)
  have hA : GermRatioAgree (x.left ≫ (fstG (maximalIdeal R) e G).left)
      (x'.left ≫ (fstG (maximalIdeal R) e G).left) s₀ i i'' y := by
    refine ⟨m₁, m₃, u₁, u₃, fun s₁ => ?_⟩
    have e₁ := secRatioEq_iff_germ.1 (hx s₁ s₀) y i i' m₁ m₂
    have e₂ := secRatioEq_iff_germ.1 (hx' s₁ s₀) y i'' i' m₃ m₂
    apply (u₂.mul_left_inj).1
    linear_combination secGerm (x'.left ≫ (fstG (maximalIdeal R) e G).left) y s₀ i'' * e₁ -
      secGerm (x.left ≫ (fstG (maximalIdeal R) e G).left) y s₀ i * e₂
  have hb : x.left ≫ (thickObj R (maximalIdeal R) e G).hom = x'.left ≫ (thickObj R (maximalIdeal R) e G).hom := by
    rw [Over.w x, Over.w x']
  have hk₁' : k₁ ≤ k := le_trans (le_max_left _ _) hk
  have hk₂' : k₂ ≤ k := le_trans (le_max_right _ _) hk
  exact H₂ e k hk₂' _ x.left x'.left hb s₀ i i'' y hA (H₁ e k hk₁' _ x.left x'.left hb s₀ i i'' y hA)

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupMorphismsAgreeOfSectionRatiosStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.uniformisedGroup_morphisms_agree_of_sectionRatios : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∀ (e k k' : ℕ), k₀ ≤ k → ∀ (x x' : thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G) (T : H0 U.LG.L k → H0 U.LG.L k'), (∀ s₁ s₂ : H0 U.LG.L k, SecRatioEq U.LG.L (x.left ≫ (fstG (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left s₁ s₂ (T s₁) (T s₂)) → (∀ s₁ s₂ : H0 U.LG.L k, SecRatioEq U.LG.L (x'.left ≫ (fstG (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left s₁ s₂ (T s₁) (T s₂)) → ∀ (y : (thickObj R (maximalIdeal R) e G).left) (s₀ : H0 U.LG.L k) (i i' i'' : Fin 1 → U.LG.L.ι), y ∈ (thickObj R (maximalIdeal R) e G).left.basicOpen ((((x).left ≫ (fstG (maximalIdeal R) e G).left).app (secChart U.LG.L i)).hom (s₀.f i)) → y ∈ (thickObj R (maximalIdeal R) e G).left.basicOpen (((fstG (maximalIdeal R) e G).left.app (secChart U.LG.L i')).hom ((T s₀).f i')) → y ∈ (thickObj R (maximalIdeal R) e G).left.basicOpen ((((x').left ≫ (fstG (maximalIdeal R) e G).left).app (secChart U.LG.L i'')).hom (s₀.f i'')) → ∃ W : (thickObj R (maximalIdeal R) e G).left.Opens, y ∈ W ∧ W.ι ≫ x.left = W.ι ≫ x'.left := by
  first | exact @GlobalTheory.Mum.agree_near_of_ratios | exact GlobalTheory.Mum.agree_near_of_ratios | (intros; apply GlobalTheory.Mum.agree_near_of_ratios <;> assumption)
end
end
