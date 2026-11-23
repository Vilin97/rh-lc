module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicardClassEqZeroOfZeroDenseOpenAndSectionOpenStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TheoremOfSquareCechPicardTranslatesStatement
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTheoremPicClassOverOpen

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SquareOpen

theorem pull_mul_add_pull_mul_inv_of_opens : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (U : S.Opens) (c : Pic (A.hom ⁻¹ᵁ U).toScheme) (Y : Over S) (l : (Y ⟶ A) → (Y.left ⟶ (A.hom ⁻¹ᵁ U).toScheme)), (∀ y, Y.hom y ∈ U) → (∀ p, l p ≫ (A.hom ⁻¹ᵁ U).ι = p.left) → ∀ x a : Y ⟶ A, GlobalTheory.CechPic.pull (l (x * a)) c + GlobalTheory.CechPic.pull (l (x * a⁻¹)) c = 2 • GlobalTheory.CechPic.pull (l (x)) c + GlobalTheory.CechPic.pull (l (a)) c + GlobalTheory.CechPic.pull (l (a⁻¹)) c - 2 • GlobalTheory.CechPic.pull (l ((1 : Y ⟶ A))) c := by
  intro S _ A _ hA U c Y l hY hl x a
  let A' := (Over.pullback U.ι).obj A
  have hA' : IsAbelianScheme A' := ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback U.ι A hA
  have h := isGrpPullback_pullback A U.ι
  let e := (isPullback_morphismRestrict A.hom U).flip.isoPullback
  have he : e.inv ≫ (A.hom ⁻¹ᵁ U).ι = pullback.fst A.hom U.ι := by
    rw [Iso.inv_comp_eq, IsPullback.isoPullback_hom_fst]
  have hrange : Set.range Y.hom.base ⊆ Set.range U.ι.base := by
    rintro _ ⟨y, rfl⟩
    rw [U.range_ι]
    exact hY y
  let Y' : Over U.toScheme := Over.mk (IsOpenImmersion.lift U.ι Y.hom hrange)
  have hY' : Y'.hom ≫ U.ι = Y.hom := IsOpenImmersion.lift_fac _ _ _
  let τ : Over.mk (Y'.hom ≫ U.ι) ⟶ Y := Over.homMk (𝟙 Y.left) (by erw [Category.id_comp]; exact hY'.symm)
  have lift : ∀ p : Y ⟶ A, ∃ p' : Y' ⟶ A', pushHom h Y' p' = τ ≫ p := by
    intro p
    refine ⟨Over.homMk (pullback.lift p.left Y'.hom (by rw [Over.w p, hY'])) (by
      exact pullback.lift_snd _ _ _), ?_⟩
    apply Over.OverMorphism.ext
    simp only [pushHom, pushPt, τ, MonoidHom.mk'_apply, Over.homMk_left, Over.comp_left]
    rw [pullback.lift_fst]
    exact (Category.id_comp p.left).symm
  have key : ∀ (p : Y ⟶ A) (p' : Y' ⟶ A'), pushHom h Y' p' = τ ≫ p → l p = p'.left ≫ e.inv := by
    intro p p' hp
    rw [← cancel_mono (A.hom ⁻¹ᵁ U).ι, hl, Category.assoc, he]
    have := congrArg (fun q => q.left) hp
    simp only [pushHom, pushPt, τ, MonoidHom.mk'_apply, Over.homMk_left, Over.comp_left] at this
    exact (Category.id_comp _).symm.trans this.symm
  obtain ⟨x', hx⟩ := lift x
  obtain ⟨a', ha⟩ := lift a
  have hmul : pushHom h Y' (x' * a') = τ ≫ (x * a) := by
    rw [map_mul, hx, ha, MonObj.comp_mul]
  have hainv : pushHom h Y' a'⁻¹ = τ ≫ a⁻¹ := by
    rw [map_inv, ha, GrpObj.comp_inv]
  have hinv : pushHom h Y' (x' * a'⁻¹) = τ ≫ (x * a⁻¹) := by
    rw [map_mul, hainv, hx, MonObj.comp_mul]
  have hone : pushHom h Y' 1 = τ ≫ 1 := by
    rw [map_one, MonObj.comp_one]
  rw [key _ _ hmul, key _ _ hinv, key _ _ hx, key _ _ ha, key _ _ hainv, key _ _ hone]
  simp only [pull_comp]
  exact GlobalTheory.T.theorem_of_square_cechPicard_translates U.toScheme A' hA' (pull e.inv c) Y' x' a'

end GlobalTheory.SquareOpen
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTheoremPicClassOverOpenStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.square_theorem_pic_class_over_open : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (U : S.Opens) (c : Pic (A.hom ⁻¹ᵁ U).toScheme) (Y : Over S) (l : (Y ⟶ A) → (Y.left ⟶ (A.hom ⁻¹ᵁ U).toScheme)), (∀ y, Y.hom y ∈ U) → (∀ p, l p ≫ (A.hom ⁻¹ᵁ U).ι = p.left) → ∀ x a : Y ⟶ A, GlobalTheory.CechPic.pull (l (x * a)) c + GlobalTheory.CechPic.pull (l (x * a⁻¹)) c = 2 • GlobalTheory.CechPic.pull (l (x)) c + GlobalTheory.CechPic.pull (l (a)) c + GlobalTheory.CechPic.pull (l (a⁻¹)) c - 2 • GlobalTheory.CechPic.pull (l ((1 : Y ⟶ A))) c := by
  first | exact @GlobalTheory.SquareOpen.pull_mul_add_pull_mul_inv_of_opens | exact GlobalTheory.SquareOpen.pull_mul_add_pull_mul_inv_of_opens | (intros; apply GlobalTheory.SquareOpen.pull_mul_add_pull_mul_inv_of_opens <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwicePicardClassEqZeroOfTranslatesMemOpen

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualTriv

theorem range_sub {S : Scheme.{0}} (A : Over S) (U : S.Opens) (Y : Over S) (p : Y ⟶ A)
    (hY : ∀ y, Y.hom y ∈ U) : Set.range p.left ⊆ Set.range (A.hom ⁻¹ᵁ U).ι := by
  rintro _ ⟨y, rfl⟩
  rw [Scheme.Opens.range_ι]
  show A.hom (p.left y) ∈ U
  rw [← Scheme.Hom.comp_apply, Over.w p]
  exact hY y

noncomputable def liftU {S : Scheme.{0}} (A : Over S) (U : S.Opens) (Y : Over S)
    (hY : ∀ y, Y.hom y ∈ U) (p : Y ⟶ A) : Y.left ⟶ (A.hom ⁻¹ᵁ U).toScheme :=
  IsOpenImmersion.lift (A.hom ⁻¹ᵁ U).ι p.left (range_sub A U Y p hY)

theorem liftU_fac {S : Scheme.{0}} (A : Over S) (U : S.Opens) (Y : Over S)
    (hY : ∀ y, Y.hom y ∈ U) (p : Y ⟶ A) : liftU A U Y hY p ≫ (A.hom ⁻¹ᵁ U).ι = p.left :=
  IsOpenImmersion.lift_fac _ _ _

end GlobalTheory.DualTriv

open GlobalTheory.DualTriv in
theorem GlobalTheory.twice_cls_eq_zero_of_translates_mem : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (U : S.Opens) (V W : A.left.Opens) (hV : V ≤ W), A.hom ⁻¹ᵁ U ≤ W → ∀ c : Pic W.toScheme, GlobalTheory.CechPic.pull (A.left.homOfLE hV) c = 0 → ∀ (Y : Over S) (x a v : Y ⟶ A), (∀ y, Y.hom y ∈ U) → (∀ y, v.left y ∈ V) → (∀ y, (x * a).left y ∈ V ∧ (x * a⁻¹).left y ∈ V ∧ (v * a).left y ∈ V ∧ (v * a⁻¹).left y ∈ V) → ∀ l : Y.left ⟶ W.toScheme, l ≫ W.ι = x.left → GlobalTheory.CechPic.pull l (2 • c) = 0 := by
  intro S _ A _ _ U V W hV hW c hc Y x a v hY hv hxa l hl
  set cU := GlobalTheory.CechPic.pull (A.left.homOfLE hW) c with hcU
  have zero_of : ∀ p : Y ⟶ A, (∀ y, p.left y ∈ V) →
      GlobalTheory.CechPic.pull (liftU A U Y hY p) cU = 0 := by
    intro p hp
    have H : Set.range p.left ⊆ Set.range V.ι := by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hp y
    have e : liftU A U Y hY p ≫ A.left.homOfLE hW = IsOpenImmersion.lift V.ι p.left H ≫ A.left.homOfLE hV := by
      rw [← cancel_mono W.ι, Category.assoc, Category.assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι,
        liftU_fac, IsOpenImmersion.lift_fac]
    rw [hcU, ← GlobalTheory.CechPic.pull_comp, e, GlobalTheory.CechPic.pull_comp, hc, map_zero]
  have s1 := GlobalTheory.T.square_theorem_pic_class_over_open S A ‹_› U cU Y (liftU A U Y hY) hY (liftU_fac A U Y hY) x a
  have s2 := GlobalTheory.T.square_theorem_pic_class_over_open S A ‹_› U cU Y (liftU A U Y hY) hY (liftU_fac A U Y hY) v a
  rw [zero_of _ (fun y => (hxa y).1), zero_of _ (fun y => (hxa y).2.1)] at s1
  rw [zero_of _ (fun y => (hxa y).2.2.1), zero_of _ (fun y => (hxa y).2.2.2), zero_of _ hv] at s2
  have two : 2 • GlobalTheory.CechPic.pull (liftU A U Y hY x) cU = 0 := by
    calc 2 • GlobalTheory.CechPic.pull (liftU A U Y hY x) cU
        = (2 • GlobalTheory.CechPic.pull (liftU A U Y hY x) cU + GlobalTheory.CechPic.pull (liftU A U Y hY a) cU +
            GlobalTheory.CechPic.pull (liftU A U Y hY a⁻¹) cU - 2 • GlobalTheory.CechPic.pull (liftU A U Y hY 1) cU) -
          (2 • (0 : GlobalTheory.CechPic.Pic _) + GlobalTheory.CechPic.pull (liftU A U Y hY a) cU +
            GlobalTheory.CechPic.pull (liftU A U Y hY a⁻¹) cU - 2 • GlobalTheory.CechPic.pull (liftU A U Y hY 1) cU) := by abel
      _ = 0 := by rw [← s1, ← s2, sub_self]
  have el : l = liftU A U Y hY x ≫ A.left.homOfLE hW := by
    rw [← cancel_mono W.ι, Category.assoc, Scheme.homOfLE_ι, liftU_fac, hl]
  rw [map_nsmul, el, GlobalTheory.CechPic.pull_comp, ← hcU, two]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwicePicardClassEqZeroOfTranslatesMemOpenStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.twice_picardClass_eq_zero_of_translates_mem_open : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (U : S.Opens) (V W : A.left.Opens) (hV : V ≤ W), A.hom ⁻¹ᵁ U ≤ W → ∀ c : Pic W.toScheme, GlobalTheory.CechPic.pull (A.left.homOfLE hV) c = 0 → ∀ (Y : Over S) (x a v : Y ⟶ A), (∀ y, Y.hom y ∈ U) → (∀ y, v.left y ∈ V) → (∀ y, (x * a).left y ∈ V ∧ (x * a⁻¹).left y ∈ V ∧ (v * a).left y ∈ V ∧ (v * a⁻¹).left y ∈ V) → ∀ l : Y.left ⟶ W.toScheme, l ≫ W.ι = x.left → GlobalTheory.CechPic.pull l (2 • c) = 0 := by
  first | exact @GlobalTheory.twice_cls_eq_zero_of_translates_mem | exact GlobalTheory.twice_cls_eq_zero_of_translates_mem | (intros; apply GlobalTheory.twice_cls_eq_zero_of_translates_mem <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardTwoNsmulPullbackEqZeroOnTripleParamete

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem pull_two_nsmul_eq_zero_of_triples : ∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → ∀ (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (U : S.Opens) (V W : A.left.Opens) (hV : V ≤ W), (U : Set S).Nonempty → (∀ s : S, ∃ x ∈ V, A.hom x = s) → A.hom ⁻¹ᵁ U ≤ W → W ≤ A.hom ⁻¹ᵁ U ⊔ V → ∀ c : Pic W.toScheme, GlobalTheory.CechPic.pull (A.left.homOfLE hV) c = 0 → ∀ (Y : Over S) (x a v : Y ⟶ A) (p : Y.left ⟶ V.toScheme) (e : V.toScheme ⟶ (x.left ⁻¹ᵁ V).toScheme), p ≫ V.ι = v.left → (∀ y, (x * a).left y ∈ V ∧ (x * a⁻¹).left y ∈ V ∧ (v * a).left y ∈ V ∧ (v * a⁻¹).left y ∈ V) → Smooth ((x.left ⁻¹ᵁ V).ι ≫ p) → GeometricallyIntegral ((x.left ⁻¹ᵁ V).ι ≫ p) → e ≫ (x.left ⁻¹ᵁ V).ι ≫ p = 𝟙 _ → GlobalTheory.CechPic.pull (x.left ∣_ W) (2 • c) = 0 := by
  intro S _ _ hS A _ hA U V W hV hU hsurj hUW hWUV c hc Y x a v p e hpv hmem hsm hgi he
  have := hA.smooth
  have : GeometricallyIntegral A.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hA.smooth
      hA.geomConnected
  have : GlobalTheory.IsNormalScheme S := (GlobalTheory.isNormalScheme_iff S).mpr hS
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian A.hom
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  obtain ⟨s0, hs0⟩ := hU
  obtain ⟨a0, ha0V, ha0⟩ := hsurj s0
  have : Nonempty V := ⟨⟨a0, ha0V⟩⟩
  have : IsIntegral V.toScheme := inferInstance
  have hVn : GlobalTheory.IsNormalScheme V.toScheme := GlobalTheory.isNormalScheme_of_smooth (V.ι ≫ A.hom)
  let i0 := (x.left ⁻¹ᵁ W).ι
  let O : (x.left ⁻¹ᵁ W).toScheme.Opens := i0 ⁻¹ᵁ (x.left ⁻¹ᵁ V)
  have hrange : Set.range (x.left ⁻¹ᵁ V).ι = Set.range (O.ι ≫ i0) := by
    have hO : (O : Set _) = i0 ⁻¹' (x.left ⁻¹ᵁ V : Set Y.left) := rfl
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
      Scheme.Opens.range_ι, hO, Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι]
    ext z
    simp only [Set.mem_inter_iff, SetLike.mem_coe, Scheme.Hom.mem_preimage]
    exact ⟨fun h => ⟨h, hV h⟩, fun h => h.1⟩
  let φ := IsOpenImmersion.isoOfRangeEq (x.left ⁻¹ᵁ V).ι (O.ι ≫ i0) hrange
  have hφ : φ.hom ≫ O.ι ≫ i0 = (x.left ⁻¹ᵁ V).ι := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  let UT : V.toScheme.Opens := (V.ι ≫ A.hom) ⁻¹ᵁ U
  have hUT : (UT : Set V.toScheme).Nonempty := ⟨⟨a0, ha0V⟩, by
    show A.hom (V.ι ⟨a0, ha0V⟩) ∈ U
    simpa [ha0] using hs0⟩
  let p' := i0 ≫ p
  have hOp : O.ι ≫ p' = φ.inv ≫ (x.left ⁻¹ᵁ V).ι ≫ p := by
    rw [← hφ]; simp [p']
  have hsm' : Smooth (O.ι ≫ p') := by rw [hOp]; infer_instance
  have hgi' : GeometricallyIntegral (O.ι ≫ p') := by
    have : MorphismProperty.RespectsIso @GeometricallyIntegral :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    rw [hOp]; exact (MorphismProperty.cancel_left_of_respectsIso @GeometricallyIntegral φ.inv _).mpr hgi
  have he' : (e ≫ φ.hom) ≫ O.ι ≫ p' = 𝟙 _ := by
    simp only [p', Category.assoc]; rw [reassoc_of% hφ]; exact he
  have hpY : p' ≫ V.ι ≫ A.hom = i0 ≫ Y.hom := by
    simp only [p', Category.assoc]; rw [reassoc_of% hpv, Over.w v]
  have hcover : O ⊔ p' ⁻¹ᵁ UT = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    have hz : x.left (i0 z) ∈ W := z.2
    have h' : x.left (i0 z) ∈ ((A.hom ⁻¹ᵁ U ⊔ V : A.left.Opens) : Set A.left) := hWUV hz
    rw [TopologicalSpace.Opens.coe_sup] at h'
    rcases h' with h | h
    · right
      show (V.ι ≫ A.hom) (p' z) ∈ U
      rw [← Scheme.Hom.comp_apply, hpY, ← Over.w x, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
      exact h
    · left
      exact h
  have key : ∀ c' : Pic (x.left ⁻¹ᵁ W).toScheme, pull O.ι c' = 0 → pull (p' ⁻¹ᵁ UT).ι c' = 0 →
      c' = 0 := fun c' h1 h2 =>
    GlobalTheory.T.picardClass_eq_zero_of_zero_dense_open_and_section_open V.toScheme (x.left ⁻¹ᵁ W).toScheme ((GlobalTheory.isNormalScheme_iff _).mp hVn) UT hUT p'
      O (e ≫ φ.hom) hsm' hgi' he' hcover c' h1 h2
  apply key
  · rw [← pull_comp]
    have hfac : O.ι ≫ (x.left ∣_ W) = φ.inv ≫ (x.left ∣_ V) ≫ A.left.homOfLE hV := by
      rw [← cancel_mono W.ι]
      simp only [Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι]
      rw [← reassoc_of% hφ]
      simp [i0]
    rw [hfac, pull_comp, pull_comp, map_nsmul, hc, smul_zero, map_zero, map_zero]
  · rw [← pull_comp]
    let j := (p' ⁻¹ᵁ UT).ι
    let Y' : Over S := Over.mk (j ≫ i0 ≫ Y.hom)
    let q : Y' ⟶ Y := Over.homMk (j ≫ i0) (by simp [Y'])
    refine GlobalTheory.T.twice_picardClass_eq_zero_of_translates_mem_open S A hA U V W hV hUW c hc Y' (q ≫ x) (q ≫ a) (q ≫ v) ?_ ?_ ?_
      (j ≫ (x.left ∣_ W)) ?_
    · intro y
      show (j ≫ i0 ≫ Y.hom) y ∈ U
      rw [← hpY]
      exact y.2
    · intro y
      have : (q ≫ v).left = (j ≫ i0 ≫ p) ≫ V.ι := by simp [q, hpv]
      rw [this, Scheme.Hom.comp_apply]
      exact ((j ≫ i0 ≫ p) y).2
    · intro y
      simp only [← GrpObj.comp_inv, ← MonObj.comp_mul, Over.comp_left, Scheme.Hom.comp_apply]
      exact hmem _
    · simp [q, j, i0, morphismRestrict_ι]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardTwoNsmulPullbackEqZeroOnTripleParameteStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.cechPicard_two_nsmul_pullback_eq_zero_on_tripleParameterScheme : ∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → ∀ (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (U : S.Opens) (V W : A.left.Opens) (hV : V ≤ W), (U : Set S).Nonempty → (∀ s : S, ∃ x ∈ V, A.hom x = s) → A.hom ⁻¹ᵁ U ≤ W → W ≤ A.hom ⁻¹ᵁ U ⊔ V → ∀ c : Pic W.toScheme, GlobalTheory.CechPic.pull (A.left.homOfLE hV) c = 0 → ∀ (Y : Over S) (x a v : Y ⟶ A) (p : Y.left ⟶ V.toScheme) (e : V.toScheme ⟶ (x.left ⁻¹ᵁ V).toScheme), p ≫ V.ι = v.left → (∀ y, (x * a).left y ∈ V ∧ (x * a⁻¹).left y ∈ V ∧ (v * a).left y ∈ V ∧ (v * a⁻¹).left y ∈ V) → Smooth ((x.left ⁻¹ᵁ V).ι ≫ p) → GeometricallyIntegral ((x.left ⁻¹ᵁ V).ι ≫ p) → e ≫ (x.left ⁻¹ᵁ V).ι ≫ p = 𝟙 _ → GlobalTheory.CechPic.pull (x.left ∣_ W) (2 • c) = 0 := by
  first | exact @GlobalTheory.pull_two_nsmul_eq_zero_of_triples | exact GlobalTheory.pull_two_nsmul_eq_zero_of_triples | (intros; apply GlobalTheory.pull_two_nsmul_eq_zero_of_triples <;> assumption)
end
end
