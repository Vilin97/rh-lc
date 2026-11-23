module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionOfFinite

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.FiniteSectionLift

theorem exists_section_of_finite (R A K : CommRingCat) (φ : R ⟶ K)
    (hinj : Function.Injective φ.hom)
    (hint : ∀ x : K, φ.hom.IsIntegralElem x → ∃ r : R, φ.hom r = x)
    (g : R ⟶ A) (hg : g.hom.Finite) (f : A ⟶ K) (hf : g ≫ f = φ) :
    ∃ s : A ⟶ R, g ≫ s = 𝟙 R ∧ s ≫ φ = f := by
  have hmem : ∀ a, f.hom a ∈ φ.hom.range := by
    intro a
    obtain ⟨q, hq, h0⟩ := hg.to_isIntegral a
    obtain ⟨r, hr⟩ := hint (f.hom a) ⟨q, hq, by
      rw [← hf, CommRingCat.hom_comp, ← Polynomial.hom_eval₂, h0, map_zero]⟩
    exact ⟨r, hr⟩
  let e : R ≃+* φ.hom.range := RingEquiv.ofBijective φ.hom.rangeRestrict
    ⟨fun a b h => hinj (congrArg Subtype.val h), φ.hom.rangeRestrict_surjective⟩
  let t : A →+* R := e.symm.toRingHom.comp (f.hom.codRestrict φ.hom.range hmem)
  have hkey : ∀ a, φ.hom (t a) = f.hom a := by
    intro a
    have h1 : e (e.symm ⟨f.hom a, hmem a⟩) = ⟨f.hom a, hmem a⟩ := e.apply_symm_apply _
    exact congrArg Subtype.val h1
  refine ⟨CommRingCat.ofHom t, ?_, ?_⟩
  · ext r
    apply hinj
    change φ.hom (t (g.hom r)) = φ.hom r
    rw [hkey, ← hf]
    rfl
  · ext a
    exact hkey a

theorem lift_of_finite : ∀ (R K : CommRingCat) (φ : R ⟶ K),
    Function.Injective (⇑(CommRingCat.Hom.hom φ) : (↑R : Type) → (↑K : Type)) →
    (∀ (x : (↑K : Type)), RingHom.IsIntegralElem (CommRingCat.Hom.hom φ) x →
      ∃ (r : (↑R : Type)), (CommRingCat.Hom.hom φ : (↑R : Type) → (↑K : Type)) r = x) →
    ∀ (Z P : AlgebraicGeometry.Scheme) (p : Z ⟶ P) (ξ₀ : AlgebraicGeometry.Spec R ⟶ P)
      (y : AlgebraicGeometry.Spec K ⟶ Z), AlgebraicGeometry.IsFinite p →
      CategoryTheory.CategoryStruct.comp y p =
        CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.Spec.map φ) ξ₀ →
      ∃ (ξ : AlgebraicGeometry.Spec R ⟶ Z),
        CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.Spec.map φ) ξ = y ∧
        CategoryTheory.CategoryStruct.comp ξ p = ξ₀ := by
  intro R K φ hinj hint Z P p ξ₀ y hp hy
  haveI : IsAffine (pullback p ξ₀) := isAffine_of_isAffineHom (pullback.snd p ξ₀)
  let l : Spec K ⟶ pullback p ξ₀ := pullback.lift y (Spec.map φ) hy
  let g : R ⟶ Γ(pullback p ξ₀, ⊤) :=
    Spec.preimage ((pullback p ξ₀).isoSpec.inv ≫ pullback.snd p ξ₀)
  let f : Γ(pullback p ξ₀, ⊤) ⟶ K := Spec.preimage (l ≫ (pullback p ξ₀).isoSpec.hom)
  have hgS : Spec.map g = (pullback p ξ₀).isoSpec.inv ≫ pullback.snd p ξ₀ := Spec.map_preimage _
  have hfS : Spec.map f = l ≫ (pullback p ξ₀).isoSpec.hom := Spec.map_preimage _
  have hgfin : g.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hgS]
    infer_instance
  have hf : g ≫ f = φ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hfS, hgS]
    simp only [l, Category.assoc, Iso.hom_inv_id_assoc]
    exact pullback.lift_snd _ _ _
  obtain ⟨s, hs1, hs2⟩ := exists_section_of_finite R _ K φ hinj hint g hgfin f hf
  refine ⟨Spec.map s ≫ (pullback p ξ₀).isoSpec.inv ≫ pullback.fst p ξ₀, ?_, ?_⟩
  · rw [← Category.assoc, ← Spec.map_comp, hs2, hfS]
    simp only [l, Category.assoc, Iso.hom_inv_id_assoc]
    exact pullback.lift_fst _ _ _
  · rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc _ (pullback.snd p ξ₀),
      ← hgS, ← Category.assoc, ← Spec.map_comp, hs1, Spec.map_id, Category.id_comp]

end GlobalTheory.FiniteSectionLift
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalSchemeExtensionThroughFiniteCover

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.NormalFiniteLift

theorem finite_lift_of_integral (R K : CommRingCat.{0}) (φ : R ⟶ K) (hinj : Function.Injective φ.hom)
    (H : ∀ x : K, φ.hom.IsIntegralElem x → ∃ r : R, φ.hom r = x)
    (Z P : Scheme.{0}) (p : Z ⟶ P) (ξ₀ : Spec R ⟶ P) (y : Spec K ⟶ Z)
    (hp : IsFinite p) (hy : y ≫ p = Spec.map φ ≫ ξ₀) :
    ∃ ξ : Spec R ⟶ Z, Spec.map φ ≫ ξ = y ∧ ξ ≫ p = ξ₀ := by
  first
  | exact @_root_.GlobalTheory.FiniteSectionLift.lift_of_finite
  | exact _root_.GlobalTheory.FiniteSectionLift.lift_of_finite
  | (apply _root_.GlobalTheory.FiniteSectionLift.lift_of_finite <;> assumption)
  | (intros; apply _root_.GlobalTheory.FiniteSectionLift.lift_of_finite <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FiniteSectionLift.lift_of_finite <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FiniteSectionLift.lift_of_finite ..)

theorem isDominant_of_generic {T S : Scheme.{0}} [IsIntegral S] (r : T ⟶ S) [IsOpenImmersion r]
    (K : CommRingCat.{0}) [IsLocalRing K] (w : Spec K ⟶ T)
    (hw : r (w (IsLocalRing.closedPoint K)) = genericPoint S) : IsDominant w := by
  refine ⟨?_⟩
  rw [DenseRange, dense_iff_inter_open]
  rintro O hO ⟨t, ht⟩
  obtain ⟨t', ht', e⟩ : genericPoint S ∈ r '' O :=
    ((genericPoint_spec S).mem_open_set_iff (r.isOpenEmbedding.isOpenMap O hO)).2 ⟨r t, Set.mem_univ _, t, ht, rfl⟩
  refine ⟨w (IsLocalRing.closedPoint K), ?_, ⟨_, rfl⟩⟩
  rw [← r.isOpenEmbedding.injective (e.trans hw.symm)]
  exact ht'

end GlobalTheory.NormalFiniteLift

namespace GlobalTheory.NormalFiniteLift

theorem exists_lift_of_finite : ∀ (o : Type) [CommRing o] (N : ℕ) (S' X Z : Scheme.{0}) (U : S'.Opens)
    (c : U.toScheme ⟶ X) (i : X ⟶ Z) (p : Z ⟶ PSpace o N) (h : S' ⟶ PSpace o N), IsIntegral S' →
    Geo.Tor.IsNormalScheme S' → IsIntegral Z → Dense (U : Set S') → IsDominant c → IsFinite p →
    IsOpenImmersion i → Dense (Set.range i) → U.ι ≫ h = c ≫ i ≫ p →
    ∃ π : S' ⟶ Z, U.ι ≫ π = c ≫ i ∧ π ≫ p = h := by
  intro o _ N S' X Z U c i p h _ hN _ hU _ hp _ _ e
  have := GlobalTheory.IsNormalScheme.of_pred hN
  have hη : ∀ V : S'.Opens, (V : Set S').Nonempty → genericPoint S' ∈ V := fun V hV =>
    ((genericPoint_spec S').mem_open_set_iff V.isOpen).2 (by simpa using hV)
  have hηU : genericPoint S' ∈ U := hη U hU.nonempty
  let gS : Spec S'.functionField ⟶ S' := S'.fromSpecStalk (genericPoint S')
  have hgS : gS (IsLocalRing.closedPoint S'.functionField) = genericPoint S' := Scheme.fromSpecStalk_closedPoint
  have hrO : ∀ O : S'.Opens, genericPoint S' ∈ O → Set.range gS ⊆ Set.range O.ι := by
    rintro O hO _ ⟨q, rfl⟩
    rw [Scheme.Opens.range_ι]
    have : gS q ⤳ genericPoint S' := (S'.range_fromSpecStalk (x := genericPoint S')).le ⟨q, rfl⟩
    exact this.mem_open O.isOpen hO
  let gO : ∀ O : S'.Opens, genericPoint S' ∈ O → (Spec S'.functionField ⟶ O.toScheme) := fun O hO =>
    IsOpenImmersion.lift O.ι gS (hrO O hO)
  have hgO : ∀ O hO, gO O hO ≫ O.ι = gS := fun O hO => IsOpenImmersion.lift_fac _ _ _
  let y : Spec S'.functionField ⟶ Z := gO U hηU ≫ c ≫ i
  have hy : y ≫ p = gS ≫ h := by
    simp only [y, Category.assoc, ← e]
    rw [← Category.assoc, hgO U hηU]

  have loc : ∀ (V : S'.Opens) (hV : IsAffineOpen V) (hηV : genericPoint S' ∈ V),
      ∃ m : V.toScheme ⟶ Z, m ≫ p = V.ι ≫ h ∧ gO V hηV ≫ m = y := by
    intro V hV hηV
    have : Nonempty V := ⟨⟨_, hηV⟩⟩
    have : IsIntegrallyClosed Γ(S', V) := GlobalTheory.IsNormalScheme.isIntegrallyClosed_of_isAffineOpen hV
    have : IsFractionRing Γ(S', V) S'.functionField := functionField_isFractionRing_of_isAffineOpen S' V hV
    have hsp : Spec.map (S'.germToFunctionField V) ≫ hV.fromSpec = gS :=
      hV.fromSpecStalk_eq_fromSpecStalk hηV
    obtain ⟨ξ, h1, h2⟩ := finite_lift_of_integral Γ(S', V) S'.functionField (S'.germToFunctionField V)
      (S'.germToFunctionField_injective V) (fun x hx => IsIntegrallyClosed.isIntegral_iff.1 hx) Z _ p
      (hV.fromSpec ≫ h) y hp (by rw [hy, ← Category.assoc, hsp])
    have hg : gO V hηV ≫ hV.isoSpec.hom = Spec.map (S'.germToFunctionField V) := by
      rw [← cancel_mono hV.fromSpec, Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec, hgO V hηV, hsp]
    refine ⟨hV.isoSpec.hom ≫ ξ, ?_, ?_⟩
    · rw [Category.assoc, h2, ← Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec]
    · rw [← Category.assoc, hg, h1]

  choose V hVa hxV _ using fun x : S' => exists_isAffineOpen_mem_and_subset (X := S') (U := ⊤) (x := x) (by simp)
  have hcov : TopologicalSpace.IsOpenCover V := eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxV x⟩
  have hηV : ∀ x, genericPoint S' ∈ V x := fun x => hη (V x) ⟨x, hxV x⟩
  choose m hm hmy using fun x => loc (V x) (hVa x) (hηV x)
  let 𝒰 := S'.openCoverOfIsOpenCover V hcov
  have hc : ∀ a b, pullback.fst (V a).ι (V b).ι ≫ m a = pullback.snd (V a).ι (V b).ι ≫ m b := by
    intro a b
    let r := pullback.fst (V a).ι (V b).ι ≫ (V a).ι
    have : IsReduced (pullback (V a).ι (V b).ι) := isReduced_of_isOpenImmersion r
    let w : Spec S'.functionField ⟶ pullback (V a).ι (V b).ι :=
      pullback.lift (gO (V a) (hηV a)) (gO (V b) (hηV b)) ((hgO (V a) (hηV a)).trans (hgO (V b) (hηV b)).symm)
    have : IsDominant w := isDominant_of_generic r _ w (by
      show (w ≫ pullback.fst _ _ ≫ (V a).ι) (IsLocalRing.closedPoint _) = _
      rw [pullback.lift_fst_assoc, hgO (V a) (hηV a)]; exact hgS)
    refine ext_of_isDominant_of_isSeparated p ?_ w ?_
    · rw [Category.assoc, Category.assoc, hm, hm, pullback.condition_assoc]
    · rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc, hmy, hmy]
  have hg : ∀ a, (V a).ι ≫ 𝒰.glueMorphisms m hc = m a := fun a => 𝒰.ι_glueMorphisms m hc a
  let π := 𝒰.glueMorphisms m hc
  have hπp : π ≫ p = h := 𝒰.hom_ext _ _ fun a => ((reassoc_of% hg a) p).trans (hm a)
  refine ⟨π, ?_, hπp⟩
  have : IsReduced U.toScheme := isReduced_of_isOpenImmersion U.ι
  have : IsDominant (gO U hηU) := isDominant_of_generic U.ι _ _ (by
    show (gO U hηU ≫ U.ι) (IsLocalRing.closedPoint _) = _
    rw [hgO U hηU]; exact hgS)
  refine ext_of_isDominant_of_isSeparated p ?_ (gO U hηU) ?_
  · rw [Category.assoc, hπp, e]; simp only [Category.assoc]
  · let x := genericPoint S'
    rw [← Category.assoc, hgO U hηU, ← hgO (V x) (hηV x), Category.assoc, hg, hmy]
end GlobalTheory.NormalFiniteLift
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalSchemeExtensionThroughFiniteCoverStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.normal_scheme_extension_through_finite_cover : ∀ (o : Type) [CommRing o] (N : ℕ) (S' X Z : Scheme.{0}) (U : S'.Opens) (c : U.toScheme ⟶ X) (i : X ⟶ Z) (p : Z ⟶ PSpace o N) (h : S' ⟶ PSpace o N), IsIntegral S' → Geo.Tor.IsNormalScheme S' → IsIntegral Z → Dense (U : Set S') → IsDominant c → IsFinite p → IsOpenImmersion i → Dense (Set.range i) → U.ι ≫ h = c ≫ i ≫ p → ∃ π : S' ⟶ Z, U.ι ≫ π = c ≫ i ∧ π ≫ p = h := by
  first | exact @GlobalTheory.NormalFiniteLift.exists_lift_of_finite | exact GlobalTheory.NormalFiniteLift.exists_lift_of_finite | (intros; apply GlobalTheory.NormalFiniteLift.exists_lift_of_finite <;> assumption)
end
end
