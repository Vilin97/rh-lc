module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionPrimitiveBundleTranslateLocalRing
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemSmulTopOfForallMem
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointPrimitiveBundleEqTranslatePpav
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatKernelPolarisationCosetsOverDVR
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LineBundleProductAcyclicOfAffineBaseAcyclicStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHoldStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsClosedSubschemeTranslationKernelStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatKernelPolarisationCosetsOverDVR
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfQuasiAffine
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsIsoOfFlatOfClosedPoint
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointTranslatePrimitiveOfAmpleKTrivial

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.PrimitiveNonSym
open GlobalTheory.PrimitiveOverField GlobalTheory.CechPic GlobalTheory.AbLaw GlobalTheory.UU

theorem exists_point_translate_of_ample : ∀ (A : Type) [Field A] [IsAlgClosed A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (g : ℕ) (L O : LB B.left), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → L.IsLB → RelAmple B L → KTriv B L → (∃ t : LB.Gen (Theta B L), t.IsGen) → O.IsLB → (∃ u : LB.Gen (abelian₂ B O), u.IsGen) → ∃ x : 𝟙_ _ ⟶ B, LBIso O (LB.LinComb L (K := Fin 2) ![((toUnit B ≫ x) * 𝟙 B).left, 𝟙 B.left] ![1, -1]) := by
  intro K _ _ B _ _ g L O hB _ hLl _ hK hΘ hO hu
  by_contra hno
  have := hB.smooth
  have := hB.proper
  have hpr : IsProjBy B.hom := GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme K B hB
  have hproj : ∀ (R : Type) [CommRing R] (u : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K)) (X : Scheme.{0})
      (π : X ⟶ B.left) (f : X ⟶ Spec (CommRingCat.of R)), IsPullback π f B.hom u → IsProjBy f :=
    fun R _ u X π f h => GlobalTheory.StabFlat.isProjBy_baseChange hpr h
  have lamO : lam (cls O hO) (fst B B) (snd B B) = 0 :=
    (cls_cube_two hO _ _ (LB.isLB_linComb hO _ _)).symm.trans ((cls_eq_zero_iff _).2 hu)
  obtain ⟨F, hF, eF⟩ := cls_surj (lam (cls L hLl) (fst B B) (snd B B) -
    CechPic.pull (snd B B).left (cls O hO))
  have hpq : IsPullback (fst B B).left (snd B B).left B.hom B.hom := IsPullback.of_hasPullback _ _
  have cst_left : ∀ x : 𝟙_ _ ⟶ B, (toUnit B ≫ x).left = B.hom ≫ x.left := fun x =>
    congrArg (· ≫ x.left) ((Category.comp_id _).symm.trans (Over.w (toUnit B)))
  have s₁ : ∀ x : 𝟙_ _ ⟶ B, cls _ (pull_isLB hF (lift (toUnit B ≫ x) (𝟙 B)).left) =
      lam (cls L hLl) (toUnit B ≫ x) (𝟙 B) - cls O hO := fun x => by
    rw [cls_pull hF, eF, map_sub, pull_lam, ← pull_comp, ← Over.comp_left, lift_fst, lift_snd, Over.id_left, pull_id]
  have s₂ : ∀ x : 𝟙_ _ ⟶ B, cls _ (pull_isLB hF (lift (𝟙 B) (toUnit B ≫ x)).left) =
      lam (cls L hLl) (toUnit B ≫ x) (𝟙 B) := fun x => by
    rw [cls_pull hF, eF, map_sub, pull_lam, ← pull_comp, ← Over.comp_left, lift_fst, lift_snd, pull_const, sub_zero,
      lam_comm]
  have total : Ac ((fst B B).left ≫ B.hom) F := by
    refine (GlobalTheory.T.lineBundle_product_acyclic_of_affine_base_acyclic K _ _ _ _ _ _ _ hpq inferInstance inferInstance inferInstance inferInstance F hF).1
      fun R _ t Y π f h ht => ac_of_slices hproj hpq h hF fun x hx _ => ?_
    let x' : 𝟙_ _ ⟶ B := Over.homMk x hx
    refine ⟨(lift (toUnit B ≫ x') (𝟙 B)).left, ?_, ?_, ac_of_primitive hB hpr (pull_isLB hF _) ?_ ?_⟩
    · exact (congrArg CommaMorphism.left (lift_fst (toUnit B ≫ x') (𝟙 B))).trans (cst_left x')
    · exact congrArg CommaMorphism.left (lift_snd (toUnit B ≫ x') (𝟙 B))
    · rw [s₁, lam_sub, lam_lam hLl hΘ, lamO, sub_zero]
    · rw [s₁, sub_ne_zero, lam_const]
      refine fun e => hno ⟨x', (cls_eq_iff hO (LB.isLB_linComb hLl _ _)).1 (e.symm.trans ?_)⟩
      refine Eq.trans ?_ (cls_linComb hLl _ _ _).symm
      rw [Fin.sum_univ_two, sub_eq_add_neg]
      exact (congrArg₂ (· + ·) (one_zsmul _) (neg_one_zsmul _)).symm
  rw [hpq.w] at total
  let o : Spec (CommRingCat.of K) ⟶ B.left := η[B].left
  have ho : o ≫ B.hom = 𝟙 _ := Over.w η[B]
  have hcl : IsClosed ({o (IsLocalRing.closedPoint K)} : Set B.left) := by
    have : IsClosedImmersion (o ≫ B.hom) := by rw [ho]; infer_instance
    have : IsClosedImmersion o := IsClosedImmersion.of_comp o B.hom
    have h := o.isClosedEmbedding.isClosedMap {IsLocalRing.closedPoint K}
      (by rw [show ({IsLocalRing.closedPoint K} : Set (Spec (CommRingCat.of K))) = Set.univ from
        Set.eq_univ_of_forall fun z => Subsingleton.elim (α := PrimeSpectrum K) _ _]; exact isClosed_univ)
    exact (congrArg IsClosed Set.image_singleton).mp h
  have all := (GlobalTheory.T.lineBundle_product_acyclic_of_affine_base_acyclic K _ _ _ _ _ _ _ hpq.flip inferInstance inferInstance inferInstance inferInstance F hF).2
    _ hcl (fun R _ t Y π f h ht hne => ac_of_slices hproj hpq.flip h hF fun x hx hr => by
      let x' : 𝟙_ _ ⟶ B := Over.homMk x hx
      refine ⟨(lift (𝟙 B) (toUnit B ≫ x')).left, ?_, ?_, ac_of_primitive hB hpr (pull_isLB hF _) ?_ ?_⟩
      · exact (congrArg CommaMorphism.left (lift_snd (𝟙 B) (toUnit B ≫ x'))).trans (cst_left x')
      · exact congrArg CommaMorphism.left (lift_fst (𝟙 B) (toUnit B ≫ x'))
      · rw [s₂, lam_lam hLl hΘ]
      · rw [s₂]
        intro e
        have e₁ : x' = η[B] := (eq_one_of_lam_eq_zero hLl hK x' e).trans (by
          rw [Hom.one_def, toUnit_unit, Category.id_comp])
        have e₂ : x = o := congrArg CommaMorphism.left e₁
        obtain ⟨y, hy⟩ := hr (IsLocalRing.closedPoint K)
        exact hne y (e₂ ▸ hy)) total
  have hs := ac_slice hproj hpq.flip hF all o ho (lift (𝟙 B) (toUnit B ≫ η[B])).left
    ((congrArg CommaMorphism.left (lift_snd (𝟙 B) (toUnit B ≫ η[B]))).trans (cst_left η[B]))
    (congrArg CommaMorphism.left (lift_fst (𝟙 B) (toUnit B ≫ η[B])))
  have : CompactSpace B.left := QuasiCompact.compactSpace_of_compactSpace B.hom
  have : Nonempty B.left := ⟨o (IsLocalRing.closedPoint K)⟩
  exact not_ac_of_cls_eq_zero _ (pull_isLB hF _) ((s₂ _).trans (lam_one_left _ _)) hs

end GlobalTheory.PrimitiveNonSym
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointTranslatePrimitiveOfAmpleKTrivialStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_point_translate_primitive_of_ample_K_trivial : ∀ (A : Type) [Field A] [IsAlgClosed A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (g : ℕ) (L O : LB B.left), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → L.IsLB → RelAmple B L → KTriv B L → (∃ t : LB.Gen (Theta B L), t.IsGen) → O.IsLB → (∃ u : LB.Gen (abelian₂ B O), u.IsGen) → ∃ x : 𝟙_ _ ⟶ B, LBIso O (LB.LinComb L (K := Fin 2) ![((toUnit B ≫ x) * 𝟙 B).left, 𝟙 B.left] ![1, -1]) := by
  first | exact @GlobalTheory.PrimitiveNonSym.exists_point_translate_of_ample | exact GlobalTheory.PrimitiveNonSym.exists_point_translate_of_ample | (intros; apply GlobalTheory.PrimitiveNonSym.exists_point_translate_of_ample <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveBundleEqTranslateAmpleNoetherianLocal

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.PrimitiveAmpleLocal
open GlobalTheory.CechPic GlobalTheory.StabFlat
open GlobalTheory.PrimitiveOverLocalRing hiding exists_section_translate
open GlobalTheory.PrimitiveOverValuationRing hiding exists_geometric_point exists_section_translate

theorem theta_pull {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {L : LB G.left}
    (hΘ : ∃ t : LB.Gen (Theta G L), t.IsGen) : ∃ t : LB.Gen (Theta G' (L.pull φ)), t.IsGen := by
  obtain ⟨t, ht⟩ := hΘ
  let U : Over.mk ((G3 G').hom ≫ f) ⟶ G3 G :=
    lift (pushPt h.1.w (x3 G' 0)) (lift (pushPt h.1.w (x3 G' 1)) (pushPt h.1.w (x3 G' 2)))
  have hx : ∀ i, pushPt h.1.w (x3 G' i) = U ≫ x3 G i := fun i => by fin_cases i <;> simp [U, x3]
  exact gen_chartPull (chartPullLinComb L φ (thφ G' (x3 G')) (thφ G (x3 G)) thε U.left
    fun k => psum_push h _ _ U hx k.down) t ht

theorem exists_geometric_point {A : Type} [CommRing A] {B : Over (Sp A)} [GrpObj B] [IsCommMonObj B] {d : ℕ}
    {L O : LB B.left} (hB : IsAbelianScheme B) (hd : SmoothOfRelativeDimension d B.hom) (hL : L.IsLB)
    (ha : RelAmple B L) (hk : KTriv B L) (hΘ : ∃ t : LB.Gen (Theta B L), t.IsGen) (hO : O.IsLB)
    (hu : ∃ u : LB.Gen (abelian₂ B O), u.IsGen) (K : Type) [Field K] [IsAlgClosed K] (f : Spec (CommRingCat.of K) ⟶ Sp A) :
    ∃ x : Over.mk f ⟶ B, Triv (LB.div (translDiff B L x) (O.pull (snd (Over.mk f) B).left)) := by
  obtain ⟨B', _, _, g, h, hB'⟩ : ∃ (B' : Over (Spec (CommRingCat.of K))) (_ : GrpObj B') (_ : IsCommMonObj B')
      (g : B'.left ⟶ B.left), IsGrpPullback B' B f g ∧ IsAbelianScheme B' :=
    ⟨(Over.pullback f).obj B, inferInstance, (TLinPf.isAb_pullback f B hB).comm, _, isGrpPullback_pullback B f,
      TLinPf.isAb_pullback f B hB⟩
  have hg := h.1
  have hm : ∀ (T : Over (Spec (CommRingCat.of K))) (x y : T ⟶ B'),
      toBase hg.w (x * y) = toBase hg.w x * toBase hg.w y := fun T x y =>
    Over.OverMorphism.ext (h.2 T x y _ _ rfl rfl).symm
  have hL' := pull_isLB hL g
  have hd' : SmoothOfRelativeDimension d B'.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hg hd
  obtain ⟨w₀, hw₀⟩ : LBIso (L.pull g) (L.pull g) := ⟨idIso _, idIso_isGen hL'⟩
  have ha' : RelAmple B' (L.pull g) :=
    relAmple_pull hg hL hL' ((isGen_iff w₀).1 hw₀) ⊤ (isAffineOpen_top _) (fun _ => trivial) ha
  have hk' : KTriv B' (L.pull g) := kTriv_pull h hL hL' ((isGen_iff w₀).1 hw₀) hk
  have hΘ' := theta_pull h hΘ
  have hc : CechPic.pull g (cls L hL) = cls (L.pull g) hL' := (cls_pull hL _ _).symm
  have hO' := pull_isLB hO g
  have one : ∀ T : Over (Spec (CommRingCat.of K)), toBase hg.w (1 : T ⟶ B') = 1 := fun T => by
    have := hm T 1 1
    rw [_root_.mul_one] at this
    exact left_eq_mul.1 this
  have lamO : lam (cls O hO) (fst B B) (snd B B) = 0 :=
    (cls_cube_two hO _ _ (LB.isLB_linComb hO _ _)).symm.trans ((cls_eq_zero_iff _).2 hu)
  have lamO' : lam (cls _ hO') (fst B' B') (snd B' B') = 0 := by
    have e := congrArg (CechPic.pull (lift (toBase hg.w (fst B' B')) (toBase hg.w (snd B' B'))).left) lamO
    rw [pull_lam, lift_fst, lift_snd, map_zero, lam, ← hm, ← one] at e
    rw [cls_pull hO, lam, ← pull_comp, ← pull_comp, ← pull_comp, ← pull_comp]
    exact e
  obtain ⟨x', hx'⟩ := GlobalTheory.T.exists_point_translate_primitive_of_ample_K_trivial K B' d (L.pull g) (O.pull g) hB' hd' hL' ha' hk' hΘ' hO'
    ((cls_eq_zero_iff (LB.isLB_linComb hO' _ _)).1 ((cls_cube_two hO' _ _ (LB.isLB_linComb hO' _ _)).trans lamO'))
  have e := ((cls_eq_iff hO' (LB.isLB_linComb hL' _ _)).2 hx').trans (cls_pair hL' _ _ _)
  let T : Over (Sp A) := Over.mk f
  have wx : x'.left ≫ B'.hom = 𝟙 _ := Over.w x'
  let x : T ⟶ B := Over.homMk (x'.left ≫ g) (by
    show (x'.left ≫ g) ≫ B.hom = f
    rw [Category.assoc, hg.w, ← Category.assoc, wx]
    exact Category.id_comp _)
  have w : (snd T B).left ≫ B.hom = (fst T B).left ≫ f := (Over.w (snd T B)).trans (Over.w (fst T B)).symm
  let T' : Over (Spec (CommRingCat.of K)) := Over.mk (Y := (T ⊗ B).left) (fst T B).left
  let h : T' ⟶ B' := Over.homMk (hg.lift (snd T B).left (fst T B).left w) (hg.lift_snd _ _ _)
  have hh : h.left ≫ g = (snd T B).left := hg.lift_fst _ _ _
  let u : Over.mk (T'.hom ≫ f) ⟶ T ⊗ B := Over.homMk (𝟙 _) ((Category.id_comp _).trans (Over.w (fst T B)).symm)
  have b₁ : u ≫ snd T B = toBase hg.w h := Over.OverMorphism.ext ((Category.id_comp _).trans hh.symm)
  have b₂ : u ≫ fst T B ≫ x = toBase hg.w (toUnit T' ≫ x') := by
    refine Over.OverMorphism.ext ((Category.id_comp _).trans ?_)
    have : (toUnit T').left = (fst T B).left := (Category.comp_id _).symm.trans (Over.w (toUnit T'))
    show (fst T B).left ≫ x'.left ≫ g = ((toUnit T').left ≫ x'.left) ≫ g
    rw [this]
    exact (Category.assoc _ _ _).symm
  have b : h.left ≫ ((toUnit B' ≫ x') * 𝟙 B').left ≫ g = ((fst T B ≫ x) * snd T B).left := by
    have b₃ : toBase hg.w (h ≫ ((toUnit B' ≫ x') * 𝟙 B')) = u ≫ ((fst T B ≫ x) * snd T B) := by
      rw [MonObj.comp_mul, MonObj.comp_mul, b₁, b₂, ← hm, Category.comp_id, ← Category.assoc, comp_toUnit]
    exact (Category.assoc _ _ _).symm.trans ((congrArg CommaMorphism.left b₃).trans (Category.id_comp _))
  have e' := congrArg (CechPic.pull h.left) e
  rw [cls_pull hO, ← hc, pull_id, map_sub, ← pull_comp, ← pull_comp, ← pull_comp, ← pull_comp, Category.assoc, b, hh] at e'
  have h₁ : (translDiff B L x).IsLB := LB.isLB_linComb hL _ _
  have h₂ := pull_isLB hO (snd T B).left
  refine ⟨x, (cls_eq_zero_iff (LB.isLB_div h₁ h₂)).1 ?_⟩
  rw [cls_div h₁ h₂, sub_eq_zero]
  exact (cls_pair hL _ _ h₁).trans e'.symm

theorem exists_section_translate : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (g : ℕ) (L O : LB B.left), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → L.IsLB → RelAmple B L → KTriv B L → (∃ t : LB.Gen (Theta B L), t.IsGen) → O.IsLB → (∃ u : LB.Gen (abelian₂ B O), u.IsGen) → ∃ x : 𝟙_ _ ⟶ B, LBIso O (LB.LinComb L (K := Fin 2) ![((toUnit B ≫ x) * 𝟙 B).left, 𝟙 B.left] ![1, -1]) := by
  intro V _ _ _ B _ _ d L O hB hd hL ha hk hΘ hO hu
  have hG : GlobalFnsSt := GlobalTheory.T.all_six_abelian_scheme_laws_hold.1.globalFns
  have proj : IsProjBy B.hom := by
    obtain ⟨d, -, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy V B L hL).1 ha
    exact ⟨_, isLB_pw hL _, n, s, hs⟩
  obtain ⟨H, j, hj, hH⟩ := GlobalTheory.T.exists_closed_subscheme_translation_kernel hG V B hB proj L O hL hO
  have fin : IsFinite H.hom := GlobalTheory.AmpleStabFinite.isFinite_of_relAmple hG V B hB L O hL hO
    ha H j hj hH
  have mono : Mono H.hom := ⟨fun {Z} a b e => by
    let a' : Over.mk (b ≫ H.hom) ⟶ H := Over.homMk a e
    let b' : Over.mk (b ≫ H.hom) ⟶ H := Over.homMk b rfl
    have := (inK_mul_inv hL hO (a' ≫ j) (b' ≫ j) ((hH _ _).2 ⟨_, rfl⟩) ((hH _ _).2 ⟨_, rfl⟩)).eq_one hk
    rw [mul_inv_eq_one] at this
    exact (cancel_mono j.left).1 (congrArg CommaMorphism.left this)⟩
  have : IsClosedImmersion H.hom := (IsClosedImmersion.iff_isFinite_and_mono _).2 ⟨fin, mono⟩
  let K : Type := AlgebraicClosure (IsLocalRing.ResidueField V)
  let φ : V →+* K := (algebraMap (IsLocalRing.ResidueField V) K).comp (IsLocalRing.residue V)
  have : IsLocalHom φ := RingHom.isLocalHom_comp _ _
  obtain ⟨x₀, hx₀⟩ := exists_geometric_point hB hd hL ha hk hΘ hO hu K (Spec.map (CommRingCat.ofHom φ))
  obtain ⟨y, -⟩ := (hH _ x₀).1 fun p => ⟨⊤, trivial, by
    have hM := LB.isLB_div (show (translDiff B L x₀).IsLB from LB.isLB_linComb hL _ _)
      (pull_isLB hO (snd _ B).left)
    refine (cls_eq_zero_iff (pull_isLB hM _)).1 ?_
    rw [cls_pull hM, (cls_eq_zero_iff hM).2 hx₀, map_zero]⟩
  let y' : Spec (CommRingCat.of K) ⟶ H.left := y.left
  have hy : H.hom (y' (IsLocalRing.closedPoint K)) = IsLocalRing.closedPoint V :=
    (congrArg (fun q => q (IsLocalRing.closedPoint K)) (Over.w y)).trans (IsLocalRing.comap_closedPoint φ)
  obtain ⟨R, _, _, _, _, ξ, g₀, hfl, hξ, hξV, hg₀, hξK, hreg, hdim⟩ :=
    FibreAcyclic.exists_localRing B.hom d hd (y' ≫ j.left) (by
      have := j.left.isClosedEmbedding.isClosedMap _ (isClosed_of_isFinite H.hom _ hy)
      rwa [Set.image_singleton] at this) ((congrArg (fun q => q (y' (IsLocalRing.closedPoint K))) (Over.w j)).trans hy)
  obtain ⟨I, C, c₁, ⟨n, c₂⟩, ⟨e⟩, c₃, hI⟩ := exists_ideal_complex hG B hB proj hd hL hO
    hΘ hu j hH R ξ K g₀ hg₀ ⟨y', hξK.symm⟩
  have hI₀ : I ≠ ⊤ := ne_top_of_le_ne_top (RingHom.ker_ne_top g₀) ((hI K g₀).1 ⟨y', hξK.symm⟩)
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI₀
  have : IsLocalRing (R ⧸ I) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  obtain ⟨w, hw⟩ := (hI (R ⧸ I) (Ideal.Quotient.mk I)).2 Ideal.mk_ker.ge
  have hwV : w ≫ H.hom = Spec.map (CommRingCat.ofHom (algebraMap V (R ⧸ I))) := by
    rw [← Over.w j, ← Category.assoc, hw, Category.assoc, hξV, ← Spec.map_comp]
    rfl
  have hN : (IsLocalRing.maximalIdeal V).map (algebraMap V R) ≤ IsLocalRing.maximalIdeal R :=
    IsLocalRing.le_maximalIdeal (Ideal.Quotient.nontrivial_iff.1 inferInstance)
  have hloc : IsLocalHom (algebraMap V R) := ((IsLocalRing.local_hom_tfae (algebraMap V R)).out 3 1).1 hN
  have hsurj : Function.Surjective (algebraMap V (R ⧸ I)) := by
    have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    have : IsPreimmersion (w ≫ j.left) := hw ▸ inferInstance
    have : IsPreimmersion w := IsPreimmersion.of_comp w j.left
    have h₁ : IsPreimmersion (Spec.map (CommRingCat.ofHom (algebraMap V (R ⧸ I)))) := hwV ▸ inferInstance
    have : IsLocalHom (Ideal.Quotient.mk I) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    have : IsLocalHom (algebraMap V (R ⧸ I)) := RingHom.isLocalHom_comp (Ideal.Quotient.mk I) (algebraMap V R)
    exact RingHom.surjectiveOnStalks_iff_of_isLocalHom.1 ((IsPreimmersion.SpecMap_iff _).1 h₁).2
  have hinj : Function.Injective (algebraMap V (R ⧸ I)) := by
    have hfree := fun i => (c₁ i).1
    have hfin := fun i => (c₁ i).2
    refine FibreAcyclic.injective_of_exact (C.d 0 1).hom (C.d 1 2).hom (DualCokernel.d_d_apply C 0 1 2) ?_ I hI₀ e hsurj
    refine FibreAcyclic.exact_hom_one _ hN _ (fun s hs x => ?_) d (FibreAcyclic.extZero_quotient _ _ hdim) C c₁ n c₂
      fun p hp hNp => ?_
    · rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2 hs, zero_mul]
    · obtain ⟨K', _, ψ, hψ, hex⟩ := c₃ p hp
      refine ⟨K', inferInstance, ψ, hψ, fun i hi => hex i (hi.imp_left fun hne hIp => hne ?_)⟩
      refine (IsLocalRing.le_maximalIdeal hp.ne_top).antisymm fun s hs => ?_
      obtain ⟨a, ha⟩ := hsurj (Ideal.Quotient.mk I s)
      have h₁ : algebraMap V R a - s ∈ I := Ideal.Quotient.eq.1 ha
      have h₂ : algebraMap V R a ∈ IsLocalRing.maximalIdeal R := by
        simpa using add_mem (IsLocalRing.le_maximalIdeal hI₀ h₁) hs
      have h₃ : a ∈ IsLocalRing.maximalIdeal V := fun h => h₂ (h.map _)
      simpa using sub_mem (hNp (Ideal.mem_map_of_mem _ h₃)) (hIp h₁)
  have : IsIso (CommRingCat.ofHom (algebraMap V (R ⧸ I))) := (ConcreteCategory.isIso_iff_bijective _).2 ⟨hinj, hsurj⟩
  let σ : 𝟙_ (Over (Spec (CommRingCat.of V))) ⟶ H :=
    Over.homMk (inv (Spec.map (CommRingCat.ofHom (algebraMap V (R ⧸ I)))) ≫ w) (by
      rw [Category.assoc, hwV]
      exact IsIso.inv_hom_id _)
  obtain ⟨U, hU, ht⟩ := (hH _ (σ ≫ j)).2 ⟨σ, rfl⟩ (IsLocalRing.closedPoint V)
  obtain rfl : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).1 hU
  have e := pull_eq_zero_of_mem ((fst _ B).left ⁻¹ᵁ ⊤) (lift (toUnit B) (𝟙 B)).left (fun _ => trivial)
    ((triv_iff hL hO (σ ≫ j) _).1 ht)
  rw [map_sub, map_sub, ← pull_comp, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, MonObj.comp_mul,
    lift_snd, lift_fst_assoc, sub_eq_zero, Over.id_left, pull_id (cls O hO)] at e
  exact ⟨σ ≫ j, (cls_eq_iff hO (LB.isLB_linComb hL _ _)).1 (e.symm.trans (cls_pair hL _ _ _).symm)⟩

end GlobalTheory.PrimitiveAmpleLocal
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveBundleEqTranslateAmpleNoetherianLocalStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.primitive_bundle_eq_translate_ample_noetherian_local : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (g : ℕ) (L O : LB B.left), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → L.IsLB → RelAmple B L → KTriv B L → (∃ t : LB.Gen (Theta B L), t.IsGen) → O.IsLB → (∃ u : LB.Gen (abelian₂ B O), u.IsGen) → ∃ x : 𝟙_ _ ⟶ B, LBIso O (LB.LinComb L (K := Fin 2) ![((toUnit B ≫ x) * 𝟙 B).left, 𝟙 B.left] ![1, -1]) := by
  first | exact @GlobalTheory.PrimitiveAmpleLocal.exists_section_translate | exact GlobalTheory.PrimitiveAmpleLocal.exists_section_translate | (intros; apply GlobalTheory.PrimitiveAmpleLocal.exists_section_translate <;> assumption)
end
end
