module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.WhiskerLeftEqLift
public import Mathlib.FieldTheory.IsAlgClosed.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Definitions.Divisors.WhiskerLeftEqLift
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullLiftOneEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedPicardClassZeroOfLocallyZeroStatement
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentableOfZariskiSheafOpenChartsLargeStatement
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.CategoryTheory.Monoidal.Mon

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeomPointThrough

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_geomPoint_through : ∀ (T : Scheme.{0}) (p : T), ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (s : Sp K ⟶ T), p ∈ Set.range s := by
  intro T p
  refine ⟨AlgebraicClosure (T.residueField p), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (T.residueField p) (AlgebraicClosure (T.residueField p)))) ≫ T.fromSpecResidueField p, ?_⟩
  obtain ⟨x⟩ : Nonempty (Sp (AlgebraicClosure (T.residueField p))) := inferInstance
  refine ⟨x, ?_⟩
  show (T.fromSpecResidueField p).base _ = p
  exact Scheme.fromSpecResidueField_apply p _

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullUnitEqZero

section

@[expose] public section

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

theorem AddCls.pull_unit_eq_zero {S : Scheme.{0}} {A T Z : Over S} [GrpObj A] {c : Pic (A ⊗ T).left}
    (h : AddCls A c) (t : Z ⟶ T) : CechPic.pull (lift (1 : Z ⟶ A) t).left c = 0 := by
  have h1 := h Z 1 1 t
  rw [_root_.mul_one] at h1
  exact left_eq_add.1 h1

theorem addF_separated : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → (∀ (T : Over S) (y y' : (addF A).obj (op T)), (∀ p : T.left, ∃ (Z : Over S) (z : Z ⟶ T), IsOpenImmersion z.left ∧ p ∈ Set.range z.left ∧ (addF A).map z.op y = (addF A).map z.op y') → y = y') := by
  intro S A _ hA T y y' h
  refine Subtype.ext (sub_eq_zero.1 (GlobalTheory.T.rigidified_picard_class_zero_of_locally_zero S A T hA (y.1 - y'.1) ?_ fun p ↦ ?_))
  · rw [map_sub, y.2.pull_unit_eq_zero, y'.2.pull_unit_eq_zero, sub_zero]
  · obtain ⟨Z, z, hz, hp, e⟩ := h p
    refine ⟨Z, z, hz, hp, ?_⟩
    rw [map_sub, sub_eq_zero]
    exact congrArg Subtype.val e

end GlobalTheory.PicGlue
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentableOver

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory.RepOver

noncomputable def coverOf {T : Scheme.{0}} {J : Type} (Z : J → Scheme.{0}) (z : ∀ i, Z i ⟶ T)
    (hz : ∀ i, IsOpenImmersion (z i)) (hc : ∀ p : T, ∃ i, p ∈ Set.range (z i)) : T.OpenCover :=
  Scheme.Cover.mkOfCovers J Z z (fun p => hc p) hz

theorem hom_eq_of_local {T S : Scheme.{0}} (t t' : T ⟶ S)
    (h : ∀ p : T, ∃ (Z : Scheme.{0}) (z : Z ⟶ T), IsOpenImmersion z ∧ p ∈ Set.range z ∧
      z ≫ t = z ≫ t') : t = t' := by
  choose Z z hz hp he using h
  exact Scheme.Cover.hom_ext (coverOf Z z hz (fun p => ⟨p, hp p⟩)) t t' he

theorem exists_glue {T S : Scheme.{0}} {J : Type} (Z : J → Scheme.{0}) (z : ∀ i, Z i ⟶ T)
    (hz : ∀ i, IsOpenImmersion (z i)) (hc : ∀ p : T, ∃ i, p ∈ Set.range (z i))
    (t : ∀ i, Z i ⟶ S)
    (ht : ∀ (i k : J) (Y : Scheme.{0}) (a : Y ⟶ Z i) (b : Y ⟶ Z k), a ≫ z i = b ≫ z k →
      a ≫ t i = b ≫ t k) : ∃ t₀ : T ⟶ S, ∀ i, z i ≫ t₀ = t i :=
  ⟨Scheme.Cover.glueMorphisms (coverOf Z z hz hc) t
      (fun i k => ht i k _ _ _ pullback.condition),
    fun i => Scheme.Cover.ι_glueMorphisms (coverOf Z z hz hc) t _ i⟩

variable {S : Scheme.{0}} (F : (Over S)ᵒᵖ ⥤ Type 1)

theorem map_map {X Y Z : Over S} (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z) (h : a.left ≫ b.left = c.left)
    (d : F.obj (op Z)) : F.map a.op (F.map b.op d) = F.map c.op d := by
  have : c = a ≫ b := Over.OverMorphism.ext (by simpa using h.symm)
  subst this
  simp

theorem sig_eq {Y : Scheme.{0}} (r r' : Y ⟶ S) (h : r = r') (e : F.obj (op (Over.mk r)))
    (e' : F.obj (op (Over.mk r'))) (c : Over.mk r ⟶ Over.mk r') (hc : c.left = 𝟙 Y)
    (he : F.map c.op e' = e) :
    (⟨r, e⟩ : Σ t : Y ⟶ S, F.obj (op (Over.mk t))) = ⟨r', e'⟩ := by
  subst h
  have : c = 𝟙 _ := Over.OverMorphism.ext hc
  subst this
  subst he
  simp

noncomputable def tot : Scheme.{0}ᵒᵖ ⥤ Type 1 where
  obj X := Σ t : X.unop ⟶ S, F.obj (op (Over.mk t))
  map {X Y} f := TypeCat.ofHom fun y =>
    ⟨f.unop ≫ y.1, F.map (Over.homMk f.unop rfl : Over.mk (f.unop ≫ y.1) ⟶ Over.mk y.1).op y.2⟩
  map_id X := by
    refine ConcreteCategory.hom_ext _ _ fun y => ?_
    exact sig_eq F _ _ (Category.id_comp _) _ _ _ rfl rfl
  map_comp f g := by
    refine ConcreteCategory.hom_ext _ _ fun y => ?_
    refine sig_eq F _ _ (Category.assoc _ _ _) _ _ (Over.homMk (𝟙 _) (by simp)) rfl ?_
    refine (map_map F _ _ (Over.homMk g.unop (Category.assoc _ _ _).symm) (by simp) _).trans ?_
    exact map_map F _ _ _ (by simp) _

def el {V : Over S} (v : F.obj (op V)) : (tot F).obj (op V.left) := ⟨V.hom, v⟩

theorem el_inj {V : Over S} {v v' : F.obj (op V)} (h : el F v = el F v') : v = v' :=
  eq_of_heq (Sigma.mk.inj h).2

theorem map_el {Y V : Over S} (a : Y ⟶ V) (v : F.obj (op V)) :
    (tot F).map a.left.op (el F v) = el F (F.map a.op v) :=
  sig_eq F (a.left ≫ V.hom) Y.hom (Over.w a) _ _ (Over.homMk (𝟙 _) (by simp)) rfl
    (map_map F _ _ _ (by simp) _)

theorem w_of_map_el {Y V : Over S} {a : Y.left ⟶ V.left} {v : F.obj (op V)} {y : F.obj (op Y)}
    (h : (tot F).map a.op (el F v) = el F y) : a ≫ V.hom = Y.hom :=
  congrArg Sigma.fst h

theorem w_of_map_eq {Y : Scheme.{0}} {V V' : Over S} {a : Y ⟶ V.left} {b : Y ⟶ V'.left}
    {v : F.obj (op V)} {v' : F.obj (op V')}
    (h : (tot F).map a.op (el F v) = (tot F).map b.op (el F v')) : a ≫ V.hom = b ≫ V'.hom :=
  congrArg Sigma.fst h

theorem map_eq_iff {Y V V' : Over S} (a : Y ⟶ V) (b : Y ⟶ V')
    (v : F.obj (op V)) (v' : F.obj (op V')) :
    (tot F).map a.left.op (el F v) = (tot F).map b.left.op (el F v') ↔
      F.map a.op v = F.map b.op v' := by
  rw [map_el, map_el]
  exact ⟨el_inj F, fun h => by rw [h]⟩

end GlobalTheory.RepOver


open GlobalTheory.RepOver in
theorem GlobalTheory.RepOver.representable_over : ∀ (S : Scheme.{0}) (F : (Over S)ᵒᵖ ⥤ Type 1), (∀ (T : Over S) (y y' : F.obj (op T)), (∀ p : T.left, ∃ (Z : Over S) (z : Z ⟶ T), IsOpenImmersion z.left ∧ p ∈ Set.range z.left ∧ F.map z.op y = F.map z.op y') → y = y') → (∀ (T : Over S) (J : Type) (Z : J → Over S) (z : ∀ i, Z i ⟶ T) (y : ∀ i, F.obj (op (Z i))), (∀ i, IsOpenImmersion (z i).left) → (∀ p : T.left, ∃ i, p ∈ Set.range (z i).left) → (∀ (i k : J) (Y : Over S) (a : Y ⟶ Z i) (b : Y ⟶ Z k), a ≫ z i = b ≫ z k → F.map a.op (y i) = F.map b.op (y k)) → ∃ y₀ : F.obj (op T), ∀ i, F.map (z i).op y₀ = y i) → ∀ (Ix : Type) (U : Ix → Over S) (x : ∀ i, F.obj (op (U i))), (∀ (i : Ix) (Y : Over S) (u u' : Y ⟶ U i), F.map u.op (x i) = F.map u'.op (x i) → u = u') → (∀ (i : Ix) (T : Over S) (y : F.obj (op T)), ∃ W : T.left.Opens, ∀ (Y : Over S) (a : Y ⟶ T), (∃ u : Y ⟶ U i, F.map a.op y = F.map u.op (x i)) ↔ ∀ q, a.left q ∈ W) → (∀ (T : Over S) (y : F.obj (op T)) (p : T.left), ∃ (i : Ix) (Y : Over S) (a : Y ⟶ T) (u : Y ⟶ U i), p ∈ Set.range a.left ∧ F.map a.op y = F.map u.op (x i)) → ∃ (B : Over S) (x₀ : F.obj (op B)), (∀ (T : Over S) (y : F.obj (op T)), ∃! g : T ⟶ B, F.map g.op x₀ = y) ∧ ∃ j : ∀ i, U i ⟶ B, (∀ i, IsOpenImmersion (j i).left) ∧ (∀ p : B.left, ∃ i, p ∈ Set.range (j i).left) ∧ ∀ i, F.map (j i).op x₀ = x i := by
  intro S F hsep hglue Ix U x hmono hopen hcov
  refine Exists.elim (GlobalTheory.T.representable_of_zariski_sheaf_open_charts_large (tot F) ?_ ?_ Ix (fun i => (U i).left)
    (fun i => el F (x i)) ?_ ?_ ?_) ?_
  rotate_right
  · rintro B ⟨⟨tB, dB⟩, huniv, j, hj, hc, hx⟩
    refine ⟨Over.mk tB, dB, fun T y => ?_, fun i => Over.homMk (j i)
      (w_of_map_el F (V := Over.mk tB) (hx i)), hj, hc, fun i => ?_⟩
    · obtain ⟨g, hg, hu⟩ := huniv T.left (el F y)
      refine ⟨Over.homMk g (w_of_map_el F (V := Over.mk tB) hg), ?_, fun g' hg' => ?_⟩
      · exact el_inj F ((map_el F _ dB).symm.trans hg)
      · exact Over.OverMorphism.ext (hu g'.left ((map_el F g' dB).trans (congrArg (el F) hg')))
    · exact el_inj F ((map_el F _ dB).symm.trans (hx i))
  · rintro T ⟨t, d⟩ ⟨t', d'⟩ h
    obtain rfl : t = t' := hom_eq_of_local t t' fun p => by
      obtain ⟨Z, z, hz, hp, he⟩ := h p
      exact ⟨Z, z, hz, hp, congrArg Sigma.fst he⟩
    obtain rfl : d = d' := hsep (Over.mk t) d d' fun p => by
      obtain ⟨Z, z, hz, hp, he⟩ := h p
      exact ⟨Over.mk (z ≫ t), Over.homMk z rfl, hz, hp, (map_eq_iff F _ _ d d').1 he⟩
    rfl
  · intro T J Z z y hz hc hy
    obtain ⟨t, ht⟩ := exists_glue Z z hz hc (fun i => (y i).1)
      (fun i k Y a b hab => congrArg Sigma.fst (hy i k Y a b hab))
    obtain ⟨d, hd⟩ := hglue (Over.mk t) J (fun i => Over.mk (y i).1)
      (fun i => Over.homMk (z i) (ht i)) (fun i => (y i).2) hz hc
      (fun i k Y a b hab => (map_eq_iff F a b _ _).1
        (hy i k Y.left a.left b.left (congrArg (fun c => c.left) hab)))
    exact ⟨⟨t, d⟩, fun i => (map_el F (Y := Over.mk (y i).1) (V := Over.mk t)
      (Over.homMk (z i) (ht i)) d).trans (congrArg (el F) (hd i))⟩
  · intro i Y u u' h
    have := hmono i (Over.mk (u ≫ (U i).hom)) (Over.homMk u rfl)
      (Over.homMk u' (w_of_map_eq F h).symm) ((map_eq_iff F _ _ _ _).1 h)
    exact congrArg (fun c => c.left) this
  · rintro i T ⟨t, d⟩
    obtain ⟨W, hW⟩ := hopen i (Over.mk t) d
    refine ⟨W, fun Y a => Iff.trans ?_ (hW (Over.mk (a ≫ t)) (Over.homMk a rfl))⟩
    constructor
    · rintro ⟨u, hu⟩
      exact ⟨Over.homMk u (w_of_map_eq F (V := Over.mk t) hu).symm, (map_eq_iff F _ _ _ _).1 hu⟩
    · rintro ⟨u, hu⟩
      exact ⟨u.left, (map_eq_iff F _ _ _ _).2 hu⟩
  · rintro T ⟨t, d⟩ p
    obtain ⟨i, Y, a, u, hp, h⟩ := hcov (Over.mk t) d p
    exact ⟨i, Y.left, a.left, u.left, hp, (map_eq_iff F _ _ _ _).2 h⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueOpenChartsAdditiveFamiliesRepresenting

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

theorem same_id_map {S : Scheme.{0}} {A T U : Over S} [GrpObj A] {N : LB (A ⊗ T).left} {M : LB (A ⊗ U).left}
    (hN : Fam A N) (hM : Fam A M) (u : T ⟶ U) :
    Same A N M (𝟙 T) u ↔ (addF A).map u.op (famCls hM) = famCls hN := by
  rw [same_iff_map hN hM, op_id, CategoryTheory.Functor.map_id]
  exact eq_comm

theorem glue : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (Ix : Type) (U : Ix → Over S) (M : ∀ i, LB (A ⊗ U i).left), (∀ i, IsChart A (M i)) → (∀ (K : Type) [Field K] [IsAlgClosed K] (s : Sp K ⟶ S) (N : LB (A ⊗ Over.mk s).left), Fam A N → ∃ (i : Ix) (u : Over.mk s ⟶ U i), Same A N (M i) (𝟙 _) u) → ∃ (B : Over S) (P : LB (A ⊗ B).left) (j : ∀ i, U i ⟶ B), Rep A (toUnit B) P ∧ (∀ i, IsOpenImmersion (j i).left) ∧ (∀ p : B.left, ∃ i, p ∈ Set.range (j i).left) ∧ ∀ i, Same A (M i) P (𝟙 _) (j i) := by
  intro S A _ hA Ix U M hM hcov
  obtain ⟨B, x, hu, j, ho, hc, hj⟩ := GlobalTheory.RepOver.representable_over S (addF A) (GlobalTheory.PicGlue.addF_separated S A hA) (GlobalTheory.PicGlue.addF_glue S A hA) Ix U
    (fun i ↦ famCls (hM i).fam)
    (fun i Y u u' h ↦ (hM i).inj Y u u' ((same_iff_map (hM i).fam (hM i).fam u u').2 h))
    (fun i T y ↦ by
      obtain ⟨N, hN, rfl⟩ := famCls_surj y
      obtain ⟨W, hW⟩ := (hM i).chart T N hN
      exact ⟨W, fun Y a ↦ (exists_congr fun u ↦ (same_iff_map hN (hM i).fam a u).symm).trans (hW Y a)⟩)
    (fun T y p ↦ by
      obtain ⟨K, _, _, s, hs⟩ := GlobalTheory.exists_geomPoint_through T.left p
      let a : Over.mk (s ≫ T.hom) ⟶ T := Over.homMk s rfl
      obtain ⟨N, hN, e⟩ := famCls_surj ((addF A).map a.op y)
      obtain ⟨i, u, h⟩ := hcov K (s ≫ T.hom) N hN
      exact ⟨i, _, a, u, hs, e.symm.trans ((same_id_map hN (hM i).fam u).1 h).symm⟩)
  obtain ⟨P, hP, rfl⟩ := famCls_surj x
  refine ⟨B, P, j, ⟨hP, fun T t N hN ↦ ?_⟩, ho, hc, fun i ↦ (same_id_map (hM i).fam hP _).2 (hj i)⟩
  obtain ⟨g, hg, hg'⟩ := hu T (famCls hN)
  have k : ∀ g : T ⟶ B, LBIso N (ev P (fst A T) (snd A T ≫ g)) ↔ (addF A).map g.op (famCls hP) = famCls hN :=
    fun g ↦ (same_id_iff hN.isLB hP.isLB g).symm.trans (same_id_map hN hP g)
  exact ⟨g, ⟨toUnit_unique _ _, (k g).2 hg⟩, fun g' h ↦ hg' g' ((k g').1 h.2)⟩

end GlobalTheory.PicGlue
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueOpenChartsAdditiveFamiliesRepresentingStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.glue_openCharts_additiveFamilies_representing : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (Ix : Type) (U : Ix → Over S) (M : ∀ i, LB (A ⊗ U i).left), (∀ i, IsChart A (M i)) → (∀ (K : Type) [Field K] [IsAlgClosed K] (s : Sp K ⟶ S) (N : LB (A ⊗ Over.mk s).left), Fam A N → ∃ (i : Ix) (u : Over.mk s ⟶ U i), Same A N (M i) (𝟙 _) u) → ∃ (B : Over S) (P : LB (A ⊗ B).left) (j : ∀ i, U i ⟶ B), Rep A (toUnit B) P ∧ (∀ i, IsOpenImmersion (j i).left) ∧ (∀ p : B.left, ∃ i, p ∈ Set.range (j i).left) ∧ ∀ i, Same A (M i) P (𝟙 _) (j i) := by
  first | exact @GlobalTheory.PicGlue.glue | exact GlobalTheory.PicGlue.glue | (intros; apply GlobalTheory.PicGlue.glue <;> assumption)
end
end
