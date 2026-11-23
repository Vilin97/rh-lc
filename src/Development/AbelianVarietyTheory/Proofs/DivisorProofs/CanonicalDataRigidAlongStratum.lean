module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfNsmulEqOfEqClosedPointDualNumbers
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsObjectMapsOfDualNumberIdentifications
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusRigiditySndEqZeroCanonicalChart
import Mathlib.RingTheory.DualNumber

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberPointsPulledBackObjectFromBase

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon.EpsPts

variable {S S₀ : Scheme.{0}}

theorem unit_hom (X : Scheme.{0}) : (𝟙_ (Over X)).hom = 𝟙 X := rfl

theorem exists_pt {G : Over S} {G₀ A : Over S₀} {g : S ⟶ S₀} {φ : G.left ⟶ G₀.left} {φB : G₀.left ⟶ A.left}
    (h₁ : IsPullback φ G.hom G₀.hom g) (h₂ : IsPullback φB G₀.hom A.hom (𝟙 S₀)) (a : S₀ ⟶ A.left)
    (ha : a ≫ A.hom = 𝟙 S₀) : ∃ x : S ⟶ G.left, x ≫ φ ≫ φB = g ≫ a ∧ x ≫ G.hom = 𝟙 S := by
  let P := h₂.lift (g ≫ a) g (by rw [Category.assoc, ha, Category.comp_id])
  refine ⟨h₁.lift P (𝟙 S) (by rw [h₂.lift_snd, Category.id_comp]), ?_, h₁.lift_snd _ _ _⟩
  rw [← Category.assoc, h₁.lift_fst, h₂.lift_fst]

theorem pt_unique {G : Over S} {G₀ A : Over S₀} {g : S ⟶ S₀} {φ : G.left ⟶ G₀.left} {φB : G₀.left ⟶ A.left}
    (h₁ : IsPullback φ G.hom G₀.hom g) (h₂ : IsPullback φB G₀.hom A.hom (𝟙 S₀)) {Z : Scheme.{0}} (r : Z ⟶ S)
    (x x' : Z ⟶ G.left) (hφ : x ≫ φ ≫ φB = x' ≫ φ ≫ φB) (hx : x ≫ G.hom = r) (hx' : x' ≫ G.hom = r) : x = x' := by
  apply h₁.hom_ext
  · apply h₂.hom_ext
    · simpa only [Category.assoc] using hφ
    · rw [Category.assoc, Category.assoc, h₁.w, ← Category.assoc, hx, ← Category.assoc, hx']
  · rw [hx, hx']

theorem pow_left {G : Over S} {G₀ A : Over S₀} [GrpObj G] [GrpObj G₀] [GrpObj A] {g : S ⟶ S₀}
    {φ : G.left ⟶ G₀.left} {φB : G₀.left ⟶ A.left}
    (h₁ : IsGrpPullback G G₀ g φ) (h₂ : IsGrpPullback G₀ A (𝟙 S₀) φB) (X : 𝟙_ (Over S) ⟶ G)
    (a : 𝟙_ (Over S₀) ⟶ A) (hX : X.left ≫ φ ≫ φB = g ≫ a.left) (n : ℕ) :
    (X ^ n).left ≫ φ ≫ φB = g ≫ (a ^ n).left := by
  let p₁ := pushHom h₁ (𝟙_ (Over S))
  let p₂ := pushHom h₂ (Over.mk ((𝟙_ (Over S)).hom ≫ g))
  let U : Over.mk (((𝟙_ (Over S)).hom ≫ g) ≫ 𝟙 S₀) ⟶ 𝟙_ (Over S₀) := toUnit _
  have hU : U.left = g := by
    have := Over.w U
    simpa [unit_hom] using this
  have e : p₂ (p₁ X) = preHom U a := by
    apply Over.OverMorphism.ext
    show (X.left ≫ φ) ≫ φB = U.left ≫ a.left
    rw [Category.assoc, hX, hU]
  have e' : p₂ (p₁ (X ^ n)) = preHom U (a ^ n) := by
    rw [map_pow, map_pow, e, map_pow]
  have := congrArg (fun z => z.left) e'
  rw [← Category.assoc]
  refine this.trans ?_
  show U.left ≫ (a ^ n).left = _
  rw [hU]

theorem c_nsmul {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (y : D.X) (n : ℕ) :
    D.c (n • y) = D.c y ^ n := by
  have hpadd : ∀ a b, D.c (a + b) = D.c a * D.c b := fun a b => by
    rw [D.c_add, Hom.mul_def]; rfl
  induction n with
  | zero =>
    have h := hpadd 0 0
    rw [add_zero] at h
    rw [zero_smul, pow_zero]
    exact (mul_eq_left.1 h.symm)
  | succ n ih => rw [succ_nsmul, hpadd, ih, pow_succ]

end GlobalTheory.UCanon.EpsPts

namespace GlobalTheory.UCanon


open GlobalTheory.UCanon.EpsPts in
theorem pts_eps_of_mul : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (k : Type) [Field k] (f : L.W →+* DualNumber k) (o' : LowObj D' c (f.comp L.b)) (m₁ : ObjMap o' L.o (spMap f)) (m₂ : ObjMap o' L.o (spMap (GlobalTheory.RigChart.constHom f))) (n : ℕ), (n : k) ≠ 0 → (∀ (Z : Scheme.{0}) (x : Z ⟶ o'.t.G.left) (y : Z ⟶ Sp k), x ≫ o'.t.G.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ m₁.toSABMap.φ = x ≫ m₂.toSABMap.φ) → ∀ u : L.D.X → (Sp (DualNumber k) ⟶ o'.t.G.left), (∀ y, u y ≫ o'.t.G.hom = 𝟙 _) → (∀ y, u y ≫ m₁.toSABMap.φ ≫ L.φB = spMap f ≫ (L.D.c (n • y)).left) → (∀ y, u y ≫ m₂.toSABMap.φ ≫ L.φB = spMap (GlobalTheory.RigChart.constHom f) ≫ (L.D.c (n • y)).left) → ∃ x : L.D.X → (Sp (DualNumber k) ⟶ o'.t.G.left), (∀ y, x y ≫ m₁.toSABMap.φ ≫ L.φB = spMap f ≫ (L.D.c y).left) ∧ (∀ y, x y ≫ m₂.toSABMap.φ ≫ L.φB = spMap (GlobalTheory.RigChart.constHom f) ≫ (L.D.c y).left) ∧ (∀ y, x y ≫ o'.t.G.hom = 𝟙 _) := by
  intro E _ _ _ H D' l c L k _ f o' m₁ m₂ n hn h0 u hu hu₁ hu₂
  have hc : ∀ y, (L.D.c y).left ≫ L.D.P.A.hom = 𝟙 _ := fun y => Over.w (L.D.c y)
  have ex₁ := fun y => exists_pt m₁.cart.1 L.ab.1.1 (L.D.c y).left (hc y)
  have ex₂ := fun y => exists_pt m₂.cart.1 L.ab.1.1 (L.D.c y).left (hc y)
  choose x hx₁ hxG using ex₁
  choose x₂ hx₂ hx₂G using ex₂
  haveI : IsCommMonObj o'.t.G := o'.t.comm
  have hAb : IsAbelianScheme o'.t.G := ⟨o'.t.comm, o'.t.semi.smooth, o'.proper, o'.t.semi.geomConnected⟩
  let r : Sp k ⟶ Sp (DualNumber k) := spMap (TrivSqZeroExt.fstHom k k k).toRingHom
  have hr : r ≫ spMap f = r ≫ spMap (GlobalTheory.RigChart.constHom f) := by
    simp only [r, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    all_goals (ext z; simp [GlobalTheory.RigChart.constHom])
  have heq : ∀ y, x y = x₂ y := by
    intro y
    let X : 𝟙_ (Over (Sp (DualNumber k))) ⟶ o'.t.G := Over.homMk (x y) (hxG y)
    let X₂ : 𝟙_ (Over (Sp (DualNumber k))) ⟶ o'.t.G := Over.homMk (x₂ y) (hx₂G y)
    have hpow : X ^ n = X₂ ^ n := by
      apply Over.OverMorphism.ext
      have e₁ : (X ^ n).left = u y := by
        apply pt_unique m₁.cart.1 L.ab.1.1 (𝟙 _) _ _ _ (Over.w (X ^ n)) (hu y)
        rw [pow_left m₁.cart L.ab.1 X (L.D.c y) (hx₁ y) n, hu₁ y, c_nsmul]
      have e₂ : (X₂ ^ n).left = u y := by
        apply pt_unique m₂.cart.1 L.ab.1.1 (𝟙 _) _ _ _ (Over.w (X₂ ^ n)) (hu y)
        rw [pow_left m₂.cart L.ab.1 X₂ (L.D.c y) (hx₂ y) n, hu₂ y, c_nsmul]
      rw [e₁, e₂]
    have h0' : r ≫ X.left = r ≫ X₂.left := by
      show r ≫ x y = r ≫ x₂ y
      have hh := h0 (Sp k) (r ≫ x₂ y) (𝟙 _) (by rw [Category.assoc, hx₂G, Category.comp_id, Category.id_comp])
      have hh' : r ≫ x₂ y ≫ m₁.cm.F = r ≫ x₂ y ≫ m₂.cm.F := by simpa only [Category.assoc] using hh
      have w₁ : x y ≫ m₁.cm.F ≫ L.o.t.G.hom = spMap f := by
        rw [m₁.cart.1.w, ← Category.assoc, hxG y, Category.id_comp]
      have w₂ : x₂ y ≫ m₂.cm.F ≫ L.o.t.G.hom = spMap (GlobalTheory.RigChart.constHom f) := by
        rw [m₂.cart.1.w, ← Category.assoc, hx₂G y, Category.id_comp]
      apply m₁.cart.1.hom_ext
      · simp only [Category.assoc]
        rw [hh']
        apply L.ab.1.1.hom_ext
        · simp only [Category.assoc]
          rw [hx₁ y, hx₂ y, ← Category.assoc, hr, Category.assoc]
        · simp only [Category.assoc]
          rw [w₁, w₂, hr]
      · simp only [Category.assoc]
        rw [hxG y, hx₂G y]
    exact congrArg (fun z => z.left) (eq_of_pow_eq_of_eq_at_closed k o'.t.G hAb n hn X X₂ hpow h0')
  exact ⟨x, hx₁, fun y => heq y ▸ hx₂ y, hxG⟩

end GlobalTheory.UCanon
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberPointsPulledBackObjectFromBaseStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.dualNumber_points_pulledBack_object_from_base : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (k : Type) [Field k] (f : L.W →+* DualNumber k) (o' : LowObj D' c (f.comp L.b)) (m₁ : ObjMap o' L.o (spMap f)) (m₂ : ObjMap o' L.o (spMap (GlobalTheory.RigChart.constHom f))) (n : ℕ), (n : k) ≠ 0 → (∀ (Z : Scheme.{0}) (x : Z ⟶ o'.t.G.left) (y : Z ⟶ Sp k), x ≫ o'.t.G.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ m₁.toSABMap.φ = x ≫ m₂.toSABMap.φ) → ∀ u : L.D.X → (Sp (DualNumber k) ⟶ o'.t.G.left), (∀ y, u y ≫ o'.t.G.hom = 𝟙 _) → (∀ y, u y ≫ m₁.toSABMap.φ ≫ L.φB = spMap f ≫ (L.D.c (n • y)).left) → (∀ y, u y ≫ m₂.toSABMap.φ ≫ L.φB = spMap (GlobalTheory.RigChart.constHom f) ≫ (L.D.c (n • y)).left) → ∃ x : L.D.X → (Sp (DualNumber k) ⟶ o'.t.G.left), (∀ y, x y ≫ m₁.toSABMap.φ ≫ L.φB = spMap f ≫ (L.D.c y).left) ∧ (∀ y, x y ≫ m₂.toSABMap.φ ≫ L.φB = spMap (GlobalTheory.RigChart.constHom f) ≫ (L.D.c y).left) ∧ (∀ y, x y ≫ o'.t.G.hom = 𝟙 _) := by
  first | exact @GlobalTheory.UCanon.pts_eps_of_mul | exact GlobalTheory.UCanon.pts_eps_of_mul | (intros; apply GlobalTheory.UCanon.pts_eps_of_mul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsObjectMapsOfDualNumberIdentificationsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_objectMaps_of_dualNumber_identifications : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} (c : Coeff l) (W : Type) [CommRing W] (b : c.F →+* W) (o : LowObj D' c b) (k : Type) [Field k] (f : W →+* DualNumber k) (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ o.t.G.left), IsGrpPullback B' o.t.G (spMap f) π₁ → IsGrpPullback B' o.t.G (spMap (GlobalTheory.RigChart.constHom f)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → LBIso (o.t.PP.L.pull π₁) (o.t.PP.L.pull π₂) → ∃ (o' : LowObj D' c (f.comp b)) (m₁ : ObjMap o' o (spMap f)) (m₂ : ObjMap o' o (spMap (GlobalTheory.RigChart.constHom f))) (io : o'.t.G.left ≅ B'.left), io.hom ≫ B'.hom = o'.t.G.hom ∧ m₁.toSABMap.φ = io.hom ≫ π₁ ∧ m₂.toSABMap.φ = io.hom ≫ π₂ := by
  first | exact @GlobalTheory.UCanon.EpsObj.exists_objMaps | exact GlobalTheory.UCanon.EpsObj.exists_objMaps | (intros; apply GlobalTheory.UCanon.EpsObj.exists_objMaps <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseRigidityTangentVectorConstant

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RigBase

theorem grp_through {S S₁ S₂ : Scheme.{0}} {B' : Over S₂} {Q : Over S₁} {D O : Over S} [GrpObj B'] [GrpObj Q]
    [GrpObj D] [GrpObj O] {g : S₂ ⟶ S} {π : B'.left ⟶ Q.left} {β : Q.left ⟶ D.left} {φB : O.left ⟶ D.left}
    {ρ₁ : S₂ ⟶ S₁} {j : S₁ ⟶ S} (hπ : IsGrpPullback B' Q ρ₁ π) (hβ : IsGrpPullback Q D j β)
    (hφ : IsGrpPullback O D (𝟙 S) φB) (hg : ρ₁ ≫ j = g) :
    ∃ π' : B'.left ⟶ O.left, π' ≫ φB = π ≫ β ∧ π' ≫ O.hom = B'.hom ≫ g ∧ IsGrpPullback B' O g π' := by
  have hc := (hπ.comp hβ).congr hg rfl
  have w : (π ≫ β) ≫ D.hom = (B'.hom ≫ g) ≫ 𝟙 S := by rw [Category.comp_id]; exact hc.1.w
  exact ⟨hφ.1.lift (π ≫ β) (B'.hom ≫ g) w, hφ.1.lift_fst _ _ _, hφ.1.lift_snd _ _ _,
    hφ.cancel (hc.congr (Category.comp_id g).symm (hφ.1.lift_fst _ _ _).symm) (hφ.1.lift_snd _ _ _)⟩

theorem lb_through {X Y Z T : Scheme.{0}} {L₀ : LB X} {L : LB Y} {M : LB Z} (hL₀ : L₀.IsLB) (hL : L.IsLB)
    (hM : M.IsLB) {φB : X ⟶ Y} {β : Z ⟶ Y} {π₁ π₂ : T ⟶ Z} {π₁' π₂' : T ⟶ X} (h₀ : LBIso L₀ (L.pull φB))
    (hβ : LBIso M (L.pull β)) (h : LBIso (M.pull π₁) (M.pull π₂)) (e₁ : π₁' ≫ φB = π₁ ≫ β)
    (e₂ : π₂' ≫ φB = π₂ ≫ β) : LBIso (L₀.pull π₁') (L₀.pull π₂') := by
  have key : ∀ {A : Scheme.{0}} {L' : LB A} {F : A ⟶ Y}, LBIso L' (L.pull F) → ∀ j : T ⟶ A,
      LBIso (L'.pull j) (L.pull (j ≫ F)) := fun H j =>
    LBIso.chartPull (chartPullPull _ _) (chartPullSame L _ _ _ j fun _ => rfl) H
  have a₁ := key h₀ π₁'
  have a₂ := key h₀ π₂'
  have b₁ := key hβ π₁
  have b₂ := key hβ π₂
  rw [e₁] at a₁
  rw [e₂] at a₂
  exact LBIso.trans (pull_isLB hL₀ _) (pull_isLB hL _) (pull_isLB hL₀ _) (LBIso.trans (pull_isLB hL₀ _) (pull_isLB hM _) (pull_isLB hL _)
    (LBIso.trans (pull_isLB hL₀ _) (pull_isLB hM _) (pull_isLB hM _) (LBIso.trans (pull_isLB hL₀ _) (pull_isLB hL _) (pull_isLB hM _) a₁ b₁.symm) h) b₂) a₂.symm

theorem const_on_base : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), ∀ (k : Type) [Field k] (ρ : R →+* DualNumber k) (a : Fin C.m → k), GlobalTheory.RigChart.IsConstAlong C.P.D.toPre C.s (fun i => (l.M' : ℤ) • C.δ i) ρ a → ρ.comp (Cn.ψ.comp MvPolynomial.C) = GlobalTheory.RigChart.constHom (ρ.comp (Cn.ψ.comp MvPolynomial.C)) := by
  intro E _ _ _ H Dw l Xo c φ R _ _ _ _ C Cn k _ ρ a hC
  obtain ⟨B', _, π₁, π₂, w, c', h₁, h₂, h0, hw, hc', -⟩ := hC
  obtain ⟨g, hD, -, hxe, -⟩ := Cn.data
  haveI := hD.e_hom
  have hβ : IsGrpPullback C.P.D.toPre.P.A Cn.L.D.P.A (specOf (Cn.ψ.comp MvPolynomial.C))
      (hD.e.hom.left ≫ pullback.fst Cn.L.D.P.A.hom (specOf (Cn.ψ.comp MvPolynomial.C))) :=
    ((isGrpPullback_of_iso hD.e).comp (isGrpPullback_pullback _ _)).congr (Category.id_comp _) rfl
  have hsp : ∀ ρ' : R →+* DualNumber k, spMap ρ' ≫ specOf (Cn.ψ.comp MvPolynomial.C) = spMap (ρ'.comp (Cn.ψ.comp MvPolynomial.C)) := fun ρ' => by
    rw [← Spec.map_comp]; rfl
  obtain ⟨π₁', e₁, w₁, g₁⟩ := grp_through h₁ hβ Cn.L.ab.1 (hsp ρ)
  obtain ⟨π₂', e₂, w₂, g₂⟩ := grp_through h₂ hβ Cn.L.ab.1
    (hsp _ : _ = spMap (GlobalTheory.RigChart.constHom (ρ.comp (Cn.ψ.comp MvPolynomial.C))))
  have hfst : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (ρ.comp (Cn.ψ.comp MvPolynomial.C)) =
      spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (GlobalTheory.RigChart.constHom (ρ.comp (Cn.ψ.comp MvPolynomial.C))) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
  have agree : ∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k),
      x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁' = x ≫ π₂' := by
    intro Z x y hx
    apply Cn.L.ab.1.1.hom_ext
    · rw [Category.assoc, Category.assoc, e₁, e₂, ← Category.assoc, ← Category.assoc, h0 Z x y hx]
    · rw [Category.assoc, Category.assoc, w₁, w₂, ← Category.assoc, ← Category.assoc, hx, Category.assoc,
        Category.assoc, hfst]
  obtain ⟨w₀, hw₀⟩ := Cn.L.ab.2.2
  have hLB : LBIso (Cn.L.o.t.PP.L.pull π₁') (Cn.L.o.t.PP.L.pull π₂') :=
    lb_through Cn.L.o.t.PP.isLB Cn.L.D.P.isLB C.P.D.toPre.P.isLB ⟨w₀, hw₀⟩ ⟨hD.w, hD.w_gen⟩ ⟨w, hw⟩ e₁ e₂
  obtain ⟨o', m₁, m₂, io, hio, hm₁, hm₂⟩ :=
    GlobalTheory.T.exists_objectMaps_of_dualNumber_identifications c Cn.L.W Cn.L.b Cn.L.o k (ρ.comp (Cn.ψ.comp MvPolynomial.C)) B' π₁' π₂' g₁ g₂ agree hLB
  have hn : ((l.M' : ℕ) : k) ≠ 0 := by
    intro h0'
    have hM : l.M' ≠ 0 := Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne'
    have hk : ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ((ρ.comp (Cn.ψ.comp MvPolynomial.C)).comp Cn.L.b))
        (l.M' : c.F) = 0 := by rw [map_natCast]; exact h0'
    rw [map_eq_zero_iff _ (RingHom.injective _)] at hk
    exact hM (by exact_mod_cast hk)
  have agree' : ∀ (Z : Scheme.{0}) (x : Z ⟶ o'.t.G.left) (y : Z ⟶ Sp k),
      x ≫ o'.t.G.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom →
        x ≫ m₁.toSABMap.φ = x ≫ m₂.toSABMap.φ := by
    intro Z x y hx
    rw [hm₁, hm₂, ← Category.assoc, ← Category.assoc]
    exact agree Z _ y (by rw [Category.assoc, hio, hx])
  have hinv : io.inv ≫ o'.t.G.hom = B'.hom := by rw [← hio, Iso.inv_hom_id_assoc]
  have hc : ∀ y, (C.P.D.toPre.c (Cn.e.symm y)).left ≫ hD.e.hom.left ≫ pullback.fst Cn.L.D.P.A.hom (specOf (Cn.ψ.comp MvPolynomial.C)) =
      specOf (Cn.ψ.comp MvPolynomial.C) ≫ (Cn.L.D.c (l.M' • y)).left := fun y => by
    have := hD.c_pr (Cn.e.symm y)
    rw [hxe, LinearEquiv.apply_symm_apply] at this
    exact this
  obtain ⟨x, hx₁, hx₂, hx₀⟩ := GlobalTheory.T.dualNumber_points_pulledBack_object_from_base Cn.L k (ρ.comp (Cn.ψ.comp MvPolynomial.C)) o' m₁ m₂ l.M' hn agree'
    (fun y => c' (Cn.e.symm y) ≫ io.inv)
    (fun y => by rw [Category.assoc, hinv, (hc' _).1])
    (fun y => by
      rw [hm₁]; simp only [Category.assoc, Iso.inv_hom_id_assoc]; rw [e₁, ← Category.assoc, (hc' _).2.1, Category.assoc, hc,
        ← Category.assoc, hsp])
    (fun y => by
      rw [hm₂]; simp only [Category.assoc, Iso.inv_hom_id_assoc]; rw [e₂, ← Category.assoc, (hc' _).2.2, Category.assoc, hc,
        ← Category.assoc, hsp]; rfl)
  exact Cn.L.fineEps k (ρ.comp (Cn.ψ.comp MvPolynomial.C)) o' m₁ m₂ x hx₁ hx₂ hx₀

end GlobalTheory.RigBase
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseRigidityTangentVectorConstantStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.base_rigidity_tangent_vector_constant : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), ∀ (k : Type) [Field k] (ρ : R →+* DualNumber k) (a : Fin C.m → k), GlobalTheory.RigChart.IsConstAlong C.P.D.toPre C.s (fun i => (l.M' : ℤ) • C.δ i) ρ a → ρ.comp (Cn.ψ.comp MvPolynomial.C) = GlobalTheory.RigChart.constHom (ρ.comp (Cn.ψ.comp MvPolynomial.C)) := by
  first | exact @GlobalTheory.RigBase.const_on_base | exact GlobalTheory.RigBase.const_on_base | (intros; apply GlobalTheory.RigBase.const_on_base <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusRigiditySndEqZeroCanonicalChartStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.torus_rigidity_snd_eq_zero_canonicalChart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), ∀ (k : Type) [Field k] (ρ : R →+* DualNumber k) (a : Fin C.m → k), GlobalTheory.RigChart.IsConstAlong C.P.D.toPre C.s (fun i => (l.M' : ℤ) • C.δ i) ρ a → ρ.comp (Cn.ψ.comp MvPolynomial.C) = GlobalTheory.RigChart.constHom (ρ.comp (Cn.ψ.comp MvPolynomial.C)) → ∀ j, (ρ (Cn.ψ (MvPolynomial.X (.inr j)))).snd = 0 := by
  first | exact @GlobalTheory.TorRigid.snd_eq_zero_of_isConstAlong | exact GlobalTheory.TorRigid.snd_eq_zero_of_isConstAlong | (intros; apply GlobalTheory.TorRigid.snd_eq_zero_of_isConstAlong <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalDataRigidAlongStratum

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon.Rigid

theorem isLocalHom_of_fst {R : Type} [CommRing R] [IsLocalRing R] {k : Type} [Field k] (θ : R →+* DualNumber k)
    (h : ∀ r ∈ maximalIdeal R, (θ r).fst = 0) : IsLocalHom θ := by
  refine ⟨fun r hr => ?_⟩
  by_contra hn
  have hm : r ∈ maximalIdeal R := (mem_maximalIdeal r).mpr hn
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, h r hm] at hr
  exact not_isUnit_zero hr

end GlobalTheory.UCanon.Rigid

theorem GlobalTheory.UCanon.isRigid_canon : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), GlobalTheory.RigChart.IsRigid C.P.D.toPre C.s (fun i => (l.M' : ℤ) • C.δ i) := by
  intro E _ _ _ H Dw l Xo c φ R _ _ _ hB C Cn k _ ρ a hmax hs hc
  have hbase := GlobalTheory.T.base_rigidity_tangent_vector_constant Xo c φ R hB C Cn k ρ a hc
  have htor := GlobalTheory.T.torus_rigidity_snd_eq_zero_canonicalChart Xo c φ R hB C Cn k ρ a hc hbase
  have h₁ : IsLocalHom ρ := GlobalTheory.UCanon.Rigid.isLocalHom_of_fst ρ hmax
  have h₂ : IsLocalHom (GlobalTheory.RigChart.constHom ρ) := by
    refine GlobalTheory.UCanon.Rigid.isLocalHom_of_fst _ fun r hr => ?_
    simp [GlobalTheory.RigChart.constHom, hmax r hr]
  have hψ : ρ.comp Cn.ψ = (GlobalTheory.RigChart.constHom ρ).comp Cn.ψ := by
    apply MvPolynomial.ringHom_ext
    · intro x
      have := congrArg (fun f => f x) hbase
      simpa [GlobalTheory.RigChart.constHom] using this
    · rintro (i | j)
      · simp [GlobalTheory.RigChart.constHom, Cn.bd, hs]
      · apply TrivSqZeroExt.ext
        · simp [GlobalTheory.RigChart.constHom, TrivSqZeroExt.algebraMap_eq_inl]
        · simpa [GlobalTheory.RigChart.constHom, TrivSqZeroExt.algebraMap_eq_inl] using htor j
  have heq := GlobalTheory.TChart.cuniq _ R (DualNumber k) Cn.ψ Cn.compl ρ (GlobalTheory.RigChart.constHom ρ) h₁ h₂ hψ
  intro r
  rw [heq]
  simp [GlobalTheory.RigChart.constHom, TrivSqZeroExt.algebraMap_eq_inl]
end
end
