module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitExtDatumOfSplitTorusExtension
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolOfSecondQuotient
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubTrivDeltaAndEvenUnique
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslatedCubicalBundleClosedFibreUniformisationStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsMemCommonChart
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsCPMapCompCancel

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubicalTrivTranslateOrderTwo

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option autoImplicit false

noncomputable section
namespace GlobalTheory.TranslateEvenTriv
open GlobalTheory.UU

theorem exists_gen_pull {X X' Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {F : X' ⟶ X} {L' : LB X'} (e : L' = L.pull F)
    {K : Type} [Fintype K] (φ : K → (Y ⟶ X')) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L (fun k => φ k ≫ F) ε))
    (ht : t.IsGen) : ∃ a : LB.Gen (LB.LinComb L' φ ε), a.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι), Good L z J →
        (∀ q, HEq (J' q) (fun _ : PUnit.{1} => J (q ≫ F))) → val a r z J' = val t r z J := by
  subst e
  have h := pull_isLB hL F
  have hc : ∀ k, φ k ≫ F = 𝟙 Y ≫ (fun k => φ k ≫ F) k := fun k => (Category.id_comp _).symm
  obtain ⟨a, ha, Ha⟩ := CubTransport.exists_pmaps ((isGen_iff _).1 (pullIso_isGen hL F)) hL h (𝟙 Y) hc t ht
  refine ⟨a, ha, fun Z r z J J' hJ hJ' => ?_⟩
  obtain rfl : J' = fun q _ => J (q ≫ F) := funext fun q => eq_of_heq (hJ' q)
  have hg : Good (L.pull F) z (fun q _ => J (q ≫ F)) := fun q => mem_pull.2 (hJ (q ≫ F))
  have := CubTransport.val_pmaps hc Ha r hJ hg
  rw [Category.comp_id, Finset.prod_eq_one, _root_.one_mul] at this
  · exact this.symm
  · intro k _
    have : gw (pullIso L F) (r ≫ φ k) z (J ((r ≫ φ k) ≫ F)) (fun _ => J ((r ≫ φ k) ≫ F)) = 1 :=
      gm_self h (r ≫ φ k) z (hg (r ≫ φ k))
    rw [this, one_zpow]

theorem exists_good_of_pull {X Z : Scheme.{0}} {L L' : LB X} {F : X ⟶ X} (hF : F ≫ F = 𝟙 X) (e : L' = L.pull F)
    {z : Z} {J' : (Z ⟶ X) → L'.ι} (hJ' : Good L' z J') :
    ∃ J : (Z ⟶ X) → L.ι, Good L z J ∧ ∀ q, HEq (J' q) (fun _ : PUnit.{1} => J (q ≫ F)) := by
  subst e
  refine ⟨fun q => J' (q ≫ F) PUnit.unit, fun q => ?_, fun q => heq_of_eq ?_⟩
  · have : ((q ≫ F) ≫ F) z ∈ L.U (J' (q ≫ F) PUnit.unit) := (mem_pull (F := F)).1 (hJ' (q ≫ F))
    rwa [Category.assoc, hF, Category.comp_id] at this
  · show J' q = J' ((q ≫ F) ≫ F)
    rw [Category.assoc, hF, Category.comp_id]

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]


omit [IsCommMonObj G] in
theorem comp_translate (a : 𝟙_ (Over S) ⟶ G) {T : Over S} (g : T ⟶ G) :
    g ≫ ((toUnit G ≫ a) * 𝟙 G) = (toUnit T ≫ a) * g := by
  rw [MonObj.comp_mul, comp_toUnit_assoc, Category.comp_id]

variable {X : Type} [AddCommGroup X] (Q : TQ G X)


omit [IsCommMonObj G] in
theorem mul_torus_comp {T : Over S} (g : T ⟶ G) (x : T ⟶ splitTorus S X) : (g * (x ≫ Q.i)) ≫ Q.q = g ≫ Q.q := by
  have := Q.q_hom
  have e : Q.i ≫ Q.q = 1 := Q.isKernel.w
  rw [MonObj.mul_comp, Category.assoc, e, MonObj.comp_one, _root_.mul_one]

theorem exists_gen_torus {P₁ : CP G} (D : Q.Desc P₁) (a : 𝟙_ (Over S) ⟶ G) :
    ∃ s : LB.Gen (LB.LinComb P₁.L.L (K := Fin 2) (fun k => ![Q.i.left, (1 : splitTorus S X ⟶ G).left] k ≫
      ((toUnit G ≫ a) * 𝟙 G).left) ![1, -1]), s.IsGen ∧
      ∀ (T : Over S) (x : T ⟶ splitTorus S X) (z : T.left) (N) (J), Good D.M.L.L z N → Good P₁.L.L z J →
        ∀ W : (T ⟶ G) → (T.left.presheaf.stalk z)ˣ,
          (∀ g, W g = gw D.w g.left z (N (g.left ≫ Q.q.left)) (J g.left)) →
          val s x.left z J = W (toUnit T ≫ a) * (W ((toUnit T ≫ a) * (x ≫ Q.i)))⁻¹ := by
  obtain ⟨t, ht, v⟩ := exists_gen D.M.L.isLB (φ := (PEmpty.elim : PEmpty → ((splitTorus S X).left ⟶ Q.B.left)))
    (ε := PEmpty.elim) (K' := Fin 2) (φ' := fun _ => ((toUnit (splitTorus S X) ≫ a) ≫ Q.q).left)
    (ε' := ![1, -1]) (fun U _ h => by simp [Fin.prod_univ_two]) (LB.oneGen D.M.L.L)
    (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
  have hc : ∀ k : Fin 2, (![Q.i.left, (1 : splitTorus S X ⟶ G).left] k ≫ ((toUnit G ≫ a) * 𝟙 G).left) ≫ Q.q.left =
      𝟙 _ ≫ ((toUnit (splitTorus S X) ≫ a) ≫ Q.q).left := fun k => by
    rw [Category.id_comp]
    fin_cases k
    · refine congrArg (fun q => q.left) (show (Q.i ≫ ((toUnit G ≫ a) * 𝟙 G)) ≫ Q.q = _ from ?_)
      have := mul_torus_comp Q (toUnit (splitTorus S X) ≫ a) (𝟙 _)
      rw [Category.id_comp] at this
      rw [comp_translate, this]
    · refine congrArg (fun q => q.left) (show ((1 : splitTorus S X ⟶ G) ≫ ((toUnit G ≫ a) * 𝟙 G)) ≫ Q.q = _ from ?_)
      rw [comp_translate, _root_.mul_one]
  obtain ⟨s, hs, Hs⟩ := CubTransport.exists_pmaps ((isGen_iff _).1 D.map.gen) D.M.L.isLB P₁.L.isLB (𝟙 _) hc t ht
  refine ⟨s, hs, fun T x z N J hN hJ W hW => ?_⟩
  have e := CubTransport.val_pmaps hc Hs x.left hN hJ
  rw [v _ _ z N hN, val_one] at e
  have hτ : ∀ g : T ⟶ G, g.left ≫ ((toUnit G ≫ a) * 𝟙 G).left = ((toUnit T ≫ a) * g).left := fun g =>
    congrArg (fun q => q.left) (comp_translate a g)
  have e₂ := CubTrivTorus.prod_cubTriv Q.i x (fun q => gw D.w (q ≫ ((toUnit G ≫ a) * 𝟙 G).left) z
    (N ((q ≫ ((toUnit G ≫ a) * 𝟙 G).left) ≫ Q.q.left)) (J (q ≫ ((toUnit G ≫ a) * 𝟙 G).left)))
  rw [hτ, hτ, _root_.mul_one, ← hW, ← hW] at e₂
  simp only [← Category.assoc x.left] at e
  have e₃ := e.trans (congrArg₂ (· * ·) e₂ rfl)
  apply Additive.ofMul.injective
  have e₄ := congrArg Additive.ofMul e₃
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at e₄ ⊢
  linear_combination (norm := abel) -e₄

theorem exists_even_cubTriv : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (X : Type) [AddCommGroup X]
    (Q : GlobalTheory.UU.TQ G X) (P₁ : GlobalTheory.UU.CP G), Nonempty (Q.Desc P₁) → ∀ a : 𝟙_ (Over S) ⟶ G, a ^ 2 = 1 →
    ∀ P : GlobalTheory.UU.CP G, P.L.L = P₁.L.L.pull ((toUnit G ≫ a) * 𝟙 G).left →
    (∀ (T : Over S) (x : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → P₁.L.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good P₁.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        val P.sym x.left z J' =
          val P₁.sym ((toUnit T ≫ a) * x).left z J * (val P₁.sym (toUnit T ≫ a).left z J)⁻¹) →
    (∀ (T : Over S) (x y u : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → P₁.L.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good P₁.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        cubV P.c z J' x y u = cubV P₁.c z J x y ((toUnit T ≫ a) * u) * (cubV P₁.c z J x y (toUnit T ≫ a))⁻¹) →
    ∃ σ : GlobalTheory.UU.CubTriv P.c Q.i, σ.Even := by
  rintro S G _ _ X _ Q P₁ ⟨D⟩ a ha P hP hsym hcub
  have := Q.i_hom
  have hinv : ∀ T : Over S, (toUnit T ≫ a)⁻¹ = toUnit T ≫ a := fun T => by
    rw [inv_eq_iff_mul_eq_one, ← MonObj.comp_mul, ← pow_two, ha, MonObj.comp_one]
  have hF : ((toUnit G ≫ a) * 𝟙 G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left = 𝟙 G.left := by
    refine congrArg (fun q => q.left) (show ((toUnit G ≫ a) * 𝟙 G) ≫ ((toUnit G ≫ a) * 𝟙 G) = 𝟙 G from ?_)
    rw [comp_translate, ← _root_.mul_assoc, (inv_eq_iff_mul_eq_one.1 (hinv G)), _root_.one_mul]
  obtain ⟨s, hs, vs⟩ := exists_gen_torus Q D a
  obtain ⟨σ, hσ, vσ⟩ := exists_gen_pull P₁.L.isLB hP _ _ s hs
  have hq : ∀ {T : Over S} (g : T ⟶ G) (x : T ⟶ splitTorus S X), (g * (x ≫ Q.i)).left ≫ Q.q.left = g.left ≫ Q.q.left :=
    fun g x => congrArg (fun q => q.left) (mul_torus_comp Q g x)
  refine ⟨⟨σ, hσ, fun T x y u z J' hJ' => ?_⟩, fun T x z J' hJ' => ?_⟩
  all_goals
    obtain ⟨J, hJ, hJJ⟩ := exists_good_of_pull hF hP hJ'
    obtain ⟨N, hN⟩ := exists_good_pt D.M.L.isLB z
    obtain ⟨W, hW⟩ : ∃ W : (T ⟶ G) → (T.left.presheaf.stalk z)ˣ,
      ∀ g, W g = gw D.w g.left z (N (g.left ≫ Q.q.left)) (J g.left) := ⟨_, fun _ => rfl⟩
    have v : ∀ t : T ⟶ splitTorus S X, val σ t.left z J' = W (toUnit T ≫ a) * (W ((toUnit T ≫ a) * (t ≫ Q.i)))⁻¹ :=
      fun t => (vσ _ t.left z J J' hJ hJJ).trans (vs T t z N J hN hJ W hW)
    obtain ⟨-, a₂, a₃⟩ := D.map.vals T z J N hJ hN W hW
  · have b₁ := a₃ (x ≫ Q.i) (y ≫ Q.i) ((toUnit T ≫ a) * (u ≫ Q.i))
    have b₂ := a₃ (x ≫ Q.i) (y ≫ Q.i) (toUnit T ≫ a)
    have e : toBase (f := 𝟙 S) (g := Q.q.left) (by simp) ((toUnit T ≫ a) * (u ≫ Q.i)) =
        toBase (f := 𝟙 S) (g := Q.q.left) (by simp) (toUnit T ≫ a) := Over.OverMorphism.ext (hq _ u)
    rw [e] at b₁
    rw [hcub T _ _ _ z J J' hJ hJJ]
    simp only [v, MonObj.mul_comp]
    generalize x ≫ Q.i = x' at *
    generalize y ≫ Q.i = y' at *
    generalize u ≫ Q.i = u' at *
    generalize toUnit T ≫ a = A at *
    rw [mul_left_comm x' A, mul_left_comm y' A, mul_left_comm (x' * y') A] at b₁
    rw [mul_comm x' A, mul_comm y' A, mul_comm (x' * y') A] at b₂
    apply Additive.ofMul.injective
    have c₁ := congrArg Additive.ofMul b₁
    have c₂ := congrArg Additive.ofMul b₂
    simp only [ofMul_mul, ofMul_inv] at c₁ c₂ ⊢
    linear_combination (norm := abel) c₁ - c₂
  · have b₁ := a₂ ((toUnit T ≫ a) * (x ≫ Q.i))
    have b₂ := a₂ (toUnit T ≫ a)
    rw [hq, mul_inv, hinv] at b₁
    rw [hinv] at b₂
    show val σ _ z J' = _ * val σ _ z J'
    rw [hsym T _ z J J' hJ hJJ, v, v, GrpObj.inv_comp]
    apply Additive.ofMul.injective
    have c₁ := congrArg Additive.ofMul b₁
    have c₂ := congrArg Additive.ofMul b₂
    simp only [ofMul_mul, ofMul_inv] at c₁ c₂ ⊢
    linear_combination (norm := abel) c₁ - c₂

end GlobalTheory.TranslateEvenTriv
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubicalTrivTranslateOrderTwoStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.exists_even_cubicalTriv_translate_order_two : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (X : Type) [AddCommGroup X]
    (Q : GlobalTheory.UU.TQ G X) (P₁ : GlobalTheory.UU.CP G), Nonempty (Q.Desc P₁) → ∀ a : 𝟙_ (Over S) ⟶ G, a ^ 2 = 1 →
    ∀ P : GlobalTheory.UU.CP G, P.L.L = P₁.L.L.pull ((toUnit G ≫ a) * 𝟙 G).left →
    (∀ (T : Over S) (x : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → P₁.L.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good P₁.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        val P.sym x.left z J' =
          val P₁.sym ((toUnit T ≫ a) * x).left z J * (val P₁.sym (toUnit T ≫ a).left z J)⁻¹) →
    (∀ (T : Over S) (x y u : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → P₁.L.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good P₁.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        cubV P.c z J' x y u = cubV P₁.c z J x y ((toUnit T ≫ a) * u) * (cubV P₁.c z J x y (toUnit T ≫ a))⁻¹) →
    ∃ σ : GlobalTheory.UU.CubTriv P.c Q.i, σ.Even := by
  first | exact @GlobalTheory.TranslateEvenTriv.exists_even_cubTriv | exact GlobalTheory.TranslateEvenTriv.exists_even_cubTriv | (intros; apply GlobalTheory.TranslateEvenTriv.exists_even_cubTriv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslatedUniformisationBundleEvenClosedFibreTor

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.TransEven
open GlobalTheory.UU



theorem evenOn_translate : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 →
    ∀ P : GlobalTheory.UU.CP G, P.L.L = U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left →
      (∀ (T : Over (Sp R)) (x : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → U.LG.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good U.LG.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        val P.sym x.left z J' =
          val U.symG ((toUnit T ≫ a) * x).left z J * (val U.symG (toUnit T ≫ a).left z J)⁻¹) →
      (∀ (T : Over (Sp R)) (x y u : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → U.LG.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good U.LG.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        cubV P.c z J' x y u = cubV U.cubG z J x y ((toUnit T ≫ a) * u) * (cubV U.cubG z J x y (toUnit T ≫ a))⁻¹) →
      EvenOn P := by
  intro R _ _ _ hR D A G _ _ hS U a ha P hP hsym hcub
  have hG := GlobalTheory.firstFiveLaws.1.globalFns
  obtain ⟨wA, hwA⟩ := U.ext
  let U' := GlobalTheory.ValueForm.toPreU U.toUnifPre hG hS wA hwA
  set g := U.gt 0 with hg
  have := g.q_hom
  have := g.i_hom
  have := g.q_flat
  have := g.q_surj
  have := g.q_affine
  have hB : IsAbelianScheme (thickObj R (maximalIdeal R) 0 D.toPre.P.A) :=
    GlobalTheory.isAbelianScheme_pullback_obj _ _ D.toPre.P.isAb
  have := hB.comm
  obtain ⟨O, h₁, h₂, h₃, hd⟩ := GlobalTheory.exists_gtDatum_of_splitTorus_extension _ D.toPre.X (thickObj R (maximalIdeal R) 0 G)
    (thickObj R (maximalIdeal R) 0 D.toPre.P.A) hB g.q g.i g.q_hom g.i_hom g.q_flat g.q_surj inferInstance g.isKernel
  obtain ⟨d, hdq, hdi⟩ := hd hB
  let Q : TQ (thickObj R (maximalIdeal R) 0 G) D.toPre.X :=
    { B := thickObj R (maximalIdeal R) 0 D.toPre.P.A
      isAb := hB
      q := g.q
      i := g.i
      q_hom := g.q_hom
      i_hom := g.i_hom
      q_flat := g.q_flat
      q_surj := g.q_surj
      q_affine := g.q_affine
      isKernel := g.isKernel
      loc := by
        have l := (TQ.ofGtDatum d).loc
        rw [show (TQ.ofGtDatum d).q = g.q from hdq, show (TQ.ofGtDatum d).i = g.i from hdi] at l
        exact l }
  obtain ⟨P₀, hlev⟩ := exists_isLevelCP (maximalIdeal R) 0 U'.P
  have hlev' := hlev
  obtain ⟨w₀, h₀⟩ := hlev
  obtain ⟨rig, hr, c, σ, h₁, h₂, h₃, H⟩ := exists_isCPMap U'.P (toBase_mul_pullback G (thick R (maximalIdeal R) 0)) _
    (pull_isLB U'.P.L.isLB _) _ (pullIso_isGen U'.P.L.isLB (pullback.fst G.hom (thick R (maximalIdeal R) 0)))
  obtain ⟨w₁, k₁⟩ := GlobalTheory.ClosedPol.cpMap_congr (Category.id_comp _).symm (Category.id_comp _).symm h₀
    (by rw [Category.id_comp, Category.id_comp]; exact pullback.condition)
  obtain ⟨w₂, k₂, -⟩ := (isCPMap_comp_cancel _ _ _ _ _ _ _ _ _ _ P₀ _ _ _ (𝟙 _) (by simp) _ H).2
    (toBase_mul_of_isMonHom (𝟙 _) _) w₁ k₁
  have H' := GlobalTheory.ClosedPol.isCPMap_w hG U' 0 H
  obtain ⟨w₃, -, k₃⟩ := H'.exists_comp k₂ (by rw [Category.id_comp, Category.id_comp]; exact Over.w (U'.gt 0).pG)
  obtain ⟨M, wM, hM⟩ := exists_isLevelCP (maximalIdeal R) 0 (CP.ofDegPre hG D.toPre)
  obtain ⟨w₄, k₄⟩ := GlobalTheory.ClosedPol.cpMap_congr rfl (Category.id_comp _) k₃
    (by rw [Category.assoc, pullback.condition, Category.id_comp]; simpa using Over.w (U'.gt 0).pG)
  obtain ⟨w₅, k₅, -⟩ := (isCPMap_comp_cancel _ _ _ _ _ _ _ _ _ M P₀ _ _ _ g.q.left
    ((Over.w g.q).trans (Category.comp_id _).symm) _ hM).2
    (toBase_mul_of_isMonHom g.q _) w₄ k₄
  have De : Q.Desc P₀ := ⟨M, w₅, k₅⟩
  obtain ⟨a₀, P', -, ha₀, hl', hL', hs', hc'⟩ := GlobalTheory.T.translatedCubicalBundle_closedFibre_uniformisation R D A G U a ha P hP hsym hcub P₀ hlev'
  obtain ⟨σ', hσ'⟩ := GlobalTheory.T.exists_even_cubicalTriv_translate_order_two _ _ D.toPre.X Q P₀ ⟨De⟩ a₀ ha₀ P' hL' hs' hc'
  exact ⟨D.toPre.X, inferInstance, inferInstance, inferInstance, Q, P', hl', σ', hσ'⟩

end GlobalTheory.Mum.TransEven
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslatedUniformisationBundleEvenClosedFibreTorStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.translatedUniformisationBundle_even_closedFibreTorus : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 →
    ∀ P : GlobalTheory.UU.CP G, P.L.L = U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left →
      (∀ (T : Over (Sp R)) (x : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → U.LG.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good U.LG.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        val P.sym x.left z J' =
          val U.symG ((toUnit T ≫ a) * x).left z J * (val U.symG (toUnit T ≫ a).left z J)⁻¹) →
      (∀ (T : Over (Sp R)) (x y u : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → U.LG.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good U.LG.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        cubV P.c z J' x y u = cubV U.cubG z J x y ((toUnit T ≫ a) * u) * (cubV U.cubG z J x y (toUnit T ≫ a))⁻¹) →
      EvenOn P := by
  first | exact @GlobalTheory.Mum.TransEven.evenOn_translate | exact GlobalTheory.Mum.TransEven.evenOn_translate | (intros; apply GlobalTheory.Mum.TransEven.evenOn_translate <;> assumption)
end
end
