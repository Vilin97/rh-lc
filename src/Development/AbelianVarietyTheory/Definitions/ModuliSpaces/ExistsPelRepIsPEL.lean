module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.NotGoodClassZeroSucc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Linter.HaveILetI
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionPointsUnconditional
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.NotGoodClassZeroSucc
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.MulLeftCompOfPullbackPointEquivMul
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

-- Source module: Development.AbelianVarietyTheory.Definitions.ModuliSpaces.NotPelRepOfTwoPoints

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
namespace GlobalTheory.ZM

variable {o : Type} [CommRing o] {S : Scheme.{0}} {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

namespace DimZero
open Out.Inh GlobalTheory.ZM.Model

theorem translT_zero {T : Over S} (x : T ⟶ (zeroPolAV S).A) : (Out.translT (zeroPolAV S).A x).left = 𝟙 _ := by
  have : Out.translT (zeroPolAV S).A x = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [Out.translT]
    · exact toUnit_unique _ _
  rw [this]; rfl

theorem exists_gen {X : Scheme.{0}} (L : LB X) (hL : ∀ i j, L.g i j = 1) : ∃ t : L.Gen, t.IsGen ∧ ∀ i, t.s i = 1 :=
  ⟨⟨fun _ => 1⟩, fun i j => by
    rw [hL, _root_.one_mul]; exact (map_one _).trans (map_one _).symm, fun _ => rfl⟩

theorem corr_comm {X Y : Scheme.{0}} (L : LB X) [Unique L.ι] {K : Type} [Fintype K] (φ φ' : K → (Y ⟶ X)) (ε : K → ℤ)
    (a : LB.Gen (LB.LinComb L φ ε)) (b : LB.Gen (LB.LinComb L φ' ε)) (h h' : Y ⟶ Y) (hh : h = 𝟙 Y) (hh' : h' = 𝟙 Y)
    (c : LB.Gen (LB.LinComb L (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim)) (hc : ∀ j, c.s j = 1) :
    LB.Gen.Corr L _ _ _ _ (LB.mulGen _ _ _ _ _ a (LB.pullGen _ _ _ b h))
      (LB.mulGen _ _ _ _ _ (LB.mulGen _ _ _ _ _ b (LB.pullGen _ _ _ a h')) c) := by
  subst hh hh'
  intro j j' _ _ _
  obtain rfl : j = fun _ => default := Subsingleton.elim _ _
  obtain rfl : j' = fun _ => default := Subsingleton.elim _ _
  have e1 : ∀ (V W : Y.Opens) (h1 : V ≤ W) (U U' : Y.Opens) (h2 : W ≤ U) (h3 : W ≤ U') (u : Γ(Y, U)ˣ) (v : Γ(Y, U')ˣ),
      res h1 (res h2 u * res h3 v) = res (h1.trans h2) u * res (h1.trans h3) v := by
    intros; rw [map_mul, DVR.res_res', DVR.res_res']
  refine (e1 _ _ _ _ _ _ _ _ _).trans (Eq.trans ?_ (e1 _ _ _ _ _ _ _ _ _).symm)
  refine Eq.trans ?_ (congrArg₂ (· * ·) (e1 _ _ _ _ _ _ _ _ _) ((congrArg _ (hc _)).trans (map_one _))).symm
  rw [_root_.mul_one, _root_.mul_comm]
  refine congrArg₂ (· * ·) ?_ ?_
  · exact (DVR.res_res' _ _ _)
  · exact (DVR.res_res' _ _ _).symm

theorem weilIs_zero (L : LB (zeroPolAV S).A.left) [Unique L.ι] (hL : ∀ i j, L.g i j = 1) (n : ℤ) {T : Over S}
    (x y : T ⟶ (zeroPolAV S).A) : Out.WeilIs (zeroPolAV S).A L n x y 1 := by
  intro p
  have ex : ∀ z : Out.overRes (T := T) ⊤ ⟶ (zeroPolAV S).A, ∃ θ : Out.ThetaGrp _ L n _, θ.pt = z := fun z => by
    obtain ⟨t, ht, -⟩ := exists_gen (Out.thetaLB _ L n z) (linComb_g_one L hL _ _)
    exact ⟨⟨z, t, ht⟩, rfl⟩
  refine ⟨⊤, trivial, ?_, fun θx θy _ _ => ?_⟩
  · obtain ⟨θx, hx⟩ := ex (Out.overResι ⊤ ≫ x)
    obtain ⟨θy, hy⟩ := ex (Out.overResι ⊤ ≫ y)
    exact ⟨θx, θy, hx, hy⟩
  · have hc : Out.unitRes (T := T) ⊤ 1 = 1 := map_one _
    rw [hc]
    exact corr_comm L _ _ _ _ _ _ _ (translT_zero _) (translT_zero _) _
      (fun j => (congrArg _ (map_one _)).trans (map_one _))

def zeroSieg (k : ℕ) {B : Type} [CommRing B] (ζ : B) (s : S ⟶ Sp B) : SiegPre 0 k ζ s where
  A := (zeroPolAV S).A
  comm := (zeroPolAV S).isAb.comm
  ab := (zeroPolAV S).isAb
  P := trivLB _
  isLB := trivLB_isLB _
  rig₁ := (exists_gen _ (linComb_triv_g _ _)).imp fun _ h => h.1
  rig₂ := (exists_gen _ (linComb_triv_g _ _)).imp fun _ h => h.1
  symm := lbIso_of_g _ _ (fun _ _ => rfl) (linComb_triv_g _ _)
  lev := fun _ => 1
  lev_add := fun _ _ => toUnit_unique _ _
  lev_tors := fun _ => toUnit_unique _ _
  geom := fun K _ _ x β z _ _ => by
    refine ⟨fun a => ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => toUnit_unique _ _⟩,
      fun _ _ => ⟨0, toUnit_unique _ _⟩, fun a a' => ?_⟩
    have h1 : unitOn (z ^ (2 * omegaStd a a')) = 1 := by
      have : omegaStd a a' = 0 := by simp [omegaStd]
      rw [this, mul_zero, zpow_zero]
      exact map_one _
    rw [h1]
    exact @weilIs_zero S _ (inferInstanceAs (Unique (PUnit → PUnit))) (linComb_triv_g _ _) _ _ _ _

theorem principal_zeroSieg (k : ℕ) {B : Type} [CommRing B] (ζ : B) (s : S ⟶ Sp B) : (zeroSieg k ζ s).Principal := by
  refine ⟨?_, fun _ _ _ => toUnit_unique _ _⟩
  generalize hM : (zeroSieg k ζ s).diag = M
  have hg : ∀ i j, M.g i j = 1 := by subst hM; exact linComb_triv_g _ _
  have hU : ∃ i, M.U i = ⊤ := by
    subst hM; exact ⟨fun _ => PUnit.unit, top_unique fun y _ => Set.mem_iInter.2 fun _ => trivial⟩
  obtain ⟨i₀, hi₀⟩ := hU
  change LB (𝟙_ (Over S)).left at M
  change Out.RelAmple (𝟙_ (Over S)) M
  intro U hU
  haveI : IsIso (𝟙_ (Over S)).hom := by show IsIso (𝟙 S); infer_instance
  let Y := ((𝟙_ (Over S)).hom ⁻¹ᵁ U).toScheme
  have hp : ∀ i j, (Out.powOver (𝟙_ (Over S)) M U 1).g i j = 1 := fun i j => by
    exact linComb_g_one M hg _ _ i j
  let s0 : LB.Sec (Out.powOver (𝟙_ (Over S)) M U 1) :=
    ⟨fun _ => 1, by
      intro i j; rw [hp, Units.val_one, _root_.one_mul]; repeat erw [map_one]
      all_goals rfl⟩
  have hD : Out.nonzeroLocus s0 = ⊤ := by
    apply top_unique
    intro x _
    simp only [Out.nonzeroLocus, s0, Scheme.basicOpen_one]
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i₀, Set.mem_iInter.2 fun _ => by
      show _ ∈ M.U i₀
      rw [hi₀]; trivial⟩
  refine ⟨1, le_rfl, 0, fun _ => s0, by simp only [iSup_const]; exact hD,
    fun _ => ⟨?_, fun _ => 1, ?_, ?_⟩⟩
  · rw [hD]
    have : IsAffine Y := hU
    exact isAffineOpen_top Y
  · intro j k
    erw [map_one]; (try erw [map_one]); (try erw [map_one]); exact (_root_.mul_one _).symm
  · intro p
    obtain ⟨a, rfl⟩ := surj_appLE ((𝟙_ (Over S)).hom ∣_ U) _ hD le_top p
    exact ⟨MvPolynomial.C a, MvPolynomial.eval₂Hom_C _ _ _⟩

end DimZero

end GlobalTheory.ZM
end
end
end

-- Source module: Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsPelRepIsPEL

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
namespace GlobalTheory.ZM.SFamModel
open Out.Inh GlobalTheory.ZM.Model GlobalTheory.ZM.DimZero

variable {o : Type} [CommRing o] {S S' : Scheme.{0}} {k : ℕ}

theorem isIso_of_points [IsReduced S] (A : Over S) [GrpObj A] (h : IsAbelianScheme A)
    (hp : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (y : Over.mk x ⟶ A), y = 1) : IsIso A.hom := by
  haveI := h.proper
  haveI := h.smooth
  haveI : IsReduced A.left := GlobalTheory.isReduced_of_smooth_of_isReduced A.hom
  let e : S ⟶ A.left := eSec A
  have he : e ≫ A.hom = 𝟙 S := Over.w η[A]
  haveI : IsClosedImmersion e := by
    haveI : IsClosedImmersion (e ≫ A.hom) := by rw [he]; infer_instance
    exact IsClosedImmersion.of_comp e A.hom
  haveI : Surjective e := ⟨fun a => by
    let K := AlgebraicClosure (A.left.residueField a)
    let y : Sp K ⟶ A.left := spMap (algebraMap (A.left.residueField a) K) ≫ A.left.fromSpecResidueField a
    have h1 := hp K (y ≫ A.hom) (Over.homMk y rfl)
    have h2 : y = (y ≫ A.hom) ≫ e := by
      have := congrArg (·.left) h1
      simpa [Hom.one_def, e, eSec] using this
    have h3 : y default = a := by
      simp only [y, Scheme.Hom.comp_apply]
      exact Scheme.fromSpecResidueField_apply _ _
    exact ⟨(y ≫ A.hom) default, by rw [← Scheme.Hom.comp_apply, ← h2, h3]⟩⟩
  haveI : IsIso e := isIso_of_isClosedImmersion_of_surjective e
  haveI : IsIso (e ≫ A.hom) := by rw [he]; infer_instance
  exact IsIso.of_isIso_comp_left e _

theorem siegPB_zero {B : Type} [CommRing B] {ζ' : B} {s' : S' ⟶ Sp B} (c : SiegPre 0 k ζ' s') [IsIso c.A.hom]
    (ζ : o) (s : S ⟶ Sp o) (f : S' ⟶ S) : SiegPB c (zeroSieg k ζ s) f := by
  have uniq : ∀ {T : Over S'} (x y : T ⟶ c.A), x = y := fun x y =>
    Over.OverMorphism.ext (by rw [← cancel_mono c.A.hom, Over.w x, Over.w y])
  have aux : ∀ {X Y Z : Scheme.{0}} (u : X ⟶ S') (d : S ⟶ Z) (p : Z ⟶ S) (q : X ⟶ Y) (a : Y ⟶ S') (f : S' ⟶ S),
      d ≫ p = 𝟙 S → q ≫ a = u → (u ≫ f ≫ d) ≫ p = q ≫ a ≫ f := by
    rintro X Y Z _ d p q a f h rfl
    simp [h]
  obtain ⟨r, hr⟩ := c.rig₁
  have hF : (fst c.A c.A).left ≫ (lift (1 : c.A ⟶ c.A) (𝟙 c.A)).left = 𝟙 _ := by
    have : fst c.A c.A ≫ lift (1 : c.A ⟶ c.A) (𝟙 c.A) = 𝟙 _ :=
      CartesianMonoidalCategory.hom_ext _ _ (uniq _ _) (uniq _ _)
    exact congrArg (·.left) this
  let d : 𝟙_ (Over S) ⟶ 𝟙_ (Over S) ⊗ 𝟙_ (Over S) := lift (𝟙 _) (𝟙 _)
  have d1 : d.left ≫ (fst _ _ : 𝟙_ (Over S) ⊗ 𝟙_ (Over S) ⟶ _).left = 𝟙 S := by
    rw [← Over.comp_left, lift_fst]; rfl
  have d2 : d.left ≫ (snd _ _ : 𝟙_ (Over S) ⊗ 𝟙_ (Over S) ⟶ _).left = 𝟙 S := by
    rw [← Over.comp_left, lift_snd]; rfl
  refine ⟨c.A.hom ≫ f, (c.A ⊗ c.A).hom ≫ f ≫ d.left, ⟨?_, fun T x y x₀ y₀ _ _ => ?_⟩, ⟨?_, ?_⟩,
    lbIso_of_gen _ _ _ hF _ (DVR.pullGen_isGen _ _ _ r hr (fst c.A c.A).left) (linComb_triv_g _ _), fun a => ?_⟩
  · show IsPullback (c.A.hom ≫ f) c.A.hom (𝟙 S) f
    exact IsPullback.of_vert_isIso ⟨by simp⟩
  · have h1 : (x₀ * y₀).left ≫ 𝟙 S = T.hom ≫ f := Over.w (x₀ * y₀)
    exact ((Category.comp_id _).symm.trans h1).trans
      ((congrArg (· ≫ f) (Over.w (x * y))).symm.trans (Category.assoc _ _ _))
  · exact aux _ _ _ _ _ _ d1 (Over.w (fst c.A c.A))
  · exact aux _ _ _ _ _ _ d2 (Over.w (snd c.A c.A))
  · have h1 : (c.lev a).left ≫ c.A.hom = 𝟙 S' := Over.w (c.lev a)
    have h2 : ((zeroSieg k ζ s).lev a).left ≫ 𝟙 S = 𝟙 S := Over.w ((zeroSieg k ζ s).lev a)
    exact ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ f) h1).trans (Category.id_comp _))).trans
      ((congrArg (f ≫ ·) ((Category.comp_id _).symm.trans h2)).trans (Category.comp_id _)).symm

def zeroFam (k : ℕ) (ζ : o)
    (hz : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp o) (c : SiegPre 0 k ζ s'), IsReduced S → IsIso c.A.hom) : SFam 0 k ζ where
  X := Sp o
  s := 𝟙 _
  smooth := inferInstanceAs (SmoothOfRelativeDimension 0 (𝟙 _))
  qproj := OnePoint.isQProjOver_id o
  univ := zeroSieg k ζ _
  princ := principal_zeroSieg k ζ _
  rep := fun S s' c hS _ _ => by
    haveI := hz S s' c hS
    exact ⟨s', Category.comp_id _, siegPB_zero c ζ _ s'⟩
  inj := fun _ _ _ _ _ _ _ h _ _ => by simpa using h

theorem tors_eq_one {ζ : o} (hζ : IsUnit ζ) {s' : S ⟶ Sp o} (c : SiegPre 0 k ζ s') (K : Type) [Field K]
    [IsAlgClosed K] (x : Sp K ⟶ S) (y : Over.mk x ⟶ c.A) (hy : y ^ k = 1) : y = 1 := by
  let β : o →+* K := (Spec.preimage (x ≫ s')).hom
  have hβ : x ≫ s' = spMap β := by simp [β, spMap]
  obtain ⟨h1, h2, -⟩ := c.geom K x β (hζ.map β).unit hβ rfl
  obtain ⟨a, rfl⟩ := h2 y hy
  exact (h1 a).2 ⟨0, Subsingleton.elim _ _⟩

def zeroFamLevelZero {ζ : o} (hζ : IsUnit ζ) : SFam 0 0 ζ :=
  zeroFam 0 ζ fun _ _ c _ => isIso_of_points c.A c.ab fun K _ _ x y => tors_eq_one hζ c K x y (pow_zero y)

theorem isIso_of_count
    (H : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B] (g n : ℕ), IsAbelianScheme B →
      SmoothOfRelativeDimension g B.hom → (n : K) ≠ 0 →
      Nat.card {x : (𝟙_ (Over (Sp K)) ⟶ B) // x ^ n = 1} = n ^ (2 * g))
    {ζ : o} (hζ : IsUnit ζ) (hku : IsUnit (k : o)) (hk : 2 ≤ k) {s' : S ⟶ Sp o} (c : SiegPre 0 k ζ s') [IsReduced S] :
    IsIso c.A.hom :=
  isIso_of_points c.A c.ab fun K _ _ t y => by
    have hB' : IsAbelianScheme ((Over.pullback t).obj c.A) :=
      { comm := by have := c.ab.comm; infer_instance
        smooth := by have := c.ab.smooth; show Smooth (pullback.snd _ _); infer_instance
        proper := by have := c.ab.proper; show IsProper (pullback.snd _ _); infer_instance
        geomConnected := by
          have := c.ab.geomConnected; show GeometricallyConnected (pullback.snd _ _); infer_instance }
    obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim K _ hB'
    have hn : (k : K) ≠ 0 := by
      have := hku.map (Spec.preimage (t ≫ s')).hom
      rw [map_natCast] at this
      exact this.ne_zero
    have h := H K _ g k hB' hg hn
    have hp := isGrpPullback_pullback c.A t
    have hinj : Function.Injective (pushHom hp (𝟙_ (Over (Sp K)))) := by
      intro x y hxy
      have e : x.left ≫ pullback.fst c.A.hom t = y.left ≫ pullback.fst c.A.hom t := congrArg (fun z => z.left) hxy
      exact Over.OverMorphism.ext (hp.1.hom_ext e ((Over.w x).trans (Over.w y).symm))
    have h1 : Nat.card {x : (𝟙_ (Over (Sp K)) ⟶ (Over.pullback t).obj c.A) // x ^ k = 1} = 1 := by
      rw [Nat.card_eq_one_iff_exists]
      refine ⟨⟨1, one_pow k⟩, fun x => Subtype.ext (hinj ?_)⟩
      rw [map_one]
      exact tors_eq_one hζ c K _ _ (by rw [← map_pow, x.2, map_one])
    rw [h1] at h
    obtain rfl : g = 0 := by
      rcases (Nat.pow_eq_one.1 h.symm) with h | h <;> omega
    haveI : IsIso (pullback.snd c.A.hom t) := isIso_of_dim_zero _ hB' hg
    have u : ∀ z z' : Over.mk t ⟶ c.A, z = z' := fun z z' => by
      have e : pullback.lift z.left (𝟙 _) ((Over.w z).trans (Category.id_comp t).symm) =
          pullback.lift z'.left (𝟙 _) ((Over.w z').trans (Category.id_comp t).symm) := by
        rw [← cancel_mono (pullback.snd c.A.hom t), pullback.lift_snd, pullback.lift_snd]
      have := congrArg (· ≫ pullback.fst c.A.hom t) e
      simp only [pullback.lift_fst] at this
      exact Over.OverMorphism.ext this
    exact u _ _

theorem hom_ext {h : ℕ} {ζ : o} (F : SFam h k ζ) {s' : S ⟶ Sp o} (c : SiegPre h k ζ s') (f f' : S ⟶ F.X)
    (hs : f ≫ F.s = f' ≫ F.s) (h₁ : SiegPB c F.univ f) (h₂ : SiegPB c F.univ f') : f = f' := by
  refine GlobalTheory.hom_ext_of_fromSpecStalk fun x => ?_
  obtain ⟨c', hc'⟩ := (GlobalTheory.siegPre_pullback h k o ζ S (Sp (S.presheaf.stalk x)) s' _ (S.fromSpecStalk x) c rfl).1
  exact F.inj (S.presheaf.stalk x) _ _ _ c'
    ((Category.assoc _ _ _).trans ((congrArg (S.fromSpecStalk x ≫ ·) hs).trans (Category.assoc _ _ _).symm))
    (GlobalTheory.SiegelPullComp.pb_comp h₁ hc') (GlobalTheory.SiegelPullComp.pb_comp h₂ hc')

def zeroFamLevel {ζ : o} (hζ : IsUnit ζ) (hku : IsUnit (k : o)) (hk : 2 ≤ k) : SFam 0 k ζ :=
  zeroFam k ζ fun _ _ c _ => isIso_of_count GlobalTheory.UU.TorsionCount.card_torsion_points_unconditional hζ hku hk c

end GlobalTheory.ZM.SFamModel
end
end
end
