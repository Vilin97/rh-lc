module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
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
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Topology.Sheaves.Init
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.SpanXLeKerAevalZero

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.ChartPointCongruence.InChartSt

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open MvPowerSeries
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF

namespace ReciprocityTheory.ChartRestriction.G.Pdiv.ChPt

attribute [local instance] Over.cartesianMonoidalCategory

def SepSt : Prop :=
  ∀ (T A O : Type) [CommRing T] [CommRing A] [Algebra T A] [CommRing O] [Algebra T O] (p : O),
    IsHausdorff (Ideal.span {p}) O → ∀ h h' : A →ₐ[T] O,
      (∀ n : ℕ, (Ideal.Quotient.mkₐ T (Ideal.span {p ^ n})).comp h = (Ideal.Quotient.mkₐ T _).comp h') → h = h'

def AlgLimSt : Prop :=
  ∀ (T A O : Type) [CommRing T] [CommRing A] [Algebra T A] [CommRing O] [Algebra T O] (p : O),
    IsAdicComplete (Ideal.span {p}) O → ∀ a : ∀ n : ℕ, A →ₐ[T] O ⧸ Ideal.span {p ^ n},
      (∀ (n : ℕ) (z : A) (y : O), Ideal.Quotient.mk _ y = a (n + 1) z → Ideal.Quotient.mk _ y = a n z) →
      ∃ h : A →ₐ[T] O, ∀ n, (Ideal.Quotient.mkₐ T (Ideal.span {p ^ n})).comp h = a n

end ReciprocityTheory.ChartRestriction.G.Pdiv.ChPt
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.ChartPointCongruence.EqOfMod

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open IsLocalRing MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open ReciprocityTheory.ChartRestriction.G.Chart (jetLift jetLift_zR jet_ext)

namespace ReciprocityTheory.ChartRestriction.G.Pdiv.ChPt

theorem smod_iff {O : Type} [CommRing O] (p : O) (n : ℕ) (u w : O) :
    u ≡ w [SMOD ((Ideal.span {p}) ^ n • ⊤ : Submodule O O)] ↔
      Ideal.Quotient.mk (Ideal.span {p ^ n}) u = Ideal.Quotient.mk _ w := by
  have h : ((Ideal.span {p}) ^ n • ⊤ : Submodule O O) = Ideal.span {p ^ n} := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  rw [SModEq.sub_mem, Ideal.Quotient.eq, h]

theorem eq_of_mod {O : Type} [CommRing O] (p : O) (hH : IsHausdorff (Ideal.span {p}) O) (u w : O)
    (h : ∀ n : ℕ, Ideal.Quotient.mk (Ideal.span {p ^ n}) u = Ideal.Quotient.mk _ w) : u = w := by
  refine sub_eq_zero.mp (hH.haus (u - w) fun n => (smod_iff p n (u - w) 0).mpr ?_)
  rw [map_sub, map_zero, h n, sub_self]

theorem algLimSt : AlgLimSt := by
  intro T A O _ _ _ _ _ p hC a hc
  have hdown : ∀ z : A, ∀ m n : ℕ, m ≤ n → ∀ y : O,
      Ideal.Quotient.mk (Ideal.span {p ^ n}) y = a n z →
        Ideal.Quotient.mk (Ideal.span {p ^ m}) y = a m z := by
    intro z m n hmn
    induction n, hmn using Nat.le_induction with
    | base => exact fun y hy => hy
    | succ n _ ih => exact fun y hy => ih y (hc n z y hy)
  have hlim : ∀ z : A, ∃ L : O, ∀ n, Ideal.Quotient.mk (Ideal.span {p ^ n}) L = a n z := by
    intro z
    have hs : ∀ n, ∃ y : O, Ideal.Quotient.mk (Ideal.span {p ^ n}) y = a n z :=
      fun n => Ideal.Quotient.mk_surjective (a n z)
    choose y hy using hs
    obtain ⟨L, hL⟩ := hC.toIsPrecomplete.prec' y (fun {m n} hmn =>
      (smod_iff p m (y m) (y n)).mpr (by rw [hy m, hdown z m n hmn (y n) (hy n)]))
    exact ⟨L, fun n => by rw [← (smod_iff p n (y n) L).mp (hL n), hy n]⟩
  choose L hL using hlim
  have huniq : ∀ x y : O, (∀ n : ℕ, Ideal.Quotient.mk (Ideal.span {p ^ n}) x =
      Ideal.Quotient.mk (Ideal.span {p ^ n}) y) → x = y :=
    fun x y H => eq_of_mod p hC.toIsHausdorff x y H
  refine ⟨
    { toFun := L
      map_one' := ?_
      map_mul' := ?_
      map_zero' := ?_
      map_add' := ?_
      commutes' := ?_ }, ?_⟩
  · exact huniq _ _ fun n => by simp only [hL, map_one]
  · intro x y
    exact huniq _ _ fun n => by simp only [hL, map_mul]
  · exact huniq _ _ fun n => by simp only [hL, map_zero]
  · intro x y
    exact huniq _ _ fun n => by simp only [hL, map_add (f := _)]
  · intro t
    refine huniq _ _ fun n => ?_
    rw [hL, AlgHom.commutes]
    exact ((Ideal.Quotient.mkₐ T (Ideal.span {p ^ n})).commutes t).symm
  · intro n
    ext z
    exact hL z n

end ReciprocityTheory.ChartRestriction.G.Pdiv.ChPt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueLim

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AdicPt

open IsLocalRing

private theorem factor_range {S : Type} [CommRing S] {Y : Scheme.{0}} {A : CommRingCat.{0}} (j : Spec A ⟶ Y)
    [IsOpenImmersion j] (f : Spec (CommRingCat.of S) ⟶ Y) (h : Set.range f ⊆ Set.range j) :
    ∃ φ : A ⟶ CommRingCat.of S, Spec.map φ ≫ j = f :=
  ⟨Spec.preimage (IsOpenImmersion.lift j f h), by rw [Spec.map_preimage, IsOpenImmersion.lift_fac]⟩

private theorem range_subset {S : Type} [CommRing S] [IsLocalRing S] {Y : Scheme.{0}} {A : CommRingCat.{0}}
    (j : Spec A ⟶ Y) [IsOpenImmersion j] (f : Spec (CommRingCat.of S) ⟶ Y)
    (h : f (closedPoint S) ∈ Set.range j) : Set.range f ⊆ Set.range j := by
  rintro _ ⟨y, rfl⟩
  exact ((IsLocalRing.specializes_closedPoint y).map f.continuous).mem_open j.isOpenEmbedding.isOpen_range h

variable {R : Type} [CommRing R] [IsLocalRing R] {a : R}

private theorem quot_local (ha : ¬ IsUnit a) (m : ℕ) : IsLocalRing (R ⧸ Ideal.span {a ^ (m + 1)}) := by
  haveI : Nontrivial (R ⧸ Ideal.span {a ^ (m + 1)}) := by
    refine Ideal.Quotient.nontrivial_iff.mpr ?_
    rw [Ne, Ideal.span_singleton_eq_top]
    exact fun h => ha (isUnit_of_dvd_unit (dvd_pow_self a (Nat.succ_ne_zero m)) h)
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

private theorem spec_closed {S S' : Type} [CommRing S] [CommRing S'] [IsLocalRing S] [IsLocalRing S']
    (f : S →+* S') (hf : Function.Surjective f) {Y : Scheme.{0}} (g : Spec (CommRingCat.of S) ⟶ Y) :
    (Spec.map (CommRingCat.ofHom f) ≫ g) (closedPoint S') = g (closedPoint S) := by
  haveI : IsLocalHom f := IsLocalHom.of_surjective f hf
  haveI : IsLocalHom (CommRingCat.ofHom f).hom := this
  exact congrArg g (Spec_closedPoint (f := CommRingCat.ofHom f))

theorem scheme_ext (ha : ¬ IsUnit a) (hc : IsAdicComplete (Ideal.span {a}) R) {Y : Scheme.{0}}
    (f g : Spec (CommRingCat.of R) ⟶ Y)
    (h : ∀ m : ℕ, Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a ^ m}))) ≫ f =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a ^ m}))) ≫ g) : f = g := by
  haveI := quot_local ha 0
  have hcl : f (closedPoint R) = g (closedPoint R) := by
    rw [← spec_closed (Ideal.Quotient.mk (Ideal.span {a ^ (0 + 1)})) Ideal.Quotient.mk_surjective f,
      ← spec_closed (Ideal.Quotient.mk (Ideal.span {a ^ (0 + 1)})) Ideal.Quotient.mk_surjective g, h]
  obtain ⟨A, j, _, hx, -⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (x := f (closedPoint R)) (U := ⊤) trivial
  obtain ⟨φ, rfl⟩ := factor_range j f (range_subset j f hx)
  obtain ⟨ψ, rfl⟩ := factor_range j g (range_subset j g (hcl ▸ hx))
  congr 2
  ext z
  refine ChPt.eq_of_mod a hc.toIsHausdorff _ _ fun m => ?_
  have e := h m
  rw [← Category.assoc, ← Category.assoc, cancel_mono, ← Spec.map_comp, ← Spec.map_comp] at e
  exact congrArg (fun k => k.hom z) (Spec.map_injective e)

theorem scheme_lim (ha : ¬ IsUnit a) (hc : IsAdicComplete (Ideal.span {a}) R) {Y : Scheme.{0}}
    (y : ∀ m : ℕ, Spec (CommRingCat.of (R ⧸ Ideal.span {a ^ m})) ⟶ Y)
    (hy : ∀ m : ℕ, Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
      (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow a (Nat.le_succ m))))) ≫ y (m + 1) = y m) :
    ∃ Q : Spec (CommRingCat.of R) ⟶ Y, ∀ m : ℕ,
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a ^ m}))) ≫ Q = y m := by
  haveI := quot_local ha
  obtain ⟨A, j, _, hx, -⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (x := y (0 + 1) (closedPoint _)) (U := ⊤) trivial
  have hcl : ∀ m : ℕ, y (m + 1) (closedPoint _) ∈ Set.range j := by
    intro m
    induction m with
    | zero => exact hx
    | succ m ih =>
      have e := spec_closed _ (Ideal.Quotient.factor_surjective (Ideal.span_singleton_le_span_singleton.mpr
        (pow_dvd_pow a (Nat.le_succ (m + 1))))) (y (m + 1 + 1))
      rw [hy (m + 1)] at e
      obtain ⟨u, hu⟩ := ih
      exact ⟨u, hu.trans e⟩
  have hr : ∀ m : ℕ, Set.range (y m) ⊆ Set.range j := by
    intro m
    rw [← hy m]
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact range_subset j _ (hcl m) ⟨_, rfl⟩
  choose φ hφ using fun m => factor_range j (y m) (hr m)
  obtain ⟨L, hL⟩ := ChPt.algLimSt ℤ A R a hc (fun m => (φ m).hom.toIntAlgHom) (by
    intro m z w hw
    have e := hy m
    rw [← hφ, ← hφ, ← Category.assoc, cancel_mono, ← Spec.map_comp] at e
    have e' := congrArg (fun k => k.hom z) (Spec.map_injective e)
    exact (congrArg (Ideal.Quotient.factor
      (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow a (Nat.le_succ m)))) hw).trans e')
  refine ⟨Spec.map (CommRingCat.ofHom L.toRingHom) ≫ j, fun m => ?_⟩
  rw [← hφ m, ← Category.assoc, ← Spec.map_comp]
  congr 2
  ext z
  exact congrArg (fun k => k z) (hL m)

theorem existsUnique_lim : ∀ (O R : Type) [CommRing O] [CommRing R] [Algebra O R] [IsLocalRing R] (a : R), ¬ IsUnit a → IsAdicComplete (Ideal.span {a}) R → ∀ (X : Over (Spec (CommRingCat.of O))) (x : ∀ m : ℕ, specO O (R ⧸ Ideal.span {a ^ m}) ⟶ X), (∀ m : ℕ, ptMap (Ideal.Quotient.factorₐ O (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow a (Nat.le_succ m)))) ≫ x (m + 1) = x m) → ∃! Q : specO O R ⟶ X, ∀ m : ℕ, ptMap (Ideal.Quotient.mkₐ O (Ideal.span {a ^ m})) ≫ Q = x m := by
  intro O R _ _ _ _ a ha hc X x hx
  obtain ⟨Q, hQ⟩ := scheme_lim ha hc (Y := X.left) (fun m => (x m).left)
    (fun m => congrArg CommaMorphism.left (hx m))
  have hw : Q ≫ X.hom = (specO O R).hom := by
    refine scheme_ext ha hc _ _ fun m => ?_
    rw [← Category.assoc, hQ]
    exact (Over.w (x m)).trans (Over.w (ptMap (Ideal.Quotient.mkₐ O (Ideal.span {a ^ m})))).symm
  refine ⟨Over.homMk Q hw, fun m => Over.OverMorphism.ext (hQ m), fun Q' hQ' => Over.OverMorphism.ext ?_⟩
  refine scheme_ext ha hc _ _ fun m => ?_
  exact (congrArg CommaMorphism.left (hQ' m)).trans (hQ m).symm

end GlobalTheory.AdicPt
end
end
end
