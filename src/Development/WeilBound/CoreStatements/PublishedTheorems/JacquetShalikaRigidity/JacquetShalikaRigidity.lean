module

public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.CauchyLoc
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.JacquetShalikaBound
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.RsPoleOfInputs
public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.ConvergenceEntriesGeneralLinearHolds
public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.AbsoluteCharacterNorms.UnitExponentHolds
public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.NewtonLow
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.ConjugateAnalyticity.RankinSelbergUnitaryOfPole
public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.DeterminantCharacterSplit.NormExponentEquality
public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.DeterminantOneCharacters.DeterminantOneConditionHolds
public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.DiagonalTermNorms.ConvergenceOfLandauEuler
public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.EulerLogarithms.EulerProductLogBound
public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.LandauIteratedDerivatives.LandauL
public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.NewtonLowerBounds.NewtonIdentitiesLowDegree
public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.NonnegativeCoefficients.DirichletSeriesUnbounded
public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.PrimeNonSummability.PrimeSumConvergesAndDiverges
public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.RemovableSingularities.RemovableSingularityHolds
public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.RigidityCriterion.JacquetShalikaRigidityOfBound
public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.SatakeTwists.SatakeTwistHolds
public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.SubtypeIteSums.CommonOfLandauEuler
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.Finset.Functor
import Mathlib.Topology.Separation.CompletelyRegular
public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.CauchyIdentity.CauchyVariationInequality

-- Source module: Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.AbsoluteRigidityLemma.AbsoluteRigidityOfCommon

section

@[expose] public section

noncomputable section

namespace PositivityTheory.RgJS

namespace AbsoluteRigidity

variable {W : Type} {q : W → ℕ} {X : Type} {d : X → ℕ} {A : ∀ x, W → Fin (d x) → ℂ}

theorem rel_symm {ι κ : Type} [Fintype ι] [Fintype κ] {x : ι → X × ℝ} {y : κ → X × ℝ}
    (h : Rel q A x y) : Rel q A y x := fun w k => (h w k).symm

def sh (τ : ℝ) (p : X × ℝ) : X × ℝ := (p.1, p.2 - τ)

theorem rel_shift (hq : ∀ w, 2 ≤ q w) {ι κ : Type} [Fintype ι] [Fintype κ] {x : ι → X × ℝ} {y : κ → X × ℝ}
    (h : Rel q A x y) (τ : ℝ) : Rel q A (sh τ ∘ x) (sh τ ∘ y) := by
  intro w k
  have hq0 : (q w : ℂ) ≠ 0 := by
    have := hq w
    exact_mod_cast (by omega : q w ≠ 0)
  have e : ∀ (a : ℂ) (t : ℝ), (a * (q w : ℂ) ^ (-((t - τ : ℝ) : ℂ))) ^ k =
      ((q w : ℂ) ^ (τ : ℂ)) ^ k * (a * (q w : ℂ) ^ (-(t : ℂ))) ^ k := by
    intro a t
    rw [← mul_pow]
    congr 1
    rw [show (q w : ℂ) ^ (τ : ℂ) * (a * (q w : ℂ) ^ (-(t : ℂ))) = a * ((q w : ℂ) ^ (τ : ℂ) * (q w : ℂ) ^ (-(t : ℂ))) by ring,
      ← Complex.cpow_add _ _ hq0]
    congr 2
    push_cast
    ring
  have h1 := congrArg (fun z => ((q w : ℂ) ^ (τ : ℂ)) ^ k * z) (h w k)
  simp only [Finset.mul_sum] at h1
  simp only [Function.comp_apply, sh, e]
  exact h1

theorem rel_remove {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] {x : ι → X × ℝ}
    {y : κ → X × ℝ} (h : Rel q A x y) (i : ι) (j : κ) (hij : x i = y j) :
    Rel q A (fun i' : {i' // i' ≠ i} => x i') (fun j' : {j' // j' ≠ j} => y j') := by
  intro w k
  have h1 := h w k
  rw [Fintype.sum_eq_add_sum_subtype_ne _ i, Fintype.sum_eq_add_sum_subtype_ne _ j, hij] at h1
  exact add_left_cancel h1

theorem exists_common (hC : Common0) (hS : Sys q X d A) {ι κ : Type} [Fintype ι] [Fintype κ]
    (x : ι → X × ℝ) (y : κ → X × ℝ) (h : Rel q A x y) (hne : Nonempty ι ∨ Nonempty κ) :
    ∃ i j, x i = y j := by
  classical
  set T : Finset ℝ := (Finset.univ.image fun i => (x i).2) ∪ (Finset.univ.image fun j => (y j).2) with hT
  have hTne : T.Nonempty := by
    rcases hne with ⟨⟨i⟩⟩ | ⟨⟨j⟩⟩
    · exact ⟨_, Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))⟩
    · exact ⟨_, Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))⟩
  set τ := T.min' hTne with hτ
  have hx : ∀ i, τ ≤ (x i).2 := fun i =>
    T.min'_le _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  have hy : ∀ j, τ ≤ (y j).2 := fun j =>
    T.min'_le _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j)))
  have hmem : τ ∈ T := T.min'_mem hTne
  have hsh := rel_shift hS.primes.two h τ
  have hinj : ∀ p p' : X × ℝ, sh τ p = sh τ p' → p = p' := fun p p' e => by
    have e1 := congrArg Prod.fst e
    have e2 := congrArg Prod.snd e
    simp only [sh] at e1 e2
    exact Prod.ext e1 (by linarith)
  rcases Finset.mem_union.1 hmem with hm | hm
  · obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hm
    obtain ⟨i', j, e⟩ := hC W q X d A hS ι κ (sh τ ∘ x) (sh τ ∘ y) hsh
      (fun i => by simp only [Function.comp_apply, sh]; linarith [hx i])
      (fun j => by simp only [Function.comp_apply, sh]; linarith [hy j])
      ⟨i, by simp only [Function.comp_apply, sh]; linarith⟩
    exact ⟨i', j, hinj _ _ e⟩
  · obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hm
    obtain ⟨j', i, e⟩ := hC W q X d A hS κ ι (sh τ ∘ y) (sh τ ∘ x) (rel_symm hsh)
      (fun j => by simp only [Function.comp_apply, sh]; linarith [hy j])
      (fun i => by simp only [Function.comp_apply, sh]; linarith [hx i])
      ⟨j, by simp only [Function.comp_apply, sh]; linarith⟩
    exact ⟨i, j', (hinj _ _ e).symm⟩

theorem main (hC : Common0) (hS : Sys q X d A) : ∀ (N : ℕ) (ι κ : Type) [Fintype ι] [Fintype κ]
    (x : ι → X × ℝ) (y : κ → X × ℝ), Fintype.card ι + Fintype.card κ ≤ N → Rel q A x y →
      ∃ s : ι ≃ κ, ∀ i, x i = y (s i) := by
  intro N
  induction N with
  | zero =>
    intro ι κ _ _ x y hN _
    have : IsEmpty ι := Fintype.card_eq_zero_iff.1 (by omega)
    have : IsEmpty κ := Fintype.card_eq_zero_iff.1 (by omega)
    exact ⟨Equiv.equivOfIsEmpty ι κ, fun i => isEmptyElim i⟩
  | succ N ih =>
    intro ι κ _ _ x y hN h
    classical
    have step : Nonempty ι ∨ Nonempty κ → ∃ s : ι ≃ κ, ∀ i, x i = y (s i) := by
      intro hne
      obtain ⟨i, j, hij⟩ := exists_common hC hS x y h hne
      have hr := rel_remove h i j hij
      have c1 : Fintype.card {i' // i' ≠ i} < Fintype.card ι := Fintype.card_subtype_lt (p := fun i' => i' ≠ i) (x := i) (by simp)
      have c2 : Fintype.card {j' // j' ≠ j} < Fintype.card κ := Fintype.card_subtype_lt (p := fun j' => j' ≠ j) (x := j) (by simp)
      obtain ⟨s', hs'⟩ := ih {i' // i' ≠ i} {j' // j' ≠ j} (fun i' => x i') (fun j' => y j') (by omega) hr
      refine ⟨(Equiv.optionSubtypeNe i).symm.trans ((Equiv.optionCongr s').trans (Equiv.optionSubtypeNe j)), fun i' => ?_⟩
      by_cases hi : i' = i
      · subst hi
        simp only [Equiv.trans_apply, Equiv.optionSubtypeNe_symm_self, Equiv.optionCongr_apply, Option.map_none,
          Equiv.optionSubtypeNe_none]
        exact hij
      · simp only [Equiv.trans_apply, Equiv.optionSubtypeNe_symm_of_ne hi, Equiv.optionCongr_apply, Option.map_some,
          Equiv.optionSubtypeNe_some]
        exact hs' ⟨i', hi⟩
    rcases isEmpty_or_nonempty ι with hι | hι
    · rcases isEmpty_or_nonempty κ with hκ | hκ
      · exact ⟨Equiv.equivOfIsEmpty ι κ, fun i => isEmptyElim i⟩
      · exact step (Or.inr hκ)
    · exact step (Or.inl hι)

end AbsoluteRigidity

theorem absolute_rigidity_of_common : Common0 → AbsRig := by
  intro hC W q X d A hS ι κ _ _ x y h
  exact AbsoluteRigidity.main hC hS _ ι κ x y le_rfl h

end PositivityTheory.RgJS
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.AbsRigClosed

section

@[expose] public section

namespace PositivityTheory.RgJS

theorem absRig_closed : AbsRig :=
  absolute_rigidity_of_common (common_of_landau_euler landauL euler_product_log_bound (convergence_of_landau_euler landauL euler_product_log_bound)
    (dirichlet_series_unbounded landauL newton_identities_low_degree euler_product_log_bound removable_singularity_holds (convergence_of_landau_euler landauL euler_product_log_bound)))

theorem rigid (h : RSPole) (hB : GlobalTheory.Published.JacquetShalikaBound) : GlobalTheory.Published.JacquetShalikaRigidity :=
  jacquet_shalika_rigidity_of_bound absRig_closed unit_exponent_holds satake_twist_holds determinant_one_condition_holds prime_sum_converges_and_diverges (rankin_selberg_unitary_of_pole norm_exponent_equality satake_twist_holds h) hB

end PositivityTheory.RgJS
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.CauchyLocalisation.PolyMulGaussianLeConst

section

@[expose] public section

noncomputable section

open scoped ComplexConjugate
open Classical

namespace PositivityTheory.RgJS.CauchySplitting

section Gen

variable {ι L : Type} [Zero L]

def Φ (F : ι → L → ℂ) (l : ι →₀ L) : ℂ := ∏ w ∈ l.support, F w (l w)

theorem Φ_eq (F : ι → L → ℂ) (h0 : ∀ w, F w 0 = 1) (l : ι →₀ L) (T : Finset ι) (hT : l.support ⊆ T) :
    Φ F l = ∏ w ∈ T, F w (l w) := by
  unfold Φ
  refine Finset.prod_subset hT fun w _ hw => ?_
  rw [Finsupp.notMem_support_iff.1 hw, h0]

def splitE (a : ι) (T : Finset ι) (ha : a ∉ T) :
    {l : ι →₀ L // l.support ⊆ insert a T} ≃ {l : ι →₀ L // l.support ⊆ T} × L where
  toFun l := (⟨l.1.erase a, fun w hw => by
      rw [Finsupp.support_erase, Finset.mem_erase] at hw
      exact (Finset.mem_insert.1 (l.2 hw.2)).resolve_left hw.1⟩, l.1 a)
  invFun p := ⟨p.1.1.update a p.2, fun w hw => by
      rw [Finsupp.mem_support_iff, Finsupp.update_apply] at hw
      by_cases h : w = a
      · exact Finset.mem_insert.2 (Or.inl h)
      · rw [if_neg h] at hw
        exact Finset.mem_insert.2 (Or.inr (p.1.2 (Finsupp.mem_support_iff.2 hw)))⟩
  left_inv l := Subtype.ext (by
    ext w
    by_cases h : w = a
    · subst h; simp [Finsupp.update_apply]
    · simp [Finsupp.update_apply, Finsupp.erase_apply, h])
  right_inv p := by
    have hpa : p.1.1 a = 0 := Finsupp.notMem_support_iff.1 fun h => ha (p.1.2 h)
    refine Prod.ext (Subtype.ext ?_) ?_
    · ext w
      by_cases h : w = a
      · subst h; simp [Finsupp.erase_apply, hpa]
      · simp [Finsupp.update_apply, Finsupp.erase_apply, h]
    · simp [Finsupp.update_apply]

theorem Φ_split (F : ι → L → ℂ) (h0 : ∀ w, F w 0 = 1) (a : ι) (T : Finset ι) (ha : a ∉ T)
    (l : {l : ι →₀ L // l.support ⊆ insert a T}) :
    Φ F l.1 = Φ F (splitE a T ha l).1.1 * F a (splitE a T ha l).2 := by
  rw [Φ_eq F h0 l.1 _ l.2, Φ_eq F h0 _ T (splitE a T ha l).1.2, Finset.prod_insert ha, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun w hw => ?_
  have hwa : w ≠ a := fun e => ha (e ▸ hw)
  simp [splitE, Finsupp.erase_apply, hwa]

variable (F : ι → L → ℂ) (h0 : ∀ w, F w 0 = 1) (hs : ∀ w, Summable fun l => ‖F w l‖)
include h0 hs

theorem fin (T : Finset ι) :
    Summable (fun l : {l : ι →₀ L // l.support ⊆ T} => ‖Φ F l.1‖) ∧
    HasSum (fun l : {l : ι →₀ L // l.support ⊆ T} => Φ F l.1) (∏ w ∈ T, ∑' l, F w l) ∧
    HasSum (fun l : {l : ι →₀ L // l.support ⊆ T} => ‖Φ F l.1‖) (∏ w ∈ T, ∑' l, ‖F w l‖) := by
  induction T using Finset.induction_on with
  | empty =>
    have hu : ∀ l : {l : ι →₀ L // l.support ⊆ ∅}, l.1 = 0 := fun l =>
      Finsupp.support_eq_empty.1 (Finset.subset_empty.1 l.2)
    haveI : Unique {l : ι →₀ L // l.support ⊆ ∅} := ⟨⟨⟨0, by simp⟩⟩, fun l => Subtype.ext (hu l)⟩
    have hΦ : ∀ l : {l : ι →₀ L // l.support ⊆ ∅}, Φ F l.1 = 1 := fun l => by rw [hu l]; simp [Φ]
    have e1 := hasSum_unique (fun l : {l : ι →₀ L // l.support ⊆ ∅} => Φ F l.1)
    have e2 := hasSum_unique (fun l : {l : ι →₀ L // l.support ⊆ ∅} => ‖Φ F l.1‖)
    rw [hΦ] at e1
    rw [hΦ, norm_one] at e2
    simp only [Finset.prod_empty]
    exact ⟨e2.summable, e1, e2⟩
  | insert a T ha ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    let e := splitE (L := L) a T ha
    have hp1 : Summable fun p : {l : ι →₀ L // l.support ⊆ T} × L => Φ F p.1.1 * F a p.2 :=
      summable_mul_of_summable_norm (f := fun l : {l : ι →₀ L // l.support ⊆ T} => Φ F l.1) (g := F a) ih1 (hs a)
    have hH := ih2.mul (hs a).of_norm.hasSum hp1
    have hp2 : Summable fun p : {l : ι →₀ L // l.support ⊆ T} × L => ‖Φ F p.1.1‖ * ‖F a p.2‖ :=
      summable_mul_of_summable_norm (f := fun l : {l : ι →₀ L // l.support ⊆ T} => ‖Φ F l.1‖)
        (g := fun x => ‖F a x‖) (by simp only [norm_norm]; exact ih1) (by simp only [norm_norm]; exact hs a)
    have hH' := ih3.mul (hs a).hasSum hp2
    have k1 : HasSum (fun l : {l : ι →₀ L // l.support ⊆ insert a T} => Φ F l.1)
        ((∏ w ∈ T, ∑' l, F w l) * ∑' l, F a l) := by
      have := (e.hasSum_iff (f := fun p : {l : ι →₀ L // l.support ⊆ T} × L => Φ F p.1.1 * F a p.2)).2 hH
      convert this using 1
      funext l
      exact Φ_split F h0 a T ha l
    have k2 : HasSum (fun l : {l : ι →₀ L // l.support ⊆ insert a T} => ‖Φ F l.1‖)
        ((∏ w ∈ T, ∑' l, ‖F w l‖) * ∑' l, ‖F a l‖) := by
      have := (e.hasSum_iff (f := fun p : {l : ι →₀ L // l.support ⊆ T} × L => ‖Φ F p.1.1‖ * ‖F a p.2‖)).2 hH'
      convert this using 1
      funext l
      rw [Φ_split F h0 a T ha l, norm_mul]
      rfl
    rw [Finset.prod_insert ha, Finset.prod_insert ha, mul_comm (∑' l, F a l), mul_comm (∑' l, ‖F a l‖)]
    exact ⟨k2.summable, k1, k2⟩

theorem main (ht : Summable fun w => (∑' l, ‖F w l‖) - 1) :
    Summable (fun l : ι →₀ L => ‖Φ F l‖) ∧ HasSum (fun l : ι →₀ L => Φ F l) (∏' w, ∑' l, F w l) := by
  set c := Real.exp (∑' w, ((∑' l, ‖F w l‖) - 1)) with hc
  have hge : ∀ w, 1 ≤ ∑' l, ‖F w l‖ := fun w => by
    have := (hs w).le_tsum 0 (fun _ _ => norm_nonneg _)
    rwa [h0, norm_one] at this
  have hprod : ∀ T : Finset ι, ∏ w ∈ T, ∑' l, ‖F w l‖ ≤ c := fun T => by
    calc ∏ w ∈ T, ∑' l, ‖F w l‖ ≤ ∏ w ∈ T, Real.exp ((∑' l, ‖F w l‖) - 1) :=
          Finset.prod_le_prod₀ (fun w _ => by linarith [hge w])
            (fun w _ => by linarith [Real.add_one_le_exp ((∑' l, ‖F w l‖) - 1)])
      _ = Real.exp (∑ w ∈ T, ((∑' l, ‖F w l‖) - 1)) := (Real.exp_sum _ _).symm
      _ ≤ c := Real.exp_le_exp.2 (ht.sum_le_tsum T (fun w _ => by linarith [hge w]))
  have hN : Summable (fun l : ι →₀ L => ‖Φ F l‖) := by
    refine summable_of_sum_le (c := c) (fun l => norm_nonneg _) fun u => ?_
    set T := u.biUnion fun l => l.support
    have hsub : ∀ l ∈ u, l.support ⊆ T := fun l hl => Finset.subset_biUnion_of_mem (fun l => l.support) hl
    obtain ⟨h1, -, h3⟩ := fin F h0 hs T
    calc ∑ l ∈ u, ‖Φ F l‖ = ∑ l ∈ u.subtype (fun l => l.support ⊆ T), ‖Φ F l.1‖ :=
          (Finset.sum_subtype_of_mem (fun l => ‖Φ F l‖) hsub).symm
      _ ≤ ∑' l : {l : ι →₀ L // l.support ⊆ T}, ‖Φ F l.1‖ := h1.sum_le_tsum _ (fun _ _ => norm_nonneg _)
      _ = ∏ w ∈ T, ∑' l, ‖F w l‖ := h3.tsum_eq
      _ ≤ c := hprod T
  have hS : Summable (fun l : ι →₀ L => Φ F l) := hN.of_norm
  refine ⟨hN, ?_⟩
  have hP : HasProd (fun w => ∑' l, F w l) (∑' l, Φ F l) := by
    change Filter.Tendsto (fun s : Finset ι => ∏ b ∈ s, ∑' l, F b l) Filter.atTop _
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨u, hu⟩ : ∃ u : Finset (ι →₀ L), ∑' l : {l // l ∉ u}, ‖Φ F l‖ < ε :=
      ((tendsto_tsum_compl_atTop_zero (fun l : ι →₀ L => ‖Φ F l‖)).eventually (gt_mem_nhds hε)).exists
    refine ⟨u.biUnion (·.support), fun T hT => ?_⟩
    obtain ⟨-, h2, -⟩ := fin F h0 hs T
    rw [dist_eq_norm, ← h2.tsum_eq, ← hS.tsum_subtype_add_tsum_subtype_compl {l | l.support ⊆ T},
      show (∑' b : {l : ι →₀ L // l.support ⊆ T}, Φ F b) = ∑' x : ↑{l : ι →₀ L | l.support ⊆ T}, Φ F x from rfl,
      sub_add_cancel_left, norm_neg]
    refine lt_of_le_of_lt ((norm_tsum_le_tsum_norm (hN.subtype _)).trans ?_) hu
    refine (hN.subtype _).tsum_le_tsum_of_inj (fun l => (⟨l.1, fun h => l.2 ?_⟩ : {l // l ∉ u}))
      (fun x y h => Subtype.ext (congrArg Subtype.val h : _)) (fun _ _ => norm_nonneg _) (fun _ => le_rfl) (hN.subtype _)
    exact (Finset.subset_biUnion_of_mem (·.support) h).trans hT
  rw [hP.tprod_eq]
  exact hS.hasSum

end Gen

theorem poly_mul_gaussian_le_const (N : ℕ) (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) :
    ((1 - x)⁻¹) ^ N - 1 ≤ (2 * N * 2 ^ N) * x := by
  have hx1 : 0 < 1 - x := by linarith
  set a := (1 - x)⁻¹ with ha
  have ha1 : 1 ≤ a := by rw [ha]; exact one_le_inv₀ hx1 |>.2 (by linarith)
  have ha2 : a ≤ 2 := by rw [ha, inv_le_comm₀ hx1 (by norm_num)]; linarith
  have hax : a - 1 ≤ 2 * x := by
    have e : a - 1 = x / (1 - x) := by rw [ha]; field_simp; ring
    rw [e, div_le_iff₀ hx1]
    nlinarith
  have hg : a ^ N - 1 = (∑ i ∈ Finset.range N, a ^ i) * (a - 1) := (geom_sum_mul a N).symm
  have hs : ∑ i ∈ Finset.range N, a ^ i ≤ N * 2 ^ N := by
    calc ∑ i ∈ Finset.range N, a ^ i ≤ ∑ _i ∈ Finset.range N, (2 : ℝ) ^ N :=
          Finset.sum_le_sum fun i hi => (pow_le_pow_left₀ (by linarith) ha2 i).trans
            (pow_le_pow_right₀ (by norm_num) (Finset.mem_range.1 hi).le)
      _ = N * 2 ^ N := by simp
  rw [hg]
  calc _ ≤ (N * 2 ^ N) * (2 * x) :=
        mul_le_mul hs hax (by linarith) (by positivity)
    _ = _ := by ring

end PositivityTheory.RgJS.CauchySplitting

namespace PositivityTheory.RgJS

open CauchySplitting

theorem cauchy_of_local_prime : CauchyLoc → PrimeOff → CAUCHY := by
  intro hC hP E _ _ S m k α β s hkm hα hβ hs
  have hq := hP E S
  set F : Off E S → (Fin k → ℤ) → ℂ := fun w l => loc (nq w) (α w) (β w) s l with hF
  have hloc := fun w : Off E S => hC m k (nq w) (α w) (β w) s hkm (hq.two w) (hα w) (hβ w) (by linarith)
  set σ := s.re with hσ
  have hx : ∀ w : Off E S, 0 ≤ (nq w : ℝ) ^ (1 - σ) ∧ (nq w : ℝ) ^ (1 - σ) ≤ 1 / 2 := fun w => by
    have h2 : (2 : ℝ) ≤ nq w := by exact_mod_cast hq.two w
    refine ⟨Real.rpow_nonneg (by linarith) _, ?_⟩
    calc (nq w : ℝ) ^ (1 - σ) ≤ (nq w : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = (nq w : ℝ)⁻¹ := Real.rpow_neg_one _
      _ ≤ 1 / 2 := by rw [one_div]; exact inv_anti₀ (by norm_num) h2
  have hge : ∀ w, 1 ≤ ∑' l, ‖F w l‖ := fun w => by
    have := (hloc w).2.2.1.le_tsum 0 (fun _ _ => norm_nonneg _)
    rwa [(hloc w).1, norm_one] at this
  have ht : Summable fun w => (∑' l, ‖F w l‖) - 1 := by
    refine Summable.of_nonneg_of_le (fun w => by linarith [hge w]) (fun w => ?_)
      ((hq.conv (σ - 1) (by linarith)).mul_left (2 * ((m * m : ℕ) : ℝ) * 2 ^ (m * m)))
    have e : (nq w : ℝ) ^ (-(σ - 1)) = (nq w : ℝ) ^ (1 - σ) := by congr 1; ring
    rw [e]
    exact (sub_le_sub_right (hloc w).2.2.2 1).trans (poly_mul_gaussian_le_const (m * m) _ (hx w).1 (hx w).2)
  obtain ⟨h1, h2⟩ := main F (fun w => (hloc w).1) (fun w => (hloc w).2.2.1) ht
  refine ⟨h1, ?_⟩
  have e : LS S α β s = ∏' w, ∑' l, F w l := by
    unfold LS eul
    congr 1
    funext w
    exact ((hloc w).2.1.tsum_eq).symm
  rw [e]
  exact h2

end PositivityTheory.RgJS
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.CauchyAll

section

@[expose] public section

namespace PositivityTheory.RgJS

theorem cauchyAll : CAUCHY := cauchy_of_local_prime cauchy_local_inequality prime_sum_converges_and_diverges

end PositivityTheory.RgJS
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.JacquetShalikaRigidity

section

@[expose] public section

namespace PositivityTheory.AdelicQuotientData

open PositivityTheory.RgJS

theorem rsPole : RSPole :=
  rsPole_of_inputs jumpWindows.automorphic_basic_setup_holds cauchyAll jumpWindows.compositionalInverseSymm JacquetShalikaLocal.l7 JacquetShalikaLocal.l12 jumpWindows.whittaker_functional_exists_holds jumpWindows.mirabolic_induction_step_holds jumpWindows.positive_matrix_block_product_holds jumpWindows.smooth_vectors_regular_holds jumpWindows.orthogonalSplitPolarizationVanishes jumpWindows.lattice_open_last_entry_holds jumpWindows.multiplicity_one_holds jumpWindows.almost_everywhere_spherical jumpWindows.hecke_operator_automorphic_holds jumpWindows.averaging_projection_linear_holds jumpWindows.local_uniqueness_auxiliary_holds jumpWindows.expCongruenceExtendsToSum jumpWindows.exists_logarithm_linear_holds (jumpWindows.finite_part_of_meet_holds JacquetShalikaLocal.l7 JacquetShalikaLocal.l12) (jumpWindows.smooth_multiplicity_normalized JacquetShalikaLocal.l7 JacquetShalikaLocal.l12) JacquetShalikaLocal.jacquetShalikaBound jumpWindows.adelic_character_condition_holds

theorem jacquetShalikaRigidity : GlobalTheory.Published.JacquetShalikaRigidity := rigid rsPole JacquetShalikaLocal.jacquetShalikaBound

theorem jacquetShalika : GlobalTheory.Published.JacquetShalika := ⟨jacquetShalikaRigidity, JacquetShalikaLocal.jacquetShalikaBound⟩

end PositivityTheory.AdelicQuotientData
end
end
