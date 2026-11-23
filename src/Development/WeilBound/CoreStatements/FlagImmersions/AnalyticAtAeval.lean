module

public import Development.WeilBound.CoreStatements.FlagImmersions.Transport
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LiftToLogResolutionAnalytic
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackPullback
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HodgeIPIffHodgeFormConj
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtFractionNoetherianClosedStatement
import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.WeilBound.CoreStatements.VolumeEquality.Pieces

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.LiftToLogResolutionAnalyticStatement

section

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

theorem _root_.GlobalTheory.T.lift_to_log_resolution_analytic : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (D e : ℕ) (R : AnLogRes P J D), J = ⊤ → ∀ (V : Set (Fin e → ℂ)) (μ : (Fin e → ℂ) → (Σ k, ι k) → ℂ) (g : (Fin e → ℂ) → R.X), IsOpen V → (∀ q, AnalyticOnNhd ℂ (fun u => μ u q) V) → (∀ u ∈ V, SameOrbit (R.lift (g u) (g u)) (μ u)) → ContinuousOn g V ∧ ∀ k, AnalyticOnNhd ℂ (R.A.chart k ∘ g) (V ∩ g ⁻¹' (R.A.chart k).source) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.HoloLift.holo_of_analytic_lift | exact GlobalTheory.CompanionTheory.Ar.PB.HoloLift.holo_of_analytic_lift | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.HoloLift.holo_of_analytic_lift <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.FlagImmersions.ExistsInverse

section

@[expose] public section

noncomputable section

namespace RootFieldNumerics.Bh

open Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo

theorem contAt_of_holoOn {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {U : Set X} {f : X → ℂ}
    (hf : A.HoloOn U f) {x : X} (hx : x ∈ U) : ContinuousAt f x := by
  obtain ⟨j, hj⟩ := A.cover x
  have h1 := (hf j (A.chart j x) ⟨(A.chart j).map_source hj, by
    show (A.chart j).symm (A.chart j x) ∈ U
    rwa [(A.chart j).left_inv hj]⟩).continuousAt
  have h2 := h1.comp ((A.chart j).continuousAt hj)
  refine h2.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [(A.chart j).left_inv hy]

theorem surj_of_degree {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [CompactSpace Y]
    {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {h : Y → X} {S : Set X} (hc : Continuous h) (hd : IsDegreeOff A B h 1 S) :
    Function.Surjective h := by
  have h1 : IsClosed (Set.range h) := (isCompact_range hc).isClosed
  have h2 : Dense Sᶜ := interior_eq_empty_iff_dense_compl.1 hd.2.1
  have h3 : Sᶜ ⊆ Set.range h := fun x hx => by
    obtain ⟨y, hy⟩ := Set.nonempty_of_ncard_ne_zero (s := h ⁻¹' {x}) (by rw [hd.2.2.2.2.1 x hx]; exact one_ne_zero)
    exact ⟨y, hy⟩
  rw [← Set.range_eq_univ, ← h1.closure_eq]
  exact (h2.mono h3).closure_eq

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem SO_symm {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') : SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), funext fun p => by rw [inv_mul_cancel_left₀ (hc _)]⟩

theorem SO_trans {z z' z'' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') (h' : SameOrbit z' z'') : SameOrbit z z'' := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨c', hc', rfl⟩ := h'
  exact ⟨fun k => c k * c' k, fun k => mul_ne_zero (hc k) (hc' k), funext fun p => (mul_assoc _ _ _).symm⟩

theorem SO_ne {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') (q : Σ k, ι k) : z q ≠ 0 ↔ z' q ≠ 0 := by
  obtain ⟨c, hc, rfl⟩ := h
  simp [hc q.1]

theorem isOpen_lift_ne {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e) (q : Σ k, ι k) :
    IsOpen {w : R.X | R.lift w w q ≠ 0} := by
  refine isOpen_iff_mem_nhds.2 fun w hw => ?_
  filter_upwards [(R.isOpen_U w).mem_nhds (R.mem_U w),
    (contAt_of_holoOn (R.holo w q) (R.mem_U w)).eventually_ne hw] with w' h1 h2
  exact (SO_ne (R.compat w' w w' ⟨R.mem_U w', h1⟩) q).2 h2

theorem exists_inverse {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e) (hJ : J = ⊤) {X : Type} [TopologicalSpace X]
    (A : FinHolAtlas e X) (π : R.X → X) (hs : Function.Surjective π)
    (key : ∀ w₁, ∃ (O : Set X) (μ : X → (Σ k, ι k) → ℂ), IsOpen O ∧ π w₁ ∈ O ∧ (∀ q, A.HoloOn O fun x => μ x q) ∧
      ∀ w, π w ∈ O → SameOrbit (R.lift w w) (μ (π w))) :
    ∃ ψ : X → R.X, HoloMap A R.A ψ ∧ (∀ x, π (ψ x) = x) ∧ ∀ w, ψ (π w) = w := by
  have hinj : Function.Injective π := fun w w₁ e₀ => by
    obtain ⟨O, μ, -, h1, -, h2⟩ := key w₁
    have a1 := h2 w (e₀ ▸ h1)
    rw [e₀] at a1
    refine R.inj w w₁ (fun h => ?_) (SO_trans a1 (SO_symm (h2 w₁ h1)))
    simpa using h.2 1 (hJ ▸ Submodule.mem_top)
  let ψ := Function.surjInv hs
  have r : ∀ x, π (ψ x) = x := Function.surjInv_eq hs
  have loc : ∀ j, ∀ t ∈ (A.chart j).target, ∃ V, IsOpen V ∧ t ∈ V ∧ ContinuousOn (ψ ∘ (A.chart j).symm) V ∧
      ∀ k, AnalyticOnNhd ℂ (R.A.chart k ∘ (ψ ∘ (A.chart j).symm)) (V ∩ (ψ ∘ (A.chart j).symm) ⁻¹' (R.A.chart k).source) := by
    intro j t ht
    obtain ⟨O, μ, hO, h1, h2, h3⟩ := key (ψ ((A.chart j).symm t))
    rw [r] at h1
    have hV : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' O) := (A.chart j).isOpen_inter_preimage_symm hO
    refine ⟨_, hV, ⟨ht, h1⟩, GlobalTheory.T.lift_to_log_resolution_analytic K ι P J e e R hJ _ (fun u => μ ((A.chart j).symm u)) _ hV (fun q => h2 q j)
      fun u hu => ?_⟩
    have := h3 (ψ ((A.chart j).symm u)) (by rw [r]; exact hu.2)
    rwa [r] at this
  refine ⟨ψ, ⟨continuous_iff_continuousAt.2 fun x => ?_, fun j k t ht => ?_⟩, r, fun w => hinj (r _)⟩
  · obtain ⟨j, hj⟩ := A.cover x
    obtain ⟨V, hV, h1, h2, -⟩ := loc j _ ((A.chart j).map_source hj)
    refine ((h2.continuousAt (hV.mem_nhds h1)).comp ((A.chart j).continuousAt hj)).congr ?_
    filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
    simp [(A.chart j).left_inv hy]
  · obtain ⟨V, -, h1, -, h2⟩ := loc j t ht.1
    exact h2 k t ⟨h1, ht.2⟩

end RootFieldNumerics.Bh
end
end
end

-- Source module: Development.WeilBound.CoreStatements.FlagImmersions.NeZeroOfHasVal

section

@[expose] public section

noncomputable section

namespace RootFieldNumerics.Bh

open AlgebraicGeometry CategoryTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {K : Type} [Fintype K] {J : K → Type}
  [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

theorem exists_poly (T : CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩)) (hn : IsNormalScheme X)
    (c : (k : K) → J k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {a : Ω} (ha : a ∈ integralClosure (chartRingZ y c) Ω) :
    ∃ p : MRing J, aeval (fun q : Σ k, J k => y q / y ⟨q.1, c q.1⟩) p = a := by
  classical
  have hc0 : (∏ k, y ⟨k, c k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc k
  have hle : Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩) ≤ chartRingZ y c := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨j, rfl⟩
    show (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩ ∈ chartRingZ y c
    rw [← Finset.prod_div_distrib]
    exact Subalgebra.prod_mem _ fun k _ => Algebra.subset_adjoin ⟨⟨k, j k⟩, rfl⟩
  have hge : chartRingZ y c ≤ Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩) := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨⟨k, i⟩, rfl⟩
    refine Algebra.subset_adjoin ⟨Function.update c k i, ?_⟩
    show (∏ k', y ⟨k', Function.update c k i k'⟩) / ∏ k, y ⟨k, c k⟩ = y ⟨k, i⟩ / y ⟨k, c k⟩
    rw [← Finset.prod_div_distrib, Finset.prod_eq_single k]
    · rw [Function.update_self]
    · intro k' _ h
      rw [Function.update_of_ne h, div_self (hc k')]
    · simp
  have hmem : a ∈ chartRingZ y c := by
    refine hle ((T.ring c hc0 a).2 fun q hq => ?_)
    obtain ⟨h1, -, h3⟩ := GlobalTheory.T.regAt_fraction_noetherian_closed X Ω ξ T.gen q
    have h4 := h3 (hn q.1).2
    let φ : chartRingZ y c →+* regAt ξ q :=
      (algebraMap (chartRingZ y c) Ω).codRestrict _ fun r => (T.ring c hc0 r).1 (hge r.2) q hq
    have h5 : IsIntegral (regAt ξ q) a := IsIntegral.map_of_comp_eq φ (RingHom.id Ω) rfl ha
    obtain ⟨r, rfl⟩ := (isIntegrallyClosed_iff Ω).1 h4 h5
    exact r.2
  unfold chartRingZ at hmem
  rw [Algebra.adjoin_range_eq_range_aeval] at hmem
  exact hmem

variable {z : Spec (CommRingCat.of ℂ) ⟶ X} {w : (Σ k, J k) → ℂ}

theorem val_ratio (h : CoordsAt ξ y z w) (k : K) (i c : J k) (hc : w ⟨k, c⟩ ≠ 0) :
    ValAt ξ z (y ⟨k, i⟩ / y ⟨k, c⟩) (w ⟨k, i⟩ / w ⟨k, c⟩) := by
  obtain ⟨r, hr, e⟩ := (h.2 k c (IsUnit.mk0 _ hc)).2 i
  rwa [e, mul_div_cancel_right₀ _ hc]

theorem val_prod (hz : genPt ξ ⤳ centre z) {a : K → Ω} {r : K → ℂ} (h : ∀ k, ValAt ξ z (a k) (r k)) :
    ValAt ξ z (∏ k, a k) (∏ k, r k) := by
  classical
  have : ∀ s : Finset K, ValAt ξ z (∏ k ∈ s, a k) (∏ k ∈ s, r k) := fun s => by
    induction s using Finset.induction_on with
    | empty => simpa using CxVal.one hz
    | insert k s hk ih =>
      rw [Finset.prod_insert hk, Finset.prod_insert hk]
      exact CxVal.mul (h k) ih
  exact this _

theorem val_pow (hz : genPt ξ ⤳ centre z) {a : Ω} {r : ℂ} (h : ValAt ξ z a r) (n : ℕ) : ValAt ξ z (a ^ n) (r ^ n) := by
  induction n with
  | zero => simpa using CxVal.one hz
  | succ n ih => rw [pow_succ, pow_succ]; exact CxVal.mul ih h

def fn (y : (Σ k, J k) → Ω) (s : Ω) (m : ℕ) (k₀ : K) (i₀ : J k₀) (c : (k : K) → J k) : Ω :=
  s * (∏ k, y ⟨k, c k⟩) / y ⟨k₀, i₀⟩ ^ m

theorem val_fn (hz : genPt ξ ⤳ centre z) (h : CoordsAt ξ y z w) {s : Ω} {m : ℕ} {k₀ : K} (i₀ : J k₀) (c c' : (k : K) → J k)
    (hc : ∀ k, w ⟨k, c' k⟩ ≠ 0) (hi : w ⟨k₀, i₀⟩ ≠ 0) {p : MRing J}
    (hp : aeval (fun q : Σ k, J k => y q / y ⟨q.1, c' q.1⟩) p = fn y s m k₀ (c' k₀) c') :
    ValAt ξ z (fn y s m k₀ i₀ c) (aeval (fun q : Σ k, J k => w q / w ⟨q.1, c' q.1⟩) p * (∏ k, w ⟨k, c k⟩ / w ⟨k, c' k⟩) *
      (w ⟨k₀, c' k₀⟩ / w ⟨k₀, i₀⟩) ^ m) := by
  have h1 := CxVal.aeval hz (fun q : Σ k, J k => val_ratio h q.1 q.2 (c' q.1) (hc q.1)) p
  have h2 := val_prod hz fun k => val_ratio h k (c k) (c' k) (hc k)
  have h3 := val_pow hz (val_ratio h k₀ (c' k₀) i₀ hi) m
  have hy := fun k => (h.2 k (c' k) (IsUnit.mk0 _ (hc k))).1
  have hy0 := (h.2 k₀ i₀ (IsUnit.mk0 _ hi)).1
  have hP : (∏ k, y ⟨k, c' k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hy k
  have hk := hy k₀
  convert CxVal.mul (CxVal.mul h1 h2) h3 using 1
  have hp' : aeval (fun q : Σ k, J k => y ⟨q.1, q.2⟩ / y ⟨q.1, c' q.1⟩) p = fn y s m k₀ (c' k₀) c' := hp
  rw [hp', Finset.prod_div_distrib, div_pow]
  unfold fn
  field_simp

theorem fn_eq [DecidableEq K] {s : Ω} {m : ℕ} {k₀ : K} {a : K → ℤ} (ha : a k₀ = 1 ∧ ∀ k, k ≠ k₀ → a k = 0)
    (c : (k : K) → J k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    s * ∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * a k - 1)) = fn y s m k₀ (c k₀) c := by
  have e : ∀ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * a k - 1)) = y ⟨k, c k⟩ / y ⟨k, c k⟩ ^ ((m : ℤ) * a k) := fun k => by
    rw [neg_sub, zpow_sub₀ (hc k), zpow_one]
  simp only [e, Finset.prod_div_distrib]
  rw [Finset.prod_eq_single k₀ (f := fun k => y ⟨k, c k⟩ ^ ((m : ℤ) * a k))]
  · rw [ha.1, mul_one, zpow_natCast, fn, mul_div_assoc]
  · intro k _ h
    rw [ha.2 k h, mul_zero, zpow_zero]
  · simp

theorem ne_zero_of_hasVal (hz : genPt ξ ⤳ centre z) (h : CoordsAt ξ y z w) {s : Ω} {a : K → ℤ} (c : (k : K) → J k)
    (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) {p : MRing J}
    (hp : aeval (fun q : Σ k, J k => y q / y ⟨q.1, c q.1⟩) p = s * ∏ k, y ⟨k, c k⟩ ^ (-a k)) {v : ℂ} (hv : v ≠ 0)
    (hs : Small.HasVal y a s w v) : aeval (fun q : Σ k, J k => w q / w ⟨q.1, c q.1⟩) p ≠ 0 := by
  obtain ⟨dg, dh, g, h', hg, hh, hd, e1, hne, e2⟩ := hs
  have hy := fun k => (h.2 k (c k) (IsUnit.mk0 _ (hc k))).1
  have V := fun f : MRing J => CxVal.aeval hz (fun q : Σ k, J k => val_ratio h q.1 q.2 (c q.1) (hc q.1)) f
  have ey : y = fun q => y ⟨q.1, c q.1⟩ * (y ⟨q.1, q.2⟩ / y ⟨q.1, c q.1⟩) :=
    funext fun q => (mul_div_cancel₀ _ (hy q.1)).symm
  have ew : w = fun q => w ⟨q.1, c q.1⟩ * (w ⟨q.1, q.2⟩ / w ⟨q.1, c q.1⟩) :=
    funext fun q => (mul_div_cancel₀ _ (hc q.1)).symm
  have g1 := aeval_blockScale hg (fun k => y ⟨k, c k⟩) fun q => y ⟨q.1, q.2⟩ / y ⟨q.1, c q.1⟩
  have g2 := aeval_blockScale hh (fun k => y ⟨k, c k⟩) fun q => y ⟨q.1, q.2⟩ / y ⟨q.1, c q.1⟩
  have g3 := aeval_blockScale hg (fun k => w ⟨k, c k⟩) fun q => w ⟨q.1, q.2⟩ / w ⟨q.1, c q.1⟩
  rw [← ey] at g1 g2
  rw [← ew] at g3
  have key : aeval (fun q : Σ k, J k => y ⟨q.1, q.2⟩ / y ⟨q.1, c q.1⟩) g =
      aeval (fun q : Σ k, J k => y ⟨q.1, q.2⟩ / y ⟨q.1, c q.1⟩) p *
        aeval (fun q : Σ k, J k => y ⟨q.1, q.2⟩ / y ⟨q.1, c q.1⟩) h' := by
    have hp' : aeval (fun q : Σ k, J k => y ⟨q.1, q.2⟩ / y ⟨q.1, c q.1⟩) p = s * ∏ k, y ⟨k, c k⟩ ^ (-a k) := hp
    have h0 : (∏ k, y ⟨k, c k⟩ ^ dg k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hy k)
    have h1 : (∏ k, y ⟨k, c k⟩ ^ dg k) * ∏ k, y ⟨k, c k⟩ ^ (-a k) = ∏ k, y ⟨k, c k⟩ ^ dh k := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hy k), hd k]
      congr 1
      ring
    refine mul_left_cancel₀ h0 ?_
    rw [← g1, e1, g2, hp', ← h1]
    ring
  have e3 := CxVal.unique (key ▸ V g) (CxVal.mul (V p) (V h'))
  intro h0
  have h0' : aeval (fun q : Σ k, J k => w ⟨q.1, q.2⟩ / w ⟨q.1, c q.1⟩) p = 0 := h0
  rw [h0', zero_mul] at e3
  rw [e3, mul_zero, e2] at g3
  exact mul_ne_zero hv hne g3

end RootFieldNumerics.Bh
end
end
end

-- Source module: Development.WeilBound.CoreStatements.FlagImmersions.AnalyticAtAeval

section

@[expose] public section

noncomputable section

namespace RootFieldNumerics

open AlgebraicGeometry CategoryTheory NumberField Filter Topology MvPolynomial
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB Bh

theorem Bh.analyticAt_aeval {σ : Type} {n : ℕ} {f : σ → (Fin n → ℂ) → ℂ} {t : Fin n → ℂ} (h : ∀ q, AnalyticAt ℂ (f q) t)
    (p : MvPolynomial σ ℤ) : AnalyticAt ℂ (fun u => aeval (fun q => f q u) p) t := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using analyticAt_const
  | add p q hp hq => simpa using hp.fun_add hq
  | mul_X p i hp => simpa using hp.fun_mul (h i)

theorem biholo_of : Descend → Biholo := by
  intro hD E _ _ _ H D l Xo c Y S RM Sys Fx Or hJ hdeg hamp
  classical
  obtain ⟨m, n, s, hs, hamp⟩ := hamp
  have hd : IsDegreeOff Sys.A Or.Re.R.A Or.Re.π 1 Or.Re.br := by
    have := Or.Re.degree
    rwa [Or.Re_deg, hdeg] at this
  have hsurj := surj_of_degree Or.Re.holo.1 hd
  set R := Or.Re.R with hR
  set π := Or.Re.π with hπ
  let k₀ := Or.k₀
  have hmem : ∀ w, ∀ w' ∈ R.U w, R.lift w w' ∈ mcPts (mCoordIdeal RM.y) := R.mem
  choose z hz using fun w => SheetDecomposition.exists_pt Or.𝔐 (hmem w w (R.mem_U w))
  have hz' : ∀ w, ∀ w' ∈ R.U w, CoordsAt Or.𝔐.ξ RM.y (z w') (R.lift w w') := fun w w' h => by
    obtain ⟨a, ha, e⟩ := R.compat w w' w' ⟨h, R.mem_U w'⟩
    exact SheetDecomposition.coords_of_sat Or.𝔐 (hz w') ⟨_, rfl, a, ha, e⟩
  have hpoly : ∀ i (cc : (k : RM.K) → RM.ι k), (∀ k, RM.y ⟨k, cc k⟩ ≠ 0) → ∃ p : MRing RM.ι,
      aeval (fun q : Σ k, RM.ι k => RM.y q / RM.y ⟨q.1, cc q.1⟩) p = s i * ∏ k, RM.y ⟨k, cc k⟩ ^ (-((m : ℤ) * RM.A.a k - 1)) ∧
      aeval (fun q : Σ k, RM.ι k => RM.y q / RM.y ⟨q.1, cc q.1⟩) p = fn RM.y (s i) m k₀ (cc k₀) cc := fun i cc hc => by
    have h1 := hs i cc hc
    simp only [Nat.cast_one, one_mul] at h1
    obtain ⟨p, hp⟩ := exists_poly Or.𝔐.tie Or.𝔐.normal cc hc h1
    exact ⟨p, hp, hp.trans (fn_eq Or.A_deg cc hc)⟩
  have hchart : ∀ w, ∃ cc : (k : RM.K) → RM.ι k, (∀ k, R.lift w w ⟨k, cc k⟩ ≠ 0) ∧ ∀ k, RM.y ⟨k, cc k⟩ ≠ 0 := fun w => by
    choose cc hc using (hmem w w (R.mem_U w)).1
    exact ⟨cc, hc, fun k => ((hz w).2 k (cc k) (IsUnit.mk0 _ (hc k))).1⟩
  let f : Fin n → RM.ι k₀ → ((k : RM.K) → RM.ι k) → R.X → ℂ := fun i i₀ cc w =>
    if h : ∃ r, ValAt Or.𝔐.ξ (z w) (fn RM.y (s i) m k₀ i₀ cc) r then h.choose else 0
  have hf : ∀ i i₀ cc w r, ValAt Or.𝔐.ξ (z w) (fn RM.y (s i) m k₀ i₀ cc) r → f i i₀ cc w = r := fun i i₀ cc w r h => by
    have h' : ∃ r, ValAt Or.𝔐.ξ (z w) (fn RM.y (s i) m k₀ i₀ cc) r := ⟨r, h⟩
    simp only [f, dif_pos h']
    exact CxVal.unique h'.choose_spec h
  let U : RM.ι k₀ → Set Sys.X := fun i₀ => {x | Fx.pt x (Or.ix.symm i₀) ≠ 0}
  have hU : ∀ i₀ w, π w ∈ U i₀ ↔ R.lift w w ⟨k₀, i₀⟩ ≠ 0 := fun i₀ w => by
    obtain ⟨a, ha⟩ := Or.π_pt w
    have h1 : R.lift w w ⟨k₀, i₀⟩ = a * Fx.pt (π w) (Or.ix.symm i₀) := by
      have := congrFun ha (Or.ix.symm i₀)
      simpa using this
    have h2 : a ≠ 0 := by
      rintro rfl
      obtain ⟨i, hi⟩ := (hmem w w (R.mem_U w)).1 k₀
      have := congrFun ha (Or.ix.symm i)
      exact hi (by simpa using this)
    rw [h1]
    simp [U, h2]
  have hUo : ∀ i₀, IsOpen (U i₀) := fun i₀ => by
    have e : (U i₀)ᶜ = π '' {w | R.lift w w ⟨k₀, i₀⟩ ≠ 0}ᶜ := by
      ext x
      obtain ⟨w, rfl⟩ := hsurj x
      exact ⟨fun h => ⟨w, fun h' => h ((hU _ _).2 h'), rfl⟩, fun ⟨w', h, e⟩ h' => h ((hU _ _).1 (e ▸ h'))⟩
    rw [← isClosed_compl_iff, e]
    exact Or.Re.holo.1.isClosedMap _ (isOpen_lift_ne R _).isClosed_compl
  have hhol : ∀ i i₀ cc, R.A.HoloOn (π ⁻¹' U i₀) (f i i₀ cc) := fun i i₀ cc j t ht => by
    obtain ⟨c', hc', hy'⟩ := hchart ((R.A.chart j).symm t)
    obtain ⟨p, -, hp⟩ := hpoly i c' hy'
    have h0 := (hU _ _).1 ht.2
    set w₁ := (R.A.chart j).symm t with hw₁
    have ha : ∀ q, AnalyticAt ℂ (fun u => R.lift w₁ ((R.A.chart j).symm u) q) t := fun q =>
      R.holo w₁ q j t ⟨ht.1, R.mem_U w₁⟩
    have hA : AnalyticAt ℂ (fun u => aeval (fun q : Σ k, RM.ι k => R.lift w₁ ((R.A.chart j).symm u) q /
        R.lift w₁ ((R.A.chart j).symm u) ⟨q.1, c' q.1⟩) p *
        (∏ k, R.lift w₁ ((R.A.chart j).symm u) ⟨k, cc k⟩ / R.lift w₁ ((R.A.chart j).symm u) ⟨k, c' k⟩) *
        (R.lift w₁ ((R.A.chart j).symm u) ⟨k₀, c' k₀⟩ / R.lift w₁ ((R.A.chart j).symm u) ⟨k₀, i₀⟩) ^ m) t :=
      ((Bh.analyticAt_aeval (fun q => (ha q).fun_div (ha _) (hc' _)) p).fun_mul
        (Finset.analyticAt_fun_prod _ fun k _ => (ha _).fun_div (ha _) (hc' _))).fun_mul
        (((ha _).fun_div (ha _) h0).fun_pow m)
    refine hA.congr ?_
    have e1 : ∀ᶠ u in 𝓝 t, (R.A.chart j).symm u ∈ R.U w₁ :=
      ((R.A.chart j).continuousAt_symm ht.1).eventually_mem ((R.isOpen_U w₁).mem_nhds (R.mem_U w₁))
    have e2 : ∀ᶠ u in 𝓝 t, ∀ k, R.lift w₁ ((R.A.chart j).symm u) ⟨k, c' k⟩ ≠ 0 :=
      Filter.eventually_all.2 fun k => (ha _).continuousAt.eventually_ne (hc' k)
    filter_upwards [e1, e2, (ha _).continuousAt.eventually_ne h0] with u h1 h2 h3
    exact (hf _ _ _ _ _ (val_fn (Or.𝔐.all _) (hz' w₁ _ h1) i₀ cc c' h2 h3 hp)).symm
  choose F hF hFf using fun i i₀ cc =>
    hD _ Sys.X R.X Sys.A R.A π Or.Re.br (U i₀) (f i i₀ cc) Or.Re.holo hd (hUo i₀) (hhol i i₀ cc)
  refine exists_inverse R hJ Sys.A π hsurj fun w₁ => ?_
  obtain ⟨c', hc', hy'⟩ := hchart w₁
  obtain ⟨i, v, hv, hval⟩ := hamp ℂ (R.lift w₁ w₁) ⟨(hmem w₁ w₁ (R.mem_U w₁)).1, fun g hg => by
    have := (hmem w₁ w₁ (R.mem_U w₁)).2 g hg
    rwa [MvPolynomial.eval_map] at this⟩
  obtain ⟨p, hp1, hp2⟩ := hpoly i c' hy'
  have hu := ne_zero_of_hasVal (Or.𝔐.all _) (hz w₁) c' hc' hp1 hv hval
  have hin : π w₁ ∈ U (c' k₀) := (hU _ _).2 (hc' k₀)
  refine ⟨{x ∈ U (c' k₀) | F i (c' k₀) c' x ≠ 0}, fun x q => F i (c' k₀) (Function.update c' q.1 q.2) x, ?_, ⟨hin, ?_⟩,
    fun q j => (hF _ _ _ j).mono fun t ht => ⟨ht.1, ht.2.1⟩, fun w hw => ?_⟩
  · refine isOpen_iff_mem_nhds.2 fun x hx => ?_
    filter_upwards [(hUo _).mem_nhds hx.1, (contAt_of_holoOn (hF i _ c') hx.1).eventually_ne hx.2] with x' h1 h2
    exact ⟨h1, h2⟩
  · rw [hFf _ _ _ _ hin, hf _ _ _ _ _ (val_fn (Or.𝔐.all _) (hz w₁) (c' k₀) c' c' hc' (hc' k₀) hp2)]
    exact mul_ne_zero (mul_ne_zero hu (Finset.prod_ne_zero_iff.2 fun k _ => div_ne_zero (hc' k) (hc' k)))
      (pow_ne_zero _ (div_ne_zero (hc' _) (hc' _)))
  · obtain ⟨c₂, hc₂, hy₂⟩ := hchart w
    obtain ⟨p₂, -, hp₂⟩ := hpoly i c₂ hy₂
    have h0 := (hU _ _).1 hw.1
    obtain ⟨κ, hκ⟩ : ∃ κ : ℂ, ∀ cc, F i (c' k₀) cc (π w) = κ * ∏ k, R.lift w w ⟨k, cc k⟩ := by
      refine ⟨aeval (fun q : Σ k, RM.ι k => R.lift w w q / R.lift w w ⟨q.1, c₂ q.1⟩) p₂ *
        (R.lift w w ⟨k₀, c₂ k₀⟩ / R.lift w w ⟨k₀, c' k₀⟩) ^ m / ∏ k, R.lift w w ⟨k, c₂ k⟩, fun cc => ?_⟩
      rw [hFf _ _ _ _ hw.1, hf _ _ _ _ _ (val_fn (Or.𝔐.all _) (hz w) (c' k₀) cc c₂ hc₂ h0 hp₂), Finset.prod_div_distrib]
      ring
    have h1 := hw.2
    rw [hκ] at h1
    have h2 := left_ne_zero_of_mul h1
    have h3 := Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul h1)
    refine SO_symm ⟨fun k => κ * ∏ k' ∈ Finset.univ.erase k, R.lift w w ⟨k', c' k'⟩,
      fun k => mul_ne_zero h2 (Finset.prod_ne_zero_iff.2 fun k' _ => h3 k' (Finset.mem_univ _)), funext fun q => ?_⟩
    obtain ⟨k, j⟩ := q
    show F i (c' k₀) (Function.update c' k j) (π w) = _
    rw [hκ, ← Finset.prod_erase_mul _ _ (Finset.mem_univ k), Function.update_self, mul_assoc]
    congr 2
    exact Finset.prod_congr rfl fun k' hk' => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk')]

end RootFieldNumerics
end
end
end
