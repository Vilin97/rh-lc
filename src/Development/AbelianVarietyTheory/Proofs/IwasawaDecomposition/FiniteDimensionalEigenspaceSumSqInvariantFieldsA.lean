module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Topology.UrysohnsLemma
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.Analysis.Calculus.Deriv.Mul

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalOfUniformlyAlmostInvariant

section

@[expose] public section

open MeasureTheory Filter Topology
open scoped ContDiff

namespace GlobalTheory

theorem norm_sq_toLp_two_eq_integral_norm_sq {K : Type} [TopologicalSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] (g : C(K, ℂ)) :
    ‖ContinuousMap.toLp 2 μ ℂ g‖ ^ 2 = ∫ x, ‖g x‖ ^ 2 ∂μ := by
  have h := ContinuousMap.inner_toLp μ g g
  rw [inner_self_eq_norm_sq_to_K] at h
  simp_rw [Complex.mul_conj'] at h
  have h2 : (∫ x, ((‖g x‖ : ℂ)) ^ 2 ∂μ) = ((∫ x, ‖g x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]; simp
  rw [h2] at h
  apply Complex.ofReal_injective
  rw [← h, Complex.ofReal_pow]
  rfl

theorem finiteDimensional_of_uniformly_almost_invariant :
    ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
      [T2Space K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure]
      [μ.IsMulRightInvariant] [IsProbabilityMeasure μ] (E : Submodule ℂ (K → ℂ)),
      (∀ f ∈ E, Continuous f) → ∀ U ∈ 𝓝 (1 : K),
      (∀ f ∈ E, ∀ u ∈ U, ∫ x, ‖f (x * u) - f x‖ ^ 2 ∂μ ≤ (1 / 4) * ∫ x, ‖f x‖ ^ 2 ∂μ) →
      FiniteDimensional ℂ E := by
  intro K _ _ _ _ _ _ _ μ _ _ _ E hE U hU hinv
  classical
  obtain ⟨β, hβ1, -, hβU, hβ01⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen
    (isCompact_singleton (x := (1 : K))) isOpen_interior
    (Set.singleton_subset_iff.2 (mem_interior_iff_mem_nhds.2 hU))
  have hβ0 : ∀ x, 0 ≤ β x := fun x => (hβ01 x).1
  have hβU' : ∀ u, β u ≠ 0 → u ∈ U := fun u hu =>
    interior_subset (hβU (subset_tsupport _ hu))
  set c : ℝ := ∫ u, β u ∂μ with hc
  have hcpos : 0 < c := β.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (x := 1) (HasCompactSupport.of_compactSpace _) hβ0 (by simp [hβ1 (Set.mem_singleton _)])
  set L := ContinuousMap.toLp (α := K) (E := ℂ) 2 μ ℂ with hL

  let b : C(K, C(K, ℂ)) := ContinuousMap.curry
    ⟨fun p : K × K => (β (p.1⁻¹ * p.2) : ℂ), by fun_prop⟩
  have hb : Continuous fun x => L (b x) := L.continuous.comp b.continuous
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover
    (fun x : K => (fun y => L (b y)) ⁻¹' Metric.ball (L (b x)) (c / 4))
    (fun x _ => hb.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ (by positivity)))
  let ι : E →ₗ[ℂ] C(K, ℂ) :=
    { toFun := fun f => ⟨f.1, hE f.1 f.2⟩
      map_add' := fun f g => by ext; simp
      map_smul' := fun a f => by ext; simp }
  let Φ : E →ₗ[ℂ] (t → ℂ) := LinearMap.pi fun j : t =>
    (innerSL ℂ (L (b j.1))).toLinearMap ∘ₗ L.toLinearMap ∘ₗ ι
  refine FiniteDimensional.of_injective Φ ((injective_iff_map_eq_zero Φ).2 fun f hf => ?_)
  have hf0 : ∀ j ∈ t, inner ℂ (L (b j)) (L (ι f)) = 0 := fun j hj => by
    simpa [Φ] using congrFun hf ⟨j, hj⟩
  set g : C(K, ℂ) := ι f with hg
  let R : C(K, C(K, ℂ)) := ContinuousMap.curry
    ⟨fun p : K × K => g (p.2 * p.1), by fun_prop⟩
  have hint : ∀ {V : Type} [NormedAddCommGroup V] {F : K → V}, Continuous F → Integrable F μ :=
    fun hF => hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi1 : Integrable (fun u => β u • R u) μ := hint (by fun_prop)
  set T : C(K, ℂ) := ∫ u, β u • R u ∂μ with hT
  have hTx : ∀ x, T x = inner ℂ (L (b x)) (L g) := fun x => by
    rw [hT, ContinuousMap.integral_apply hi1, hL, ContinuousMap.inner_toLp,
      ← integral_mul_left_eq_self (μ := μ) (fun z => g z * (starRingEnd ℂ) (b x z)) x]
    congr 1
    ext u
    simp [R, b, mul_comm]
  have hTb : ∀ x, ‖T x‖ ≤ c / 4 * ‖L g‖ := fun x => by
    obtain ⟨j, hj, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    have hx' : ‖L (b x) - L (b j)‖ ≤ c / 4 := by
      rw [← dist_eq_norm]; exact le_of_lt hx
    have : T x = inner ℂ (L (b x) - L (b j)) (L g) := by
      rw [inner_sub_left, hf0 j hj, sub_zero, hTx]
    rw [this]
    exact (norm_inner_le_norm _ _).trans (by gcongr)
  have hLT : ‖L T‖ ≤ c / 4 * ‖L g‖ := by
    have := Lp.norm_le_of_ae_bound (f := L T) (C := c / 4 * ‖L g‖) (by positivity)
      (by
        filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ T] with x hx
        rw [hL, hx]; exact hTb x)
    simpa [measureUnivNNReal] using this
  have hmove : ∀ u ∈ U, ‖L (R u) - L g‖ ≤ 1 / 2 * ‖L g‖ := fun u hu => by
    have h1 := hinv f.1 f.2 u hu
    have h2 : ‖L (R u - g)‖ ^ 2 ≤ (1 / 2 * ‖L g‖) ^ 2 := by
      rw [mul_pow, hL, norm_sq_toLp_two_eq_integral_norm_sq, norm_sq_toLp_two_eq_integral_norm_sq]
      norm_num
      simpa [R, hg, ι] using h1
    rw [← map_sub]
    exact le_of_sq_le_sq h2 (by positivity)
  have hdiff : L T - c • L g = ∫ u, β u • (L (R u) - L g) ∂μ := by
    rw [hT, ← L.integral_comp_comm hi1, hc, ← integral_smul_const, ← integral_sub]
    · congr 1
      ext1 u
      rw [smul_sub, L.map_smul_of_tower]
    · exact L.integrable_comp hi1
    · exact hint (by fun_prop)
  have hdn : ‖L T - c • L g‖ ≤ c * (1 / 2 * ‖L g‖) := by
    rw [hdiff, hc, ← integral_mul_const]
    refine norm_integral_le_of_norm_le (hint (by fun_prop)) (Eventually.of_forall fun u => ?_)
    rw [norm_smul, Real.norm_of_nonneg (hβ0 u)]
    by_cases hu : β u = 0
    · simp [hu]
    · exact mul_le_mul_of_nonneg_left (hmove u (hβU' u hu)) (hβ0 u)
  have hfin : c * ‖L g‖ ≤ c / 4 * ‖L g‖ + c * (1 / 2 * ‖L g‖) := by
    have : ‖c • L g‖ ≤ ‖L T‖ + ‖L T - c • L g‖ := by
      simpa using norm_sub_le (L T) (L T - c • L g)
    rw [norm_smul, Real.norm_of_nonneg hcpos.le] at this
    linarith
  have hg0 : ‖L g‖ = 0 := by
    have := norm_nonneg (L g)
    nlinarith
  have hg1 : g = 0 := ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) μ
    (by rw [map_zero]; exact norm_eq_zero.1 hg0)
  ext x
  simpa [hg, ι] using congrArg (fun h : C(K, ℂ) => h x) hg1

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalOfUniformlyAlmostInvariantStatement

section

@[expose] public section

open MeasureTheory Filter Topology
open scoped ContDiff

theorem _root_.GlobalTheory.T.finiteDimensional_of_uniformly_almost_invariant_alt : ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] [IsProbabilityMeasure μ] (E : Submodule ℂ (K → ℂ)), (∀ f ∈ E, Continuous f) → ∀ U ∈ 𝓝 (1 : K), (∀ f ∈ E, ∀ u ∈ U, ∫ x, ‖f (x * u) - f x‖ ^ 2 ∂μ ≤ (1 / 4) * ∫ x, ‖f x‖ ^ 2 ∂μ) → FiniteDimensional ℂ E := by
  first | exact @GlobalTheory.finiteDimensional_of_uniformly_almost_invariant | exact GlobalTheory.finiteDimensional_of_uniformly_almost_invariant | (intros; apply GlobalTheory.finiteDimensional_of_uniformly_almost_invariant <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RightTranslationCurveSqLeAndIntegralDerivEqZeroA

section

@[expose] public section

open MeasureTheory Filter Topology
open scoped ContDiff

namespace GlobalTheory

theorem integral_intervalIntegral_mul_right_curve {K : Type} [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [μ.IsMulRightInvariant] [IsProbabilityMeasure μ]
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology E]
    (c : ℝ → K) (hc : Continuous c) (g : K → E) (hg : Continuous g) :
    ∫ x, (∫ t in (0:ℝ)..1, g (x * c t)) ∂μ = ∫ x, g x ∂μ := by
  obtain ⟨C, hC⟩ := (isCompact_univ.image hg).isBounded.exists_norm_le
  have hcont : Continuous (Function.uncurry fun (x : K) (t : ℝ) => g (x * c t)) := by
    unfold Function.uncurry
    fun_prop
  have hint : Integrable (Function.uncurry fun (x : K) (t : ℝ) => g (x * c t))
      (μ.prod (volume.restrict (Set.Ioc (0:ℝ) 1))) := by
    refine Integrable.of_bound hcont.aestronglyMeasurable C (Eventually.of_forall fun p => ?_)
    exact hC _ ⟨_, Set.mem_univ _, rfl⟩
  simp_rw [intervalIntegral.integral_of_le (zero_le_one' ℝ)]
  rw [integral_integral_swap hint]
  simp_rw [integral_mul_right_eq_self g]
  simp

theorem norm_intervalIntegral_unit_sq_le (h : ℝ → ℂ) (hh : Continuous h) :
    ‖∫ t in (0:ℝ)..1, h t‖ ^ 2 ≤ ∫ t in (0:ℝ)..1, ‖h t‖ ^ 2 := by
  set a : ℝ := ∫ t in (0:ℝ)..1, ‖h t‖ with ha
  have h1 : ‖∫ t in (0:ℝ)..1, h t‖ ≤ a :=
    intervalIntegral.norm_integral_le_integral_norm zero_le_one
  have h2 : 0 ≤ ∫ t in (0:ℝ)..1, (‖h t‖ - a) ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one fun t _ => sq_nonneg _
  have hn : Continuous fun t => ‖h t‖ := hh.norm
  have h3 : ∫ t in (0:ℝ)..1, (‖h t‖ - a) ^ 2
      = (∫ t in (0:ℝ)..1, ‖h t‖ ^ 2) - a ^ 2 := by
    have e : ∀ t, (‖h t‖ - a) ^ 2 = (‖h t‖ ^ 2 - 2 * a * ‖h t‖) + a ^ 2 := fun t => by ring
    simp_rw [e]
    rw [intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul, ← ha]
    · simp; ring
    all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _
  have h4 : ‖∫ t in (0:ℝ)..1, h t‖ ^ 2 ≤ a ^ 2 := by
    gcongr
  linarith

theorem right_translation_curve_sq_le_and_integral_deriv_eq_zero :
    ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
      [T2Space K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure]
      [μ.IsMulRightInvariant] [IsProbabilityMeasure μ] (c : ℝ → K), Continuous c → c 0 = 1 →
      ∀ f f' : K → ℂ, Continuous f → Continuous f' →
      (∀ x t, HasDerivAt (fun t : ℝ => f (x * c t)) (f' (x * c t)) t) →
      (∫ x, ‖f (x * c 1) - f x‖ ^ 2 ∂μ ≤ ∫ x, ‖f' x‖ ^ 2 ∂μ) ∧ ∫ x, f' x ∂μ = 0 := by
  intro K _ _ _ _ _ _ _ μ _ _ _ c hc h0 f f' hf hf' hd
  have key : ∀ x, f (x * c 1) - f x = ∫ t in (0:ℝ)..1, f' (x * c t) := by
    intro x
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd x t)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    simp [h0]
  have hI : ∀ {E : Type} [NormedAddCommGroup E] [SecondCountableTopology E] (g : K → E),
      Continuous g → Integrable g μ :=
    fun g hg => hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)
  constructor
  · rw [← integral_intervalIntegral_mul_right_curve μ c hc (fun x => ‖f' x‖ ^ 2) (by fun_prop)]
    refine integral_mono (hI _ (by fun_prop)) (hI _ ?_) fun x => ?_
    · exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (f := fun (x : K) (t : ℝ) => ‖f' (x * c t)‖ ^ 2)
        (by unfold Function.uncurry; fun_prop) 0 1
    · simp only [key]
      exact norm_intervalIntegral_unit_sq_le _ (by fun_prop)
  · rw [← integral_intervalIntegral_mul_right_curve μ c hc f' hf']
    simp_rw [← key]
    rw [integral_sub (hI _ (by fun_prop)) (hI _ hf), integral_mul_right_eq_self f, sub_self]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RightTranslationCurveSqLeAndIntegralDerivEqZeroAStatement

section

@[expose] public section

open MeasureTheory Filter Topology
open scoped ContDiff

theorem _root_.GlobalTheory.T.right_translation_curve_sq_le_and_integral_deriv_eq_zero_alt : ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] [IsProbabilityMeasure μ] (c : ℝ → K), Continuous c → c 0 = 1 → ∀ f f' : K → ℂ, Continuous f → Continuous f' → (∀ x t, HasDerivAt (fun t : ℝ => f (x * c t)) (f' (x * c t)) t) → (∫ x, ‖f (x * c 1) - f x‖ ^ 2 ∂μ ≤ ∫ x, ‖f' x‖ ^ 2 ∂μ) ∧ ∫ x, f' x ∂μ = 0 := by
  first | exact @GlobalTheory.right_translation_curve_sq_le_and_integral_deriv_eq_zero | exact GlobalTheory.right_translation_curve_sq_le_and_integral_deriv_eq_zero | (intros; apply GlobalTheory.right_translation_curve_sq_le_and_integral_deriv_eq_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalEigenspaceSumSqInvariantFieldsA

section

@[expose] public section

open MeasureTheory Filter Topology
open scoped ContDiff

namespace GlobalTheory

theorem finiteDimensional_eigenspace_sum_sq_invariantFields : ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K] (L : Type) [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L] (S : Submodule ℂ (K → ℂ)), (∀ f ∈ S, Continuous f) → ∀ e : L → K, (∀ X : L, Continuous fun t : ℝ => e (t • X)) → e 0 = 1 → (∀ r : ℝ, 0 < r → e '' Metric.ball 0 r ∈ 𝓝 (1 : K)) → ∀ d : L → Module.End ℂ S, (∀ X Y, d (X + Y) = d X + d Y) → (∀ (a : ℝ) X, d (a • X) = (a : ℂ) • d X) → (∀ (X : L) (f : S) (x : K) (t : ℝ), HasDerivAt (fun t : ℝ => f.1 (x * e (t • X))) ((d X f).1 (x * e (t • X))) t) → ∀ (ι : Type) [Fintype ι] (X : ι → L), Submodule.span ℝ (Set.range X) = ⊤ → ∀ lam : ℂ, FiniteDimensional ℂ (Module.End.eigenspace (∑ i, d (X i) * d (X i)) lam) := by
  intro K _ _ _ _ _ L _ _ _ S hS e he he0 hU d hadd hsmul hder ι _ X hX lam
  classical
  letI : MeasurableSpace K := borel K
  haveI : BorelSpace K := ⟨rfl⟩
  set μ : Measure K := haarProb K with hμ
  have hc : ∀ f : S, Continuous f.1 := fun f => hS f.1 f.2
  have hint : ∀ {F : Type} [NormedAddCommGroup F] {g : K → F}, Continuous g → Integrable g μ :=
    fun hg => hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi2 : ∀ f g : S, Integrable (fun x => (starRingEnd ℂ) (f.1 x) * g.1 x) μ :=
    fun f g => hint ((Complex.continuous_conj.comp (hc f)).mul (hc g))

  have hskew : ∀ (Y : L) (f : S), ((∫ x, ‖(d Y f).1 x‖ ^ 2 ∂μ : ℝ) : ℂ) +
      ∫ x, (starRingEnd ℂ) (f.1 x) * (d Y (d Y f)).1 x ∂μ = 0 := by
    intro Y f
    have c1 : Continuous fun x => (starRingEnd ℂ) (f.1 x) :=
      Complex.continuous_conj.comp (hc f)
    have c2 : Continuous fun x => (starRingEnd ℂ) ((d Y f).1 x) :=
      Complex.continuous_conj.comp (hc _)
    have h := (GlobalTheory.T.right_translation_curve_sq_le_and_integral_deriv_eq_zero_alt K μ (fun t => e (t • Y)) (he Y) (by simp [he0])
      (fun x => (starRingEnd ℂ) (f.1 x) * (d Y f).1 x)
      (fun x => (starRingEnd ℂ) ((d Y f).1 x) * (d Y f).1 x
        + (starRingEnd ℂ) (f.1 x) * (d Y (d Y f)).1 x)
      (c1.mul (hc _)) ((c2.mul (hc _)).add (c1.mul (hc _)))
      (fun x t => (hder Y f x t).star.mul (hder Y (d Y f) x t))).2
    rw [integral_add (hi2 _ _) (hi2 _ _)] at h
    rw [← h, ← integral_complex_ofReal]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp [Complex.conj_mul']
  have hsum : ∀ f : S, f ∈ Module.End.eigenspace (∑ i, d (X i) * d (X i)) lam →
      ∑ i, ∫ x, ‖(d (X i) f).1 x‖ ^ 2 ∂μ ≤ ‖lam‖ * ∫ x, ‖f.1 x‖ ^ 2 ∂μ := by
    intro f hf
    rw [Module.End.mem_eigenspace_iff] at hf
    have h1 : ∑ i, ∫ x, (starRingEnd ℂ) (f.1 x) * (d (X i) (d (X i) f)).1 x ∂μ
        = lam * ((∫ x, ‖f.1 x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
      rw [← integral_finsetSum _ (fun i _ => hi2 _ _), ← integral_complex_ofReal,
        ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      have h2 := congrArg (fun g : S => g.1 x) hf
      simp only [LinearMap.sum_apply, Module.End.mul_apply, Submodule.coe_sum, Finset.sum_apply,
        Submodule.coe_smul, Pi.smul_apply, smul_eq_mul] at h2
      simp only
      rw [← Finset.mul_sum, h2, mul_left_comm, Complex.conj_mul']
      simp
    have h3 : ((∑ i, ∫ x, ‖(d (X i) f).1 x‖ ^ 2 ∂μ : ℝ) : ℂ)
        = - (lam * ((∫ x, ‖f.1 x‖ ^ 2 ∂μ : ℝ) : ℂ)) := by
      rw [← h1, Complex.ofReal_sum, eq_neg_iff_add_eq_zero, ← Finset.sum_add_distrib]
      exact Finset.sum_eq_zero fun i _ => hskew _ _
    have h4 := congrArg norm h3
    rw [norm_neg, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (a := ∫ x, ‖f.1 x‖ ^ 2 ∂μ)
        (integral_nonneg fun x => by positivity)] at h4
    rw [← h4]
    exact le_abs_self _
  obtain ⟨a, ha⟩ := (Fintype.linearCombination ℝ X).exists_rightInverse_of_surjective
    (by rw [Fintype.range_linearCombination, hX])
  have hac : Continuous a := a.continuous_of_finiteDimensional
  have hd0 : d 0 = 0 := by
    have := hsmul 0 0
    simpa using this
  have hdY : ∀ Y, d Y = ∑ i, ((a Y i : ℝ) : ℂ) • d (X i) := by
    intro Y
    have h1 : Y = ∑ i, a Y i • X i := by
      have := LinearMap.congr_fun ha Y
      simpa [Fintype.linearCombination_apply] using this.symm
    let D : L →+ Module.End ℂ S := ⟨⟨d, hd0⟩, hadd⟩
    calc d Y = D (∑ i, a Y i • X i) := congrArg d h1
      _ = ∑ i, D (a Y i • X i) := map_sum D _ _
      _ = _ := Finset.sum_congr rfl fun i _ => hsmul _ _
  have hbound : ∀ (Y : L) (f : S), ∫ x, ‖(d Y f).1 x‖ ^ 2 ∂μ ≤
      (∑ i, (a Y i) ^ 2) * ∑ i, ∫ x, ‖(d (X i) f).1 x‖ ^ 2 ∂μ := by
    intro Y f
    have ci : ∀ g : S, Continuous fun x => ‖g.1 x‖ ^ 2 := fun g => (hc g).norm.pow 2
    rw [← integral_finsetSum _ (fun i _ => hint (ci _)), ← integral_const_mul]
    refine integral_mono (hint (ci _))
      (hint (continuous_const.mul (continuous_finsetSum _ fun i _ => ci _))) fun x => ?_
    have h1 : ‖(d Y f).1 x‖ ≤ ∑ i, |a Y i| * ‖(d (X i) f).1 x‖ := by
      rw [hdY Y]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Finset.sum_apply,
        Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      simp
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => |a Y i|)
      (fun i => ‖(d (X i) f).1 x‖)
    simp only [sq_abs] at h2
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
  have hcont : Continuous fun Y : L => (∑ i, (a Y i) ^ 2) * ‖lam‖ := by fun_prop
  have hev : ∀ᶠ Y in 𝓝 (0 : L), (∑ i, (a Y i) ^ 2) * ‖lam‖ < 1 / 4 :=
    hcont.continuousAt.eventually_lt continuousAt_const (by simp)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  have hfin := GlobalTheory.T.finiteDimensional_of_uniformly_almost_invariant_alt K μ
    ((Module.End.eigenspace (∑ i, d (X i) * d (X i)) lam).map S.subtype)
    (by rintro _ ⟨f, -, rfl⟩; exact hc f) _ (hU r hr) (by
      rintro _ ⟨f, hf, rfl⟩ _ ⟨Y, hY, rfl⟩
      have h := (GlobalTheory.T.right_translation_curve_sq_le_and_integral_deriv_eq_zero_alt K μ (fun t => e (t • Y)) (he Y) (by simp [he0])
        f.1 (d Y f).1 (hc _) (hc _) (hder Y f)).1
      simp only [one_smul] at h
      have hn : 0 ≤ ∫ x, ‖f.1 x‖ ^ 2 ∂μ := integral_nonneg fun x => by positivity
      have hs : 0 ≤ ∑ i, (a Y i) ^ 2 := Finset.sum_nonneg fun i _ => by positivity
      calc _ ≤ _ := h
        _ ≤ _ := hbound Y f
        _ ≤ (∑ i, (a Y i) ^ 2) * (‖lam‖ * ∫ x, ‖f.1 x‖ ^ 2 ∂μ) :=
          mul_le_mul_of_nonneg_left (hsum f hf) hs
        _ = ((∑ i, (a Y i) ^ 2) * ‖lam‖) * ∫ x, ‖f.1 x‖ ^ 2 ∂μ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (hball Y hY).le hn)
  exact (Submodule.equivMapOfInjective S.subtype S.subtype_injective _).symm.finiteDimensional

end GlobalTheory
end
end
