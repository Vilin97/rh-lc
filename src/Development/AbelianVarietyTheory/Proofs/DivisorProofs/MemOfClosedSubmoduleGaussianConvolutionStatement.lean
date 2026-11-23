module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianIsSchwartzFunction
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumGaussianConvolutionSeriesTermIntegralStatement
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableSeminormGaussianConvolutionSeriesTermStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianMulMultilinearDiagonalMemSchwartzSubmodu

section

@[expose] public section

open MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.ConvSeries

theorem exists_mem_prod_mul_gauss {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (M : Submodule ℂ (SchwartzMap E ℂ))
    (hM : ∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ M → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ M)
    (G : SchwartzMap E ℂ) (hG : G ∈ M) :
    ∀ (m : ℕ) (ℓ : Fin m → E →L[ℝ] ℝ), ∃ t ∈ M, ∀ y, t y = (∏ i, ((ℓ i y : ℝ) : ℂ)) * G y := by
  intro m
  induction m with
  | zero => intro ℓ; exact ⟨G, hG, fun y => by simp⟩
  | succ m ih =>
    intro ℓ
    obtain ⟨t, ht, hty⟩ := ih (fun i => ℓ i.succ)
    have hg : (fun x : E => ((ℓ 0 x : ℝ) : ℂ)).HasTemperateGrowth :=
      (Complex.ofRealCLM.comp (ℓ 0)).hasTemperateGrowth
    refine ⟨SchwartzMap.smulLeftCLM ℂ (fun x : E => ((ℓ 0 x : ℝ) : ℂ)) t,
      hM (ℓ 0) t _ ht (fun x => by rw [SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul]), fun y => ?_⟩
    rw [SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul, hty, Fin.prod_univ_succ, mul_assoc]

theorem gauss_mul_diag_mem : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (M : Submodule ℂ (SchwartzMap E ℂ)),
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ M → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ M) →
    ∀ (c : ℝ), 0 < c →
    (∀ g : SchwartzMap E ℂ, (∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) → g ∈ M) →
    ∀ (k : ℕ) (B : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℂ),
      ∃ t ∈ M, ∀ y, t y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)) * B (fun _ => y) := by
  intro E _ _ _ M hM c hc hGM k B
  have hin : ∀ x : E, innerSL ℝ x x = ‖x‖ ^ 2 := fun x => by
    first
    | rw [innerSL_apply_apply, real_inner_self_eq_norm_sq]
    | simp [real_inner_self_eq_norm_sq]
    | exact real_inner_self_eq_norm_sq x
  obtain ⟨G, hG⟩ := GlobalTheory.GaussSchwartz.exists_schwartz_exp_diag (-c • innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ)
    (fun x hx => by
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]; rw [hin]
      have : 0 < ‖x‖ ^ 2 := by positivity
      nlinarith)
  have hG' : ∀ y, G y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)) := fun y => by
    rw [hG, Complex.ofReal_exp]
    congr 1
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]; rw [hin]
    push_cast; ring
  have hGmem := hGM G hG'
  let b := stdOrthonormalBasis ℝ E
  have key : ∀ r : Fin k → Fin (Module.finrank ℝ E), ∃ t ∈ M,
      ∀ y, t y = (∏ j, ((innerSL ℝ (b (r j)) y : ℝ) : ℂ)) * G y :=
    fun r => exists_mem_prod_mul_gauss M hM G hGmem k (fun j => innerSL ℝ (b (r j)))
  choose t ht hty using key
  refine ⟨∑ r, B (fun j => b (r j)) • t r, M.sum_mem fun r _ => M.smul_mem _ (ht r), fun y => ?_⟩
  have hy : (fun _ : Fin k => y) = fun _ : Fin k => ∑ i, (inner ℝ (b i) y) • b i := by
    funext _; exact (b.sum_repr' y).symm

  rw [hy, ContinuousMultilinearMap.map_sum, Finset.mul_sum, SchwartzMap.sum_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [B.map_smul_univ (fun j => inner ℝ (b (r j)) y) (fun j => b (r j)), SchwartzMap.smul_apply, hty, hG',
    Complex.real_smul, smul_eq_mul]
  have hi : ∀ v : E, innerSL ℝ v y = inner ℝ v y := fun v => rfl
  simp only [hi]
  push_cast
  ring

end GlobalTheory.ConvSeries
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianMulMultilinearDiagonalMemSchwartzSubmoduStatement

section

@[expose] public section

open MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.gaussian_mul_multilinear_diagonal_mem_schwartzSubmodule : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (M : Submodule ℂ (SchwartzMap E ℂ)),
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ M → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ M) →
    ∀ (c : ℝ), 0 < c →
    (∀ g : SchwartzMap E ℂ, (∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) → g ∈ M) →
    ∀ (k : ℕ) (B : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℂ),
      ∃ t ∈ M, ∀ y, t y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)) * B (fun _ => y) := by
  first | exact @GlobalTheory.ConvSeries.gauss_mul_diag_mem | exact GlobalTheory.ConvSeries.gauss_mul_diag_mem | (intros; apply GlobalTheory.ConvSeries.gauss_mul_diag_mem <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableSchwartzOfSummableSeminorms

section

@[expose] public section

open MeasureTheory Filter Topology

namespace GlobalTheory.ConvSeries

theorem seminorm_finset_sum_le {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : Seminorm ℂ (SchwartzMap E ℂ)) (u : Finset ℕ) (t : ℕ → SchwartzMap E ℂ) :
    p (∑ j ∈ u, t j) ≤ ∑ j ∈ u, p (t j) := by
  classical
  induction u using Finset.induction_on with
  | empty => simp
  | insert a u ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (map_add_le_add p _ _).trans (by gcongr)

theorem summable_of_summable_seminorm (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (t : ℕ → SchwartzMap E ℂ)
    (h : ∀ k n, Summable (fun j => SchwartzMap.seminorm ℂ k n (t j))) : Summable t := by
  classical
  have iteratedFDeriv_sub' (f g : (SchwartzMap E ℂ)) (n : ℕ) (x : E) :
      iteratedFDeriv ℝ n (⇑(f - g)) x = iteratedFDeriv ℝ n f x - iteratedFDeriv ℝ n g x := by
    have hf : ContDiff ℝ n f := f.smooth n
    have hg : ContDiff ℝ n g := g.smooth n
    rw [show (⇑(f - g) : E → ℂ) = ⇑f - ⇑g from rfl]
    exact iteratedFDeriv_sub_apply hf.contDiffAt hg.contDiffAt
  
  have cauchy_seminorm {u : ℕ → (SchwartzMap E ℂ)} (hu : CauchySeq u) (k n : ℕ) {ε : ℝ} (hε : 0 < ε) :
      ∃ N, ∀ a ≥ N, ∀ b ≥ N, SchwartzMap.seminorm ℝ k n (u a - u b) < ε := by
    rw [cauchySeq_iff_tendsto, uniformity_eq_comap_nhds_zero, tendsto_comap_iff] at hu
    have h := ((schwartz_withSeminorms ℝ E ℂ).tendsto_nhds _ 0).1 hu (k, n) ε hε
    obtain ⟨⟨N₁, N₂⟩, hN⟩ := eventually_atTop.1 h
    refine ⟨max N₁ N₂, fun a ha b hb => ?_⟩
    have := hN (b, a) (Prod.mk_le_mk.2 ⟨le_of_max_le_left hb, le_of_max_le_right ha⟩)
    simpa [schwartzSeminormFamily] using this
  
  let limD (u : ℕ → (SchwartzMap E ℂ)) (n : ℕ) (x : E) :
      ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℂ :=
    limUnder atTop fun j => iteratedFDeriv ℝ n (u j) x
  
  have tendsto_limD {u : ℕ → (SchwartzMap E ℂ)} (hu : CauchySeq u) (n : ℕ) (x : E) :
      Tendsto (fun j => iteratedFDeriv ℝ n (u j) x) atTop (𝓝 (limD u n x)) := by
    refine tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete ?_)
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := cauchy_seminorm hu 0 n hε
    refine ⟨N, fun a ha b hb => ?_⟩
    rw [dist_eq_norm, ← iteratedFDeriv_sub']
    have := SchwartzMap.le_seminorm ℝ 0 n (u a - u b) x
    simp only [pow_zero, one_mul] at this
    exact this.trans_lt (hN a ha b hb)
  
  have key {u : ℕ → (SchwartzMap E ℂ)} (hu : CauchySeq u) (k n : ℕ) {ε : ℝ} (hε : 0 < ε) :
      ∃ N, ∀ j ≥ N, ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (u j) x - limD u n x‖ ≤ ε := by
    obtain ⟨N, hN⟩ := cauchy_seminorm hu k n hε
    refine ⟨N, fun j hj x => ?_⟩
    have ht : Tendsto (fun b => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (u j) x - iteratedFDeriv ℝ n (u b) x‖)
        atTop (𝓝 (‖x‖ ^ k * ‖iteratedFDeriv ℝ n (u j) x - limD u n x‖)) :=
      ((tendsto_const_nhds.sub (tendsto_limD hu n x)).norm).const_mul _
    refine le_of_tendsto ht (eventually_atTop.2 ⟨N, fun b hb => ?_⟩)
    rw [← iteratedFDeriv_sub']
    exact (SchwartzMap.le_seminorm ℝ k n (u j - u b) x).trans (hN j hj b hb).le
  
  have tendstoUniformly_limD {u : ℕ → (SchwartzMap E ℂ)} (hu : CauchySeq u) (n : ℕ) :
      TendstoUniformly (fun j => iteratedFDeriv ℝ n (u j)) (limD u n) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := key hu 0 n (half_pos hε)
    refine eventually_atTop.2 ⟨N, fun j hj x => ?_⟩
    have := hN j hj x
    rw [pow_zero, one_mul] at this
    rw [dist_eq_norm, norm_sub_rev]
    linarith
  
  have continuous_limD {u : ℕ → (SchwartzMap E ℂ)} (hu : CauchySeq u) (n : ℕ) :
      Continuous (limD u n) :=
    (tendstoUniformly_limD hu n).continuous (Eventually.of_forall (f := atTop) fun j =>
      ((u j).smooth ⊤).continuous_iteratedFDeriv (m := n) (by exact_mod_cast le_top)).frequently
  
  have hasFDerivAt_limD {u : ℕ → (SchwartzMap E ℂ)} (hu : CauchySeq u) (m : ℕ) (x : E) :
      HasFDerivAt (limD u m) ((limD u (m + 1) x).curryLeft) x := by
    refine hasFDerivAt_of_tendstoUniformly (f := fun j => iteratedFDeriv ℝ m (u j))
      (f' := fun j y => fderiv ℝ (iteratedFDeriv ℝ m (⇑(u j))) y)
      (g' := fun y => (limD u (m + 1) y).curryLeft) ?_ ?_ (fun y => tendsto_limD hu m y) x
    · exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) ℂ).isometry.uniformContinuous.comp_tendstoUniformly
        (tendstoUniformly_limD hu (m + 1))
    · intro j y
      exact ((((u j).smooth ⊤).differentiable_iteratedFDeriv
        (by exact_mod_cast WithTop.coe_lt_top (m : ℕ))) y).hasFDerivAt
  
  have hasFTaylorSeries {u : ℕ → (SchwartzMap E ℂ)} (hu : CauchySeq u) :
      HasFTaylorSeriesUpTo ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => (limD u 0 x).curry0)
        (fun x => (fun m => limD u m x : FormalMultilinearSeries ℝ E ℂ)) := by
    exact { zero_eq := fun _ => rfl
            fderiv := fun m _ x => hasFDerivAt_limD hu m x
            cont := fun m _ => continuous_limD hu m }
  
  let limMap (u : ℕ → (SchwartzMap E ℂ)) (hu : CauchySeq u) : (SchwartzMap E ℂ) := by
    refine { toFun := fun x => (limD u 0 x).curry0
             smooth' := (hasFTaylorSeries hu).contDiff
             decay' := ?_ }
    intro k n
    obtain ⟨N, hN⟩ := key hu k n one_pos
    refine ⟨SchwartzMap.seminorm ℝ k n (u N) + 1, fun x => ?_⟩
    rw [← (hasFTaylorSeries hu).eq_iteratedFDeriv (m := n) (by exact_mod_cast le_top) x]
    have h1 := hN N le_rfl x
    have h2 := SchwartzMap.le_seminorm ℝ k n (u N) x
    have h3 : ‖limD u n x‖ ≤ ‖iteratedFDeriv ℝ n (u N) x‖ + ‖iteratedFDeriv ℝ n (u N) x - limD u n x‖ := by
      have := norm_sub_le (iteratedFDeriv ℝ n (u N) x) (iteratedFDeriv ℝ n (u N) x - limD u n x)
      simpa using this
    have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ ‖x‖ ^ k)
    change ‖x‖ ^ k * ‖limD u n x‖ ≤ _
    rw [mul_add] at h4
    linarith

  have iteratedFDeriv_limMap {u : ℕ → (SchwartzMap E ℂ)} (hu : CauchySeq u) (n : ℕ) (x : E) :
      iteratedFDeriv ℝ n (limMap u hu) x = limD u n x :=
    ((hasFTaylorSeries hu).eq_iteratedFDeriv (m := n) (by exact_mod_cast le_top) x).symm
  
  have tendsto_limMap {u : ℕ → (SchwartzMap E ℂ)} (hu : CauchySeq u) :
      Tendsto u atTop (𝓝 (limMap u hu)) := by
    rw [(schwartz_withSeminorms ℝ E ℂ).tendsto_nhds]
    rintro ⟨k, n⟩ ε hε
    obtain ⟨N, hN⟩ := key hu k n (half_pos hε)
    refine eventually_atTop.2 ⟨N, fun j hj => ?_⟩
    refine lt_of_le_of_lt ?_ (half_lt_self hε)
    refine SchwartzMap.seminorm_le_bound ℝ k n _ (half_pos hε).le fun x => ?_
    rw [iteratedFDeriv_sub', iteratedFDeriv_limMap hu]
    exact hN j hj x
  
  haveI : CompleteSpace (SchwartzMap E ℂ) := by
    haveI : (uniformity (SchwartzMap E ℂ)).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
    exact UniformSpace.complete_of_cauchySeq_tendsto fun u hu => ⟨limMap u hu, tendsto_limMap hu⟩
  rw [summable_iff_vanishing]
  intro U hU
  obtain ⟨s, r, hr, hsub⟩ := (schwartz_withSeminorms ℂ E ℂ).mem_nhds_iff 0 U |>.1 hU
  have hr' : 0 < r / 2 := half_pos hr
  have hS : ∀ i : ℕ × ℕ, ∃ S : Finset ℕ, ∀ u : Finset ℕ, Disjoint u S →
      ∑ j ∈ u, SchwartzMap.seminorm ℂ i.1 i.2 (t j) ∈ Set.Iio (r / 2) :=
    fun i => summable_iff_vanishing.1 (h i.1 i.2) _ (Iio_mem_nhds (by simpa using hr'))
  choose S hS using hS
  refine ⟨s.biUnion S, fun u hu => hsub ?_⟩
  rw [Seminorm.mem_ball_zero]
  refine lt_of_le_of_lt (Seminorm.finset_sup_apply_le hr'.le fun i hi => ?_) (half_lt_self hr)
  refine (seminorm_finset_sum_le _ u t).trans ?_
  exact (hS i u (Finset.disjoint_of_subset_right (Finset.subset_biUnion_of_mem S hi) hu)).le

end GlobalTheory.ConvSeries
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableSchwartzOfSummableSeminormsStatement

section

@[expose] public section

open MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.summable_schwartz_of_summable_seminorms : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (t : ℕ → SchwartzMap E ℂ),
    (∀ k n, Summable (fun j => SchwartzMap.seminorm ℂ k n (t j))) → Summable t := by
  first | exact @GlobalTheory.ConvSeries.summable_of_summable_seminorm | exact GlobalTheory.ConvSeries.summable_of_summable_seminorm | (intros; apply GlobalTheory.ConvSeries.summable_of_summable_seminorm <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfClosedSubmoduleGaussianConvolution

section

@[expose] public section

open FourierTransform MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.ConvSeries

theorem mem_of_conv_gaussian : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (M : Submodule ℂ (SchwartzMap E ℂ)), IsClosed (M : Set (SchwartzMap E ℂ)) →
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ M → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ M) →
    ∀ (b c : ℝ), 0 < b → 0 < c →
    (∀ g : SchwartzMap E ℂ, (∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) → g ∈ M) →
    ∀ (h u : SchwartzMap E ℂ),
      (∀ y, u y = ∫ a, Complex.exp (-((b * ‖a‖ ^ 2 : ℝ) : ℂ)) * h a * Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))) →
      u ∈ M := by
  intro E _ _ _ _ _ M hM hℓ b c hb hc hg h u hu
  have ht : ∀ j, ∃ t ∈ M, ∀ y, t y = term b c h j y := by
    intro j
    obtain ⟨t, htM, ht⟩ := GlobalTheory.T.gaussian_mul_multilinear_diagonal_mem_schwartzSubmodule E M hℓ c hc hg j (coef b c h j)
    refine ⟨(((2 * c) ^ j / (j.factorial : ℝ) : ℝ) : ℂ) • t, M.smul_mem _ htM, fun y => ?_⟩
    simp only [SchwartzMap.smul_apply, ht, term, smul_eq_mul]
    ring
  choose t htM hty using ht
  have hs : Summable t := GlobalTheory.T.summable_schwartz_of_summable_seminorms E t (GlobalTheory.T.summable_seminorm_gaussianConvolutionSeriesTerm E b c hb hc h t hty)
  have hL := hs.hasSum
  have hev : ∀ y, (∑' j, t j) y = u y := by
    intro y
    let φ : SchwartzMap E ℂ →L[ℂ] ℂ :=
      (BoundedContinuousFunction.evalCLM ℂ y).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ E ℂ)
    have h1 : HasSum (fun j => t j y) ((∑' j, t j) y) := hL.mapL φ
    have h2 : HasSum (fun j => t j y) (u y) := by
      rw [hu y]
      exact (GlobalTheory.T.hasSum_gaussianConvolutionSeriesTerm_integral E b c hb hc h y).congr_fun (fun j => hty j y)
    exact h1.unique h2
  have hLu : (∑' j, t j) = u := SchwartzMap.ext hev
  rw [← hLu]
  exact hM.mem_of_tendsto hL (Eventually.of_forall fun s => M.sum_mem fun j _ => htM j)

end GlobalTheory.ConvSeries
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfClosedSubmoduleGaussianConvolutionStatement

section

@[expose] public section

open FourierTransform MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.mem_of_closedSubmodule_gaussian_convolution : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (M : Submodule ℂ (SchwartzMap E ℂ)), IsClosed (M : Set (SchwartzMap E ℂ)) →
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ M → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ M) →
    ∀ (b c : ℝ), 0 < b → 0 < c →
    (∀ g : SchwartzMap E ℂ, (∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) → g ∈ M) →
    ∀ (h u : SchwartzMap E ℂ),
      (∀ y, u y = ∫ a, Complex.exp (-((b * ‖a‖ ^ 2 : ℝ) : ℂ)) * h a * Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))) →
      u ∈ M := by
  first | exact @GlobalTheory.ConvSeries.mem_of_conv_gaussian | exact GlobalTheory.ConvSeries.mem_of_conv_gaussian | (intros; apply GlobalTheory.ConvSeries.mem_of_conv_gaussian <;> assumption)
end
end
