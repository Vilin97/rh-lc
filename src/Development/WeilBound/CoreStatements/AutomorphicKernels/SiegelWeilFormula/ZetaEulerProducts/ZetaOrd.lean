module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ZetaEulerProducts.MeromorphicAtProd
public import GroundTheory.GlobalFields.TateThesis.DedekindZetaContinuation
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
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
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ZetaEulerProducts.SummablePrimesRpow
import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ZetaEulerProducts.InvGammaRZo

section

@[expose] public section

open Filter Topology Complex
open scoped Real

namespace PositivityTheory.Lord

theorem invGamma_zo (n : ℕ) : ZO (fun z => (Complex.Gamma z)⁻¹) (-(n : ℂ)) 1 := by
  induction n with
  | zero =>
    refine ⟨fun z => (Complex.Gamma (z + 1))⁻¹, ?_, ?_, ?_⟩
    · have hd : Differentiable ℂ fun z : ℂ => (Complex.Gamma (z + 1))⁻¹ := by
        intro z
        have h := (Complex.differentiable_one_div_Gamma (z + 1)).comp z (differentiableAt_id.add_const (1 : ℂ))
        exact h.congr_of_eventuallyEq (Eventually.of_forall fun w => by simp)
      exact hd.analyticAt _
    · simp
    · filter_upwards [self_mem_nhdsWithin] with z hz
      have hz0 : z ≠ 0 := by simpa using hz
      rw [Complex.Gamma_add_one z hz0, mul_inv, ← mul_assoc]
      simp [hz0]
  | succ n ih =>
    obtain ⟨u, hu, hu0, he⟩ := ih
    have hx : (-((n + 1 : ℕ) : ℂ)) + 1 = -(n : ℂ) := by push_cast; ring
    refine ⟨fun z => z * u (z + 1), ?_, ?_, ?_⟩
    · have h1 : AnalyticAt ℂ (fun z : ℂ => z + 1) (-((n + 1 : ℕ) : ℂ)) :=
        analyticAt_id.add analyticAt_const
      exact analyticAt_id.mul (hu.comp_of_eq h1 hx)
    · simp only [hx]
      refine mul_ne_zero ?_ hu0
      rw [neg_ne_zero]
      exact_mod_cast Nat.succ_ne_zero n
    · have ht : Tendsto (fun z : ℂ => z + 1) (𝓝[≠] (-((n + 1 : ℕ) : ℂ))) (𝓝[≠] (-(n : ℂ))) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        · have hc : Continuous fun z : ℂ => z + 1 := continuous_id.add continuous_const
          have := (hc.tendsto (-((n + 1 : ℕ) : ℂ))).mono_left (nhdsWithin_le_nhds (s := {(-((n + 1 : ℕ) : ℂ))}ᶜ))
          simpa only [hx] using this
        · filter_upwards [self_mem_nhdsWithin] with z hz
          intro h
          apply hz
          have : z = -(n : ℂ) - 1 := by rw [← h]; ring
          rw [Set.mem_singleton_iff, this]; push_cast; ring
      have h0 : ∀ᶠ z in 𝓝[≠] (-((n + 1 : ℕ) : ℂ)), z ≠ 0 := by
        refine eventually_nhdsWithin_of_eventually_nhds (isOpen_compl_singleton.mem_nhds ?_)
        rw [Set.mem_compl_singleton_iff, neg_ne_zero]
        exact_mod_cast Nat.succ_ne_zero n
      filter_upwards [ht.eventually he, h0] with z h1 h2
      have hg : (Complex.Gamma z)⁻¹ = z * (Complex.Gamma (z + 1))⁻¹ := by
        rw [Complex.Gamma_add_one z h2, mul_inv, ← mul_assoc, mul_inv_cancel₀ h2, one_mul]
      rw [hg, h1]
      push_cast
      ring

theorem invGammaR_zo (j : ℤ) (hj : j ≤ 0) :
    ZO (fun s => (Gammaℝ s)⁻¹) (j : ℂ) (if Even j then 1 else 0) := by
  split_ifs with he
  · obtain ⟨m, hm⟩ := he
    obtain ⟨n, hn⟩ : ∃ n : ℕ, m = -(n : ℤ) := ⟨m.natAbs, by omega⟩
    obtain ⟨u, hu, hu0, hue⟩ := invGamma_zo n
    have hjn : (j : ℂ) = -(2 * (n : ℂ)) := by rw [hm, hn]; push_cast; ring
    have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
    refine ⟨fun s => ((π : ℂ) ^ (-s / 2))⁻¹ * u (s / 2) / 2, ?_, ?_, ?_⟩
    · have h1 : AnalyticAt ℂ (fun s : ℂ => ((π : ℂ) ^ (-s / 2))⁻¹) (j : ℂ) := by
        have hd : Differentiable ℂ fun s : ℂ => (π : ℂ) ^ (-s / 2) :=
          fun s => ((differentiableAt_id.neg).div_const 2).const_cpow (Or.inl hpi)
        exact (hd.analyticAt _).inv (by rw [Ne, cpow_eq_zero_iff]; tauto)
      have h2 : AnalyticAt ℂ (fun s : ℂ => u (s / 2)) (j : ℂ) := by
        have hc : AnalyticAt ℂ (fun s : ℂ => s / 2) (j : ℂ) := analyticAt_id.div_const
        exact hu.comp_of_eq hc (by rw [hjn]; ring)
      exact (h1.mul h2).div_const
    · simp only
      have : (j : ℂ) / 2 = -(n : ℂ) := by rw [hjn]; ring
      rw [this]
      refine div_ne_zero (mul_ne_zero (inv_ne_zero ?_) hu0) two_ne_zero
      rw [Ne, cpow_eq_zero_iff]; tauto
    · have ht : Tendsto (fun s : ℂ => s / 2) (𝓝[≠] (j : ℂ)) (𝓝[≠] (-(n : ℂ))) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        · have hc : Continuous fun s : ℂ => s / 2 := continuous_id.div_const 2
          have := (hc.tendsto (j : ℂ)).mono_left (nhdsWithin_le_nhds (s := {(j : ℂ)}ᶜ))
          have e : (j : ℂ) / 2 = -(n : ℂ) := by rw [hjn]; ring
          simpa only [e] using this
        · filter_upwards [self_mem_nhdsWithin] with s hs
          intro h
          apply hs
          have : s = 2 * (-(n : ℂ)) := by rw [← h]; ring
          rw [Set.mem_singleton_iff, this, hjn]; ring
      filter_upwards [ht.eventually hue] with s h1
      rw [Gammaℝ_def, mul_inv, h1, hjn]
      ring
  · have hd : Differentiable ℂ fun s => (Gammaℝ s)⁻¹ := differentiable_Gammaℝ_inv
    refine ⟨fun s => (Gammaℝ s)⁻¹, hd.analyticAt _, inv_ne_zero fun h => he ?_,
      Eventually.of_forall fun s => by simp⟩
    obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.1 h
    refine ⟨-(n : ℤ), ?_⟩
    have : ((j : ℤ) : ℂ) = ((-(n : ℤ) + -(n : ℤ) : ℤ) : ℂ) := by rw [hn]; push_cast; ring
    exact_mod_cast this

theorem invGammaC_zo (j : ℤ) (hj : j ≤ 0) : ZO (fun s => (Gammaℂ s)⁻¹) (j : ℂ) 1 := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, j = -(n : ℤ) := ⟨j.natAbs, by omega⟩
  obtain ⟨u, hu, hu0, hue⟩ := invGamma_zo n
  have hjn : (j : ℂ) = -(n : ℂ) := by rw [hn]; push_cast; ring
  have h2pi : (2 * (π : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_ne_zero)
  refine ⟨fun s => (2 * (2 * (π : ℂ)) ^ (-s))⁻¹ * u s, ?_, ?_, ?_⟩
  · have hd : Differentiable ℂ fun s : ℂ => 2 * (2 * (π : ℂ)) ^ (-s) :=
      fun s => (differentiableAt_id.neg.const_cpow (Or.inl h2pi)).const_mul 2
    refine ((hd.analyticAt _).inv ?_).mul (by rw [hjn]; exact hu)
    exact mul_ne_zero two_ne_zero (by rw [Ne, cpow_eq_zero_iff]; tauto)
  · simp only
    rw [hjn]
    refine mul_ne_zero (inv_ne_zero (mul_ne_zero two_ne_zero ?_)) hu0
    rw [Ne, cpow_eq_zero_iff]; tauto
  · rw [hjn]
    filter_upwards [hue] with s h1
    rw [Gammaℂ_def, mul_inv, h1]
    ring

end PositivityTheory.Lord
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ZetaEulerProducts.ZetaOrd

section

@[expose] public section

open Filter Topology Complex NumberField InfinitePlace
open scoped Real

namespace PositivityTheory.Lord

open GroundTheory.Global

theorem zeta_analyticAt (K : Type) [Field K] [NumberField K] {x : ℂ} (hx : x ≠ 1) :
    AnalyticAt ℂ (continuedDedekindZeta K) x :=
  (differentiableOn_continuedDedekindZeta K).analyticAt (isOpen_compl_singleton.mem_nhds hx)

theorem zeta_pole (K : Type) [Field K] [NumberField K] :
    ∃ A : ℂ → ℂ, AnalyticAt ℂ A 1 ∧ A 1 ≠ 0 ∧
      ∀ᶠ s in 𝓝[≠] (1 : ℂ), (s - 1) * continuedDedekindZeta K s = A s := by
  refine ⟨Function.update (fun s => (s - 1) * continuedDedekindZeta K s) 1 (dedekindZeta_residue K : ℂ),
    (differentiable_sub_one_mul_continuedDedekindZeta K).analyticAt 1, ?_, ?_⟩
  · rw [Function.update_apply, if_pos rfl]
    exact Complex.ofReal_ne_zero.mpr (dedekindZeta_residue_ne_zero K)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    rw [Function.update_apply, if_neg (show s ≠ 1 from hs)]

theorem completed_zeta_continued_eq (K : Type) [Field K] [NumberField K] {s : ℂ} (hs0 : s ≠ 0) :
    continuedDedekindZeta K s = ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (-(s / 2)) *
      ((Gammaℝ s)⁻¹ ^ nrRealPlaces K * (Gammaℂ s)⁻¹ ^ nrComplexPlaces K) * completedDedekindZeta K s := by
  rw [continuedDedekindZeta_of_ne_zero K hs0, normalizedDedekindZeta, mul_inv, inv_pow, inv_pow]

theorem discr_cpow_analytic (K : Type) [Field K] [NumberField K] (x : ℂ) :
    AnalyticAt ℂ (fun s : ℂ => ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (-(s / 2))) x ∧
      ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (-(x / 2)) ≠ 0 := by
  have hpos : (0 : ℝ) < |(discr K : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))
  refine ⟨AnalyticAt.cpow analyticAt_const (by fun_prop) (Complex.ofReal_mem_slitPlane.mpr hpos), ?_⟩
  rw [Ne, Complex.cpow_eq_zero_iff]
  exact fun h => (Complex.ofReal_ne_zero.mpr hpos.ne') h.1

theorem gammaInv_zo (K : Type) [Field K] [NumberField K] (j : ℤ) (hj : j ≤ 0) :
    ZO (fun s => (Gammaℝ s)⁻¹ ^ nrRealPlaces K * (Gammaℂ s)⁻¹ ^ nrComplexPlaces K) (j : ℂ)
      ((if Even j then 1 else 0) * nrRealPlaces K + 1 * nrComplexPlaces K) :=
  ((invGammaR_zo j hj).pow _).mul ((invGammaC_zo j hj).pow _)

theorem one_le_places (K : Type) [Field K] [NumberField K] : 1 ≤ nrRealPlaces K + nrComplexPlaces K := by
  have h := card_add_two_mul_card_eq_rank K
  have h1 : 0 < Module.finrank ℚ K := Module.finrank_pos
  omega

theorem zeta_zo_nonpos (K : Type) [Field K] [NumberField K] (j : ℤ) (hj : j ≤ 0) :
    ZO (continuedDedekindZeta K) (j : ℂ)
      (nrRealPlaces K * (if Even j then 1 else 0) + nrComplexPlaces K - (if j = 0 then 1 else 0)) := by
  have hG := gammaInv_zo K j hj
  rcases hj.lt_or_eq with hlt | rfl
  · have hb := discr_cpow_analytic K (j : ℂ)
    have hne : j ≠ 0 := hlt.ne
    have hj0 : (j : ℂ) ≠ 0 := by exact_mod_cast hne
    have hj1 : (j : ℂ) ≠ 1 := by
      intro h
      have : j = 1 := by exact_mod_cast h
      omega
    have hΛa : AnalyticAt ℂ (completedDedekindZeta K) (j : ℂ) := by
      refine DifferentiableOn.analyticAt (s := {0}ᶜ ∩ {1}ᶜ) (fun z hz => ?_)
        ((isOpen_compl_singleton.inter isOpen_compl_singleton).mem_nhds ⟨hj0, hj1⟩)
      exact (differentiableAt_completedDedekindZeta K hz.1 hz.2).differentiableWithinAt
    have hΛ0 : completedDedekindZeta K (j : ℂ) ≠ 0 := by
      intro h0
      have hre : 1 < (1 - (j : ℂ)).re := by
        have : (j : ℝ) < 0 := by exact_mod_cast hlt
        simp only [Complex.sub_re, Complex.one_re, Complex.intCast_re]
        linarith
      have hs1 : (1 - (j : ℂ)) ≠ 0 := by
        intro h
        rw [h, Complex.zero_re] at hre
        exact absurd hre (by norm_num)
      have e1 := completedDedekindZeta_one_sub K hj0 hj1
      have e2 := completed_zeta_continued_eq K hs1
      rw [e1, h0, mul_zero] at e2
      exact (zeta_euler K hre).2 e2
    have Z := ((ZO.of_analytic hb.1 hb.2).mul hG).mul (ZO.of_analytic hΛa hΛ0)
    have hord : nrRealPlaces K * (if Even j then 1 else 0) + nrComplexPlaces K - (if j = 0 then 1 else 0)
        = 0 + ((if Even j then 1 else 0) * nrRealPlaces K + 1 * nrComplexPlaces K) + 0 := by
      rw [if_neg hne, Nat.sub_zero]
      ring
    rw [hord]
    refine Z.congr ?_
    filter_upwards [nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds hj0)] with s hs
    exact (completed_zeta_continued_eq K hs).symm
  · have he : Even (0 : ℤ) := ⟨0, rfl⟩
    simp only [Int.cast_zero, he, ↓reduceIte, one_mul, mul_one] at hG ⊢
    have hm : 1 ≤ nrRealPlaces K + nrComplexPlaces K := one_le_places K
    obtain ⟨k, hk⟩ : ∃ k, nrRealPlaces K + nrComplexPlaces K = k + 1 :=
      ⟨_, (Nat.sub_add_cancel hm).symm⟩
    rw [hk] at hG
    rw [hk, Nat.add_sub_cancel]
    have hb0 := discr_cpow_analytic K 0
    obtain ⟨L, hT, hL0⟩ : ∃ L : ℂ, Tendsto (fun s => s * completedDedekindZeta K s) (𝓝[≠] 0) (𝓝 L) ∧ L ≠ 0 := by
      refine ⟨_, tendsto_mul_completedDedekindZeta_zero K, ?_⟩
      have h1 : (0 : ℝ) < √|(discr K : ℝ)| * dedekindZeta_residue K :=
        mul_pos (Real.sqrt_pos.mpr (abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))))
          (dedekindZeta_residue_pos K)
      exact neg_ne_zero.mpr (mul_ne_zero (Complex.ofReal_ne_zero.mpr h1.ne')
        (inv_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))))
    set F : ℂ → ℂ := Function.update (fun s => s * completedDedekindZeta K s) 0 L with hFdef
    have hFa : AnalyticAt ℂ F 0 := by
      apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      · filter_upwards [self_mem_nhdsWithin,
          nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds (zero_ne_one : (0 : ℂ) ≠ 1))] with z hz0 hz1
        have hd : DifferentiableAt ℂ (fun s => s * completedDedekindZeta K s) z :=
          differentiableAt_id.mul (differentiableAt_completedDedekindZeta K hz0 hz1)
        refine hd.congr_of_eventuallyEq ?_
        filter_upwards [isOpen_compl_singleton.mem_nhds hz0] with w hw
        rw [hFdef, Function.update_apply, if_neg (show w ≠ 0 from hw)]
      · rw [hFdef]
        exact continuousAt_update_same.mpr hT
    unfold ZO at hG ⊢
    obtain ⟨u, hu, hu0, hGu⟩ := hG
    refine ⟨fun s => ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (-(s / 2)) * u s * F s, (hb0.1.mul hu).mul hFa, ?_, ?_⟩
    · refine mul_ne_zero (mul_ne_zero hb0.2 hu0) ?_
      rw [hFdef, Function.update_apply, if_pos rfl]
      exact hL0
    · filter_upwards [self_mem_nhdsWithin, hGu] with s hs hGs
      beta_reduce at hGs
      rw [completed_zeta_continued_eq K hs, hGs]
      have hFs : F s = s * completedDedekindZeta K s := by
        rw [hFdef, Function.update_apply, if_neg (show s ≠ 0 from hs)]
      rw [hFs, pow_succ]
      ring

end PositivityTheory.Lord
end
end
