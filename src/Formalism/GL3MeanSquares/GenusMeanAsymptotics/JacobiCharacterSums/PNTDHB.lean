module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHBSt
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.DeuringHeilbronnFinishTuran
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHSt
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LandauLocal3
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MeanSquareHypWIff
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHDom
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.DHFinish2Of
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHHyperA
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHHyperB
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHHyperC
import Mathlib.Algebra.Order.Star.Real
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHIneqF
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHLocal
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHPos
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHPrime
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Turan2Main

-- Source module: Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHCauchy

section

@[expose] public section

open Finset Complex Classical Filter Topology

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

lemma dhc_removable (Z : Finset ℂ) : ∀ (U : Set ℂ) (G : ℂ → ℂ) (C : ℝ), IsOpen U →
    DifferentiableOn ℂ G (U \ (Z : Set ℂ)) → (∀ z ∈ U \ (Z : Set ℂ), ‖G z‖ ≤ C) →
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H U ∧ (∀ z ∈ U \ (Z : Set ℂ), H z = G z) ∧
      ∀ z ∈ U, ‖H z‖ ≤ C := by
  induction Z using Finset.induction_on with
  | empty =>
    intro U G C _ hd hb
    exact ⟨G, by simpa using hd, fun _ _ => rfl, by simpa using hb⟩
  | insert a Z ha ih =>
    intro U G C hU hd hb
    have hset : U \ ((insert a Z : Finset ℂ) : Set ℂ) = (U \ {a}) \ (Z : Set ℂ) := by
      ext z
      simp [not_or, and_assoc]
    rw [hset] at hd hb
    obtain ⟨H₁, hH₁d, hH₁e, hH₁b⟩ := ih (U \ {a}) G C (hU.sdiff isClosed_singleton) hd hb
    rw [hset]
    by_cases haU : a ∈ U
    · have hUa : U ∈ 𝓝 a := hU.mem_nhds haU
      have hbd : BddAbove (norm ∘ H₁ '' (U \ {a})) :=
        ⟨C, by rintro _ ⟨z, hz, rfl⟩; exact hH₁b z hz⟩
      have hD := differentiableOn_update_limUnder_of_bddAbove hUa hH₁d hbd
      have hne : ∀ z, z ≠ a → Function.update H₁ a (limUnder (𝓝[≠] a) H₁) z = H₁ z :=
        fun z hz => Function.update_of_ne hz _ _
      refine ⟨_, hD, ?_, ?_⟩
      · intro z hz
        rw [hne z hz.1.2]
        exact hH₁e z hz
      · intro z hz
        by_cases hza : z = a
        · rw [hza]
          have hc := (hD.differentiableAt hUa).continuousAt
          have ht := (hc.norm).tendsto.mono_left (nhdsWithin_le_nhds (s := {a}ᶜ))
          refine le_of_tendsto ht ?_
          filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hUa] with w hw hwU
          rw [hne w hw]
          exact hH₁b w ⟨hwU, hw⟩
        · rw [hne z hza]
          exact hH₁b z ⟨hz, hza⟩
    · have hUe : U \ {a} = U := Set.sdiff_singleton_eq_self haU
      rw [hUe] at hH₁d hH₁b hH₁e ⊢
      exact ⟨H₁, hH₁d, hH₁e, hH₁b⟩

lemma dhc_iter (c ρ : ℂ) (k : ℕ) (s : ℂ) :
    iteratedDeriv k (fun z => c / (z - ρ)) s =
      c * ((-1) ^ k * (k.factorial : ℂ)) * ((s - ρ) ^ (k + 1))⁻¹ := by
  have h : (fun z : ℂ => c / (z - ρ)) = fun z => c * (fun z : ℂ => (1 * z - ρ)⁻¹) z := by
    ext z
    simp [div_eq_mul_inv]
  have hk : (-1 - (k : ℤ)) = -((k + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h, iteratedDeriv_const_mul_field, iteratedDeriv_eq_iterate, iter_deriv_inv_linear_sub]
  simp only [one_pow, mul_one, one_mul]
  rw [hk, zpow_neg, zpow_natCast]
  ring

lemma dhc_cauchy (H : ℂ → ℂ) (z₀ s : ℂ) (ϱ C : ℝ) (hϱ : 0 < ϱ)
    (hHd : DifferentiableOn ℂ H (Metric.ball z₀ (2 * ϱ))) (hHb : ∀ z ∈ Metric.ball z₀ (2 * ϱ), ‖H z‖ ≤ C)
    (hs : s ∈ Metric.closedBall z₀ ϱ) (k : ℕ) :
    ‖iteratedDeriv k H s‖ ≤ k.factorial * C / ϱ ^ k := by
  have hcont : ContinuousAt (fun R : ℝ => (k.factorial : ℝ) * C / R ^ k) ϱ :=
    continuousAt_const.div (continuousAt_id.pow k) (pow_pos hϱ k).ne'
  have ht := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio ϱ))
  refine ge_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsLT hϱ] with R hR
  have hsub : Metric.closedBall s R ⊆ Metric.ball z₀ (2 * ϱ) := by
    intro z hz
    rw [Metric.mem_closedBall] at hz hs
    rw [Metric.mem_ball]
    have := dist_triangle z s z₀
    linarith [hR.2]
  exact norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hR.1 (hHd.diffContOnCl_ball hsub)
    (fun z hz => hHb z (hsub (Metric.sphere_subset_closedBall hz)))

theorem deuring_heilbronn_cauchy : DHCauchy := by
  intro f z₀ r B hr hB hfd hf0 hfb
  obtain ⟨Z, m, hZ, hm1, -, -, hsum, hbd⟩ := landau_local3 f z₀ r B hr hB hfd hf0 hfb
  refine ⟨Z, m, hZ, hm1, hsum, ?_⟩
  have hfan : ∀ z ∈ Metric.ball z₀ (r / 6), AnalyticAt ℂ f z := fun z hz =>
    (hfd.mono Metric.ball_subset_closedBall).analyticAt
      (Metric.isOpen_ball.mem_nhds (Metric.ball_subset_ball (by linarith) hz))
  have hnz : ∀ z ∈ Metric.ball z₀ (r / 6) \ (Z : Set ℂ), f z ≠ 0 := fun z hz h0 =>
    hz.2 (Finset.mem_coe.2 ((hZ z).2
      ⟨Metric.closedBall_subset_closedBall (by linarith) (Metric.ball_subset_closedBall hz.1), h0⟩))
  have hGd : DifferentiableOn ℂ (fun z => deriv f z / f z - ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ))
      (Metric.ball z₀ (r / 6) \ (Z : Set ℂ)) := by
    intro z hz
    have h1 := hfan z hz.1
    refine DifferentiableAt.differentiableWithinAt ?_
    refine (h1.deriv.differentiableAt.div h1.differentiableAt (hnz z hz)).sub ?_
    refine DifferentiableAt.fun_sum (fun ρ hρ => ?_)
    exact (differentiableAt_const _).div (differentiableAt_id.sub_const ρ)
      (sub_ne_zero.2 (fun h => hz.2 (h ▸ Finset.mem_coe.2 hρ)))
  obtain ⟨H, hHd, hHe, hHb⟩ := dhc_removable Z _ _ (72 * Real.log B / r) Metric.isOpen_ball hGd
    (fun z hz => hbd z (Metric.ball_subset_closedBall hz.1) (hnz z hz))
  intro k s hs hfs
  have hsZ : s ∉ (Z : Set ℂ) := fun h => hfs ((hZ s).1 (Finset.mem_coe.1 h)).2
  have hsU : s ∈ Metric.ball z₀ (r / 6) := by
    rw [Metric.mem_closedBall] at hs
    rw [Metric.mem_ball]
    linarith
  have hev : (fun z => -(deriv f z / f z)) =ᶠ[𝓝 s]
      fun z => -(∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ)) - H z := by
    have hn : Metric.ball z₀ (r / 6) \ (Z : Set ℂ) ∈ 𝓝 s :=
      (Metric.isOpen_ball.sdiff Z.finite_toSet.isClosed).mem_nhds ⟨hsU, hsZ⟩
    filter_upwards [hn] with z hz
    rw [hHe z hz]
    ring
  have hHan : AnalyticAt ℂ H s := hHd.analyticAt (Metric.isOpen_ball.mem_nhds hsU)
  have hcd : ∀ ρ ∈ Z, ContDiffAt ℂ k (fun z => (m ρ : ℂ) / (z - ρ)) s := fun ρ hρ =>
    contDiffAt_const.div (contDiffAt_id.sub contDiffAt_const)
      (sub_ne_zero.2 (fun h => hsZ (h ▸ Finset.mem_coe.2 hρ)))
  have hkey : ‖iteratedDeriv k H s‖ ≤ k.factorial * (72 * Real.log B / r) / (r / 12) ^ k := by
    have h2 : 2 * (r / 12) = r / 6 := by ring
    exact dhc_cauchy H z₀ s (r / 12) _ (by positivity) (h2 ▸ hHd) (h2 ▸ hHb) hs k
  have hfac : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hpm : ((-1 : ℂ) ^ k * (-1) ^ k) = 1 := by rw [← mul_pow]; simp
  rw [hev.iteratedDeriv_eq k, iteratedDeriv_fun_sub (ContDiffAt.neg (ContDiffAt.sum hcd)) hHan.contDiffAt,
    iteratedDeriv_fun_neg, iteratedDeriv_fun_sum hcd]
  simp_rw [dhc_iter]
  have he : (-1 : ℂ) ^ k / (k.factorial : ℂ) *
        (-∑ ρ ∈ Z, (m ρ : ℂ) * ((-1) ^ k * (k.factorial : ℂ)) * ((s - ρ) ^ (k + 1))⁻¹ -
          iteratedDeriv k H s) + ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1) =
      -((-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k H s) := by
    have : ∑ ρ ∈ Z, (m ρ : ℂ) * ((-1) ^ k * (k.factorial : ℂ)) * ((s - ρ) ^ (k + 1))⁻¹ =
        ((-1) ^ k * (k.factorial : ℂ)) * ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun ρ _ => ?_)
      rw [div_eq_mul_inv]
      ring
    rw [this]
    generalize (∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1)) = S
    field_simp
    linear_combination (-(k.factorial : ℂ) * S) * hpm
  rw [he, norm_neg, norm_mul, norm_div, norm_pow, norm_neg, norm_one, one_pow, Complex.norm_natCast]
  have hfr : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  calc 1 / (k.factorial : ℝ) * ‖iteratedDeriv k H s‖
      ≤ 1 / (k.factorial : ℝ) * (k.factorial * (72 * Real.log B / r) / (r / 12) ^ k) := by gcongr
    _ = 72 * Real.log B / r * (12 / r) ^ k := by
      rw [div_pow, div_pow]
      field_simp

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end
end

-- Source module: Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHHyper

section

@[expose] public section

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

namespace Hyp

theorem g_mono (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) :
    (Real.log b + 1) / √b ≤ 2 * ((Real.log a + 1) / √a) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hL : 0 ≤ Real.log a := Real.log_nonneg ha
  have hsa : 0 < √a := Real.sqrt_pos.2 ha0
  have hsb : 0 < √b := Real.sqrt_pos.2 hb0
  set s := √b / √a with hs
  have hs1 : 1 ≤ s := by
    rw [hs, le_div_iff₀ hsa, one_mul]
    exact Real.sqrt_le_sqrt hab
  have hs0 : 0 < s := by linarith
  have hsb' : √b = √a * s := by
    rw [hs]
    field_simp
  have hb' : b = a * s ^ 2 := by
    rw [hs, div_pow, Real.sq_sqrt hb0.le, Real.sq_sqrt ha0.le]
    field_simp
  have hlogb : Real.log b = Real.log a + 2 * Real.log s := by
    rw [hb', Real.log_mul ha0.ne' (by positivity), Real.log_pow]
    push_cast
    ring
  have hlogs : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos hs0
  rw [hsb', hlogb, div_le_iff₀ (by positivity)]
  have e : 2 * ((Real.log a + 1) / √a) * (√a * s) = 2 * (Real.log a + 1) * s := by
    field_simp
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left hs1 hL]

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

theorem diff_bound (hχ : χ ≠ 1) (N₀ N₁ : ℕ) (h0 : 1 ≤ N₀) (h01 : N₀ ≤ N₁) :
    (cF χ N₁ - cF χ N₀).re ≤ ‖DirichletCharacter.LFunction χ 1‖ * (Real.log N₁ - Real.log N₀) +
      86 * ((q : ℝ) + 1) * ((Real.log N₀ + 1) / √(N₀ : ℝ)) := by
  set L := DirichletCharacter.LFunction χ 1
  set U₀ := Nat.sqrt N₀ with hU₀
  set U₁ := Nat.sqrt N₁ with hU₁
  set B := (q : ℝ) + 1 with hBdef
  have hB : 1 ≤ B := by have := Nat.cast_nonneg (α := ℝ) q; linarith
  have hN0r : (1 : ℝ) ≤ N₀ := by exact_mod_cast h0
  have hN01r : (N₀ : ℝ) ≤ N₁ := by exact_mod_cast h01
  have hU01 : U₀ ≤ U₁ := Nat.sqrt_le_sqrt h01
  have hU0 : 1 ≤ U₀ := Nat.sqrt_pos.mpr (by omega)
  have hR1 := cF_approx χ hχ N₁ (by omega)
  have hR0 := cF_approx χ hχ N₀ h0
  have hT := cT_diff χ hχ U₀ U₁ hU0 hU01
  set R₁ := cF χ N₁ - (((Real.log N₁ + Real.eulerMascheroniConstant : ℝ) : ℂ) * L - cT χ U₁)
  set R₀ := cF χ N₀ - (((Real.log N₀ + Real.eulerMascheroniConstant : ℝ) : ℂ) * L - cT χ U₀)
  set t := Real.log N₁ - Real.log N₀ with ht
  have ht0 : 0 ≤ t := by
    have := Real.log_le_log (by linarith) hN01r; linarith
  set W := -(cT χ U₁ - cT χ U₀) + R₁ - R₀ with hW
  have eD : cF χ N₁ - cF χ N₀ = (t : ℂ) * L + W := by
    simp only [hW, R₁, R₀, ht]; push_cast; ring
  rw [eD, Complex.add_re, Complex.re_ofReal_mul]
  have hLre : L.re ≤ ‖L‖ := Complex.re_le_norm L
  have hWre : W.re ≤ ‖W‖ := Complex.re_le_norm W
  have hWn : ‖W‖ ≤ ‖cT χ U₁ - cT χ U₀‖ + ‖R₁‖ + ‖R₀‖ := by
    rw [hW]
    calc ‖-(cT χ U₁ - cT χ U₀) + R₁ - R₀‖ ≤ ‖-(cT χ U₁ - cT χ U₀) + R₁‖ + ‖R₀‖ := norm_sub_le _ _
      _ ≤ ‖-(cT χ U₁ - cT χ U₀)‖ + ‖R₁‖ + ‖R₀‖ := by gcongr; exact norm_add_le _ _
      _ = _ := by rw [norm_neg]
  have hg := g_mono (N₀ : ℝ) (N₁ : ℝ) hN0r hN01r
  set g₀ := (Real.log N₀ + 1) / √(N₀ : ℝ)
  have hg0 : 0 ≤ g₀ := div_nonneg (by linarith [Real.log_natCast_nonneg N₀]) (Real.sqrt_nonneg _)
  have hR1' : ‖R₁‖ ≤ 52 * B * g₀ := by
    have e : 26 * B * (Real.log N₁ + 1) / √(N₁ : ℝ) = 26 * B * ((Real.log N₁ + 1) / √(N₁ : ℝ)) := by ring
    rw [e] at hR1
    have := mul_le_mul_of_nonneg_left hg (by positivity : (0 : ℝ) ≤ 26 * B)
    nlinarith
  have hR0' : ‖R₀‖ ≤ 26 * B * g₀ := by
    have e : 26 * B * (Real.log N₀ + 1) / √(N₀ : ℝ) = 26 * B * g₀ := by ring
    rw [e] at hR0; exact hR0
  have hT' : ‖cT χ U₁ - cT χ U₀‖ ≤ 8 * B * g₀ := by
    have hUr : (1 : ℝ) ≤ U₀ := by exact_mod_cast hU0
    have hUN : U₀ ≤ N₀ := Nat.sqrt_le_self N₀
    have hUNr : (U₀ : ℝ) ≤ N₀ := by exact_mod_cast hUN
    have hlt : N₀ < (U₀ + 1) * (U₀ + 1) := Nat.lt_succ_sqrt N₀
    have hltr : (N₀ : ℝ) < ((U₀ : ℝ) + 1) * ((U₀ : ℝ) + 1) := by exact_mod_cast hlt
    have hsU : √(N₀ : ℝ) < (U₀ : ℝ) + 1 := by
      have := Real.sqrt_lt_sqrt (Nat.cast_nonneg N₀) hltr
      rwa [Real.sqrt_mul_self (by linarith)] at this
    have hs0 : 0 < √(N₀ : ℝ) := Real.sqrt_pos.mpr (by linarith)
    have hlog : Real.log ((U₀ : ℝ) + 1) ≤ 1 + Real.log N₀ := by
      have h1 : Real.log ((U₀ : ℝ) + 1) ≤ Real.log (2 * N₀) := Real.log_le_log (by linarith) (by linarith)
      rw [Real.log_mul (by norm_num) (by linarith)] at h1
      have := Real.log_two_lt_d9
      linarith
    have hln : 0 ≤ Real.log N₀ := Real.log_natCast_nonneg N₀
    have h2 : (1 + Real.log ((U₀ : ℝ) + 1)) / ((U₀ : ℝ) + 1) ≤ 2 * g₀ := by
      have e : 2 * g₀ = 2 * (Real.log N₀ + 1) / √(N₀ : ℝ) := by ring
      rw [e, div_le_div_iff₀ (by linarith) hs0]
      nlinarith
    have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 4 * B)
    linarith
  have hLt : t * L.re ≤ ‖L‖ * t := by nlinarith
  linarith

end Hyp

theorem deuring_heilbronn_hypergeometric : DHHyper := by
  refine ⟨400, by norm_num, ?_⟩
  intro M _ χ₁ y x hM _ hne hy hyx
  have e : ∀ N₀ N₁ : ℕ, N₀ ≤ N₁ → ∑ n ∈ Finset.Ioc N₀ N₁, (∑ d ∈ n.divisors, χ₁ (d : ZMod M)).re / (n : ℝ) =
      (Hyp.cF χ₁ N₁ - Hyp.cF χ₁ N₀).re := by
    intro N₀ N₁ h
    rw [Hyp.cF, Hyp.cF, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le N₀) h, add_sub_cancel_left,
      Complex.re_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Complex.div_natCast_re]
  have h0 : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by simpa using hy)
  have h01 : ⌊y⌋₊ ≤ ⌊x⌋₊ := Nat.floor_mono hyx
  rw [e _ _ h01]
  have hd := Hyp.diff_bound χ₁ hne ⌊y⌋₊ ⌊x⌋₊ h0 h01
  set N₀ := ⌊y⌋₊ with hN₀
  set N₁ := ⌊x⌋₊ with hN₁
  set L := DirichletCharacter.LFunction χ₁ 1
  set B := (M : ℝ) + 1 with hBdef
  have hMr : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hN0y : (N₀ : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hyN0 : y < N₀ + 1 := Nat.lt_floor_add_one y
  have hN1x : (N₁ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hN0r : (1 : ℝ) ≤ N₀ := by exact_mod_cast h0
  have hN01r : (N₀ : ℝ) ≤ N₁ := by exact_mod_cast h01
  have hly : 0 ≤ Real.log y := Real.log_nonneg hy

  have hlog1 : Real.log N₁ ≤ Real.log x := Real.log_le_log (by linarith) hN1x
  have hlog0 : Real.log y - Real.log N₀ ≤ 2 / y := by
    rw [← Real.log_div (by linarith) (by linarith)]
    have h := Real.log_le_sub_one_of_pos (show 0 < y / N₀ by positivity)
    have h' : y / N₀ - 1 ≤ 2 / y := by
      rw [div_sub_one (by linarith), div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith
    linarith
  have hxy : Real.log (x / y) = Real.log x - Real.log y := Real.log_div (by linarith) (by linarith)

  have hLB : ‖L‖ ≤ 5 * B := by
    have h := Hyp.cS_approx χ₁ hne 1 le_rfl
    have h1 : Hyp.cS χ₁ 1 = 1 := by simp [Hyp.cS]
    rw [h1] at h
    have := norm_sub_norm_le L 1
    simp only [norm_one, Nat.cast_one, div_one] at h this
    linarith

  have hsy : 0 < √y := Real.sqrt_pos.mpr (by linarith)
  have hs0 : 0 < √(N₀ : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hsyN : √y ≤ 2 * √(N₀ : ℝ) := by
    have h4 : (2 * √(N₀ : ℝ)) * (2 * √(N₀ : ℝ)) = 4 * N₀ := by
      have := Real.mul_self_sqrt (Nat.cast_nonneg (α := ℝ) N₀); nlinarith
    have := Real.sqrt_le_sqrt (show y ≤ (2 * √(N₀ : ℝ)) * (2 * √(N₀ : ℝ)) by rw [h4]; linarith)
    rwa [Real.sqrt_mul_self (by positivity)] at this
  have hlN0 : Real.log N₀ ≤ Real.log y := Real.log_le_log (by linarith) hN0y
  set Y := (Real.log y + 1) / √y with hY
  have hY0 : 0 ≤ Y := by positivity
  have hg0 : (Real.log N₀ + 1) / √(N₀ : ℝ) ≤ 2 * Y := by
    have e2 : 2 * Y = 2 * (Real.log y + 1) / √y := by ring
    rw [e2, div_le_div_iff₀ hs0 hsy]
    have hln : 0 ≤ Real.log N₀ := Real.log_natCast_nonneg N₀
    nlinarith
  have hyY : 2 / y ≤ 2 * Y := by
    have hsyy : √y ≤ y := by
      have := Real.sqrt_le_sqrt (show y ≤ y * y by nlinarith)
      rwa [Real.sqrt_mul_self (by linarith)] at this
    have e2 : 2 * Y = 2 * (Real.log y + 1) / √y := by ring
    rw [e2, div_le_div_iff₀ (by linarith) hsy]
    nlinarith
  have hLn : 0 ≤ ‖L‖ := norm_nonneg _
  have i1 : ‖L‖ * (Real.log N₁ - Real.log N₀) ≤ ‖L‖ * Real.log (x / y) + ‖L‖ * (2 / y) := by
    rw [hxy, ← mul_add]; exact mul_le_mul_of_nonneg_left (by linarith) hLn
  have i2 : ‖L‖ * (2 / y) ≤ 5 * B * (2 * Y) := mul_le_mul hLB hyY (by positivity) (by positivity)
  have i3 : 86 * B * ((Real.log N₀ + 1) / √(N₀ : ℝ)) ≤ 86 * B * (2 * Y) :=
    mul_le_mul_of_nonneg_left hg0 (by positivity)
  have e3 : 400 * (M : ℝ) * (Real.log y + 1) / √y = 400 * M * Y := by rw [hY]; ring
  rw [e3]
  have hB2 : B ≤ 2 * M := by rw [hBdef]; linarith
  have i4 : 5 * B * (2 * Y) + 86 * B * (2 * Y) ≤ 400 * M * Y := by nlinarith
  linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end
end

-- Source module: Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.TuranPowerSumBound

section

@[expose] public section

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

theorem turan_power_sum_bound : DHTuran2 := by
  refine ⟨1600, 1, by norm_num, le_rfl, fun n m z hn hz hz1 => ?_⟩
  obtain ⟨k, h1, h2, h3⟩ := T2.turan2Main n m z hn hz hz1
  exact ⟨k, h1, by simpa using h2, by simpa using h3⟩

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end
end

-- Source module: Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHB

section

@[expose] public section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

theorem deuring_heilbronn_lossy : DeuringHeilbronnMB :=
  deuring_heilbronn_finish_turan turan_power_sum_bound (deuring_heilbronn_inequality deuring_heilbronn_positivity (deuring_heilbronn_local deuring_heilbronn_cauchy) deuring_heilbronn_dominant)
    (deuring_heilbronn_prime_sum deuring_heilbronn_hypergeometric)

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end
