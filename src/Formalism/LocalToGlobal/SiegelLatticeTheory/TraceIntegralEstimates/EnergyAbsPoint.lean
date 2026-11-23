module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsTrunc
public import Mathlib.Order.CompletePartialOrder
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsBasic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.MeasureTheory.Group.MeasurableEquiv
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Measure.Prod
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsTail
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosedProd

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsEquiv

section

@[expose] public section

noncomputable section

open MeasureTheory
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.S.Pv.EnergyAbs

open Formalism.L2.SG.Pf.EnergyAbs

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']

omit [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] [CompleteSpace HH] in
theorem fY_linear (σ : G → (HH →L[ℂ] HH)) (w : HH) (W : G → V) (e : V) (p : G × G) :
    ∑ i, ⟪stdOrthonormalBasis ℂ V i, e⟫_ℂ • fY σ w W (stdOrthonormalBasis ℂ V i) p = fY σ w W e p := by
  simp only [fY]
  simp_rw [smul_smul, ← Finset.sum_smul]
  congr 1
  rw [← (stdOrthonormalBasis ℂ V).sum_inner_mul_inner (W (p.2⁻¹ * p.1)) e]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem Yop_apply_integral {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {μ μS ν : Measure G} [SFinite ν]
    [SFinite μS] {d : ℝ} {w : HH} {S : Set G} {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hW : IsWAbs μ σ d w S τ ν W) (hinv : ∀ a ∈ S, a⁻¹ ∈ S) {A : Set G} (hA : MeasurableSet A) (hAS : A ⊆ S)
    (hAf : μS A < ⊤) (e : V) :
    Yop μS ν σ w W A e = ∫ p, fY σ w W e p ∂(ν.prod (μS.restrict A)) := by
  rw [Yop_apply]
  simp_rw [yv_eq_integral hσ hW hinv hA hAS hAf]
  have hint : ∀ i, Integrable (fun p => ⟪stdOrthonormalBasis ℂ V i, e⟫_ℂ •
      fY σ w W (stdOrthonormalBasis ℂ V i) p) (ν.prod (μS.restrict A)) :=
    fun i => (integrable_fY hσ hW hinv hA hAS hAf _).smul _
  symm
  calc ∫ p, fY σ w W e p ∂(ν.prod (μS.restrict A))
      = ∫ p, ∑ i, ⟪stdOrthonormalBasis ℂ V i, e⟫_ℂ • fY σ w W (stdOrthonormalBasis ℂ V i) p
          ∂(ν.prod (μS.restrict A)) := by
        congr 1
        funext p
        exact (fY_linear σ w W e p).symm
    _ = ∑ i, ∫ p, ⟪stdOrthonormalBasis ℂ V i, e⟫_ℂ • fY σ w W (stdOrthonormalBasis ℂ V i) p
          ∂(ν.prod (μS.restrict A)) := integral_finsetSum _ fun i _ => hint i
    _ = _ := by simp_rw [integral_smul]

omit [SecondCountableTopology G] in
theorem prod_restrict_translate {μS : Measure G} [SFinite μS] (ν : Measure G) [SFinite ν] {s0 : G}
    (hmap : μS.map (fun x => x * s0⁻¹) = μS) (A : Set G) :
    ν.prod (μS.restrict A) =
      (ν.prod (μS.restrict ((fun v => v * s0⁻¹) ⁻¹' A))).map (Prod.map id (fun v => v * s0⁻¹)) := by
  have hE := (MeasurableEquiv.mulRight (s0⁻¹ : G)).measurableEmbedding.restrict_map μS A
  rw [MeasurableEquiv.coe_mulRight, hmap] at hE
  rw [← Measure.map_prod_map ν _ measurable_id (measurable_mul_const s0⁻¹), Measure.map_id, ← hE]

theorem sigma_Yop {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {μ μS ν : Measure G} [SFinite ν] {S : Set G}
    (hS : IsHaarSub S μS) {d : ℝ} {w : HH} {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hW : IsWAbs μ σ d w S τ ν W) {A : Set G} (hA : MeasurableSet A) (hAS : A ⊆ S) (hAf : μS A < ⊤)
    {s0 : G} (hs0 : s0 ∈ S) (e : V) :
    σ s0⁻¹ (Yop μS ν σ w W A e) =
      Yop μS ν σ w W ((fun v => v * s0⁻¹) ⁻¹' A) (ContinuousLinearMap.adjoint (τ s0) e) := by
  obtain ⟨-, -, hmulS, hinvS, hsig, -, -, -, -, hright, -⟩ := hS
  have : SFinite μS := by have := hsig; infer_instance
  have hmap : μS.map (fun x => x * s0⁻¹) = μS := hright _ (hinvS s0 hs0)
  have hA'm : MeasurableSet ((fun v => v * s0⁻¹) ⁻¹' A) := measurable_mul_const s0⁻¹ hA
  have hA'S : (fun v => v * s0⁻¹) ⁻¹' A ⊆ S := by
    intro v hv
    have h1 := hmulS _ (hAS hv) s0 hs0
    simpa [mul_assoc] using h1
  have hA'f : μS ((fun v => v * s0⁻¹) ⁻¹' A) < ⊤ := by
    rw [← Measure.map_apply (measurable_mul_const s0⁻¹) hA, hmap]
    exact hAf
  have hemb : MeasurableEmbedding (Prod.map id (fun v : G => v * s0⁻¹)) :=
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl G) (MeasurableEquiv.mulRight s0⁻¹)).measurableEmbedding

  rw [Yop_apply_integral hσ hW hinvS hA hAS hAf, Yop_apply_integral hσ hW hinvS hA'm hA'S hA'f,
    ← ContinuousLinearMap.integral_comp_comm _ (integrable_fY hσ hW hinvS hA hAS hAf e),
    prod_restrict_translate ν hmap A, hemb.integral_map]
  congr 1
  funext p
  have hq : (p.2 * s0⁻¹)⁻¹ * p.1 = s0 * (p.2⁻¹ * p.1) := by group
  simp only [fY, Prod.map, id_eq, ContinuousLinearMap.map_smul]
  rw [hq, rep_mul_apply hσ, inv_mul_cancel_left, hW.2.2.2.1 s0 hs0,
    ContinuousLinearMap.adjoint_inner_right]

theorem sand_translate {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {μ μS ν μS' ν' : Measure G} [SFinite ν]
    [SFinite ν'] {S S' : Set G} (hS : IsHaarSub S μS) (hS' : IsHaarSub S' μS') {d : ℝ} {w : HH}
    {τ : G → (V →L[ℂ] V)} {τ' : G → (V' →L[ℂ] V')} {W : G → V} {W' : G → V'}
    (hW : IsWAbs μ σ d w S τ ν W) (hW' : IsWAbs μ σ d w S' τ' ν' W')
    {Ω Ω' : Set G} (hΩm : MeasurableSet Ω) (hΩS : Ω ⊆ S) (hΩf : μS Ω < ⊤)
    (hΩm' : MeasurableSet Ω') (hΩS' : Ω' ⊆ S') (hΩf' : μS' Ω' < ⊤)
    {s0 s0' : G} (hs0 : s0 ∈ S) (hs0' : s0' ∈ S') (γ : G) :
    sand σ (Yop μS ν σ w W Ω) (Yop μS' ν' σ w W' Ω') (s0 * γ * s0'⁻¹) =
      (τ s0).comp ((sand σ (Yop μS ν σ w W ((fun v => v * s0⁻¹) ⁻¹' Ω))
        (Yop μS' ν' σ w W' ((fun v => v * s0'⁻¹) ⁻¹' Ω')) γ).comp (ContinuousLinearMap.adjoint (τ' s0'))) := by
  ext b
  refine ext_inner_left ℂ fun a => ?_
  rw [inner_sand]
  conv_rhs => rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ← ContinuousLinearMap.adjoint_inner_left, inner_sand]
  rw [← sigma_Yop hσ hS hW hΩm hΩS hΩf hs0 a, ← sigma_Yop hσ hS' hW' hΩm' hΩS' hΩf' hs0' b]
  have hmove : ∀ u : HH, σ γ (σ s0'⁻¹ u) = σ s0⁻¹ (σ (s0 * γ * s0'⁻¹) u) := by
    intro u
    rw [rep_mul_apply hσ, rep_mul_apply hσ, show s0⁻¹ * (s0 * γ * s0'⁻¹) = γ * s0'⁻¹ by group]
  rw [hmove, hσ.2.2.1]

theorem hsA_Xop_translate {μ : Measure G} {σ : G → (HH →L[ℂ] HH)} {d : ℝ} {w : HH} {S S' : Set G}
    {μS ν μS' ν' : Measure G} {τ : G → (V →L[ℂ] V)} {τ' : G → (V' →L[ℂ] V')} {W : G → V} {W' : G → V'}
    [SFinite ν] [SFinite ν'] (hσ : IsUnitRep σ) (hS : IsHaarSub S μS) (hS' : IsHaarSub S' μS')
    (hW : IsWAbs μ σ d w S τ ν W) (hW' : IsWAbs μ σ d w S' τ' ν' W')
    {Ω Ω' : Set G} (hΩm : MeasurableSet Ω) (hΩS : Ω ⊆ S) (hΩf : μS Ω < ⊤)
    (hΩm' : MeasurableSet Ω') (hΩS' : Ω' ⊆ S') (hΩf' : μS' Ω' < ⊤)
    {s0 s0' : G} (hs0 : s0 ∈ S) (hs0' : s0' ∈ S') (γ : G) :
    hsA (Xop μS ν μS' ν' σ d w W W' Ω Ω' (s0 * γ * s0'⁻¹)) =
      hsA (Xop μS ν μS' ν' σ d w W W' ((fun v => v * s0⁻¹) ⁻¹' Ω) ((fun v => v * s0'⁻¹) ⁻¹' Ω') γ) := by
  simp only [Xop]
  rw [hsA_smul, hsA_smul, sand_translate hσ hS hS' hW hW' hΩm hΩS hΩf hΩm' hΩS' hΩf' hs0 hs0' γ,
    hsA_conj (τ s0) (τ' s0') (hW.2.2.1 s0 hs0) (hW'.2.2.1 s0' hs0')]

end Formalism.L2.S.Pv.EnergyAbs
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsLower

section

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Measure Filter Topology
open scoped ENNReal

namespace Formalism.L2.S.Pv.EnergyAbs

variable {G : Type} [Group G] [MeasurableSpace G]

theorem lintegral_ge_rect {μS μS' : Measure G} [SFinite μS'] (f : G → G → ℝ≥0∞)
    (hf : Measurable (fun p : G × G => f p.1 p.2)) (E E' : Set G) (c : ℝ≥0∞)
    (h : ∀ s ∈ E, ∀ s' ∈ E', c ≤ f s s') : c * μS' E' * μS E ≤ ∫⁻ s, ∫⁻ s', f s s' ∂μS' ∂μS := by
  have hsec : ∀ s, Measurable (f s) := fun s =>
    hf.comp (by fun_prop : Measurable (fun s' : G => (s, s')))
  have hin : ∀ s ∈ E, c * μS' E' ≤ ∫⁻ s', f s s' ∂μS' := by
    intro s hs
    calc c * μS' E' ≤ c * μS' {s' | c ≤ f s s'} :=
          mul_le_mul' le_rfl (measure_mono fun s' hs' => h s hs s' hs')
      _ ≤ _ := mul_meas_ge_le_lintegral₀ (hsec s).aemeasurable c
  have hg : Measurable (fun s => ∫⁻ s', f s s' ∂μS') := hf.lintegral_prod_right'
  calc c * μS' E' * μS E ≤ c * μS' E' * μS {s | c * μS' E' ≤ ∫⁻ s', f s s' ∂μS'} :=
        mul_le_mul' le_rfl (measure_mono fun s hs => hin s hs)
    _ ≤ _ := mul_meas_ge_le_lintegral₀ hg.aemeasurable _

def folInt (Ω K : Set G) : Set G := {t | t ∈ Ω ∧ ∀ k ∈ K, k * t ∈ Ω}

theorem measure_inv_preimage {μS : Measure G} [MeasurableInv G] (hinv : μS.map (fun x => x⁻¹) = μS)
    (B : Set G) : μS {s | s⁻¹ ∈ B} = μS B := by
  have e : (μS.map (MeasurableEquiv.inv G)) B = μS ((MeasurableEquiv.inv G) ⁻¹' B) :=
    MeasurableEquiv.map_apply _ _
  have hm : μS.map (MeasurableEquiv.inv G) = μS := hinv
  rw [hm] at e
  exact e.symm

theorem tendsto_ratio_ennreal {a b : ℕ → ℝ≥0∞} (hb0 : ∀ n, 0 < b n) (hbt : ∀ n, b n < ⊤)
    (hab : ∀ n, a n ≤ b n) (h : Tendsto (fun n => (a n).toReal / (b n).toReal) atTop (𝓝 1)) :
    Tendsto (fun n => a n / b n) atTop (𝓝 1) := by
  have hfin : ∀ n, a n / b n ≠ ⊤ := fun n =>
    ENNReal.div_ne_top (ne_top_of_le_ne_top (hbt n).ne (hab n)) (hb0 n).ne'
  have hfun : (fun n => a n / b n) = fun n => ENNReal.ofReal ((a n).toReal / (b n).toReal) := by
    funext n
    rw [← ENNReal.toReal_div, ENNReal.ofReal_toReal (hfin n)]
  rw [hfun, ← ENNReal.ofReal_one]
  exact ENNReal.tendsto_ofReal h

theorem liminf_lower {μS μS' : Measure G} [SFinite μS'] [MeasurableInv G]
    (hinv : μS.map (fun x => x⁻¹) = μS) (hinv' : μS'.map (fun x => x⁻¹) = μS')
    (Ω Ω' : ℕ → Set G) (hΩ0 : ∀ n, 0 < μS (Ω n)) (hΩt : ∀ n, μS (Ω n) < ⊤)
    (hΩ0' : ∀ n, 0 < μS' (Ω' n)) (hΩt' : ∀ n, μS' (Ω' n) < ⊤)
    (f : ℕ → G → G → ℝ≥0∞) (hf : ∀ n, Measurable (fun p : G × G => f n p.1 p.2)) (h : ℝ) (hh : 0 ≤ h)
    (key : ∀ ε : ℝ, 0 < ε → ∃ K K' : Set G,
      Tendsto (fun n => μS (folInt (Ω n) K) / μS (Ω n)) atTop (𝓝 1) ∧
      Tendsto (fun n => μS' (folInt (Ω' n) K') / μS' (Ω' n)) atTop (𝓝 1) ∧
      ∀ n s s', s⁻¹ ∈ folInt (Ω n) K → s'⁻¹ ∈ folInt (Ω' n) K' →
        ENNReal.ofReal ((max (Real.sqrt h - ε) 0) ^ 2) ≤ f n s s') :
    ENNReal.ofReal h ≤
      liminf (fun n => (μS (Ω n) * μS' (Ω' n))⁻¹ * ∫⁻ s, ∫⁻ s', f n s s' ∂μS' ∂μS) atTop := by
  set L := liminf (fun n => (μS (Ω n) * μS' (Ω' n))⁻¹ * ∫⁻ s, ∫⁻ s', f n s s' ∂μS' ∂μS) atTop
    with hL
  have step : ∀ ε : ℝ, 0 < ε → ENNReal.ofReal ((max (Real.sqrt h - ε) 0) ^ 2) ≤ L := by
    intro ε hε
    obtain ⟨K, K', hK, hK', hf'⟩ := key ε hε
    set c := ENNReal.ofReal ((max (Real.sqrt h - ε) 0) ^ 2) with hc
    have hlim : Tendsto (fun n => c * ((μS (folInt (Ω n) K) / μS (Ω n)) *
        (μS' (folInt (Ω' n) K') / μS' (Ω' n)))) atTop (𝓝 c) := by
      have h1 := ENNReal.Tendsto.mul hK (Or.inl one_ne_zero) hK' (Or.inl one_ne_zero)
      have h2 := ENNReal.Tendsto.const_mul h1 (a := c) (Or.inr ENNReal.ofReal_ne_top)
      rw [mul_one, mul_one] at h2
      exact h2
    rw [hL, ← hlim.liminf_eq]
    refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
    have hA0 := (hΩ0 n).ne'
    have hAt := (hΩt n).ne
    have hmain := lintegral_ge_rect (μS := μS) (μS' := μS') (f n) (hf n)
      {s | s⁻¹ ∈ folInt (Ω n) K} {s' | s'⁻¹ ∈ folInt (Ω' n) K'} c
      (fun s hs s' hs' => hf' n s s' hs hs')
    rw [measure_inv_preimage hinv, measure_inv_preimage hinv'] at hmain
    rw [ENNReal.mul_inv (Or.inl hA0) (Or.inl hAt), div_eq_mul_inv, div_eq_mul_inv]
    calc c * (μS (folInt (Ω n) K) * (μS (Ω n))⁻¹ *
          (μS' (folInt (Ω' n) K') * (μS' (Ω' n))⁻¹))
        = (μS (Ω n))⁻¹ * (μS' (Ω' n))⁻¹ *
          (c * μS' (folInt (Ω' n) K') * μS (folInt (Ω n) K)) := by ring
      _ ≤ _ := mul_le_mul' le_rfl hmain
  have hcont : Continuous (fun ε : ℝ => ENNReal.ofReal ((max (Real.sqrt h - ε) 0) ^ 2)) :=
    ENNReal.continuous_ofReal.comp (((continuous_const.sub continuous_id).max continuous_const).pow 2)
  have h0 : ENNReal.ofReal ((max (Real.sqrt h - 0) 0) ^ 2) = ENNReal.ofReal h := by
    rw [sub_zero, max_eq_left (Real.sqrt_nonneg h), Real.sq_sqrt hh]
  have hg : Tendsto (fun ε : ℝ => ENNReal.ofReal ((max (Real.sqrt h - ε) 0) ^ 2)) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal h)) := by
    rw [← h0]
    exact (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  exact le_of_tendsto hg (eventually_nhdsWithin_of_forall fun ε hε => step ε hε)

end Formalism.L2.S.Pv.EnergyAbs
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsPoint

section

@[expose] public section

noncomputable section

open MeasureTheory Measure Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.S.Pv.EnergyAbs

open Formalism.L2.SG.Pf.EnergyAbs

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']

def cpiece (S : Set G) (n : ℕ) : Set G := CompactExhaustion.choice G n ∩ S

theorem cpiece_compact {S : Set G} (hS : IsClosed S) (n : ℕ) : IsCompact (cpiece S n) :=
  ((CompactExhaustion.choice G).isCompact n).inter_right hS

theorem cpiece_mono (S : Set G) : Monotone (cpiece S) := by
  intro m n hmn
  exact Set.inter_subset_inter_left _ ((CompactExhaustion.choice G).subset hmn)

theorem cpiece_cover (S : Set G) : S ⊆ ⋃ n, cpiece S n := by
  intro x hx
  obtain ⟨n, hn⟩ := (CompactExhaustion.choice G).exists_mem x
  exact Set.mem_iUnion.2 ⟨n, hn, hx⟩

theorem translate_props {μS : Measure G} {S : Set G} (hS : IsHaarSub S μS) {Ω : Set G} (hΩm : MeasurableSet Ω)
    (hΩS : Ω ⊆ S) (hΩt : μS Ω < ⊤) {s : G} (hs : s ∈ S) :
    MeasurableSet ((fun v => v * s⁻¹) ⁻¹' Ω) ∧ (fun v => v * s⁻¹) ⁻¹' Ω ⊆ S ∧
      μS ((fun v => v * s⁻¹) ⁻¹' Ω) < ⊤ := by
  obtain ⟨-, -, hmul, hinv, -, -, -, -, -, hr, -⟩ := hS
  refine ⟨hΩm.preimage (measurable_mul_const s⁻¹), fun v hv => ?_, ?_⟩
  · have h1 : v * s⁻¹ * s ∈ S := hmul _ (@hΩS (v * s⁻¹) hv) _ hs
    simpa using h1
  · rw [← Measure.map_apply (measurable_mul_const s⁻¹) hΩm, hr _ (hinv _ hs)]
    exact hΩt

private theorem hilbertSchmidtSq_nonneg_aux_lemma (A : V' →L[ℂ] V) : 0 ≤ Formalism.L2.SG.Pf.EnergyAbs.hsA A := by
  unfold Formalism.L2.SG.Pf.EnergyAbs.hsA
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

private theorem sq_max_le_hilbertSchmidtSq_lemma_2 (A B : V' →L[ℂ] V) {ε : ℝ}
    (h : Real.sqrt (Formalism.L2.SG.Pf.EnergyAbs.hsA (A - B)) ≤ ε) :
    max (Real.sqrt (Formalism.L2.SG.Pf.EnergyAbs.hsA A) - ε) 0 ^ 2 ≤ Formalism.L2.SG.Pf.EnergyAbs.hsA B := by
  have hB := hilbertSchmidtSq_nonneg_aux_lemma B
  have htri := sqrt_hsA_le_add_sub A B
  have hmax : max (Real.sqrt (Formalism.L2.SG.Pf.EnergyAbs.hsA A) - ε) 0 ≤ Real.sqrt (Formalism.L2.SG.Pf.EnergyAbs.hsA B) :=
    max_le (by linarith) (Real.sqrt_nonneg _)
  calc max (Real.sqrt (Formalism.L2.SG.Pf.EnergyAbs.hsA A) - ε) 0 ^ 2 ≤ Real.sqrt (Formalism.L2.SG.Pf.EnergyAbs.hsA B) ^ 2 :=
        pow_le_pow_left₀ (le_max_right _ _) hmax 2
    _ = Formalism.L2.SG.Pf.EnergyAbs.hsA B := Real.sq_sqrt hB

theorem point_lower {μ : Measure G} [μ.IsHaarMeasure] {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {d : ℝ}
    {w : HH} {S S' : Set G} {μS μS' ν ν' : Measure G} {τ : G → (V →L[ℂ] V)} {τ' : G → (V' →L[ℂ] V')}
    {W : G → V} {W' : G → V'} [SFinite ν] [SFinite ν'] (hS : IsHaarSub S μS) (hS' : IsHaarSub S' μS')
    (hq : IsQuot μ μS ν) (hq' : IsQuot μ μS' ν')
    (hW : IsWAbs μ σ d w S τ ν W) (hW' : IsWAbs μ σ d w S' τ' ν' W')
    (Ω Ω' : ℕ → Set G) (hΩ : ∀ n, MeasurableSet (Ω n) ∧ Ω n ⊆ S ∧ 0 < μS (Ω n) ∧ μS (Ω n) < ⊤)
    (hΩ' : ∀ n, MeasurableSet (Ω' n) ∧ Ω' n ⊆ S' ∧ 0 < μS' (Ω' n) ∧ μS' (Ω' n) < ⊤)
    (hF : ∀ K : Set G, IsCompact K → K ⊆ S → Tendsto (fun n =>
      (μS {t | t ∈ Ω n ∧ ∀ k ∈ K, k * t ∈ Ω n}).toReal / (μS (Ω n)).toReal) atTop (𝓝 1))
    (hF' : ∀ K : Set G, IsCompact K → K ⊆ S' → Tendsto (fun n =>
      (μS' {t | t ∈ Ω' n ∧ ∀ k ∈ K, k * t ∈ Ω' n}).toReal / (μS' (Ω' n)).toReal) atTop (𝓝 1))
    (hXc : ∀ n, Continuous (fun g => hsA (Xop μS ν μS' ν' σ d w W W' (Ω n) (Ω' n) g)))
    (γ : G) (hB : ∫⁻ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', bInt σ w W W' γ z z' s s' ∂μS' ∂μS ∂ν' ∂ν < ⊤) :
    ENNReal.ofReal (hsA (∫ x, rk1A (W x) (W' (γ⁻¹ * x)) ∂μ)) ≤
      liminf (fun n => (μS (Ω n) * μS' (Ω' n))⁻¹ *
        ∫⁻ s, ∫⁻ s', ENNReal.ofReal (hsA (Xop μS ν μS' ν' σ d w W W' (Ω n) (Ω' n) (s * γ * s'⁻¹)))
          ∂μS' ∂μS) atTop := by
  have hS₀ := hS
  have hS'₀ := hS'
  obtain ⟨hSc, -, -, hinvS, hσS, -, h0S, -, -, -, hinvmS⟩ := hS₀
  obtain ⟨hSc', -, -, hinvS', hσS', -, h0S', -, -, -, hinvmS'⟩ := hS'₀
  have : SigmaFinite μS := hσS
  have : SigmaFinite μS' := hσS'
  have hm : μ = (ν.prod μS).map φinv := (quot_map_inv hq) hinvmS
  have hm' : μ = (ν'.prod μS').map φinv := (quot_map_inv hq') hinvmS'
  refine liminf_lower hinvmS hinvmS' Ω Ω'
    (fun n => (hΩ n).2.2.1) (fun n => (hΩ n).2.2.2) (fun n => (hΩ' n).2.2.1) (fun n => (hΩ' n).2.2.2)
    (fun n s s' => ENNReal.ofReal (Formalism.L2.SG.Pf.EnergyAbs.hsA
      (Xop μS ν μS' ν' σ d w W W' (Ω n) (Ω' n) (s * γ * s'⁻¹))))
    (fun n => ?_) (Formalism.L2.SG.Pf.EnergyAbs.hsA (∫ x, Formalism.L2.SG.Pf.EnergyAbs.rk1A (W x) (W' (γ⁻¹ * x)) ∂μ))
    (hilbertSchmidtSq_nonneg_aux_lemma _) (fun ε hε => ?_)
  · exact ENNReal.measurable_ofReal.comp ((hXc n).measurable.comp
      ((continuous_fst.mul continuous_const).mul continuous_snd.inv).measurable)
  · obtain ⟨n₀, hn₀⟩ := approx_OO hσ hW hW' hinvS hinvS' h0S h0S' hm hm' γ hB
      (cpiece S) (cpiece S')
      (fun n => (cpiece_compact hSc n).isClosed.measurableSet)
      (fun n => (cpiece_compact hSc' n).isClosed.measurableSet)
      (cpiece_mono S) (cpiece_mono S')
      (cpiece_cover S) (cpiece_cover S') ε hε
    refine ⟨cpiece S n₀, cpiece S' n₀, ?_, ?_, ?_⟩
    · refine tendsto_ratio_ennreal (fun n => (hΩ n).2.2.1) (fun n => (hΩ n).2.2.2)
        (fun n => measure_mono fun t ht => (show t ∈ Ω n ∧ _ from ht).1) ?_
      exact hF _ (cpiece_compact hSc n₀) Set.inter_subset_right
    · refine tendsto_ratio_ennreal (fun n => (hΩ' n).2.2.1) (fun n => (hΩ' n).2.2.2)
        (fun n => measure_mono fun t ht => (show t ∈ Ω' n ∧ _ from ht).1) ?_
      exact hF' _ (cpiece_compact hSc' n₀) Set.inter_subset_right
    · intro n s s' hs hs'
      have hs2 : s⁻¹ ∈ Ω n ∧ ∀ k ∈ cpiece S n₀, k * s⁻¹ ∈ Ω n := hs
      have hs2' : s'⁻¹ ∈ Ω' n ∧ ∀ k ∈ cpiece S' n₀, k * s'⁻¹ ∈ Ω' n := hs'
      have hsS : s ∈ S := by simpa using hinvS _ ((hΩ n).2.1 hs2.1)
      have hsS' : s' ∈ S' := by simpa using hinvS' _ ((hΩ' n).2.1 hs2'.1)
      obtain ⟨hAm, hAS, hAt⟩ := translate_props hS (hΩ n).1 (hΩ n).2.1 (hΩ n).2.2.2 hsS
      obtain ⟨hAm', hAS', hAt'⟩ :=
        translate_props hS' (hΩ' n).1 (hΩ' n).2.1 (hΩ' n).2.2.2 hsS'
      have happrox := hn₀ _ _ hAm hAS hAt hAm' hAS' hAt' (fun k hk => hs2.2 k hk)
        (fun k hk => hs2'.2 k hk)
      rw [hsA_Xop_translate hσ hS hS' hW hW' (hΩ n).1 (hΩ n).2.1
        (hΩ n).2.2.2 (hΩ' n).1 (hΩ' n).2.1 (hΩ' n).2.2.2 hsS hsS' γ]
      exact ENNReal.ofReal_le_ofReal (sq_max_le_hilbertSchmidtSq_lemma_2 _ _ happrox)

end Formalism.L2.S.Pv.EnergyAbs
end
end
end
