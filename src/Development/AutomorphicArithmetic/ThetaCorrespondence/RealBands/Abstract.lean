module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.IsBand
public import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.BandCc
public import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.BandKill
public import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.ConvAssoc
public import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.ConvEig
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.IsBand
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Topology.UrysohnsLemma
public import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.ExistsCompactTail
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Basic
public import Mathlib.Topology.Algebra.Constructions.DomMulAct
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Prod

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.EqZeroOfTest

section

@[expose] public section

open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

theorem UpperTheory.Lit.Cusp.eq_zero_of_test :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (F : G → ℂ), Continuous F →
      (∀ ψ : G → ℂ, Continuous ψ → HasCompactSupport ψ → ∫ y, ψ y⁻¹ * F y ∂μ = 0) → ∀ y, F y = 0 := by
  intro G _ _ _ _ _ _ _ _ μ _ F hF h y₀
  by_contra hy
  obtain ⟨χ, hχc, hχ0, hχy⟩ := exists_continuous_nonneg_pos y₀
  have hχcont : Continuous (fun y => χ y) := χ.continuous
  have hc1 : Continuous (fun y => (χ y : ℂ) * (starRingEnd ℂ) (F y)) :=
    (Complex.continuous_ofReal.comp hχcont).mul (Complex.continuous_conj.comp hF)
  have hs0 : HasCompactSupport (fun y => (χ y : ℂ)) :=
    hχc.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
  have hs1 : HasCompactSupport (fun y => (χ y : ℂ) * (starRingEnd ℂ) (F y)) :=
    hs0.mul_right (f' := fun y => (starRingEnd ℂ) (F y))
  have h1 := h (fun z => (χ z⁻¹ : ℂ) * (starRingEnd ℂ) (F z⁻¹)) (hc1.comp continuous_inv)
    (hs1.comp_homeomorph (Homeomorph.inv G))
  have h2 : ∀ y, (χ y⁻¹⁻¹ : ℂ) * (starRingEnd ℂ) (F y⁻¹⁻¹) * F y
      = ((χ y * ‖F y‖ ^ 2 : ℝ) : ℂ) := by
    intro y
    rw [inv_inv, mul_assoc, Complex.conj_mul']
    push_cast
    rfl
  simp only [h2] at h1
  rw [integral_complex_ofReal, Complex.ofReal_eq_zero] at h1
  have hc2 : Continuous (fun y => χ y * ‖F y‖ ^ 2) := hχcont.mul (hF.norm.pow 2)
  have hs2 : HasCompactSupport (fun y => χ y * ‖F y‖ ^ 2) :=
    hχc.mul_right (f' := fun y => ‖F y‖ ^ 2)
  have hpos := hc2.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := μ) (x := y₀) hs2
    (fun y => mul_nonneg (hχ0 y) (sq_nonneg _))
    (mul_ne_zero hχy (pow_ne_zero 2 (norm_ne_zero_iff.mpr hy)))
  exact hpos.ne' h1
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.Transl

section

@[expose] public section

open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

theorem UpperTheory.Lit.Cusp.transl_small :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (f : G → ℂ), Integrable f μ →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ b in 𝓝 (1 : G), ∫ g, ‖f (b * g) - f g‖ ∂μ ≤ ε := by
  intro G _ _ _ _ _ _ _ _ μ _ f hf ε hε
  haveI : Fact ((1 : ENNReal) ≠ ⊤) := ⟨ENNReal.one_ne_top⟩
  have hm : MemLp f 1 μ := memLp_one_iff_integrable.2 hf
  set F : Lp ℂ 1 μ := hm.toLp f with hF
  have hc : Continuous fun b : G => ‖(DomMulAct.mk b) • F - F‖ :=
    ((DomMulAct.continuous_mk.smul continuous_const).sub continuous_const).norm
  have h1 : ‖(DomMulAct.mk (1 : G)) • F - F‖ < ε := by
    have : (DomMulAct.mk (1 : G)) • F = F := one_smul Gᵈᵐᵃ F
    rw [this, sub_self, norm_zero]; exact hε
  have hev := hc.continuousAt.eventually_lt continuousAt_const h1
  filter_upwards [hev] with b hb
  refine le_of_eq_of_le ?_ hb.le
  rw [L1.norm_eq_integral_norm]
  refine integral_congr_ae ?_
  have hFf : F =ᵐ[μ] f := hm.coeFn_toLp
  have h2 : (fun g => F (b * g)) =ᵐ[μ] fun g => f (b * g) :=
    (measurePreserving_mul_left μ b).quasiMeasurePreserving.ae_eq_comp hFf
  filter_upwards [Lp.coeFn_sub ((DomMulAct.mk b) • F) F, DomMulAct.smul_Lp_ae_eq (DomMulAct.mk b) F, hFf, h2] with g e1 e2 e3 e4
  rw [e1, Pi.sub_apply, e2, e3, ← e4]
  rfl
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.OpLeHalf

section

@[expose] public section

open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

theorem UpperTheory.Lit.Cusp.opLe_half :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (N : Set G) (a : ℝ → G) (H : G → ℝ) (f : G → ℂ),
      IsRay N a H → Integrable f μ → ∃ s : ℝ, OpLe μ N a f s (1 / 2) := by
  intro G _ _ _ _ _ _ _ _ μ _ N a H f hR hf
  have hU := transl_small G μ f hf 1 one_pos
  have a0 : a 0 = 1 := by
    have := hR.add 0 0
    rw [add_zero] at this
    exact (mul_eq_left.mp this.symm)
  obtain ⟨D, hD, hk⟩ := hR.cpt
  have hc : Continuous fun p : ℝ × G => p.2 * a p.1 * p.2⁻¹ :=
    (continuous_snd.mul (hR.cont.comp continuous_fst)).mul continuous_snd.inv
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ k ∈ D, ∫ g, ‖f ((k * a t * k⁻¹) * g) - f g‖ ∂μ ≤ 1 := by
    apply hD.eventually_forall_of_forall_eventually
    intro k _
    have ht : Tendsto (fun p : ℝ × G => p.2 * a p.1 * p.2⁻¹) (𝓝 (0, k)) (𝓝 1) := by
      have := hc.tendsto (0, k)
      simpa [a0] using this
    exact ht.eventually hU
  have hev' : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ k ∈ D, ∫ g, ‖f ((k * a t * k⁻¹) * g) - f g‖ ∂μ ≤ 1 :=
    hev.filter_mono nhdsWithin_le_nhds
  obtain ⟨t, ht, htpos⟩ := (hev'.and self_mem_nhdsWithin).exists
  have htpos : 0 < t := htpos
  refine ⟨Real.pi / t, ?_⟩
  rintro C h ⟨hcont, hbd, hN, hE⟩ x
  obtain ⟨k, hkD, hk⟩ := hk x
  obtain ⟨m, hm, hkm⟩ := hk t
  have hb := ht k hkD
  set b := k * a t * k⁻¹ with hbdef
  have hneg : ∀ g, h (g⁻¹ * b * x) = - h (g⁻¹ * x) := by
    intro g
    have e : g⁻¹ * b * x = g⁻¹ * x * a t * m := by
      rw [mul_assoc, hkm]; simp only [mul_assoc]
    rw [e, hN _ m hm, hE]
    have : Real.pi / t * t = Real.pi := by field_simp
    rw [this, Complex.exp_pi_mul_I]; ring
  have h1 : ∫ g, f (b * g) * h (g⁻¹ * x) ∂μ = - conv μ f h x := by
    have := integral_mul_left_eq_self (μ := μ) (fun g => f g * h (g⁻¹ * b * x)) b
    simp only [mul_inv_rev, inv_mul_cancel_right] at this
    rw [this, conv, ← integral_neg]
    congr 1
    ext g
    rw [hneg]; ring
  have hfb : Integrable (fun g => f (b * g)) μ := hf.comp_mul_left b
  have hmeas : AEStronglyMeasurable (fun g => h (g⁻¹ * x)) μ :=
    (hcont.comp (continuous_inv.mul continuous_const)).aestronglyMeasurable
  have i1 : Integrable (fun g => f (b * g) * h (g⁻¹ * x)) μ :=
    hfb.mul_bdd hmeas (Eventually.of_forall fun g => hbd _)
  have i2 : Integrable (fun g => f g * h (g⁻¹ * x)) μ :=
    hf.mul_bdd hmeas (Eventually.of_forall fun g => hbd _)
  have h2 : ∫ g, (f (b * g) - f g) * h (g⁻¹ * x) ∂μ = -2 * conv μ f h x := by
    simp only [sub_mul]
    rw [integral_sub i1 i2, h1, conv]; ring
  have hC : 0 ≤ C := (norm_nonneg _).trans (hbd 1)
  have h3 : ‖∫ g, (f (b * g) - f g) * h (g⁻¹ * x) ∂μ‖ ≤ C := by
    calc _ ≤ ∫ g, ‖f (b * g) - f g‖ * C ∂μ := by
          apply norm_integral_le_of_norm_le ((hfb.sub hf).norm.mul_const C)
          refine Eventually.of_forall fun g => ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hbd _) (norm_nonneg _)
      _ = (∫ g, ‖f (b * g) - f g‖ ∂μ) * C := integral_mul_const _ _
      _ ≤ 1 * C := mul_le_mul_of_nonneg_right hb hC
      _ = C := one_mul C
  rw [h2, norm_mul] at h3
  simp at h3
  linarith
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.KillsOfIdem

section

@[expose] public section

open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

theorem UpperTheory.Lit.Cusp.kills_of_idem :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (N : Set G) (a : ℝ → G) (H : G → ℝ) (e : G → ℂ),
      IsRay N a H → Continuous e → Integrable e μ → (∀ x, conv μ e e x = e x) → Kills μ N a e := by
  intro G _ _ _ _ _ _ _ _ μ _ N a H e hR hc hi hid
  have step1 : ∀ s, OpLe μ N a e s (1 / 2) → OpLe μ N a e s 0 := by
    intro s hs
    have hk : ∀ k : ℕ, OpLe μ N a e s ((1 / 2) ^ (k + 1)) := by
      intro k
      induction k with
      | zero => simpa using hs
      | succ k ih =>
        intro C h hh x
        have h1 := conv_isEig G μ N a e h s C hi hh
        have h2 : IsEig N a s (1 / 2 * C) (conv μ e h) := ⟨h1.1, hs C h hh, h1.2.2.1, h1.2.2.2⟩
        have h3 := ih _ _ h2 x
        rw [← conv_assoc G μ e e h C hc hi hc hi hh.1 hh.2.1 hid x] at h3
        calc _ ≤ _ := h3
          _ = _ := by ring
    intro C h hh x
    have ht : Tendsto (fun k : ℕ => ((1 / 2 : ℝ) ^ (k + 1)) * C) atTop (𝓝 (0 * C)) :=
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
        (tendsto_add_atTop_nat 1)).mul_const C
    exact ge_of_tendsto' ht (fun k => hk k C h hh x)
  obtain ⟨δ, hδ, hnear⟩ := opLe_near G μ N a H e hR hi (1 / 2) (by norm_num)
  have step2 : ∀ s s', |s - s'| < δ → OpLe μ N a e s 0 → OpLe μ N a e s' 0 := by
    intro s s' hss hs
    have := hnear s s' 0 hss hs
    rw [zero_add] at this
    exact step1 s' this
  obtain ⟨s₀, hs₀⟩ := opLe_half G μ N a H e hR hi
  have h0 := step1 s₀ hs₀
  have step3 : ∀ n : ℕ, ∀ s, |s - s₀| ≤ n * (δ / 2) → OpLe μ N a e s 0 := by
    intro n
    induction n with
    | zero =>
      intro s hs
      have : s = s₀ := by
        have : |s - s₀| ≤ 0 := by simpa using hs
        linarith [abs_nonpos_iff.mp this]
      rw [this]; exact h0
    | succ n ih =>
      intro s hs
      have hn : (0 : ℝ) ≤ n * (δ / 2) := by positivity
      push_cast at hs
      rw [abs_le] at hs
      by_cases h1 : |s - s₀| ≤ n * (δ / 2)
      · exact ih s h1
      · rcases le_total s s₀ with h2 | h2
        · refine step2 (s₀ - n * (δ / 2)) s ?_ (ih _ ?_)
          · rw [abs_of_nonpos (by linarith), not_le] at h1
            rw [abs_lt]; constructor <;> nlinarith
          · rw [abs_le]; constructor <;> linarith
        · refine step2 (s₀ + n * (δ / 2)) s ?_ (ih _ ?_)
          · rw [abs_of_nonneg (by linarith), not_le] at h1
            rw [abs_lt]; constructor <;> nlinarith
          · rw [abs_le]; constructor <;> linarith
  intro s C h hh x
  obtain ⟨n, hn⟩ := exists_nat_ge (|s - s₀| / (δ / 2))
  rw [div_le_iff₀ (by positivity)] at hn
  have := step3 n s hn C h hh x
  rw [zero_mul] at this
  exact norm_le_zero_iff.mp this
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.Unfold

section

@[expose] public section

open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

theorem UpperTheory.Lit.Cusp.conv_average :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (N : Set G) (a : ℝ → G) (H : G → ℝ)
      (ν : Measure G) [IsFiniteMeasureOnCompacts ν], ν Nᶜ = 0 → (∀ m ∈ N, ν.map (fun x => m * x) = ν) →
      IsRay N a H → ∀ f ψ : G → ℂ, Continuous f → Integrable f μ → Continuous ψ → HasCompactSupport ψ → ∀ x,
        conv μ f (fun g => ∫ m, ψ (g * m) ∂ν) x = ∫ y, ψ y⁻¹ * ∫ m, f (x * m * y) ∂ν ∂μ := by
  intro G _ _ _ _ _ _ _ _ μ _ N a H ν _ hN hinv hray f ψ hf hfi hψ hψc x
  haveI : IsLocallyFiniteMeasure ν := inferInstance
  haveI : SigmaFinite ν := inferInstance
  have hn := isBand_of_compact G N a H ν hN hinv hray (fun g => ((‖ψ g‖ : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp hψ.norm)
    (hψc.comp_left (g := fun z : ℂ => ((‖z‖ : ℝ) : ℂ)) (by simp))
  have hb := isBand_of_compact G N a H ν hN hinv hray ψ hψ hψc
  obtain ⟨⟨-, ⟨C, hC⟩, -, -⟩, -⟩ := hn
  have hC' : ∀ g, ∫ m, ‖ψ (g * m)‖ ∂ν ≤ C := by
    intro g
    have h := hC g
    simp only [integral_complex_ofReal, Complex.norm_real, Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h
  have hc1 : Continuous (fun p : G × G => f p.1 * ψ (p.1⁻¹ * x * p.2)) := by fun_prop
  have h1 : Integrable (fun p : G × G => f p.1 * ψ (p.1⁻¹ * x * p.2)) (μ.prod ν) := by
    rw [integrable_prod_iff hc1.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun g => (hb.2 (g⁻¹ * x)).const_mul (f g), ?_⟩
    refine Integrable.mono' (hfi.norm.mul_const C)
      (hc1.norm.stronglyMeasurable.integral_prod_right' (ν := ν)).aestronglyMeasurable
      (Eventually.of_forall fun g => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    simp only [norm_mul]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hC' _) (norm_nonneg _)
  have h2 := (integrable_prod_iff h1.swap.aestronglyMeasurable).1 h1.swap
  have key : ∀ m y : G, (x * m * y)⁻¹ * x * m = y⁻¹ := by
    intro m y; group
  have hc3 : Continuous (fun p : G × G => ψ p.2⁻¹ * f (x * p.1 * p.2)) := by fun_prop
  have h3 : Integrable (fun p : G × G => ψ p.2⁻¹ * f (x * p.1 * p.2)) (ν.prod μ) := by
    rw [integrable_prod_iff hc3.aestronglyMeasurable]
    refine ⟨h2.1.mono fun m hm => ?_, h2.2.congr (Eventually.of_forall fun m => ?_)⟩
    · have := hm.comp_mul_left (x * m)
      simpa only [Function.comp, Prod.swap, key, mul_comm (f _)] using this
    · have := integral_mul_left_eq_self (μ := μ) (fun g => ‖f g * ψ (g⁻¹ * x * m)‖) (x * m)
      simp only [key, mul_comm (f (x * m * _))] at this
      simpa only [Function.comp, Prod.swap] using this.symm
  calc conv μ f (fun g => ∫ m, ψ (g * m) ∂ν) x
      = ∫ g, ∫ m, f g * ψ (g⁻¹ * x * m) ∂ν ∂μ := by
        simp only [conv, integral_const_mul]
    _ = ∫ m, ∫ g, f g * ψ (g⁻¹ * x * m) ∂μ ∂ν := integral_integral_swap h1
    _ = ∫ m, ∫ y, ψ y⁻¹ * f (x * m * y) ∂μ ∂ν := by
        refine integral_congr_ae (Eventually.of_forall fun m => ?_)
        have := integral_mul_left_eq_self (μ := μ) (fun g => f g * ψ (g⁻¹ * x * m)) (x * m)
        simp only [key, mul_comm (f (x * m * _))] at this
        exact this.symm
    _ = ∫ y, ∫ m, ψ y⁻¹ * f (x * m * y) ∂ν ∂μ := integral_integral_swap h3
    _ = ∫ y, ψ y⁻¹ * ∫ m, f (x * m * y) ∂ν ∂μ := by
        simp only [integral_const_mul]
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.Abstract

section

@[expose] public section

open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

theorem UpperTheory.Lit.Cusp.average_eq_zero :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (N : Set G) (a : ℝ → G) (H : G → ℝ)
      (ν : Measure G) [IsFiniteMeasureOnCompacts ν], ν Nᶜ = 0 → (∀ m ∈ N, ν.map (fun x => m * x) = ν) →
      IsRay N a H → ∀ e f : G → ℂ, Continuous e → Integrable e μ → Continuous f → Integrable f μ →
        (∀ x, conv μ e e x = e x) → (∀ x, conv μ e f x = f x) →
        ∀ x, (Continuous fun y => ∫ m, f (x * m * y) ∂ν) → ∀ y, ∫ m, f (x * m * y) ∂ν = 0 := by
  intro G _ _ _ _ _ _ _ _ μ _ N a H ν _ hν hinv hray e f hec hei hfc hfi hee hef x hcont
  have hKe : Kills μ N a e := kills_of_idem G μ N a H e hray hec hei hee
  have hKf : Kills μ N a f := by
    intro s C h hh z
    rw [conv_assoc G μ e f h C hec hei hfc hfi hh.1 hh.2.1 hef z]
    exact hKe s _ _ (conv_isEig G μ N a f h s C hfi hh) z
  refine eq_zero_of_test G μ (fun y => ∫ m, f (x * m * y) ∂ν) hcont ?_
  intro ψ hψ hψc
  rw [← conv_average G μ N a H ν hν hinv hray f ψ hfc hfi hψ hψc x]
  exact conv_band G μ N a H f _ hray hfc hfi hKf
    (isBand_of_compact G N a H ν hν hinv hray ψ hψ hψc).1 x
end
end
