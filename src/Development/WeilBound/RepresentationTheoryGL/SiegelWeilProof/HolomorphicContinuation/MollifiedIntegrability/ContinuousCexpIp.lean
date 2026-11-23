module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.MollId
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
import Mathlib.Tactic.Linter.Style

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ExpCombine

section

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace PositivityTheory.Rg.Sw.WR.D.Moll

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D

variable {n : ℕ} {X : Type} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

theorem exp_combine (t : ℝ) (y q β : E n) :
    Complex.exp (Complex.I * t * ip y q) * Complex.exp (-(Complex.I * t * ip β y)) =
      Complex.exp (Complex.I * t * ip y (q - β)) := by
  rw [ip_sub_right, ip_comm β y, ← Complex.exp_add]
  congr 1
  push_cast
  ring


theorem step_a (Ψ : X → ℂ) (qq : X → E n) (hΨ : Integrable Ψ μ) (hqq : Measurable qq) (t ε : ℝ) (hε : 0 < ε)
    (β : E n) :
    ∫ y, (∫ x, Ψ x * Complex.exp (Complex.I * t * ip y (qq x)) ∂μ) * gam ε y *
        Complex.exp (-(Complex.I * t * ip β y)) =
      ∫ x, Ψ x * kr ε t (qq x - β) ∂μ := by
  have hfun : ∀ (y : E n) (x : X), Ψ x * Complex.exp (Complex.I * t * ip y (qq x)) * gam ε y *
      Complex.exp (-(Complex.I * t * ip β y)) =
      Ψ x * (gam ε y * Complex.exp (Complex.I * t * ip y (qq x - β))) := by
    intro y x
    rw [← exp_combine]
    ring
  have hL : ∀ y : E n, (∫ x, Ψ x * Complex.exp (Complex.I * t * ip y (qq x)) ∂μ) * gam ε y *
      Complex.exp (-(Complex.I * t * ip β y)) =
      ∫ x, Ψ x * (gam ε y * Complex.exp (Complex.I * t * ip y (qq x - β))) ∂μ := by
    intro y
    rw [← integral_mul_const, ← integral_mul_const]
    exact integral_congr_ae (Eventually.of_forall fun x => hfun y x)
  have hm1 : Measurable fun p : E n × X => ip p.1 (qq p.2 - β) :=
    continuous_ip.measurable.comp (measurable_fst.prodMk ((hqq.comp measurable_snd).sub_const β))
  have hm2 : Measurable fun p : E n × X => Complex.exp (Complex.I * t * ip p.1 (qq p.2 - β)) :=
    ((Complex.measurable_ofReal.comp hm1).const_mul (Complex.I * t)).cexp
  have hint : Integrable (fun p : E n × X =>
      Ψ p.2 * (gam ε p.1 * Complex.exp (Complex.I * t * ip p.1 (qq p.2 - β))))
      ((volume : Measure (E n)).prod μ) := by
    refine Integrable.mono ((integrable_gauss (n := n) ε hε).mul_prod hΨ) ?_ ?_
    · exact (hΨ.1.comp_snd (μ := (volume : Measure (E n)))).mul
        ((((continuous_gam ε).measurable.comp measurable_fst).mul hm2).aestronglyMeasurable)
    · refine Eventually.of_forall fun p => ?_
      simp only [norm_mul, norm_cexp_It, mul_one]
      exact le_of_eq (mul_comm _ _)
  simp only [hL, kr, ← integral_const_mul]
  exact integral_integral_swap hint

end PositivityTheory.Rg.Sw.WR.D.Moll
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.StepB

section

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace PositivityTheory.Rg.Sw.WR.D.Moll

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D

variable {n : ℕ} {X : Type} [MeasurableSpace X] {μ : Measure X} [SFinite μ]


theorem step_b (Ψ : X → ℂ) (qq : X → E n) (hΨ : Integrable Ψ μ) (hqq : Measurable qq) (t ε : ℝ) (hε : 0 < ε)
    (ψ : E n → ℂ) (hψc : Continuous ψ) (hψi : Integrable ψ) (C : ℂ) :
    ∫ β, ψ β * (C * (∫ x, Ψ x * kr ε t (qq x - β) ∂μ)) =
      ∫ x, Ψ x * (∫ β, ψ β * (C * kr ε t (qq x - β))) ∂μ := by
  have hm : Measurable (fun p : E n × X => kr ε t (qq p.2 - p.1)) :=
    (continuous_kr ε t hε).measurable.comp ((hqq.comp measurable_snd).sub measurable_fst)
  have hs : AEStronglyMeasurable (fun p : E n × X => Ψ p.2) ((volume : Measure (E n)).prod μ) :=
    hΨ.aestronglyMeasurable.comp_snd
  have hψm : AEStronglyMeasurable (fun p : E n × X => ψ p.1) ((volume : Measure (E n)).prod μ) :=
    (hψc.measurable.comp measurable_fst).aestronglyMeasurable
  have hint : Integrable (fun p : E n × X => ψ p.1 * (C * (Ψ p.2 * kr ε t (qq p.2 - p.1))))
      ((volume : Measure (E n)).prod μ) := by
    refine Integrable.mono' ((hψi.norm.mul_prod hΨ.norm).mul_const (‖C‖ * ∫ y, ‖gam (n := n) ε y‖))
      (hψm.mul (aestronglyMeasurable_const.mul (hs.mul hm.aestronglyMeasurable))) ?_
    refine Eventually.of_forall fun p => ?_
    obtain ⟨β, x⟩ := p
    show ‖ψ β * (C * (Ψ x * kr ε t (qq x - β)))‖ ≤ ‖ψ β‖ * ‖Ψ x‖ * (‖C‖ * ∫ y, ‖gam (n := n) ε y‖)
    rw [norm_mul, norm_mul, norm_mul]
    have hk := norm_kr_le ε t hε (qq x - β)
    calc ‖ψ β‖ * (‖C‖ * (‖Ψ x‖ * ‖kr ε t (qq x - β)‖)) ≤
          ‖ψ β‖ * (‖C‖ * (‖Ψ x‖ * ∫ y, ‖gam (n := n) ε y‖)) := by gcongr
      _ = ‖ψ β‖ * ‖Ψ x‖ * (‖C‖ * ∫ y, ‖gam (n := n) ε y‖) := by ring
  have e1 : (fun β : E n => ψ β * (C * (∫ x, Ψ x * kr ε t (qq x - β) ∂μ))) =
      fun β => ∫ x, ψ β * (C * (Ψ x * kr ε t (qq x - β))) ∂μ := by
    funext β
    rw [← integral_const_mul, ← integral_const_mul]
  have e2 : (fun x : X => ∫ β : E n, ψ β * (C * (Ψ x * kr ε t (qq x - β)))) =
      fun x => Ψ x * (∫ β, ψ β * (C * kr ε t (qq x - β))) := by
    funext x
    rw [← integral_const_mul]
    congr 1
    funext β
    ring
  rw [e1, integral_integral_swap (f := fun (β : E n) (x : X) => ψ β * (C * (Ψ x * kr ε t (qq x - β)))) hint, e2]

end PositivityTheory.Rg.Sw.WR.D.Moll
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.StepC

section

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace PositivityTheory.Rg.Sw.WR.D.Moll

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D

variable {n : ℕ} {X : Type} [MeasurableSpace X] {μ : Measure X} [SFinite μ]


theorem step_c (ψ : E n → ℂ) (t ε : ℝ) (ht : t ≠ 0) (hε : 0 < ε) (w : E n) :
    ∫ β, ψ β * ((((|t| / (2 * Real.pi)) ^ (n ^ 2) : ℝ) : ℂ) * kr ε t (w - β)) =
      mM ψ (|t| / (2 * Real.sqrt ε)) w := by
  have hlpos : 0 < |t| / (2 * Real.sqrt ε) := div_pos (abs_pos.2 ht) (by have := Real.sqrt_pos.2 hε; positivity)
  set l := |t| / (2 * Real.sqrt ε) with hl
  have hk : ∀ u : E n, (((|t| / (2 * Real.pi)) ^ (n ^ 2) : ℝ) : ℂ) * kr ε t u =
      (((l ^ (n ^ 2) * gK (l • u)) : ℝ) : ℂ) := fun u => kraw_eq ε hε t ht u
  simp_rw [hk]
  have h1 : ∫ β, ψ β * (((l ^ (n ^ 2) * gK (l • (w - β))) : ℝ) : ℂ) =
      ∫ u, ψ (w - u) * (((l ^ (n ^ 2) * gK (l • u)) : ℝ) : ℂ) := by
    have := integral_sub_left_eq_self (μ := (volume : Measure (E n)))
      (fun u => ψ (w - u) * (((l ^ (n ^ 2) * gK (l • u)) : ℝ) : ℂ)) w
    simpa only [sub_sub_cancel] using this
  rw [h1]
  have h2 := Measure.integral_comp_smul (μ := (volume : Measure (E n))) (fun v : E n => ψ (w - l⁻¹ • v) * (gK v : ℂ)) l
  simp only [inv_smul_smul₀ hlpos.ne'] at h2
  rw [finrank_E] at h2
  unfold mM
  calc ∫ u, ψ (w - u) * (((l ^ (n ^ 2) * gK (l • u)) : ℝ) : ℂ)
      = ((l ^ (n ^ 2) : ℝ) : ℂ) * ∫ u, ψ (w - u) * (gK (l • u) : ℂ) := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        simp only
        push_cast
        ring
    _ = ((l ^ (n ^ 2) : ℝ) : ℂ) * (|(l ^ (n ^ 2))⁻¹| • ∫ v, ψ (w - l⁻¹ • v) * (gK v : ℂ)) := by rw [h2]
    _ = ∫ v, ψ (w - l⁻¹ • v) * (gK v : ℂ) := by
        rw [abs_of_pos (by positivity), Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
          mul_inv_cancel₀ (pow_pos hlpos _).ne', Complex.ofReal_one, one_mul]

end PositivityTheory.Rg.Sw.WR.D.Moll
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ContinuousCexpIp

section

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace PositivityTheory.Rg.Sw.WR.D.Moll

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D

variable {n : ℕ} {X : Type} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

theorem continuous_cexp_ip (t : ℝ) : Continuous (fun p : E n × E n => Complex.exp (-(Complex.I * t * ip p.1 p.2))) :=
  Complex.continuous_exp.comp ((continuous_const.mul (Complex.continuous_ofReal.comp continuous_ip)).neg)


theorem lim_one (ρ : E n → ℂ) (hρ : Integrable ρ) (t : ℝ) (ψ : E n → ℂ) (hψc : Continuous ψ) (hψi : Integrable ψ)
    (C : ℂ) (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) (hε0 : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun k => ∫ β, ψ β * (C * ∫ y, ρ y * gam (ε k) y * Complex.exp (-(Complex.I * t * ip β y))))
      atTop (𝓝 (∫ β, ψ β * (C * ∫ y, ρ y * Complex.exp (-(Complex.I * t * ip β y))))) := by
  have hexp := continuous_cexp_ip (n := n) t
  have hbd : ∀ k y β, ‖ρ y * gam (ε k) y * Complex.exp (-(Complex.I * t * ip β y))‖ ≤ ‖ρ y‖ := by
    intro k y β
    rw [norm_mul, norm_mul, norm_cexp_neg_It, mul_one]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_gauss_le _ (hε k) y)
  have hcont : ∀ k, Continuous (fun β : E n => ∫ y, ρ y * gam (ε k) y * Complex.exp (-(Complex.I * t * ip β y))) := by
    intro k
    refine continuous_of_dominated (bound := fun y => ‖ρ y‖) ?_ ?_ hρ.norm ?_
    · intro β
      exact (hρ.aestronglyMeasurable.mul (continuous_gam (ε k)).aestronglyMeasurable).mul
        (hexp.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    · intro β; exact Eventually.of_forall fun y => hbd k y β
    · exact Eventually.of_forall fun y => by
        have hip : Continuous (fun β : E n => ip β y) := by
          unfold ip
          fun_prop
        have hy : Continuous (fun β : E n => Complex.exp (-(Complex.I * t * ip β y))) :=
          Complex.continuous_exp.comp ((continuous_const.mul (Complex.continuous_ofReal.comp hip)).neg)
        exact continuous_const.mul hy
  have hin : ∀ β : E n, Tendsto (fun k => ∫ y, ρ y * gam (ε k) y * Complex.exp (-(Complex.I * t * ip β y)))
      atTop (𝓝 (∫ y, ρ y * Complex.exp (-(Complex.I * t * ip β y)))) := by
    intro β
    refine tendsto_integral_of_dominated_convergence (fun y => ‖ρ y‖) ?_ hρ.norm ?_ ?_
    · intro k
      exact (hρ.aestronglyMeasurable.mul (continuous_gam (ε k)).aestronglyMeasurable).mul
        (hexp.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    · intro k; exact Eventually.of_forall fun y => hbd k y β
    · refine Eventually.of_forall fun y => ?_
      have h0 : Tendsto (fun k => -(((ε k * ip y y : ℝ)) : ℂ)) atTop (𝓝 0) := by
        have h := hε0.mul_const (ip y y)
        rw [zero_mul] at h
        have h' := ((Complex.continuous_ofReal.tendsto 0).comp h).neg
        simpa [Function.comp_def] using h'
      have hg : Tendsto (fun k => gam (ε k) y) atTop (𝓝 1) := by
        have := (Complex.continuous_exp.tendsto 0).comp h0
        simpa [gam, Function.comp_def] using this
      have := ((tendsto_const_nhds (x := ρ y)).mul hg).mul
        (tendsto_const_nhds (x := Complex.exp (-(Complex.I * t * ip β y))))
      simpa using this
  refine tendsto_integral_of_dominated_convergence (fun β => ‖ψ β‖ * (‖C‖ * ∫ y, ‖ρ y‖)) ?_
    (hψi.norm.mul_const _) ?_ ?_
  · intro k
    exact (hψc.mul (continuous_const.mul (hcont k))).aestronglyMeasurable
  · intro k; refine Eventually.of_forall fun β => ?_
    rw [norm_mul, norm_mul]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)) (norm_nonneg _)
    exact norm_integral_le_of_norm_le hρ.norm (Eventually.of_forall fun y => hbd k y β)
  · exact Eventually.of_forall fun β => tendsto_const_nhds.mul (tendsto_const_nhds.mul (hin β))


theorem lim_two (Ψ : X → ℂ) (qq : X → E n) (hΨ : Integrable Ψ μ) (hqq : Measurable qq) (ψ : E n → ℂ)
    (hψc : Continuous ψ) (B : ℝ) (hB : ∀ x, ‖ψ x‖ ≤ B) (l : ℕ → ℝ) (hl : Tendsto (fun k => (l k)⁻¹) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, Ψ x * mM ψ (l k) (qq x) ∂μ) atTop (𝓝 (∫ x, ψ (qq x) * Ψ x ∂μ)) := by
  have hlim : ∫ x, ψ (qq x) * Ψ x ∂μ = ∫ x, Ψ x * ψ (qq x) ∂μ := by simp_rw [mul_comm]
  rw [hlim]
  refine tendsto_integral_of_dominated_convergence (fun x => ‖Ψ x‖ * B) ?_ (hΨ.norm.mul_const _) ?_ ?_
  · intro k
    exact hΨ.aestronglyMeasurable.mul ((continuous_mM ψ B hB hψc (l k)).measurable.comp hqq).aestronglyMeasurable
  · intro k; refine Eventually.of_forall fun x => ?_
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left (norm_mM_le ψ B hB hψc _ _) (norm_nonneg _)
  · exact Eventually.of_forall fun x => tendsto_const_nhds.mul (tendsto_mM ψ B hB hψc l hl (qq x))


theorem eq_A (Ψ : X → ℂ) (qq : X → E n) (hΨ : Integrable Ψ μ) (hqq : Measurable qq) (t : ℝ) (ht : t ≠ 0)
    (ψ : E n → ℂ) (hψc : Continuous ψ) (hψi : Integrable ψ) (ε : ℝ) (hε : 0 < ε) :
    ∫ β, ψ β * ((((|t| / (2 * Real.pi)) ^ (n ^ 2) : ℝ) : ℂ) *
        ∫ y, (∫ x, Ψ x * Complex.exp (Complex.I * t * ip y (qq x)) ∂μ) * gam ε y *
          Complex.exp (-(Complex.I * t * ip β y))) =
      ∫ x, Ψ x * mM ψ (|t| / (2 * Real.sqrt ε)) (qq x) ∂μ := by
  have ha : ∀ β : E n, ∫ y, (∫ x, Ψ x * Complex.exp (Complex.I * t * ip y (qq x)) ∂μ) * gam ε y *
      Complex.exp (-(Complex.I * t * ip β y)) = ∫ x, Ψ x * kr ε t (qq x - β) ∂μ :=
    fun β => step_a Ψ qq hΨ hqq t ε hε β
  simp_rw [ha]
  rw [step_b Ψ qq hΨ hqq t ε hε ψ hψc hψi]
  congr 1
  funext x
  rw [step_c ψ t ε ht hε (qq x)]

theorem _root_.PositivityTheory.Rg.Sw.WR.D.mollId : MollId := by
  intro n X _ μ _ Ψ qq hΨ hqq t ht hρ ψ hψc hψs
  obtain ⟨B, hB⟩ := hψc.bounded_above_of_compact_support hψs
  have hψi : Integrable ψ := hψc.integrable_of_hasCompactSupport hψs
  have hε : ∀ k : ℕ, 0 < 1 / ((k : ℝ) + 1) := fun k => by positivity
  have hε0 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hl : Tendsto (fun k : ℕ => (|t| / (2 * Real.sqrt (1 / ((k : ℝ) + 1))))⁻¹) atTop (𝓝 0) := by
    have e : (fun k : ℕ => (|t| / (2 * Real.sqrt (1 / ((k : ℝ) + 1))))⁻¹) =
        fun k : ℕ => (2 / |t|) * Real.sqrt (1 / ((k : ℝ) + 1)) := by
      funext k; rw [inv_div]; ring
    rw [e]
    have h := ((Real.continuous_sqrt.tendsto 0).comp hε0).const_mul (2 / |t|)
    simpa [Real.sqrt_zero, Function.comp_def] using h
  have h1 := lim_one _ hρ t ψ hψc hψi ((((|t| / (2 * Real.pi)) ^ (n ^ 2) : ℝ) : ℂ)) _ hε hε0
  have h2 := lim_two Ψ qq hΨ hqq ψ hψc B hB _ hl
  have e : (fun k : ℕ => ∫ β, ψ β * ((((|t| / (2 * Real.pi)) ^ (n ^ 2) : ℝ) : ℂ) *
        ∫ y, (∫ x, Ψ x * Complex.exp (Complex.I * t * ip y (qq x)) ∂μ) * gam (1 / ((k : ℝ) + 1)) y *
          Complex.exp (-(Complex.I * t * ip β y)))) =
      fun k : ℕ => ∫ x, Ψ x * mM ψ (|t| / (2 * Real.sqrt (1 / ((k : ℝ) + 1)))) (qq x) ∂μ := by
    funext k
    exact eq_A Ψ qq hΨ hqq t ht ψ hψc hψi _ (hε k)
  rw [e] at h1
  exact tendsto_nhds_unique h2 h1

end PositivityTheory.Rg.Sw.WR.D.Moll
end
end
end
