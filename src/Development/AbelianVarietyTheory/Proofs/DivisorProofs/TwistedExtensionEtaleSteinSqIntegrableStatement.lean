module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutoffHoloSmoothDbarFormulaStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothLogTwistInequalities
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviFormTwistedWeightLowerBoundStatement
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.TsupportDbSubset
public import ReciprocityTheory.L2DbarEstimates.Localization.Choice
public import ReciprocityTheory.L2DbarEstimates.NormFibrations.Hormander

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothLogTwistInequalitiesStatement

section

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.exists_smooth_log_twist_inequalities : ∀ T : ℝ, 300 ≤ T → ∃ κ : ℝ → ℝ, ContDiff ℝ ∞ κ ∧ (∃ C : ℝ, ∀ x, x ≤ 0 → |κ x| ≤ C) ∧ (∀ x, x ≤ 0 → 0 ≤ deriv κ x ∧ deriv κ x ≤ 1 ∧ 0 < deriv (deriv κ) x ∧ deriv κ x ^ 2 ≤ deriv (deriv κ) x ∧ wT T x / 8 ≤ (1 - deriv κ x ^ 2 / deriv (deriv κ) x) * Real.exp (κ x)) ∧ (∀ x, -T - 1 ≤ x → x ≤ -T + 1 → Real.exp (κ x) / deriv (deriv κ) x ≤ 16 / 3 ∧ wT T x / 8 ≤ (1 - 5 * (deriv κ x ^ 2 / deriv (deriv κ) x)) * Real.exp (κ x)) := by
  first | exact @GlobalTheory.OTY.exists_log_twist | exact GlobalTheory.OTY.exists_log_twist | (intros; apply GlobalTheory.OTY.exists_log_twist <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointwiseAbsorptionTwisted

section

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem pointwise_absorption_twisted :
    ∀ (T x u g t k1 k2 E : ℝ), 0 ≤ u → 0 ≤ g → 0 < k2 → 0 < E → |t| ≤ 3 / 4 →
      wT T x / 8 ≤ (1 - k1 ^ 2 / k2) * E →
      ((-T - 1 ≤ x ∧ x ≤ -T + 1) → E / k2 ≤ 16 / 3 ∧ wT T x / 8 ≤ (1 - 5 * (k1 ^ 2 / k2)) * E) →
      (¬ (-T - 1 ≤ x ∧ x ≤ -T + 1) → t = 0) →
      (Real.sqrt (t ^ 2 * g ^ 2 / k2) + u * Real.sqrt (k1 ^ 2 / k2)) ^ 2 * E + u ^ 2 * (wT T x / 8)
        ≤ u ^ 2 * E + (if (-T - 1 ≤ x ∧ x ≤ -T + 1) then 15 / 4 * g ^ 2 else 0) := by
  intro T x u g t k1 k2 E hu hg hk2 hE ht hw hwin hoff
  have ha : 0 ≤ t ^ 2 * g ^ 2 / k2 := by positivity
  have hb : 0 ≤ k1 ^ 2 / k2 := by positivity
  have hA := Real.sq_sqrt ha
  have hB := Real.sq_sqrt hb
  have hA0 := Real.sqrt_nonneg (t ^ 2 * g ^ 2 / k2)
  have hB0 := Real.sqrt_nonneg (k1 ^ 2 / k2)
  by_cases h : (-T - 1 ≤ x ∧ x ≤ -T + 1)
  · rw [if_pos h]
    obtain ⟨h1, h2⟩ := hwin h
    have ht2 : t ^ 2 ≤ 9 / 16 := by
      have h0 : 0 ≤ |t| := abs_nonneg t
      have : |t| ^ 2 ≤ (3 / 4) ^ 2 := by nlinarith
      rw [sq_abs] at this
      linarith
    have haE : t ^ 2 * g ^ 2 / k2 * E ≤ 3 * g ^ 2 := by
      have e : t ^ 2 * g ^ 2 / k2 * E = t ^ 2 * g ^ 2 * (E / k2) := by ring
      rw [e]
      calc t ^ 2 * g ^ 2 * (E / k2) ≤ (9 / 16) * g ^ 2 * (16 / 3) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_right ht2 (sq_nonneg g)) h1
              (by positivity) (by positivity)
        _ = 3 * g ^ 2 := by ring
    have key : (Real.sqrt (t ^ 2 * g ^ 2 / k2) + u * Real.sqrt (k1 ^ 2 / k2)) ^ 2
        ≤ 5 / 4 * (t ^ 2 * g ^ 2 / k2) + 5 * (k1 ^ 2 / k2) * u ^ 2 := by
      nlinarith [sq_nonneg (Real.sqrt (t ^ 2 * g ^ 2 / k2) / 2 - 2 * u * Real.sqrt (k1 ^ 2 / k2))]
    have k1' := mul_le_mul_of_nonneg_right key hE.le
    have k2' := mul_le_mul_of_nonneg_left h2 (sq_nonneg u)
    nlinarith
  · rw [if_neg h]
    have t0 := hoff h
    subst t0
    have z : Real.sqrt ((0:ℝ) ^ 2 * g ^ 2 / k2) = 0 := by simp
    rw [z]
    have k2' := mul_le_mul_of_nonneg_left hw (sq_nonneg u)
    have e : (0 + u * Real.sqrt (k1 ^ 2 / k2)) ^ 2 * E = u ^ 2 * (k1 ^ 2 / k2) * E := by
      rw [zero_add, mul_pow, hB]
    rw [e]
    nlinarith

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointwiseAbsorptionTwistedStatement

section

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.sq_sqrt_add_mul_le_of_twisted_absorption : ∀ (T x u g t k1 k2 E : ℝ), 0 ≤ u → 0 ≤ g → 0 < k2 → 0 < E → |t| ≤ 3 / 4 → wT T x / 8 ≤ (1 - k1 ^ 2 / k2) * E → ((-T - 1 ≤ x ∧ x ≤ -T + 1) → E / k2 ≤ 16 / 3 ∧ wT T x / 8 ≤ (1 - 5 * (k1 ^ 2 / k2)) * E) → (¬ (-T - 1 ≤ x ∧ x ≤ -T + 1) → t = 0) → (Real.sqrt (t ^ 2 * g ^ 2 / k2) + u * Real.sqrt (k1 ^ 2 / k2)) ^ 2 * E + u ^ 2 * (wT T x / 8) ≤ u ^ 2 * E + (if (-T - 1 ≤ x ∧ x ≤ -T + 1) then 15 / 4 * g ^ 2 else 0) := by
  first | exact @GlobalTheory.pointwise_absorption_twisted | exact GlobalTheory.pointwise_absorption_twisted | (intros; apply GlobalTheory.pointwise_absorption_twisted <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedExtensionEtaleSteinSqIntegrable

section

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem twEst_cancel {M : Type} [MeasurableSpace M] (μ : Measure M) (A B W S : M → ℝ≥0∞)
    (hS : Measurable S) (hpt : ∀ x, A x + W x ≤ B x + S x)
    (hBA : ∫⁻ x, B x ∂μ ≤ ∫⁻ x, A x ∂μ) (hB : ∫⁻ x, B x ∂μ ≠ ⊤) :
    ∫⁻ x, W x ∂μ ≤ ∫⁻ x, S x ∂μ := by
  have h1 : ∫⁻ x, A x ∂μ + ∫⁻ x, W x ∂μ ≤ ∫⁻ x, B x ∂μ + ∫⁻ x, S x ∂μ :=
    (le_lintegral_add A W).trans ((lintegral_mono hpt).trans_eq (lintegral_add_right _ hS))
  have h2 : ∫⁻ x, B x ∂μ + ∫⁻ x, W x ∂μ ≤ ∫⁻ x, B x ∂μ + ∫⁻ x, S x ∂μ :=
    (add_le_add hBA le_rfl).trans h1
  exact (ENNReal.add_le_add_iff_left hB).1 h2

theorem twEst_deriv_cut_zero (T : ℝ) (θ : ℝ → ℝ) (hθ : IsCut T θ) (s : ℝ)
    (hs : ¬ (-T - 1 ≤ s ∧ s ≤ -T + 1)) : deriv θ s = 0 := by
  obtain ⟨_, hθ1, hθ0, _, _⟩ := hθ
  rcases not_and_or.1 hs with h | h
  · push_neg at h
    have he : θ =ᶠ[𝓝 s] fun _ => (1 : ℝ) := by
      filter_upwards [Iio_mem_nhds h] with y hy using hθ1 y (le_of_lt hy)
    rw [he.deriv_eq]; simp
  · push_neg at h
    have he : θ =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
      filter_upwards [Ioi_mem_nhds h] with y hy using hθ0 y (le_of_lt hy)
    rw [he.deriv_eq]; simp

theorem twistedExtension_sqInt : ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M], ∀ (X : EtaleStein n M) (φ ψ : M → ℝ) (G : M → ℂ) (Ω : Set M) (δ T : ℝ) (θ : ℝ → ℝ), SmoothR n X.z φ → SmoothR n X.z ψ → (∀ x, ψ x ≤ 0) → 0 < δ → 300 ≤ T → IsCut T θ → (∀ α ∈ Set.Icc (1 : ℝ) (1 + δ), LeviNonneg n X.z (fun x => φ x + α * ψ x)) → IsOpen Ω → Measurable G → (∀ e : OpenPartialHomeomorph M (V n), IsChart n X.z e → DifferentiableOn ℂ (G ∘ e.symm) (e.target ∩ e.symm ⁻¹' Ω)) → (∀ x, δ * ψ x ≤ -T + 1 → x ∈ Ω) → wint n X.z (fun x => (θ (δ * ψ x) : ℂ) * G x) (fun x => φ x + ψ x) < ⊤ → ∃ F : M → ℂ, Holo n X.z F ∧ ∫⁻ x, ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ^ 2 * (wT T (δ * ψ x) * Real.exp (-(φ x + ψ x)))) ∂vol n X.z ≤ 30 * ∫⁻ x in {x | -T - 1 ≤ δ * ψ x ∧ δ * ψ x ≤ -T + 1}, ENNReal.ofReal (‖G x‖ ^ 2 * Real.exp (-(φ x + ψ x))) ∂vol n X.z := by
  intro n M _ _ _ _ _ X φ ψ G Ω δ T θ hφ hψ hψ0 hδ hT hθ hlevi hΩ hG hGh hΩsub hint
  have hz := X.isLocalHomeomorph
  obtain ⟨κ, hκ, ⟨C, hC⟩, hκ1, hκ2⟩ := GlobalTheory.T.exists_smooth_log_twist_inequalities T hT
  have hθ' := hθ
  obtain ⟨hθs, hθ1, hθ0, hθb, hθd⟩ := hθ'
  have hδψ : ∀ x, δ * ψ x ≤ 0 := fun x => mul_nonpos_of_nonneg_of_nonpos hδ.le (hψ0 x)
  have hk2 : ∀ x, 0 < deriv (deriv κ) (δ * ψ x) := fun x => (hκ1 _ (hδψ x)).2.2.1
  have h6 := GlobalTheory.T.leviForm_twisted_weight_lower_bound n M X.z φ ψ δ κ hz hφ hψ hψ0 hδ hκ
    (fun t ht => ⟨(hκ1 t ht).1, (hκ1 t ht).2.1⟩) hlevi
  have h7 := GlobalTheory.T.cutoff_holo_smooth_dbar_formula n M X ψ G Ω δ (-T + 1) θ hψ hθs (fun t ht => hθ0 t ht) hΩ hGh hΩsub
  have hψc : Continuous ψ := ReciprocityTheory.L2DbarEstimates.F.smoothReal_continuous n X.z hz ψ hψ
  have hφc : Continuous φ := ReciprocityTheory.L2DbarEstimates.F.smoothReal_continuous n X.z hz φ hφ
  have hψm : Measurable ψ := hψc.measurable
  have hφm : Measurable φ := hφc.measurable
  have hθm : Measurable θ := hθs.continuous.measurable
  have hdθ : Measurable (deriv θ) := measurable_deriv θ
  have hdk : Measurable (deriv (deriv κ)) := measurable_deriv _
  have hdk1 : Measurable (deriv κ) := measurable_deriv _
  have hκm : Measurable κ := hκ.continuous.measurable
  have hLevi : ∀ x ξ, deriv (deriv κ) (δ * ψ x) *
      (δ ^ 2 * ‖dbarDot n X.z (fun y => (ψ y : ℂ)) x ξ‖ ^ 2) ≤
      (Levi n X.z (fun y => (φ y + ψ y) + κ (δ * ψ y)) x ξ).re := fun x ξ => (h6.2 x ξ).2
  have hLnn : ∀ x ξ, 0 ≤ (Levi n X.z (fun y => (φ y + ψ y) + κ (δ * ψ y)) x ξ).re := by
    intro x ξ
    exact le_trans (mul_nonneg (hk2 x).le (by positivity)) (hLevi x ξ)
  obtain ⟨⟨F, hF⟩, hbd⟩ := ReciprocityTheory.L2DbarEstimates.tw n M X (fun x => φ x + ψ x) (fun x => κ (δ * ψ x))
    (fun x => (θ (δ * ψ x) : ℂ) * G x)
    (fun x => deriv θ (δ * ψ x) ^ 2 * ‖G x‖ ^ 2 / deriv (deriv κ) (δ * ψ x))
    (fun x => deriv κ (δ * ψ x) ^ 2 / deriv (deriv κ) (δ * ψ x))
    (SmoothR.add n X.z φ ψ hφ hψ) h6.1 ⟨C, fun x => hC _ (hδψ x)⟩ hLnn h7.1 hint
    (by fun_prop) (by fun_prop)
    (fun x => div_nonneg (by positivity) (hk2 x).le)
    (fun x => div_nonneg (by positivity) (hk2 x).le)
    (fun x => (div_le_one (hk2 x)).2 (hκ1 _ (hδψ x)).2.2.2.1)
    (by
      intro x ξ
      rw [(h7.2 x ξ)]
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc (|deriv θ (δ * ψ x)| * |δ| * ‖G x‖ * ‖dbarDot n X.z (fun y => (ψ y : ℂ)) x ξ‖) ^ 2
          = deriv θ (δ * ψ x) ^ 2 * ‖G x‖ ^ 2 / deriv (deriv κ) (δ * ψ x) *
            (deriv (deriv κ) (δ * ψ x) *
              (δ ^ 2 * ‖dbarDot n X.z (fun y => (ψ y : ℂ)) x ξ‖ ^ 2)) := by
            simp only [mul_pow, sq_abs]
            field_simp [(hk2 x).ne']
        _ ≤ _ := mul_le_mul_of_nonneg_left (hLevi x ξ) (div_nonneg (by positivity) (hk2 x).le))
    (by
      intro x ξ
      rw [(h6.2 x ξ).1]
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc (|deriv κ (δ * ψ x)| * |δ| * ‖dbarDot n X.z (fun y => (ψ y : ℂ)) x ξ‖) ^ 2
          = deriv κ (δ * ψ x) ^ 2 / deriv (deriv κ) (δ * ψ x) *
            (deriv (deriv κ) (δ * ψ x) *
              (δ ^ 2 * ‖dbarDot n X.z (fun y => (ψ y : ℂ)) x ξ‖ ^ 2)) := by
            simp only [mul_pow, sq_abs]
            field_simp [(hk2 x).ne']
        _ ≤ _ := mul_le_mul_of_nonneg_left (hLevi x ξ) (div_nonneg (by positivity) (hk2 x).le))
  refine ⟨F, hF.1, ?_⟩
  have hB := hbd F hF
  beta_reduce at hB
  have hsh : MeasurableSet {x | -T - 1 ≤ δ * ψ x ∧ δ * ψ x ≤ -T + 1} := by
    have h1 : Measurable (fun x => δ * ψ x) := by fun_prop
    exact (measurableSet_le measurable_const h1).inter (measurableSet_le h1 measurable_const)
  have hw : ∀ s, 0 ≤ wT T s := fun s => by unfold wT; positivity
  have hfin : ∫⁻ x, ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ^ 2 *
      Real.exp (κ (δ * ψ x) - (φ x + ψ x))) ∂vol n X.z ≠ ⊤ := by
    have hF0 : ∫⁻ x, ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x‖ ^ 2 *
        Real.exp (-(φ x + ψ x))) ∂vol n X.z < ⊤ := hint
    have hF1 : ∫⁻ x, ENNReal.ofReal (‖F x‖ ^ 2 * Real.exp (-(φ x + ψ x))) ∂vol n X.z < ⊤ :=
      hF.2.1
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono (g := fun x =>
      ENNReal.ofReal (2 * Real.exp C) *
        (ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x‖ ^ 2 * Real.exp (-(φ x + ψ x))) +
          ENNReal.ofReal (‖F x‖ ^ 2 * Real.exp (-(φ x + ψ x))))) ?_) ?_)
    · intro x
      beta_reduce
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hu : ‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ^ 2 ≤
          2 * (‖(θ (δ * ψ x) : ℂ) * G x‖ ^ 2 + ‖F x‖ ^ 2) := by
        have h0 := norm_sub_le ((θ (δ * ψ x) : ℂ) * G x) (F x)
        have h1 := pow_le_pow_left₀ (norm_nonneg _) h0 2
        nlinarith [sq_nonneg (‖(θ (δ * ψ x) : ℂ) * G x‖ - ‖F x‖)]
      have hk : Real.exp (κ (δ * ψ x)) ≤ Real.exp C :=
        Real.exp_le_exp.2 (le_trans (le_abs_self _) (hC _ (hδψ x)))
      have he : Real.exp (κ (δ * ψ x) - (φ x + ψ x)) =
          Real.exp (κ (δ * ψ x)) * Real.exp (-(φ x + ψ x)) := by
        rw [sub_eq_add_neg, Real.exp_add]
      rw [he]
      have hpos := Real.exp_pos (-(φ x + ψ x))
      calc ‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ^ 2 *
            (Real.exp (κ (δ * ψ x)) * Real.exp (-(φ x + ψ x)))
          ≤ (2 * (‖(θ (δ * ψ x) : ℂ) * G x‖ ^ 2 + ‖F x‖ ^ 2)) *
            (Real.exp C * Real.exp (-(φ x + ψ x))) :=
            mul_le_mul hu (mul_le_mul_of_nonneg_right hk hpos.le) (by positivity) (by positivity)
        _ = _ := by ring
    · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left (by fun_prop)]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.2 ⟨hF0, hF1⟩)
  have hcan := twEst_cancel (vol n X.z)
    (fun x => ENNReal.ofReal ((Real.sqrt (deriv θ (δ * ψ x) ^ 2 * ‖G x‖ ^ 2 /
        deriv (deriv κ) (δ * ψ x)) + ‖(θ (δ * ψ x) : ℂ) * G x - F x‖ *
        Real.sqrt (deriv κ (δ * ψ x) ^ 2 / deriv (deriv κ) (δ * ψ x))) ^ 2 *
        Real.exp (κ (δ * ψ x) - (φ x + ψ x))))
    (fun x => ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ^ 2 *
        Real.exp (κ (δ * ψ x) - (φ x + ψ x))))
    (fun x => ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ^ 2 * (wT T (δ * ψ x) / 8) *
        Real.exp (-(φ x + ψ x))))
    (Set.indicator {x | -T - 1 ≤ δ * ψ x ∧ δ * ψ x ≤ -T + 1}
      (fun x => ENNReal.ofReal (15 / 4 * (‖G x‖ ^ 2 * Real.exp (-(φ x + ψ x))))))
    ((by fun_prop : Measurable (fun x =>
      ENNReal.ofReal (15 / 4 * (‖G x‖ ^ 2 * Real.exp (-(φ x + ψ x)))))).indicator hsh)
    (by
      intro x
      beta_reduce
      have h8 := GlobalTheory.T.sq_sqrt_add_mul_le_of_twisted_absorption T (δ * ψ x) ‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ‖G x‖
        (deriv θ (δ * ψ x)) (deriv κ (δ * ψ x)) (deriv (deriv κ) (δ * ψ x))
        (Real.exp (κ (δ * ψ x))) (norm_nonneg _) (norm_nonneg _) (hk2 x) (Real.exp_pos _)
        (hθd _) (hκ1 _ (hδψ x)).2.2.2.2 (fun h => hκ2 _ h.1 h.2)
        (fun h => twEst_deriv_cut_zero T θ hθ _ h)
      have he : Real.exp (κ (δ * ψ x) - (φ x + ψ x)) =
          Real.exp (κ (δ * ψ x)) * Real.exp (-(φ x + ψ x)) := by
        rw [sub_eq_add_neg, Real.exp_add]
      have hp := Real.exp_pos (-(φ x + ψ x))
      have hreal := mul_le_mul_of_nonneg_right h8 hp.le
      have hwx := hw (δ * ψ x)
      rw [he]
      by_cases hx : -T - 1 ≤ δ * ψ x ∧ δ * ψ x ≤ -T + 1
      · rw [Set.indicator_of_mem (show x ∈ {x | -T - 1 ≤ δ * ψ x ∧ δ * ψ x ≤ -T + 1} from hx),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        rw [if_pos hx] at hreal
        linear_combination hreal
      · rw [Set.indicator_of_notMem (show x ∉ {x | -T - 1 ≤ δ * ψ x ∧ δ * ψ x ≤ -T + 1} from hx),
          ← ENNReal.ofReal_add (by positivity) (by positivity), add_zero]
        apply ENNReal.ofReal_le_ofReal
        rw [if_neg hx] at hreal
        linear_combination hreal)
    hB hfin
  have hLHS : ∫⁻ x, ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ^ 2 *
      (wT T (δ * ψ x) * Real.exp (-(φ x + ψ x)))) ∂vol n X.z =
      ENNReal.ofReal 8 * ∫⁻ x, ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ^ 2 *
        (wT T (δ * ψ x) / 8) * Real.exp (-(φ x + ψ x))) ∂vol n X.z := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr (fun x => ?_)
    rw [← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    ring
  have hRHS : ∫⁻ x, Set.indicator {x | -T - 1 ≤ δ * ψ x ∧ δ * ψ x ≤ -T + 1}
      (fun x => ENNReal.ofReal (15 / 4 * (‖G x‖ ^ 2 * Real.exp (-(φ x + ψ x))))) x ∂vol n X.z =
      ENNReal.ofReal (15 / 4) * ∫⁻ x in {x | -T - 1 ≤ δ * ψ x ∧ δ * ψ x ≤ -T + 1},
        ENNReal.ofReal (‖G x‖ ^ 2 * Real.exp (-(φ x + ψ x))) ∂vol n X.z := by
    rw [lintegral_indicator hsh, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr (fun x => ?_)
    rw [ENNReal.ofReal_mul (by norm_num)]
  rw [hLHS]
  calc ENNReal.ofReal 8 * ∫⁻ x, ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ^ 2 *
        (wT T (δ * ψ x) / 8) * Real.exp (-(φ x + ψ x))) ∂vol n X.z
      ≤ ENNReal.ofReal 8 * ∫⁻ x, Set.indicator {x | -T - 1 ≤ δ * ψ x ∧ δ * ψ x ≤ -T + 1}
        (fun x => ENNReal.ofReal (15 / 4 * (‖G x‖ ^ 2 * Real.exp (-(φ x + ψ x))))) x
          ∂vol n X.z := by gcongr
    _ = _ := by
      rw [hRHS, ← mul_assoc, ← ENNReal.ofReal_mul (by norm_num)]
      norm_num

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedExtensionEtaleSteinSqIntegrableStatement

section

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.twistedExtension_etaleStein_sqIntegrable : ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M], ∀ (X : EtaleStein n M) (φ ψ : M → ℝ) (G : M → ℂ) (Ω : Set M) (δ T : ℝ) (θ : ℝ → ℝ), SmoothR n X.z φ → SmoothR n X.z ψ → (∀ x, ψ x ≤ 0) → 0 < δ → 300 ≤ T → IsCut T θ → (∀ α ∈ Set.Icc (1 : ℝ) (1 + δ), LeviNonneg n X.z (fun x => φ x + α * ψ x)) → IsOpen Ω → Measurable G → (∀ e : OpenPartialHomeomorph M (V n), IsChart n X.z e → DifferentiableOn ℂ (G ∘ e.symm) (e.target ∩ e.symm ⁻¹' Ω)) → (∀ x, δ * ψ x ≤ -T + 1 → x ∈ Ω) → wint n X.z (fun x => (θ (δ * ψ x) : ℂ) * G x) (fun x => φ x + ψ x) < ⊤ → ∃ F : M → ℂ, Holo n X.z F ∧ ∫⁻ x, ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ^ 2 * (wT T (δ * ψ x) * Real.exp (-(φ x + ψ x)))) ∂vol n X.z ≤ 30 * ∫⁻ x in {x | -T - 1 ≤ δ * ψ x ∧ δ * ψ x ≤ -T + 1}, ENNReal.ofReal (‖G x‖ ^ 2 * Real.exp (-(φ x + ψ x))) ∂vol n X.z := by
  first | exact @GlobalTheory.twistedExtension_sqInt | exact GlobalTheory.twistedExtension_sqInt | (intros; apply GlobalTheory.twistedExtension_sqInt <;> assumption)
end
end
