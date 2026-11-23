module

public import Development.AutomorphicSpectrum.Statements.GeometryStatements.AgreementPos
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AbsCoeffProdXLeOne
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionDifferenceTelescopingIntegralStatement
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereRegularizationLogLogBoundStatement
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Order.Group
public import Mathlib.Topology.MetricSpace.Pseudo.Basic
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.LimRateMulLogSqLe

section

@[expose] public section

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem limRate_log_inv_exp (s : ℝ) : Real.log (1 / Real.exp (-(s ^ 2)⁻¹)) = (s ^ 2)⁻¹ := by
  rw [one_div, Real.log_inv, Real.log_exp, neg_neg]

theorem limRate_sq_le_exp {x : ℝ} (hx : 0 ≤ x) : x ^ 2 ≤ Real.exp x := by
  have h := Real.sum_le_exp_of_nonneg hx 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  nlinarith [mul_nonneg hx (sq_nonneg (x - 3 / 2))]

theorem limRate_mul_log_sq_le {s : ℝ} (hs : 0 < s) (h1 : s ≤ 1) : s * Real.log s ^ 2 ≤ 1 := by
  have h := limRate_sq_le_exp (x := -Real.log s) (by linarith [Real.log_nonpos hs.le h1])
  rw [Real.exp_neg, Real.exp_log hs, neg_sq] at h
  calc s * Real.log s ^ 2 ≤ s * s⁻¹ := mul_le_mul_of_nonneg_left h hs.le
    _ = 1 := mul_inv_cancel₀ hs.ne'

theorem limRate : Filter.Tendsto (fun t : ℝ => Real.log (Real.log (1 / t)) ^ 2 / Real.log (1 / t)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧ (∀ s : ℝ, 0 < s → s ≤ 1 → Real.log (Real.log (1 / Real.exp (-(s ^ 2)⁻¹))) ^ 2 / Real.log (1 / Real.exp (-(s ^ 2)⁻¹)) ≤ 4 * s) ∧ (∀ s : ℝ, 0 < s → s ≤ 1 → Real.exp (-(s ^ 2)⁻¹) ^ ((1 : ℝ) / 3) ≤ 2 * s) ∧ ∀ C ε : ℝ, 0 < ε → ∃ s₀ > (0 : ℝ), ∀ s, 0 < s → s ≤ s₀ → C * Real.log (Real.log (1 / Real.exp (-(s ^ 2)⁻¹))) / Real.log (1 / Real.exp (-(s ^ 2)⁻¹)) ≤ ε * s := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hl : Filter.Tendsto (fun t : ℝ => Real.log (1 / t)) (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
      simp only [one_div]
      exact Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp hl
    refine h.congr fun t => ?_
    simp
  · intro s hs h1
    rw [limRate_log_inv_exp, Real.log_inv, Real.log_pow, div_inv_eq_mul]
    have h3 := limRate_mul_log_sq_le hs h1
    push_cast
    have e : (-(2 * Real.log s)) ^ 2 * s ^ 2 = 4 * s * (s * Real.log s ^ 2) := by ring
    rw [e]
    nlinarith
  · intro s hs h1
    rw [← Real.exp_mul]
    set y := (s ^ 2)⁻¹ with hy
    have hys : y * s ^ 2 = 1 := inv_mul_cancel₀ (by positivity)
    have hy0 : 0 ≤ y := by positivity
    have ha := Real.add_one_le_exp (y * (1 / 3))
    have hE : 0 < Real.exp (y * (1 / 3)) := Real.exp_pos _
    rw [show -y * (1 / 3) = -(y * (1 / 3)) by ring, Real.exp_neg]
    have hkey : 1 ≤ 2 * s * (1 + y * (1 / 3)) := by
      nlinarith [sq_nonneg (s - 1 / 4), mul_pos hs hs]
    calc (Real.exp (y * (1 / 3)))⁻¹ ≤ (1 + y * (1 / 3))⁻¹ :=
          inv_anti₀ (by positivity) (by linarith)
      _ ≤ 2 * s := by
          rw [inv_le_iff_one_le_mul₀ (by positivity)]
          linarith
  · intro C ε hε
    set K := 2 * |C| + 1 with hK
    have hKpos : 0 < K := by positivity
    refine ⟨min 1 ((ε / K) ^ 2), by positivity, ?_⟩
    intro s hs hs0
    have h1 : s ≤ 1 := le_trans hs0 (min_le_left _ _)
    have h2 : s ≤ (ε / K) ^ 2 := le_trans hs0 (min_le_right _ _)
    rw [limRate_log_inv_exp, Real.log_inv, Real.log_pow, div_inv_eq_mul]
    push_cast
    have h3 := limRate_mul_log_sq_le hs h1
    have hsq : (s * Real.log s) ^ 2 ≤ (ε / K) ^ 2 := by
      calc (s * Real.log s) ^ 2 = s * (s * Real.log s ^ 2) := by ring
        _ ≤ s * 1 := mul_le_mul_of_nonneg_left h3 hs.le
        _ ≤ (ε / K) ^ 2 := by linarith
    have habs : |s * Real.log s| ≤ ε / K := abs_le.mpr (abs_le_of_sq_le_sq' hsq (by positivity))
    have hb : -2 * C * (s * Real.log s) ≤ ε := by
      calc -2 * C * (s * Real.log s) ≤ |-2 * C * (s * Real.log s)| := le_abs_self _
        _ = 2 * |C| * |s * Real.log s| := by
            rw [abs_mul, abs_mul, abs_neg, abs_two]
        _ ≤ 2 * |C| * (ε / K) := mul_le_mul_of_nonneg_left habs (by positivity)
        _ ≤ ε := by
            rw [mul_div_assoc', div_le_iff₀ hKpos, hK]
            nlinarith [abs_nonneg C]
    calc C * -(2 * Real.log s) * s ^ 2 = s * (-2 * C * (s * Real.log s)) := by ring
      _ ≤ s * ε := mul_le_mul_of_nonneg_left hb hs.le
      _ = ε * s := mul_comm _ _

end GlobalTheory.CompanionTheory.Ar.PB
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.TendstoLimUnderOfCauchyRate

section

@[expose] public section

open Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem tendsto_limUnder_of_cauchy_rate :
    ∀ (f δ : ℝ → ℝ) (t₁ : ℝ), 0 < t₁ → Filter.Tendsto δ (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) →
      (∀ t t', 0 < t' → t' ≤ t → t ≤ t₁ → |f t - f t'| ≤ δ t) →
      Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0))
          (nhds (Filter.limUnder (nhdsWithin 0 (Set.Ioi 0)) f)) ∧
        ∀ t, 0 < t → t ≤ t₁ → |f t - Filter.limUnder (nhdsWithin 0 (Set.Ioi 0)) f| ≤ δ t := by
  intro f δ t₁ ht₁ hδ hrate
  set F : Filter ℝ := nhdsWithin 0 (Set.Ioi 0) with hF

  have hS : ∀ ε > 0, {t | δ t < ε ∧ 0 < t ∧ t ≤ t₁} ∈ F := by
    intro ε hε
    filter_upwards [hδ (Iio_mem_nhds hε),
      (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ F),
      (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds ht₁) : Set.Iic t₁ ∈ F)] with t hδt ht ht₁t
    exact ⟨hδt, ht, ht₁t⟩
  have hC : Cauchy (Filter.map f F) := by
    rw [Metric.cauchy_iff]
    refine ⟨inferInstance, fun ε hε => ⟨f '' {t | δ t < ε ∧ 0 < t ∧ t ≤ t₁}, Filter.image_mem_map (hS ε hε), ?_⟩⟩
    rintro _ ⟨t, ⟨h1, h2, h3⟩, rfl⟩ _ ⟨t', ⟨h1', h2', h3'⟩, rfl⟩
    rw [Real.dist_eq]
    rcases le_total t' t with h | h
    · exact (hrate t t' h2' h h3).trans_lt h1
    · rw [abs_sub_comm]; exact (hrate t' t h2 h h3').trans_lt h1'
  obtain ⟨L, hL⟩ := CompleteSpace.complete hC
  have hlim : Filter.Tendsto f F (nhds (Filter.limUnder F f)) := tendsto_nhds_limUnder ⟨L, hL⟩
  refine ⟨hlim, fun t ht htt => ?_⟩

  have hev : ∀ᶠ t' in F, |f t - f t'| ≤ δ t := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds ht)] with t' h0 h1
    exact hrate t t' h0 h1 htt
  exact le_of_tendsto (tendsto_const_nhds.sub hlim).abs hev

end GlobalTheory.CompanionTheory.Ar.PB
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.AgreementPositive

section

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB
open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

def agreeRate (t : ℝ) : ℝ := Real.log (Real.log (1 / t)) ^ 2 / Real.log (1 / t)

theorem agree_exp_le_sq {s : ℝ} (hs : 0 < s) : Real.exp (-(s ^ 2)⁻¹) ≤ s ^ 2 := by
  have hx : 0 < (s ^ 2)⁻¹ := by positivity
  have h1 : (s ^ 2)⁻¹ ≤ Real.exp ((s ^ 2)⁻¹) := by linarith [Real.add_one_le_exp ((s ^ 2)⁻¹)]
  rw [Real.exp_neg]
  calc (Real.exp (s ^ 2)⁻¹)⁻¹ ≤ ((s ^ 2)⁻¹)⁻¹ := inv_anti₀ hx h1
    _ = s ^ 2 := inv_inv _

theorem agreeRate_nonneg (s : ℝ) (hs : 0 < s) : 0 ≤ agreeRate (Real.exp (-(s ^ 2)⁻¹)) := by
  unfold agreeRate
  rw [limRate_log_inv_exp]
  have : 0 < (s ^ 2)⁻¹ := by positivity
  positivity

theorem agree_cauchy (hI : Inputs) (D : ℕ) (σ : Type) [Fintype σ] (S : AnSys D σ) (h0 : 0 < S.t₀) :
    ∃ C' t₁ : ℝ, 0 < t₁ ∧ t₁ ≤ S.t₀ ∧
    ∀ (II : IntersectionSystem), IsFullIntersectionSystem II →
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (Re : Realis S P)
      (w : Fin (D + 1) → σ) (t t' : ℝ), 0 < t' → t' ≤ t → t ≤ t₁ →
      |Re.num II t w - Re.num II t' w| ≤ ((D : ℝ) + 1) * (|C'| * |agreeRate t|) := by
  obtain ⟨C', t₁, ht₁, ht₁0, hb⟩ := GlobalTheory.T.monge_ampere_regularization_log_log_bound hI.convergenceRate D σ S h0
  refine ⟨C', t₁, ht₁, ht₁0, ?_⟩
  intro II hII K _ ι _ P Re w t t' ht' htt ht
  have ht0 : 0 < t := lt_of_lt_of_le ht' htt
  rw [GlobalTheory.T.intersection_difference_telescoping_integral hI II hII K ι D σ S P Re t t' w ht0 (ht.trans ht₁0) ht' ((htt.trans ht).trans ht₁0)]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hr : ∀ r : Fin (D + 1), |mInt S.A (fun i => S.potT (w (r.succAbove i)) (if r.succAbove i < r then t else t'))
      (fun x => S.phT (w r) t x - S.phT (w r) t' x)| ≤ |C'| * |agreeRate t| := by
    intro r
    have := hb t t' ht' htt ht (w r) (fun i => w (r.succAbove i)) (fun i => decide (r.succAbove i < r))
    simp only [decide_eq_true_eq] at this
    refine this.trans ?_
    rw [mul_div_assoc]
    exact (le_abs_self _).trans (by rw [abs_mul]; rfl)
  refine (Finset.sum_le_sum fun r _ => hr r).trans ?_
  simp

theorem agreementPos : AgreementPos := by
  intro hI D σ _ S abelian₂ h0
  obtain ⟨C', t₁, ht₁, ht₁0, hc⟩ := agree_cauchy hI D σ S h0
  obtain ⟨hlim, hrate, -, -⟩ := limRate
  refine ⟨|abelian₂| ^ (D + 1) * (((D : ℝ) + 1) * (|C'| * 4)), min 1 t₁, lt_min one_pos ht₁, ?_⟩
  intro II hII K _ ι _ P Re
  have hδ : Tendsto (fun t => ((D : ℝ) + 1) * (|C'| * |agreeRate t|)) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun t => |agreeRate t|) (𝓝[>] 0) (𝓝 0) := by
      have h2 := hlim.abs
      rw [abs_zero] at h2
      exact h2
    simpa using (this.const_mul |C'|).const_mul ((D : ℝ) + 1)
  have hL := fun w => tendsto_limUnder_of_cauchy_rate (fun t => Re.num II t w)
    (fun t => ((D : ℝ) + 1) * (|C'| * |agreeRate t|)) t₁ ht₁ hδ (hc II hII K ι P Re w)
  refine ⟨fun w => (hL w).1, fun s hs hss => ?_⟩
  have hs1 : s ≤ 1 := hss.trans (min_le_left _ _)
  have hst : s ≤ t₁ := hss.trans (min_le_right _ _)
  have hT : Real.exp (-(s ^ 2)⁻¹) ≤ t₁ := by
    refine (agree_exp_le_sq hs).trans ?_
    nlinarith
  refine ⟨hT.trans ht₁0, fun c hcL => ?_⟩
  set t := Real.exp (-(s ^ 2)⁻¹)
  have hM : ∀ w, |Re.num II t w - Re.limNum II w| ≤ ((D : ℝ) + 1) * (|C'| * |agreeRate t|) :=
    fun w => (hL w).2 t (Real.exp_pos _) hT
  have hb := (formPoly_sub_bound σ (D + 1) (Re.num II t) (Re.limNum II) _ hM).2 c
  have hr : |agreeRate t| ≤ 4 * s := by
    rw [abs_of_nonneg (agreeRate_nonneg s hs)]
    exact hrate s hs hs1
  have hsum : (∑ a, |c a|) ^ (D + 1) ≤ |abelian₂| ^ (D + 1) :=
    pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => abs_nonneg _) (hcL.trans (le_abs_self _)) _
  have hD : (0 : ℝ) ≤ (D : ℝ) + 1 := by positivity
  calc |eval c (Re.FT II t) - eval c (Re.PB II)|
      ≤ (∑ a, |c a|) ^ (D + 1) * (((D : ℝ) + 1) * (|C'| * |agreeRate t|)) := hb
    _ ≤ |abelian₂| ^ (D + 1) * (((D : ℝ) + 1) * (|C'| * (4 * s))) := by
      gcongr
    _ = |abelian₂| ^ (D + 1) * (((D : ℝ) + 1) * (|C'| * 4)) * s := by ring

end GlobalTheory.CompanionTheory.Ar.PB
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.AgreementPositiveStatement

section

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.agreement_positive : AgreementPos := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.agreementPos | exact GlobalTheory.CompanionTheory.Ar.PB.agreementPos | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.agreementPos <;> assumption)
end
end
