module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfL
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfF
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IsOrth
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EnormPowLeInvMeasureMulLintegralBall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFactorAndDensityNearOneInFlagChart
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Linter.HaveILetI
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FinrankEqTwoMulHalfDegree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.QuadraticCoefficientForms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralUnitaryKernelLeExpPowEightStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitSumKernelBallMeasureLeIntegralStatement
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormBcharMulNfacRmul
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OrthoStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PairUnfoldPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PairUnfoldPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfG
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ProdCastLESucc
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantMeasureChartBallOrthonormalLowerBound

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal

namespace GlobalTheory.BallVol

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem spread_zero (X : Data E r) (hr : 0 < r) (τ : X.Ψ) : X.spread (fun _ _ => 0) τ = 0 := by
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  simp [Data.spread]

theorem nd_le (X : Data E r) : nd X ≤ X.Ψ.card * (r * r) := by
  unfold nd
  rw [Fintype.card_prod, Fintype.card_coe]
  refine Nat.mul_le_mul_left _ ?_
  calc Fintype.card {p : Fin r × Fin r // p.2 < p.1} ≤ Fintype.card (Fin r × Fin r) :=
        Fintype.card_subtype_le _
    _ = r * r := by simp

theorem nat_bound (f r n : ℕ) (hf : 1 ≤ f) (hr : 1 ≤ r) (hn : n ≤ f * (r * r)) :
    2 * n * (200 * r ^ 3 * f) + n * n + 1 ≤ 402 * (f * r) ^ 8 := by
  set a := f * r with ha
  have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hra : r ≤ a := by rw [ha]; exact Nat.le_mul_of_pos_left r (by omega)
  have hfa : f ≤ a := by rw [ha]; exact Nat.le_mul_of_pos_right f (by omega)
  have hna : n ≤ a * a := hn.trans (by rw [ha, ← Nat.mul_assoc]; exact Nat.mul_le_mul_left _ hra)
  have h1 : 2 * n * (200 * r ^ 3 * f) ≤ 400 * a ^ 8 := by
    have e : 2 * n * (200 * r ^ 3 * f) ≤ 400 * ((a * a) * (a ^ 3 * a)) := by
      have := Nat.mul_le_mul hna (Nat.mul_le_mul (Nat.pow_le_pow_left hra 3) hfa)
      nlinarith
    refine e.trans (Nat.mul_le_mul_left _ ?_)
    calc a * a * (a ^ 3 * a) = a ^ 6 := by ring
      _ ≤ a ^ 8 := Nat.pow_le_pow_right ha1 (by norm_num)
  have h2 : n * n ≤ a ^ 8 := by
    calc n * n ≤ (a * a) * (a * a) := Nat.mul_le_mul hna hna
      _ = a ^ 4 := by ring
      _ ≤ a ^ 8 := Nat.pow_le_pow_right ha1 (by norm_num)
  have h3 : 1 ≤ a ^ 8 := Nat.one_le_pow _ _ ha1
  omega

theorem real_bound (f r n : ℕ) (hf : 1 ≤ f) (hr : 1 ≤ r) (hn : n ≤ f * (r * r)) :
    Real.exp (-(402 * ((f : ℝ) * r) ^ 8)) ≤ Real.exp (-(1 / 10)) *
      (Real.pi ^ n * (1 / (200 * (r : ℝ) ^ 3 * f)) ^ (2 * n) / n.factorial) := by
  set K : ℝ := 200 * (r : ℝ) ^ 3 * f with hK
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hK1 : 1 ≤ K := by
    have : (1 : ℝ) ≤ (r : ℝ) ^ 3 := one_le_pow₀ hr'
    rw [hK]; nlinarith
  have hKpos : 0 < K := by linarith

  have hδ : Real.exp (-K) ≤ 1 / K := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ hKpos (by linarith [Real.add_one_le_exp K])
  have hδn : Real.exp (-(2 * n * K)) ≤ (1 / K) ^ (2 * n) := by
    calc Real.exp (-(2 * n * K)) = Real.exp (-K) ^ (2 * n) := by
          rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      _ ≤ (1 / K) ^ (2 * n) := pow_le_pow_left₀ (Real.exp_pos _).le hδ _
  have hpi : (1 : ℝ) ≤ Real.pi ^ n := one_le_pow₀ (by linarith [Real.pi_gt_three])
  have hfac : (n.factorial : ℝ) ≤ Real.exp ((n : ℝ) * n) := by
    have h1 : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
    have h2 : (n : ℝ) ^ n ≤ Real.exp n ^ n :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith [Real.add_one_le_exp (n : ℝ)]) _
    rw [← Real.exp_nat_mul] at h2
    exact h1.trans h2
  have hfpos : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hN := nat_bound f r n hf hr hn
  have hNR : 2 * (n : ℝ) * K + n * n + 1 ≤ 402 * ((f : ℝ) * r) ^ 8 := by
    rw [hK]; exact_mod_cast hN
  have hmain : Real.exp (-(402 * ((f : ℝ) * r) ^ 8)) ≤
      Real.exp (-(1 / 10)) * (Real.exp (-(2 * n * K)) / Real.exp ((n : ℝ) * n)) := by
    rw [← Real.exp_sub, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  refine hmain.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
  calc Real.exp (-(2 * n * K)) / Real.exp ((n : ℝ) * n)
      ≤ (1 / K) ^ (2 * n) / n.factorial := div_le_div₀ (by positivity) hδn hfpos hfac
    _ ≤ Real.pi ^ n * (1 / K) ^ (2 * n) / n.factorial := by
        gcongr
        exact le_mul_of_one_le_left (by positivity) hpi

theorem ballvol : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), 0 < X.p0 → X.p0 < r →
    ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x →
    ENNReal.ofReal (Real.exp (-(C * ((X.Ψ.card : ℝ) * r) ^ 8))) ≤
      ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x (Metric.ball (0 : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X))
        (1 / (100 * (r : ℝ) ^ 2)) ∩ ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x) := by
  refine ⟨402, by norm_num, ?_⟩
  intro E _ _ _ r X x hp0 hpr hx
  have hr : 0 < r := lt_of_le_of_lt (Nat.zero_le _) hpr
  set la : Wt X.Ψ r := fun _ _ => 0 with hla
  set w : ℝ := ∑ τ, X.spread la τ with hw
  have hw0 : w = 0 := Finset.sum_eq_zero fun τ _ => spread_zero X hr τ
  have hcard : ((X.Ψ.card : ℕ) : ℝ) = fdeg E := by
    rw [← Fintype.card_coe, QuadraticCoefficientForms.card_Psi X]
  have hf1 : (1 : ℝ) ≤ (X.Ψ.card : ℝ) := by rw [hcard]; exact one_le_field_half_degree
  have hf1n : 1 ≤ X.Ψ.card := by exact_mod_cast hf1
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  set δ := GlobalTheory.LevGeo.chartRad E r w with hδ
  have hδeq : δ = 1 / (200 * (r : ℝ) ^ 3 * (X.Ψ.card : ℝ)) := by
    rw [hδ, GlobalTheory.LevGeo.chartRad, hw0, zero_add, hcard]
  have hδpos : 0 < δ := by rw [hδeq]; positivity
  have hδle : δ ≤ 1 / (100 * (r : ℝ) ^ 2) := by
    rw [hδeq]
    refine one_div_le_one_div_of_le (by positivity) ?_
    have h3 : (r : ℝ) ^ 2 ≤ (r : ℝ) ^ 3 := pow_le_pow_right₀ hr1 (by norm_num)
    have h4 : (r : ℝ) ^ 3 ≤ (r : ℝ) ^ 3 * (X.Ψ.card : ℝ) := le_mul_of_one_le_right (by positivity) hf1
    nlinarith
  have hnear : ∀ z : V (nd X), ‖z‖ ≤ δ → cpt X x z ∈ X.dom ∧
      Real.exp (-(1 / 20)) ≤ X.nfac la (cpt X x z) ^ 2 ∧ Real.exp (-(1 / 10)) ≤ densF X x z :=
    fun z hz => GlobalTheory.ChartNearOne.chart_near_one E r X la w x hr hx le_rfl z hz
  have hsubO : Metric.ball (0 : V (nd X)) δ ⊆ OmF X x := fun z hz =>
    (hnear z (le_of_lt (mem_ball_zero_iff.1 hz))).1
  have hsub : Metric.ball (0 : V (nd X)) δ ⊆
      Metric.ball 0 (1 / (100 * (r : ℝ) ^ 2)) ∩ OmF X x := fun z hz =>
    ⟨Metric.ball_subset_ball hδle hz, hsubO hz⟩
  refine le_trans ?_ (measure_mono hsub)
  have hm : muF X x (Metric.ball 0 δ) =
      ∫⁻ z in Metric.ball (0 : V (nd X)) δ, ENNReal.ofReal (densF X x z) := by
    rw [muF, withDensity_apply _ measurableSet_ball, Measure.restrict_restrict measurableSet_ball,
      Set.inter_eq_left.2 hsubO]
  rw [hm]
  have hn := nd_le X
  calc ENNReal.ofReal (Real.exp (-(402 * ((X.Ψ.card : ℝ) * r) ^ 8)))
      ≤ ENNReal.ofReal (Real.exp (-(1 / 10))) * volume (Metric.ball (0 : V (nd X)) δ) := by
        rw [GlobalTheory.volume_ball_euclideanSpace_complex 0 hδpos, Fintype.card_fin,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hδeq]
        exact real_bound X.Ψ.card r (nd X) hf1n hr hn
    _ = ∫⁻ z in Metric.ball (0 : V (nd X)) δ, ENNReal.ofReal (Real.exp (-(1 / 10))) := by
        rw [setLIntegral_const, mul_comm]
    _ ≤ _ := setLIntegral_mono' measurableSet_ball fun z hz =>
        ENNReal.ofReal_le_ofReal (hnear z (le_of_lt (mem_ball_zero_iff.1 hz))).2.2

end

end GlobalTheory.BallVol
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantMeasureChartBallOrthonormalLowerBoundStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal

theorem _root_.GlobalTheory.T.invariantMeasure_chartBall_orthonormal_lower_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ENNReal.ofReal (Real.exp (-(C * ((X.Ψ.card : ℝ) * r) ^ 8))) ≤ ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x (Metric.ball (0 : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (1 / (100 * (r : ℝ) ^ 2)) ∩ ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x) := by
  first | exact @GlobalTheory.BallVol.ballvol | exact GlobalTheory.BallVol.ballvol | (intros; apply GlobalTheory.BallVol.ballvol <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareL2InequalityFundamentalSet

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
open ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal

namespace GlobalTheory.PoincareL2

theorem nfac_pos' {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (la : Wt X.Ψ r)
    {y : Frame X.Ψ r} (hy : y ∈ X.dom) : 0 < X.nfac la y := by
  unfold Data.nfac
  refine Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Real.rpow_pos_of_pos ?_ _
  exact norm_pos_iff.mpr (div_ne_zero (PoinPf.dmin_ne X hy τ _) (PoinPf.dmin_ne X hy τ _))

theorem poincareNorm_sq_eq_weight_mul_norm_sq {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (la : Wt X.Ψ r)
    (P : Frame X.Ψ r → ℂ) {y : Frame X.Ψ r} (hy : y ∈ X.dom) :
    ENNReal.ofReal (X.pnorm la P y ^ 2) = ENNReal.ofReal (‖P y‖ ^ 2) * IW.Wpsi X la (fun _ => 0) y := by
  have h1 : X.pnorm la P y ^ 2 = ‖P y‖ ^ 2 * Real.exp (-phla X la y) := by
    rw [PoinPf.exp_neg_phla X la (nfac_pos' X la hy)]
    change (‖P y‖ * X.nfac la y) ^ 2 = _
    ring
  have h2 : IW.Wpsi X la (fun _ => 0) y = ENNReal.ofReal (Real.exp (-(phla X la y + 0))) := by
    simp [IW.Wpsi, hy]
  rw [h1, h2, add_zero, ENNReal.ofReal_mul (by positivity)]

theorem sum_le (h1 : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x y : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X y → (∀ γ ∈ X.Γ, ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ∀ b ∈ Bor X.Ψ r, lact γ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = rmul (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z') b → γ = 1) → ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x (Metric.ball (0 : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (1 / (100 * (r : ℝ) ^ 2)) ∩ ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x) * ∑' γ : X.Γ, ENNReal.ofReal (ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.kaY X x (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) (lact γ.1 y)) ≤ ENNReal.ofReal (Real.exp (C * ((X.Ψ.card : ℝ) * r) ^ 8)) * ∫⁻ z, ENNReal.ofReal (ReciprocityTheory.ChartRestriction.G.AR.Up.kaF X y (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) z) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X y)) (h2 : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (y : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X y → ∫⁻ z, ENNReal.ofReal (ReciprocityTheory.ChartRestriction.G.AR.Up.kaF X y (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) z) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X y) ≤ ENNReal.ofReal (Real.exp (C * ((X.Ψ.card : ℝ) * r) ^ 8))) (h3 : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ENNReal.ofReal (Real.exp (-(C * ((X.Ψ.card : ℝ) * r) ^ 8))) ≤ ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x (Metric.ball (0 : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (1 / (100 * (r : ℝ) ^ 2)) ∩ ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r),
      0 < X.p0 → X.p0 < r → IsOrth X x → (∀ γ ∈ X.Γ, ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ∀ b ∈ Bor X.Ψ r, lact γ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = rmul (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z') b → γ = 1) → ∀ y ∈ X.dom,
      ∑' γ : X.Γ, ENNReal.ofReal (PoinPf.kaY X x (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) (lact γ.1 y)) ≤ ENNReal.ofReal (Real.exp (C * ((X.Ψ.card : ℝ) * r) ^ 8)) := by
  obtain ⟨C1, hC1, hS1⟩ := h1
  obtain ⟨C2, hC2, hS2⟩ := h2
  obtain ⟨C3, hC3, hS3⟩ := h3
  refine ⟨C1 + C2 + C3, by positivity, ?_⟩
  intro E _ _ _ r X x hp0 hp0r hx hinj y hy
  have hb := FrameDegreeData.bOf_mem X hy
  have ho : IsOrth X (rmul y (FrameDegreeData.bOf X y)) := FrameDegreeData.ortho_bOf X hy
  set y' := rmul y (FrameDegreeData.bOf X y) with hy'
  have heq : ∑' γ : X.Γ, ENNReal.ofReal (PoinPf.kaY X x (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) (lact γ.1 y)) =
      ∑' γ : X.Γ, ENNReal.ofReal (PoinPf.kaY X x (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) (lact γ.1 y')) := by
    refine tsum_congr fun γ => ?_
    rw [hy', PoinPf.lact_rmul' γ.1 y (FrameDegreeData.bOf X y),
      PoinPf.kaY_rmul X hx ((PairUnfoldPf.lact_mem_dom_iff X γ.2 y).2 hy) hb]
  rw [heq]
  set S := ∑' γ : X.Γ, ENNReal.ofReal (PoinPf.kaY X x (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) (lact γ.1 y'))
  set N : ℝ := ((X.Ψ.card : ℝ) * r) ^ 8
  set M := muF X x (Metric.ball (0 : V (nd X)) (1 / (100 * (r : ℝ) ^ 2)) ∩ OmF X x)
  have e1 : M * S ≤ ENNReal.ofReal (Real.exp (C1 * N)) * ENNReal.ofReal (Real.exp (C2 * N)) :=
    (hS1 E r X x y' hp0 hp0r hx ho hinj).trans (mul_le_mul' le_rfl (hS2 E r X y' hp0 hp0r ho))
  have e3 : ENNReal.ofReal (Real.exp (-(C3 * N))) ≤ M := hS3 E r X x hp0 hp0r hx
  have hone : ENNReal.ofReal (Real.exp (C3 * N)) * ENNReal.ofReal (Real.exp (-(C3 * N))) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), ← Real.exp_add]; simp
  calc S = (ENNReal.ofReal (Real.exp (C3 * N)) * ENNReal.ofReal (Real.exp (-(C3 * N)))) * S := by
          rw [hone, one_mul]
    _ ≤ (ENNReal.ofReal (Real.exp (C3 * N)) * M) * S := by gcongr
    _ = ENNReal.ofReal (Real.exp (C3 * N)) * (M * S) := by ring
    _ ≤ ENNReal.ofReal (Real.exp (C3 * N)) * (ENNReal.ofReal (Real.exp (C1 * N)) * ENNReal.ofReal (Real.exp (C2 * N))) := by
          gcongr
    _ = ENNReal.ofReal (Real.exp ((C1 + C2 + C3) * N)) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), ← Real.exp_add,
            ← Real.exp_add]
          congr 2; ring

end GlobalTheory.PoincareL2

theorem GlobalTheory.PoincareL2.poincare_l2_of_orthogonal (h1 : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field
    E] [NumberField E] [IsCMField E] (r : ℕ) (X
    : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x y
    : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X y → (∀ γ ∈ X.Γ, ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd
    X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^
    2) → ∀ b ∈ Bor X.Ψ r, lact γ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x
    z) = rmul (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x
    z') b → γ = 1) → ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x (Metric.ball (0
    : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (1 /
    (100 * (r : ℝ) ^ 2)) ∩ ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X
    x) * ∑' γ : X.Γ, ENNReal.ofReal (ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.kaY X x (4 *
    (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) (lact γ.1 y)) ≤ ENNReal.ofReal (Real.exp (C * ((X.Ψ.card : ℝ)
    * r) ^ 8)) * ∫⁻ z, ENNReal.ofReal (ReciprocityTheory.ChartRestriction.G.AR.Up.kaF X y (4 *
    (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) z) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X y)) (h2
    : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X
    : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (y
    : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X y → ∫⁻ z, ENNReal.ofReal (ReciprocityTheory.ChartRestriction.G.AR.Up.kaF
    X y (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) z) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X
    y) ≤ ENNReal.ofReal (Real.exp (C * ((X.Ψ.card : ℝ) * r) ^ 8))) (h3 : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X
    : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x
    : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ENNReal.ofReal (Real.exp
    (-(C * ((X.Ψ.card : ℝ) * r) ^
    8))) ≤ ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x (Metric.ball (0
    : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (1 /
    (100 * (r : ℝ) ^ 2)) ∩ ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X
    x)) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X
    : Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (x x0 : Frame X.Ψ r) (FF
    : Set (ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd
    X))) (F : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd
    X) → ℂ) (P0
    : Frame X.Ψ r → ℂ), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0 → ReciprocityTheory.ChartRestriction.G.AR.Up.IsFundSet X x0 FF → (∀ γ ∈ X.Γ, ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd
    X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^
    2) → ∀ b ∈ Bor X.Ψ r, lact γ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x
    z) = rmul (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x
    z') b → γ = 1) → DifferentiableOn ℂ F (ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X
    x) → ReciprocityTheory.ChartRestriction.G.AR.Up.IsBEq X la P0 → (∀ z ∈ ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x, P0 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt
    X x z) = F z) → ∫⁻ z in FF, ENNReal.ofReal (X.pnorm la
    (ReciprocityTheory.ChartRestriction.G.AR.Up.poin X la P0)
    (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ^
    2) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x0) ≤ ENNReal.ofReal (Real.exp (C *
    ((X.Ψ.card : ℝ) * r) ^ 8)) * ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 /
    ReciprocityTheory.ChartRestriction.G.AR.Up.kaF X x (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1)
    z) * ReciprocityTheory.ChartRestriction.G.AR.Up.IW.Wpsi X la (fun _ => 0) (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt
    X x z) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x) := by
  obtain ⟨C, hC, hsum⟩ := GlobalTheory.PoincareL2.sum_le h1 h2 h3
  refine ⟨C, hC, ?_⟩
  intro E _ _ _ r X la x x0 FF F P0 hp0 hp0r hx hx0 hFF hinj hFd hP0 hPF
  classical
  set bb : ℝ := (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) with hbbdef
  have hInv : IsInvFn X (fun _ : Frame X.Ψ r => (0 : ℝ)) := fun _ _ _ _ _ _ => rfl
  have hW := (IW.metricW_of GlobalTheory.NormFactor.nfacRmul_holds GlobalTheory.NormFactor.nfacLact_holds ortho_holds
    lu_holds X la (fun _ => 0) hInv (fun _ _ => contDiffOn_const) ⟨0, fun _ _ => le_rfl⟩).1
  set W := IW.Wpsi X la (fun _ => 0) with hWdef
  obtain ⟨D⟩ := ExtFPf.luData_of lu_holds X x0 hx0
  set C1 := ENNReal.ofReal (Real.exp (C * ((X.Ψ.card : ℝ) * r) ^ 8)) with hC1def
  have hsumY := hsum E r X x hp0 hp0r hx hinj
  set Pd := X.dom.indicator P0 with hPd
  have hPdm : Measurable Pd := PairUnfoldPf.meas_indC X hP0.1.continuousOn
  set ψ : Frame X.Ψ r → ℝ≥0∞ := fun y => ‖Pd y‖ₑ ^ 2 * W y / ENNReal.ofReal (PoinPf.kaY X x bb y) with hψ
  have hψm : Measurable ψ :=
    ((hPdm.enorm.pow_const 2).mul hW.1).div (PoinPf.meas_kaY X x bb).ennreal_ofReal
  have hψB : ∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul y b) = ψ y := by
    intro y hy b hb
    have hyb : rmul y b ∈ X.dom := PoinPf.rmulDom X hb hy
    simp only [hψ, hPd, Set.indicator_of_mem hyb, Set.indicator_of_mem hy, hP0.2 y hy b hb,
      hW.2.1 y hy b hb, PoinPf.kaY_rmul X hx hy hb]
    have hpos : 0 < ‖bchar la b‖ ^ 2 := pow_pos (norm_pos_iff.2 (PoinPf.bchar_ne X la hb)) 2
    have h0 : ENNReal.ofReal (‖bchar la b‖ ^ 2) ≠ 0 := (ENNReal.ofReal_pos.2 hpos).ne'
    have ht : ENNReal.ofReal (‖bchar la b‖ ^ 2) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hc : ‖bchar la b‖ₑ ^ 2 = ENNReal.ofReal (‖bchar la b‖ ^ 2) := by
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [enorm_mul, mul_pow, hc]
    congr 1
    rw [ENNReal.div_eq_inv_mul]
    calc ENNReal.ofReal (‖bchar la b‖ ^ 2) * ‖P0 y‖ₑ ^ 2 * ((ENNReal.ofReal (‖bchar la b‖ ^ 2))⁻¹ * W y)
        = (ENNReal.ofReal (‖bchar la b‖ ^ 2) * (ENNReal.ofReal (‖bchar la b‖ ^ 2))⁻¹) *
            (‖P0 y‖ₑ ^ 2 * W y) := by ring
      _ = ‖P0 y‖ₑ ^ 2 * W y := by rw [ENNReal.mul_inv_cancel h0 ht, one_mul]
  have hpt : ∀ z ∈ FF, ENNReal.ofReal (X.pnorm la (poin X la P0) (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ^ 2) ≤
      C1 * ∑' γ : X.Γ, ψ (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)) := by
    intro z hz
    have hy : ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z ∈ X.dom := hFF.2.1 hz
    rw [GlobalTheory.PoincareL2.poincareNorm_sq_eq_weight_mul_norm_sq X la _ hy]
    have hk0 : ∀ γ : X.Γ, ENNReal.ofReal (PoinPf.kaY X x bb (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z))) ≠ 0 :=
      fun γ => (ENNReal.ofReal_pos.2 (PoinPf.kaY_pos _ _ _ _)).ne'
    have hkt : ∀ γ : X.Γ, ENNReal.ofReal (PoinPf.kaY X x bb (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z))) ≠ ⊤ :=
      fun _ => ENNReal.ofReal_ne_top
    have hcs := PoinPf.cs_sq (fun γ : X.Γ => ‖P0 (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z))‖ₑ)
      (fun γ => ENNReal.ofReal (PoinPf.kaY X x bb (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)))) hk0 hkt
    have e1 : ENNReal.ofReal (‖poin X la P0 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)‖ ^ 2) ≤
        (∑' γ : X.Γ, ‖P0 (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z))‖ₑ) ^ 2 := by
      rw [ENNReal.ofReal_pow (norm_nonneg _)]
      exact pow_le_pow_left₀ zero_le (PoinPf.enorm_poin_le X la P0 _) 2
    have e2 : ∀ γ : X.Γ, ‖P0 (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z))‖ₑ ^ 2 /
        ENNReal.ofReal (PoinPf.kaY X x bb (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z))) * W (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) =
          ψ (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)) := by
      intro γ
      have hγy : lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ∈ X.dom := (PairUnfoldPf.lact_mem_dom_iff X γ.2 _).2 hy
      simp only [hψ, hPd, Set.indicator_of_mem hγy, hW.2.2 γ.1 γ.2 _ hy]
      rw [ENNReal.mul_div_right_comm]
    calc ENNReal.ofReal (‖poin X la P0 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)‖ ^ 2) * W (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)
        ≤ ((∑' γ : X.Γ, ‖P0 (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z))‖ₑ ^ 2 /
            ENNReal.ofReal (PoinPf.kaY X x bb (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)))) * C1) * W (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) :=
          mul_le_mul_of_nonneg_right
            (e1.trans (hcs.trans (mul_le_mul_of_nonneg_left (hsumY _ hy) zero_le))) zero_le
      _ = C1 * ∑' γ : X.Γ, ψ (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)) := by
          rw [← tsum_congr e2, ENNReal.tsum_mul_right]; ring
  have hmeasγ : ∀ γ : X.Γ, AEMeasurable (fun z => ψ (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)))
      ((muF X x0).restrict FF) := fun γ =>
    (hψm.comp ((PairUnfoldPf.lact_cont X γ.1).comp (PairUnfoldPf.cpt_cont X x0)).measurable).aemeasurable
  have hunf := PairUnfoldPf.lunfold D FF measInv_holds hx0 hFF ψ hψm hψB
  have hmi := measInv_holds r X x0 x hx0 hx ψ hψm hψB
  have hrhs : ∫⁻ z, ψ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) ∂muF X x =
      ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x bb z) * W (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) ∂muF X x := by
    refine lintegral_congr_ae ?_
    filter_upwards [ExtFPf.ae_OmF] with z hz
    have hyd : ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z ∈ X.dom := hz
    simp only [hψ, hPd, Set.indicator_of_mem hyd, hPF z hz, PoinPf.kaY_cpt X hx]
    rw [ENNReal.ofReal_div_of_pos (by unfold kaF; exact Real.exp_pos _), ENNReal.ofReal_pow (norm_nonneg _),
      ofReal_norm, ENNReal.mul_div_right_comm]
  calc ∫⁻ z in FF, ENNReal.ofReal (X.pnorm la (poin X la P0) (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ^ 2) ∂muF X x0
      ≤ ∫⁻ z in FF, C1 * ∑' γ : X.Γ, ψ (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)) ∂muF X x0 :=
        setLIntegral_mono' hFF.1 hpt
    _ = C1 * ∑' γ : X.Γ, ∫⁻ z in FF, ψ (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)) ∂muF X x0 := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_tsum hmeasγ]
    _ = C1 * ∫⁻ z, ψ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ∂muF X x0 := by rw [hunf]
    _ = C1 * ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x bb z) * W (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) ∂muF X x := by
        rw [hmi, hrhs]

theorem GlobalTheory.PoincareL2.poincare_l2_inequality : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (x x0 : Frame X.Ψ r) (FF : Set (ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X))) (F : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) → ℂ) (P0 : Frame X.Ψ r → ℂ), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0 → ReciprocityTheory.ChartRestriction.G.AR.Up.IsFundSet X x0 FF → (∀ γ ∈ X.Γ, ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ∀ b ∈ Bor X.Ψ r, lact γ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = rmul (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z') b → γ = 1) → DifferentiableOn ℂ F (ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x) → ReciprocityTheory.ChartRestriction.G.AR.Up.IsBEq X la P0 → (∀ z ∈ ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x, P0 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = F z) → ∫⁻ z in FF, ENNReal.ofReal (X.pnorm la (ReciprocityTheory.ChartRestriction.G.AR.Up.poin X la P0) (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ^ 2) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x0) ≤ ENNReal.ofReal (Real.exp (C * ((X.Ψ.card : ℝ) * r) ^ 8)) * ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 / ReciprocityTheory.ChartRestriction.G.AR.Up.kaF X x (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) z) * ReciprocityTheory.ChartRestriction.G.AR.Up.IW.Wpsi X la (fun _ => 0) (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x) :=
  GlobalTheory.PoincareL2.poincare_l2_of_orthogonal GlobalTheory.T.orbitSum_kernel_ballMeasure_le_integral GlobalTheory.T.lintegral_unitaryKernel_le_exp_pow_eight GlobalTheory.T.invariantMeasure_chartBall_orthonormal_lower_bound
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareL2InequalityFundamentalSetStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
open ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal

theorem _root_.GlobalTheory.T.poincare_l2_inequality_fundamental_set : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (x x0 : Frame X.Ψ r) (FF : Set (ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X))) (F : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) → ℂ) (P0 : Frame X.Ψ r → ℂ), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0 → ReciprocityTheory.ChartRestriction.G.AR.Up.IsFundSet X x0 FF → (∀ γ ∈ X.Γ, ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ∀ b ∈ Bor X.Ψ r, lact γ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = rmul (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z') b → γ = 1) → DifferentiableOn ℂ F (ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x) → ReciprocityTheory.ChartRestriction.G.AR.Up.IsBEq X la P0 → (∀ z ∈ ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x, P0 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = F z) → ∫⁻ z in FF, ENNReal.ofReal (X.pnorm la (ReciprocityTheory.ChartRestriction.G.AR.Up.poin X la P0) (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ^ 2) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x0) ≤ ENNReal.ofReal (Real.exp (C * ((X.Ψ.card : ℝ) * r) ^ 8)) * ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 / ReciprocityTheory.ChartRestriction.G.AR.Up.kaF X x (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) z) * ReciprocityTheory.ChartRestriction.G.AR.Up.IW.Wpsi X la (fun _ => 0) (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x) := by
  first | exact @GlobalTheory.PoincareL2.poincare_l2_inequality | exact GlobalTheory.PoincareL2.poincare_l2_inequality | (intros; apply GlobalTheory.PoincareL2.poincare_l2_inequality <;> assumption)
end
end
