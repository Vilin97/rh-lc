module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QSPow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfOrthonormalConjBlockUpperTriangularStatement
public import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Group.Tannery
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
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QSPow
public import Mathlib.Analysis.SpecificLimits.Normed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IsOrth
public import Development.AbelianVarietyTheory.Counterexamples.UpperHalfSurvey.ExistsFundSetOrth
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.PhlaBlockWtCpt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormScalarPoincareDetRatioLactLeOneStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarPoincareDetRatioPowerDifferentiableOnStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarPoincareDetRatioPowerRmulBorelStatement
import Mathlib.Tactic.ENatToNat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CuspStatementPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.DivCoreUpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OrthoStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalFlagTranslateHolds

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeTsumPowNeZeroOfSingleUnit

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.ScalarPoin MeasureTheory

namespace GlobalTheory

theorem tsum_pow_eventually_ne_zero : ∀ {ι : Type} (a : ι → ℂ) (i0 : ι) (k0 : ℕ), a i0 = 1 → (∀ i, ‖a i‖ ≤ 1) → (∀ i, i ≠ i0 → ‖a i‖ < 1) → Summable (fun i => ‖a i‖ ^ k0) → ∀ N : ℕ, ∃ k : ℕ, N ≤ k ∧ ∑' i, a i ^ k ≠ 0 := by
  intro ι a i0 k0 h0 h1 hlt hs N
  classical
  have hlim : Filter.Tendsto (fun k : ℕ => ∑' i, a i ^ k) Filter.atTop
      (nhds (∑' i, (if i = i0 then (1:ℂ) else 0))) := by
    apply tendsto_tsum_of_dominated_convergence (bound := fun i => ‖a i‖ ^ k0) hs
    · intro i
      by_cases hi : i = i0
      · subst hi; simp [h0]
      · simp only [hi, if_false]
        exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one (hlt i hi)
    · filter_upwards [Filter.eventually_ge_atTop k0] with k hk i
      rw [norm_pow]
      exact pow_le_pow_of_le_one (norm_nonneg _) (h1 i) hk
  rw [tsum_ite_eq] at hlim
  have hev := hlim.eventually_ne one_ne_zero
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 hev
  exact ⟨max N M, le_max_left _ _, hM _ (le_max_right _ _)⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeTsumPowNeZeroOfSingleUnitStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.ScalarPoin MeasureTheory

theorem _root_.GlobalTheory.T.exists_ge_tsum_pow_ne_zero_of_single_unit : ∀ {ι : Type} (a : ι → ℂ) (i0 : ι) (k0 : ℕ), a i0 = 1 → (∀ i, ‖a i‖ ≤ 1) → (∀ i, i ≠ i0 → ‖a i‖ < 1) → Summable (fun i => ‖a i‖ ^ k0) → ∀ N : ℕ, ∃ k : ℕ, N ≤ k ∧ ∑' i, a i ^ k ≠ 0 := by
  first | exact @GlobalTheory.tsum_pow_eventually_ne_zero | exact GlobalTheory.tsum_pow_eventually_ne_zero | (intros; apply GlobalTheory.tsum_pow_eventually_ne_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralPotentialWeightChartLtTop

section

@[expose] public section

namespace GlobalTheory.ScalarPoin

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst MeasureTheory

theorem lintegral_kaF_lt_top : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (x0 : Frame X.Ψ r), IsOrth X x0 → ∃ s0 : ℝ, ∀ s : ℝ, s0 ≤ s →
      ∫⁻ z, ENNReal.ofReal (kaF X x0 s z) ∂muF X x0 < ⊤ := by
  intro E _ _ _ r X x0 ho
  obtain ⟨FF, hF⟩ := GlobalTheory.MetricWeightTest.exists_fundSet_orth X ho
  have hfin := (GlobalTheory.TrueCx.covol_eq X ho hF).1
  refine ⟨4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1, fun s hs => ?_⟩
  obtain ⟨C, hC, hCb⟩ := kaUnfoldStatement_holds r X x0 ho (GlobalTheory.ClosedDiscontinuity.propDisc_closed r X) FF hF s
    (by linarith)
  have h := hCb (fun _ => 1) measurable_const (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
  simp only [mul_one, lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, one_mul] at h
  exact h.trans_lt (ENNReal.mul_lt_top hC hfin)

end GlobalTheory.ScalarPoin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralPotentialWeightChartLtTopStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.ScalarPoin MeasureTheory

theorem _root_.GlobalTheory.T.lintegral_potentialWeight_chart_lt_top : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∃ s0 : ℝ, ∀ s : ℝ, s0 ≤ s → ∫⁻ z, ENNReal.ofReal (kaF X x0 s z) ∂muF X x0 < ⊤ := by
  first | exact @GlobalTheory.ScalarPoin.lintegral_kaF_lt_top | exact GlobalTheory.ScalarPoin.lintegral_kaF_lt_top | (intros; apply GlobalTheory.ScalarPoin.lintegral_kaF_lt_top <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetricScalarPoincareWeightEqTwoMulPotential

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.ScalarPoin MeasureTheory

namespace GlobalTheory.ScalarPoin

theorem phla_laS_cpt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ (k : ℕ) (z : ReciprocityTheory.L2DbarEstimates.V (nd X)), z ∈ OmF X x0 →
    phla X (laS X k) (cpt X x0 z) = 2 * (k : ℝ) * rhF X x0 z := by
  intro E _ _ _ r X x0 ho k z hz
  rw [IW.phla_eq X hz, rhF, ← Finset.sum_neg_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  set x := cpt X x0 z
  let L' : ℕ → ℝ := fun j => if h : j < r + 1 then IW.Lm X x τ ⟨j, h⟩ else 0
  have h1 : ∀ i : Fin r, IW.Lm X x τ i.succ = L' (i + 1) := fun i => by
    simp only [L', dif_pos (Nat.succ_lt_succ i.isLt)]; rfl
  have h2 : ∀ i : Fin r, IW.Lm X x τ i.castSucc = L' i := fun i => by
    simp only [L', dif_pos (Nat.lt_succ_of_lt i.isLt)]; rfl
  have hk : ∀ i : Fin r, ((laS X k τ i : ℤ) : ℝ) =
      2 * (k : ℝ) * (if (i : ℕ) < X.p0 then (0 : ℝ) else 1) - (k : ℝ) := fun i => by
    unfold laS
    by_cases h : (i : ℕ) < X.p0
    · rw [if_neg (not_le.2 h), if_pos h]; push_cast; ring
    · rw [if_pos (not_lt.1 h), if_neg h]; push_cast; ring
  have hL0 : L' 0 = 0 := by
    simp only [L', dif_pos (Nat.succ_pos r)]; exact IW.Lm_zero X x τ
  have hLr : L' r = 0 := by
    simp only [L', dif_pos (Nat.lt_succ_self r)]; exact IW.Lm_last_cpt X x0 ho z τ
  have hLp : L' X.p0 = Real.log ‖dmin X.Gm x τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ := by
    simp only [L', dif_pos (Nat.lt_succ_of_le X.p0_le)]; rfl
  simp_rw [h1, h2, hk]
  rw [Fin.sum_univ_eq_sum_range
    (fun i => (2 * (k : ℝ) * (if i < X.p0 then (0 : ℝ) else 1) - (k : ℝ)) * (L' (i + 1) - L' i)) r]
  have hsplit : ∑ i ∈ Finset.range r,
      (2 * (k : ℝ) * (if i < X.p0 then (0 : ℝ) else 1) - (k : ℝ)) * (L' (i + 1) - L' i) =
      2 * (k : ℝ) * ∑ i ∈ Finset.range r, (if i < X.p0 then (0 : ℝ) else 1) * (L' (i + 1) - L' i) -
        (k : ℝ) * ∑ i ∈ Finset.range r, (L' (i + 1) - L' i) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hsplit, GlobalTheory.CurvMargin.tele_tail L' X.p0 r X.p0_le, Finset.sum_range_sub L' r, hLr, hL0, hLp]
  ring

end GlobalTheory.ScalarPoin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetricScalarPoincareWeightEqTwoMulPotentialStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.ScalarPoin MeasureTheory

theorem _root_.GlobalTheory.T.metric_scalarPoincareWeight_eq_two_mul_potential : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ (k : ℕ) (z : ReciprocityTheory.L2DbarEstimates.V (nd X)), z ∈ OmF X x0 → phla X (laS X k) (cpt X x0 z) = 2 * (k : ℝ) * rhF X x0 z := by
  first | exact @GlobalTheory.ScalarPoin.phla_laS_cpt | exact GlobalTheory.ScalarPoin.phla_laS_cpt | (intros; apply GlobalTheory.ScalarPoin.phla_laS_cpt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspNe

section

@[expose] public section

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.ScalarPoin
open ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst MeasureTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem qS_base (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) (k : ℕ) : qS X x0 k x0 = 1 := by
  unfold qS
  refine Finset.prod_eq_one fun τ _ => ?_
  have hu : IsUnit (mat x0 τ).det := isUnit_iff_ne_zero.mpr (ExF.det_ne_of_orth X ho τ)
  rw [KU.Mx, Matrix.nonsing_inv_mul _ hu, KU.tl_one]
  have h1 : (1 : Matrix (Fin (r - X.p0) ⊕ Fin X.p0) (Fin (r - X.p0) ⊕ Fin X.p0) ℂ).toBlocks₂₂ = 1 := by
    ext i j; simp [Matrix.toBlocks₂₂, Matrix.one_apply]
  rw [h1]
  simp

end GlobalTheory.ScalarPoin

open ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst MeasureTheory GlobalTheory.ScalarPoin in
theorem GlobalTheory.ScalarPoin.exists_cusp_ne : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), 0 < X.p0 → X.p0 < r → (∀ n : ℕ, Even n → ∀ γ ∈ X.Γ, X.χ (fun (τ : X.Ψ) (j : Fin r) => if X.p0 ≤ (j : ℕ) then ((n / 2 : ℕ) : ℤ) else -((n / 2 : ℕ) : ℤ)) γ = 1) → ∀ y ∈ X.dom, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ 0 < n ∧ Even n ∧ ∃ P ∈ X.SS (fun (τ : X.Ψ) (j : Fin r) => if X.p0 ≤ (j : ℕ) then ((n / 2 : ℕ) : ℤ) else -((n / 2 : ℕ) : ℤ)), P y ≠ 0 := by
  intro E _ _ _ r X hp0 hpr hχ y hy N
  obtain ⟨x0, ho, b, hb, rfl⟩ := ortho_holds r X y hy
  have hPD := GlobalTheory.ClosedDiscontinuity.propDisc_closed r X
  have hx0 : x0 ∈ X.dom := KU.orth_dom X ho
  set bb : ℝ := 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1 with hbbdef
  have hbb : 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb := by linarith
  obtain ⟨s0, hs0⟩ := GlobalTheory.T.lintegral_potentialWeight_chart_lt_top E r X x0 ho
  obtain ⟨k0, hk0⟩ := exists_nat_ge ((s0 + bb) / 2)
  have hla : ∀ k : ℕ, (fun (τ : X.Ψ) (j : Fin r) => if X.p0 ≤ (j : ℕ) then (((2 * k) / 2 : ℕ) : ℤ)
      else -(((2 * k) / 2 : ℕ) : ℤ)) = laS X k := by
    intro k; funext τ j; simp [laS]
  have hχk : ∀ k : ℕ, ∀ γ ∈ X.Γ, X.χ (laS X k) γ = 1 := by
    intro k γ hγ
    have := hχ (2 * k) (even_two_mul k) γ hγ
    rwa [hla k] at this
  have hIn : ∀ k : ℕ, k0 ≤ k →
      InAt X x0 (fun x => ENNReal.ofReal (Real.exp (-phla X (laS X k) x))) bb (fun _ => (1 : ℂ)) := by
    intro k hk
    have hs : s0 ≤ 2 * (k : ℝ) - bb := by
      have : ((s0 + bb) / 2 : ℝ) ≤ k := le_trans hk0 (by exact_mod_cast hk)
      linarith
    unfold InAt
    refine lt_of_le_of_lt (le_of_eq ?_) (hs0 _ hs)
    refine lintegral_congr_ae ?_
    filter_upwards [ExtFPf.ae_OmF (X := X) (x0 := x0)] with z hz
    rw [GlobalTheory.T.metric_scalarPoincareWeight_eq_two_mul_potential E r X x0 ho k z hz]
    simp only [norm_one, one_pow, kaF]
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [one_div, ← Real.exp_neg, ← Real.exp_add]
    congr 1; ring
  have hpo := fun k (hk : k0 ≤ k) => poin_holds r X x0 ho hPD (laS X k) _ bb (DivUpPf.metricW_exp X _)
    (DivUpPf.wLower_exp X _) hbb (fun _ => (1 : ℂ)) (qS X x0 k) (differentiableOn_const _) (hIn k hk)
    ⟨GlobalTheory.T.scalarPoincareDetRatioPower_differentiableOn E r X x0 ho k, fun x _ b hb => GlobalTheory.T.scalarPoincareDetRatioPower_rmul_borel E r X x0 k x b hb⟩ (fun z _ => qS_cpt X ho k z)
  set a : X.Γ → ℂ := fun γ => qS X x0 1 (lact γ.1 x0) with ha
  have ha1 : a 1 = 1 := by
    simp only [ha, OneMemClass.coe_one, KU.lact_one]
    exact qS_base X ho 1
  have hterm : ∀ k (γ : X.Γ), (X.χ (laS X k) γ.1)⁻¹ * qS X x0 k (lact γ.1 x0) = a γ ^ k := by
    intro k γ
    rw [hχk k γ.1 γ.2, inv_one, one_mul, qS_pow]
  have hsum : Summable fun γ : X.Γ => ‖a γ‖ ^ k0 := by
    have h := (hpo k0 le_rfl).1 x0 hx0
    simp_rw [hterm k0, norm_pow] at h
    exact h
  have hle : ∀ γ : X.Γ, ‖a γ‖ ≤ 1 := fun γ => (GlobalTheory.T.norm_scalarPoincareDetRatio_lact_le_one E r X x0 ho γ.1 γ.2).1
  have hlt : ∀ γ : X.Γ, γ ≠ 1 → ‖a γ‖ < 1 := by
    intro γ hne
    refine lt_of_le_of_ne (hle γ) fun heq => hne (Subtype.ext ?_)
    exact GlobalTheory.T.eq_one_of_orthonormal_conj_block_upper_triangular E r X x0 ho γ.1 γ.2 ((GlobalTheory.T.norm_scalarPoincareDetRatio_lact_le_one E r X x0 ho γ.1 γ.2).2 heq)
  obtain ⟨k, hk, hne⟩ := GlobalTheory.T.exists_ge_tsum_pow_ne_zero_of_single_unit a 1 k0 ha1 hle hlt hsum (max N (k0 + 1))
  have hk0k : k0 ≤ k := le_trans (by omega) hk
  have hkpos : 0 < k := lt_of_lt_of_le (by omega) hk
  obtain ⟨τ0⟩ : Nonempty X.Ψ := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    by_cases hτ : τ ∈ X.Ψ
    · exact ⟨⟨τ, hτ⟩⟩
    · exact ⟨⟨_, not_not.mp ((X.cmType τ).not.mp hτ)⟩⟩
  have hB := (hpo k hk0k).2.1
  refine ⟨2 * k, le_trans (le_max_left _ _) (le_trans hk (by omega)), by omega, even_two_mul k, ?_⟩
  rw [hla k]
  refine ⟨poin X (laS X k) (qS X x0 k), ?_, ?_⟩
  · refine cuspStatement_holds r X (laS X k) τ0 hp0 hpr (fun i j hij hjp => ?_) (fun i0 i1 h0 h1 => ?_) _ hB
    · simp only [laS]
      split_ifs with h1 h2 <;> omega
    · simp only [laS]
      rw [if_neg (by omega), if_pos (by omega)]
      omega
  · rw [hB.1.2.1 x0 hx0 b hb]
    refine mul_ne_zero ?_ ?_
    · unfold bchar
      exact Finset.prod_ne_zero_iff.mpr fun τ _ => Finset.prod_ne_zero_iff.mpr fun i _ =>
        zpow_ne_zero _ (FrameDegreeData.bdiag_ne X hb τ i)
    · unfold poin
      simp_rw [hterm k]
      exact hne
end
end
