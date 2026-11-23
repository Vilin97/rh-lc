module

public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.CuspFrame
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.NearNonzeroTerms
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.FarTermSum
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.RareFlags
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.DeepSetBound
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.LatticeCountingTheorem
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
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
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutomorphicKernelConvergencePropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountHypPAtAddQAt
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteUnitaryGroupCountEqMainTermStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesCoefficientIntegrableMajorant
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalConvolutionOrthogonalProjectorProof
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrablePhStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NearAbsMeasurableAndSplit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizeRightTranslateLowerBoun
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.AbsIntegralSubConstMulLeOfSplit

section

@[expose] public section

open MeasureTheory

namespace GlobalTheory

theorem abs_integral_sub_const_mul_le_of_split :
    ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ] (M : Set X) (K : X → ℝ) (nr fr : X → ENNReal) (c a b e : ℝ), MeasurableSet M → Integrable K μ → (∀ x, 0 ≤ K x) → Measurable nr → 0 ≤ c → 0 ≤ a → 0 ≤ b → 0 ≤ e → (∀ x ∈ M, ENNReal.ofReal |K x - c| ≤ nr x + fr x) → ∫⁻ x in M, nr x ∂μ ≤ ENNReal.ofReal a → ∫⁻ x in M, fr x ∂μ ≤ ENNReal.ofReal b → ∫⁻ x in Mᶜ, ENNReal.ofReal (K x) ∂μ ≤ ENNReal.ofReal e → |∫ x, K x ∂μ - c * (μ Set.univ).toReal| ≤ a + b + c * (μ Mᶜ).toReal + e := by
  intro X _ μ _ M K nr fr c a b e hM hK hK0 hnr hc ha hb he hpt hna hfb hce
  have hsplit : ∫ x, K x ∂μ = ∫ x in M, K x ∂μ + ∫ x in Mᶜ, K x ∂μ :=
    (integral_add_compl hM hK).symm
  have hmeas : (μ Set.univ).toReal = (μ M).toReal + (μ Mᶜ).toReal := by
    rw [← measure_add_measure_compl hM,
      ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  have hintM : ∫ x in M, (K x - c) ∂μ = ∫ x in M, K x ∂μ - c * (μ M).toReal := by
    rw [integral_sub hK.integrableOn (integrable_const c), setIntegral_const, smul_eq_mul,
      measureReal_def, mul_comm]

  have h1 : |∫ x in M, (K x - c) ∂μ| ≤ a + b := by
    have hle : ∫⁻ x in M, ENNReal.ofReal ‖K x - c‖ ∂μ ≤ ENNReal.ofReal (a + b) := by
      calc ∫⁻ x in M, ENNReal.ofReal ‖K x - c‖ ∂μ ≤ ∫⁻ x in M, (nr x + fr x) ∂μ := by
            apply lintegral_mono_ae
            filter_upwards [ae_restrict_mem hM] with x hx
            simpa [Real.norm_eq_abs] using hpt x hx
        _ = ∫⁻ x in M, nr x ∂μ + ∫⁻ x in M, fr x ∂μ := lintegral_add_left hnr _
        _ ≤ ENNReal.ofReal a + ENNReal.ofReal b := add_le_add hna hfb
        _ = ENNReal.ofReal (a + b) := (ENNReal.ofReal_add ha hb).symm
    have hn := norm_integral_le_lintegral_norm (μ := μ.restrict M) (fun x => K x - c)
    rw [Real.norm_eq_abs] at hn
    exact hn.trans (ENNReal.toReal_le_of_le_ofReal (add_nonneg ha hb) hle)

  have h2 : ∫ x in Mᶜ, K x ∂μ ≤ e := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hK0)
      hK.integrableOn.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal he hce
  have h3 : 0 ≤ ∫ x in Mᶜ, K x ∂μ := integral_nonneg fun x => hK0 x
  have h4 : 0 ≤ c * (μ Mᶜ).toReal := mul_nonneg hc ENNReal.toReal_nonneg
  have key : ∫ x, K x ∂μ - c * (μ Set.univ).toReal =
      ∫ x in M, (K x - c) ∂μ + (∫ x in Mᶜ, K x ∂μ - c * (μ Mᶜ).toReal) := by
    rw [hsplit, hmeas, hintM]; ring
  rw [key]
  calc _ ≤ |∫ x in M, (K x - c) ∂μ| + |∫ x in Mᶜ, K x ∂μ - c * (μ Mᶜ).toReal| := abs_add_le _ _
    _ ≤ (a + b) + (c * (μ Mᶜ).toReal + e) := by
        gcongr
        rw [abs_le]; constructor <;> linarith
    _ = a + b + c * (μ Mᶜ).toReal + e := by ring

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.AbsSubLeExpNegSixteenthMul

section

@[expose] public section

open Matrix Finset Real

namespace GlobalTheory

theorem abs_sub_le_exp_neg_sixteenth_mul :
    ∀ (D Ds n f : ℝ), 0 ≤ D → 0 ≤ Ds → Real.exp 15 ≤ n → 1 ≤ f → |D - Ds| ≤ (2 * Real.exp (-(1 / 4) * n * f * Real.log n) + Real.exp (-n ^ 2 * f)) * Ds + Real.exp (-n ^ 2 * f) * D → |D - Ds| ≤ Real.exp (-(1 / 16) * n * f * Real.log n) * Ds := by
  intro D Ds n f hD hDs hn hf h
  have hn16 : (16:ℝ) ≤ n := by
    have := Real.add_one_le_exp (15:ℝ); linarith
  have hn0 : 0 < n := by linarith
  have hL : 15 ≤ Real.log n := by
    have := Real.log_le_log (Real.exp_pos 15) hn
    rwa [Real.log_exp] at this
  have hLn : Real.log n ≤ n := by
    have := Real.log_le_sub_one_of_pos hn0; linarith
  have hnf : 16 ≤ n * f := by nlinarith
  have ha : 240 ≤ n * f * Real.log n := by nlinarith
  have hnn : n * f * Real.log n ≤ n ^ 2 * f := by
    have := mul_le_mul_of_nonneg_left hLn (by linarith : (0:ℝ) ≤ n * f)
    nlinarith
  have hlog8 : Real.log 8 ≤ 7 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 8); linarith
  have hT8 : Real.exp (-(1 / 16) * n * f * Real.log n - Real.log 8) =
      Real.exp (-(1 / 16) * n * f * Real.log n) / 8 := by
    rw [Real.exp_sub, Real.exp_log (by norm_num)]
  have e1 : Real.exp (-(1 / 4) * n * f * Real.log n) ≤
      Real.exp (-(1 / 16) * n * f * Real.log n) / 8 := by
    rw [← hT8]; apply Real.exp_le_exp.mpr; nlinarith
  have e2 : Real.exp (-n ^ 2 * f) ≤ Real.exp (-(1 / 16) * n * f * Real.log n) / 8 := by
    rw [← hT8]; apply Real.exp_le_exp.mpr; nlinarith
  have hT1 : Real.exp (-(1 / 16) * n * f * Real.log n) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr; nlinarith
  have hδ0 : 0 ≤ Real.exp (-n ^ 2 * f) := (Real.exp_pos _).le
  have hδ : Real.exp (-n ^ 2 * f) ≤ 1 / 2 := by linarith
  have hX : 0 ≤ |D - Ds| := abs_nonneg _
  have hD' : D ≤ Ds + |D - Ds| := by have := le_abs_self (D - Ds); linarith
  have p1 := mul_le_mul_of_nonneg_left hD' hδ0
  have p2 := mul_le_mul_of_nonneg_right hδ hX
  have p3 := mul_le_mul_of_nonneg_right e1 hDs
  have p4 := mul_le_mul_of_nonneg_right e2 hDs
  nlinarith

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesCountingOfFiniteAndBounds

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CountSum

theorem countHyp_mono {B : RowsAut} {Cg : ℝ} {n₀ n₁ : ℕ} {d : InfinitePlace B.I.F → ℝ} {p q : ℕ} {b : ℝ}
    (h : CountHyp B Cg n₀ d p q b) (hn : n₁ ≤ n₀) : CountHyp B Cg n₁ d p q b :=
  ⟨h.1, h.2.1, hn.trans h.2.2.1, h.2.2.2⟩

theorem countingTheorem_of_finite_of_bounds :
    (∀ (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ), 8 ≤ n₀ →
      CountHyp B Cg n₀ d p q b → FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re)) →
    GlobalTheory.FlagMeas.FlagMeasureBound → GlobalTheory.Deep.PtBound →
    GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.NearModerate → GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.FarModerate → GlobalTheory.IndefiniteRowSideFullHecke.RareFlags.FlagRare →
    GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.DeepBound → GlobalTheory.IndefiniteRowSideFullHecke.LatticeCountingTheorem.CountingTheorem := by
  intro hfinC hflag hpt hnear hfar hrare hdeep Cg
  by_cases hC : 0 ≤ Cg
  swap
  · exact ⟨8, fun B d p q b h => absurd (GlobalTheory.Dec.countHyp_numerics B Cg 8 d p q b le_rfl h).1 hC⟩
  obtain ⟨n₁, hn₁⟩ := hnear Cg hC
  obtain ⟨n₂, hn₂⟩ := hfar Cg hC
  obtain ⟨n₃, hn₃⟩ := hrare
  obtain ⟨n₄, hn₄⟩ := hdeep Cg hC
  refine ⟨8 + n₁ + n₂ + n₃ + n₄ + ⌈Real.exp 15⌉₊, fun B d p q b H => ?_⟩
  have hfin := hfinC B Cg _ d p q b (by omega) H
  refine ⟨hfin, ?_⟩
  obtain ⟨-, -, hf1, -, hpq, h2q, hrk, hmin, hd, -, -, hts, h, -, hgap, -, h32, -, h120, -⟩ :=
    GlobalTheory.Dec.countHyp_numerics B Cg _ d p q b (by omega) H
  have H1 := countHyp_mono H (n₁ := n₁) (by omega)
  have H2 := countHyp_mono H (n₁ := n₂) (by omega)
  have H4 := countHyp_mono H (n₁ := n₄) (by omega)
  obtain ⟨hDS, hsig, hn, hq2, hrd, hlf, -, -, -, hg, -, hpr, h4, hsp, -⟩ := H
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · have e := GlobalTheory.T.definiteUnitaryGroup_count_eq_mainTerm B d p ⟨hDS, hsig, by omega, hg, hpr, h4, hsp⟩ hfin
    rw [← e, sub_self, abs_zero]
    positivity
  have hn1 : 1 ≤ B.I.n := by omega
  obtain ⟨hT, hL, hS, -⟩ := GlobalTheory.CongTop.adelic_topology B.I
  have : BorelSpace B.I.GA := inferInstance
  obtain ⟨-, -, hphe1, him, hre, -, hloc⟩ := hpt B d p q h hDS hsig hgap (by rw [hmin]; exact h120)
  obtain ⟨-, hv0, hvT, -⟩ := hflag B.I B.μf B.fund B.fund_spec p q hsig h2q 1 (fun _ => 1) le_rfl
    (fun _ => le_rfl) (by simpa using Nat.succ_le_of_lt hq) ∅ MeasurableSet.empty (Set.empty_subset _)
  obtain ⟨hc, hle, hint⟩ := GlobalTheory.Dec.PhMajProof.phMaj B d h hDS hloc
  have hI : Integrable (ph B d) (muInf B.I) := by
    have h0 := hint 0 le_rfl (fun v => Or.inr (by
      have h1 := h32 v
      rw [hrk v] at h1 ⊢
      have hs : 0 < Real.sqrt q := Real.sqrt_pos.2 (by exact_mod_cast hq)
      have hqn : (q : ℝ) < B.I.n := by exact_mod_cast (by omega : q < B.I.n)
      have hn0 : (0 : ℝ) < B.I.n := by exact_mod_cast hn1
      have := mul_lt_mul_of_pos_left hqn (mul_pos hs hn0)
      nlinarith))
    simp only [zero_mul, Real.exp_zero, mul_one] at h0
    exact h0.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall hle)
  obtain ⟨-, -, ⟨T, hT⟩, -⟩ := GlobalTheory.GlobProj.globalProj_holds B d hDS hI
  obtain ⟨-, Fc, -, -, -, hexp, hKi, hD, -⟩ := GlobalTheory.T.kernelB' B d h hDS hn1 hloc h32 hfin T hT
  obtain ⟨hsum, -⟩ := GlobalTheory.T.automorphicKernel_convergence_properties B d h hDS hn1 hloc h32
  obtain ⟨hmeas, hsplit⟩ := GlobalTheory.NearMeas.nearAbs_measurable_and_split B d hDS
  have hcl : Continuous (least B.I) := (GlobalTheory.LeastVar.least_variation_continuity B.I hn1).2.1
  set μ := (B.I.muA B.μf).restrict B.fund with hμ
  have : IsFiniteMeasure μ := ⟨by rw [hμ, Measure.restrict_apply_univ]; exact hvT⟩
  have hM : MeasurableSet {x | tauStar B q b ≤ least B.I x} :=
    (isClosed_le continuous_const hcl).measurableSet
  have hvol : 0 < B.I.vol B.μf B.fund := ENNReal.toReal_pos hv0.ne' hvT.ne
  have hc0 : 0 ≤ (∏ v, d v) * (B.e 1).re := mul_nonneg hd.le hre
  have hmain : mainTerm B d = (∏ v, d v) * (B.e 1).re * B.I.vol B.μf B.fund := by
    unfold mainTerm AutInst.Dstar; ring
  have hm0 : 0 ≤ mainTerm B d := hmain ▸ mul_nonneg hc0 hvol.le
  have e1 : {x | tauStar B q b ≤ least B.I x} ∩ B.fund = {x | x ∈ B.fund ∧ tauStar B q b ≤ least B.I x} :=
    Set.inter_comm _ _
  have e2 : {x | tauStar B q b ≤ least B.I x}ᶜ ∩ B.fund = GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.deepSet B q b := by
    ext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.deepSet, and_comm]
  have key := GlobalTheory.abs_integral_sub_const_mul_le_of_split B.I.GA μ {x | tauStar B q b ≤ least B.I x}
    (fun x => (kern B.I (phe B d) x x).re) (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d) (GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.farSum B d)
    ((∏ v, d v) * (B.e 1).re) (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearBound B d)
    (Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ))) * mainTerm B d)
    ((B.D : ℝ) * Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ)))) hM hKi.re
    (fun x => by
      simp only [hexp, Complex.re_sum]
      refine Finset.sum_nonneg fun i _ => ?_
      rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
      exact Complex.normSq_nonneg _)
    hmeas hc0 (mul_nonneg (Real.exp_pos _).le hm0) (mul_nonneg (Real.exp_pos _).le hm0) (by positivity)
    (fun x _ => by
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hsplit x (hsum x x).1)
      refine le_trans (le_of_eq ?_) (Complex.abs_re_le_norm _)
      rw [Complex.sub_re, hphe1, Complex.re_ofReal_mul])
    (by rw [hμ, Measure.restrict_restrict hM, e1]; exact hn₁ B d p q b hq H1)
    (by rw [hμ, Measure.restrict_restrict hM, e1]; exact hn₂ B d p q b hq H2)
    (by rw [hμ, Measure.restrict_restrict hM.compl, e2]; exact hn₄ B d p q b hq H4)
  have hKD : ∫ x, (kern B.I (phe B d) x x).re ∂μ = (B.D : ℝ) := by
    have := integral_re hKi
    rw [hD] at this
    simpa using this
  have hU : (μ Set.univ).toReal = B.I.vol B.μf B.fund := by
    rw [hμ, Measure.restrict_apply_univ]; rfl
  have hP : (μ {x | tauStar B q b ≤ least B.I x}ᶜ).toReal ≤
      Real.exp (-(1 / 4 * (B.I.n : ℝ) * (B.I.f : ℝ) * Real.log B.I.n)) * B.I.vol B.μf B.fund := by
    have h1 := hn₃ B p q hsig (by omega) hq2 hrd hlf
    unfold prob at h1
    rw [div_le_iff₀ hvol] at h1
    refine le_trans ?_ h1
    rw [hμ, Measure.restrict_apply hM.compl]
    refine ENNReal.toReal_mono ((measure_mono Set.inter_subset_right).trans_lt hvT).ne
      (measure_mono (Set.inter_subset_inter_left _ fun x hx => ?_))
    have hx' : ¬ tauStar B q b ≤ least B.I x := hx
    exact lt_trans (not_le.1 hx') (hts hq).1
  rw [hKD, hU, ← hmain] at key
  have hP' := mul_le_mul_of_nonneg_left hP hc0
  have hne : Real.exp 15 ≤ (B.I.n : ℝ) := Nat.ceil_le.1 (by omega)
  have fin := GlobalTheory.abs_sub_le_exp_neg_sixteenth_mul (B.D : ℝ) (mainTerm B d) B.I.n B.I.f (by positivity) hm0 hne
    (by exact_mod_cast hf1) (by
      refine key.trans ?_
      unfold GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearBound
      simp only [neg_mul]
      rw [hmain] at *
      nlinarith [hP'])
  simpa only [neg_mul] using fin

end GlobalTheory.CountSum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesCountingOfFiniteAndBoundsStatement

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.discreteSeries_counting_of_finite_and_bounds : (∀ (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ), 8 ≤ n₀ → CountHyp B Cg n₀ d p q b → FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re)) → GlobalTheory.FlagMeas.FlagMeasureBound → GlobalTheory.Deep.PtBound → GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.NearModerate → GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.FarModerate → GlobalTheory.IndefiniteRowSideFullHecke.RareFlags.FlagRare → GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.DeepBound → GlobalTheory.IndefiniteRowSideFullHecke.LatticeCountingTheorem.CountingTheorem := by
  first | exact @GlobalTheory.CountSum.countingTheorem_of_finite_of_bounds | exact GlobalTheory.CountSum.countingTheorem_of_finite_of_bounds | (intros; apply GlobalTheory.CountSum.countingTheorem_of_finite_of_bounds <;> assumption)
end
end
