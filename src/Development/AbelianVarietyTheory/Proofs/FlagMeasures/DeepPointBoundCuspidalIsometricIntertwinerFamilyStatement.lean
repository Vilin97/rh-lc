module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsProjOnOne
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.DeepKernelBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalLatticeFiltrationSizeProperties
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountHypPAtAddQAt
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DeepRegionExponents
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.OrthonormalPlaceBasis
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesStepBoundOfCountingHypotheses
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointMajorantFramesGiveMajorants
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizeRightTranslateLowerBoun
import Formalism.HarderNarasimhan.ShiftInvariance
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingReindex
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StepBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentOrbitCover
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesStepBoundOfCountingHypothesesStatement

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.discreteSeries_stepBound_of_countingHypotheses : ∀ (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ), 8 ≤ n₀ → CountHyp B Cg n₀ d p q b → ∀ P : ℕ, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.StepBoundAt B b P := by
  first | exact @GlobalTheory.Dec.stepBoundAt_of_countHyp | exact GlobalTheory.Dec.stepBoundAt_of_countHyp | (intros; apply GlobalTheory.Dec.stepBoundAt_of_countHyp <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.HalfTruncatedLeastLatticeSizeLeUnipotentNeighbou

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Deep Formalism.HN
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.OmegaLeast


open scoped Matrix.Norms.L2Operator in
theorem opNorm_le_sqrt_hs {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : ‖A‖ ≤ Real.sqrt (Formalism.REAL.hs A) := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  have hhs : 0 ≤ Formalism.REAL.hs A := by unfold Formalism.REAL.hs; positivity
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, ← Real.sqrt_mul hhs]
  apply Real.sqrt_le_sqrt
  unfold Formalism.REAL.hs
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : ‖∑ j, A i j * x j‖ ≤ ∑ j, ‖A i j‖ * ‖x j‖ :=
    (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => norm_mul _ _))
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖A i j‖) (fun j => ‖x j‖)
  refine le_trans ?_ h2
  exact pow_le_pow_left₀ (norm_nonneg _) h1 2


open scoped Matrix.Norms.L2Operator in
theorem opNorm_exp_le {n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖NormedSpace.exp A‖ ≤ Real.exp ‖A‖ := by
  have h1 : ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ = 1 := GlobalTheory.LeastVar.opN_one hn
  haveI : NormOneClass (Matrix (Fin n) (Fin n) ℂ) := ⟨h1⟩
  have h := NormedSpace.expSeries_hasSum_exp (𝕂 := ℂ) A
  have h' := NormedSpace.expSeries_hasSum_exp (𝕂 := ℝ) ‖A‖
  rw [Real.exp_eq_exp_ℝ]
  refine h.norm_le_of_bounded h' fun k => ?_
  rw [NormedSpace.expSeries_apply_eq, NormedSpace.expSeries_apply_eq, norm_smul, smul_eq_mul]
  gcongr
  · simp
  · exact norm_pow_le _ _

open scoped Matrix.Norms.L2Operator in
theorem dOp_exp_mul_exp_le {n : ℕ} (hn : 1 ≤ n) (A Z : Matrix (Fin n) (Fin n) ℂ) :
    dOp (NormedSpace.exp A * NormedSpace.exp Z) ≤
      Real.sqrt (Formalism.REAL.hs A) + Real.sqrt (Formalism.REAL.hs Z) := by
  have h : ‖NormedSpace.exp A * NormedSpace.exp Z‖ ≤
      Real.exp (Real.sqrt (Formalism.REAL.hs A) + Real.sqrt (Formalism.REAL.hs Z)) := by
    rw [Real.exp_add]
    refine (norm_mul_le _ _).trans ?_
    gcongr
    · exact (opNorm_exp_le hn A).trans (Real.exp_le_exp.2 (opNorm_le_sqrt_hs A))
    · exact (opNorm_exp_le hn Z).trans (Real.exp_le_exp.2 (opNorm_le_sqrt_hs Z))
  change Real.log ‖NormedSpace.exp A * NormedSpace.exp Z‖ ≤ _
  rcases (norm_nonneg (NormedSpace.exp A * NormedSpace.exp Z)).eq_or_lt with h0 | h0
  · rw [← h0, Real.log_zero]; positivity
  · exact (Real.log_le_iff_le_exp h0).2 h

theorem half_truncatedLeastLatticeSize_le_unipotentNeighbourhood : ∀ (I : AutInst) (x : I.GA) (W : Submodule I.E (Fin I.n → I.E)) (ρ : ℝ), 1 ≤ I.n → ρ ≤ Real.log 2 → ∀ y ∈ omega I x W ρ, tau1 I x / 2 ≤ tau1 I y := by
  intro I x W ρ hn hρ y hy
  obtain ⟨h2, A, Z, -, hAZ, hy1, -⟩ := hy
  obtain ⟨-, -, -, -, -, ⟨K, hK⟩, -⟩ := GlobalTheory.CongTop.adelic_topology I
  have hk : (x⁻¹ * y).2 ∈ I.Kset := by
    have : (x⁻¹ * y).2 = 1 := by simp [h2]
    rw [this, ← hK]; exact K.one_mem
  have hv := GlobalTheory.LeastVar.truncatedLeastLatticeSize_rightTranslate_lower_bound I hn x (x⁻¹ * y) hk
  rw [mul_inv_cancel_left] at hv
  have hcard := (GlobalTheory.Count.FrameMajorant.frames_give_majorants I x).2.2.1
  have hfpos : (0 : ℝ) < I.f := by
    rw [← hcard]; exact_mod_cast Fintype.card_pos
  have hhs : ∀ B : Matrix (Fin I.n) (Fin I.n) ℂ, 0 ≤ Formalism.REAL.hs B := fun B => by
    unfold Formalism.REAL.hs; positivity
  have hd : ∀ v, dOp (uMat ((x⁻¹ * y).1 v)) ≤ Real.log 2 := by
    intro v
    have e : uMat ((x⁻¹ * y).1 v) = NormedSpace.exp (A v) * NormedSpace.exp (Z v) := by
      have e1 : uMat ((x⁻¹ * y).1 v) = uMat ((x.1 v)⁻¹) * uMat (y.1 v) := by simp [uMat]
      have e2 : uMat ((x.1 v)⁻¹) * uMat (x.1 v) = 1 := by simp [uMat]
      rw [e1, hy1 v, Matrix.mul_assoc, ← Matrix.mul_assoc, e2, Matrix.one_mul]
    rw [e]
    refine (dOp_exp_mul_exp_le hn _ _).trans (le_trans ?_ (hAZ.trans hρ))
    gcongr
    · exact Finset.single_le_sum (f := fun v => Formalism.REAL.hs (A v)) (fun v _ => hhs _) (Finset.mem_univ v)
    · exact Finset.single_le_sum (f := fun v => Formalism.REAL.hs (Z v)) (fun v _ => hhs _) (Finset.mem_univ v)
  have hs : (∑ v, dOp (uMat ((x⁻¹ * y).1 v))) / I.f ≤ Real.log 2 := by
    rw [div_le_iff₀ hfpos]
    refine (Finset.sum_le_sum fun v _ => hd v).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul, mul_comm]
  have he : (1 / 2 : ℝ) ≤ Real.exp (-((∑ v, dOp (uMat ((x⁻¹ * y).1 v))) / I.f)) := by
    have : (1 / 2 : ℝ) = Real.exp (-Real.log 2) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
    rw [this]
    exact Real.exp_le_exp.2 (neg_le_neg hs)
  have ht : 0 ≤ tau1 I x := by
    obtain ⟨-, hfg, hspan, -, -⟩ := GlobalTheory.T.autPointLatticeIntersection_selfDual_properties I x
    haveI := (GlobalTheory.Count.FrameMajorant.frames_give_majorants I x).1
    have hx := (GlobalTheory.Count.FrameMajorant.frames_give_majorants I x).2.2.2.2
    have hne : lamX I x ≠ ⊥ := by
      intro h
      haveI : Nonempty (Fin I.n) := ⟨⟨0, hn⟩⟩
      rw [h] at hspan
      simp at hspan
    have h3 := (sizeMu I.E _ _ (bas I) (frm I x) (fun w => (hx w).1) (lamX I x) hfg hne).2.2.2.1
    unfold tau1 least
    rw [h3]
    exact le_min (by norm_num) (Real.exp_pos _).le
  have := mul_le_mul_of_nonneg_left he ht
  linarith

end GlobalTheory.OmegaLeast
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.DeepPointBoundCuspidalIsometricIntertwinerFamily

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Deep GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.DeepFamilyGap

theorem one_mem_NA (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)) : (1 : I.GA) ∈ I.NA W := by
  unfold AutInst.NA
  refine ⟨fun v => ?_, ?_⟩
  · have hdet : IsUnit (I.P v).det := by
      first
      | exact (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)
      | exact I.P_unit v
    have hg : I.P v * uMat ((1 : I.GA).1 v) * (I.P v)⁻¹ = 1 := by
      rw [show uMat ((1 : I.GA).1 v) = 1 from rfl, mul_one]
      exact Matrix.mul_nonsing_inv _ hdet
    rw [hg]
    unfold AutInst.InUnipRad
    simp
    intro x _
    unfold Formalism.UG.hform
    simp
  · have hf : I.fmat (1 : I.GA).2 = 1 := by
      first
      | rfl
      | simp
      | exact map_one _
    rw [hf]
    unfold AutInst.InUnipRad
    simp
    intro x _
    unfold Formalism.UG.hform
    simp

theorem self_mem_omega (I : AutInst) (x : I.GA) (W : Submodule I.E (Fin I.n → I.E)) {ρ : ℝ} (h : 0 ≤ ρ) :
    x ∈ omega I x W ρ := by
  refine ⟨rfl, fun _ => 0, fun _ => 0, fun v => ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie (I.ε v)).zero_mem,
    (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie (I.ε v)).zero_mem⟩, ?_, fun v => by simp, fun s t => ⟨1, ?_, fun v => ?_⟩⟩
  · simpa [GlobalTheory.SobolevBound.hs_eq_trace] using h
  · exact one_mem_NA I W
  · rw [smul_zero, smul_zero, NormedSpace.exp_zero, mul_one, mul_one]
    exact one_mul _

theorem beP_nonneg (n : ℕ) (b : ℝ) (P : ℕ) : 0 ≤ beP n b P := by
  unfold beP
  positivity

theorem monotone₂ (n : ℕ) (b : ℝ) {P Q : ℕ} (h : P ≤ Q) : beP n b P ≤ beP n b Q := by
  unfold beP
  have : (P : ℝ) ≤ Q := by exact_mod_cast h
  linarith

theorem iterate (B : RowsAut) (b ρ M β : ℝ) (P₀ : ℕ) (D : ℕ)
    (T : Fin D → (B.Hs →L[ℂ] B.I.L2 B.μf B.fund)) (Fr : Fin D → B.Hs → B.I.GA → ℂ) (x : B.I.GA)
    (W : Submodule B.I.E (Fin B.I.n → B.I.E)) (hg : 1 ≤ B.g) (hW : B.I.IsIsot W)
    (hcov : ∀ ν : B.I.Ginf, ((ν, 1) : B.I.GA) ∈ B.I.NA W → ∃ γ ∈ B.I.GFset, ∃ k ∈ B.I.Kg B.g,
      ∃ y ∈ omega B.I x W ρ, ((ν, 1) : B.I.GA) * x = γ * y * (1, k))
    (hS : ∀ P, StepBoundAt B b P) (hR : ∀ i, IsReps B (T i) (Fr i))
    (hC : ∀ i u, B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext (T i u))) (hρ : 0 ≤ ρ) (hM : 0 ≤ M)
    (hβ : beP B.I.n b P₀ ≤ β)
    (h0 : ∀ y ∈ omega B.I x W ρ, ∀ u ∈ VP B P₀, ‖vv B Fr u y‖ ≤ M * ‖u‖) :
    ∀ k P : ℕ, P + k = P₀ → ∀ y ∈ omega B.I x W ρ, ∀ u ∈ VP B P,
      ‖vv B Fr u y‖ ≤ (2 * ρ * Real.sqrt B.I.f * β) ^ k * M * ‖u‖ := by
  have hβ0 : 0 ≤ β := le_trans (beP_nonneg _ _ _) hβ
  have hc0 : 0 ≤ 2 * ρ * Real.sqrt B.I.f * β :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hρ) (Real.sqrt_nonneg _)) hβ0
  intro k
  induction k with
  | zero =>
    intro P hP y hy u hu
    have hPP : P = P₀ := by simpa using hP
    subst hPP
    simpa using h0 y hy u hu
  | succ k ih =>
    intro P hP y hy u hu
    have hP' : (P + 1) + k = P₀ := by omega
    have hM' : 0 ≤ (2 * ρ * Real.sqrt B.I.f * β) ^ k * M := mul_nonneg (pow_nonneg hc0 _) hM
    have key := GlobalTheory.DeepStep.step_bound B b ρ ((2 * ρ * Real.sqrt B.I.f * β) ^ k * M) P D T Fr x W hg hW
      hcov (hS P) hR hC hM' (ih (P + 1) hP') y hy u hu
    have hle : beP B.I.n b P ≤ β := le_trans (monotone₂ _ _ (by omega : P ≤ P₀)) hβ
    calc ‖vv B Fr u y‖
        ≤ 2 * ρ * Real.sqrt B.I.f * beP B.I.n b P * ((2 * ρ * Real.sqrt B.I.f * β) ^ k * M) * ‖u‖ := key
      _ ≤ 2 * ρ * Real.sqrt B.I.f * β * ((2 * ρ * Real.sqrt B.I.f * β) ^ k * M) * ‖u‖ := by
          gcongr
      _ = (2 * ρ * Real.sqrt B.I.f * β) ^ (k + 1) * M * ‖u‖ := by ring

theorem mult_le {n τ t : ℝ} (hn : 1 ≤ n) (hτ : 0 < τ) (hτ1 : τ < 1 / 2) (ht : τ / 2 ≤ t) :
    1 + 4 * Real.sqrt n / t ^ 2 ≤ 17 * Real.sqrt n / τ ^ 2 := by
  have hs : 1 ≤ Real.sqrt n := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hn
  have ht0 : 0 < t := by linarith
  have hτt : τ ^ 2 ≤ 4 * t ^ 2 := by nlinarith
  have h1 : 4 * Real.sqrt n / t ^ 2 ≤ 16 * Real.sqrt n / τ ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have h2 : 1 ≤ Real.sqrt n / τ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have h3 : 17 * Real.sqrt n / τ ^ 2 = 16 * Real.sqrt n / τ ^ 2 + Real.sqrt n / τ ^ 2 := by ring
  linarith

theorem deep_bound_family : ∀ (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ) (c : InfinitePlace B.I.F → ℝ) (x : B.I.GA) (D : ℕ) (T : Fin D → (B.Hs →L[ℂ] B.I.L2 B.μf B.fund)) (Fr : Fin D → B.Hs → B.I.GA → ℂ), 8 ≤ n₀ → 1 ≤ q → CountHyp B Cg n₀ d p q b → (∀ v, IsGauge (B.I.ε v) (c v)) → least B.I x < tauStar B q b → (∀ i, IsReps B (T i) (Fr i)) → (∀ i u, ‖T i u‖ = ‖u‖) → (∀ i u, B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext (T i u))) → ‖vv B Fr (B.tens B.w) x‖ ^ 2 ≤ (2 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh B q (least B.I x) * Real.sqrt B.I.f * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B)) ^ (16 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) * (6 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B)) ^ GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B * Real.exp B.I.f * (17 * Real.sqrt B.I.n / least B.I x ^ 2) ^ (2 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) * (D : ℝ) * (∏ v, c v) / (B.μf (B.I.Kg B.g)).toReal := by
  intro B Cg n₀ d p q b c x D T Fr hn₀ hq hCH hc hτ hR hiso hcusp
  obtain ⟨hDS, -, hn₀n, hq2, -, -, hb2, -, -, hg, -⟩ := id hCH
  obtain ⟨-, hrd, hf, -, -, -, hrk, -, -, -, -, htau, -⟩ :=
    GlobalTheory.Dec.countHyp_numerics B Cg n₀ d p q b hn₀ hCH
  obtain ⟨htau2, hb19⟩ := htau hq
  have hn8 : 8 ≤ B.I.n := le_trans hn₀ hn₀n
  have hn1 : 1 ≤ B.I.n := by omega
  have hτpos : 0 < least B.I x :=
    ((GlobalTheory.CountSteps.steps B.I x 1 one_pos).2.2.2.2.2.2.2.2 hn1).1
  have hτhalf : least B.I x < 1 / 2 := lt_trans hτ htau2
  have hτ1 : tau1 B.I x = least B.I x := min_eq_right hτhalf.le
  obtain ⟨W, hW, hcov⟩ := GlobalTheory.DeepCover.unipotent_orbit_cover B.I x B.g q hg hn1
    (fun v => (hrk v).le) hτhalf
  have hτX : least B.I x ≤ ((B.I.n : ℝ) * B.I.f * B.I.rd * B.g * b)⁻¹ ^ (11 * q) := hτ.le
  have hex := GlobalTheory.deep_region_exponents B.I.n B.I.f q B.I.rd B.g b (least B.I x) hn8 hf hq hq2 hrd hb2
    (by exact_mod_cast hg) hτpos hτX
  have hrho : GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh B q (least B.I x) ≤ Real.log 2 := hex.1
  have hρ0 : 0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh B q (least B.I x) := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh
    have hg0 : (1 : ℝ) ≤ B.g := by exact_mod_cast hg
    exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
      (Real.sqrt_nonneg _)) (by linarith)) (by linarith)) (Real.rpow_nonneg (by linarith) _))
      (by norm_num)
  have hS : ∀ P, StepBoundAt B b P := GlobalTheory.T.discreteSeries_stepBound_of_countingHypotheses B Cg n₀ d p q b hn₀ hCH
  have hβ : beP B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + B.I.n ^ 2 * B.I.f) =
      GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) := rfl
  have hβ0 : 0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) := by
    rw [← hβ]; exact beP_nonneg _ _ _
  have hβle : beP B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) ≤
      GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) := by
    rw [← hβ]; exact monotone₂ _ _ (Nat.le_add_right _ _)
  have hc0 : 0 < ∏ v, c v := Finset.prod_pos fun v _ => GlobalTheory.SobolevBound.gauge_pos (hc v)
  have hN : B.I.n ^ 2 * B.I.f = GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B := rfl
  have hK0 : 0 ≤ (6 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B)) ^ GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B * Real.exp B.I.f * (17 * Real.sqrt B.I.n / least B.I x ^ 2) ^ (2 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) * (D : ℝ) * (∏ v, c v) / (B.μf (B.I.Kg B.g)).toReal :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (by linarith) _)
      (Real.exp_pos _).le) (pow_nonneg (by positivity) _)) (Nat.cast_nonneg _)) hc0.le)
      ENNReal.toReal_nonneg
  have h0 : ∀ y ∈ omega B.I x W (GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh B q (least B.I x)),
      ∀ u ∈ VP B (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B), ‖vv B Fr u y‖ ≤
        Real.sqrt ((6 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B)) ^ GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B * Real.exp B.I.f * (17 * Real.sqrt B.I.n / least B.I x ^ 2) ^ (2 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) * (D : ℝ) * (∏ v, c v) / (B.μf (B.I.Kg B.g)).toReal) * ‖u‖ := by
    intro y hy u hu
    have hs := GlobalTheory.SobolevBound.sobolev_bound B b c (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) D T Fr hn8 hg hb19 hc hS
      hR hiso y u hu
    rw [hβ, hN] at hs
    have ht : least B.I x / 2 ≤ tau1 B.I y := by
      rw [← hτ1]; exact GlobalTheory.OmegaLeast.half_truncatedLeastLatticeSize_le_unipotentNeighbourhood B.I x W _ hn1 hrho y hy
    have hm := mult_le (n := (B.I.n : ℝ)) (by exact_mod_cast hn1) hτpos hτhalf ht
    have hle : ‖vv B Fr u y‖ ^ 2 ≤ ((6 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B)) ^ GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B * Real.exp B.I.f * (17 * Real.sqrt B.I.n / least B.I x ^ 2) ^ (2 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) * (D : ℝ) * (∏ v, c v) / (B.μf (B.I.Kg B.g)).toReal) * ‖u‖ ^ 2 := by
      refine hs.trans ?_
      gcongr
    have := Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul hK0, Real.sqrt_sq (norm_nonneg _)] at this
  have key := GlobalTheory.DeepFamilyGap.iterate B b (GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh B q (least B.I x)) _ _
    (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) D T Fr x W hg hW hcov hS hR hcusp hρ0 (Real.sqrt_nonneg _) hβle h0
    (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) 0 (by simp) x (self_mem_omega B.I x W hρ0) (B.tens B.w)
    (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.tens_w_mem B hDS 0).1
  rw [(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.tens_w_mem B hDS 0).2, mul_one] at key
  have hA0 : 0 ≤ 2 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh B q (least B.I x) * Real.sqrt B.I.f *
      GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hρ0) (Real.sqrt_nonneg _)) hβ0
  have hsq := pow_le_pow_left₀ (norm_nonneg _) key 2
  rw [mul_pow, ← pow_mul, Real.sq_sqrt hK0] at hsq
  refine hsq.trans (le_of_eq ?_)
  rw [show 8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B * 2 = 16 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B by ring]
  ring

end GlobalTheory.DeepFamilyGap
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.DeepPointBoundCuspidalIsometricIntertwinerFamilyStatement

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Deep GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.deepPoint_bound_cuspidalIsometricIntertwinerFamily : ∀ (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ) (c : InfinitePlace B.I.F → ℝ) (x : B.I.GA) (D : ℕ) (T : Fin D → (B.Hs →L[ℂ] B.I.L2 B.μf B.fund)) (Fr : Fin D → B.Hs → B.I.GA → ℂ), 8 ≤ n₀ → 1 ≤ q → CountHyp B Cg n₀ d p q b → (∀ v, IsGauge (B.I.ε v) (c v)) → least B.I x < tauStar B q b → (∀ i, IsReps B (T i) (Fr i)) → (∀ i u, ‖T i u‖ = ‖u‖) → (∀ i u, B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext (T i u))) → ‖vv B Fr (B.tens B.w) x‖ ^ 2 ≤ (2 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh B q (least B.I x) * Real.sqrt B.I.f * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B)) ^ (16 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) * (6 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B)) ^ GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B * Real.exp B.I.f * (17 * Real.sqrt B.I.n / least B.I x ^ 2) ^ (2 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) * (D : ℝ) * (∏ v, c v) / (B.μf (B.I.Kg B.g)).toReal := by
  first | exact @GlobalTheory.DeepFamilyGap.deep_bound_family | exact GlobalTheory.DeepFamilyGap.deep_bound_family | (intros; apply GlobalTheory.DeepFamilyGap.deep_bound_family <;> assumption)
end
end
