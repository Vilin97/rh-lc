module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedAtlasSmoothPotentialLocalStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HasStepCharts
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapHolomorphicPullbackFirst
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
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapHolomorphicPullbackFourth
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapHolomorphicPullbackSecond
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapHolomorphicPullbackThird
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapPullbackFirst
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapPullbackSecondStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapPullbackThirdStatement
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices.InstFintypeFlIdx
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FubiniStudyMetricSmooth
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SelM
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.MaIntEmpty
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFubiniStudyPositiveStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SingularPotentialLogGrowthPshStatement

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapHolomorphicPullbackFirstStatement

section

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical


theorem _root_.GlobalTheory.T.flag_gap_holomorphic_pullback_first : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr), HasStepCharts M BM p κ v R pr → IsPotential R.A (potOf R (fsHerm ιk fun k => M.dy p (κ k))) → R.A.SmoothOn (bdry (fun x y => BM.s (pr x) (pr y)))ᶜ (stepPh M BM p v R pr) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CWeight.smoothOn_stepPh | exact GlobalTheory.CompanionTheory.Ar.PB.CWeight.smoothOn_stepPh | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CWeight.smoothOn_stepPh <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapHolomorphicPullbackFourthStatement

section

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical


theorem _root_.GlobalTheory.T.flag_gap_holomorphic_pullback_fourth : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr), HasStepCharts M BM p κ v R pr → IsPotential R.A (potOf R (fsHerm ιk fun k => M.dy p (κ k))) → ∀ x, ∃ (ψ : OpenPartialHomeomorph R.X (Fin e → ℂ)) (V : Set R.X) (c : ℝ), IsCompatChart R.A ψ ∧ IsOpen V ∧ x ∈ V ∧ V ⊆ ψ.source ∧ ∀ x' ∈ V, x' ∉ bdry (fun x y => BM.s (pr x) (pr y)) → ‖fderiv ℝ (stepPh M BM p v R pr ∘ ψ.symm) (ψ x')‖ ≤ c * rW (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x' ^ c * Real.exp (rW (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x' / 2) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.StepW.GradLoc.stepPh_grad_local | exact GlobalTheory.CompanionTheory.Ar.PB.StepW.GradLoc.stepPh_grad_local | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.StepW.GradLoc.stepPh_grad_local <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapHolomorphicPullbackSecondStatement

section

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical


theorem _root_.GlobalTheory.T.flag_gap_holomorphic_pullback_second : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr), HasStepCharts M BM p κ v R pr → IsPshOn R.A (bdry (fun x y => BM.s (pr x) (pr y)))ᶜ (potOf R (fsHerm ιk fun k => M.dy p (κ k)) + LocPot.ofFun (stepPh M BM p v R pr)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.StepW.PshW.isPshOn_stepPot | exact GlobalTheory.CompanionTheory.Ar.PB.StepW.PshW.isPshOn_stepPot | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.StepW.PshW.isPshOn_stepPot <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapHolomorphicPullbackThirdStatement

section

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical


theorem _root_.GlobalTheory.T.flag_gap_holomorphic_pullback_third : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr), HasStepCharts M BM p κ v R pr → IsPotential R.A (potOf R (fsHerm ιk fun k => M.dy p (κ k))) → ∃ C₁ : ℝ, ∀ x ∉ bdry (fun x y => BM.s (pr x) (pr y)), |stepPh M BM p v R pr x| ≤ C₁ * Real.log (rW (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.StepW.WeightSize.stepPh_le_log | exact GlobalTheory.CompanionTheory.Ar.PB.StepW.WeightSize.stepPh_le_log | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.StepW.WeightSize.stepPh_le_log <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapPullbackFirstStatement

section

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical


theorem _root_.GlobalTheory.T.flag_gap_pullback_first : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X), IsStepHyp M BM p κ v R pr → ∀ (x y' : R.X) (z : (Σ k, ι k) → ℂ), y' ∈ R.U x → pr y' ∉ bdry BM.s → z ∈ mcPts (mCoordIdeal y) → z ∘ v = R.lift x y' → stepPh M BM p v R pr y' = stepGap M BM p z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.StepW.Wgt.main | exact GlobalTheory.CompanionTheory.Ar.PB.StepW.Wgt.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.StepW.Wgt.main <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.FubiniStudyMetricSmoothStatement

section

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical


theorem _root_.GlobalTheory.T.fubini_study_metric_smooth : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (a : K → ℤ), IsSmoothHerm (fsHerm ι a) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.StepW.fsHerm_isSmoothHerm | exact GlobalTheory.CompanionTheory.Ar.PB.StepW.fsHerm_isSmoothHerm | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.StepW.fsHerm_isSmoothHerm <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.PartialFlagBundleMetricLine

section

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem stepWeight_exists : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)), IsBlockMap κ v → (∀ k, ((∀ p', M.blk p' ≠ some k) ∨ M.blk p = some k) → k ∈ Set.range κ) → ∀ (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr) (B : FinHolAtlas e R.X), (∀ x, ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x ∧ SameOrbit (basePart M.blk z) (BM.Rb.lift (pr x) (pr x))) → IsPotential R.A (BM.L.pullback pr hp.1) → IsSection R.A (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) → IsSNC R.A (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) BM.m (fun k => pr ⁻¹' BM.W k) → IsAdaptedAtlas R.A B (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) → ∃ (ph : R.X → ℝ) (C₅ : ℝ), (∀ x, pr x ∉ bdry BM.s → ∀ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x → Real.log ((BM.hom p).h z) = Real.log ((fsHerm ι (M.dy p)).h z) + ph x) ∧ (∀ x x', pr x = pr x' → (∀ k (m : ιk k), M.blk p = some (κ k) → ∃ a : ℂ, ∀ m' : ιk k, R.lift x x ⟨k, m'⟩ = a * R.lift x' x' ⟨k, m'⟩) → ph x = ph x') ∧ IsSingWeight R.A (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) (potOf R (fsHerm ιk fun k => M.dy p (κ k))) ph C₅ ∧ IsGradBound B (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) ph C₅ := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM p Kk _ ιk _ κ v hb hr e R pr hp B h1 hpot hsec hsnc had
  have hyp : IsStepHyp M BM p κ v R pr := ⟨hb, hr, hp, h1⟩
  have hc := GlobalTheory.T.flag_gap_pullback_third K ι Φ y Ψ N j M n BM p Kk ιk κ v e R pr hyp
  have hfs : IsPotential R.A (potOf R (fsHerm ιk fun k => M.dy p (κ k))) :=
    (GlobalTheory.T.log_resolution_fubini_study_positive Kk ιk _ e R).1 _ (GlobalTheory.T.fubini_study_metric_smooth Kk ιk _)
  have hnorm : ∀ x, logNormSec (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x ≤ 0 :=
    fun x => BM.norm_le (pr x)
  have hsm := GlobalTheory.T.flag_gap_holomorphic_pullback_first K ι Φ y Ψ N j M n BM p Kk ιk κ v e R pr hp hc hfs
  have hps := GlobalTheory.T.flag_gap_holomorphic_pullback_second K ι Φ y Ψ N j M n BM p Kk ιk κ v e R pr hp hc
  obtain ⟨C₁, hC₁⟩ := GlobalTheory.T.flag_gap_holomorphic_pullback_third K ι Φ y Ψ N j M n BM p Kk ιk κ v e R pr hp hc hfs
  have hgr := GlobalTheory.T.flag_gap_holomorphic_pullback_fourth K ι Φ y Ψ N j M n BM p Kk ιk κ v e R pr hp hc hfs
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.T.singular_potential_log_growth_psh e R.X R.A (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) BM.nb BM.m
    (fun k => pr ⁻¹' BM.W k) hpot hsec hsnc hnorm _ (stepPh M BM p v R pr) C₁ hfs hsm hps hC₁
  obtain ⟨C₃, hC₃⟩ := GlobalTheory.T.adapted_atlas_smooth_potential_local e R.X R.A B (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) BM.nb BM.m
    (fun k => pr ⁻¹' BM.W k) hpot hsec hsnc hnorm had (stepPh M BM p v R pr) hsm hgr
  refine ⟨stepPh M BM p v R pr, max C₂ C₃, ?_, ?_, ?_, hC₃ _ (le_max_right _ _)⟩
  · intro x hx z hz hzv
    have := GlobalTheory.T.flag_gap_pullback_first K ι Φ y Ψ N j M n BM p Kk ιk κ v e R pr hyp x x z (R.mem_U x) hx hz hzv
    rw [this, stepGap]
    ring
  · intro x x' hxx hk
    exact GlobalTheory.T.flag_gap_pullback_second K ι Φ y Ψ N j M n BM p Kk ιk κ v e R pr hyp x x' hxx hk
  · obtain ⟨h1', h2', h3', h4'⟩ := hC₂
    refine ⟨h1', h2', h3', fun x hx => ?_⟩
    have hlog : 0 ≤ Real.log (rW (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x) := by
      apply Real.log_nonneg
      have := hnorm x
      have h2 := Real.add_one_le_exp (1 : ℝ)
      unfold rW
      linarith
    obtain ⟨ha, hb'⟩ := h4' x hx
    refine ⟨?_, hb'.trans (le_max_left _ _)⟩
    have : -max C₂ C₃ * Real.log (rW (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x) ≤
        -C₂ * Real.log (rW (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x) :=
      mul_le_mul_of_nonneg_right (neg_le_neg (le_max_left _ _)) hlog
    exact this.trans ha

end GlobalTheory.CompanionTheory.Ar.PB
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.PartialFlagBundleMetricLineStatement

section

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem _root_.GlobalTheory.T.partial_flag_bundle_metric_line : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)), IsBlockMap κ v → (∀ k, ((∀ p', M.blk p' ≠ some k) ∨ M.blk p = some k) → k ∈ Set.range κ) → ∀ (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr) (B : FinHolAtlas e R.X), (∀ x, ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x ∧ SameOrbit (basePart M.blk z) (BM.Rb.lift (pr x) (pr x))) → IsPotential R.A (BM.L.pullback pr hp.1) → IsSection R.A (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) → IsSNC R.A (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) BM.m (fun k => pr ⁻¹' BM.W k) → IsAdaptedAtlas R.A B (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) → ∃ (ph : R.X → ℝ) (C₅ : ℝ), (∀ x, pr x ∉ bdry BM.s → ∀ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x → Real.log ((BM.hom p).h z) = Real.log ((fsHerm ι (M.dy p)).h z) + ph x) ∧ (∀ x x', pr x = pr x' → (∀ k (m : ιk k), M.blk p = some (κ k) → ∃ a : ℂ, ∀ m' : ιk k, R.lift x x ⟨k, m'⟩ = a * R.lift x' x' ⟨k, m'⟩) → ph x = ph x') ∧ IsSingWeight R.A (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) (potOf R (fsHerm ιk fun k => M.dy p (κ k))) ph C₅ ∧ IsGradBound B (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) ph C₅ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.stepWeight_exists | exact GlobalTheory.CompanionTheory.Ar.PB.stepWeight_exists | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.stepWeight_exists <;> assumption)
end
end
