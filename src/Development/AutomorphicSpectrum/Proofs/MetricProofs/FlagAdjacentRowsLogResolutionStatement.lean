module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackPullback
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsFibreChartIff
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseChartFlagAnalyticMapStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapHolomorphicPullbackFirst
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogNormNonvanishingAnalyticHarmonicStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularFunctionAnalyticOnChartStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.UnipotentValueNeZeroStatement
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
import Mathlib.Tactic.Linter.Style
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
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartSecondStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ElementaryFactorPropertiesStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartFifthStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartSixthStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartThirdStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreTwistedResolution

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartFourth

section

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem contDiffOn_alphaOf : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (X : Type) (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∀ p, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (alphaOf BM l H bp p) Un := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b ca cb hab hj hca hcb X q Un Gn ΦYn ΦWn l H bp hUn hF p
  obtain ⟨hH, hbpc, hchart, hpt, -⟩ := hF
  intro w hw
  have hbw : bp w ∈ BM.O l \ ReciprocityTheory.AnForm.P.bdry BM.s := (hpt w hw).1
  have hA : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u => GlobalTheory.CompanionTheory.Ar.PB.blockPot j p.2 (BM.G l p.1 (bp u)) (H p.1 u)) w := by
    refine GlobalTheory.CompanionTheory.Ar.PB.CWeight.contDiffAt_blockPot j p.2 ?_ ?_ ?_ ?_
    · intro r s
      exact (GlobalTheory.T.base_chart_flag_analytic_map K ι Φ y Ψ N j M n d BM l p.1 Un bp hUn hbpc hchart
        (fun w' hw' => (hpt w' hw').1) r s).contDiffAt (hUn.mem_nhds hw)
    · intro r s
      exact (hH p.1 r s w hw).contDiffAt.restrict_scalars ℝ
    · exact (BM.G_pos l p.1 (bp w) hbw).2
    · exact ((hpt w hw).2 p.1).2
  have hB : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u => GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.upsLogAt BM l p (bp u)) w := by
    by_cases hb : M.blk p = none
    · have hreg := ((BM.good l (bp w) hbw.1).2.2 p hb).2.1
      have han := GlobalTheory.T.regular_function_analytic_on_chart _ _ _ M.x ((BM.F l).υ p) d n BM.Rb Un bp w hUn hw hbpc hchart hreg
      have hne : GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.upsVal BM l p (bp w) ≠ 0 :=
        GlobalTheory.T.unipotent_value_ne_zero K ι Φ y Ψ N j M n d BM l p (bp w) hbw.1 hb
      obtain ⟨Hh, hHh, hev⟩ := GlobalTheory.T.log_norm_nonvanishing_analytic_harmonic d _ w han hne
      have hre0 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => Complex.reCLM (Hh z)) w :=
        Complex.reCLM.contDiff.contDiffAt.comp w (hHh.contDiffAt.restrict_scalars ℝ)
      have hre : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => (Hh z).re) w := by
        simpa using hre0
      refine hre.congr_of_eventuallyEq ?_
      filter_upwards [hev] with z hz
      show GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.upsLogAt BM l p (bp z) = (Hh z).re
      unfold GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.upsLogAt
      rw [if_pos hb]
      exact hz
    · have hz : (fun u => GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.upsLogAt BM l p (bp u)) = fun _ => (0 : ℝ) := by
        funext u
        unfold GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.upsLogAt
        rw [if_neg hb]
      rw [hz]
      exact contDiffAt_const
  have he : GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.alphaOf BM l H bp p = fun u =>
      GlobalTheory.CompanionTheory.Ar.PB.blockPot j p.2 (BM.G l p.1 (bp u)) (H p.1 u) -
        GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.upsLogAt BM l p (bp u) := rfl
  rw [he]
  exact (hA.sub hB).contDiffWithinAt

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartFourthStatement

section

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem _root_.GlobalTheory.T.two_point_fibre_chart_fourth : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (X : Type) (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∀ p, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (alphaOf BM l H bp p) Un := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.contDiffOn_alphaOf | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.contDiffOn_alphaOf | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.contDiffOn_alphaOf <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartSeventh

section

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem fibre_base_member : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (X : Type) (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∀ p, p ≠ (τ, a) → ∀ z : Fin (d + 1) → ℂ, Fin.tail z ∈ Un → ∃ Hh : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, ((FA.S.comap some).potH p).φ (ΦYn z) (ΦYn z') = alphaOf BM l H bp p (Fin.tail z') + (Hh z').re := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b ca cb hb hst hca hcb X q Un Gn ΦYn ΦWn l H bp hU hD p hp z hz
  obtain ⟨Hh, hHh, hev⟩ := GlobalTheory.T.two_point_fibre_chart_fifth K ι Φ y Ψ N j M n d BM FA τ a b ca cb hb hst hca hcb X q Un Gn
    ΦYn ΦWn l H bp hU hD p z hz
  refine ⟨Hh, hHh, ?_⟩
  filter_upwards [hev] with z' h
  rw [h]
  congr 1
  unfold alphaOf potAt
  congr 1
  by_cases hτ : p.1 = τ
  · have hpa : p.2 ≠ a := fun e => hp (Prod.ext hτ e)
    have hs := (GlobalTheory.T.elementary_factor_properties N j a b ca cb (z' 0) M.j_le hb hst hca hcb).2.2.2
      (BM.G l p.1 (bp (Fin.tail z'))) (H τ (Fin.tail z')) p.2 hpa
    simp only [flagAt, if_pos hτ]
    rw [hs, hτ]
  · simp only [flagAt, if_neg hτ]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartSeventhStatement

section

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem _root_.GlobalTheory.T.two_point_fibre_chart_seventh : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (X : Type) (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∀ p, p ≠ (τ, a) → ∀ z : Fin (d + 1) → ℂ, Fin.tail z ∈ Un → ∃ Hh : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, ((FA.S.comap some).potH p).φ (ΦYn z) (ΦYn z') = alphaOf BM l H bp p (Fin.tail z') + (Hh z').re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.fibre_base_member | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.fibre_base_member | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.fibre_base_member <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreTwistedResolutionStatement

section

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem _root_.GlobalTheory.T.two_point_fibre_twisted_resolution : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (k₀ : K), M.blk (τ, a) = some k₀ → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (q : Fin 2 → RW.X → FA.S.X), (∀ x x₀, FA.Re.π x₀ = q 0 x → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x))) → (∀ x x₀, FA.Re.π x₀ = q 1 x → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x))) → ∀ f : RW.X → ℝ, IsNormFn M τ a k₀ ca cb RW f → ∀ (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → RW.X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∀ z : Fin (d + 2) → ℂ, Fin.tail (Fin.tail z) ∈ Un → z 0 ≠ z 1 → f (ΦWn z) + (1 / 2) * ∑ p, (xiCoef τ a p : ℝ) * ((FA.S.comap some).ph p (q 0 (ΦWn z)) + (FA.S.comap some).ph p (q 1 (ΦWn z))) = logSin (Gn (Fin.tail (Fin.tail z))) (z 0) (z 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.NormFib.logNorm_add_weights_eq_logSin | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.NormFib.logNorm_add_weights_eq_logSin | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.NormFib.logNorm_add_weights_eq_logSin <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentRowsLogResolution

section

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

theorem GlobalTheory.CompanionTheory.Ar.PB.WSq.fibre_potentials : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (q : Fin 2 → RW.X → FA.S.X), (∀ i, HoloMap RW.A FA.S.A (q i)) → (∀ x x₀, FA.Re.π x₀ = q 0 x → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x))) → (∀ x x₀, FA.Re.π x₀ = q 1 x → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x))) → ∀ (L' : LocPot RW.X) (v : RW.X → RW.X → ℂ) (cst : ℝ), IsNormFn M τ a k₀ ca cb RW (fun x => logNormSec L' v x + cst) → ∀ (U : ℕ → Set (Fin d → ℂ)) (G : ℕ → (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦY : ℕ → (Fin (d + 1) → ℂ) → FA.S.X) (ΦW : ℕ → (Fin (d + 2) → ℂ) → RW.X), (∀ m, IsOpen (U m)) → (∀ m, IsFibreChart FA τ a ca cb q (U m) (G m) (ΦY m) (ΦW m)) → ∃ α : ℕ → Ψ × Fin N → (Fin d → ℂ) → ℝ, (∀ m, ∀ w ∈ U m, (G m w).PosDef) ∧ (∀ m r s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => G m w r s) (U m)) ∧ (∀ m p, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (α m p) (U m)) ∧ (∀ m (z : Fin (d + 1) → ℂ), Fin.tail z ∈ U m → ∃ Hh : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, ∑ p, (xiCoef τ a p : ℝ) * ((FA.S.comap some).potH p).φ (ΦY m z) (ΦY m z') = xiPot (G m (Fin.tail z')) (z' 0) + (Hh z').re) ∧ (∀ m p, p ≠ (τ, a) → ∀ z : Fin (d + 1) → ℂ, Fin.tail z ∈ U m → ∃ Hh : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, ((FA.S.comap some).potH p).φ (ΦY m z) (ΦY m z') = α m p (Fin.tail z') + (Hh z').re) ∧ ∀ m (z : Fin (d + 2) → ℂ), Fin.tail (Fin.tail z) ∈ U m → z 0 ≠ z 1 → logNormSec L' v (ΦW m z) + cst + (1 / 2) * ∑ p, (xiCoef τ a p : ℝ) * ((FA.S.comap some).ph p (q 0 (ΦW m z)) + (FA.S.comap some).ph p (q 1 (ΦW m z))) = logSin (G m (Fin.tail (Fin.tail z))) (z 0) (z 1) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b k₀ ca cb hb hcase hblk hca hcb RW q hq h0 h1 L' v cst hnorm U G ΦY ΦW hU hC
  have hC' := fun m => (isFibreChart_iff FA τ a ca cb q (U m) (G m) (ΦY m) (ΦW m)).1 (hC m)
  choose l H bp hD using hC'
  refine ⟨fun m => alphaOf BM (l m) (H m) (bp m), fun m => ?_, fun m => ?_, fun m => ?_, fun m => ?_, fun m => ?_, fun m => ?_⟩
  · exact GlobalTheory.T.two_point_fibre_chart_second K ι Φ y Ψ N j M n d BM FA τ a b ca cb hb hcase hca hcb _ q (U m) (G m) (ΦY m) (ΦW m) (l m) (H m) (bp m) (hU m) (hD m)
  · exact GlobalTheory.T.two_point_fibre_chart_third K ι Φ y Ψ N j M n d BM FA τ a b ca cb hb hcase hca hcb _ q (U m) (G m) (ΦY m) (ΦW m) (l m) (H m) (bp m) (hU m) (hD m)
  · exact GlobalTheory.T.two_point_fibre_chart_fourth K ι Φ y Ψ N j M n d BM FA τ a b ca cb hb hcase hca hcb _ q (U m) (G m) (ΦY m) (ΦW m) (l m) (H m) (bp m) (hU m) (hD m)
  · exact GlobalTheory.T.two_point_fibre_chart_sixth K ι Φ y Ψ N j M n d BM FA τ a b ca cb hb hcase hca hcb _ q (U m) (G m) (ΦY m) (ΦW m) (l m) (H m) (bp m) (hU m) (hD m)
  · exact GlobalTheory.T.two_point_fibre_chart_seventh K ι Φ y Ψ N j M n d BM FA τ a b ca cb hb hcase hca hcb _ q (U m) (G m) (ΦY m) (ΦW m) (l m) (H m) (bp m) (hU m) (hD m)
  · exact GlobalTheory.T.two_point_fibre_twisted_resolution K ι Φ y Ψ N j M n d BM FA τ a b ca cb hb hcase hca hcb k₀ hblk RW q h0 h1 _ hnorm (U m) (G m) (ΦY m) (ΦW m) (l m) (H m) (bp m) (hU m) (hD m)
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentRowsLogResolutionStatement

section

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

theorem _root_.GlobalTheory.T.flag_adjacent_rows_log_resolution : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (q : Fin 2 → RW.X → FA.S.X), (∀ i, HoloMap RW.A FA.S.A (q i)) → (∀ x x₀, FA.Re.π x₀ = q 0 x → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x))) → (∀ x x₀, FA.Re.π x₀ = q 1 x → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x))) → ∀ (L' : LocPot RW.X) (v : RW.X → RW.X → ℂ) (cst : ℝ), IsNormFn M τ a k₀ ca cb RW (fun x => logNormSec L' v x + cst) → ∀ (U : ℕ → Set (Fin d → ℂ)) (G : ℕ → (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦY : ℕ → (Fin (d + 1) → ℂ) → FA.S.X) (ΦW : ℕ → (Fin (d + 2) → ℂ) → RW.X), (∀ m, IsOpen (U m)) → (∀ m, IsFibreChart FA τ a ca cb q (U m) (G m) (ΦY m) (ΦW m)) → ∃ α : ℕ → Ψ × Fin N → (Fin d → ℂ) → ℝ, (∀ m, ∀ w ∈ U m, (G m w).PosDef) ∧ (∀ m r s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => G m w r s) (U m)) ∧ (∀ m p, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (α m p) (U m)) ∧ (∀ m (z : Fin (d + 1) → ℂ), Fin.tail z ∈ U m → ∃ Hh : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, ∑ p, (xiCoef τ a p : ℝ) * ((FA.S.comap some).potH p).φ (ΦY m z) (ΦY m z') = xiPot (G m (Fin.tail z')) (z' 0) + (Hh z').re) ∧ (∀ m p, p ≠ (τ, a) → ∀ z : Fin (d + 1) → ℂ, Fin.tail z ∈ U m → ∃ Hh : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, ((FA.S.comap some).potH p).φ (ΦY m z) (ΦY m z') = α m p (Fin.tail z') + (Hh z').re) ∧ ∀ m (z : Fin (d + 2) → ℂ), Fin.tail (Fin.tail z) ∈ U m → z 0 ≠ z 1 → logNormSec L' v (ΦW m z) + cst + (1 / 2) * ∑ p, (xiCoef τ a p : ℝ) * ((FA.S.comap some).ph p (q 0 (ΦW m z)) + (FA.S.comap some).ph p (q 1 (ΦW m z))) = logSin (G m (Fin.tail (Fin.tail z))) (z 0) (z 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.fibre_potentials | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.fibre_potentials | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.fibre_potentials <;> assumption)
end
end
