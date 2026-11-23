module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GeometricAbelianConnected
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackPullback
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentRowsAnalytic
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
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentRowsBaseMetricStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentRowsDimension
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentRowsLogResolutionStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentRowsResolution
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticDimensionCountStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFubiniStudyPositiveStatement
public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncAdaptedAtlasProjection
import Mathlib.NumberTheory.Height.NumberField
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SingularWeightMonotoneRegularization
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackPullback
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInhab

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentRowsAnalyticStatement

section

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

theorem _root_.GlobalTheory.T.flag_adjacent_rows_analytic : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsArithVar (mCoordIdeal y) (d + 2) → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (pr : RW.X → BM.Rb.X), HoloMap RW.A BM.Rb.A pr → (∀ x, SameOrbit (BM.Rb.lift (pr x) (pr x)) (basePart M.blk (fstPt k₀ (RW.lift x x)))) → ∃ q : Fin 2 → RW.X → FA.S.X, (∀ i, HoloMap RW.A FA.S.A (q i)) ∧ (∀ i, FA.pr ∘ q i = pr) ∧ (∀ x x₀, FA.Re.π x₀ = q 0 x → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x))) ∧ (∀ x x₀, FA.Re.π x₀ = q 1 x → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x))) ∧ (Function.Injective fun w => (q 0 w, q 1 w)) ∧ ∀ p, p ≠ (τ, a) → FA.S.ph (some p) ∘ q 0 = FA.S.ph (some p) ∘ q 1 ∧ ∀ t, FA.S.phT (some p) t ∘ q 0 = FA.S.phT (some p) t ∘ q 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Pr.two_projections | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Pr.two_projections | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Pr.two_projections <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentRowsDimensionStatement

section

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

theorem _root_.GlobalTheory.T.flag_adjacent_rows_dimension : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (q : Fin 2 → RW.X → FA.S.X), (∀ i, HoloMap RW.A FA.S.A (q i)) → (∀ x x₀, FA.Re.π x₀ = q 0 x → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x))) → (∀ x x₀, FA.Re.π x₀ = q 1 x → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x))) → (Function.Injective fun w => (q 0 w, q 1 w)) → ∃ (U B : ℕ → Set (Fin d → ℂ)) (G : ℕ → (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦY : ℕ → (Fin (d + 1) → ℂ) → FA.S.X) (ΦW : ℕ → (Fin (d + 2) → ℂ) → RW.X), (∀ m, IsOpen (U m)) ∧ (∀ m, MeasurableSet (B m) ∧ B m ⊆ U m) ∧ IsParamCover FA.S.A (fun m => {z | Fin.tail z ∈ U m}) (fun m => {z | Fin.tail z ∈ B m}) ΦY ∧ IsParamCover RW.A (fun m => {z | Fin.tail (Fin.tail z) ∈ U m}) (fun m => {z | Fin.tail (Fin.tail z) ∈ B m}) ΦW ∧ (∀ m (z : Fin (d + 1) → ℂ), Fin.tail z ∈ U m → ΦY m z ∉ bdry FA.S.s) ∧ ∀ m, IsFibreChart FA τ a ca cb q (U m) (G m) (ΦY m) (ΦW m) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.fibre_charts | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.fibre_charts | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.fibre_charts <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentRowsResolutionStatement

section

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

theorem _root_.GlobalTheory.T.flag_adjacent_rows_resolution : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsArithVar (mCoordIdeal y) (d + 2) → d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) → ∃ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (pr : RW.X → Rb.X), IsWAtlas M Rb τ a k₀ ca cb RW pr := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.fibreSquare_atlas | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.fibreSquare_atlas | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.fibreSquare_atlas <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.SncAdaptedAtlasProjectionStatement

section

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem _root_.GlobalTheory.T.snc_adapted_atlas_projection : ∀ (e n : ℕ) (X Z : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] [TopologicalSpace Z] [CompactSpace Z] [T2Space Z] (A : FinHolAtlas e X) (Ab Bb : FinHolAtlas n Z) (pr : X → Z) (hp : HoloMap A Ab pr) (L : LocPot Z) (s : Z → Z → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set Z), IsPotential Ab L → IsSection Ab L s → IsSNC Ab L s m W → (∀ x, logNormSec L s x ≤ 0) → (∀ x, ∃ (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (kb : Fin Ab.n) (σ : Fin n ↪ Fin e), IsCompatChart A ψ ∧ x ∈ ψ.source ∧ (∀ x' ∈ ψ.source, pr x' ∈ (Ab.chart kb).source ∧ ∀ i, Ab.chart kb (pr x') i = ψ x' (σ i))) → IsPotential A (L.pullback pr hp.1) ∧ IsSection A (L.pullback pr hp.1) (fun x y => s (pr x) (pr y)) ∧ IsSNC A (L.pullback pr hp.1) (fun x y => s (pr x) (pr y)) m (fun k => pr ⁻¹' W k) ∧ ∃ B : FinHolAtlas e X, IsAdaptedAtlas A B (L.pullback pr hp.1) (fun x y => s (pr x) (pr y)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.SncPull.pullback_projection | exact GlobalTheory.CompanionTheory.Ar.PB.SncPull.pullback_projection | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.SncPull.pullback_projection <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoMapPullbackEnergy

section

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.SysPull

theorem finite_bound {ι : Type} [Finite ι] (f : ι → ℝ) : ∃ M : ℝ, ∀ a, f a ≤ M := by
  obtain ⟨M, hM⟩ := (Set.finite_range f).bddAbove
  exact ⟨M, fun a => hM ⟨a, rfl⟩⟩

theorem finite_scale {ι : Type} [Finite ι] (f : ι → ℝ) (hf : ∀ a, 0 < f a) : ∃ t : ℝ, 0 < t ∧ ∀ a, t ≤ f a := by
  obtain ⟨M, hM⟩ := finite_bound fun a => (f a)⁻¹
  by_cases he : Nonempty ι
  · obtain ⟨a₀⟩ := he
    have hM0 : 0 < M := lt_of_lt_of_le (inv_pos.2 (hf a₀)) (hM a₀)
    exact ⟨M⁻¹, inv_pos.2 hM0, fun a => inv_le_of_inv_le₀ (hf a) (hM a)⟩
  · exact ⟨1, one_pos, fun a => absurd ⟨a⟩ he⟩

theorem pullback_common : ∀ (e e' : ℕ) (σ : Type) [Fintype σ] (S : AnSys e σ) (X' : Type) [TopologicalSpace X'] [CompactSpace X'] [T2Space X'] (A' : FinHolAtlas e' X') (Θ' L' : LocPot X') (s' : X' → X' → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X') (q : Fin 2 → X' → S.X) (hq : ∀ i, HoloMap A' S.A (q i)), PullbackStatement → IsPotential A' Θ' → IsPosPot A' Θ' → IsPotential A' L' → IsSection A' L' s' → IsSNC A' L' s' m W → (∀ y, logNormSec L' s' y ≤ 0) → (∀ i, S.L.pullback (q i) (hq i).1 = L') → (∀ i, (fun x y => S.s (q i x) (q i y)) = s') → ∃ C₅ C t₀ : ℝ, t₀ ≤ S.t₀ ∧ ∀ (i : Fin 2) (a : σ), IsSingWeight A' L' s' ((S.th a).pullback (q i) (hq i).1) (S.ph a ∘ q i) C₅ ∧ IsRegFamily A' Θ' L' s' ((S.th a).pullback (q i) (hq i).1) (S.ph a ∘ q i) (fun t => S.phT a t ∘ q i) C t₀ ∧ IsRegFamilyC2 A' s' (S.ph a ∘ q i) (fun t => S.phT a t ∘ q i) := by
  intro e e' σ _ S X' _ _ _ A' Θ' L' s' nb m W q hq hP pΘ' posΘ' pL' sec' snc' nrm hL hs
  have key : ∀ p : Fin 2 × σ, ∃ C' t' : ℝ,
      IsSingWeight A' L' s' ((S.th p.2).pullback (q p.1) (hq p.1).1) (S.ph p.2 ∘ q p.1) S.C₅ ∧
      IsRegFamily A' Θ' L' s' ((S.th p.2).pullback (q p.1) (hq p.1).1) (S.ph p.2 ∘ q p.1)
        (fun t => S.phT p.2 t ∘ q p.1) C' t' ∧
      IsRegFamilyC2 A' s' (S.ph p.2 ∘ q p.1) (fun t => S.phT p.2 t ∘ q p.1) := by
    rintro ⟨i, a⟩
    have snc_i : IsSNC A' (S.L.pullback (q i) (hq i).1) (fun x y => S.s (q i x) (q i y)) m W := by
      rw [hL i, hs i]
      exact snc'
    obtain ⟨C', t', h1, h2, h3⟩ := hP S.A A' (q i) (hq i) S.Θ S.L Θ' S.s S.m S.W m W S.potΘ S.posΘ pΘ' posΘ'
      S.potL S.sec S.snc S.norm_le snc_i (S.th a) (S.ph a) (S.phT a) S.C₅ S.C S.t₀ (S.sing a) (S.reg a) (S.c2 a)
    rw [hL i, hs i] at h1 h2
    rw [hs i] at h3
    exact ⟨C', t', h1, h2, h3⟩
  choose C' t' h1 h2 h3 using key
  by_cases hσ : Nonempty σ
  · obtain ⟨a₀⟩ := hσ
    obtain ⟨D, hD⟩ := finite_bound fun p => |C' p|
    obtain ⟨T₀, hT₀, hT⟩ := finite_scale t' fun p => (h2 p).1
    have hS : 0 < S.t₀ := (S.reg a₀).1
    refine ⟨S.C₅, D, min (min T₀ S.t₀) (Real.exp (-1)),
      (min_le_left _ _).trans (min_le_right _ _), fun i a => ⟨h1 (i, a), ?_, h3 (i, a)⟩⟩
    exact (GlobalTheory.CompanionTheory.Ar.PB.enlarging_constants_smooth_members e' X' A' Θ' L' s' nb m W pL' sec' snc' nrm pΘ' posΘ').2.1 _ _ _ _ _ _ _ (hD (i, a))
      (lt_min (lt_min hT₀ hS) (Real.exp_pos _)) ((min_le_left _ _).trans ((min_le_left _ _).trans (hT (i, a))))
      (min_le_right _ _) (h2 (i, a)) (h1 (i, a)).1
  · exact ⟨0, 0, S.t₀, le_rfl, fun _ a => absurd ⟨a⟩ hσ⟩

end GlobalTheory.CompanionTheory.Ar.PB.SysPull
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoMapPullbackEnergyStatement

section

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

theorem _root_.GlobalTheory.T.two_map_pullback_energy : ∀ (e e' : ℕ) (σ : Type) [Fintype σ] (S : AnSys e σ) (X' : Type) [TopologicalSpace X'] [CompactSpace X'] [T2Space X'] (A' : FinHolAtlas e' X') (Θ' L' : LocPot X') (s' : X' → X' → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X') (q : Fin 2 → X' → S.X) (hq : ∀ i, HoloMap A' S.A (q i)), PullbackStatement → IsPotential A' Θ' → IsPosPot A' Θ' → IsPotential A' L' → IsSection A' L' s' → IsSNC A' L' s' m W → (∀ y, logNormSec L' s' y ≤ 0) → (∀ i, S.L.pullback (q i) (hq i).1 = L') → (∀ i, (fun x y => S.s (q i x) (q i y)) = s') → ∃ C₅ C t₀ : ℝ, t₀ ≤ S.t₀ ∧ ∀ (i : Fin 2) (a : σ), IsSingWeight A' L' s' ((S.th a).pullback (q i) (hq i).1) (S.ph a ∘ q i) C₅ ∧ IsRegFamily A' Θ' L' s' ((S.th a).pullback (q i) (hq i).1) (S.ph a ∘ q i) (fun t => S.phT a t ∘ q i) C t₀ ∧ IsRegFamilyC2 A' s' (S.ph a ∘ q i) (fun t => S.phT a t ∘ q i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.SysPull.pullback_common | exact GlobalTheory.CompanionTheory.Ar.PB.SysPull.pullback_common | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.SysPull.pullback_common <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentSwapSquareSystem

section

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq

theorem ansq_exists : Inputs → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsArithVar (mCoordIdeal y) (d + 2) → ∃ (Q : AnSq (FA.S.comap some) (τ, a) (xiCoef τ a)) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (e : RW.X → Q.SW.X), HoloMap RW.A Q.SW.A e ∧ IsDegreeOff Q.SW.A RW.A e 1 ∅ ∧ (∀ x x₀, FA.Re.π x₀ = Q.q 0 (e x) → SameOrbit (FA.Re.R.lift x₀ x₀) fun p => RW.lift x x ⟨some p.1, p.2⟩) ∧ (∀ x x₀, FA.Re.π x₀ = Q.q 1 (e x) → ∃ z₁, SameOrbit (FA.Re.R.lift x₀ x₀) z₁ ∧ (∀ p : (Σ k, ι k), p.1 ≠ k₀ → z₁ p = RW.lift x x ⟨some p.1, p.2⟩) ∧ ∀ m : ι k₀, z₁ ⟨k₀, m⟩ = RW.lift x x ⟨none, m⟩) ∧ (Function.Injective fun w => (Q.q 0 w, Q.q 1 w)) ∧ ∀ x (z₀ z₁ : (Σ k, ι k) → ℂ) F (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ), M.IsFrame F → M.GoodAt F (mCoordIdeal (basePart M.blk z₀)) → (∀ x₀, FA.Re.π x₀ = Q.q 0 (e x) → SameOrbit (FA.Re.R.lift x₀ x₀) z₀) → (∀ x₀, FA.Re.π x₀ = Q.q 1 (e x) → SameOrbit (FA.Re.R.lift x₀ x₀) z₁) → IsBlockDiag j h → h.det ≠ 0 → t ≠ 0 → (∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ, i) z₀ h) → (∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ, i) z₁ (h * (1 + Matrix.single cb ca t))) → logNormSec Q.L' Q.v (e x) + Q.cst = Real.log ‖t * ∏ i : Fin N, (if IsProperStep N j i then 1 else valAt M.x (F.υ (τ, i)) (basePart M.blk z₀) * (if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ h (wIdx N j) (wIdx N j) else 1) else minorIJ h (omIdx N j) (omIdx N j))) ^ xiCoef τ a (τ, i)‖ + (1 / 2) * ∑ p, (xiCoef τ a p : ℝ) * (Real.log ((fsHerm ι (M.dy p)).h z₀) + Real.log ((fsHerm ι (M.dy p)).h z₁)) := by
  intro hin K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b k₀ ca cb hb hs hk hca hcb har
  have hdim := GlobalTheory.T.flag_analytic_dimension_count K ι Φ y Ψ N j M n d BM FA
  obtain ⟨RW, pr, hpr, hbase, hch⟩ := GlobalTheory.T.flag_adjacent_rows_resolution K ι Φ y Ψ N j M n d BM.Rb τ a b k₀ ca cb hb hs hk hca hcb har hdim
  obtain ⟨q, hq, hpq, hl0, hl1, hinj, hbp⟩ :=
    GlobalTheory.T.flag_adjacent_rows_analytic K ι Φ y Ψ N j M n d BM FA τ a b k₀ ca cb hb hs hk hca hcb har RW pr hpr hbase
  have hch' : ∀ x, ∃ (ψ : OpenPartialHomeomorph RW.X (Fin (d + 2) → ℂ)) (kb : Fin BM.Rb.A.n) (σ : Fin n ↪ Fin (d + 2)),
      IsCompatChart RW.A ψ ∧ x ∈ ψ.source ∧ (∀ x' ∈ ψ.source, pr x' ∈ (BM.Rb.A.chart kb).source ∧
        ∀ i, BM.Rb.A.chart kb (pr x') i = ψ x' (σ i)) := fun x => by
    obtain ⟨ψ, kb, σ, i₀, F, H, hx, h1, -, -, h4, -⟩ := hch x
    exact ⟨ψ, kb, σ, h1, hx, h4⟩
  obtain ⟨pL, sL, nL, -⟩ := GlobalTheory.T.snc_adapted_atlas_projection (d + 2) n RW.X BM.Rb.X RW.A BM.Rb.A BM.Bat pr hpr BM.L BM.s BM.nb BM.m BM.W
    BM.potL BM.sec BM.snc BM.norm_le hch'
  obtain ⟨hA, hfs, hΘ⟩ := GlobalTheory.T.log_resolution_fubini_study_positive (Option K) (fun o => ι (o.getD k₀)) _ (d + 2) RW
  have hL : ∀ i, (FA.S.comap some).L.pullback (q i) (hq i).1 = BM.L.pullback pr hpr.1 := fun i => by
    show FA.S.L.pullback (q i) (hq i).1 = _
    have e := FA.L_eq
    revert e
    generalize FA.S.L = LL
    intro e
    subst e
    exact pullback_pullback _ _ _ _ _ _ _ (hpq i)
  have hs' : ∀ i, (fun x y => (FA.S.comap some).s (q i x) (q i y)) = fun x y => BM.s (pr x) (pr y) := fun i => by
    funext x y
    show FA.S.s (q i x) (q i y) = _
    rw [FA.s_eq]
    show BM.s ((FA.pr ∘ q i) x) ((FA.pr ∘ q i) y) = _
    rw [hpq i]
  obtain ⟨C₅, C, t₀, ht₀, hmem⟩ := GlobalTheory.T.two_map_pullback_energy (d + 1) (d + 2) (Ψ × Fin N) (FA.S.comap some) RW.X RW.A
    (potOf RW (fsHerm _ fun _ => 1)) (BM.L.pullback pr hpr.1) (fun x y => BM.s (pr x) (pr y)) BM.nb BM.m
    (fun k => pr ⁻¹' BM.W k) q hq hin.pullback (hA _ hfs) hΘ pL sL nL (fun x => BM.norm_le (pr x)) hL hs'
  obtain ⟨L', v, Dg, cst, potL', secv, sncv, sncsv, normv, hN⟩ :=
    GlobalTheory.T.flag_adjacent_rows_base_metric K ι Φ y Ψ N j M n d BM τ a b k₀ ca cb hb hs hk hca hcb har RW pr hpr.1 ⟨hpr, hbase, hch⟩
  obtain ⟨U, B, G, ΦY, ΦW, U_open, B_meas, coverY, coverW, ΦY_open, hfc⟩ :=
    GlobalTheory.T.flag_adjacent_rows_dimension K ι Φ y Ψ N j M n d BM FA τ a b k₀ ca cb hb hs hk hca hcb hdim RW q hq hl0 hl1 hinj
  obtain ⟨α, G_pos, G_smooth, α_smooth, xi_pot, base_pot, norm_hom⟩ :=
    GlobalTheory.T.flag_adjacent_rows_log_resolution K ι Φ y Ψ N j M n d BM FA τ a b k₀ ca cb hb hs hk hca hcb RW q hq hl0 hl1 L' v cst hN U G ΦY ΦW U_open hfc
  let SW : AnSys (d + 2) (Option (Ψ × Fin N)) :=
    { X := RW.X
      A := RW.A
      Θ := potOf RW (fsHerm _ fun _ => 1)
      L := BM.L.pullback pr hpr.1
      s := fun x y => BM.s (pr x) (pr y)
      nb := BM.nb
      m := BM.m
      W := fun k => pr ⁻¹' BM.W k
      potΘ := hA _ hfs
      posΘ := hΘ
      potL := pL
      sec := sL
      snc := nL
      norm_le := fun x => BM.norm_le (pr x)
      th := fun o => o.elim (((FA.S.comap some).th (τ, a)).pullback (q 1) (hq 1).1)
        fun p => ((FA.S.comap some).th p).pullback (q 0) (hq 0).1
      ph := fun o => o.elim ((FA.S.comap some).ph (τ, a) ∘ q 1) fun p => (FA.S.comap some).ph p ∘ q 0
      phT := fun o => o.elim (fun t => (FA.S.comap some).phT (τ, a) t ∘ q 1)
        fun p t => (FA.S.comap some).phT p t ∘ q 0
      C₅ := C₅
      C := C
      t₀ := t₀
      sing := fun o => by
        cases o with
        | none => exact (hmem 1 (τ, a)).1
        | some p => exact (hmem 0 p).1
      reg := fun o => by
        cases o with
        | none => exact (hmem 1 (τ, a)).2.1
        | some p => exact (hmem 0 p).2.1
      c2 := fun o => by
        cases o with
        | none => exact (hmem 1 (τ, a)).2.2
        | some p => exact (hmem 0 p).2.2 }
  have hsame : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (P : LocPot X), SamePot A Set.univ P P :=
    fun A P x _ => ⟨Set.univ, isOpen_univ, trivial, fun _ => 0, fun _ _ _ => analyticAt_const, fun y _ => by simp⟩
  let Q : AnSq (FA.S.comap some) (τ, a) (xiCoef τ a) :=
    { eps_a₀ := by simp [xiCoef]
      SW := SW
      q := q
      holo := hq
      bdry_eq := fun i => by
        ext x
        show BM.s (pr x) (pr x) ≠ 0 ↔ FA.S.s (q i x) (q i x) ≠ 0
        rw [FA.s_eq]
        show _ ↔ BM.s ((FA.pr ∘ q i) x) ((FA.pr ∘ q i) x) ≠ 0
        rw [hpq i]
      t₀_le := ht₀
      th0 := fun p => hsame _ _
      th1 := hsame _ _
      ph0 := fun _ => rfl
      ph1 := rfl
      phase_some_eq_comp_first_projection := fun _ _ => rfl
      phase_none_eq_comp_second_projection := fun _ => rfl
      base_ph := fun p hp => (hbp p hp).1
      base_phT := fun p hp t => (hbp p hp).2 t
      L' := L'
      v := v
      Dg := Dg
      cst := cst
      potL' := potL'
      secv := secv
      sncv := sncv
      sncsv := sncsv
      normv := normv
      U := U
      B := B
      G := G
      α := α
      ΦY := ΦY
      ΦW := ΦW
      U_open := U_open
      B_meas := B_meas
      G_pos := G_pos
      G_smooth := G_smooth
      α_smooth := fun m p => α_smooth m p
      coverY := coverY
      coverW := coverW
      ΦY_open := ΦY_open
      first_projection_chart_compat := fun m z hz => by
        obtain ⟨l, H, bp, -, -, -, -, -, -, h⟩ := hfc m
        exact (h z hz).1
      second_projection_chart_compat := fun m z hz => by
        obtain ⟨l, H, bp, -, -, -, -, -, -, h⟩ := hfc m
        exact (h z hz).2
      xi_pot := xi_pot
      base_pot := base_pot
      norm_hom := norm_hom }
  have hsurj : ∀ w, ∃ x₀, FA.Re.π x₀ = w := fun w => by
    have hd := FA.Re.degree
    rw [FA.deg_one, FA.br_empty] at hd
    obtain ⟨x₀, hx₀⟩ := Set.ncard_eq_one.1 (hd.2.2.2.2.1 w (Set.notMem_empty w))
    exact ⟨x₀, (hx₀ ▸ Set.mem_singleton x₀ : x₀ ∈ FA.Re.π ⁻¹' {w})⟩
  refine ⟨Q, RW, id, ⟨continuous_id, fun j k => RW.A.holo j k⟩, isDegreeOff_id RW.A, hl0, ?_, hinj, ?_⟩
  · intro x x₀ hx
    refine ⟨sndPt k₀ (RW.lift x x), hl1 x x₀ hx, fun p hp => ?_, fun m => ?_⟩
    · show RW.lift x x (v₁ k₀ p) = _
      rw [v₁_ne hp]
    · show RW.lift x x (v₁ k₀ ⟨k₀, m⟩) = _
      rw [v₁_self]
  · intro x z₀ z₁ F h t hF hG h0 h1 hh hd ht hE0 hE1
    obtain ⟨x₀, hx₀⟩ := hsurj (q 0 x)
    obtain ⟨x₁, hx₁⟩ := hsurj (q 1 x)
    exact hN x z₀ z₁ F h t hF hG (orbit_trans (orbit_symm (h0 x₀ hx₀)) (hl0 x x₀ hx₀)) (orbit_trans (orbit_symm (h1 x₁ hx₁)) (hl1 x x₁ hx₁))
      hh hd ht hE0 hE1

end GlobalTheory.CompanionTheory.Ar.PB.WSq
end
end
end
