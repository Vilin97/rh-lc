module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSmoothHermTrivLine
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.MaIntEmpty
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothFunctionAsDegreeZeroMetric
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PFsInvPow
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices.InstFintypeFlIdx
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothHermFubiniStudyO1

-- Source module: Development.WeilBound.CoreStatements.PluriharmonicCharts.X_line_conj

section

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

theorem PositivityTheory.Xgp.t_line_conj : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (A : HermLine ι), IsSmoothHerm A → ∃ B : HermLine ι, B.a = A.a ∧ IsSmoothHerm B ∧ IsConjInvariantH B ∧ ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → Real.log (B.h z) = (Real.log (A.h z) + Real.log (A.h fun p => starRingEnd ℂ (z p))) / 2 := by
  intro K _ ι _ A hA
  have hne : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      ∀ k, ∃ i, (fun p => starRingEnd ℂ (z p)) ⟨k, i⟩ ≠ 0 := by
    intro z hz k
    obtain ⟨i, hi⟩ := hz k
    exact ⟨i, by simpa using hi⟩
  refine ⟨⟨A.a, fun z => Real.sqrt (A.h z * A.h fun p => starRingEnd ℂ (z p)), ?_, ?_⟩, rfl, ?_, ?_, ?_⟩
  · intro z hz
    exact Real.sqrt_pos.2 (mul_pos (A.pos z hz) (A.pos _ (hne z hz)))
  · intro c z hc
    have h1 := A.smul (fun k => starRingEnd ℂ (c k)) (fun p => starRingEnd ℂ (z p)) (fun k => by simpa using hc k)
    simp only [RCLike.norm_conj] at h1
    simp only [map_mul]
    rw [h1, A.smul c z hc]
    have h0 : 0 ≤ ∏ k, ‖c k‖ ^ A.a k := Finset.prod_nonneg fun k _ => zpow_nonneg (norm_nonneg _) _
    rw [mul_mul_mul_comm, Real.sqrt_mul (mul_nonneg h0 h0), Real.sqrt_mul_self h0]
  · have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, ι k) → ℂ => fun p => starRingEnd ℂ (z p)) := by
      refine contDiff_pi.2 fun p => ?_
      exact Complex.conjCLE.contDiff.comp (contDiff_apply ℝ (fun _ => ℂ) p)
    refine ContDiffOn.sqrt (ContDiffOn.mul hA (hA.comp hc.contDiffOn fun z hz => hne z hz)) ?_
    intro z hz
    exact (mul_pos (A.pos z hz) (A.pos _ (hne z hz))).ne'
  · intro z
    simp only [Complex.conj_conj, mul_comm]
  · intro z hz
    show Real.log (Real.sqrt _) = _
    rw [Real.log_sqrt (mul_pos (A.pos z hz) (A.pos _ (hne z hz))).le,
      Real.log_mul (A.pos z hz).ne' (A.pos _ (hne z hz)).ne']
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.ConjugationInvariantHermitianMetric

section

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem exists_conjInvariant_line_averaged : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (A : HermLine ι), IsSmoothHerm A → ∃ B : HermLine ι, B.a = A.a ∧ IsSmoothHerm B ∧ IsConjInvariantH B ∧ ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → Real.log (B.h z) = (Real.log (A.h z) + Real.log (A.h fun p => starRingEnd ℂ (z p))) / 2 :=
  @PositivityTheory.Xgp.t_line_conj

end GlobalTheory.CompanionTheory.Ar.PB
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.ConjugationInvariantHermitianMetricStatement

section

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.conjugation_invariant_hermitian_metric : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (A : HermLine ι), IsSmoothHerm A → ∃ B : HermLine ι, B.a = A.a ∧ IsSmoothHerm B ∧ IsConjInvariantH B ∧ ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → Real.log (B.h z) = (Real.log (A.h z) + Real.log (A.h fun p => starRingEnd ℂ (z p))) / 2 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.exists_conjInvariant_line_averaged | exact GlobalTheory.CompanionTheory.Ar.PB.exists_conjInvariant_line_averaged | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.exists_conjInvariant_line_averaged <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothFunctionAsDegreeZeroMetricStatement

section

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.smooth_function_as_degree_zero_metric : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (D : ℕ) (R : AnLogRes P ⊤ D) (u : R.X → ℝ), R.A.Smooth u → ∃ B : HermLine ι, B.a = 0 ∧ IsSmoothHerm B ∧ ∀ x, Real.log (B.h (R.lift x x)) = u x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.exists_hermLine_log_eq_of_smooth | exact GlobalTheory.CompanionTheory.Ar.PB.exists_hermLine_log_eq_of_smooth | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.exists_hermLine_log_eq_of_smooth <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.PositiveHomogeneousPotential

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Chg.FlatExt

open Filter Topology Set

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem isOpen_blockNz : IsOpen {z : (Σ k, J k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have e : {z : (Σ k, J k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
    ext z
    simp
  rw [e]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem conj_mem_mcPts {P : Ideal (MRing J)} {z : (Σ k, J k) → ℂ} (hz : z ∈ mcPts P) :
    (fun p => starRingEnd ℂ (z p)) ∈ mcPts P := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, by simpa using hi⟩
  · have h := hz.2 f hf
    rw [MvPolynomial.eval_map] at h ⊢
    have e := MvPolynomial.eval₂_comp_left (starRingEnd ℂ) (Int.castRingHom ℂ) z f
    rw [h, map_zero, Subsingleton.elim ((starRingEnd ℂ).comp (Int.castRingHom ℂ)) (Int.castRingHom ℂ)] at e
    exact e.symm

theorem continuousOn_of_holoOn {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {U : Set X}
    {g : X → ℂ} (h : A.HoloOn U g) : ContinuousOn g U := by
  intro y hy
  obtain ⟨j, hj⟩ := A.cover y
  have hc := (A.chart j).continuousAt hj
  have hsy : (A.chart j).symm (A.chart j y) = y := (A.chart j).left_inv hj
  have han : ContinuousAt (g ∘ (A.chart j).symm) (A.chart j y) :=
    (h j _ ⟨(A.chart j).map_source hj, by simpa [hsy] using hy⟩).continuousAt
  have hcomp : ContinuousAt ((g ∘ (A.chart j).symm) ∘ (A.chart j)) y := ContinuousAt.comp han hc
  refine (hcomp.congr ?_).continuousWithinAt
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with w hw
  simp [(A.chart j).left_inv hw]

theorem analyticAt_lift {P Jd : Ideal (MRing J)} {D : ℕ} (R : AnLogRes P Jd D) (x : R.X) (j : Fin R.A.n)
    {t : Fin D → ℂ} (ht : t ∈ (R.A.chart j).target) (hx : (R.A.chart j).symm t ∈ R.U x) :
    AnalyticAt ℂ (fun t' => R.lift x ((R.A.chart j).symm t')) t :=
  AnalyticAt.pi fun p => R.holo x p j t ⟨ht, hx⟩

theorem ratio_eq {P Jd : Ideal (MRing J)} {D : ℕ} (R : AnLogRes P Jd D) {a : K → ℤ}
    {φ : ((Σ k, J k) → ℂ) → ℝ}
    (hsm : ∀ z ∈ mcPts P, ∀ c : K → ℂ, (∀ k, c k ≠ 0) →
      φ (fun p => c p.1 * z p) = (∏ k, ‖c k‖ ^ a k) * φ z)
    (H : HermLine J) (hHa : H.a = a) {x y : R.X} (hy : y ∈ R.U x) :
    φ (R.lift y y) / H.h (R.lift y y) = φ (R.lift x y) / H.h (R.lift x y) := by
  obtain ⟨c, hc, e⟩ := R.compat y x y ⟨R.mem_U y, hy⟩
  have hne : (∏ k, ‖c k‖ ^ a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
  rw [e, hsm _ (R.mem x y hy) c hc, H.smul c _ hc, hHa, mul_div_mul_left _ _ hne]

theorem smooth_ratio {P Jd : Ideal (MRing J)} {D : ℕ} (R : AnLogRes P Jd D) {a : K → ℤ}
    {φ : ((Σ k, J k) → ℂ) → ℝ}
    (hsm : ∀ z ∈ mcPts P, ∀ c : K → ℂ, (∀ k, c k ≠ 0) →
      φ (fun p => c p.1 * z p) = (∏ k, ‖c k‖ ^ a k) * φ z)
    (hloc : ∀ z ∈ mcPts P, ∃ (V : Set ((Σ k, J k) → ℂ)) (F : ((Σ k, J k) → ℂ) → ℂ), IsOpen V ∧ z ∈ V ∧
      AnalyticOnNhd ℂ F V ∧ ∀ z' ∈ V ∩ mcPts P, F z' ≠ 0 ∧ φ z' = ‖F z'‖)
    (H : HermLine J) (hHa : H.a = a) (hH : IsSmoothHerm H) :
    R.A.Smooth fun x => Real.log (φ (R.lift x x) / H.h (R.lift x x)) := by
  intro j t ht
  have ht : t ∈ (R.A.chart j).target := ht.1
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, x₀ = (R.A.chart j).symm t := ⟨_, rfl⟩
  have hm₀ : R.lift x₀ x₀ ∈ mcPts P := R.mem _ _ (R.mem_U _)
  obtain ⟨V, F, hV, hzV, hF, hFφ⟩ := hloc _ hm₀
  have hγ : AnalyticAt ℂ (fun t' => R.lift x₀ ((R.A.chart j).symm t')) t :=
    analyticAt_lift R x₀ j ht (hx₀ ▸ R.mem_U _)
  have hγt : R.lift x₀ ((R.A.chart j).symm t) = R.lift x₀ x₀ := by rw [hx₀]
  have hsc : ContinuousAt (R.A.chart j).symm t := (R.A.chart j).continuousAt_symm ht
  have hev : ∀ᶠ t' in 𝓝 t, (R.A.chart j).symm t' ∈ R.U x₀ ∧
      R.lift x₀ ((R.A.chart j).symm t') ∈ V := by
    refine (hsc.eventually ((R.isOpen_U x₀).mem_nhds (hx₀ ▸ R.mem_U _))).and
      (hγ.continuousAt.eventually (hV.mem_nhds ?_))
    show R.lift x₀ ((R.A.chart j).symm t) ∈ V
    rw [hγt]
    exact hzV
  have hne : F (R.lift x₀ ((R.A.chart j).symm t)) ≠ 0 := by
    rw [hγt]
    exact (hFφ _ ⟨hzV, hm₀⟩).1
  have hFa : AnalyticAt ℂ (fun t' => F (R.lift x₀ ((R.A.chart j).symm t'))) t :=
    AnalyticAt.fun_comp (hF _ (by rw [hγt]; exact hzV)) hγ
  have e1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t' => F (R.lift x₀ ((R.A.chart j).symm t'))) t :=
    hFa.contDiffAt.restrict_scalars ℝ
  have e2 := (e1.norm ℝ hne).log (norm_ne_zero_iff.2 hne)
  have hγr : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t' => R.lift x₀ ((R.A.chart j).symm t')) t :=
    hγ.contDiffAt.restrict_scalars ℝ
  have hmem : R.lift x₀ ((R.A.chart j).symm t) ∈ {z : (Σ k, J k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    rw [hγt]
    exact hm₀.1
  have e3 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t' => H.h (R.lift x₀ ((R.A.chart j).symm t'))) t :=
    ContDiffAt.comp t (hH.contDiffAt (isOpen_blockNz.mem_nhds hmem)) hγr
  have e4 := e3.log (H.pos _ hmem).ne'
  refine ((e2.sub e4).congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hev] with t' ht'
  obtain ⟨h1, h2⟩ := ht'
  have hm := R.mem _ _ h1
  obtain ⟨h0, hφ⟩ := hFφ _ ⟨h2, hm⟩
  show Real.log (φ (R.lift _ _) / H.h (R.lift _ _)) = _
  rw [ratio_eq R hsm H hHa h1, hφ, Real.log_div (norm_ne_zero_iff.2 h0) (H.pos _ hm.1).ne']

theorem isFlatOn_of_local {P Jd : Ideal (MRing J)} {D : ℕ} (R : AnLogRes P Jd D) (T : HermLine J)
    {φ : ((Σ k, J k) → ℂ) → ℝ} (hT : ∀ z ∈ mcPts P, T.h z = φ z)
    (hloc : ∀ z ∈ mcPts P, ∃ (V : Set ((Σ k, J k) → ℂ)) (F : ((Σ k, J k) → ℂ) → ℂ), IsOpen V ∧ z ∈ V ∧
      AnalyticOnNhd ℂ F V ∧ ∀ z' ∈ V ∩ mcPts P, F z' ≠ 0 ∧ φ z' = ‖F z'‖) :
    IsFlatOn R T := by
  intro x _
  have hm₀ : R.lift x x ∈ mcPts P := R.mem _ _ (R.mem_U _)
  obtain ⟨V, F, hV, hzV, hF, hFφ⟩ := hloc _ hm₀
  have hcl : ContinuousOn (R.lift x) (R.U x) :=
    continuousOn_pi.2 fun p => continuousOn_of_holoOn R.A (R.holo x p)
  have hW₁ : IsOpen (R.U x ∩ R.lift x ⁻¹' V) := hcl.isOpen_inter_preimage (R.isOpen_U x) hV
  have hf0 : F (R.lift x x) ≠ 0 := (hFφ _ ⟨hzV, hm₀⟩).1
  have hfc : ContinuousOn (fun y => F (R.lift x y) / F (R.lift x x)) (R.U x ∩ R.lift x ⁻¹' V) :=
    (hF.continuousOn.comp (hcl.mono inter_subset_left) fun y hy => hy.2).div_const _
  have hW := hfc.isOpen_inter_preimage hW₁ Complex.isOpen_slitPlane
  refine ⟨_, hW, ⟨⟨R.mem_U x, hzV⟩, by simp [hf0]⟩,
    fun y => Complex.log (F (R.lift x y) / F (R.lift x x)) + (Real.log ‖F (R.lift x x)‖ : ℂ), ?_, ?_⟩
  · intro j t ht
    have hγ := analyticAt_lift R x j ht.1 ht.2.1.1
    have hFa : AnalyticAt ℂ (fun t' => F (R.lift x ((R.A.chart j).symm t'))) t :=
      AnalyticAt.fun_comp (hF _ ht.2.1.2) hγ
    have hga : AnalyticAt ℂ (fun t' => F (R.lift x ((R.A.chart j).symm t')) / F (R.lift x x)) t :=
      hFa.div analyticAt_const hf0
    exact (hga.clog ht.2.2).add analyticAt_const
  · intro y hy
    have hm : R.lift x y ∈ V ∩ mcPts P := ⟨hy.1.2, R.mem x y hy.1.1⟩
    obtain ⟨h0, h1⟩ := hFφ _ hm
    show Real.log (T.h (R.lift x y)) - 0 = _
    rw [hT _ hm.2, h1, Complex.add_re, Complex.log_re, Complex.ofReal_re, norm_div,
      Real.log_div (norm_ne_zero_iff.2 h0) (norm_ne_zero_iff.2 hf0)]
    ring

theorem exists_flat_line : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J)) (D : ℕ) (R : AnLogRes P ⊤ D) (a : K → ℤ) (φ : ((Σ k, J k) → ℂ) → ℝ), (∀ z ∈ mcPts P, 0 < φ z) → (∀ z ∈ mcPts P, φ (fun p => starRingEnd ℂ (z p)) = φ z) → (∀ z ∈ mcPts P, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → φ (fun p => c p.1 * z p) = (∏ k, ‖c k‖ ^ a k) * φ z) → (∀ z ∈ mcPts P, ∃ (V : Set ((Σ k, J k) → ℂ)) (F : ((Σ k, J k) → ℂ) → ℂ), IsOpen V ∧ z ∈ V ∧ AnalyticOnNhd ℂ F V ∧ ∀ z' ∈ V ∩ mcPts P, F z' ≠ 0 ∧ φ z' = ‖F z'‖) → ∃ T : HermLine J, T.a = a ∧ IsSmoothHerm T ∧ IsConjInvariantH T ∧ (∀ z ∈ mcPts P, T.h z = φ z) ∧ IsFlatOn R T := by
  intro K _ J _ P D R a φ hpos hconj hsm hloc
  have hHs : IsSmoothHerm (GroundTheory.Heights₂.Heights.LowerBoundFree.fsHerm J a) :=
    GroundTheory.Heights₂.Heights.LowerBoundFree.FsInvPow.isSmoothHerm_fsHerm a
  obtain ⟨H, hHdef⟩ : ∃ H, H = GroundTheory.Heights₂.Heights.LowerBoundFree.fsHerm J a := ⟨_, rfl⟩
  have hHa : H.a = a := by rw [hHdef]; rfl
  rw [← hHdef] at hHs
  obtain ⟨B, hBa, hBs, hB⟩ := GlobalTheory.T.smooth_function_as_degree_zero_metric K J P D R _ (smooth_ratio R hsm hloc H hHa hHs)
  have hT₀s : IsSmoothHerm (H.tensor B) := ContDiffOn.mul hHs hBs
  have hT₀a : (H.tensor B).a = a := by
    show H.a + B.a = a
    rw [hHa, hBa, add_zero]
  have hpt : ∀ x, (H.tensor B).h (R.lift x x) = φ (R.lift x x) := by
    intro x
    have hm := R.mem x x (R.mem_U x)
    have hHp := H.pos _ hm.1
    have hBp := B.pos _ hm.1
    have hq : 0 < φ (R.lift x x) / H.h (R.lift x x) := div_pos (hpos _ hm) hHp
    have e := Real.log_injOn_pos (Set.mem_Ioi.2 hBp) (Set.mem_Ioi.2 hq) (hB x)
    show H.h _ * B.h _ = _
    rw [e]
    field_simp
  have hT₀ : ∀ z ∈ mcPts P, (H.tensor B).h z = φ z := by
    intro z hz
    have hnt : z ∉ mcPts (⊤ : Ideal (MRing J)) := fun h => by
      have h1 := h.2 1 trivial
      simp at h1
    obtain ⟨x, c, hc, e⟩ := R.surj z hz hnt
    have hne : (∏ k, ‖c k‖ ^ a k) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
    have h1 := hpt x
    rw [e, (H.tensor B).smul c z hc, hT₀a, hsm z hz c hc] at h1
    exact mul_left_cancel₀ hne h1
  obtain ⟨T, hTa, hTs, hTc, hT⟩ := GlobalTheory.T.conjugation_invariant_hermitian_metric K J (H.tensor B) hT₀s
  have hTφ : ∀ z ∈ mcPts P, T.h z = φ z := by
    intro z hz
    have hc := conj_mem_mcPts hz
    have e := hT z hz.1
    rw [hT₀ z hz, hT₀ _ hc, hconj z hz, add_self_div_two] at e
    exact Real.log_injOn_pos (Set.mem_Ioi.2 (T.pos z hz.1)) (Set.mem_Ioi.2 (hpos z hz)) e
  exact ⟨T, hTa.trans hT₀a, hTs, hTc, hTφ, isFlatOn_of_local R T hTφ hloc⟩

end GlobalTheory.CompanionTheory.Ar.Chg.FlatExt
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.PositiveHomogeneousPotentialStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)


theorem _root_.GlobalTheory.T.positive_homogeneous_potential : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J)) (D : ℕ) (R : AnLogRes P ⊤ D) (a : K → ℤ) (φ : ((Σ k, J k) → ℂ) → ℝ), (∀ z ∈ mcPts P, 0 < φ z) → (∀ z ∈ mcPts P, φ (fun p => starRingEnd ℂ (z p)) = φ z) → (∀ z ∈ mcPts P, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → φ (fun p => c p.1 * z p) = (∏ k, ‖c k‖ ^ a k) * φ z) → (∀ z ∈ mcPts P, ∃ (V : Set ((Σ k, J k) → ℂ)) (F : ((Σ k, J k) → ℂ) → ℂ), IsOpen V ∧ z ∈ V ∧ AnalyticOnNhd ℂ F V ∧ ∀ z' ∈ V ∩ mcPts P, F z' ≠ 0 ∧ φ z' = ‖F z'‖) → ∃ T : HermLine J, T.a = a ∧ IsSmoothHerm T ∧ IsConjInvariantH T ∧ (∀ z ∈ mcPts P, T.h z = φ z) ∧ IsFlatOn R T := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Chg.FlatExt.exists_flat_line | exact GlobalTheory.CompanionTheory.Ar.Chg.FlatExt.exists_flat_line | (intros; apply GlobalTheory.CompanionTheory.Ar.Chg.FlatExt.exists_flat_line <;> assumption)
end
end
