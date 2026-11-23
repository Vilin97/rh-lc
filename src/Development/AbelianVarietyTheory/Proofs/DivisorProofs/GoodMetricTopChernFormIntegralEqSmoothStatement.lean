module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.GoodTopChernForm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceComplexPointsOfProjVariety
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMulTopChernFormIsTopDegreeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodPatchOfComplexPointOpenPartStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedFrameEventuallyNearComplexPointStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothPartitionOfUnityComplexPointsStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasChernIntegralOfEqMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTopFormChartIntegralZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFiniteSumTopForms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTransgressionDensitiesPartitionUnityEqZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionCorrectionIsTopDegreeFormStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionTopChernFormGoodPatch

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPoincareGoodPatchOutsideOpen

section

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

set_option autoImplicit false

namespace GlobalTheory.GoodTop

theorem exists_goodPatch : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ}
    (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens)
    (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ),
    IsGood E O H → ∀ y ∉ ptsIn X.str σ O, ∃ e S A W c, y ∈ W ∧ GoodPatch E O H e S A W c := by
  intro F _ σ X m E O H hG y hy
  obtain ⟨e, S, hholo, hys, hy0, hcomp, A, hA, c, N, hev⟩ := hG y hy
  have h1 : ∀ᶠ z in 𝓝 y, z ∈ ptsIn X.str σ O → GoodBound S c N (fun v => H A (e.symm v) ()) (e z) :=
    (eventually_nhdsWithin_iff.1 hev).mono fun z hz hzO => hz hzO ()
  have h2 : ∀ᶠ z in 𝓝 y, A ∈ E.S (under z) := GlobalTheory.T.adaptedFrame_eventually_near_complexPoint E hA
  have h3 : ∀ᶠ z in 𝓝 y, z ∈ e.source := e.open_source.mem_nhds hys
  have h4 : ∀ᶠ z in 𝓝 y, ∀ a ∈ S, ‖e z a‖ ≤ 1 / 2 := by
    refine (Filter.eventually_all_finset S).2 fun a ha => ?_
    have hc : ContinuousAt (fun z => e z a) y :=
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin X.dim => ℂ) a).continuous.comp
        (PiLp.continuous_ofLp 2 _)).continuousAt.comp (e.continuousAt hys)
    have h0 : e y a = 0 := hy0 a ha
    have : ∀ᶠ z in 𝓝 y, e z a ∈ Metric.ball (0 : ℂ) (1 / 2) :=
      hc.preimage_mem_nhds (by rw [h0]; exact Metric.ball_mem_nhds _ (by norm_num))
    exact this.mono fun z hz => le_of_lt (by simpa using hz)
  obtain ⟨W, hW, hWo, hyW⟩ := eventually_nhds_iff.1 (h1.and (h2.and (h3.and h4)))
  refine ⟨e, S, A, W, c, hyW, ?_⟩
  exact
  { holo := hholo
    isOpen := hWo
    sub := fun z hz => (hW z hz).2.2.1
    frame := fun z hz => (hW z hz).2.1
    small := fun z hz => (hW z hz).2.2.2
    mem := fun z hz => by
      have := hcomp z (hW z hz).2.2.1
      constructor
      · intro hzO a ha h
        exact (this.2 ⟨a, ha, h⟩) hzO
      · intro hne
        by_contra hzO
        obtain ⟨a, ha, h⟩ := this.1 hzO
        exact hne a ha h
    form := fun z hz hzO a i j => ((hW z hz).1 hzO).form a i j
    dbar := fun z hz hzO a b i j => ((hW z hz).1 hzO).dbar a b i j }

end GlobalTheory.GoodTop
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPoincareGoodPatchOutsideOpenStatement

section

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.exists_poincareGoodPatch_outside_open : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsGood E O H → ∀ y ∉ ptsIn X.str σ O, ∃ e S A W c, y ∈ W ∧ GoodPatch E O H e S A W c := by
  first | exact @GlobalTheory.GoodTop.exists_goodPatch | exact GlobalTheory.GoodTop.exists_goodPatch | (intros; apply GlobalTheory.GoodTop.exists_goodPatch <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTopFormChartIntegralCongrOn

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix ENNReal

namespace GlobalTheory.GoodTop

theorem hasInt_congr_on : ∀ {n : ℕ} {Y κ : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (e : κ → OpenPartialHomeomorph Y (V n)) {S : Set Y}, MeasurableSet S → ∀ {d d' : κ → Y → ℝ} {t : ℝ},
    (∀ i y, y ∈ S → y ∈ (e i).source → d i y = d' i y) → HasInt e d S t → HasInt e d' S t := by
  intro n Y κ _ _ _ e S hS d d' t h hd
  have key : ∀ ε : ℤˣ, glueMeas e (fun i y => ENNReal.ofReal ((ε : ℤ) * d' i y)) S =
      glueMeas e (fun i y => ENNReal.ofReal ((ε : ℤ) * d i y)) S := by
    intro ε
    have hm := GlobalTheory.ChernScale.glueMeas_restrict_eq e
      (ρ := fun i y => ENNReal.ofReal ((ε : ℤ) * d' i y)) (ρ' := fun i y => ENNReal.ofReal ((ε : ℤ) * d i y))
      (c := 1) ENNReal.one_ne_top hS (fun i y hy hyS => by rw [one_mul, h i y hyS hy])
    have := congrArg (fun μ : Measure Y => μ S) hm
    simpa only [one_smul, Measure.restrict_apply_self] using this
  refine ⟨fun ε => by rw [key ε]; exact hd.1 ε, ?_⟩
  rw [← hd.2, measureReal_def, measureReal_def, measureReal_def, measureReal_def, key 1, key (-1)]

end GlobalTheory.GoodTop
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTopFormChartIntegralCongrOnStatement

section

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.hasTopFormChartIntegral_congr_on : ∀ {n : ℕ} {Y κ : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] (e : κ → OpenPartialHomeomorph Y (V n)) {S : Set Y}, MeasurableSet S → ∀ {d d' : κ → Y → ℝ} {t : ℝ}, (∀ i y, y ∈ S → y ∈ (e i).source → d i y = d' i y) → HasInt e d S t → HasInt e d' S t := by
  first | exact @GlobalTheory.GoodTop.hasInt_congr_on | exact GlobalTheory.GoodTop.hasInt_congr_on | (intros; apply GlobalTheory.GoodTop.hasInt_congr_on <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFiniteSumTopFormsStatement

section

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.integral_finite_sum_topForms : ∀ {n : ℕ} {Y κ : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y] (e : κ → OpenPartialHomeomorph Y (V n)), (∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' (e j).source)) → (∀ y, ∃ i, y ∈ (e i).source) → ∀ {S : Set Y}, MeasurableSet S → ∀ {ι : Type} [Fintype ι] {d : ι → κ → Y → ℝ} {t : ι → ℝ}, (∀ a, IsTopForm e (d a) S) → (∀ a, HasInt e (d a) S (t a)) → HasInt e (fun i y => ∑ a, d a i y) S (∑ a, t a) := by
  first | exact @GlobalTheory.GoodTop.hasInt_sum | exact GlobalTheory.GoodTop.hasInt_sum | (intros; apply GlobalTheory.GoodTop.hasInt_sum <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionTopChernFormGoodPatchStatement

section

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.transgression_topChernForm_goodPatch : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H H₀ : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → IsMetricOn E ⊤ H₀ → ∀ {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} {S : Finset (Fin X.dim)} {A : Mat (fun _ : Unit => m) X.Fn} {W : Set (CxPts X.str σ)} {c : ℝ}, GoodPatch E O H e S A W c → ∀ {ρ : CxPts X.str σ → ℝ}, (∀ y, CInfAt ρ y) → tsupport ρ ⊆ W → ∃ a b : ℝ, HasInt (fun c : AlgChart X.str σ X.dim => c.e) (fun c y => ρ y * topDens E H c y) (ptsIn X.str σ O) a ∧ HasInt (fun c : AlgChart X.str σ X.dim => c.e) (fun c y => ρ y * topDens E H₀ c y) (ptsIn X.str σ ⊤) b ∧ HasInt (fun c : AlgChart X.str σ X.dim => c.e) (corrDens E H₀ H ρ) (ptsIn X.str σ O) (a - b) := by
  first | exact @GlobalTheory.GoodTop.hasInt_patch_transgression | exact GlobalTheory.GoodTop.hasInt_patch_transgression | (intros; apply GlobalTheory.GoodTop.hasInt_patch_transgression <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodMetricTopChernFormIntegralEqSmooth

section

@[expose] public section

open AlgebraicGeometry MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)

namespace GlobalTheory.GoodTop

theorem goodTopChernForm : GlobalTheory.Published.GoodTopChernForm := by
  intro F _ σ X m E O H H₀ hH hG hH₀ t ht
  rw [hasChernIntegral_iff] at ht ⊢
  haveI := X.smooth_str
  haveI : SecondCountableTopology (CxPts X.str σ) := inferInstance
  have hp : ∀ y : CxPts X.str σ, ∃ e S A W c, y ∈ W ∧ GoodPatch E O H e S A W c := fun y => by
    by_cases hy : y ∈ ptsIn X.str σ O
    · exact GlobalTheory.T.exists_goodPatch_of_complexPoint_openPart E O H hH y hy
    · exact GlobalTheory.T.exists_poincareGoodPatch_outside_open E O H hG y hy
  choose e S A W c hyW hP using hp
  obtain ⟨s, ρ, hρ, hsupp, hsum⟩ := GlobalTheory.T.exists_smooth_partition_of_unity_complexPoints W fun y => (hP y).isOpen.mem_nhds (hyW y)
  choose a b ha hb hab using fun i : s => GlobalTheory.T.transgression_topChernForm_goodPatch E O H H₀ hH hH₀ (hP i) (hρ i) (hsupp i)
  have hd : ∀ i j : AlgChart X.str σ X.dim,
      DifferentiableOn ℂ (j.e ∘ i.e.symm) (i.e.target ∩ i.e.symm ⁻¹' j.e.source) := fun i j => i.holo_trans j
  have hcov : ∀ y, ∃ i : AlgChart X.str σ X.dim, y ∈ i.e.source := fun y => AlgChart.exists_mem_source y
  have hm : ∀ U : X.X.Opens, MeasurableSet (ptsIn X.str σ U) := fun U => (isOpen_ptsIn U).measurableSet
  have hc : ∀ i, Continuous (ρ i) := fun i => continuous_iff_continuousAt.2 fun y => (hρ i y).continuousAt
  have h₁ : HasInt (fun c : AlgChart X.str σ X.dim => c.e) (topDens E H) (ptsIn X.str σ O) (∑ i, a i) := by
    refine GlobalTheory.T.hasTopFormChartIntegral_congr_on _ (hm O) (fun i y _ _ => ?_)
      (GlobalTheory.T.integral_finite_sum_topForms _ hd hcov (hm O) (fun i => GlobalTheory.T.continuous_mul_top_chern_form_isTopDegree E O H hH (hc i)) ha)
    rw [← Finset.sum_mul, hsum, one_mul]
  have h₂ : HasInt (fun c : AlgChart X.str σ X.dim => c.e) (topDens E H₀) (ptsIn X.str σ ⊤) (∑ i, b i) := by
    refine GlobalTheory.T.hasTopFormChartIntegral_congr_on _ (hm ⊤) (fun i y _ _ => ?_)
      (GlobalTheory.T.integral_finite_sum_topForms _ hd hcov (hm ⊤) (fun i => GlobalTheory.T.continuous_mul_top_chern_form_isTopDegree E ⊤ H₀ hH₀ (hc i)) hb)
    rw [← Finset.sum_mul, hsum, one_mul]
  have h₃ : HasInt (fun c : AlgChart X.str σ X.dim => c.e) (fun _ _ => 0) (ptsIn X.str σ O) (∑ i, (a i - b i)) :=
    GlobalTheory.T.hasTopFormChartIntegral_congr_on _ (hm O) (fun i y _ hy => GlobalTheory.T.sum_transgression_densities_partition_unity_eq_zero E O H H₀ ρ hρ hsum i y hy)
      (GlobalTheory.T.integral_finite_sum_topForms _ hd hcov (hm O) (fun i => GlobalTheory.T.transgression_correction_isTopDegreeForm E O H H₀ hH hH₀ (hρ i)) hab)
  have e₂ : ∑ i, b i = t := h₂.2.symm.trans ht.2
  have e₃ : ∑ i, (a i - b i) = 0 := h₃.2.symm.trans (GlobalTheory.T.hasTopFormChartIntegral_zero _ _).2
  rw [Finset.sum_sub_distrib, sub_eq_zero, e₂] at e₃
  exact e₃ ▸ h₁

end GlobalTheory.GoodTop
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodMetricTopChernFormIntegralEqSmoothStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.goodMetric_topChernForm_integral_eq_smooth : GlobalTheory.Published.GoodTopChernForm := by
  first | exact @GlobalTheory.GoodTop.goodTopChernForm | exact GlobalTheory.GoodTop.goodTopChernForm | (intros; apply GlobalTheory.GoodTop.goodTopChernForm <;> assumption)
end
end
