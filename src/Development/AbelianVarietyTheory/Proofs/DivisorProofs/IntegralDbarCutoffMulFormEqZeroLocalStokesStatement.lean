module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIsFormDelDbarSmoothStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeDensityPullbackEqNormSqDetMul
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.UniformSpace.Uniformizable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralReTopDegreeDensityDbarEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormOneAddMulSmulStatement
import Mathlib.Tactic.Basify

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqEuclideanIntegralOfSupportInChart

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)

namespace GlobalTheory.CxForm.HolAtlas

theorem integral_eq_integral_chart_of_support : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (α : A.Fld)
    (i : A.ι) (K : Set M), A.IsForm α → IsCompact K → K ⊆ (A.e i).source → (∀ x : A.Pt, x.pt ∉ K → α x = 0) →
    A.integral α = ∫ v, (GlobalTheory.CxForm.dens (A.loc α i v)).re := by
  intro M _ _ _ _ _ _ n A α i K hα hK hKs h0
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  set r : A.ι → V n → ℝ := fun j v => (dens (A.loc α j v)).re with hr
  have dens_zero : dens (0 : Alt n) = 0 := by simp [dens]

  have hc : ∀ j k y, y ∈ (A.e j).source → y ∈ (A.e k).source →
      r j (A.e j y) = ‖ChartGlue.transDet (A.e j) (A.e k) y‖ ^ 2 * r k (A.e k y) := by
    intro j k y hj hk
    have h1 := A.loc_crd α (⟨(j, y), hj⟩ : A.Pt)
    have h2 := A.loc_crd α (⟨(k, y), hk⟩ : A.Pt)
    have h3 := hα.compat (⟨(j, y), hj⟩ : A.Pt) ⟨(k, y), hk⟩ rfl
    simp only [hr]
    erw [h1, h2, h3, dens_pull]
    rw [Complex.re_ofReal_mul]
    rfl

  have hz : ∀ j y, y ∈ (A.e j).source → y ∉ K → r j (A.e j y) = 0 := by
    intro j y hj hy
    have h1 := A.loc_crd α (⟨(j, y), hj⟩ : A.Pt)
    simp only [hr]
    erw [h1, h0 _ hy, dens_zero]
    rfl

  have hpart : ∀ ε : ℤˣ, A.part α ε univ =
      ∫⁻ v in A.e i '' K, ENNReal.ofReal (((ε : ℤ) : ℝ) * r i v) := by
    intro ε
    set ρ : A.ι → M → ENNReal := fun j y => ENNReal.ofReal (((ε : ℤ) : ℝ) * r j (A.e j y)) with hρ
    have hp : A.part α ε = ChartGlue.glueMeas A.e ρ := rfl
    have hρc : ∀ j k y, y ∈ (A.e j).source → y ∈ (A.e k).source →
        ρ j y = ENNReal.ofReal (‖ChartGlue.transDet (A.e j) (A.e k) y‖ ^ 2) * ρ k y := by
      intro j k y hj hk
      simp only [hρ]
      rw [hc j k y hj hk, ← ENNReal.ofReal_mul (by positivity)]
      ring_nf
    have hcompl : ChartGlue.glueMeas A.e ρ Kᶜ = 0 := by
      have key : ChartGlue.glueMeas A.e ρ ≤ (ChartGlue.glueMeas A.e ρ).restrict K := iSup_le fun j => by
        have e : ChartGlue.chartMeas (A.e j) (ρ j) Kᶜ = 0 := by
          rw [ChartGlue.chartMeas_apply _ _ hKm.compl]
          refine setLIntegral_eq_zero (ChartGlue.measurableSet_image _
            ((A.e j).open_source.measurableSet.inter hKm.compl) Set.inter_subset_left) ?_
          rintro _ ⟨y, hy, rfl⟩
          simp only [hρ, (A.e j).left_inv hy.1, hz j y hy.1 hy.2, mul_zero, ENNReal.ofReal_zero, Pi.zero_apply]
        rw [← Measure.restrict_eq_self_of_ae_mem (s := K) (mem_ae_iff.2 e)]
        exact Measure.restrict_mono le_rfl (le_iSup (fun j => ChartGlue.chartMeas (A.e j) (ρ j)) j)
      refine le_antisymm ((key Kᶜ).trans_eq ?_) bot_le
      rw [Measure.restrict_apply hKm.compl, Set.compl_inter_self, measure_empty]
    rw [hp, ← measure_add_measure_compl hKm, hcompl, add_zero,
      ChartGlue.glueMeas_apply A.e ρ A.holo hρc i hKm hKs, ChartGlue.chartMeas_apply_of_subset _ _ hKm hKs]
    refine setLIntegral_congr_fun (ChartGlue.measurableSet_image _ hKm hKs) ?_
    rintro _ ⟨y, hy, rfl⟩
    simp only [hρ, (A.e i).left_inv (hKs hy)]

  have hBc : IsCompact (A.e i '' K) := hK.image_of_continuousOn ((A.e i).continuousOn.mono hKs)
  have hBt : A.e i '' K ⊆ (A.e i).target := by
    rintro _ ⟨y, hy, rfl⟩
    exact (A.e i).map_source (hKs hy)
  have hH0 : ∀ v ∉ A.e i '' K, r i v = 0 := by
    intro v hv
    by_cases ht : v ∈ (A.e i).target
    · have hs := (A.e i).map_target ht
      have hnK : (A.e i).symm v ∉ K := fun hk => hv ⟨_, hk, (A.e i).right_inv ht⟩
      have := hz i _ hs hnK
      rwa [(A.e i).right_inv ht] at this
    · have hl : A.loc α i v = 0 := by
        unfold loc
        exact dif_neg ht
      simp only [hr, hl, dens_zero, Complex.zero_re]
  have hcon : ContinuousOn (r i) (A.e i).target :=
    Complex.continuous_re.comp_continuousOn ((hα.smooth i Finset.univ).continuousOn.div_const _)
  have hHc : Continuous (r i) := continuous_iff_continuousAt.2 fun v => by
    by_cases ht : v ∈ (A.e i).target
    · exact hcon.continuousAt ((A.e i).open_target.mem_nhds ht)
    · have : r i =ᶠ[𝓝 v] fun _ => 0 := by
        filter_upwards [hBc.isClosed.isOpen_compl.mem_nhds (fun h => ht (hBt h))] with w hw
        exact hH0 w hw
      exact continuousAt_const.congr this.symm
  have hHi : Integrable (r i) := hHc.integrable_of_hasCompactSupport (HasCompactSupport.intro hBc hH0)
  have hl : ∀ ε : ℤˣ, ∫⁻ v in A.e i '' K, ENNReal.ofReal (((ε : ℤ) : ℝ) * r i v) =
      ∫⁻ v, ENNReal.ofReal (((ε : ℤ) : ℝ) * r i v) := by
    intro ε
    rw [← lintegral_indicator hBc.measurableSet]
    refine lintegral_congr fun v => ?_
    by_cases hv : v ∈ A.e i '' K
    · rw [Set.indicator_of_mem hv]
    · rw [Set.indicator_of_notMem hv, hH0 v hv, mul_zero, ENNReal.ofReal_zero]
  have e1 := hpart 1
  have e2 := hpart (-1)
  rw [hl] at e1 e2
  simp only [Units.val_one, Int.cast_one, one_mul, Units.val_neg, Int.cast_neg, neg_one_mul] at e1 e2
  simp only [GlobalTheory.CxForm.HolAtlas.integral, Measure.real, e1, e2]
  exact (integral_eq_lintegral_pos_part_sub_lintegral_neg_part hHi).symm

end GlobalTheory.CxForm.HolAtlas
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqEuclideanIntegralOfSupportInChartStatement

section

@[expose] public section

open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)

theorem _root_.GlobalTheory.T.integral_eq_euclidean_integral_of_support_in_chart : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (α : A.Fld) (i : A.ι) (K : Set M), A.IsForm α → IsCompact K → K ⊆ (A.e i).source → (∀ x : A.Pt, x.pt ∉ K → α x = 0) → A.integral α = ∫ v, (GlobalTheory.CxForm.dens (A.loc α i v)).re := by
  exact @GlobalTheory.CxForm.HolAtlas.integral_eq_integral_chart_of_support
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralReTopDegreeDensityDbarEqZeroStatement

section

@[expose] public section

open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)

theorem _root_.GlobalTheory.T.integral_re_topDegreeDensity_dbar_eq_zero : ∀ {n : ℕ} (F : V n → GlobalTheory.CxForm.Alt n), (∀ S, ContDiff ℝ 1 (fun v => (GlobalTheory.CxForm.bas n).repr (F v) S)) → HasCompactSupport F → ∫ v, (GlobalTheory.CxForm.dens (GlobalTheory.CxForm.dbarAt F v)).re = 0 := by
  first | exact @GlobalTheory.CxForm.integral_re_dens_dbarAt_eq_zero | exact GlobalTheory.CxForm.integral_re_dens_dbarAt_eq_zero | (intros; apply GlobalTheory.CxForm.integral_re_dens_dbarAt_eq_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDbarCutoffMulFormEqZeroLocalStokes

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open Set Filter Topology Matrix MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame
open GlobalTheory.GoodMetric (coordVec)
open scoped ComplexOrder ContDiff

namespace GlobalTheory.CxForm.DbarLocStokes

open GlobalTheory.CxForm GlobalTheory.CxForm.HolAtlas

theorem dbarAt_eq_zero_of_eventually {n : ℕ} {F : V n → Alt n} {v : V n} (h : F =ᶠ[𝓝 v] fun _ => 0) :
    dbarAt F v = 0 := by
  refine Finset.sum_eq_zero fun a _ => ?_
  have : coefwise (fun f => GlobalTheory.dbar f v (coordVec a)) F = 0 := by
    refine Finset.sum_eq_zero fun S _ => ?_
    have hS : (fun x => (bas n).repr (F x) S) =ᶠ[𝓝 v] fun _ => (0 : ℂ) := by
      filter_upwards [h] with x hx
      simp [hx]
    beta_reduce
    rw [GlobalTheory.dbar_congr hS, GlobalTheory.dbar_const]
    simp
  rw [this, mul_zero]

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem loc_fn_mul_eq_zero (γ : A.Fld) (χ : M → ℝ) (j : A.ι) (w : V n)
    (h : w ∈ (A.e j).target → χ ((A.e j).symm w) = 0) : A.loc (A.fn χ * γ) j w = 0 := by
  unfold HolAtlas.loc
  split_ifs with hw
  · have key : ∀ x : A.Pt, x.pt = (A.e j).symm w → (A.fn χ * γ) x = 0 := fun x hx => by
      rw [Pi.mul_apply, HolAtlas.fn, hx, h hw]; simp
    exact key _ rfl
  · rfl

end GlobalTheory.CxForm.DbarLocStokes

namespace GlobalTheory.CxForm.DbarLocStokes

open GlobalTheory.CxForm GlobalTheory.CxForm.HolAtlas

theorem integral_dbar_fn_mul_eq_zero : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (γ : A.Fld) (χ : M → ℝ) (i : A.ι), A.IsForm γ → A.SmoothOn univ (fun y => (χ y : ℂ)) → tsupport χ ⊆ (A.e i).source → A.integral (A.dbar (A.fn χ * γ)) = 0 := by
  intro M _ _ _ _ _ _ n A γ χ i hγ hχ hK
  set K := tsupport χ with hKdef
  have hKc : IsCompact K := (isClosed_tsupport χ).isCompact
  have hP : A.IsForm (A.fn χ * γ) :=
    ((GlobalTheory.T.isForm_one_add_mul_smul M n A).2 0 _ _ (A.isForm_fn hχ) hγ).2.1
  have hω : A.IsForm (A.dbar (A.fn χ * γ)) :=
    (GlobalTheory.T.holAtlas_isForm_del_dbar_smooth M n A _ hP).2

  have hnear : ∀ (j : A.ι) (w : V n), w ∈ (A.e j).target → (A.e j).symm w ∉ K →
      A.loc (A.fn χ * γ) j =ᶠ[𝓝 w] fun _ => 0 := by
    intro j w hw hwK
    have hW := ChartGlue.isOpen_over (A.e j) (isClosed_tsupport χ).isOpen_compl
    filter_upwards [hW.mem_nhds ⟨hw, hwK⟩] with u hu
    exact loc_fn_mul_eq_zero A γ χ j u fun _ => image_eq_zero_of_notMem_tsupport hu.2
  have hvan : ∀ x : A.Pt, x.pt ∉ K → A.dbar (A.fn χ * γ) x = 0 := by
    intro x hx
    refine dbarAt_eq_zero_of_eventually (hnear _ _ (x.ch.map_source x.2) ?_)
    rwa [x.ch.left_inv x.2]
  rw [GlobalTheory.T.integral_eq_euclidean_integral_of_support_in_chart A _ i K hω hKc hK hvan]

  set F := A.loc (A.fn χ * γ) i with hFdef
  set B : Set (V n) := A.e i '' K with hBdef
  have hB : IsCompact B := hKc.image_of_continuousOn ((A.e i).continuousOn.mono hK)
  have hBt : B ⊆ (A.e i).target := by
    rintro _ ⟨y, hy, rfl⟩
    exact (A.e i).map_source (hK hy)
  have hF0 : ∀ v ∉ B, F =ᶠ[𝓝 v] fun _ => 0 := by
    intro v hv
    filter_upwards [hB.isClosed.isOpen_compl.mem_nhds hv] with u hu
    refine loc_fn_mul_eq_zero A γ χ i u fun ht => image_eq_zero_of_notMem_tsupport fun hk => hu ⟨_, hk, ?_⟩
    exact (A.e i).right_inv ht
  have hFs : HasCompactSupport F := HasCompactSupport.intro hB fun v hv => (hF0 v hv).self_of_nhds
  have hFC : ∀ S, ContDiff ℝ 1 (fun v => (bas n).repr (F v) S) := fun S =>
    contDiff_iff_contDiffAt.2 fun v => by
      by_cases ht : v ∈ (A.e i).target
      · exact ((hP.smooth i S).contDiffAt ((A.e i).open_target.mem_nhds ht)).of_le (by norm_num)
      · have h0 : (fun v => (bas n).repr (F v) S) =ᶠ[𝓝 v] fun _ => (0 : ℂ) := by
          filter_upwards [hF0 v fun h => ht (hBt h)] with u hu
          simp [hu]
        exact contDiffAt_const.congr_of_eventuallyEq h0
  have hloc : A.loc (A.dbar (A.fn χ * γ)) i = dbarAt F := by
    funext v
    by_cases ht : v ∈ (A.e i).target
    · rw [HolAtlas.loc, dite_eq_left ht]
      simp only [HolAtlas.dbar, Pt.crd, Pt.ch, (A.e i).right_inv ht]
      rfl
    · rw [HolAtlas.loc, dite_eq_right ht, dbarAt_eq_zero_of_eventually (hF0 v fun h => ht (hBt h))]
  rw [hloc]
  exact GlobalTheory.T.integral_re_topDegreeDensity_dbar_eq_zero F hFC hFs

end GlobalTheory.CxForm.DbarLocStokes
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDbarCutoffMulFormEqZeroLocalStokesStatement

section

@[expose] public section

open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.integral_dbar_cutoff_mul_form_eq_zero_local_stokes : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (γ : A.Fld) (χ : M → ℝ) (i : A.ι), A.IsForm γ → A.SmoothOn univ (fun y => (χ y : ℂ)) → tsupport χ ⊆ (A.e i).source → A.integral (A.dbar (A.fn χ * γ)) = 0 := by
  first | exact @GlobalTheory.CxForm.DbarLocStokes.integral_dbar_fn_mul_eq_zero | exact GlobalTheory.CxForm.DbarLocStokes.integral_dbar_fn_mul_eq_zero | (intros; apply GlobalTheory.CxForm.DbarLocStokes.integral_dbar_fn_mul_eq_zero <;> assumption)
end
end
