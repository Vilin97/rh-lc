module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AntisymmFibrePointTwo
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
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffAtHolomorphicComplexChartOfSmoothAtStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOnHolomorphicChartTransEtaleChartStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionTopCoeffCompHolomorphicJacobianSq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionTopCoeffHolomorphicFrameChangeStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernDensityFrameIndepChartJacobianFactor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicInvertibleFrameCoordinates
import Mathlib.Tactic.Basify
import Mathlib.Algebra.Azumaya.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChangeOfFrameHolomorphicInvertibleHolomorphicCha

section

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem analyticAt_ratVal_holoChart {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F}
    {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} (he : IsHoloChart e) {y : CxPts X.str σ} (hy : y ∈ e.source)
    {g : X.Fn} (hg : RegAt (under y) g) : AnalyticAt ℂ (fun v => ratVal g (e.symm v)) (e y) := by
  obtain ⟨U, hU, a, rfl⟩ := hg.exists_fnOf
  have hn : e.target ∩ e.symm ⁻¹' ptsIn X.str σ U ∈ 𝓝 (e y) := by
    refine Filter.inter_mem (e.open_target.mem_nhds (e.map_source hy)) ?_
    exact (e.tendsto_symm hy) ((isOpen_ptsIn U).mem_nhds (mem_ptsIn.2 hU))
  exact GlobalTheory.SCV.analyticAt_of_differentiableOn ((he U a).congr fun w hw => ratVal_fnOf hw.2 _ a) hn

theorem changeFrame_holoChart : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)}, IsHoloChart e → ∀ {y : CxPts X.str σ}, y ∈ e.source → ∀ {A A' : Mat (fun _ : Unit => m) X.Fn}, A ∈ E.S (under y) → A' ∈ E.S (under y) → MContDiffAt 2 (fun v => ((A' * A⁻¹).map (ratVal · (e.symm v)) ())ᵀ) (e y) ∧ IsUnit (((A' * A⁻¹).map (ratVal · (e.symm (e y))) ())ᵀ).det ∧ ∀ᶠ x in 𝓝 (e y), ∀ η, mdbar (fun v => ((A' * A⁻¹).map (ratVal · (e.symm v)) ())ᵀ) x η = 0 := by
  intro F _ σ X m E e he y hy A A' hA hA'
  have hP : Par 0 ((ratOf X).O (under y)).toSubring (A' * A⁻¹) := (Fr.mem_iff hA).1 hA'
  have han (i j : Fin m) : AnalyticAt ℂ (fun v => ((A' * A⁻¹).map (ratVal · (e.symm v)) ())ᵀ i j) (e y) :=
    analyticAt_ratVal_holoChart he hy (mem_O_ratOf.1 ((hP ()).1 j i))
  refine ⟨fun i j => ((han i j).contDiffAt (n := 2)).restrict_scalars ℝ, ?_, ?_⟩
  · obtain ⟨ψ, hψ⟩ := exists_ratVal_hom y
    rw [Matrix.det_transpose, e.left_inv hy]
    exact ((hP.map_of (ratVal · y) ψ hψ).det_ne ()).isUnit
  · have h : ∀ᶠ x in 𝓝 (e y), ∀ i j : Fin m,
        AnalyticAt ℂ (fun v => ((A' * A⁻¹).map (ratVal · (e.symm v)) ())ᵀ i j) x :=
      eventually_all.2 fun i => eventually_all.2 fun j => (han i j).eventually_analyticAt
    filter_upwards [h] with x hx η
    ext i j
    rw [mdbar_apply, GlobalTheory.dbar_eq_zero (hx i j).differentiableAt]
    rfl

end GlobalTheory.GoodTop
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChangeOfFrameHolomorphicInvertibleHolomorphicChaStatement

section

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.changeOfFrame_holomorphic_invertible_holomorphicChart : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)}, IsHoloChart e → ∀ {y : CxPts X.str σ}, y ∈ e.source → ∀ {A A' : Mat (fun _ : Unit => m) X.Fn}, A ∈ E.S (under y) → A' ∈ E.S (under y) → MContDiffAt 2 (fun v => ((A' * A⁻¹).map (ratVal · (e.symm v)) ())ᵀ) (e y) ∧ IsUnit (((A' * A⁻¹).map (ratVal · (e.symm (e y))) ())ᵀ).det ∧ ∀ᶠ x in 𝓝 (e y), ∀ η, mdbar (fun v => ((A' * A⁻¹).map (ratVal · (e.symm v)) ())ᵀ) x η = 0 := by
  first | exact @GlobalTheory.GoodTop.changeFrame_holoChart | exact GlobalTheory.GoodTop.changeFrame_holoChart | (intros; apply GlobalTheory.GoodTop.changeFrame_holoChart <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionTopCoeffCompHolomorphicJacobianSqStatement

section

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.transgressionTopCoeff_comp_holomorphic_jacobian_sq : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ρ : V n → ℝ} {G₀ G₁ : V n → Matrix r r ℂ} {φ : V n → V n} {w : V n}, ContDiffAt ℂ 2 φ w → DifferentiableAt ℝ ρ (φ w) → MContDiffAt 2 G₀ (φ w) → IsUnit (G₀ (φ w)).det → MContDiffAt 2 G₁ (φ w) → IsUnit (G₁ (φ w)).det → corrC (fun x => ρ (φ x)) (fun x => G₀ (φ x)) (fun x => G₁ (φ x)) w = ((‖(fderiv ℂ φ w).det‖ ^ 2 : ℝ) : ℂ) * corrC ρ G₀ G₁ (φ w) := by
  first | exact @GlobalTheory.GoodTop.corrC_comp_holo | exact GlobalTheory.GoodTop.corrC_comp_holo | (intros; apply GlobalTheory.GoodTop.corrC_comp_holo <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionTopCoeffComplexGermCongr

section

@[expose] public section

set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem curvAt_germ_congr {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {G G' : V n → Matrix r r ℂ} {v : V n}
    (h : G =ᶠ[𝓝 v] G') : curvAt G v = curvAt G' v := by
  funext a b
  exact curv_congr h _ _

theorem cutForm_germ_congr {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ρ ρ' : V n → ℝ}
    {G₀ G₁ G₀' G₁' : V n → Matrix r r ℂ} {v : V n} (hρ : ρ =ᶠ[𝓝 v] ρ') (h₀ : G₀ =ᶠ[𝓝 v] G₀')
    (h₁ : G₁ =ᶠ[𝓝 v] G₁') : cutForm ρ G₀ G₁ v = cutForm ρ' G₀' G₁' v := by
  funext a b
  have hc : (fun x => (ρ x : ℂ)) =ᶠ[𝓝 v] fun x => (ρ' x : ℂ) := hρ.mono fun x hx => by simp only [hx]
  simp only [cutForm]
  rw [dbar_congr hc, conn_congr h₀, conn_congr h₁]

theorem corrC_germ_congr {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ρ ρ' : V n → ℝ}
    {G₀ G₁ G₀' G₁' : V n → Matrix r r ℂ} {v : V n} (hρ : ρ =ᶠ[𝓝 v] ρ') (h₀ : G₀ =ᶠ[𝓝 v] G₀')
    (h₁ : G₁ =ᶠ[𝓝 v] G₁') : corrC ρ G₀ G₁ v = corrC ρ' G₀' G₁' v := by
  simp only [corrC]
  rw [curvAt_germ_congr h₀, curvAt_germ_congr h₁, cutForm_germ_congr hρ h₀ h₁]

end GlobalTheory.GoodTop
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionTopCoeffComplexGermCongrStatement

section

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.transgressionTopCoeffComplex_germ_congr : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ρ ρ' : V n → ℝ} {G₀ G₁ G₀' G₁' : V n → Matrix r r ℂ} {v : V n}, ρ =ᶠ[𝓝 v] ρ' → G₀ =ᶠ[𝓝 v] G₀' → G₁ =ᶠ[𝓝 v] G₁' → corrC ρ G₀ G₁ v = corrC ρ' G₀' G₁' v := by
  first | exact @GlobalTheory.GoodTop.corrC_germ_congr | exact GlobalTheory.GoodTop.corrC_germ_congr | (intros; apply GlobalTheory.GoodTop.corrC_germ_congr <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionDensityHolomorphicChartEtale

section

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem corrTop_holoChart_trans : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H H₀ : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → IsMetricOn E ⊤ H₀ → ∀ {ρ : CxPts X.str σ → ℝ}, (∀ y, CInfAt ρ y) → ∀ {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)}, IsHoloChart e → ∀ (c : AlgChart X.str σ X.dim) {y : CxPts X.str σ}, y ∈ ptsIn X.str σ O → y ∈ e.source → y ∈ c.e.source → ∀ {A : Mat (fun _ : Unit => m) X.Fn}, A ∈ E.S (under y) → corrTop (fun v => ρ (e.symm v)) (fun v => H₀ A (e.symm v) ()) (fun v => H A (e.symm v) ()) (e y) = ‖transDet e c.e y‖ ^ 2 * corrDens E H₀ H ρ c y := by
  intro F _ σ X m E O H H₀ hM hM₀ ρ hρ e he c y hy hey hcy A hA
  set A' := (E.nonempty (under y)).choose with hA'def
  have hA' : A' ∈ E.S (under y) := (E.nonempty (under y)).choose_spec
  have hy₀ : y ∈ ptsIn X.str σ (⊤ : X.X.Opens) := GlobalTheory.CxPts.mem_ptsIn_top

  set φ : V X.dim → V X.dim := c.e ∘ e.symm with hφ
  have ho := isOpen_over e c.e.open_source
  have hm := mem_over e hey hcy
  have e₂ : φ (e y) = c.e y := congrArg c.e (e.left_inv hey)
  have hφa : AnalyticAt ℂ φ (e y) :=
    GlobalTheory.SCV.analyticAt_of_differentiableOn (GlobalTheory.T.differentiableOn_holomorphicChart_trans_etaleChart he c) (ho.mem_nhds hm)

  set ρc : V X.dim → ℝ := fun v => ρ (c.e.symm v)
  set G₀ : Mat (fun _ : Unit => m) X.Fn → V X.dim → Matrix (Fin m) (Fin m) ℂ := fun B v => H₀ B (c.e.symm v) ()
  set G₁ : Mat (fun _ : Unit => m) X.Fn → V X.dim → Matrix (Fin m) (Fin m) ℂ := fun B v => H B (c.e.symm v) ()
  have hback : ∀ w ∈ e.target ∩ e.symm ⁻¹' c.e.source, c.e.symm (φ w) = e.symm w := fun w hw =>
    c.e.left_inv hw.2

  have step1 : corrC (fun v => ρ (e.symm v)) (fun v => H₀ A (e.symm v) ()) (fun v => H A (e.symm v) ()) (e y) =
      corrC (fun v => ρc (φ v)) (fun v => G₀ A (φ v)) (fun v => G₁ A (φ v)) (e y) := by
    apply GlobalTheory.T.transgressionTopCoeffComplex_germ_congr
    · filter_upwards [ho.mem_nhds hm] with w hw
      simp only [ρc, hback w hw]
    · filter_upwards [ho.mem_nhds hm] with w hw
      simp only [G₀, hback w hw]
    · filter_upwards [ho.mem_nhds hm] with w hw
      simp only [G₁, hback w hw]

  have hρc : ContDiffAt ℝ ∞ ρc (c.e y) := GlobalTheory.T.contDiffAt_holomorphicComplexChart_of_smoothAt c.holo hcy (hρ y)
  have hG₀ := hM₀.mContDiffAt_chart hy₀ c hcy hA ()
  have hG₀u := hM₀.isUnit_det_chart hy₀ c hcy hA ()
  have hG₁ := hM.mContDiffAt_chart hy c hcy hA ()
  have hG₁u := hM.isUnit_det_chart hy c hcy hA ()
  have step2 : corrC (fun v => ρc (φ v)) (fun v => G₀ A (φ v)) (fun v => G₁ A (φ v)) (e y) =
      ((‖(fderiv ℂ φ (e y)).det‖ ^ 2 : ℝ) : ℂ) * corrC ρc (G₀ A) (G₁ A) (φ (e y)) := by
    apply GlobalTheory.T.transgressionTopCoeff_comp_holomorphic_jacobian_sq (hφa.contDiffAt)
    · rw [e₂]; exact hρc.differentiableAt (by simp)
    · rw [e₂]; exact hG₀
    · rw [e₂]; exact hG₀u
    · rw [e₂]; exact hG₁
    · rw [e₂]; exact hG₁u

  obtain ⟨hQ, hQu, hQh⟩ := GlobalTheory.T.changeOfFrame_holomorphic_invertible_holomorphicChart E (e := c.e) c.holo hcy hA hA'
  have step3 : corrC ρc (G₀ A) (G₁ A) (c.e y) = corrC ρc (G₀ A') (G₁ A') (c.e y) := by
    rw [← GlobalTheory.T.transgressionTopCoeff_holomorphic_frame_change ρc hG₀ hG₀u hG₁ hG₁u hQ hQu hQh]
    have hO : ∀ᶠ z in 𝓝 y, z ∈ ptsIn X.str σ O := (isOpen_ptsIn O).mem_nhds hy
    have hev := (c.e.tendsto_symm hcy).eventually
      (hO.and ((GlobalTheory.FrameLift.eventually_mem hA).and (GlobalTheory.FrameLift.eventually_mem hA')))
    apply GlobalTheory.T.transgressionTopCoeffComplex_germ_congr
    · exact Filter.EventuallyEq.rfl
    · filter_upwards [hev] with w hw
      simp only [G₀, Matrix.transpose_transpose]
      rw [hM₀.trans _ GlobalTheory.CxPts.mem_ptsIn_top A hw.2.1 A' hw.2.2 ()]
      congr 1
    · filter_upwards [hev] with w hw
      simp only [G₁, Matrix.transpose_transpose]
      rw [hM.trans _ hw.1 A hw.2.1 A' hw.2.2 ()]
      congr 1
  simp only [corrTop, corrDens]
  rw [← hA'def]
  rw [step1, step2, e₂, step3, Complex.re_ofReal_mul]
  have hT : transDet e c.e y = (fderiv ℂ φ (e y)).det := rfl
  rw [hT]
  ring

end GlobalTheory.GoodTop
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionDensityHolomorphicChartEtaleStatement

section

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.transgressionDensity_holomorphicChart_etale : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H H₀ : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → IsMetricOn E ⊤ H₀ → ∀ {ρ : CxPts X.str σ → ℝ}, (∀ y, CInfAt ρ y) → ∀ {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)}, IsHoloChart e → ∀ (c : AlgChart X.str σ X.dim) {y : CxPts X.str σ}, y ∈ ptsIn X.str σ O → y ∈ e.source → y ∈ c.e.source → ∀ {A : Mat (fun _ : Unit => m) X.Fn}, A ∈ E.S (under y) → corrTop (fun v => ρ (e.symm v)) (fun v => H₀ A (e.symm v) ()) (fun v => H A (e.symm v) ()) (e y) = ‖transDet e c.e y‖ ^ 2 * corrDens E H₀ H ρ c y := by
  first | exact @GlobalTheory.GoodTop.corrTop_holoChart_trans | exact GlobalTheory.GoodTop.corrTop_holoChart_trans | (intros; apply GlobalTheory.GoodTop.corrTop_holoChart_trans <;> assumption)
end
end
