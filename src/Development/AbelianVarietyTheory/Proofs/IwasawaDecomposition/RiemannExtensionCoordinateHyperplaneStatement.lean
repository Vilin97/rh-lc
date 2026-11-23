module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.RemovableSingularity
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Analysis.Calculus.DiffContOnCl
public import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Order.CompletePartialOrder

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CauchySliceEqRemovableExtension

section

@[expose] public section

open Metric Filter Topology Set

namespace GlobalTheory

theorem cauchy_slice_removable_extension :
    ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (k : Fin n) (f : (Fin n → ℂ) → ℂ) (z₀ : Fin n → ℂ) (r M : ℝ), 0 < r → z₀ k = 0 → IsOpen U → Metric.ball z₀ (2 * r) ⊆ U → DifferentiableOn ℂ f {z | z ∈ U ∧ z k ≠ 0} → (∀ z ∈ Metric.ball z₀ (2 * r), z k ≠ 0 → ‖f z‖ ≤ M) → ∀ z ∈ Metric.ball z₀ r, (2 * (Real.pi : ℂ) * Complex.I)⁻¹ • (∮ t in C(0, r), (t - z k)⁻¹ • f (Function.update z k t)) = (if z k = 0 then limUnder (nhdsWithin (0 : ℂ) {0}ᶜ) (fun t => f (Function.update z k t)) else f z) := by
  intro n U k f z₀ r M hr hz₀ _hU hball hd hM z hz
  set s : ℂ → ℂ := fun t => f (Function.update z k t) with hs_def

  have hupd : Differentiable ℂ (fun t : ℂ => Function.update z k t) :=
    (contDiff_update (𝕜 := ℂ) 1 z k).differentiable (by norm_num)
  have hzdist : ∀ j, ‖z j - z₀ j‖ < r := by
    intro j
    have h1 : dist z z₀ < r := hz
    rw [dist_pi_lt_iff hr] at h1
    simpa [dist_eq_norm] using h1 j
  have hzk : ‖z k‖ < r := by simpa [hz₀] using hzdist k
  have hmem : ∀ t : ℂ, ‖t‖ < 2 * r → Function.update z k t ∈ Metric.ball z₀ (2 * r) := by
    intro t ht
    rw [Metric.mem_ball, dist_pi_lt_iff (by linarith)]
    intro j
    by_cases hj : j = k
    · subst hj
      simpa [dist_eq_norm, hz₀] using ht
    · rw [Function.update_of_ne hj, dist_eq_norm]
      linarith [hzdist j]
  have hsd : DifferentiableOn ℂ s (Metric.ball (0 : ℂ) (2 * r) \ {0}) := by
    refine hd.comp hupd.differentiableOn ?_
    intro t ht
    have ht1 : ‖t‖ < 2 * r := by simpa using ht.1
    have ht2 : t ≠ 0 := ht.2
    exact ⟨hball (hmem t ht1), by simpa using ht2⟩
  have hsb : BddAbove (norm ∘ s '' (Metric.ball (0 : ℂ) (2 * r) \ {0})) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    have ht1 : ‖t‖ < 2 * r := by simpa using ht.1
    have ht2 : t ≠ 0 := ht.2
    exact hM _ (hmem t ht1) (by simpa using ht2)
  have hg := Complex.differentiableOn_update_limUnder_of_bddAbove
    (Metric.ball_mem_nhds (0 : ℂ) (by linarith)) hsd hsb
  set g := Function.update s 0 (limUnder (𝓝[≠] (0 : ℂ)) s) with hg_def
  have hgc : DifferentiableOn ℂ g (Metric.closedBall 0 r) :=
    hg.mono (Metric.closedBall_subset_ball (by linarith))
  have hw : z k ∈ Metric.ball (0 : ℂ) r := by simpa using hzk
  have hcauchy := (hgc.mono closure_ball_subset_closedBall).diffContOnCl.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hw
  have hcongr : (∮ t in C(0, r), (t - z k)⁻¹ • g t) = (∮ t in C(0, r), (t - z k)⁻¹ • s t) := by
    refine circleIntegral.integral_congr hr.le ?_
    intro t ht
    have ht0 : t ≠ 0 := by
      intro h0
      rw [h0, mem_sphere_zero_iff_norm, norm_zero] at ht
      linarith
    simp only [hg_def, Function.update_of_ne ht0]
  rw [hcongr] at hcauchy
  rw [hcauchy]
  by_cases h0 : z k = 0
  · rw [if_pos h0, h0, hg_def, Function.update_self]
  · rw [if_neg h0, hg_def, Function.update_of_ne h0, hs_def]
    simp only [Function.update_eq_self]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CauchySliceEqRemovableExtensionStatement

section

@[expose] public section

open Metric Filter Topology Set

theorem _root_.GlobalTheory.T.cauchy_slice_eq_removable_extension : ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (k : Fin n) (f : (Fin n → ℂ) → ℂ) (z₀ : Fin n → ℂ) (r M : ℝ), 0 < r → z₀ k = 0 → IsOpen U → Metric.ball z₀ (2 * r) ⊆ U → DifferentiableOn ℂ f {z | z ∈ U ∧ z k ≠ 0} → (∀ z ∈ Metric.ball z₀ (2 * r), z k ≠ 0 → ‖f z‖ ≤ M) → ∀ z ∈ Metric.ball z₀ r, (2 * (Real.pi : ℂ) * Complex.I)⁻¹ • (∮ t in C(0, r), (t - z k)⁻¹ • f (Function.update z k t)) = (if z k = 0 then limUnder (nhdsWithin (0 : ℂ) {0}ᶜ) (fun t => f (Function.update z k t)) else f z) := by
  first | exact @GlobalTheory.cauchy_slice_removable_extension | exact GlobalTheory.cauchy_slice_removable_extension | (intros; apply GlobalTheory.cauchy_slice_removable_extension <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableAtCoordinateCauchyIntegral

section

@[expose] public section

open Metric Filter Topology Set

noncomputable section

namespace GlobalTheory

def updCLM (n : ℕ) (k : Fin n) : ((Fin n → ℂ) × ℂ) →L[ℂ] (Fin n → ℂ) :=
  ContinuousLinearMap.pi fun i =>
    if i = k then ContinuousLinearMap.snd ℂ (Fin n → ℂ) ℂ
    else (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℂ (Fin n → ℂ) ℂ)

theorem updCLM_apply (n : ℕ) (k : Fin n) (p : (Fin n → ℂ) × ℂ) :
    updCLM n k p = Function.update p.1 k p.2 := by
  funext i
  simp only [updCLM, ContinuousLinearMap.pi_apply, Function.update_apply]
  split_ifs <;> simp

theorem cauchyCoord_differentiableAt :
    ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (k : Fin n) (f : (Fin n → ℂ) → ℂ) (z₀ : Fin n → ℂ) (r : ℝ),
      0 < r → z₀ k = 0 → IsOpen U → Metric.closedBall z₀ r ⊆ U →
      DifferentiableOn ℂ f {z | z ∈ U ∧ z k ≠ 0} →
      DifferentiableAt ℂ (fun z => ∮ t in C(0, r), (t - z k)⁻¹ • f (Function.update z k t)) z₀ := by
  intro n U k f z₀ r hr hz₀ hU hball hf
  set V : Set (Fin n → ℂ) := {z | z ∈ U ∧ z k ≠ 0} with hVdef
  have hV : IsOpen V := hU.inter (isOpen_ne_fun (continuous_apply k) continuous_const)
  have hfa : AnalyticOnNhd ℂ f V := ReciprocityTheory.AnForm.Osgood.osgood n V f hV hf
  set Φ : (Fin n → ℂ) × ℂ → ℂ := fun p => (p.2 - p.1 k)⁻¹ • f (Function.update p.1 k p.2) with hΦdef
  set Wd : Set ((Fin n → ℂ) × ℂ) := {p | Function.update p.1 k p.2 ∈ V ∧ p.2 - p.1 k ≠ 0} with hWdef
  have hupd : Continuous fun p : (Fin n → ℂ) × ℂ => Function.update p.1 k p.2 :=
    continuous_fst.update k continuous_snd
  have hWo : IsOpen Wd :=
    (hV.preimage hupd).inter (isOpen_ne_fun (continuous_snd.sub ((continuous_apply k).comp continuous_fst))
      continuous_const)
  have hΦa : AnalyticOnNhd ℂ Φ Wd := by
    intro p hp
    have h1 : AnalyticAt ℂ (fun p : (Fin n → ℂ) × ℂ => Function.update p.1 k p.2) p := by
      have he : (fun p : (Fin n → ℂ) × ℂ => Function.update p.1 k p.2) = updCLM n k :=
        funext fun p => (updCLM_apply n k p).symm
      rw [he]; exact (updCLM n k).analyticAt p
    have h2 : AnalyticAt ℂ (fun p : (Fin n → ℂ) × ℂ => f (Function.update p.1 k p.2)) p :=
      AnalyticAt.comp (g := f) (f := fun p : (Fin n → ℂ) × ℂ => Function.update p.1 k p.2) (hfa _ hp.1) h1
    have h3 : AnalyticAt ℂ (fun p : (Fin n → ℂ) × ℂ => p.2 - p.1 k) p :=
      analyticAt_snd.sub (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) k).analyticAt _).comp
        analyticAt_fst)
    exact (h3.inv hp.2).smul h2
  have hΦc : ContinuousOn Φ Wd := hΦa.continuousOn
  have hD : ContinuousOn (fun p => fderiv ℂ Φ p) Wd :=
    (hΦa.contDiffOn_of_completeSpace (n := 1)).continuousOn_fderiv_of_isOpen hWo le_rfl

  set K : Set ((Fin n → ℂ) × ℂ) := closedBall z₀ (r / 2) ×ˢ sphere (0 : ℂ) r
  have hKc : IsCompact K := (isCompact_closedBall _ _).prod (isCompact_sphere _ _)
  have hKW : K ⊆ Wd := by
    rintro ⟨z, t⟩ ⟨hz, ht⟩
    simp only [mem_closedBall, mem_sphere_iff_norm, sub_zero] at hz ht
    have hzk : ‖z k‖ ≤ r / 2 := by
      have := dist_le_pi_dist z z₀ k
      rw [hz₀, dist_zero_right] at this
      linarith [this]
    refine ⟨⟨hball ?_, ?_⟩, ?_⟩
    · rw [mem_closedBall, dist_pi_le_iff hr.le]
      intro i
      by_cases hi : i = k
      · subst hi; simp [hz₀, ht]
      · rw [Function.update_of_ne hi]
        exact (dist_le_pi_dist z z₀ i).trans (by linarith)
    · simp only [Function.update_self]
      intro h; rw [h, norm_zero] at ht; linarith
    · intro h
      have : t = z k := sub_eq_zero.mp h
      rw [this] at ht; linarith
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn (hD.mono hKW)
  have hcirc : ∀ θ : ℝ, circleMap 0 r θ ∈ sphere (0 : ℂ) r := fun θ => circleMap_mem_sphere 0 hr.le θ
  have hmemW : ∀ z ∈ closedBall z₀ (r / 2), ∀ θ : ℝ, (z, circleMap 0 r θ) ∈ Wd := fun z hz θ =>
    hKW ⟨hz, hcirc θ⟩
  have hderc : Continuous fun θ => deriv (circleMap 0 r) θ := by
    have : (fun θ => deriv (circleMap 0 r) θ) = fun θ => circleMap 0 r θ * Complex.I :=
      funext fun θ => deriv_circleMap 0 r θ
    rw [this]; exact (continuous_circleMap 0 r).mul continuous_const
  have hpath : ∀ z : Fin n → ℂ, Continuous fun θ : ℝ => (z, circleMap 0 r θ) := fun z =>
    continuous_const.prodMk (continuous_circleMap 0 r)
  have hr2 : 0 < r / 2 := half_pos hr
  set F : (Fin n → ℂ) → ℝ → ℂ := fun z θ => deriv (circleMap 0 r) θ • Φ (z, circleMap 0 r θ)
  set F' : (Fin n → ℂ) → ℝ → (Fin n → ℂ) →L[ℂ] ℂ := fun z θ =>
    deriv (circleMap 0 r) θ • (fderiv ℂ Φ (z, circleMap 0 r θ)).comp (ContinuousLinearMap.inl ℂ (Fin n → ℂ) ℂ)
  have hFc : ∀ z ∈ closedBall z₀ (r / 2), Continuous (F z) := fun z hz =>
    hderc.smul (hΦc.comp_continuous (hpath z) (hmemW z hz))
  have hF'c : Continuous (F' z₀) :=
    hderc.smul ((hD.comp_continuous (hpath z₀) (hmemW z₀ (mem_closedBall_self hr2.le))).clm_comp
      continuous_const)
  have key := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := MeasureTheory.volume)
    (a := 0) (b := 2 * Real.pi) (F := F) (F' := F') (x₀ := z₀)
    (bound := fun _ => r * (B * ‖ContinuousLinearMap.inl ℂ (Fin n → ℂ) ℂ‖)) (ball_mem_nhds z₀ hr2)
    (eventually_of_mem (ball_mem_nhds z₀ hr2) fun z hz =>
      (hFc z (ball_subset_closedBall hz)).aestronglyMeasurable)
    ((hFc z₀ (mem_closedBall_self hr2.le)).intervalIntegrable _ _)
    hF'c.aestronglyMeasurable
    (MeasureTheory.ae_of_all _ fun θ _ z hz => by
      simp only [F', norm_smul]
      rw [deriv_circleMap, norm_mul, Complex.norm_I, mul_one, norm_circleMap_zero, abs_of_pos hr]
      exact mul_le_mul_of_nonneg_left ((ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (hB _ ⟨ball_subset_closedBall hz, hcirc θ⟩) (norm_nonneg _))) hr.le)
    intervalIntegrable_const
    (MeasureTheory.ae_of_all _ fun θ _ z hz => by
      have hd : DifferentiableAt ℂ Φ (z, circleMap 0 r θ) :=
        (hΦa _ (hmemW z (ball_subset_closedBall hz) θ)).differentiableAt
      exact (hd.hasFDerivAt.comp z (hasFDerivAt_prodMk_left (𝕜 := ℂ) z (circleMap 0 r θ))).const_smul
        (deriv (circleMap 0 r) θ))
  exact key.differentiableAt

end GlobalTheory
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableAtCoordinateCauchyIntegralStatement

section

@[expose] public section

open Metric Filter Topology Set

theorem _root_.GlobalTheory.T.differentiableAt_coordinate_cauchy_integral : ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (k : Fin n) (f : (Fin n → ℂ) → ℂ) (z₀ : Fin n → ℂ) (r : ℝ), 0 < r → z₀ k = 0 → IsOpen U → Metric.closedBall z₀ r ⊆ U → DifferentiableOn ℂ f {z | z ∈ U ∧ z k ≠ 0} → DifferentiableAt ℂ (fun z => ∮ t in C(0, r), (t - z k)⁻¹ • f (Function.update z k t)) z₀ := by
  first | exact @GlobalTheory.cauchyCoord_differentiableAt | exact GlobalTheory.cauchyCoord_differentiableAt | (intros; apply GlobalTheory.cauchyCoord_differentiableAt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannExtensionCoordinateHyperplane

section

@[expose] public section

open Metric Filter Topology Set

namespace GlobalTheory

theorem riemann_extension_coordinate_hyperplane : ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (k : Fin n) (f : (Fin n → ℂ) → ℂ), IsOpen U → DifferentiableOn ℂ f {z | z ∈ U ∧ z k ≠ 0} → (∀ z₀ ∈ U, ∃ V ∈ nhds z₀, ∃ M : ℝ, ∀ z ∈ V, z ∈ U → z k ≠ 0 → ‖f z‖ ≤ M) → ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F U ∧ ∀ z ∈ U, z k ≠ 0 → F z = f z := by
  intro n U k f hU hd hb
  refine ⟨fun z => if z k = 0 then limUnder (𝓝[≠] (0 : ℂ)) (fun t => f (Function.update z k t)) else f z,
    ?_, fun z _ hz => by simp [hz]⟩
  have hO : IsOpen {z : Fin n → ℂ | z ∈ U ∧ z k ≠ 0} :=
    hU.inter (isOpen_ne_fun (continuous_apply k) continuous_const)
  intro z₀ hz₀
  refine DifferentiableAt.differentiableWithinAt ?_
  by_cases h0 : z₀ k = 0
  · obtain ⟨V, hV, M, hM⟩ := hb z₀ hz₀
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem (hU.mem_nhds hz₀) hV)
    have hr : 0 < ε / 3 := by positivity
    have h2 : ball z₀ (2 * (ε / 3)) ⊆ U ∩ V := (ball_subset_ball (by linarith)).trans hball
    have hG := ((GlobalTheory.T.differentiableAt_coordinate_cauchy_integral n U k f z₀ (ε / 3) hr h0 hU
      ((closedBall_subset_ball (by linarith)).trans (hball.trans inter_subset_left)) hd).const_smul
      ((2 * (Real.pi : ℂ) * Complex.I)⁻¹))
    refine hG.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with z hz
    exact (GlobalTheory.T.cauchy_slice_eq_removable_extension n U k f z₀ (ε / 3) M hr h0 hU (h2.trans inter_subset_left) hd
      (fun z hz hzk => hM z (h2 hz).2 (h2 hz).1 hzk) z hz).symm
  · have hf : DifferentiableAt ℂ f z₀ := hd.differentiableAt (hO.mem_nhds ⟨hz₀, h0⟩)
    refine hf.congr_of_eventuallyEq ?_
    filter_upwards [hO.mem_nhds ⟨hz₀, h0⟩] with z hz
    simp [hz.2]
end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannExtensionCoordinateHyperplaneStatement

section

@[expose] public section

open Metric Filter Topology Set

theorem _root_.GlobalTheory.T.exists_differentiableOn_ext_of_bounded_off_hyperplane : ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (k : Fin n) (f : (Fin n → ℂ) → ℂ), IsOpen U → DifferentiableOn ℂ f {z | z ∈ U ∧ z k ≠ 0} → (∀ z₀ ∈ U, ∃ V ∈ nhds z₀, ∃ M : ℝ, ∀ z ∈ V, z ∈ U → z k ≠ 0 → ‖f z‖ ≤ M) → ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F U ∧ ∀ z ∈ U, z k ≠ 0 → F z = f z := by
  first | exact @GlobalTheory.riemann_extension_coordinate_hyperplane | exact GlobalTheory.riemann_extension_coordinate_hyperplane | (intros; apply GlobalTheory.riemann_extension_coordinate_hyperplane <;> assumption)
end
end
