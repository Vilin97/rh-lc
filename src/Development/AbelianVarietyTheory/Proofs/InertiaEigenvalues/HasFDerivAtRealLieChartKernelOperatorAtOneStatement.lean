module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumLieCoord
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
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
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormFderivChartLeOfBoundedLieDerivatives

section

@[expose] public section

noncomputable section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW

namespace GlobalTheory.JSW

theorem norm_toL_mul_le {E : Type} [Field E] [NumberField E] {a : ℕ} (A : Matrix (Fin a) (Fin a) (Cinf E)) (B : Lie E a) :
    ‖toL (A * Matrix.of B)‖ ≤ a * (‖toL A‖ * ‖B‖) := by
  have h0 : 0 ≤ (a : ℝ) * (‖toL A‖ * ‖B‖) := by positivity
  refine (pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun j => ?_
  show ‖(A * Matrix.of B) i j‖ ≤ _
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  have hk : ∀ k, ‖A i k * Matrix.of B k j‖ ≤ ‖toL A‖ * ‖B‖ := fun k => by
    refine (norm_mul_le _ _).trans (mul_le_mul ?_ ?_ (norm_nonneg _) (norm_nonneg _))
    · exact (norm_le_pi_norm (toL A i) k).trans (norm_le_pi_norm (toL A) i)
    · exact (norm_le_pi_norm (B k) j).trans (norm_le_pi_norm B k)
  calc ∑ k, ‖A i k * Matrix.of B k j‖ ≤ ∑ _k : Fin a, ‖toL A‖ * ‖B‖ := Finset.sum_le_sum fun k _ => hk k
    _ = _ := by simp

theorem norm_fderiv_chart_le : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a),
    (∀ i, ∃ C : ℝ, ∀ g, ‖(lie E a (lieBasis E a i) φ).1 g‖ ≤ C) →
      ∃ C : ℝ, ∀ (g : GA E a) (y : GL (Fin a) (Cinf E)), ‖fderiv ℝ (chart φ.1 g) (toL y.val)‖ ≤ C * ‖toL (y⁻¹).val‖ := by
  intro E _ _ _ a φ hC
  choose C hC using hC
  set D : ℝ := ∑ i, max (C i) 0 * ‖lieCoord E a i‖ with hDdef
  have hD : 0 ≤ D := Finset.sum_nonneg fun i _ => mul_nonneg (le_max_right _ _) (norm_nonneg _)
  have hlie : ∀ (X : Lie E a) (h : GA E a), ‖lieD X φ.1 h‖ ≤ D * ‖X‖ := by
    intro X h
    have e : lieD X φ.1 h = ∑ i, ((lieBasis E a).coord i X) • lieD (lieBasis E a i) φ.1 h := by
      conv_lhs => rw [← sum_lieCoord X]

      simp only [lieD, map_sum, map_smul]
    rw [e, hDdef, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul]
    have h1 : ‖(lieBasis E a).coord i X‖ ≤ ‖lieCoord E a i‖ * ‖X‖ := by
      have : ‖lieCoord E a i X‖ = ‖(lieBasis E a).coord i X‖ := by simp [lieCoord]
      rw [← this]; exact (lieCoord E a i).le_opNorm X
    have h2 : ‖lieD (lieBasis E a i) φ.1 h‖ ≤ max (C i) 0 := by
      have := hC i h
      rw [GlobalTheory.CuspRep.lie_apply] at this
      exact this.trans (le_max_left _ _)
    calc ‖(lieBasis E a).coord i X‖ * ‖lieD (lieBasis E a i) φ.1 h‖
        ≤ (‖lieCoord E a i‖ * ‖X‖) * max (C i) 0 := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = _ := by ring
  refine ⟨a * D, fun g y => ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun W => ?_
  set X : Lie E a := toL ((y⁻¹).val * Matrix.of W) with hX
  have e := chart_lieD φ.2 X g (val_mem_invSet y)
  have eW : rmul X (toL y.val) = W := by
    change y.val * ((y⁻¹).val * Matrix.of W) = Matrix.of W
    rw [← mul_assoc, Units.mul_inv, one_mul]
  rw [eW, chart_val] at e
  rw [← e]
  calc ‖lieD X φ.1 (g * infGL E a y)‖ ≤ D * ‖X‖ := hlie _ _
    _ ≤ D * (a * (‖toL (y⁻¹).val‖ * ‖W‖)) := mul_le_mul_of_nonneg_left (norm_toL_mul_le _ _) hD
    _ = a * D * ‖toL (y⁻¹).val‖ * ‖W‖ := by ring

end GlobalTheory.JSW
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormFderivChartLeOfBoundedLieDerivativesStatement

section

@[expose] public section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW

theorem _root_.GlobalTheory.T.norm_fderiv_chart_le_of_bounded_lieDerivatives : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a),
    (∀ i, ∃ C : ℝ, ∀ g, ‖(lie E a (lieBasis E a i) φ).1 g‖ ≤ C) →
      ∃ C : ℝ, ∀ (g : GA E a) (y : GL (Fin a) (Cinf E)), ‖fderiv ℝ (chart φ.1 g) (toL y.val)‖ ≤ C * ‖toL (y⁻¹).val‖ := by
  first | exact @GlobalTheory.JSW.norm_fderiv_chart_le | exact GlobalTheory.JSW.norm_fderiv_chart_le | (intros; apply GlobalTheory.JSW.norm_fderiv_chart_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasFDerivAtRealLieChartKernelOperatorAtOne

section

@[expose] public section

noncomputable section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW Topology

namespace GlobalTheory.JSW.KerDeriv

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


omit [_root_.NumberField.IsTotallyComplex E] in
def rmulL : Lie E a →L[ℝ] Lie E a →L[ℝ] Lie E a :=
  LinearMap.toContinuousLinearMap
    { toFun := rmul
      map_add' := fun y z => ContinuousLinearMap.ext fun x => Matrix.mul_add (Matrix.of x) (Matrix.of y) (Matrix.of z)
      map_smul' := fun c y => ContinuousLinearMap.ext fun x => Matrix.mul_smul (Matrix.of x) c (Matrix.of y) }

omit [_root_.NumberField.IsTotallyComplex E] in
theorem norm_rmul_le (y : Lie E a) : ‖rmul y‖ ≤ ‖(rmulL : Lie E a →L[ℝ] Lie E a →L[ℝ] Lie E a)‖ * ‖y‖ :=
  (rmulL (E := E) (a := a)).le_opNorm y

omit [_root_.NumberField.IsTotallyComplex E] in
theorem norm_mul_le (x y : Lie E a) :
    ‖toL (Matrix.of x * Matrix.of y)‖ ≤ ‖(rmulL : Lie E a →L[ℝ] Lie E a →L[ℝ] Lie E a)‖ * ‖y‖ * ‖x‖ :=
  (rmulL (E := E) (a := a)).le_opNorm₂ y x


omit [_root_.NumberField.IsTotallyComplex E] in
theorem eventually_inv_bdd :
    ∀ᶠ Y in 𝓝 (oneL E a), Y ∈ invSet E a ∧ ‖toL (Matrix.of Y)⁻¹‖ < ‖oneL E a‖ + 1 := by
  have hc : ContinuousAt (fun Y : Lie E a => toL (Matrix.of Y)⁻¹) (oneL E a) := by
    have h := continuousAt_matrix_inv (1 : Matrix (Fin a) (Fin a) (Cinf E)) (by
      rw [Matrix.det_one]
      exact NormedRing.inverse_continuousAt (1 : (Cinf E)ˣ))
    exact h
  have h1 : toL (Matrix.of (oneL E a))⁻¹ = oneL E a := by simp
  have h0 : ‖toL (Matrix.of (oneL E a))⁻¹‖ < ‖oneL E a‖ + 1 := by rw [h1]; exact lt_add_one _
  have h2 := hc.norm.eventually (gt_mem_nhds h0)
  exact Filter.Eventually.and (isOpen_invSet.mem_nhds (isUnit_one : oneL E a ∈ invSet E a)) h2

theorem norm_chart_le (φ : GA E a → ℂ) (g : GA E a) {C : ℝ} (hC : ∀ g, ‖φ g‖ ≤ C) (Y : Lie E a) :
    ‖chart φ g Y‖ ≤ max C 0 := by
  unfold chart
  split_ifs
  · exact le_max_of_le_left (hC _)
  · simp

theorem measurable_chart {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) (g : GA E a) : Measurable (chart φ g) := by
  classical
  have h := ContinuousOn.measurable_piecewise (hφ g).continuousOn (continuousOn_const (c := (0 : ℂ)))
    isOpen_invSet.measurableSet
  convert h using 1
  funext Y
  by_cases hY : Y ∈ invSet E a
  · rw [Set.piecewise_eq_of_mem _ _ _ hY]
  · rw [Set.piecewise_eq_of_notMem _ _ _ hY]
    have hY' : ¬ IsUnit (Matrix.of Y) := hY
    simp [chart, hY']

theorem hasFDerivAt_chart_kerOp_of_bound {X : Type} [MeasurableSpace X] (ν : Measure X)
    (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)) (hk : IsRapidInf ν k γ) (φ : Sm E a) (hφ : ∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C)
    (hD : ∃ C : ℝ, ∀ (g : GA E a) (y : GL (Fin a) (Cinf E)), ‖fderiv ℝ (chart φ.1 g) (toL y.val)‖ ≤ C * ‖toL (y⁻¹).val‖)
    (g : GA E a) :
    HasFDerivAt (chart (kerOp ν k γ φ.1) g)
      (∫ x, k x • (fderiv ℝ (chart φ.1 g) (toL (γ x).val)).comp (rmul (toL (γ x).val)) ∂ν) (oneL E a) := by
  obtain ⟨hkm, hγm, hint⟩ := hk
  obtain ⟨Cφ, hCφ⟩ := hφ
  obtain ⟨CD, hCD⟩ := hD
  set M := ‖(rmulL : Lie E a →L[ℝ] Lie E a →L[ℝ] Lie E a)‖ with hM
  set B := ‖oneL E a‖ + 1 with hB
  have hM0 : 0 ≤ M := norm_nonneg _
  have hB0 : 0 ≤ B := by positivity
  set s : Set (Lie E a) := {Y | Y ∈ invSet E a ∧ ‖toL (Matrix.of Y)⁻¹‖ < B} with hs_def
  have hs : s ∈ 𝓝 (oneL E a) := eventually_inv_bdd
  set F : Lie E a → X → ℂ := fun Y x => k x * chart φ.1 g (rmul (toL (γ x).val) Y) with hF
  set F' : Lie E a → X → (Lie E a →L[ℝ] ℂ) := fun Y x =>
    k x • (fderiv ℝ (chart φ.1 g) (rmul (toL (γ x).val) Y)).comp (rmul (toL (γ x).val)) with hF'
  have hγL : Measurable fun x => toL (γ x).val := hγm
  have heq : chart (kerOp ν k γ φ.1) g =ᶠ[𝓝 (oneL E a)] fun Y => ∫ x, F Y x ∂ν := by
    filter_upwards [isOpen_invSet.mem_nhds (isUnit_one : oneL E a ∈ invSet E a)] with Y hY
    obtain ⟨u, hu⟩ := hY
    have hY' : Y = toL u.val := hu.symm
    subst hY'
    rw [chart_val]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    change k x * φ.1 (g * infGL E a u * infGL E a (γ x)) = k x * chart φ.1 g (rmul (toL (γ x).val) (toL u.val))
    rw [mul_assoc, ← map_mul, ← chart_val φ.1 g (u * γ x)]
    rfl
  have e1 : ∀ x, rmul (toL (γ x).val) (oneL E a) = toL (γ x).val := fun x => one_mul (γ x).val
  have hF'1 : F' (oneL E a) =
      fun x => k x • (fderiv ℝ (chart φ.1 g) (toL (γ x).val)).comp (rmul (toL (γ x).val)) := by
    funext x; simp only [hF', e1]
  refine HasFDerivAt.congr_of_eventuallyEq ?_ heq
  rw [← hF'1]

  have hmeasF : ∀ Y, AEStronglyMeasurable (F Y) ν := fun Y => by
    refine (hkm.aestronglyMeasurable).mul ?_
    refine ((measurable_chart φ.2 g).comp ?_).aestronglyMeasurable
    exact ((rmulL (E := E) (a := a)).flip Y).continuous.measurable.comp hγL
  have hmeasF' : AEStronglyMeasurable (F' (oneL E a)) ν := by
    rw [hF'1]
    refine hkm.aestronglyMeasurable.smul ?_
    exact (ContinuousLinearMap.compL ℝ (Lie E a) (Lie E a) ℂ).aestronglyMeasurable_comp₂
      ((measurable_fderiv ℝ (chart φ.1 g)).comp hγL).aestronglyMeasurable
      ((rmulL (E := E) (a := a)).continuous.measurable.comp hγL).aestronglyMeasurable

  have hint0 : Integrable (F (oneL E a)) ν := by
    refine Integrable.mono' ((hint 0).mul_const (max Cφ 0)) (hmeasF _) (ae_of_all _ fun x => ?_)
    simp only [hF, norm_mul, pow_zero, mul_one]
    exact mul_le_mul_of_nonneg_left (norm_chart_le φ.1 g hCφ _) (norm_nonneg _)

  set K := max CD 0 * M * B * M with hK
  have hbound : ∀ᵐ x ∂ν, ∀ Y ∈ s, ‖F' Y x‖ ≤ ‖k x‖ * height (γ x) ^ 2 * K := by
    refine ae_of_all _ fun x Y hY => ?_
    have hu : IsUnit (Matrix.of Y) := hY.1
    set y := hu.unit * γ x with hy
    have hyv : rmul (toL (γ x).val) Y = toL y.val := by
      rw [hy, Units.val_mul, IsUnit.unit_spec]; rfl
    have hyi : toL (y⁻¹).val = toL (Matrix.of (toL (γ x)⁻¹.val) * Matrix.of (toL (hu.unit⁻¹).val)) := by
      rw [hy, _root_.mul_inv_rev, Units.val_mul]; rfl
    have hui : ‖toL (hu.unit⁻¹).val‖ ≤ B := by
      rw [Matrix.coe_units_inv, IsUnit.unit_spec]; exact hY.2.le
    have hg1 : ‖toL (γ x).val‖ ≤ height (γ x) := by
      unfold height; linarith [norm_nonneg (toL (γ x)⁻¹.val)]
    have hg2 : ‖toL (γ x)⁻¹.val‖ ≤ height (γ x) := by
      unfold height; linarith [norm_nonneg (toL (γ x).val)]
    have hL : ‖fderiv ℝ (chart φ.1 g) (rmul (toL (γ x).val) Y)‖ ≤ max CD 0 * (M * B * height (γ x)) := by
      rw [hyv]
      refine (hCD g y).trans ?_
      have h1 : ‖toL (y⁻¹).val‖ ≤ M * B * height (γ x) := by
        rw [hyi]
        refine (norm_mul_le _ _).trans ?_
        gcongr
      calc CD * ‖toL (y⁻¹).val‖ ≤ max CD 0 * ‖toL (y⁻¹).val‖ := by gcongr; exact le_max_left _ _
        _ ≤ _ := by gcongr
    have hR : ‖rmul (toL (γ x).val)‖ ≤ M * height (γ x) := (norm_rmul_le _).trans (mul_le_mul_of_nonneg_left hg1 hM0)
    calc ‖F' Y x‖ ≤ ‖k x‖ * (‖fderiv ℝ (chart φ.1 g) (rmul (toL (γ x).val) Y)‖ * ‖rmul (toL (γ x).val)‖) := by
          simp only [hF', norm_smul]
          gcongr
          exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖k x‖ * ((max CD 0 * (M * B * height (γ x))) * (M * height (γ x))) := by
          have hh0 : 0 ≤ height (γ x) := (norm_nonneg _).trans hg1
          gcongr
      _ = ‖k x‖ * height (γ x) ^ 2 * K := by rw [hK]; ring
  have hdiff : ∀ᵐ x ∂ν, ∀ Y ∈ s, HasFDerivAt (F · x) (F' Y x) Y := by
    refine ae_of_all _ fun x Y hY => ?_
    have hmem : rmul (toL (γ x).val) Y ∈ invSet E a := IsUnit.mul hY.1 (γ x).isUnit
    have h1 : HasFDerivAt (chart φ.1 g) (fderiv ℝ (chart φ.1 g) (rmul (toL (γ x).val) Y))
        (rmul (toL (γ x).val) Y) :=
      ((contDiffAt_chart φ.2 g hmem).differentiableAt (by simp)).hasFDerivAt
    exact (h1.comp Y (rmul (toL (γ x).val)).hasFDerivAt).const_mul (k x)
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le hs (Filter.Eventually.of_forall hmeasF) hint0 hmeasF'
    hbound ((hint 2).mul_const K) hdiff

end GlobalTheory.JSW.KerDeriv

namespace GlobalTheory.JSW

theorem hasFDerivAt_chart_kerOp : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (X : Type)
    [MeasurableSpace X] (ν : Measure X)
    (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ → ∀ φ : Sm E a, (∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C) →
    (∀ i, ∃ C : ℝ, ∀ g, ‖(lie E a (lieBasis E a i) φ).1 g‖ ≤ C) → ∀ g,
      HasFDerivAt (chart (kerOp ν k γ φ.1) g)
        (∫ x, k x • (fderiv ℝ (chart φ.1 g) (toL (γ x).val)).comp (rmul (toL (γ x).val)) ∂ν) (oneL E a) :=
  fun E _ _ _ a _ _ ν k γ hk φ hφ hL g =>
    KerDeriv.hasFDerivAt_chart_kerOp_of_bound ν k γ hk φ hφ (GlobalTheory.T.norm_fderiv_chart_le_of_bounded_lieDerivatives E a φ hL) g

end GlobalTheory.JSW
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasFDerivAtRealLieChartKernelOperatorAtOneStatement

section

@[expose] public section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW

theorem _root_.GlobalTheory.T.hasFDerivAt_realLieChart_kernelOperator_at_one : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (X : Type) [MeasurableSpace X] (ν : Measure X)
    (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ → ∀ φ : Sm E a, (∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C) →
    (∀ i, ∃ C : ℝ, ∀ g, ‖(lie E a (lieBasis E a i) φ).1 g‖ ≤ C) → ∀ g,
      HasFDerivAt (chart (kerOp ν k γ φ.1) g)
        (∫ x, k x • (fderiv ℝ (chart φ.1 g) (toL (γ x).val)).comp (rmul (toL (γ x).val)) ∂ν) (oneL E a) := by
  first | exact @GlobalTheory.JSW.hasFDerivAt_chart_kerOp | exact GlobalTheory.JSW.hasFDerivAt_chart_kerOp | (intros; apply GlobalTheory.JSW.hasFDerivAt_chart_kerOp <;> assumption)
end
end
