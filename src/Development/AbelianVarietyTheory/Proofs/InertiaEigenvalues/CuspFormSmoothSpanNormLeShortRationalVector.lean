module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysOfMemSmoothSpan
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WordAppendSingle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodSmoothDecayModerateGrowthRightTranslate
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasFDerivAtRealChartRapidKernelOperatorStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LeSmoothOfChartDifferentiableLieDerivStableStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModerateGrowthRapidKernelOperatorStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RapidKernelIntegralConjLieDerivativeMemSpanStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysAtShortRationalVectorsRapidKernelOperator

section

@[expose] public section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise

noncomputable section

namespace GlobalTheory.RapidKernelDecay

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem norm_pInf_apply (x : Ad E) (w : InfinitePlace E) : ‖pInf E x w‖ = ‖x.1 w‖ :=
  (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _


omit [_root_.NumberField.IsTotallyComplex E] in
theorem height_inv (y : GL (Fin a) (Cinf E)) : height y⁻¹ = height y := by
  unfold height; rw [inv_inv]; ring


omit [_root_.NumberField.IsTotallyComplex E] in
theorem pFin_vecMul (x : Fin a → Ad E) (m : GA E a) :
    (fun i => pFin E ((x ᵥ* m.val) i)) = (fun i => pFin E (x i)) ᵥ* m.val.map (pFin E) := by
  funext i

  simp [vecMul, dotProduct, map_sum]

theorem norm_vecMul_infGL_le (y : GL (Fin a) (Cinf E)) (x : Fin a → Ad E) :
    ‖fun i => pInf E ((x ᵥ* (infGL E a y).val) i)‖ ≤ (a * height y) * ‖fun i => pInf E (x i)‖ := by
  have hy : ∀ j i, ‖pInf E ((infGL E a y).val j i)‖ ≤ height y := by
    intro j i
    have e : pInf E ((infGL E a y).val j i) = y.val j i :=
      congrArg (fun u : GL (Fin a) (Cinf E) => u.val j i) (pInf_infGL (E := E) y)
    rw [e]
    have : ‖y.val j i‖ ≤ ‖toL y.val‖ :=
      (norm_le_pi_norm (toL y.val j) i).trans (norm_le_pi_norm (toL y.val) j)
    unfold height; linarith [norm_nonneg (toL (y⁻¹).val)]
  have h1 := one_le_height y
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_

  simp only [vecMul, dotProduct, map_sum, map_mul]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ (height y * ‖fun i => pInf E (x i)‖)
    fun j _ => ?_).trans ?_)
  · rw [mul_comm (height y)]
    exact (norm_mul_le _ _).trans (mul_le_mul (norm_le_pi_norm (fun i => pInf E (x i)) j) (hy j i)
      (norm_nonneg _) (norm_nonneg _))
  · simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact le_of_eq (by ring)

theorem ideleModule_det_infGL_le (z : GL (Fin a) (Cinf E)) :
    (ideleModule E (GeneralLinearGroup.det (infGL E a z)) : ℝ) ≤
      ((a.factorial : ℝ) * height z ^ a) ^ (2 * Fintype.card (InfinitePlace E)) := by
  set u := GeneralLinearGroup.det (infGL E a z) with hu
  have hB : 1 ≤ (a.factorial : ℝ) * height z ^ a :=
    one_le_mul_of_one_le_of_one_le (by exact_mod_cast a.factorial_pos) (one_le_pow₀ (one_le_height z))
  have hinf : pInf E (u : Ad E) = (GeneralLinearGroup.det z : Cinf E) := by
    rw [hu, ← CuspRep.det_map, pInf_infGL]
  have hfin : pFin E (u : Ad E) = 1 := by
    rw [hu, ← CuspRep.det_map, pFin_infGL, map_one, Units.val_one]
  rw [ideleModule_eq]
  have h2 : ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), ‖(u : Ad E).2 v‖ = 1 :=
    finprod_eq_one_of_forall_eq_one fun v => by
      have : (u : Ad E).2 = 1 := hfin
      rw [this]
      exact norm_one
  rw [h2, mul_one, pow_mul, ← Finset.card_univ, ← Finset.prod_const]
  refine Finset.prod_le_prod₀ (fun _ _ => by positivity) fun w _ => ?_
  have h1 : ‖(u : Ad E).1 w‖ ≤ a.factorial * height z ^ a := by
    rw [← norm_pInf_apply, hinf]
    exact (norm_le_pi_norm _ w).trans (norm_det_le _ (by unfold height; linarith [norm_nonneg (toL (z⁻¹).val)]))
  have hm : w.mult ≤ 2 := by unfold InfinitePlace.mult; split_ifs <;> norm_num
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 _).trans (pow_le_pow_right₀ hB hm)

end GlobalTheory.RapidKernelDecay

namespace GlobalTheory.RapidKernelDecay

theorem decays_integral : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (F : GA E a → ℂ)
    (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)),
    GlobalTheory.JSW.IsRapidInf ν k γ → GlobalTheory.ShortVecDecay.Decays F →
      GlobalTheory.ShortVecDecay.Decays (fun g : GA E a => ∫ x, k x * F (g * infGL E a (γ x)) ∂ν) := by
  intro E _ _ _ a F X _ ν _ k γ hk hF L hL C₀ hC₀ N
  obtain ⟨-, -, hkI⟩ := hk
  obtain ⟨C, hC⟩ := hF L hL C₀ hC₀ N
  obtain ⟨M₁, hM₁, h₁⟩ := GlobalTheory.ShortVecDecay.exists_norm_vecMul_le hC₀
  obtain ⟨M₂, hM₂, h₂⟩ := GlobalTheory.ShortVecDecay.exists_norm_vecMul_le hC₀.inv
  set n := a * Module.finrank ℚ E with hn
  set p := 2 * Fintype.card (InfinitePlace E) with hp
  set K₀ : ℝ := (M₂ * a * M₁) ^ n * (a.factorial : ℝ) ^ p with hK₀
  set m := n + a * p with hm
  set I := ∫ x, ‖k x‖ * height (γ x) ^ (m * N) ∂ν with hI
  refine ⟨I * (|C| * K₀ ^ N), fun g c hc ξ hξ hξL => ?_⟩
  set v : Fin a → Ad E := fun j => algebraMap E (Ad E) (ξ j) with hv
  set Xn := ‖fun i => pInf E ((v ᵥ* g.val) i)‖ with hXn
  set G := (ideleModule E (GeneralLinearGroup.det g) : ℝ) with hG
  have hGpos : 0 < G := (ideleModule E _).2
  have key : ∀ y : GL (Fin a) (Cinf E),
      ‖F (g * c * infGL E a y)‖ ≤ |C| * K₀ ^ N * height y ^ (m * N) * (Xn ^ n / G) ^ N := by
    intro y
    have hy1 := one_le_height y
    set g' := g * c * infGL E a y * c⁻¹ with hg'
    have eg : g * c * infGL E a y = g' * c := (inv_mul_cancel_right _ c).symm
    have hfin : (fun i => pFin E ((v ᵥ* g'.val) i)) = (fun i => pFin E ((v ᵥ* g.val) i)) := by
      rw [pFin_vecMul, pFin_vecMul]
      congr 1
      show (GeneralLinearGroup.map (pFin E) g').val = (GeneralLinearGroup.map (pFin E) g).val
      simp [hg', map_mul, map_inv, pFin_infGL]
    have hinf : ‖fun i => pInf E ((v ᵥ* g'.val) i)‖ ≤ M₂ * a * M₁ * height y * Xn := by
      have e : v ᵥ* g'.val = ((v ᵥ* g.val ᵥ* c.val) ᵥ* (infGL E a y).val) ᵥ* (c⁻¹ : GA E a).val := by
        simp only [hg', Units.val_mul, vecMul_vecMul]
      rw [e]
      calc _ ≤ M₂ * ‖fun i => pInf E (((v ᵥ* g.val ᵥ* c.val) ᵥ* (infGL E a y).val) i)‖ :=
            h₂ c⁻¹ (Set.inv_mem_inv.2 hc) _
        _ ≤ M₂ * ((a * height y) * ‖fun i => pInf E ((v ᵥ* g.val ᵥ* c.val) i)‖) :=
            mul_le_mul_of_nonneg_left (norm_vecMul_infGL_le y _) hM₂.le
        _ ≤ M₂ * ((a * height y) * (M₁ * Xn)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (h₁ c hc _) (by positivity)) hM₂.le
        _ = _ := by ring
    set D := (ideleModule E (GeneralLinearGroup.det (infGL E a y)) : ℝ) with hD
    have hDpos : 0 < D := (ideleModule E _).2
    have hdet : (ideleModule E (GeneralLinearGroup.det g') : ℝ) = G * D := by
      have : GeneralLinearGroup.det g' = GeneralLinearGroup.det g * GeneralLinearGroup.det (infGL E a y) := by
        simp only [hg', map_mul, map_inv]
        rw [mul_right_comm (GeneralLinearGroup.det g), mul_inv_cancel_right]
      rw [this, map_mul, Positive.val_mul]
    have hDinv : D⁻¹ ≤ ((a.factorial : ℝ) * height y ^ a) ^ p := by
      have h := ideleModule_det_infGL_le (E := E) y⁻¹
      rw [height_inv] at h
      have hDD : D * (ideleModule E (GeneralLinearGroup.det (infGL E a y⁻¹)) : ℝ) = 1 := by
        rw [hD, ← Positive.val_mul, ← map_mul, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one, map_one]
        rfl
      rw [eq_inv_of_mul_eq_one_right hDD] at h
      exact h
    have hq : (‖fun i => pInf E ((v ᵥ* g'.val) i)‖ ^ n / (ideleModule E (GeneralLinearGroup.det g') : ℝ)) ≤
        K₀ * height y ^ m * (Xn ^ n / G) := by
      rw [hdet]
      have hXn0 : 0 ≤ Xn := norm_nonneg _
      have hb0 : 0 ≤ M₂ * a * M₁ * height y * Xn := by
        have := hM₁.le; have := hM₂.le; positivity
      have hc0 : 0 ≤ ((a.factorial : ℝ) * height y ^ a) ^ p := by positivity
      calc _ = ‖fun i => pInf E ((v ᵥ* g'.val) i)‖ ^ n * D⁻¹ / G := by ring
        _ ≤ (M₂ * a * M₁ * height y * Xn) ^ n * ((a.factorial : ℝ) * height y ^ a) ^ p / G :=
            div_le_div_of_nonneg_right (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hinf n) hDinv
              (inv_nonneg.2 hDpos.le) (pow_nonneg hb0 _)) hGpos.le
        _ = _ := by rw [hK₀, hm, pow_add, pow_mul]; ring
    have hL' : (fun i => pFin E ((v ᵥ* g'.val) i)) ∈ L := hfin ▸ hξL
    have hF' := hC g' c hc ξ hξ hL'
    rw [eg]
    have hnn : 0 ≤ (‖fun i => pInf E ((v ᵥ* g'.val) i)‖ ^ n / (ideleModule E (GeneralLinearGroup.det g') : ℝ)) ^ N :=
      pow_nonneg (div_nonneg (pow_nonneg (norm_nonneg _) _) (ideleModule E _).2.le) _
    calc ‖F (g' * c)‖ ≤ |C| * (‖fun i => pInf E ((v ᵥ* g'.val) i)‖ ^ n /
          (ideleModule E (GeneralLinearGroup.det g') : ℝ)) ^ N :=
          hF'.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hnn)
      _ ≤ |C| * (K₀ * height y ^ m * (Xn ^ n / G)) ^ N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (div_nonneg (pow_nonneg (norm_nonneg _) _)
            (ideleModule E _).2.le) hq N) (abs_nonneg C)
      _ = _ := by ring
  have hint : Integrable (fun x => ‖k x‖ * height (γ x) ^ (m * N)) ν := hkI (m * N)
  show ‖∫ x, k x * F (g * c * infGL E a (γ x)) ∂ν‖ ≤ I * (|C| * K₀ ^ N) * (Xn ^ n / G) ^ N
  calc ‖∫ x, k x * F (g * c * infGL E a (γ x)) ∂ν‖
      ≤ ∫ x, ‖k x‖ * height (γ x) ^ (m * N) * (|C| * K₀ ^ N * (Xn ^ n / G) ^ N) ∂ν :=
        norm_integral_le_of_norm_le (hint.mul_const _) (.of_forall fun x => by
          rw [norm_mul]
          calc ‖k x‖ * ‖F (g * c * infGL E a (γ x))‖
              ≤ ‖k x‖ * (|C| * K₀ ^ N * height (γ x) ^ (m * N) * (Xn ^ n / G) ^ N) :=
                mul_le_mul_of_nonneg_left (key _) (norm_nonneg _)
            _ = _ := by ring)
    _ = _ := by rw [integral_mul_const, hI]; ring

end GlobalTheory.RapidKernelDecay
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysAtShortRationalVectorsRapidKernelOperatorStatement

section

@[expose] public section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise

theorem _root_.GlobalTheory.T.decaysAtShortRationalVectors_rapidKernelOperator : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (F : GA E a → ℂ) (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), GlobalTheory.JSW.IsRapidInf ν k γ → GlobalTheory.ShortVecDecay.Decays F → GlobalTheory.ShortVecDecay.Decays (fun g : GA E a => ∫ x, k x * F (g * infGL E a (γ x)) ∂ν) := by
  first | exact @GlobalTheory.RapidKernelDecay.decays_integral | exact GlobalTheory.RapidKernelDecay.decays_integral | (intros; apply GlobalTheory.RapidKernelDecay.decays_integral <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodSmoothDecayModerateGrowthRightTranslateStatement

section

@[expose] public section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise

theorem _root_.GlobalTheory.T.goodSmoothDecayModerateGrowth_rightTranslate : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (F : GA E a → ℂ) (h : GA E a), GlobalTheory.MSpanDecay.Good F → GlobalTheory.MSpanDecay.Good (fun g => F (g * h)) := by
  first | exact @GlobalTheory.RtGood.good_mul_right | exact GlobalTheory.RtGood.good_mul_right | (intros; apply GlobalTheory.RtGood.good_mul_right <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormSmoothSpanNormLeShortRationalVector

section

@[expose] public section

noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise

namespace GlobalTheory.MSpanDecay

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem chart_add (F G : GA E a → ℂ) (g : GA E a) : chart (F + G) g = chart F g + chart G g := by
  funext x; by_cases h : IsUnit (Matrix.of x) <;> simp [chart, h]

theorem chart_smul (z : ℂ) (F : GA E a → ℂ) (g : GA E a) : chart (z • F) g = z • chart F g := by
  funext x; by_cases h : IsUnit (Matrix.of x) <;> simp [chart, h]

theorem chart_zero (g : GA E a) : chart (0 : GA E a → ℂ) g = 0 := by
  funext x; by_cases h : IsUnit (Matrix.of x) <;> simp [chart, h]

theorem kSpan_diff : ∀ F ∈ kSpan E a, ∀ g : GA E a, DifferentiableOn ℝ (chart F g) (invSet E a) := by
  intro F hF
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨X, _, ν, _, k, γ, G, hk, hG, rfl⟩ := hF
    intro g x hx
    obtain ⟨u, hu⟩ := id hx
    have e : x = toL u.val := hu.symm
    subst e
    obtain ⟨L, hL, -⟩ := GlobalTheory.T.hasFDerivAt_realChart_rapidKernelOperator E a G X ν k γ hk hG g u
    exact hL.differentiableAt.differentiableWithinAt
  | zero => intro g; rw [chart_zero]; exact differentiableOn_const 0
  | add F G _ _ hF hG => intro g; rw [chart_add]; exact (hF g).add (hG g)
  | smul z F _ hF => intro g; rw [chart_smul]; exact (hF g).const_smul z

theorem differentiableAt_one_of_mem {F : GA E a → ℂ} (hF : F ∈ kSpan E a) (g : GA E a) :
    DifferentiableAt ℝ (chart F g) (oneL E a) :=
  (kSpan_diff F hF g).differentiableAt (isOpen_invSet.mem_nhds isUnit_one)

theorem kSpan_lie : ∀ F ∈ kSpan E a, ∀ Y : Lie E a, lieD Y F ∈ kSpan E a := by
  intro F hF Y
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨X, _, ν, _, k, γ, G, hk, hG, rfl⟩ := hF
    have e : lieD Y (fun g : GA E a => ∫ x, k x * G (g * infGL E a (γ x)) ∂ν) = fun g : GA E a =>
        ∫ x, k x * lieD (toL (((γ x)⁻¹).val * Matrix.of Y * (γ x).val)) G (g * infGL E a (γ x)) ∂ν := by
      funext g
      obtain ⟨L, hL, hZ⟩ := GlobalTheory.T.hasFDerivAt_realChart_rapidKernelOperator E a G X ν k γ hk hG g 1
      have e1 : toL (1 : GL (Fin a) (Cinf E)).val = oneL E a := rfl
      rw [lieD, ← e1, hL.fderiv, hZ Y]
      simp
    rw [e]
    exact GlobalTheory.T.rapidKernel_integral_conjLieDerivative_mem_span E a G X ν k γ Y hk hG
  | zero =>
    have e : lieD Y (0 : GA E a → ℂ) = 0 := by
      funext g; simp [lieD, chart_zero]
    rw [e]; exact zero_mem _
  | add F G hF' hG' hF hG =>
    have e : lieD Y (F + G) = lieD Y F + lieD Y G := by
      funext g
      simp only [lieD, chart_add, Pi.add_apply]
      rw [fderiv_add (differentiableAt_one_of_mem hF' g) (differentiableAt_one_of_mem hG' g)]
      rfl
    rw [e]; exact add_mem hF hG
  | smul z F hF' hF =>
    have e : lieD Y (z • F) = z • lieD Y F := by
      funext g
      simp only [lieD, chart_smul, Pi.smul_apply]
      rw [fderiv_const_smul (differentiableAt_one_of_mem hF' g)]
      rfl
    rw [e]; exact Submodule.smul_mem _ z hF

theorem kSpan_le_Sm : kSpan E a ≤ Sm E a := GlobalTheory.T.le_smooth_of_chartDifferentiable_lieDerivStable E a _ kSpan_diff kSpan_lie

theorem kSpan_decays_growth : ∀ F ∈ kSpan E a, GlobalTheory.ShortVecDecay.Decays F ∧ Growth F := by
  intro F hF
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨X, _, ν, _, k, γ, G, hk, hG, rfl⟩ := hF
    exact ⟨GlobalTheory.T.decaysAtShortRationalVectors_rapidKernelOperator E a G X ν k γ hk hG.decays, GlobalTheory.T.moderateGrowth_rapidKernelOperator E a G X ν k γ hk hG.growth⟩
  | zero => exact ⟨GlobalTheory.ShortVecDecay.Decays.zero, Growth.zero⟩
  | add F G _ _ hF hG => exact ⟨hF.1.add hG.1, hF.2.add hG.2⟩
  | smul z F _ hF => exact ⟨hF.1.smul z, hF.2.smul z⟩

theorem word_mem_kSpan (l : List (Lie E a)) (φ : Sm E a) (hφ : φ.1 ∈ kSpan E a) :
    (GlobalTheory.GLFin.word l φ).1 ∈ kSpan E a := by
  induction l with
  | nil => simpa [GlobalTheory.GLFin.word] using hφ
  | cons Y l ih => rw [word_cons]; exact kSpan_lie _ ih Y

theorem Good.kernel {G : GA E a → ℂ} (hG : Good G) {X : Type} [MeasurableSpace X] {ν : Measure X} [SFinite ν]
    {k : X → ℂ} {γ : X → GL (Fin a) (Cinf E)} (hk : GlobalTheory.JSW.IsRapidInf ν k γ) :
    Good (fun g : GA E a => ∫ x, k x * G (g * infGL E a (γ x)) ∂ν) := by
  have hm : (fun g : GA E a => ∫ x, k x * G (g * infGL E a (γ x)) ∂ν) ∈ kSpan E a :=
    Submodule.subset_span ⟨X, inferInstance, ν, inferInstance, k, γ, G, hk, hG, rfl⟩
  exact ⟨kSpan_le_Sm hm, fun l => kSpan_decays_growth _ (word_mem_kSpan l _ hm)⟩


variable (E a) in
def goodSub : Submodule ℂ (GA E a → ℂ) where
  carrier := {F | Good F}
  add_mem' := Good.add
  zero_mem' := good_zero
  smul_mem' c _ h := h.smul c

theorem mspanR_le_goodSub {π : CuspSub E a} (hπ : π.IsUnitary) : GlobalTheory.JSW.mspanR π ≤ goodSub E a :=
  sInf_le ⟨fun φ hφ => good_of_mem hπ hφ, fun F hF h => GlobalTheory.T.goodSmoothDecayModerateGrowth_rightTranslate E a F h hF,
    fun F hF X _ ν _ k γ hk => Good.kernel (G := F) hF hk⟩

theorem norm_le_of_short_vector_mspanR : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (π : CuspSub E a), π.IsUnitary → ∀ φ : Sm E a, (φ ∈ π.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π) → ∀ l : List (Lie E a),
    ∀ L : Set (Fin a → Af E), IsCompact L → ∀ C₀ : Set (GA E a), IsCompact C₀ → ∀ N : ℕ, ∃ C : ℝ,
      ∀ g : GA E a, ∀ c ∈ C₀, ∀ ξ : Fin a → E, ξ ≠ 0 →
        (fun i => pFin E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val) i)) ∈ L →
          ‖(GlobalTheory.GLFin.word l φ).1 (g * c)‖ ≤
            C * (‖fun i => pInf E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val) i)‖ ^ (a * Module.finrank ℚ E) /
              (ideleModule E (GeneralLinearGroup.det g) : ℝ)) ^ N := by
  intro E _ _ _ a π hπ φ hφ l
  have hg : Good φ.1 := hφ.elim (good_of_mem hπ) fun h => mspanR_le_goodSub hπ h
  obtain ⟨h, hl⟩ := hg
  exact (hl l).1

end GlobalTheory.MSpanDecay
end
end
end
