module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowForm
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianConvolutionSeriesCoefficientDescFactoriaStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianIteratedFDerivWeightedExpBoundedStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
public import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
public import Mathlib.Analysis.InnerProductSpace.Calculus

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormGaussianConvolutionSeriesCoefficientLeIntegr

section

@[expose] public section

open MeasureTheory Filter Topology

namespace GlobalTheory.ConvSeries

namespace CoefNorm

theorem norm_innerC_apply_le {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (a y : E) :
    ‖innerC a y‖ ≤ ‖a‖ * ‖y‖ := by
  simp only [innerC, ContinuousLinearMap.comp_apply, innerSL_apply_apply, Complex.ofRealCLM_apply,
    Complex.norm_real, Real.norm_eq_abs]
  exact abs_real_inner_le_norm a y

theorem norm_powForm_le {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (k : ℕ) (a : E) :
    ‖powForm k a‖ ≤ ‖a‖ ^ k := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m => ?_
  simp only [powForm, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply]
  rw [norm_prod]
  calc ∏ i, ‖innerC a (m i)‖ ≤ ∏ i, (‖a‖ * ‖m i‖) :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => norm_innerC_apply_le a (m i)
    _ = ‖a‖ ^ k * ∏ i, ‖m i‖ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem norm_wt_le {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (b c : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : E → ℂ) (a : E) : ‖wt b c h a‖ ≤ ‖h a‖ := by
  unfold wt
  rw [norm_mul, norm_mul, ← Complex.ofReal_neg, ← Complex.ofReal_neg, Complex.norm_exp_ofReal,
    Complex.norm_exp_ofReal]
  have e1 : Real.exp (-(b * ‖a‖ ^ 2)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖a‖])
  have e2 : Real.exp (-(c * ‖a‖ ^ 2)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖a‖])
  calc _ ≤ 1 * ‖h a‖ * 1 := by gcongr
    _ = _ := by ring

theorem continuous_wt {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (b c : ℝ) (h : E → ℂ)
    (hh : Continuous h) : Continuous (wt b c h) := by
  unfold wt
  fun_prop

end CoefNorm


open CoefNorm in
theorem norm_coef_le_integral (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (b c : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) (h : SchwartzMap E ℂ) (j : ℕ) :
    ‖coef b c (⇑h) j‖ ≤ ∫ a, ‖wt b c (⇑h) a‖ * ‖a‖ ^ j := by
  unfold coef
  refine (norm_integral_le_integral_norm _).trans ?_
  have hw : Continuous (wt b c (⇑h)) := continuous_wt b c _ h.continuous
  have hint : Integrable (fun a : E => ‖a‖ ^ j * ‖h a‖) := h.integrable_pow_mul volume j
  have hint2 : Integrable (fun a : E => ‖wt b c (⇑h) a‖ * ‖a‖ ^ j) := by
    refine hint.mono' ((hw.norm.mul (continuous_norm.pow j)).aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun a => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_comm]
    exact mul_le_mul_of_nonneg_left (norm_wt_le b c hb hc _ a) (by positivity)
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun a => norm_nonneg _) hint2
    (Filter.Eventually.of_forall fun a => ?_)
  simp only [norm_smul]
  exact mul_le_mul_of_nonneg_left (norm_powForm_le j a) (norm_nonneg _)

end GlobalTheory.ConvSeries
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormGaussianConvolutionSeriesCoefficientLeIntegrStatement

section

@[expose] public section

open MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.norm_gaussianConvolutionSeriesCoefficient_le_integral : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (b c : ℝ), 0 ≤ b → 0 ≤ c → ∀ (h : SchwartzMap E ℂ) (j : ℕ),
    ‖GlobalTheory.ConvSeries.coef b c (⇑h) j‖ ≤ ∫ a, ‖GlobalTheory.ConvSeries.wt b c (⇑h) a‖ * ‖a‖ ^ j := by
  first | exact @GlobalTheory.ConvSeries.norm_coef_le_integral | exact GlobalTheory.ConvSeries.norm_coef_le_integral | (intros; apply GlobalTheory.ConvSeries.norm_coef_le_integral <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIteratedFDerivMultilinearDiagonalLe

section

@[expose] public section

open MeasureTheory Filter Topology

namespace GlobalTheory

theorem norm_iteratedFDeriv_diag_multilinear_le (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (j : ℕ)
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℂ) (i : ℕ) (y : E) :
    ‖iteratedFDeriv ℝ i (fun y : E => f (fun _ => y)) y‖ ≤ (j.descFactorial i : ℝ) * ‖f‖ * ‖y‖ ^ (j - i) := by
  set L : E →L[ℝ] (Fin j → E) := ContinuousLinearMap.pi (fun _ => ContinuousLinearMap.id ℝ E) with hL
  have hLn : ‖L‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => ?_)
    rw [one_mul]
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 (fun _ => ?_)
    simp [hL]
  have hfun : (fun y : E => f (fun _ => y)) = (f : (Fin j → E) → ℂ) ∘ L := by
    funext z; simp [hL]
  have hf : ContDiff ℝ ⊤ (f : (Fin j → E) → ℂ) := f.contDiff
  rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_right L hf y (by exact_mod_cast le_top)]
  have hLy : ‖L y‖ ≤ ‖y‖ := by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg y)).2 (fun _ => ?_)
    simp [hL]
  calc ‖(iteratedFDeriv ℝ i (⇑f) (L y)).compContinuousLinearMap (fun _ => L)‖
      ≤ ‖iteratedFDeriv ℝ i (⇑f) (L y)‖ * ∏ _ : Fin i, ‖L‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ i (⇑f) (L y)‖ * 1 := by
        gcongr
        exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => hLn)
    _ = ‖iteratedFDeriv ℝ i (⇑f) (L y)‖ := mul_one _
    _ ≤ (Fintype.card (Fin j)).descFactorial i * ‖f‖ * ‖L y‖ ^ (Fintype.card (Fin j) - i) :=
        f.norm_iteratedFDeriv_le i (L y)
    _ ≤ (j.descFactorial i : ℝ) * ‖f‖ * ‖y‖ ^ (j - i) := by
        rw [Fintype.card_fin]
        gcongr

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIteratedFDerivMultilinearDiagonalLeStatement

section

@[expose] public section

open MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.norm_iteratedFDeriv_multilinear_diagonal_le : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (j : ℕ)
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℂ) (i : ℕ) (y : E),
    ‖iteratedFDeriv ℝ i (fun y : E => f (fun _ => y)) y‖ ≤ (j.descFactorial i : ℝ) * ‖f‖ * ‖y‖ ^ (j - i) := by
  first | exact @GlobalTheory.norm_iteratedFDeriv_diag_multilinear_le | exact GlobalTheory.norm_iteratedFDeriv_diag_multilinear_le | (intros; apply GlobalTheory.norm_iteratedFDeriv_diag_multilinear_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableSeminormGaussianConvolutionSeriesTerm

section

@[expose] public section

open MeasureTheory Filter Topology

namespace GlobalTheory.ConvSeries

theorem summable_seminorm_term : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (b c : ℝ), 0 < b → 0 < c → ∀ (h : SchwartzMap E ℂ)
    (t : ℕ → SchwartzMap E ℂ), (∀ j y, t j y = GlobalTheory.ConvSeries.term b c h j y) →
    ∀ (k n : ℕ), Summable (fun j => SchwartzMap.seminorm ℂ k n (t j)) := by
  intro E _ _ _ _ _ b c hb hc h t ht k n

  set δ : ℝ := min 1 (b / (6 * c)) with hδ
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : δ ≤ b / (6 * c) := min_le_right _ _
  set θ : ℝ := 1 + δ with hθ
  set α : ℝ := (2 * c + b) / (2 * (b + c)) with hα
  have hθ1 : 1 ≤ θ := by linarith
  have hθpos : 0 < θ := by linarith
  have hα0 : 0 < α := by positivity
  have hα1 : α < 1 := by rw [hα, div_lt_one (by positivity)]; linarith
  have hθα : c * θ ^ 2 ≤ α * (b + c) := by
    have e1 : α * (b + c) = c + b / 2 := by rw [hα]; field_simp
    have e2 : δ * (6 * c) ≤ b := by rwa [le_div_iff₀ (by positivity)] at hδ2
    rw [e1, hθ]; nlinarith

  choose K hK using fun m => GlobalTheory.T.gaussian_iteratedFDeriv_weighted_exp_bounded E c α hc hα1 k m
  set M : ℕ → ℝ := fun i => ∫ a, (2 * c * ‖a‖) ^ i * ‖h a‖ with hM
  have hM0 : ∀ i, 0 ≤ M i := fun i => integral_nonneg fun a => by positivity
  set B : ℝ := θ ^ n * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * M (n - i) * K i with hB
  have hK0 : ∀ m, 0 ≤ K m := fun m => le_trans (by positivity) (hK m 0)
  have hB0 : 0 ≤ B := by
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => ?_)
    exact mul_nonneg (mul_nonneg (by positivity) (hM0 _)) (hK0 _)
  have hbound : ∀ j, SchwartzMap.seminorm ℂ k n (t j) ≤ θ⁻¹ ^ j * B := by
    intro j
    refine SchwartzMap.seminorm_le_bound ℂ k n (t j) (by positivity) fun y => ?_
    set s : ℝ := (2 * c) ^ j / (j.factorial : ℝ) with hs
    have hs0 : 0 ≤ s := by positivity
    set f : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℂ :=
      ((s : ℝ) : ℂ) • GlobalTheory.ConvSeries.coef b c (⇑h) j with hf
    have hfun : (⇑(t j)) = fun y => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)) * f (fun _ => y) := by
      funext y
      rw [ht, GlobalTheory.ConvSeries.term, hf, ContinuousMultilinearMap.smul_apply, smul_eq_mul, mul_assoc]
    have hG : ContDiff ℝ (⊤ : ℕ∞) (fun y : E => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) := by
      refine Complex.contDiff_exp.comp ?_
      refine ContDiff.neg ?_
      exact Complex.ofRealCLM.contDiff.comp (contDiff_const.mul (contDiff_norm_sq ℝ))
    have hP : ContDiff ℝ (⊤ : ℕ∞) (fun y : E => f (fun _ => y)) :=
      f.contDiff.comp (contDiff_pi.2 fun _ => contDiff_id)
    have hL := norm_iteratedFDeriv_mul_le hG hP y (n := n) (by exact_mod_cast le_top)
    rw [hfun]
    have hfn : ‖f‖ ≤ s * ∫ a, ‖GlobalTheory.ConvSeries.wt b c (⇑h) a‖ * ‖a‖ ^ j := by
      rw [hf, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]
      exact mul_le_mul_of_nonneg_left (GlobalTheory.T.norm_gaussianConvolutionSeriesCoefficient_le_integral E b c hb.le hc.le h j) hs0
    have hterm : ∀ i ∈ Finset.range (n + 1),
        ‖y‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y : E => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) y‖ *
          ‖iteratedFDeriv ℝ (n - i) (fun y : E => f (fun _ => y)) y‖) ≤
        θ⁻¹ ^ j * (θ ^ n * ((n.choose i : ℝ) * M (n - i) * K i)) := by
      intro i hi
      have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      set m := n - i
      have h1 := GlobalTheory.T.norm_iteratedFDeriv_multilinear_diagonal_le E j f m y
      have h3 := GlobalTheory.T.gaussianConvolutionSeriesCoefficient_descFactorial_estimate E b c θ α hc hθ1 hα0 hθα h j m y
      have hPm : ‖iteratedFDeriv ℝ m (fun y : E => f (fun _ => y)) y‖ ≤
          θ⁻¹ ^ (j - m) * Real.exp (c * α * ‖y‖ ^ 2) * M m := by
        refine h1.trans (le_trans ?_ h3)
        have := mul_le_mul_of_nonneg_left hfn (by positivity : (0:ℝ) ≤ (j.descFactorial m : ℝ))
        calc (j.descFactorial m : ℝ) * ‖f‖ * ‖y‖ ^ (j - m)
            ≤ (j.descFactorial m : ℝ) * (s * ∫ a, ‖GlobalTheory.ConvSeries.wt b c (⇑h) a‖ * ‖a‖ ^ j) * ‖y‖ ^ (j - m) := by
              gcongr
          _ = _ := by rw [hs]; ring
      have hθj : θ⁻¹ ^ (j - m) ≤ θ⁻¹ ^ j * θ ^ n := by
        have hinv : 0 < θ⁻¹ := inv_pos.2 hθpos
        have hle : θ⁻¹ ^ (j - m + m) ≤ θ⁻¹ ^ j :=
          pow_le_pow_of_le_one hinv.le (inv_le_one_of_one_le₀ hθ1) (by omega)
        have e : θ⁻¹ ^ (j - m) = θ⁻¹ ^ (j - m + m) * θ ^ m := by
          rw [pow_add, mul_assoc, ← mul_pow, inv_mul_cancel₀ hθpos.ne', one_pow, mul_one]
        rw [e]
        exact mul_le_mul hle (pow_le_pow_right₀ hθ1 (by omega)) (by positivity) (by positivity)
      have hGk := hK i y
      have hch : (0:ℝ) ≤ n.choose i := by positivity
      calc ‖y‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y : E => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) y‖ *
            ‖iteratedFDeriv ℝ m (fun y : E => f (fun _ => y)) y‖)
          ≤ ‖y‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y : E => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) y‖ *
            (θ⁻¹ ^ j * θ ^ n * Real.exp (c * α * ‖y‖ ^ 2) * M m)) := by
            gcongr
            exact hPm.trans (by gcongr)
        _ = θ⁻¹ ^ j * (θ ^ n * ((n.choose i : ℝ) * M m *
            (‖y‖ ^ k * ‖iteratedFDeriv ℝ i (fun y : E => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) y‖ *
              Real.exp (c * α * ‖y‖ ^ 2)))) := by ring
        _ ≤ θ⁻¹ ^ j * (θ ^ n * ((n.choose i : ℝ) * M m * K i)) := by
            gcongr
    calc ‖y‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)) * f (fun _ => y)) y‖
        ≤ ‖y‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i (fun y : E => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) y‖ *
            ‖iteratedFDeriv ℝ (n - i) (fun y : E => f (fun _ => y)) y‖ := by gcongr
      _ = ∑ i ∈ Finset.range (n + 1), ‖y‖ ^ k * ((n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i (fun y : E => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) y‖ *
            ‖iteratedFDeriv ℝ (n - i) (fun y : E => f (fun _ => y)) y‖) := Finset.mul_sum _ _ _
      _ ≤ ∑ i ∈ Finset.range (n + 1), θ⁻¹ ^ j * (θ ^ n * ((n.choose i : ℝ) * M (n - i) * K i)) :=
            Finset.sum_le_sum hterm
      _ = θ⁻¹ ^ j * B := by rw [← Finset.mul_sum, ← Finset.mul_sum]
  have hgeom : Summable fun j : ℕ => θ⁻¹ ^ j * B :=
    (summable_geometric_of_lt_one (inv_nonneg.2 hθpos.le) (inv_lt_one_of_one_lt₀ (by linarith))).mul_right B
  exact Summable.of_nonneg_of_le (fun j => apply_nonneg _ _) hbound hgeom

end GlobalTheory.ConvSeries
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableSeminormGaussianConvolutionSeriesTermStatement

section

@[expose] public section

open MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.summable_seminorm_gaussianConvolutionSeriesTerm : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (b c : ℝ), 0 < b → 0 < c → ∀ (h : SchwartzMap E ℂ)
    (t : ℕ → SchwartzMap E ℂ), (∀ j y, t j y = GlobalTheory.ConvSeries.term b c h j y) →
    ∀ (k n : ℕ), Summable (fun j => SchwartzMap.seminorm ℂ k n (t j)) := by
  first | exact @GlobalTheory.ConvSeries.summable_seminorm_term | exact GlobalTheory.ConvSeries.summable_seminorm_term | (intros; apply GlobalTheory.ConvSeries.summable_seminorm_term <;> assumption)
end
end
