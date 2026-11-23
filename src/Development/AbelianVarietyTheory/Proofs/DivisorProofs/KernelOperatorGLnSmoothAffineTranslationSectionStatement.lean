module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OnMatInfOfIsUnit
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArchimedeanModerateGrowthMatrixSmoothingIntegr
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
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandCLMInfApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArchimedeanRapidKernelOperatorFinsetSum
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Linter.Style
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRapidSuperpositionCharacters
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzIntegralBoundSmoothStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothingAffineFamilyEqIntegralKernelStatement
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.UniformSpace.Uniformizable

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanMatrixSmoothingModerateGrowth

section

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf

theorem smoothMatInf_keeps_modGrowth : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ)
    (α : (Fin n → Fin n → Cinf E) → ℂ), Continuous α → HasCompactSupport α →
    tsupport α ⊆ {x | IsUnit (Matrix.of x)} → ∀ W : GL (Fin n) (Cinf E) → ℂ, IsModGrowthInf W →
    IsModGrowthInf (smoothMatInf α W) :=
  isModGrowthInf_smoothMatInf

end GlobalTheory.JSW.MirCinf
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanMatrixSmoothingModerateGrowthStatement

section

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

theorem _root_.GlobalTheory.T.archimedeanMatrixSmoothing_moderateGrowth : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (α : (Fin n → Fin n → Cinf E) → ℂ), Continuous α → HasCompactSupport α → tsupport α ⊆ {x | IsUnit (Matrix.of x)} → ∀ W : GL (Fin n) (Cinf E) → ℂ, IsModGrowthInf W → IsModGrowthInf (smoothMatInf α W) := by
  first | (exact @GlobalTheory.JSW.MirCinf.smoothMatInf_keeps_modGrowth) | (exact GlobalTheory.JSW.MirCinf.smoothMatInf_keeps_modGrowth) | (intros; apply GlobalTheory.JSW.MirCinf.smoothMatInf_keeps_modGrowth  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanRapidKernelOperatorCompRapidFamily

section

@[expose] public section

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem measurable_htInf_comp {X : Type} [MeasurableSpace X] {γ : X → GL (Fin n) (Cinf E)}
    (hγ : ∀ i j, Measurable fun x => (γ x : Matrix (Fin n) (Fin n) (Cinf E)) i j) :
    Measurable fun x => htInf (γ x) := by
  unfold htInf
  refine Finset.measurable_prod _ fun w _ => ?_
  exact measurable_comp_GL (F := htGL) continuous_htGL fun i j => (measurable_pi_apply w).comp (hγ i j)

theorem isKerOpInf_comp_rapidFamInf : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Z : Type) [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (T : (GL (Fin n) (Cinf E) → ℂ) → Z → GL (Fin n) (Cinf E) → ℂ),
    IsKerOpInf T → ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : GL (Fin n) (Cinf E) → X → ℂ)
    (γ : X → GL (Fin n) (Cinf E)) (η : GL (Fin n) (Cinf E) → X → Z →L[ℝ] ℝ), IsRapidFamInf ν k γ η →
    ∀ (S : (GL (Fin n) (Cinf E) → ℂ) → GL (Fin n) (Cinf E) → ℂ) (t : Z → GL (Fin n) (Cinf E)) (χ : Z → ℂ),
    (∀ W, IsModGrowthInf W → IsModGrowthInf (S W)) →
    (∀ W, IsModGrowthInf W → ∀ q z g, χ z * S W (g * t z * q) = ∫ x, k q x * (𝐞 (η q x z) : ℂ) * W (g * γ x) ∂ν) →
    IsKerOpInf (fun W z g => χ z * T (S W) z (g * t z)) := by
  intro E _ _ n Z _ _ _ T hT X _ ν _ k γ η hfam S t χ hS hSk
  obtain ⟨X₀, m₀, ν₀, hν₀, k₀, γ₀, η₀, ⟨hk₀, hγ₀, hη₀, hint₀⟩, hT⟩ := hT
  obtain ⟨hγ, hjoint, hmom⟩ := hfam
  obtain ⟨hkj, hηj⟩ := hjoint X₀ γ₀ hγ₀
  have mη₀ : Measurable η₀ := measurable_dual hη₀
  have mηj : Measurable fun p : X₀ × X => η (γ₀ p.1) p.2 := measurable_dual hηj
  have mht : Measurable fun x => htInf (γ x) := measurable_htInf_comp hγ
  have hrap : IsRapidFInf (ν₀.prod ν) (fun p : X₀ × X => k₀ p.1 * k (γ₀ p.1) p.2) (fun p => γ p.2)
      (fun p => η₀ p.1 + η (γ₀ p.1) p.2) := by
    refine ⟨(hk₀.comp measurable_fst).mul hkj, fun i j => (hγ i j).comp measurable_snd,
      fun z => ((hη₀ z).comp measurable_fst).add (hηj z), fun N => ?_⟩
    obtain ⟨C, M, hCM⟩ := hmom N
    let F : X₀ × X → ℝ := fun p => (‖k₀ p.1‖ * (1 + ‖η₀ p.1‖) ^ N) *
      (‖k (γ₀ p.1) p.2‖ * (htInf (γ p.2) * (1 + ‖η (γ₀ p.1) p.2‖)) ^ N)
    have mF : Measurable F := by
      have a1 : Measurable fun p : X₀ × X => k₀ p.1 := hk₀.comp measurable_fst
      have a2 : Measurable fun p : X₀ × X => η₀ p.1 := mη₀.comp measurable_fst
      have a3 : Measurable fun p : X₀ × X => htInf (γ p.2) := mht.comp measurable_snd
      exact (a1.norm.mul ((measurable_const.add a2.norm).pow_const N)).mul
        (hkj.norm.mul ((a3.mul (measurable_const.add mηj.norm)).pow_const N))
    have F0 : ∀ p, 0 ≤ F p := fun p => by
      have := htInf_pos' (γ p.2)
      positivity
    have hF : Integrable F (ν₀.prod ν) := by
      rw [integrable_prod_iff mF.aestronglyMeasurable]
      refine ⟨Filter.Eventually.of_forall fun x₀ => ((hCM (γ₀ x₀)).1.const_mul (‖k₀ x₀‖ * (1 + ‖η₀ x₀‖) ^ N)), ?_⟩
      refine ((hint₀ (max N M)).const_mul (max C 0)).mono'
        (mF.norm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
        (Filter.Eventually.of_forall fun x₀ => ?_)
      have e1 : ∫ y, ‖F (x₀, y)‖ ∂ν = (‖k₀ x₀‖ * (1 + ‖η₀ x₀‖) ^ N) *
          ∫ y, ‖k (γ₀ x₀) y‖ * (htInf (γ y) * (1 + ‖η (γ₀ x₀) y‖)) ^ N ∂ν := by
        rw [← integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun y => Real.norm_of_nonneg (F0 _))
      have I0 : 0 ≤ ∫ y, ‖F (x₀, y)‖ ∂ν := integral_nonneg fun _ => norm_nonneg _
      rw [Real.norm_of_nonneg I0, e1]
      have hq := (hCM (γ₀ x₀)).2
      have A0 : 0 ≤ ‖k₀ x₀‖ * (1 + ‖η₀ x₀‖) ^ N := by positivity
      have h1 : 1 ≤ htInf (γ₀ x₀) := le_of_eq_of_le rfl (by
        unfold htInf
        calc (1 : ℝ) = ∏ _w : InfinitePlace E, (1 : ℝ) := by simp
          _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) fun w _ => one_le_htGL _)
      have h2 : (1 : ℝ) ≤ 1 + ‖η₀ x₀‖ := by linarith [norm_nonneg (η₀ x₀)]
      have p1 : (1 + ‖η₀ x₀‖) ^ N ≤ (1 + ‖η₀ x₀‖) ^ max N M := pow_le_pow_right₀ h2 (le_max_left _ _)
      have p2 : htInf (γ₀ x₀) ^ M ≤ htInf (γ₀ x₀) ^ max N M := pow_le_pow_right₀ h1 (le_max_right _ _)
      have hm : C * htInf (γ₀ x₀) ^ M ≤ max C 0 * htInf (γ₀ x₀) ^ max N M :=
        mul_le_mul (le_max_left _ _) p2 (by positivity) (le_max_right _ _)
      calc ‖k₀ x₀‖ * (1 + ‖η₀ x₀‖) ^ N * ∫ y, ‖k (γ₀ x₀) y‖ * (htInf (γ y) * (1 + ‖η (γ₀ x₀) y‖)) ^ N ∂ν
          ≤ ‖k₀ x₀‖ * (1 + ‖η₀ x₀‖) ^ N * (max C 0 * htInf (γ₀ x₀) ^ max N M) :=
            mul_le_mul_of_nonneg_left (hq.trans hm) A0
        _ ≤ ‖k₀ x₀‖ * (1 + ‖η₀ x₀‖) ^ max N M * (max C 0 * htInf (γ₀ x₀) ^ max N M) := by
            gcongr
        _ = max C 0 * (‖k₀ x₀‖ * (htInf (γ₀ x₀) * (1 + ‖η₀ x₀‖)) ^ max N M) := by rw [mul_pow]; ring
    refine hF.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact (((hk₀.comp measurable_fst).mul hkj).norm.mul (((mht.comp measurable_snd).mul
        (measurable_const.add ((mη₀.comp measurable_fst).add mηj).norm)).pow_const N)).aestronglyMeasurable
    · have hh := htInf_pos' (γ p.2)
      have hb : htInf (γ p.2) * (1 + ‖η₀ p.1 + η (γ₀ p.1) p.2‖) ≤
          (1 + ‖η₀ p.1‖) * (htInf (γ p.2) * (1 + ‖η (γ₀ p.1) p.2‖)) := by
        have := mul_le_mul_of_nonneg_left (show 1 + ‖η₀ p.1 + η (γ₀ p.1) p.2‖ ≤ (1 + ‖η₀ p.1‖) * (1 + ‖η (γ₀ p.1) p.2‖) by
          nlinarith [norm_add_le (η₀ p.1) (η (γ₀ p.1) p.2), norm_nonneg (η₀ p.1), norm_nonneg (η (γ₀ p.1) p.2),
            mul_nonneg (norm_nonneg (η₀ p.1)) (norm_nonneg (η (γ₀ p.1) p.2))]) hh.le
        linarith
      have hp : (htInf (γ p.2) * (1 + ‖η₀ p.1 + η (γ₀ p.1) p.2‖)) ^ N ≤
          (1 + ‖η₀ p.1‖) ^ N * (htInf (γ p.2) * (1 + ‖η (γ₀ p.1) p.2‖)) ^ N :=
        (pow_le_pow_left₀ (by positivity) hb N).trans_eq (mul_pow _ _ _)
      rw [Real.norm_of_nonneg (by positivity), norm_mul]
      calc ‖k₀ p.1‖ * ‖k (γ₀ p.1) p.2‖ * (htInf (γ p.2) * (1 + ‖η₀ p.1 + η (γ₀ p.1) p.2‖)) ^ N
          ≤ ‖k₀ p.1‖ * ‖k (γ₀ p.1) p.2‖ *
              ((1 + ‖η₀ p.1‖) ^ N * (htInf (γ p.2) * (1 + ‖η (γ₀ p.1) p.2‖)) ^ N) :=
            mul_le_mul_of_nonneg_left hp (by positivity)
        _ = F p := by simp only [F]; ring
  refine ⟨X₀ × X, inferInstance, ν₀.prod ν, inferInstance, _, _, _, hrap, ?_⟩
  intro W hW z g
  have hint := hrap.integrable hW z g
  show χ z * T (S W) z (g * t z) = _
  rw [integral_prod _ hint, hT (S W) (hS W hW) z (g * t z), ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x₀ => ?_)
  simp only
  rw [show χ z * (k₀ x₀ * (𝐞 (η₀ x₀ z) : ℂ) * S W (g * t z * γ₀ x₀)) =
      k₀ x₀ * (𝐞 (η₀ x₀ z) : ℂ) * (χ z * S W (g * t z * γ₀ x₀)) by ring, hSk W hW (γ₀ x₀) z g,
    ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [ContinuousLinearMap.add_apply, AddChar.map_add_eq_mul, Circle.coe_mul]
  ring

end GlobalTheory.JSW.MirCinf
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanRapidKernelOperatorCompRapidFamilyStatement

section

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

theorem _root_.GlobalTheory.T.archimedeanRapidKernelOperator_comp_rapidFamily : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (T : (GL (Fin n) (Cinf E) → ℂ) → Z → GL (Fin n) (Cinf E) → ℂ), IsKerOpInf T → ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : GL (Fin n) (Cinf E) → X → ℂ) (γ : X → GL (Fin n) (Cinf E)) (η : GL (Fin n) (Cinf E) → X → Z →L[ℝ] ℝ), IsRapidFamInf ν k γ η → ∀ (S : (GL (Fin n) (Cinf E) → ℂ) → GL (Fin n) (Cinf E) → ℂ) (t : Z → GL (Fin n) (Cinf E)) (χ : Z → ℂ), (∀ W, IsModGrowthInf W → IsModGrowthInf (S W)) → (∀ W, IsModGrowthInf W → ∀ q z g, χ z * S W (g * t z * q) = ∫ x, k q x * (𝐞 (η q x z) : ℂ) * W (g * γ x) ∂ν) → IsKerOpInf (fun W z g => χ z * T (S W) z (g * t z)) := by
  first | (exact @GlobalTheory.JSW.MirCinf.isKerOpInf_comp_rapidFamInf) | (exact GlobalTheory.JSW.MirCinf.isKerOpInf_comp_rapidFamInf) | (intros; apply GlobalTheory.JSW.MirCinf.isKerOpInf_comp_rapidFamInf  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRapidSuperpositionCharactersStatement

section

@[expose] public section

open MeasureTheory GlobalTheory.JSW
open scoped FourierTransform ContDiff

theorem _root_.GlobalTheory.T.exists_rapid_superposition_characters' : ∀ (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (Φ : Z → ℂ), ContDiff ℝ ∞ Φ → HasCompactSupport Φ → ∃ (X : Type) (_ : MeasurableSpace X) (ν : Measure X) (_ : SFinite ν) (κ : X → ℂ) (τ : X → Z →L[ℝ] ℝ), Measurable κ ∧ (∀ z, Measurable fun x => τ x z) ∧ (∀ N : ℕ, Integrable (fun x => ‖κ x‖ * (1 + ‖τ x‖) ^ N) ν) ∧ ∀ z, Φ z = ∫ x, κ x * (𝐞 (τ x z) : ℂ) ∂ν := by
  first | exact @GlobalTheory.JSW.exists_rapid_superposition_characters | exact GlobalTheory.JSW.exists_rapid_superposition_characters | (intros; apply GlobalTheory.JSW.exists_rapid_superposition_characters <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelOperatorGLnSmoothAffineTranslationSection

section

@[expose] public section

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf

theorem kerOpInf_section : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (σ₀ : Fin n → Fin n → Cinf E) (L : Z →L[ℝ] (Fin n → Fin n → Cinf E)) (χ : Z → ℂ) (α : (Fin n → Fin n → Cinf E) → ℂ), ContDiff ℝ ∞ χ → HasCompactSupport χ → (∀ z ∈ tsupport χ, IsUnit (Matrix.of (σ₀ + L z))) → ContDiff ℝ ∞ α → HasCompactSupport α → tsupport α ⊆ {x | IsUnit (Matrix.of x)} → ∀ T : (GL (Fin n) (Cinf E) → ℂ) → Z → GL (Fin n) (Cinf E) → ℂ, IsKerOpInf T → IsKerOpInf (fun W z g => χ z * T (smoothMatInf α W) z (g * (toGLInf (Matrix.of (σ₀ + L z)))⁻¹)) := by
  intro E _ _ n Z _ _ _ σ₀ L χ α hχ hχc hσ hα hαc hαs T hT
  have hdet : ∀ w : InfinitePlace E, ContDiff ℝ ∞ fun p : Z × (Fin n → Fin n → Cinf E) =>
      (Matrix.of (σ₀ + L p.1)).det w := by
    intro w
    simp only [Matrix.det_apply', Matrix.of_apply, Finset.sum_apply, Pi.mul_apply, Finset.prod_apply]
    refine ContDiff.sum fun s _ => ?_
    refine ContDiff.mul ?_ (contDiff_prod fun i _ => ?_)
    · exact contDiff_const
    have : ContDiff ℝ ∞ fun p : Z × (Fin n → Fin n → Cinf E) => σ₀ + L p.1 :=
      contDiff_const.add (L.contDiff.comp contDiff_fst)
    exact contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 this (s i)) i) w
  have hJ : ContDiff ℝ ∞ fun p : Z × (Fin n → Fin n → Cinf E) =>
      ((jacInf (Matrix.of (σ₀ + L p.1)) : ℝ) : ℂ) := by
    simp only [jacInf, Complex.ofReal_prod, Complex.ofReal_pow, Complex.normSq_eq_conj_mul_self]
    exact contDiff_prod fun w _ => ((Complex.conjCLE.contDiff.comp (hdet w)).mul (hdet w)).pow n
  have hΦ : ContDiff ℝ ∞ fun p : Z × (Fin n → Fin n → Cinf E) =>
      χ p.1 * ((jacInf (Matrix.of (σ₀ + L p.1)) : ℝ) : ℂ) * α p.2 :=
    ((hχ.comp contDiff_fst).mul hJ).mul (hα.comp contDiff_snd)
  have hΦc : HasCompactSupport fun p : Z × (Fin n → Fin n → Cinf E) =>
      χ p.1 * ((jacInf (Matrix.of (σ₀ + L p.1)) : ℝ) : ℂ) * α p.2 := by
    refine HasCompactSupport.intro (hχc.isCompact.prod hαc.isCompact) fun p hp => ?_
    rcases not_and_or.1 hp with h | h
    · simp [image_eq_zero_of_notMem_tsupport h]
    · simp [image_eq_zero_of_notMem_tsupport h]
  obtain ⟨X, _, ν, _, κ, τ, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_rapid_superposition_characters' _ _ hΦ hΦc
  obtain ⟨R, hR⟩ := GlobalTheory.T.smoothing_affine_family_eq_integral_kernel E n Z σ₀ L χ α hχc hσ hαc hαs X ν κ τ h1 h2 h3 (fun z a => h4 (z, a))
  exact GlobalTheory.T.archimedeanRapidKernelOperator_comp_rapidFamily E n Z T hT _ _ _ _ _ (GlobalTheory.T.schwartz_integral_bound_smooth E n Z X ν κ τ h1 h2 h3 R σ₀ L) (smoothMatInf α) _ χ
    (GlobalTheory.T.archimedeanMatrixSmoothing_moderateGrowth E n α hα.continuous hαc hαs) hR

end GlobalTheory.JSW.MirCinf
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelOperatorGLnSmoothAffineTranslationSectionStatement

section

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

theorem _root_.GlobalTheory.T.kernelOperator_GLn_smoothAffineTranslation_section : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (σ₀ : Fin n → Fin n → Cinf E) (L : Z →L[ℝ] (Fin n → Fin n → Cinf E)) (χ : Z → ℂ) (α : (Fin n → Fin n → Cinf E) → ℂ), ContDiff ℝ ∞ χ → HasCompactSupport χ → (∀ z ∈ tsupport χ, IsUnit (Matrix.of (σ₀ + L z))) → ContDiff ℝ ∞ α → HasCompactSupport α → tsupport α ⊆ {x | IsUnit (Matrix.of x)} → ∀ T : (GL (Fin n) (Cinf E) → ℂ) → Z → GL (Fin n) (Cinf E) → ℂ, IsKerOpInf T → IsKerOpInf (fun W z g => χ z * T (smoothMatInf α W) z (g * (toGLInf (Matrix.of (σ₀ + L z)))⁻¹)) := by
  first | exact @GlobalTheory.JSW.MirCinf.kerOpInf_section | exact GlobalTheory.JSW.MirCinf.kerOpInf_section | (intros; apply GlobalTheory.JSW.MirCinf.kerOpInf_section <;> assumption)
end
end
