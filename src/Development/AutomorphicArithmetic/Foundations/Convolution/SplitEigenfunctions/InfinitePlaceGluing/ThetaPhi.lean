module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Entire
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.KkCpt
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.VolD
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsRest
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.MultiCentre
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaLiftTrivialOrbitTermsVanish
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ConjInv
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.ConjugateSelfDual.Statement
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import GroundTheory.AutomorphicForms.GL2.GJMatrixInfinite
import GroundTheory.GlobalFields.TateThesis.NoSmallSubgroups
import ReciprocityTheory.NeutralLocalFields.Reciprocity
public import Development.AutomorphicArithmetic.WhittakerHecke.IsCompactIntegralIdeleUnitsAndAbsEqOne
public import Development.AutomorphicArithmetic.WhittakerHecke.MeasurableThetaSeriesCompContinuous
public import Development.AutomorphicArithmetic.WhittakerHecke.NormAdmissibleBaseChangeSiegelSetLe
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ConjInv
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AutomorphicArithmetic.WhittakerHecke.NormThetaSeriesSiegelSetLeExp
public import Development.AutomorphicArithmetic.WhittakerHecke.ThetaSeriesPoissonFunctionalEquation
public import Development.AutomorphicArithmetic.WhittakerHecke.ThetaSeriesRatSL2MulInvariant
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AutomorphicArithmetic.WhittakerHecke.AutomorphicFormBaseChangeRatSL2MulInvariant

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

theorem UpperTheory.automorphicForm_baseChange_ratSL2_mul_invariant :
    ∀ {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) (ω : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ), admitted D ω φ →
        ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℚ) (g : G1 ℚ) (h : GL (Fin 2) (A ℚ)), φ (em E (gl (ratS ℚ γ * g) * h)) = φ (em E (gl g * h)) := by
  intro E _ _ D ω φ hφ γ g h
  have key : em E (gl (ratS ℚ γ)) =
      ratGL E 2 (Matrix.GeneralLinearGroup.map (algebraMap ℚ E) (Matrix.SpecialLinearGroup.toGL γ)) := by
    apply Units.ext
    ext i j
    simpa [UpperTheory.ConvolutionTheory.RankTwoDescent.em, gl, ratS, ratGL, Matrix.GeneralLinearGroup.map, Matrix.SpecialLinearGroup.map, Matrix.SpecialLinearGroup.toGL] using
      (AdeleBaseChange.adeleMap_algebraMap (K := ℚ) (L := E) (γ.1 i j))
  have e : gl (ratS ℚ γ * g) * h = gl (ratS ℚ γ) * (gl g * h) := by
    rw [gl, gl, map_mul, mul_assoc]
  rw [e, map_mul, key]
  exact hφ.left _ _
end
end

-- Source module: Development.AutomorphicArithmetic.WhittakerHecke.ContinuousGL2BaseChangeDiagUnitInfiniteIdele

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

theorem UpperTheory.continuous_GL2BaseChange_diagUnit_infiniteIdele :
    ∀ (E : Type) [Field E] [NumberField E], Continuous (em E) ∧ Continuous (dM : (A ℚ)ˣ → GL (Fin 2) (A ℚ)) ∧ Continuous (fun t : ℝ => iy (Real.exp t)) := by
  intro E _ _
  refine ⟨?_, ?_, ?_⟩
  · have hc : Continuous (AdeleBaseChange.adeleMap ℚ E) := AdeleBaseChange.continuous_adeleMap
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact Units.continuous_val.matrix_map hc
    · exact Units.continuous_coe_inv.matrix_map hc
  · refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · refine continuous_matrix fun i j => ?_
      fin_cases i <;> fin_cases j
      · exact continuous_const
      · exact continuous_const
      · exact continuous_const
      · exact Units.continuous_val
    · refine continuous_matrix fun i j => ?_
      fin_cases i <;> fin_cases j
      · exact continuous_const
      · exact continuous_const
      · exact continuous_const
      · exact Units.continuous_coe_inv
  · let u : ℝ → (TR.Rinf ℚ)ˣ := fun t =>
      ⟨fun _ => Real.exp t, fun _ => (Real.exp t)⁻¹,
        funext fun _ => mul_inv_cancel₀ (Real.exp_ne_zero t),
        funext fun _ => inv_mul_cancel₀ (Real.exp_ne_zero t)⟩
    have hu : Continuous u := by
      refine Units.continuous_iff.2 ⟨?_, ?_⟩
      · exact continuous_pi fun _ => Real.continuous_exp
      · exact continuous_pi fun _ => (Real.continuous_exp.inv₀ Real.exp_ne_zero)
    have he : (fun t : ℝ => iy (Real.exp t)) = fun t => TR.infId ℚ (u t) := by
      funext t
      simp only [iy, dif_neg (Real.exp_ne_zero t)]
      rfl
    rw [he]
    exact (TR.continuous_infId ℚ).comp hu
end
end

-- Source module: Development.AutomorphicArithmetic.WhittakerHecke.DifferentiableIntegralExpMulOfRapidDecay

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

theorem UpperTheory.differentiable_integral_exp_mul_of_rapid_decay :
    ∀ I : ℝ → ℂ, AEStronglyMeasurable I volume → (∀ n : ℕ, ∃ B : ℝ, ∀ t, ‖I t‖ ≤ B * Real.exp (-((n : ℝ) * |t|))) →
        Differentiable ℂ fun s : ℂ => ∫ t : ℝ, Complex.exp (2 * s * t) * I t := by
  intro I hI hdec s₀
  have hexp : Integrable (fun t : ℝ => Real.exp (-|t|)) := by
    rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ))]
    refine IntegrableOn.union ?_ ?_
    · refine (integrableOn_exp_Iic (0 : ℝ)).congr_fun (fun t ht => ?_) measurableSet_Iic
      simp [abs_of_nonpos (Set.mem_Iic.mp ht)]
    · refine (exp_neg_integrableOn_Ioi 0 (zero_lt_one (α := ℝ))).congr_fun (fun t ht => ?_)
        measurableSet_Ioi
      simp [abs_of_pos (Set.mem_Ioi.mp ht)]
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * (|s₀.re| + 1) + 2)
  obtain ⟨B, hB⟩ := hdec n
  have hB0 : 0 ≤ B := by
    have h := hB 0
    simp only [abs_zero, mul_zero, neg_zero, Real.exp_zero, mul_one] at h
    exact (norm_nonneg _).trans h
  have key : ∀ s : ℂ, s ∈ Metric.ball s₀ 1 → ∀ t : ℝ,
      ‖Complex.exp (2 * s * t)‖ * ‖I t‖ ≤ B * Real.exp (-(2 * |t|)) := by
    intro s hs t
    have hre : |s.re| ≤ |s₀.re| + 1 := by
      have h1 : |(s - s₀).re| ≤ ‖s - s₀‖ := Complex.abs_re_le_norm (s - s₀)
      have h2 : ‖s - s₀‖ < 1 := by simpa [dist_eq_norm] using hs
      have h3 := abs_sub_abs_le_abs_sub s.re s₀.re
      rw [Complex.sub_re] at h1
      linarith
    have hn1 : ‖Complex.exp (2 * s * t)‖ = Real.exp (2 * s.re * t) := by
      rw [Complex.norm_exp]
      simp
    have ht : 2 * s.re * t ≤ 2 * (|s₀.re| + 1) * |t| := by
      have h1 : s.re * t ≤ |s.re| * |t| := by
        rw [← abs_mul]
        exact le_abs_self _
      have h2 : |s.re| * |t| ≤ (|s₀.re| + 1) * |t| :=
        mul_le_mul_of_nonneg_right hre (abs_nonneg t)
      linarith
    have hnt : (2 * (|s₀.re| + 1) + 2) * |t| ≤ (n : ℝ) * |t| :=
      mul_le_mul_of_nonneg_right hn.le (abs_nonneg t)
    calc ‖Complex.exp (2 * s * t)‖ * ‖I t‖
        ≤ Real.exp (2 * (|s₀.re| + 1) * |t|) * (B * Real.exp (-((n : ℝ) * |t|))) := by
          rw [hn1]
          exact mul_le_mul (Real.exp_le_exp.mpr ht) (hB t) (norm_nonneg _) (Real.exp_pos _).le
      _ = B * Real.exp (2 * (|s₀.re| + 1) * |t| + -((n : ℝ) * |t|)) := by
          rw [Real.exp_add]
          ring
      _ ≤ B * Real.exp (-(2 * |t|)) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hB0
          linarith
  have hcont : ∀ s : ℂ, Continuous fun t : ℝ => Complex.exp (2 * s * t) := fun s => by
    fun_prop
  have hmeas : ∀ s : ℂ, AEStronglyMeasurable (fun t : ℝ => Complex.exp (2 * s * t) * I t) volume :=
    fun s => (hcont s).aestronglyMeasurable.mul hI
  have hmeas' : AEStronglyMeasurable
      (fun t : ℝ => (2 * (t : ℂ)) * Complex.exp (2 * s₀ * t) * I t) volume := by
    have hc : Continuous fun t : ℝ => (2 * (t : ℂ)) * Complex.exp (2 * s₀ * t) := by
      fun_prop
    exact hc.aestronglyMeasurable.mul hI
  have hF_int : Integrable (fun t : ℝ => Complex.exp (2 * s₀ * t) * I t) volume := by
    refine (hexp.const_mul B).mono' (hmeas s₀) (ae_of_all _ fun t => ?_)
    rw [norm_mul]
    refine (key s₀ (Metric.mem_ball_self one_pos) t).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hB0)
    linarith [abs_nonneg t]
  have h_bound : ∀ᵐ t : ℝ ∂volume, ∀ s ∈ Metric.ball s₀ 1,
      ‖(2 * (t : ℂ)) * Complex.exp (2 * s * t) * I t‖ ≤ 2 * B * Real.exp (-|t|) := by
    refine ae_of_all _ fun t s hs => ?_
    have hk := key s hs t
    have hnorm : ‖(2 * (t : ℂ)) * Complex.exp (2 * s * t) * I t‖
        = 2 * |t| * (‖Complex.exp (2 * s * t)‖ * ‖I t‖) := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      simp only [Complex.norm_ofNat]
      ring
    have habs : |t| ≤ Real.exp |t| := by
      linarith [Real.add_one_le_exp |t|]
    rw [hnorm]
    calc 2 * |t| * (‖Complex.exp (2 * s * t)‖ * ‖I t‖)
        ≤ 2 * Real.exp |t| * (B * Real.exp (-(2 * |t|))) :=
          mul_le_mul (by linarith) hk (by positivity) (by positivity)
      _ = 2 * B * (Real.exp |t| * Real.exp (-(2 * |t|))) := by ring
      _ = 2 * B * Real.exp (-|t|) := by
          rw [← Real.exp_add]
          congr 2
          ring
  have h_diff : ∀ᵐ t : ℝ ∂volume, ∀ s ∈ Metric.ball s₀ 1,
      HasDerivAt (fun x : ℂ => Complex.exp (2 * x * t) * I t)
        ((2 * (t : ℂ)) * Complex.exp (2 * s * t) * I t) s := by
    refine ae_of_all _ fun t s _ => ?_
    have h1 : HasDerivAt (fun x : ℂ => 2 * x * (t : ℂ)) (2 * (t : ℂ)) s := by
      simpa using ((hasDerivAt_id s).const_mul (2 : ℂ)).mul_const (t : ℂ)
    have h2 := h1.cexp.mul_const (I t)
    rwa [show Complex.exp (2 * s * t) * (2 * (t : ℂ)) * I t
        = (2 * (t : ℂ)) * Complex.exp (2 * s * t) * I t by ring] at h2
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun t : ℝ => 2 * B * Real.exp (-|t|))
    (F := fun (s : ℂ) (t : ℝ) => Complex.exp (2 * s * t) * I t)
    (F' := fun (s : ℂ) (t : ℝ) => (2 * (t : ℂ)) * Complex.exp (2 * s * t) * I t)
    (Metric.ball_mem_nhds s₀ one_pos) (Eventually.of_forall hmeas) hF_int hmeas' h_bound
    (hexp.const_mul (2 * B)) h_diff).2.differentiableAt
end
end

-- Source module: Development.AutomorphicArithmetic.WhittakerHecke.NormIntegralUnitaryHeckeCharFundDomainLe

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

theorem UpperTheory.norm_integral_unitaryHeckeChar_fundDomain_le :
    ∀ (M : Meas ℚ) (U : UMeas) (χ : HChar ℚ) (f : IdeleGroup ℚ → G1 ℚ → ℂ) (B : ℝ), (∀ a, ‖((χ.1 a : ℂˣ) : ℂ)‖ = 1) → Measurable (Function.uncurry f) →
        (∀ u ∈ UU, ∀ g, ‖f u g‖ ≤ B) →
        (∀ u ∈ UU, IntegrableOn (f u) M.D M.μ) ∧ Integrable (fun u => ((χ.1 u : ℂˣ) : ℂ) * ∫ g in M.D, f u g ∂M.μ) U.υ ∧
          ‖∫ u, ((χ.1 u : ℂˣ) : ℂ) * ∫ g in M.D, f u g ∂M.μ ∂U.υ‖ ≤ B * M.μ.real M.D := by
  intro M U χ f B hχ hf hB
  haveI := U.prob
  have hD : M.μ M.D < ⊤ := UpperTheory.ConvolutionTheory.R2.M.volD ℚ M
  haveI : IsFiniteMeasure (M.μ.restrict M.D) := ⟨by simpa using hD⟩
  have hfu : ∀ u, Measurable (f u) := fun u => hf.comp measurable_prodMk_left
  have hae : ∀ᵐ u ∂U.υ, u ∈ (UU : Set (A ℚ)ˣ) := mem_ae_iff.mpr U.supp
  have hI : StronglyMeasurable (fun u => ∫ g in M.D, f u g ∂M.μ) :=
    (hf.stronglyMeasurable).integral_prod_right
  have hχm : Measurable (fun u : IdeleGroup ℚ => ((χ.1 u : ℂˣ) : ℂ)) :=
    (Units.continuous_val.comp χ.2.1).measurable
  have hbd : ∀ᵐ u ∂U.υ, ‖((χ.1 u : ℂˣ) : ℂ) * ∫ g in M.D, f u g ∂M.μ‖ ≤ B * M.μ.real M.D := by
    filter_upwards [hae] with u hu
    rw [norm_mul, hχ, one_mul]
    exact norm_setIntegral_le_of_norm_le_const hD (fun g _ => hB u hu g)
  refine ⟨fun u hu => Integrable.of_bound (hfu u).aestronglyMeasurable B (Eventually.of_forall (hB u hu)), ?_, ?_⟩
  · exact Integrable.of_bound (hχm.aestronglyMeasurable.mul hI.aestronglyMeasurable) _ hbd
  · simpa using norm_integral_le_of_norm_le_const hbd
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.ThetaPhi

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

variable {E : Type} [Field E] [NumberField E]

private theorem thetaPhi (D : Dat ℚ E) (ω : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ) (hφ : admitted D ω φ)
    (Φ : (Fin 2 → A ℚ) → ℂ) (hΦ : Φ ∈ schwartzBruhatPi (K := ℚ) (ι := Fin 2))
    (C C' : Set (GL (Fin 2) (A ℚ))) (hC : IsCompact C) (hC' : IsCompact C') (n : ℕ) :
    ∃ B : ℝ, ∀ t : ℝ, 0 ≤ t → ∀ g : G1 ℚ, ∀ k ∈ C, ∀ k' ∈ C',
      ‖φ (em E (gl g * k)) * ThR Φ t (gl g * k')‖ ≤ B * Real.exp (-((n : ℝ) * t)) := by
  obtain ⟨c, hc, hred⟩ := UpperTheory.ConvolutionTheory.R2.red ℚ
  have hK : IsCompact (KK ℚ) := (UpperTheory.ConvolutionTheory.R2.M.kkCpt ℚ).2
  have cpt : ∀ S : Set (GL (Fin 2) (A ℚ)), IsCompact S →
      IsCompact ((fun p : G1 ℚ × GL (Fin 2) (A ℚ) => gl p.1 * p.2) '' (KK ℚ ×ˢ S)) := fun S hS =>
    (hK.prod hS).image ((UpperTheory.ConvolutionTheory.R2.M.continuous_gl.comp continuous_fst).mul continuous_snd)
  obtain ⟨r, B₁, h₁⟩ := UpperTheory.norm_thetaSeries_siegelSet_le_exp Φ hΦ _ (cpt C' hC') c hc n
  obtain ⟨B₂, h₂⟩ := UpperTheory.norm_admissible_baseChange_siegelSet_le D ω φ hφ _ (cpt C hC) c hc r
  refine ⟨B₂ * B₁, fun t ht g k hk k' hk' => ?_⟩
  obtain ⟨γ, b, a, κ, hκ, hg, hca⟩ := hred g
  have ea : ∀ h : GL (Fin 2) (A ℚ), gl (nU b * mD a * κ) * h = gl (nU b * mD a) * (gl κ * h) := fun h => by
    have hm : gl (nU b * mD a * κ) = gl (nU b * mD a) * gl κ := map_mul _ _ _
    rw [hm, mul_assoc]
  have e1 : φ (em E (gl g * k)) = φ (em E (gl (nU b * mD a) * (gl κ * k))) := by
    rw [← ea, ← hg, UpperTheory.automorphicForm_baseChange_ratSL2_mul_invariant D ω φ hφ]
  have e2 : ThR Φ t (gl g * k') = ThR Φ t (gl (nU b * mD a) * (gl κ * k')) := by
    rw [← ea, ← hg, UpperTheory.thetaSeries_ratSL2_mul_invariant]
  have p₂ := h₂ b a _ ⟨(κ, k), ⟨hκ, hk⟩, rfl⟩ hca
  have p₁ := h₁ t ht b a _ ⟨(κ, k'), ⟨hκ, hk'⟩, rfl⟩ hca
  have hab : 0 < ab a := UpperTheory.ConvolutionTheory.R2.M.ab_pos a
  rw [e1, e2, norm_mul]
  calc _ ≤ (B₂ * (ab a)⁻¹ ^ r) * (B₁ * Real.exp (-((n : ℝ) * t)) * ab a ^ r) :=
        mul_le_mul p₂ p₁ (norm_nonneg _) ((norm_nonneg _).trans p₂)
    _ = B₂ * B₁ * Real.exp (-((n : ℝ) * t)) := by
        rw [inv_pow]; field_simp

private theorem measPhi (ω : HChar ℚ) (D : Dat ℚ E) (φ : GL (Fin 2) (A E) → ℂ) (hφ : admitted D ω φ) {X : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (h : X → GL (Fin 2) (A ℚ)) (hh : Continuous h) : Measurable fun x => φ (em E (h x)) :=
  (hφ.cont.comp ((UpperTheory.continuous_GL2BaseChange_diagUnit_infiniteIdele E).1.comp hh)).measurable

private theorem irMeas (D : Dat ℚ E) (ω χ : HChar ℚ) (M : Meas ℚ) (U : UMeas) (φ : GL (Fin 2) (A E) → ℂ) (hφ : admitted D ω φ)
    (Φ : (Fin 2 → A ℚ) → ℂ) (hΦ : Φ ∈ schwartzBruhatPi (K := ℚ) (ι := Fin 2)) : StronglyMeasurable (Ir M U χ φ Φ) := by
  haveI := U.prob
  haveI : IsFiniteMeasure (M.μ.restrict M.D) := ⟨by simpa using UpperTheory.ConvolutionTheory.R2.M.volD ℚ M⟩
  have hdM := (UpperTheory.continuous_GL2BaseChange_diagUnit_infiniteIdele E).2.1
  have hc : Continuous fun p : (ℝ × IdeleGroup ℚ) × G1 ℚ => gl p.2 * dM p.1.2 :=
    (UpperTheory.ConvolutionTheory.R2.M.continuous_gl.comp continuous_snd).mul (hdM.comp (continuous_snd.comp continuous_fst))
  have h1 : StronglyMeasurable fun p : (ℝ × IdeleGroup ℚ) × G1 ℚ =>
      φ (em E (gl p.2 * dM p.1.2)) * ThR Φ p.1.1 (gl p.2 * dM p.1.2) :=
    ((measPhi ω D φ hφ _ hc).mul (UpperTheory.measurable_thetaSeries_comp_continuous Φ hΦ _ _ (continuous_fst.comp continuous_fst) hc)).stronglyMeasurable
  have h2 := h1.integral_prod_right' (ν := M.μ.restrict M.D)
  have hχ : StronglyMeasurable fun x : ℝ × IdeleGroup ℚ => ((χ.1 x.2 : ℂˣ) : ℂ) :=
    (Units.continuous_val.comp (χ.2.1.comp continuous_snd)).stronglyMeasurable
  exact (hχ.mul h2).integral_prod_right' (ν := U.υ)

private theorem irDecay (D : Dat ℚ E) (ω χ : HChar ℚ) (M : Meas ℚ) (U : UMeas) (φ : GL (Fin 2) (A E) → ℂ) (hφ : admitted D ω φ)
    (hχ : ∀ a, ‖((χ.1 a : ℂˣ) : ℂ)‖ = 1) (hP : Per M U χ φ = 0)
    (Φ : (Fin 2 → A ℚ) → ℂ) (hΦ : Φ ∈ schwartzBruhatPi (K := ℚ) (ι := Fin 2)) (n : ℕ) :
    ∃ B : ℝ, ∀ t, ‖Ir M U χ φ Φ t‖ ≤ B * Real.exp (-((n : ℝ) * |t|)) := by
  haveI := U.prob
  obtain ⟨hUc, hU1⟩ := UpperTheory.isCompact_integralIdeleUnits_and_abs_eq_one
  have hdM := (UpperTheory.continuous_GL2BaseChange_diagUnit_infiniteIdele E).2.1
  obtain ⟨Ψ, hΨ, hpois⟩ := UpperTheory.thetaSeries_poisson_functional_equation Φ hΦ
  set C : Set (GL (Fin 2) (A ℚ)) := (fun u : (A ℚ)ˣ => dM u) '' UU with hCdef
  set C' : Set (GL (Fin 2) (A ℚ)) := (fun u : (A ℚ)ˣ => (gl (wW ℚ))⁻¹ * dM u⁻¹) '' UU with hC'def
  have hC : IsCompact C := hUc.image hdM
  have hc' : Continuous fun u : (A ℚ)ˣ => (gl (wW ℚ))⁻¹ * dM u⁻¹ := continuous_const.mul (hdM.comp continuous_inv)
  have hC' : IsCompact C' := hUc.image hc'
  obtain ⟨Bp, hBp⟩ := thetaPhi D ω φ hφ Φ hΦ C C hC hC n
  obtain ⟨Bm, hBm⟩ := thetaPhi D ω φ hφ Ψ hΨ C C' hC hC' (n + 2)
  set V : ℝ := M.μ.real M.D with hV
  have hV0 : 0 ≤ V := measureReal_nonneg
  obtain ⟨Bφ, hBφ⟩ := hφ.bdd
  have hcu : Continuous fun p : IdeleGroup ℚ × G1 ℚ => gl p.2 * dM p.1 :=
    (UpperTheory.ConvolutionTheory.R2.M.continuous_gl.comp continuous_snd).mul (hdM.comp continuous_fst)
  have hcu' : Continuous fun p : IdeleGroup ℚ × G1 ℚ => gl p.2 * ((gl (wW ℚ))⁻¹ * dM p.1⁻¹) :=
    (UpperTheory.ConvolutionTheory.R2.M.continuous_gl.comp continuous_snd).mul (hc'.comp continuous_fst)
  have mφ : Measurable fun p : IdeleGroup ℚ × G1 ℚ => φ (em E (gl p.2 * dM p.1)) := measPhi ω D φ hφ _ hcu
  refine ⟨(|Bp| + |Bm|) * V, fun t => ?_⟩
  rcases le_or_gt 0 t with ht | ht
  ·
    have hb : ∀ u ∈ UU, ∀ g : G1 ℚ, ‖φ (em E (gl g * dM u)) * ThR Φ t (gl g * dM u)‖ ≤ Bp * Real.exp (-((n : ℝ) * t)) :=
      fun u hu g => hBp t ht g _ ⟨u, hu, rfl⟩ _ ⟨u, hu, rfl⟩
    have hm : Measurable (Function.uncurry fun (u : IdeleGroup ℚ) (g : G1 ℚ) => φ (em E (gl g * dM u)) * ThR Φ t (gl g * dM u)) :=
      mφ.mul (UpperTheory.measurable_thetaSeries_comp_continuous Φ hΦ _ _ continuous_const hcu)
    have := (UpperTheory.norm_integral_unitaryHeckeChar_fundDomain_le M U χ _ _ hχ hm hb).2.2
    rw [abs_of_nonneg ht]
    refine le_trans this ?_
    have hex := Real.exp_pos (-((n : ℝ) * t))
    have : Bp ≤ |Bp| + |Bm| := (le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _))
    calc Bp * Real.exp (-((n : ℝ) * t)) * V ≤ (|Bp| + |Bm|) * Real.exp (-((n : ℝ) * t)) * V := by gcongr
      _ = _ := by ring
  ·
    set e : ℂ := (Real.exp (-(2 * t)) : ℂ) with he
    set c₀ : ℂ := -Φ 0 + e * Ψ 0 with hc₀
    have hb1 : ∀ u ∈ UU, ∀ g : G1 ℚ, ‖φ (em E (gl g * dM u))‖ ≤ Bφ := fun _ _ _ => hBφ _
    have hb2 : ∀ u ∈ UU, ∀ g : G1 ℚ, ‖φ (em E (gl g * dM u)) * ThR Ψ (-t) (gl g * ((gl (wW ℚ))⁻¹ * dM u⁻¹))‖ ≤
        Bm * Real.exp (-(((n + 2 : ℕ) : ℝ) * (-t))) :=
      fun u hu g => hBm (-t) (by linarith) g _ ⟨u, hu, rfl⟩ _ ⟨u, hu, rfl⟩
    have hm1 : Measurable (Function.uncurry fun (u : IdeleGroup ℚ) (g : G1 ℚ) => φ (em E (gl g * dM u))) := mφ
    have hm2 : Measurable (Function.uncurry fun (u : IdeleGroup ℚ) (g : G1 ℚ) =>
        φ (em E (gl g * dM u)) * ThR Ψ (-t) (gl g * ((gl (wW ℚ))⁻¹ * dM u⁻¹))) :=
      mφ.mul (UpperTheory.measurable_thetaSeries_comp_continuous Ψ hΨ _ _ continuous_const hcu')
    obtain ⟨i1, j1, -⟩ := UpperTheory.norm_integral_unitaryHeckeChar_fundDomain_le M U χ _ _ hχ hm1 hb1
    obtain ⟨i2, j2, n2⟩ := UpperTheory.norm_integral_unitaryHeckeChar_fundDomain_le M U χ _ _ hχ hm2 hb2
    have hae : ∀ᵐ u ∂U.υ, u ∈ UU := by
      have := U.supp
      exact measure_eq_zero_iff_ae_notMem.1 this |>.mono fun u hu => by simpa using hu
    have key : Ir M U χ φ Φ t = c₀ * Per M U χ φ + e * ∫ u, ((χ.1 u : ℂˣ) : ℂ) * ∫ g in M.D,
        φ (em E (gl g * dM u)) * ThR Ψ (-t) (gl g * ((gl (wW ℚ))⁻¹ * dM u⁻¹)) ∂M.μ ∂U.υ := by
      unfold Per
      rw [← integral_const_mul, ← integral_const_mul, ← integral_add (j1.const_mul _) (j2.const_mul _)]
      unfold Ir
      refine integral_congr_ae (hae.mono fun u hu => ?_)
      have hin : ∫ g in M.D, φ (em E (gl g * dM u)) * ThR Φ t (gl g * dM u) ∂M.μ =
          c₀ * (∫ g in M.D, φ (em E (gl g * dM u)) ∂M.μ) + e * ∫ g in M.D,
            φ (em E (gl g * dM u)) * ThR Ψ (-t) (gl g * ((gl (wW ℚ))⁻¹ * dM u⁻¹)) ∂M.μ := by
        rw [← integral_const_mul, ← integral_const_mul, ← integral_add ((i1 u hu).const_mul _) ((i2 u hu).const_mul _)]
        refine integral_congr_ae (Eventually.of_forall fun g => ?_)
        simp only []
        rw [hpois t g u (hU1 u hu)]
        ring
      simp only []
      rw [hin]
      ring
    rw [key, hP, mul_zero, zero_add, norm_mul, he, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, abs_of_neg ht]
    refine (mul_le_mul_of_nonneg_left n2 (Real.exp_pos _).le).trans ?_
    have hex : Real.exp (-(2 * t)) * Real.exp (-(((n + 2 : ℕ) : ℝ) * (-t))) = Real.exp (-((n : ℝ) * -t)) := by
      rw [← Real.exp_add]; congr 1; push_cast; ring
    have : Bm ≤ |Bp| + |Bm| := (le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _))
    have hpos := Real.exp_pos (-((n : ℝ) * -t))
    calc Real.exp (-(2 * t)) * (Bm * Real.exp (-(((n + 2 : ℕ) : ℝ) * (-t))) * V)
        = Bm * (Real.exp (-(2 * t)) * Real.exp (-(((n + 2 : ℕ) : ℝ) * (-t)))) * V := by ring
      _ = Bm * Real.exp (-((n : ℝ) * -t)) * V := by rw [hex]
      _ ≤ (|Bp| + |Bm|) * Real.exp (-((n : ℝ) * -t)) * V := by gcongr
      _ = _ := by ring

theorem ent_of :
    Ent := by
  intro E _ _ _ D P ω χ _ hω hχ M U φ hφ hP Φ hΦ
  have hχ1 : ∀ a, ‖((χ.1 a : ℂˣ) : ℂ)‖ = 1 := fun a => by
    have h := congrArg (fun z : ℂˣ => ‖(z : ℂ)‖) (hχ a)
    simp only [Units.val_pow_eq_pow_val, Units.val_mul, norm_pow, norm_mul, Units.val_one, norm_one] at h
    rw [show ‖((ω.1 a : ℂˣ) : ℂ)‖ = 1 from hω a, mul_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h
  exact UpperTheory.differentiable_integral_exp_mul_of_rapid_decay _ (irMeas D ω χ M U φ hφ Φ hΦ).aestronglyMeasurable fun n => irDecay D ω χ M U φ hφ hχ1 hP Φ hΦ n

end UpperTheory.ConvolutionTheory.RankTwoDescent

end
end
end
