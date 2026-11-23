module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Entire
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.AdmissibleRightTranslate
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.CardHeckeT1Cosets
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.ContInfGL2
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.ContOn
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.DvMulIff
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.ExistsBad
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.ExistsNat
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.ExtOf
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.FacOf
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.InnerInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.OneAddXNe
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.PairCases
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.PhiMem
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.ShiftM
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.ThetaPhi
public import Development.AutomorphicArithmetic.WhittakerHecke.IdeleCoveringLintegralEqConstMulHaar
public import Development.AutomorphicArithmetic.WhittakerHecke.IntegralTsumIdeleCoveringEqConstMul
public import Development.AutomorphicArithmetic.WhittakerHecke.IntegralUnfoldedIntegrandEqZetaIntegral
public import Development.AutomorphicArithmetic.WhittakerHecke.SetIntegralRestrictMulThetaKernelEqUnfolded
public import Development.AutomorphicArithmetic.WhittakerHecke.TsumUnfoldedIntegrandIdeleCoveringEqExpMul
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Aa
public import Development.AutomorphicArithmetic.WhittakerHecke.MeasurableWhittakerIdeleDiagTorusMul
public import Development.AutomorphicArithmetic.WhittakerHecke.SchwartzBruhatRowLintegralAbsPowBounded
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.KkCpt
public import Development.AutomorphicArithmetic.WhittakerHecke.LintegralIdeleRatPolyDecayMulNormRpowLtTop
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.WhittakerLieDerivativeLinear
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.UnitsCpt

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.Landau

section

@[expose] public section

open UpperTheory.ConvolutionTheory.RankTwoDescent

open scoped ComplexOrder

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.landau_of :
    Landau := by
  intro b hb0 hb1 hbs hent
  obtain ⟨F, hF, hFb⟩ := hent
  by_contra hinf
  have hinf' : ({n | 1 ≤ b n} \ {0, 1} : Set ℕ).Infinite :=
    Set.Infinite.diff hinf (Set.toFinite _)
  obtain ⟨m, hm⟩ := exists_nat_gt (F 0).re
  obtain ⟨S, hSsub, hScard⟩ := hinf'.exists_subset_card_eq m
  have hS0 : ∀ n ∈ S, n ≠ 0 := fun n hn h => (hSsub hn).2 (by simp [h])
  have hS1 : 1 ∉ S := fun hn => (hSsub hn).2 (by simp)
  have hS2 : ∀ n ∈ S, 1 ≤ b n := fun n hn => (hSsub hn).1
  let a : ℕ → ℂ := fun n => if n ∈ S then 0 else b n
  let G : ℂ → ℂ := fun s => F s - ∑ n ∈ S, b n / (n : ℂ) ^ s
  have hG : Differentiable ℂ G := by
    refine hF.sub (Differentiable.fun_sum fun n hn => ?_)
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (hS0 n hn)
    exact (differentiable_const _).div (differentiable_id.const_cpow (Or.inl hn0))
      fun s => by simp [Complex.cpow_eq_zero_iff, hn0]
  have hsum : ∀ s : ℂ, 4 < s.re →
      HasSum (LSeries.term a s) (LSeries b s - ∑ n ∈ S, b n / (n : ℂ) ^ s) := by
    intro s hs
    have h1 : HasSum (LSeries.term b s) (LSeries b s) := (hbs s hs).LSeriesHasSum
    have h2 : HasSum (fun n => if n ∈ S then LSeries.term b s n else 0)
        (∑ n ∈ S, b n / (n : ℂ) ^ s) := by
      have h3 : HasSum (fun n => if n ∈ S then LSeries.term b s n else 0)
          (∑ n ∈ S, if n ∈ S then LSeries.term b s n else 0) :=
        hasSum_sum_of_ne_finset_zero (fun n hn => by simp [hn])
      have h5 : (∑ n ∈ S, if n ∈ S then LSeries.term b s n else 0) =
          ∑ n ∈ S, b n / (n : ℂ) ^ s :=
        Finset.sum_congr rfl fun n hn => by
          simp [hn, LSeries.term_of_ne_zero (hS0 n hn)]
      rwa [h5] at h3
    have h6 : LSeries.term a s =
        fun n => LSeries.term b s n - if n ∈ S then LSeries.term b s n else 0 := by
      funext n
      by_cases hn : n ∈ S
      · simp [a, hn, LSeries.term_def]
      · simp [a, hn, LSeries.term_def]
    rw [h6]
    exact h1.sub h2
  have ha0 : 0 ≤ a := by
    intro n
    by_cases hn : n ∈ S
    · simp [a, hn]
    · simpa [a, hn] using hb0 n
  have ha1 : 0 < a 1 := by
    simp [a, hS1, hb1]
  have habs : LSeries.abscissaOfAbsConv a ≤ (4 : ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
      (hsum y (by simpa using hy)).summable
  have hEq : {s : ℂ | (4 : ℝ) < s.re}.EqOn G (LSeries a) := by
    intro s hs
    have hs' : (4 : ℝ) < s.re := hs
    have h4 : (4 : ℝ) < s.re := hs'
    have : LSeries a s = LSeries b s - ∑ n ∈ S, b n / (n : ℂ) ^ s :=
      LSeriesHasSum.LSeries_eq (hsum s h4)
    simp only [G, hFb s h4]
    exact this.symm
  have hpos := LSeries.positive_of_differentiable_of_eqOn ha0 ha1 hG habs hEq 0
  have hG0 : G ((0 : ℝ) : ℂ) = F 0 - ∑ n ∈ S, b n := by
    simp [G]
  rw [hG0] at hpos
  have hre : (∑ n ∈ S, b n).re < (F 0).re := by
    have := (Complex.lt_def.mp hpos).1
    simpa using this
  have hcard : (m : ℝ) ≤ (∑ n ∈ S, b n).re := by
    rw [Complex.re_sum, ← hScard]
    have : ∀ n ∈ S, (1 : ℝ) ≤ (b n).re := fun n hn => by
      simpa using (Complex.le_def.mp (hS2 n hn)).1
    simpa using Finset.card_nsmul_le_sum S _ 1 this
  linarith
end
end

-- Source module: Development.AutomorphicArithmetic.WhittakerHecke.WhittakerLintegralAbsPowBoundedOnMaximalCompact

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

theorem UpperTheory.whittaker_lintegral_abs_pow_bounded_on_maximalCompact :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (ω : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ), admitted D ω φ → ∀ x : ℝ, 1 < x → ∃ C : ℝ≥0, ∀ k ∈ KK ℚ,
        ∫⁻ y : IdeleGroup ℚ, ‖Wo D φ (em E (aE y * gl k))‖ₑ * ENNReal.ofReal (ab y ^ x) ∂(ideleMeasure ℚ) ≤ C := by
  intro E _ _ D ω φ hA x hx
  have hemc : Continuous (em E) :=
    Continuous.units_map _ (Continuous.matrix_map continuous_id AdeleBaseChange.continuous_adeleMap)
  have hglc : Continuous (gl : G1 ℚ → GL (Fin 2) (A ℚ)) := Matrix.SpecialLinearGroup.continuous_toGL
  have hC : IsCompact ((fun k : G1 ℚ => em E (gl k)) '' KK ℚ) :=
    (UpperTheory.ConvolutionTheory.R2.M.kkCpt ℚ).2.image (hemc.comp hglc)
  obtain ⟨K, hKc, hK⟩ := hA.wdec _ hC
  obtain ⟨r, hr⟩ := exists_nat_gt x
  obtain ⟨B, hB⟩ := hK r
  have hI := UpperTheory.lintegral_idele_rat_polyDecay_mul_norm_rpow_lt_top K hKc x hx r hr
  refine ⟨(ENNReal.ofReal |B| * ∫⁻ y : IdeleGroup ℚ, (if (y : A ℚ).2 ∈ K then ENNReal.ofReal (((1 + |re (y : A ℚ)|) ^ r)⁻¹ * ab y ^ x) else 0) ∂(ideleMeasure ℚ)).toNNReal, fun k hk => ?_⟩
  rw [ENNReal.coe_toNNReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI.ne),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun y => ?_
  have hb := hB y (em E (gl k)) ⟨k, hk, rfl⟩
  rw [← map_mul] at hb
  have hab : 0 ≤ ab y ^ x := Real.rpow_nonneg (IdeleGroup.ideleModule ℚ y).2.le x
  by_cases hy : (y : A ℚ).2 ∈ K
  · rw [if_pos hy, ← ENNReal.ofReal_mul (abs_nonneg _), ← ofReal_norm_eq_enorm,
      ← ENNReal.ofReal_mul (norm_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← mul_assoc]
    refine mul_le_mul_of_nonneg_right (hb.1.trans ?_) hab
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
  · have h0 : Wo D φ (em E (aE y * gl k)) = 0 := by
      by_contra h
      exact hy (hb.2 h)
    rw [h0, enorm_zero, zero_mul]
    exact bot_le
end
end

-- Source module: Development.AutomorphicArithmetic.WhittakerHecke.UnfoldedIntegrandMeasurableIntegrableOfReGtFour

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

theorem UpperTheory.unfoldedIntegrand_measurable_integrable_of_re_gt_four :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (ω χ : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ), admitted D ω φ → Unit1 ω → (∀ a, (χ.1 a * ω.1 a) ^ 2 = 1) → ∀ (M₀ : Meas ℚ), ∀ Φ ∈ schwartzBruhatPi (K := ℚ) (ι := Fin 2), ∀ s : ℂ, 4 < s.re →
        Measurable (Un.Hh D χ φ Φ s) ∧ Integrable (Un.Hh D χ φ Φ s) ((ideleMeasure ℚ).prod ((ideleMeasure ℚ).prod M₀.κ)) := by
  intro E _ _ D ω χ φ hA hU hχ M₀ Φ hΦ s hs
  haveI := M₀.prob
  have hχn : ∀ a, ‖((χ.1 a : ℂˣ) : ℂ)‖ = 1 := by
    intro a
    have h := congrArg (fun u : ℂˣ => ‖(u : ℂ)‖) (hχ a)
    simp only [Units.val_pow_eq_pow_val, Units.val_mul, norm_pow, norm_mul, Units.val_one, norm_one, hU a, mul_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h
  have hχe : ∀ a, ‖((χ.1 a : ℂˣ) : ℂ)‖ₑ = 1 := by
    intro a
    rw [← ofReal_norm, hχn a, ENNReal.ofReal_one]
  have hcn : ∀ (y : IdeleGroup ℚ) (w : ℂ), ‖((ab y : ℝ) : ℂ) ^ w‖ₑ = ENNReal.ofReal (ab y ^ w.re) := by
    intro y w
    rw [← ofReal_norm, Complex.norm_cpow_eq_rpow_re_of_pos (M.ab_pos y)]
  have hW := UpperTheory.measurable_whittaker_idele_diagTorus_mul E D ω φ hA
  have hχm : Measurable fun y : IdeleGroup ℚ => ((χ.1 y : ℂˣ) : ℂ) :=
    (Units.continuous_val.comp χ.2.1).measurable
  have habm : Measurable fun y : IdeleGroup ℚ => ab y := M.continuous_ab.measurable
  have hΦc : Continuous fun p : IdeleGroup ℚ × G1 ℚ => Φ fun j => ((p.1 : (A ℚ)ˣ) : A ℚ) * row p.2 j :=
    (continuous_of_mem_schwartzBruhatPi hΦ).comp (continuous_pi fun j =>
      (Units.continuous_val.comp continuous_fst).mul ((M.continuous_entry 1 j).comp continuous_snd))
  have hΦm := hΦc.measurable
  have hcp : ∀ w : ℂ, Measurable fun y : IdeleGroup ℚ => ((ab y : ℝ) : ℂ) ^ w := fun w =>
    (Complex.measurable_ofReal.comp habm).pow_const w
  have hrp : ∀ x : ℝ, Measurable fun y : IdeleGroup ℚ => ENNReal.ofReal (ab y ^ x) := fun x =>
    (habm.pow_const x).ennreal_ofReal
  have hm : Measurable (Un.Hh D χ φ Φ s) :=
    ((((hW.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))).mul
      (hχm.comp measurable_fst)).mul ((hcp _).comp measurable_fst))).mul
      ((hΦm.comp measurable_snd).mul ((hcp _).comp (measurable_fst.comp measurable_snd)))
  refine ⟨hm, hm.aestronglyMeasurable, ?_⟩
  obtain ⟨C₁, hC₁⟩ := UpperTheory.whittaker_lintegral_abs_pow_bounded_on_maximalCompact E D ω φ hA (s.re - 1) (by linarith)
  obtain ⟨C₂, hC₂⟩ := UpperTheory.schwartzBruhat_row_lintegral_abs_pow_bounded Φ hΦ (2 * s.re) (by linarith)
  let Aa : IdeleGroup ℚ × G1 ℚ → ℝ≥0∞ := fun p =>
    ‖Wo D φ (em E (aE p.1 * gl p.2))‖ₑ * ENNReal.ofReal (ab p.1 ^ (s.re - 1))
  let Bb : IdeleGroup ℚ × G1 ℚ → ℝ≥0∞ := fun p =>
    ‖Φ fun j => ((p.1 : (A ℚ)ˣ) : A ℚ) * row p.2 j‖ₑ * ENNReal.ofReal (ab p.1 ^ (2 * s.re))
  have hAm : Measurable Aa := hW.enorm.mul ((hrp _).comp measurable_fst)
  have hBm : Measurable Bb := hΦm.enorm.mul ((hrp _).comp measurable_fst)
  have hnorm : ∀ q, ‖Un.Hh D χ φ Φ s q‖ₑ = Aa (q.1, q.2.2) * Bb q.2 := by
    intro q
    have e1 : (s - 1).re = s.re - 1 := by simp
    have e2 : (2 * s).re = 2 * s.re := by simp
    simp only [Un.Hh, enorm_mul, hχe, mul_one, hcn, e1, e2, Aa, Bb]
  have hFm : Measurable fun q : IdeleGroup ℚ × IdeleGroup ℚ × G1 ℚ => Aa (q.1, q.2.2) * Bb q.2 :=
    (hAm.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))).mul (hBm.comp measurable_snd)
  have hae : ∀ᵐ k ∂M₀.κ, k ∈ KK ℚ := by
    rw [ae_iff]
    exact M₀.supp
  show ∫⁻ q, ‖Un.Hh D χ φ Φ s q‖ₑ ∂((ideleMeasure ℚ).prod ((ideleMeasure ℚ).prod M₀.κ)) < ⊤
  simp_rw [hnorm]
  rw [lintegral_prod_symm _ hFm.aemeasurable, lintegral_prod_symm _ hFm.lintegral_prod_left'.aemeasurable]
  refine lt_of_le_of_lt (lintegral_mono_ae (g := fun _ => (C₁ * C₂ : ℝ≥0∞)) (hae.mono fun k hk => ?_)) ?_
  · have h1 : ∀ z : IdeleGroup ℚ, ∫⁻ y : IdeleGroup ℚ, Aa (y, k) * Bb (z, k) ∂(ideleMeasure ℚ) ≤ C₁ * Bb (z, k) := by
      intro z
      have hAk : Measurable fun y : IdeleGroup ℚ => Aa (y, k) := hAm.comp measurable_prodMk_right
      rw [lintegral_mul_const _ hAk]
      exact mul_le_mul_left (hC₁ k hk) _
    refine (lintegral_mono h1).trans ?_
    have hBk : Measurable fun z : IdeleGroup ℚ => Bb (z, k) := hBm.comp measurable_prodMk_right
    rw [lintegral_const_mul _ hBk]
    exact mul_le_mul_right (hC₂ k hk) _
  · rw [lintegral_const, measure_univ, mul_one]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.coe_lt_top
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.UnfOf

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

open UpperTheory.ConvolutionTheory.RankTwoDescent

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.unf_of :
    Unf := by
  intro E _ _ _ D P ω χ hC hω hχ M U
  haveI := M.prob
  haveI := U.prob
  obtain ⟨c, hc0, hc⟩ := UpperTheory.ideleCovering_lintegral_eq_const_mul_haar U
  refine ⟨(c : ℂ), by exact_mod_cast hc0, ?_⟩
  intro φ hA Φ hΦ s hs
  obtain ⟨hm, hI⟩ := UpperTheory.unfoldedIntegrand_measurable_integrable_of_re_gt_four E D ω χ φ hA hω hχ M Φ hΦ s hs
  obtain ⟨hsum, heq⟩ := UpperTheory.integral_tsum_ideleCovering_eq_const_mul U c hc M.κ (Un.Hh D χ φ Φ s) hm hI
  rw [← UpperTheory.integral_unfoldedIntegrand_eq_zetaIntegral E D χ φ M Φ s hI, ← heq]
  unfold Zs Ir
  refine integral_congr_ae ?_
  have hUU : ∀ᵐ u ∂U.υ, u ∈ UU := mem_ae_iff.2 U.supp
  filter_upwards [hsum] with t ht
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [ht, hUU] with u hu huU
  rw [UpperTheory.setIntegral_restrict_mul_thetaKernel_eq_unfolded E D ω φ hA M Φ hΦ t u huU, ← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hu] with p hp
  exact UpperTheory.tsum_unfoldedIntegrand_ideleCovering_eq_exp_mul E D ω χ φ hA hχ Φ s t u huU p hp
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.AsaiNV

section

@[expose] public section

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

theorem trAdm : TrAdm := trAdm_of decE

theorem asaiNV : AsaiNV :=
  asai_of trAdm exGd_of chEx_of (asEx_of satU_of)
    (ext_of trAdm perTr_of ent_of unf_of phiMem_of fac_of (shiftM_of trAdm (shift_of trAdm)) hol_of nonZ_of) (lan_of satU_of landau_of)

end UpperTheory.ConvolutionTheory.RankTwoDescent
end
end
