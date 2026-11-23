module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.AffineCharacterGenerators.AffChar
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.SepNodeQuad
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.TruncSpec
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.TruncatedCuspIrreducibility.AdelDefs
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.TruncatedCuspIrreducibility.ScatteringLimits
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Archimedean
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Counting
import GroundTheory.AutomorphicForms.QuotientMeasure
import GroundTheory.AutomorphicForms.ReductionBlock
import GroundTheory.AutomorphicForms.WhittakerRelevance
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Functor
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.Exponents3

section

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.exponents3 :
    ∀ (d : ℕ → ℕ), Tendsto (fun j : ℕ => (d j : ℝ) / j) atTop (𝓝 0) → (∀ B : ℝ, ∀ᶠ j : ℕ in atTop, Real.exp (B * j) ≤ (d j).factorial) →
      ∀ (p : ℕ), 0 < p → ∀ (cq a₀ : ℝ), 0 < a₀ → a₀ ≤ 1 → ∃ N : ℝ, ∀ c₁ : ℝ, ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ < a₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ∀ (I : Type) [Fintype I] (a : I → ℝ) (ζ : I → ℂ), (∀ i, η < a i) → (∀ i, ζ i ≠ 0) →
      Function.Injective (fun i => (a i, ζ i)) → ∀ (c : ℕ → I → ℂ) (c' : I → ℂ), (∀ i, Tendsto (fun j => c j i) atTop (𝓝 (c' i))) →
      (∀ s₀ : ℕ, ∃ K : ℝ, ∀ᶠ j : ℕ in atTop, ∀ s ≤ s₀, ∀ s' ≤ s₀,
        ‖∑ i, c j i * (a i : ℂ) ^ d j * (cheb η (j / p + s) (a i) : ℂ) * ζ i ^ (j + s')‖ ≤
        K ^ (d j + 1) * (Real.exp (c₁ * j) * (1 + (4 / η) ^ (j / p) / (d j).factorial) + (4 / η) ^ (j / p) * Real.exp (-N * j))) →
      ∀ i, a₀ ≤ a i → Real.exp (-cq) ≤ ‖ζ i‖ → c' i = 0 := by
  intro d hd hfac p hp cq a₀ h0 h1
  refine ⟨cq + 2 + Real.log (4 / a₀), ?_⟩
  intro c₁
  obtain ⟨A, hA⟩ : ∃ A, A = |c₁ + cq + 1| + 1 := ⟨_, rfl⟩
  have hη₀a : a₀ * Real.exp (-(p * A)) < a₀ := by
    have hA0 : 0 < A := by rw [hA]; positivity
    have hp' : (0 : ℝ) < p := by exact_mod_cast hp
    have : Real.exp (-(p * A)) < 1 := Real.exp_lt_one_iff.2 (by nlinarith [mul_pos hp' hA0])
    nlinarith
  refine ⟨a₀ * Real.exp (-(p * A)), by positivity, hη₀a, ?_⟩
  intro η hηp hη
  have hηa : η < a₀ := hη.trans_lt hη₀a
  intro I _ a ζ ha hζ0 hinj c c' hc hbd i hi hζ
  obtain ⟨s₀, K₁, hsep⟩ := UpperTheory.ConvolutionTheory.FX.separate0 η hηp I a ζ ha hζ0 hinj
  obtain ⟨K, hK⟩ := hbd s₀
  have pow_le_exp_eventually (d : ℕ → ℕ) (hd : Tendsto (fun j : ℕ => (d j : ℝ) / j) atTop (𝓝 0))
      (L : ℝ) (hL : 0 < L) : ∀ᶠ j : ℕ in atTop, L ^ (d j + 1) ≤ Real.exp j := by
    have h1 : Tendsto (fun j : ℕ => Real.log L * ((d j : ℝ) / j + 1 / j)) atTop
        (𝓝 (Real.log L * (0 + 0))) :=
      (hd.add tendsto_one_div_atTop_nhds_zero_nat).const_mul _
    have h2 := h1.eventually (gt_mem_nhds (show Real.log L * (0 + 0) < 1 by simp))
    filter_upwards [h2, eventually_gt_atTop 0] with j hj hj0
    have hjp : (0 : ℝ) < j := by exact_mod_cast hj0
    have h3 : Real.log L * ((d j : ℝ) + 1) ≤ j := by
      have : Real.log L * ((d j : ℝ) / j + 1 / j) = Real.log L * ((d j : ℝ) + 1) / j := by ring
      rw [this, div_lt_one hjp] at hj
      exact hj.le
    calc L ^ (d j + 1) = Real.exp (Real.log L * ((d j : ℝ) + 1)) := by
          rw [← Real.rpow_def_of_pos hL]
          rw [← Real.rpow_natCast]; push_cast; rfl
      _ ≤ _ := Real.exp_le_exp.2 h3
  have err_bound2 (p : ℕ) (hp : 0 < p) (c₁ cq a₀ : ℝ) (h0 : 0 < a₀) (h1 : a₀ ≤ 1)
      (A η : ℝ) (hA : A = |c₁ + cq + 1| + 1) (hηp : 0 < η) (hη : η ≤ a₀ * Real.exp (-(p * A))) (j : ℕ) (F : ℝ)
      (hF : Real.exp ((c₁ + cq + 2 + Real.log (4 / a₀)) * j) ≤ F) :
      Real.exp ((cq + 1) * j) * (η / a₀) ^ (j / p) *
        (Real.exp (c₁ * j) * (1 + (4 / η) ^ (j / p) / F) +
          (4 / η) ^ (j / p) * Real.exp (-(cq + 2 + Real.log (4 / a₀)) * j)) ≤
        (Real.exp (p * A) + 2) * Real.exp (-j) := by
    have hFp : 0 < F := (Real.exp_pos _).trans_le hF
    set m := j / p with hm
    set g := Real.log (4 / a₀) with hg
    have hq : (η / a₀) ^ m * (4 / η) ^ m = (4 / a₀) ^ m := by
      rw [← mul_pow]; congr 1; field_simp
    have h4 : (4 / a₀) ^ m ≤ Real.exp (g * j) := by
      have : (1 : ℝ) ≤ 4 / a₀ := by rw [le_div_iff₀ h0]; linarith
      calc (4 / a₀) ^ m ≤ (4 / a₀) ^ j := pow_le_pow_right₀ this (Nat.div_le_self _ _)
        _ = Real.exp (g * j) := by
          rw [mul_comm, Real.exp_nat_mul, hg, Real.exp_log (by positivity)]
    have h5 : (η / a₀) ^ m ≤ Real.exp (-(m * p * A)) := by
      have : η / a₀ ≤ Real.exp (-(p * A)) := by rw [div_le_iff₀ h0, mul_comm]; exact hη
      calc _ ≤ Real.exp (-(p * A)) ^ m := by gcongr
        _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
    have hmp : (j : ℝ) ≤ m * p + p := by
      have := Nat.lt_div_mul_add (a := j) hp
      rw [← hm] at this
      exact_mod_cast this.le
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hA0 : 0 ≤ A := by rw [hA]; positivity
    have hA1 : c₁ + cq + 2 ≤ A := by have := le_abs_self (c₁ + cq + 1); linarith
    have t1 : Real.exp ((cq + 1) * j) * (η / a₀) ^ m * Real.exp (c₁ * j) ≤
        Real.exp (p * A) * Real.exp (-j) := by
      refine le_trans (b := Real.exp ((cq + 1) * j) * Real.exp (-(m * p * A)) * Real.exp (c₁ * j))
        (by gcongr) ?_
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.2
      nlinarith [mul_le_mul_of_nonneg_right hmp hA0, mul_le_mul_of_nonneg_right hA1 hj]
    have t2 : Real.exp ((cq + 1) * j) * Real.exp (c₁ * j) * (4 / a₀) ^ m / F ≤ Real.exp (-j) := by
      rw [div_le_iff₀ hFp]
      calc _ ≤ Real.exp ((cq + 1) * j) * Real.exp (c₁ * j) * Real.exp (g * j) := by gcongr
        _ = Real.exp (-j) * Real.exp ((c₁ + cq + 2 + g) * j) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
        _ ≤ _ := by gcongr
    have t3 : Real.exp ((cq + 1) * j) * (4 / a₀) ^ m * Real.exp (-(cq + 2 + g) * j) ≤
        Real.exp (-j) := by
      calc _ ≤ Real.exp ((cq + 1) * j) * Real.exp (g * j) * Real.exp (-(cq + 2 + g) * j) := by gcongr
        _ = Real.exp (-j) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    rw [← hq] at t2 t3
    calc _ = Real.exp ((cq + 1) * j) * (η / a₀) ^ m * Real.exp (c₁ * j) +
          Real.exp ((cq + 1) * j) * Real.exp (c₁ * j) * ((η / a₀) ^ m * (4 / η) ^ m) / F +
          Real.exp ((cq + 1) * j) * ((η / a₀) ^ m * (4 / η) ^ m) * Real.exp (-(cq + 2 + g) * j) := by
          ring
      _ ≤ _ := by linarith
  have solve_bound2 (x a z η a₀ cq K₁ K E : ℝ) (d m j : ℕ) (hx : 0 ≤ x) (hη : 0 < η)
      (hηa : η < a₀) (h1 : a₀ ≤ 1) (ha : a₀ ≤ a) (hz : Real.exp (-cq) ≤ z) (hE : 0 ≤ E)
      (hL : ((|K₁| + 1) * |K| / a₀ + 1) ^ (d + 1) ≤ Real.exp j)
      (h : x * a ^ d * (2 * a / η - 1) ^ m * z ^ j ≤ K₁ * (K ^ (d + 1) * E)) :
      x ≤ Real.exp ((cq + 1) * j) * (η / a₀) ^ m * E := by
    have h0 : 0 < a₀ := hη.trans hηa
    have hb : a₀ / η ≤ 2 * a / η - 1 := by
      rw [div_sub_one hη.ne', div_le_div_iff_of_pos_right hη]; linarith
    have hb0 : 0 < a₀ / η := by positivity
    have hl : x * a₀ ^ (d + 1) * (a₀ / η) ^ m * Real.exp (-cq) ^ j ≤
        x * a ^ d * (2 * a / η - 1) ^ m * z ^ j := by
      have : a₀ ^ (d + 1) ≤ a ^ d :=
        (pow_le_pow_of_le_one h0.le h1 (Nat.le_succ d)).trans (pow_le_pow_left₀ h0.le ha d)
      have h2 : 0 ≤ a := by linarith
      have h3 : 0 ≤ 2 * a / η - 1 := by linarith
      gcongr
    have hr : K₁ * (K ^ (d + 1) * E) ≤ a₀ ^ (d + 1) * Real.exp j * E := by
      have e1 : |K₁| ≤ (|K₁| + 1) ^ (d + 1) :=
        (by linarith : |K₁| ≤ |K₁| + 1).trans
          (le_self_pow₀ (by linarith [abs_nonneg K₁]) (Nat.succ_ne_zero d))
      calc K₁ * (K ^ (d + 1) * E) ≤ |K₁ * (K ^ (d + 1) * E)| := le_abs_self _
        _ = |K₁| * |K| ^ (d + 1) * E := by
          rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg hE, mul_assoc]
        _ ≤ (|K₁| + 1) ^ (d + 1) * |K| ^ (d + 1) * E := by gcongr
        _ = a₀ ^ (d + 1) * ((|K₁| + 1) * |K| / a₀) ^ (d + 1) * E := by
          rw [← mul_pow, ← mul_pow]; congr 2; field_simp
        _ ≤ a₀ ^ (d + 1) * ((|K₁| + 1) * |K| / a₀ + 1) ^ (d + 1) * E := by
          gcongr; linarith
        _ ≤ _ := by gcongr
    have h6 := (hl.trans h).trans hr
    have hpos : 0 < a₀ ^ (d + 1) * (a₀ / η) ^ m * Real.exp (-cq) ^ j := by positivity
    have e2 : (η / a₀) ^ m * (a₀ / η) ^ m = 1 := by
      rw [← mul_pow]
      have : η / a₀ * (a₀ / η) = 1 := by field_simp
      rw [this, one_pow]
    have e3 : Real.exp ((cq + 1) * j) * Real.exp (-cq) ^ j = Real.exp j := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
    refine le_of_mul_le_mul_right ?_ hpos
    calc _ = x * a₀ ^ (d + 1) * (a₀ / η) ^ m * Real.exp (-cq) ^ j := by ring
      _ ≤ a₀ ^ (d + 1) * Real.exp j * E := h6
      _ = a₀ ^ (d + 1) * (Real.exp ((cq + 1) * j) * Real.exp (-cq) ^ j) *
          ((η / a₀) ^ m * (a₀ / η) ^ m) * E := by rw [e2, e3, mul_one]
      _ = _ := by ring
  have hev : ∀ᶠ j : ℕ in atTop, ‖c j i‖ ≤ (Real.exp (p * A) + 2) * Real.exp (-j) := by
    filter_upwards [hK, hfac (c₁ + cq + 2 + Real.log (4 / a₀)),
      pow_le_exp_eventually d hd ((|K₁| + 1) * |K| / a₀ + 1) (by positivity)] with j hj hF hL
    have h := hsep (j / p) j (fun i => c j i * (a i : ℂ) ^ d j) _ hj i
    have hai : 0 ≤ a i := by linarith
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hai] at h
    exact (solve_bound2 _ _ _ η a₀ cq K₁ K _ _ _ _ (norm_nonneg _) hηp hηa h1 hi hζ
      (by positivity) hL h).trans (err_bound2 p hp c₁ cq a₀ h0 h1 A η hA hηp hη j _ hF)
  have hlim : Tendsto (fun j : ℕ => (Real.exp (p * A) + 2) * Real.exp (-j)) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop).const_mul
      (Real.exp (p * A) + 2)
    simpa using this
  exact tendsto_nhds_unique (hc i) (squeeze_zero_norm' hev hlim)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.Regroup

section

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

open Classical in
private lemma regroup {T : Type} (s : Finset T) (a : T → ℝ) (S : T → Finset ℂ) (c : T → ℂ → ℂ) (w : T → ℂ) (P : Finset (ℝ × ℂ))
    (hP : ∀ i ∈ s, ∀ ζ ∈ S i, (a i, ζ) ∈ P) (f : ℝ × ℂ → ℂ) :
    ∑ q ∈ P, (∑ i ∈ s, if a i = q.1 ∧ q.2 ∈ S i then w i * c i q.2 else 0) * f q =
      ∑ i ∈ s, w i * ∑ ζ ∈ S i, c i ζ * f (a i, ζ) := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mul_sum]
  symm
  have hinj : Set.InjOn (fun ζ : ℂ => (a i, ζ)) (S i) := fun z _ z' _ h => (Prod.ext_iff.1 h).2
  calc ∑ ζ ∈ S i, w i * (c i ζ * f (a i, ζ))
      = ∑ q ∈ (S i).image (fun ζ : ℂ => (a i, ζ)), (if a i = q.1 ∧ q.2 ∈ S i then w i * c i q.2 else 0) * f q := by
        rw [Finset.sum_image hinj]
        refine Finset.sum_congr rfl fun ζ hζ => ?_
        rw [if_pos ⟨rfl, hζ⟩, mul_assoc]
    _ = _ := by
        refine Finset.sum_subset ?_ ?_
        · intro q hq
          obtain ⟨ζ, hζ, rfl⟩ := Finset.mem_image.1 hq
          exact hP i hi ζ hζ
        · intro q _ hq
          rw [if_neg, zero_mul]
          rintro ⟨h1, h2⟩
          exact hq (Finset.mem_image.2 ⟨q.2, h2, Prod.ext h1 rfl⟩)

private lemma d_top (d : ℕ → ℕ) (h : ∀ B : ℝ, ∀ᶠ j : ℕ in atTop, Real.exp (B * j) ≤ (d j).factorial) :
    Tendsto d atTop atTop := by
  refine tendsto_atTop.2 fun M => ?_
  filter_upwards [h 1, eventually_ge_atTop M.factorial] with j hj hM
  by_contra hlt
  have h1 : (d j).factorial ≤ M.factorial := Nat.factorial_le (not_le.1 hlt).le
  have h2 : ((d j).factorial : ℝ) ≤ j := by exact_mod_cast h1.trans hM
  have h3 := Real.add_one_le_exp (1 * (j : ℝ))
  linarith

private lemma low_bd (Z : Finset ℂ) (hZ : ∀ ζ ∈ Z, ζ ≠ 0) : ∃ cq : ℝ, ∀ ζ ∈ Z, Real.exp (-cq) ≤ ‖ζ‖ := by
  obtain ⟨M, hM⟩ := (Z.image fun ζ => -Real.log ‖ζ‖).bddAbove
  refine ⟨M, fun ζ hζ => ?_⟩
  have h1 : -Real.log ‖ζ‖ ≤ M := hM (by simpa using ⟨ζ, hζ, rfl⟩)
  calc Real.exp (-M) ≤ Real.exp (Real.log ‖ζ‖) := Real.exp_le_exp.2 (by linarith)
    _ = ‖ζ‖ := Real.exp_log (norm_pos_iff.2 (hZ ζ hζ))

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.absX :
    ∀ (T : Type) (a : T → ℝ) (τ : T → ℕ → ℂ) (act good : T → Prop) (x : ℝ), 0 < x → x ≤ 1 → ∀ (p : ℕ), 0 < p → ∀ (d : ℕ → ℕ),
      Tendsto (fun j : ℕ => (d j : ℝ) / j) atTop (𝓝 0) → (∀ B : ℝ, ∀ᶠ j : ℕ in atTop, Real.exp (B * j) ≤ (d j).factorial) →
      (∀ i, act i → 0 < a i → ∃ (s : Finset ℂ) (c : ℂ → ℂ), 0 ∉ s ∧ ∀ᶠ j : ℕ in atTop, τ i j = ∑ ζ ∈ s, c ζ * ζ ^ j) →
      {i | act i ∧ a i = x}.Finite →
      (∀ N : ℝ, ∃ c₁ : ℝ, ∀ η : ℝ, 0 < η → η < x → ∃ (s : Finset T) (u : T → ℕ → ℂ) (u' : T → ℂ) (k : ℂ), k ≠ 0 ∧ (∀ i, i ∈ s ↔ η < a i ∧ act i) ∧
        (∀ i ∈ s, Tendsto (u i) atTop (𝓝 (u' i))) ∧ (∀ i ∈ s, good i → a i = x → u' i = k) ∧ (∀ i ∈ s, ¬ good i → u' i = 0) ∧
        ∀ s₀ : ℕ, ∃ K : ℝ, ∀ᶠ j : ℕ in atTop, ∀ m ≤ s₀, ∀ m' ≤ s₀,
          ‖∑ i ∈ s, u i (d j) * (a i : ℂ) ^ d j * (cheb η (j / p + m) (a i) : ℂ) * τ i (j + m')‖ ≤
            K ^ (d j + 1) * (Real.exp (c₁ * j) * (1 + (4 / η) ^ (j / p) / (d j).factorial) + (4 / η) ^ (j / p) * Real.exp (-N * j))) →
      ∀ᶠ j : ℕ in atTop, ∑ᶠ i ∈ {i | act i ∧ good i ∧ a i = x}, τ i j = 0 := by
  classical
  intro T a τ act good x hx hx1 p hp d hd hfac hexp hfin H
  choose! S c hS0 hτ using hexp
  obtain ⟨cq, hcq⟩ := low_bd (hfin.toFinset.biUnion S) (by
    intro ζ hζ h0
    obtain ⟨i, hi, hζ⟩ := Finset.mem_biUnion.1 hζ
    have hi' := hfin.mem_toFinset.1 hi
    exact hS0 i hi'.1 (hi'.2 ▸ hx) (h0 ▸ hζ))
  obtain ⟨N, hN⟩ := exponents3 d hd hfac p hp cq x hx hx1
  obtain ⟨c₁, H⟩ := H N
  obtain ⟨η, hη, hηx, hE⟩ := hN c₁
  obtain ⟨s, u, u', k, hk, hs, hu, hgood, hbad, hest⟩ := H η hη hηx
  have hsp : ∀ i ∈ s, act i ∧ 0 < a i := fun i hi => ⟨((hs i).1 hi).2, hη.trans ((hs i).1 hi).1⟩
  set P : Finset (ℝ × ℂ) := s.biUnion fun i => (S i).image fun ζ => (a i, ζ) with hPdef
  have hP : ∀ i ∈ s, ∀ ζ ∈ S i, (a i, ζ) ∈ P := fun i hi ζ hζ =>
    Finset.mem_biUnion.2 ⟨i, hi, Finset.mem_image.2 ⟨ζ, hζ, rfl⟩⟩
  have hP' : ∀ q ∈ P, ∃ i ∈ s, a i = q.1 ∧ q.2 ∈ S i := by
    intro q hq
    obtain ⟨i, hi, hq⟩ := Finset.mem_biUnion.1 hq
    obtain ⟨ζ, hζ, rfl⟩ := Finset.mem_image.1 hq
    exact ⟨i, hi, rfl, hζ⟩
  have hall : ∀ᶠ j : ℕ in atTop, ∀ i ∈ s, τ i j = ∑ ζ ∈ S i, c i ζ * ζ ^ j :=
    (Filter.eventually_all_finset s).2 fun i hi => hτ i (hsp i hi).1 (hsp i hi).2
  obtain ⟨J, hJ⟩ := eventually_atTop.1 hall
  let C : (T → ℂ) → ℝ × ℂ → ℂ := fun w q => ∑ i ∈ s, if a i = q.1 ∧ q.2 ∈ S i then w i * c i q.2 else 0
  have key := hE η hη le_rfl P (fun q => q.1.1) (fun q => q.1.2)
    (fun q => by
      obtain ⟨i, hi, h1, -⟩ := hP' q.1 q.2
      exact h1 ▸ ((hs i).1 hi).1)
    (fun q h0 => by
      obtain ⟨i, hi, -, h2⟩ := hP' q.1 q.2
      exact hS0 i (hsp i hi).1 (hsp i hi).2 (h0 ▸ h2))
    (fun q q' h => Subtype.ext h)
    (fun j q => C (fun i => u i (d j)) q.1) (fun q => C u' q.1)
    (fun q => by
      refine tendsto_finsetSum _ fun i hi => ?_
      split_ifs
      · exact ((hu i hi).comp (d_top d hfac)).mul_const _
      · exact tendsto_const_nhds)
    (fun s₀ => by
      obtain ⟨K, hK⟩ := hest s₀
      refine ⟨K, ?_⟩
      filter_upwards [hK, eventually_ge_atTop J] with j hj hjJ m hm m' hm'
      refine le_of_eq_of_le ?_ (hj m hm m' hm')
      congr 1
      have h1 := regroup s a S c (fun i => u i (d j)) P hP
        (fun q => (q.1 : ℂ) ^ d j * (cheb η (j / p + m) q.1 : ℂ) * q.2 ^ (j + m'))
      rw [← Finset.sum_coe_sort P] at h1
      refine Eq.trans (Finset.sum_congr rfl fun q _ => by simp only [C, mul_assoc]) (h1.trans ?_)
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hJ (j + m') (by omega) i hi, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun ζ _ => ?_
      ring)
  filter_upwards [hall] with j hj
  have h1 := regroup s a S c u' P hP (fun q => if q.1 = x then q.2 ^ j else 0)
  have h2 : ∑ q ∈ P, C u' q * (if q.1 = x then q.2 ^ j else 0) = 0 := by
    refine Finset.sum_eq_zero fun q hq => ?_
    split_ifs with hqx
    · obtain ⟨i, hi, h1, h2⟩ := hP' q hq
      have := key ⟨q, hq⟩ hqx.ge (hcq _ (Finset.mem_biUnion.2
        ⟨i, hfin.mem_toFinset.2 ⟨(hsp i hi).1, h1.trans hqx⟩, h2⟩))
      rw [this, zero_mul]
    · exact mul_zero _
  have h3 : k * ∑ i ∈ s.filter (fun i => good i ∧ a i = x), τ i j = 0 := by
    rw [← h2]
    refine Eq.trans ?_ h1.symm
    rw [Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i hi => ?_
    by_cases hg : good i
    · by_cases ha : a i = x
      · simp only [hg, ha, and_self, if_true, hgood i hi hg ha, hj i hi]
      · simp [ha]
    · simp [hg, hbad i hi hg]
  have h4 : {i | act i ∧ good i ∧ a i = x} = ↑(s.filter (fun i => good i ∧ a i = x)) := by
    ext i
    simp only [Set.mem_setOf_eq, Finset.coe_filter]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨(hs i).2 ⟨h3 ▸ hηx, h1⟩, h2, h3⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(hsp i h1).1, h2⟩
  show ∑ᶠ i ∈ {i | act i ∧ good i ∧ a i = x}, τ i j = 0
  rw [h4, finsum_mem_coe_finset]
  exact (mul_eq_zero.1 h3).resolve_left hk
end
end
