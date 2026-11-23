module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.RnStmt
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Topology.Sheaves.Presheaf
import GroundTheory.AutomorphicForms.AdelicGLn
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Archimedean
import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing

-- Source module: GroundTheory.AutomorphicForms.GL2Classical.CuspConverse

section

@[expose] public section

open NumberField IsDedekindDomain Matrix MeasureTheory Set Filter Topology CongruenceSubgroup
open UpperHalfPlane hiding I I_re I_im
open scoped NumberField.AdeleRing MatrixGroups ModularForm Manifold

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm GroundTheory.Global ModularForm

theorem continuous_vadd_upperHalfPlane (z : ℍ) : Continuous fun t : ℝ => t +ᵥ z := by
  refine UpperHalfPlane.isOpenEmbedding_coe.isEmbedding.continuous_iff.2 ?_
  have : ((↑) ∘ fun t : ℝ => t +ᵥ z) = fun t : ℝ => (t : ℂ) + (z : ℂ) := by
    funext t
    simp only [Function.comp_apply, coe_vadd]
  rw [this]
  fun_prop

theorem periodic_comp_ofComplex_of_vadd {F : ℍ → ℂ} {M : ℝ} (hper : ∀ z : ℍ, F (M +ᵥ z) = F z) :
    Function.Periodic (F ∘ ofComplex) M := by
  intro w
  by_cases hw : 0 < w.im
  · have hw' : 0 < (w + M).im := by simpa using hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw', ofComplex_apply_of_im_pos hw]
    rw [← hper ⟨w, hw⟩]
    congr 1
    ext
    simp [coe_vadd, add_comm]
  · push Not at hw
    have hw' : (w + M).im ≤ 0 := by simpa using hw
    simp [ofComplex_apply_of_im_nonpos hw', ofComplex_apply_of_im_nonpos hw]

theorem tendsto_atImInfty_of_periodic_of_mdifferentiable {F : ℍ → ℂ} {M : ℝ} (hM : 0 < M)
    (hper : ∀ z : ℍ, F (M +ᵥ z) = F z) (hhol : MDiff F) (hbdd : IsBoundedAtImInfty F) :
    Tendsto F atImInfty (𝓝 (cuspFunction M F 0)) := by
  have hfper := periodic_comp_ofComplex_of_vadd hper
  have han := analyticAt_cuspFunction_zero hM hfper hhol hbdd
  have e : (cuspFunction M F ∘ fun τ : ℍ => Function.Periodic.qParam M τ) = F := by
    funext τ
    simpa using eq_cuspFunction τ hM.ne' hfper
  simpa [e] using han.continuousAt.tendsto.comp (qParam_tendsto_atImInfty hM)

theorem isZeroAtImInfty_of_integral_vadd_eq_zero {F : ℍ → ℂ} {M : ℝ} (hM : 0 < M)
    (hper : ∀ z : ℍ, F (M +ᵥ z) = F z) (hhol : MDiff F) (hbdd : IsBoundedAtImInfty F)
    (hint : ∀ z : ℍ, ∫ t in (0 : ℝ)..M, F (t +ᵥ z) = 0) : IsZeroAtImInfty F := by
  set c := cuspFunction M F 0
  have ht := tendsto_atImInfty_of_periodic_of_mdifferentiable hM hper hhol hbdd
  suffices hc : c = 0 by
    rw [IsZeroAtImInfty, ZeroAtFilter, ← hc]
    exact ht
  refine norm_le_zero_iff.1 (le_of_forall_pos_le_add fun ε hε => ?_)
  rw [zero_add]
  obtain ⟨A, hA⟩ := (atImInfty_mem _).1 (ht.eventually (Metric.closedBall_mem_nhds c hε))
  have hY : 0 < max A 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  set z₀ : ℍ := ⟨(max A 1 : ℝ) * Complex.I, by simp [hY]⟩
  have hbound : ∀ t : ℝ, ‖F (t +ᵥ z₀) - c‖ ≤ ε := by
    intro t
    have hz : A ≤ (t +ᵥ z₀).im := by
      rw [vadd_im]
      show A ≤ ((max A 1 : ℝ) * Complex.I).im
      simp
    have := hA _ hz
    simpa [Metric.mem_closedBall, dist_eq_norm] using this
  have hcont : Continuous fun t : ℝ => F (t +ᵥ z₀) :=
    hhol.continuous.comp (continuous_vadd_upperHalfPlane z₀)
  have hint' : ∫ t in (0 : ℝ)..M, (F (t +ᵥ z₀) - c) = -(M • c) := by
    rw [intervalIntegral.integral_sub (hcont.intervalIntegrable _ _) intervalIntegrable_const, hint z₀,
      intervalIntegral.integral_const, sub_zero, zero_sub]
  have hle : ‖∫ t in (0 : ℝ)..M, (F (t +ᵥ z₀) - c)‖ ≤ ε * |M - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun t _ => hbound t
  rw [hint', norm_neg, norm_smul, Real.norm_eq_abs, sub_zero, abs_of_pos hM] at hle
  exact le_of_mul_le_mul_left (by linarith [hle] : M * ‖c‖ ≤ M * ε) hM

variable {N : ℕ} [NeZero N] {k : ℤ}

end GL2Classical

end

end GroundTheory.Automorphic
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.PerZero

section

@[expose] public section

open Filter Topology Asymptotics Function
open scoped Real

private theorem UpperTheory.V.Br.per_tendsto {g : ℂ → ℂ} {h : ℝ} (hh : 0 < h) (hp : Periodic g h)
    (hd : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ g z) (C : ℝ) (m : ℕ)
    (hb : ∀ z : ℂ, 1 ≤ z.im → |z.re| ≤ h → ‖g z‖ ≤ C * z.im ^ m) :
    ∃ c, Tendsto g (comap Complex.im atTop) (𝓝 c) := by
  have hb' : ∀ z : ℂ, 1 ≤ z.im → ‖g z‖ ≤ C * z.im ^ m := by
    intro z hz
    have h1 := hp.sub_int_mul_eq (x := z) ⌊z.re / h⌋
    have h2 := Int.sub_floor_div_mul_nonneg z.re hh
    have h3 := Int.sub_floor_div_mul_lt z.re hh
    have h4 := hb (z - (⌊z.re / h⌋ : ℤ) * (h : ℂ)) (by simpa using hz)
      (by simp only [Complex.sub_re, Complex.mul_re, Complex.intCast_re, Complex.ofReal_re,
            Complex.intCast_im, Complex.ofReal_im, mul_zero, sub_zero]
          rw [abs_of_nonneg h2]; exact h3.le)
    rw [h1] at h4
    simpa using h4
  have hev : ∀ A : ℝ, ∀ᶠ z : ℂ in comap Complex.im atTop, A ≤ z.im := fun A =>
    tendsto_comap.eventually (eventually_ge_atTop A)
  have hD := Periodic.eventually_differentiableAt_cuspFunction_nhds_ne_zero hh hp
    ((hev 1).mono fun z hz => hd z (by linarith))
  have hO : Periodic.cuspFunction h g =O[𝓝[≠] 0] fun q : ℂ => |Real.log ‖q‖| ^ (m : ℝ) := by
    refine IsBigO.of_bound (|C| * (h / (2 * π)) ^ m) ?_
    filter_upwards [(Periodic.invQParam_tendsto hh).eventually (hev 1), self_mem_nhdsWithin] with q hq hq0
    rw [Periodic.cuspFunction_eq_of_nonzero h g hq0]
    refine (hb' _ hq).trans ((le_abs_self _).trans (le_of_eq ?_))
    have : 0 < h / (2 * π) := by positivity
    rw [Periodic.im_invQParam, abs_mul, abs_pow, abs_mul, neg_div, abs_neg, abs_of_pos this,
      Real.rpow_natCast, Real.norm_eq_abs, abs_pow, abs_abs, mul_pow, mul_assoc]
  have ho : (fun q : ℂ => |Real.log ‖q‖| ^ (m : ℝ)) =o[𝓝[≠] 0] fun q : ℂ => (q - 0)⁻¹ := by
    have := (isLittleO_abs_log_rpow_rpow_nhdsGT_zero (m : ℝ) (s := -1) (by norm_num)).comp_tendsto
      (tendsto_norm_nhdsNE_zero (E := ℂ))
    refine IsLittleO.of_norm_right ?_
    simpa [Function.comp_def, Real.rpow_neg_one] using this
  have hc : (fun _ : ℂ => Periodic.cuspFunction h g 0) =o[𝓝[≠] 0] fun q : ℂ => (q - 0)⁻¹ := by
    refine isLittleO_const_left.2 (Or.inr ?_)
    simpa [Function.comp_def] using (tendsto_inv_nhdsGT_zero.comp (tendsto_norm_nhdsNE_zero (E := ℂ)))
  have hT := Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_isLittleO hD
    ((hO.trans_isLittleO ho).sub hc)
  exact ⟨_, by
    simpa only [Function.comp_def, Periodic.eq_cuspFunction hh.ne' hp] using
      hT.comp (Periodic.qParam_tendsto hh)⟩

theorem UpperTheory.V.Br.perZero :
    UpperTheory.V.Br.PerZero := by
  intro f N hN hf hper ⟨C, m, hb⟩ hint
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  refine GroundTheory.Automorphic.GL2Classical.isZeroAtImInfty_of_integral_vadd_eq_zero hN' hper hf ?_ hint
  obtain ⟨c, hc⟩ := UpperTheory.V.Br.per_tendsto hN'
    (GroundTheory.Automorphic.GL2Classical.periodic_comp_ofComplex_of_vadd hper)
    (fun z hz => (UpperHalfPlane.mdifferentiable_iff.1 hf).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz)) C m
    (fun z hz hr => by
      have h0 : 0 < z.im := by linarith
      have := hb ⟨z, h0⟩ hz hr
      simpa [UpperHalfPlane.ofComplex_apply_of_im_pos h0] using this)
  have h2 : Tendsto f UpperHalfPlane.atImInfty (𝓝 c) := by
    have := hc.comp (show Tendsto ((↑) : UpperHalfPlane → ℂ) UpperHalfPlane.atImInfty
      (comap Complex.im atTop) from tendsto_comap_iff.2 tendsto_comap)
    simpa [Function.comp_def] using this
  exact h2.isBigO_one ℝ
end
end
