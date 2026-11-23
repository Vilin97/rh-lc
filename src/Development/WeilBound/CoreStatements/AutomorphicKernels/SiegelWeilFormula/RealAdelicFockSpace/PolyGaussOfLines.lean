module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.PolynomialGaussianIntegrals.PolyGaussOfLines

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.PolynomialGaussianIntegrals.IntegrableRexpLin

section

@[expose] public section

noncomputable section

open scoped SchwartzMap InnerProductSpace
open MeasureTheory Complex

namespace PositivityTheory.SiegelWeilFormula.KFPB

section

variable {ι : Type} [Fintype ι]

theorem integrable_rexp_lin (c : ℝ) (hc : 0 < c) (a : ℝ) (ξ : EuclideanSpace ℝ ι) :
    Integrable (fun u : EuclideanSpace ℝ ι => Real.exp (-(c * ‖u‖ ^ 2) + a * ⟪ξ, u⟫_ℝ)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := EuclideanSpace ℝ ι)
    (b := (c : ℂ)) (by simpa using hc) (a : ℂ) ξ).norm
  refine h.congr (Filter.Eventually.of_forall fun u => ?_)
  simp only [Complex.norm_exp]
  congr 1
  simp
  left
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

theorem abs_le_exp_abs (x : ℝ) : |x| ≤ Real.exp |x| := by
  have := Real.add_one_le_exp |x|
  linarith

theorem exp_abs_le (a s : ℝ) : Real.exp (a * |s|) ≤ Real.exp (a * s) + Real.exp (-(a * s)) := by
  rcases abs_cases s with ⟨h, -⟩ | ⟨h, -⟩
  · rw [h]; have := Real.exp_pos (-(a * s)); linarith
  · rw [h]; have := Real.exp_pos (a * s); rw [show a * -s = -(a * s) by ring]; linarith

end

theorem entire_laplace {ι : Type} [Fintype ι] (c : ℝ) (hc : 0 < c) (h : 𝓢(EuclideanSpace ℝ ι, ℂ))
    (ξ : EuclideanSpace ℝ ι) :
    Differentiable ℂ (fun z : ℂ => ∫ u, h u * Real.exp (-(c * ‖u‖ ^ 2)) * Complex.exp (z * ⟪ξ, u⟫_ℝ)) := by
  intro z₀
  set C : ℝ := SchwartzMap.seminorm ℝ 0 0 h with hC
  have hCb : ∀ u, ‖h u‖ ≤ C := fun u => SchwartzMap.norm_le_seminorm ℝ h u
  set a : ℝ := ‖z₀‖ + 2 with ha
  let bound : EuclideanSpace ℝ ι → ℝ := fun u =>
    C * (Real.exp (-(c * ‖u‖ ^ 2) + a * ⟪ξ, u⟫_ℝ) + Real.exp (-(c * ‖u‖ ^ 2) + (-a) * ⟪ξ, u⟫_ℝ))
  have hbound : Integrable bound :=
    ((integrable_rexp_lin c hc a ξ).add (integrable_rexp_lin c hc (-a) ξ)).const_mul C

  have hest : ∀ u (z : ℂ), ‖z‖ ≤ ‖z₀‖ + 1 →
      ‖h u‖ * Real.exp (-(c * ‖u‖ ^ 2)) * (|⟪ξ, u⟫_ℝ| * Real.exp (‖z‖ * |⟪ξ, u⟫_ℝ|)) ≤ bound u := by
    intro u z hz
    set s := ⟪ξ, u⟫_ℝ
    have h1 : |s| * Real.exp (‖z‖ * |s|) ≤ Real.exp (a * |s|) := by
      calc |s| * Real.exp (‖z‖ * |s|) ≤ Real.exp |s| * Real.exp ((‖z₀‖ + 1) * |s|) := by
            gcongr
            · exact abs_le_exp_abs s
          _ = Real.exp (a * |s|) := by rw [← Real.exp_add, ha]; ring_nf
    have h2 := exp_abs_le a s
    have hE : 0 ≤ Real.exp (-(c * ‖u‖ ^ 2)) := (Real.exp_pos _).le
    calc ‖h u‖ * Real.exp (-(c * ‖u‖ ^ 2)) * (|s| * Real.exp (‖z‖ * |s|))
        ≤ C * Real.exp (-(c * ‖u‖ ^ 2)) * (Real.exp (a * s) + Real.exp (-(a * s))) := by
          gcongr
          · exact hCb u
          · exact h1.trans h2
      _ = bound u := by
          simp only [bound, Real.exp_add]
          rw [show (-a) * s = -(a * s) by ring]
          ring
  have hnormF' : ∀ u (z : ℂ), ‖h u * (Real.exp (-(c * ‖u‖ ^ 2)) : ℂ) * (((⟪ξ, u⟫_ℝ : ℝ) : ℂ) *
      Complex.exp (z * ⟪ξ, u⟫_ℝ))‖ ≤ ‖h u‖ * Real.exp (-(c * ‖u‖ ^ 2)) * (|⟪ξ, u⟫_ℝ| * Real.exp (‖z‖ * |⟪ξ, u⟫_ℝ|)) := by
    intro u z
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), Complex.norm_exp]
    gcongr
    calc (z * ((⟪ξ, u⟫_ℝ : ℝ) : ℂ)).re = z.re * ⟪ξ, u⟫_ℝ := by simp
      _ ≤ |z.re * ⟪ξ, u⟫_ℝ| := le_abs_self _
      _ = |z.re| * |⟪ξ, u⟫_ℝ| := abs_mul _ _
      _ ≤ ‖z‖ * |⟪ξ, u⟫_ℝ| := by gcongr; exact Complex.abs_re_le_norm z
  have hnormF : ∀ u, ‖h u * (Real.exp (-(c * ‖u‖ ^ 2)) : ℂ) * Complex.exp (z₀ * ⟪ξ, u⟫_ℝ)‖ ≤ bound u := by
    intro u
    set s := ⟪ξ, u⟫_ℝ
    have e1 : ‖h u * (Real.exp (-(c * ‖u‖ ^ 2)) : ℂ) * Complex.exp (z₀ * s)‖ ≤
        ‖h u‖ * Real.exp (-(c * ‖u‖ ^ 2)) * Real.exp (‖z₀‖ * |s|) := by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Complex.norm_exp]
      gcongr
      calc (z₀ * ((s : ℝ) : ℂ)).re = z₀.re * s := by simp
        _ ≤ |z₀.re * s| := le_abs_self _
        _ = |z₀.re| * |s| := abs_mul _ _
        _ ≤ ‖z₀‖ * |s| := by gcongr; exact Complex.abs_re_le_norm z₀
    refine e1.trans ?_
    have hE : 0 ≤ Real.exp (-(c * ‖u‖ ^ 2)) := (Real.exp_pos _).le
    have h3 : Real.exp (‖z₀‖ * |s|) ≤ Real.exp (a * s) + Real.exp (-(a * s)) :=
      (Real.exp_le_exp.2 (by gcongr; rw [ha]; linarith)).trans (exp_abs_le a s)
    calc ‖h u‖ * Real.exp (-(c * ‖u‖ ^ 2)) * Real.exp (‖z₀‖ * |s|)
        ≤ C * Real.exp (-(c * ‖u‖ ^ 2)) * (Real.exp (a * s) + Real.exp (-(a * s))) := by
          gcongr
          exact hCb u
      _ = bound u := by
          simp only [bound, Real.exp_add]
          rw [show (-a) * s = -(a * s) by ring]
          ring
  have hcont : ∀ z : ℂ, Continuous (fun u : EuclideanSpace ℝ ι =>
      h u * (Real.exp (-(c * ‖u‖ ^ 2)) : ℂ) * Complex.exp (z * ⟪ξ, u⟫_ℝ)) := by
    intro z
    have : Continuous (fun u : EuclideanSpace ℝ ι => ⟪ξ, u⟫_ℝ) := continuous_const.inner continuous_id
    fun_prop
  have hcont' : Continuous (fun u : EuclideanSpace ℝ ι =>
      h u * (Real.exp (-(c * ‖u‖ ^ 2)) : ℂ) * (((⟪ξ, u⟫_ℝ : ℝ) : ℂ) * Complex.exp (z₀ * ⟪ξ, u⟫_ℝ))) := by
    have : Continuous (fun u : EuclideanSpace ℝ ι => ⟪ξ, u⟫_ℝ) := continuous_const.inner continuous_id
    fun_prop
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun (z : ℂ) (u : EuclideanSpace ℝ ι) => h u * (Real.exp (-(c * ‖u‖ ^ 2)) : ℂ) * Complex.exp (z * ⟪ξ, u⟫_ℝ))
    (F' := fun (z : ℂ) (u : EuclideanSpace ℝ ι) =>
      h u * (Real.exp (-(c * ‖u‖ ^ 2)) : ℂ) * (((⟪ξ, u⟫_ℝ : ℝ) : ℂ) * Complex.exp (z * ⟪ξ, u⟫_ℝ)))
    (x₀ := z₀) (bound := bound) (Metric.ball_mem_nhds z₀ one_pos)
    (Filter.Eventually.of_forall fun z => (hcont z).aestronglyMeasurable)
    (hbound.mono' (hcont z₀).aestronglyMeasurable (Filter.Eventually.of_forall hnormF))
    hcont'.aestronglyMeasurable
    (Filter.Eventually.of_forall fun u z hz => (hnormF' u z).trans (hest u z (by
      have := Metric.mem_ball.1 hz
      have h1 : ‖z‖ ≤ ‖z - z₀‖ + ‖z₀‖ := by
        calc ‖z‖ = ‖(z - z₀) + z₀‖ := by ring_nf
          _ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_add_le _ _
      rw [dist_eq_norm] at this
      linarith)))
    hbound
    (Filter.Eventually.of_forall fun u z _ => by
      have hd : HasDerivAt (fun z : ℂ => Complex.exp (z * ⟪ξ, u⟫_ℝ))
          (Complex.exp (z * ⟪ξ, u⟫_ℝ) * (1 * ((⟪ξ, u⟫_ℝ : ℝ) : ℂ))) z :=
        ((hasDerivAt_id z).mul_const _).cexp
      refine (hd.const_mul (h u * (Real.exp (-(c * ‖u‖ ^ 2)) : ℂ))).congr_deriv ?_
      ring)
  exact key.2.differentiableAt

end PositivityTheory.SiegelWeilFormula.KFPB

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.PolynomialGaussianIntegrals.IteratedDerivScale

section

@[expose] public section

noncomputable section

open scoped Nat

namespace PositivityTheory.SiegelWeilFormula.KFPB

theorem iteratedDeriv_scale (E : ℂ → ℂ) (hE : Differentiable ℂ E) (c : ℂ) (j : ℕ) :
    iteratedDeriv j (fun z => E (c * z)) 0 = c ^ j * iteratedDeriv j E 0 := by
  rw [iteratedDeriv_comp_const_mul hE.contDiff c]
  simp only [mul_zero]

theorem iteratedDeriv_rel (q : Polynomial ℂ) (μ ω : ℂ) (E : ℂ → ℂ) (hE : Differentiable ℂ E) (j : ℕ) :
    iteratedDeriv j (fun z => ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * μ ^ i * E (ω ^ i * z)) 0 =
      q.eval (μ * ω ^ j) * iteratedDeriv j E 0 := by
  have hcomp : ∀ i : ℕ, Differentiable ℂ (fun z => E (ω ^ i * z)) := fun i => by fun_prop
  have hterm : ∀ i ∈ Finset.range (q.natDegree + 1),
      ContDiffAt ℂ (j : WithTop ℕ∞) (fun z => q.coeff i * μ ^ i * E (ω ^ i * z)) 0 := fun i _ =>
    ((hcomp i).const_mul (q.coeff i * μ ^ i)).contDiff.contDiffAt
  rw [iteratedDeriv_fun_sum hterm, Polynomial.eval_eq_sum_range, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedDeriv_const_mul _ (hcomp i).contDiff.contDiffAt,
    PositivityTheory.SiegelWeilFormula.KFPB.iteratedDeriv_scale E hE, mul_pow, ← pow_mul, ← pow_mul, mul_comm i j]
  ring

theorem poly_of_rot (q : Polynomial ℂ) (hq : q ≠ 0) (μ ω : ℂ) (hμ : μ ≠ 0) (hω0 : ω ≠ 0)
    (hω : ∀ j : ℕ, 0 < j → ω ^ j ≠ 1) :
    ∃ N : ℕ, ∀ E : ℂ → ℂ, Differentiable ℂ E →
      (∀ z, ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * μ ^ i * E (ω ^ i * z) = 0) →
      ∃ p : Polynomial ℂ, p.natDegree ≤ N ∧ ∀ z, E z = p.eval z := by
  have hlt : ∀ a b : ℕ, a < b → ω ^ a ≠ ω ^ b := by
    intro a b h hab
    apply hω (b - a) (Nat.sub_pos_of_lt h)
    apply mul_left_cancel₀ (pow_ne_zero a hω0)
    rw [← pow_add, Nat.add_sub_cancel' h.le, mul_one, hab]
  have hinj : Function.Injective fun j : ℕ => μ * ω ^ j := by
    intro a b hab
    have hab' : ω ^ a = ω ^ b := mul_left_cancel₀ hμ hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hlt a b h hab'
    · exact hlt b a h hab'.symm
  have hfin : {j : ℕ | q.eval (μ * ω ^ j) = 0}.Finite := by
    apply Set.Finite.of_finite_image _ hinj.injOn
    apply (q.roots.toFinset.finite_toSet).subset
    rintro _ ⟨j, hj, rfl⟩
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    exact (Polynomial.mem_roots hq).2 hj
  obtain ⟨N, hN⟩ := hfin.bddAbove
  refine ⟨N, fun E hE hrel => ?_⟩
  have hvan : ∀ j, N < j → iteratedDeriv j E 0 = 0 := by
    intro j hj
    have h0 : (fun z => ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * μ ^ i * E (ω ^ i * z)) = 0 :=
      funext hrel
    have h1 := PositivityTheory.SiegelWeilFormula.KFPB.iteratedDeriv_rel q μ ω E hE j
    rw [h0, iteratedDeriv_const_zero] at h1
    rcases mul_eq_zero.1 h1.symm with h | h
    · exact absurd (hN h) (not_le.2 hj)
    · exact h
  refine ⟨∑ n ∈ Finset.range (N + 1),
      Polynomial.C ((n ! : ℂ)⁻¹ * iteratedDeriv n E 0) * Polynomial.X ^ n, ?_, fun z => ?_⟩
  · exact Polynomial.natDegree_sum_le_of_forall_le _ _ fun n hn =>
      (Polynomial.natDegree_C_mul_X_pow_le _ n).trans (Nat.lt_succ_iff.1 (Finset.mem_range.1 hn))
  · have hs := Complex.hasSum_taylorSeries_of_entire hE 0 z
    refine (hs.unique (hasSum_sum_of_ne_finset_zero (s := Finset.range (N + 1)) ?_)).trans ?_
    · intro m hm
      simp only [Finset.mem_range, not_lt] at hm
      simp [hvan m (by omega)]
    · rw [Polynomial.eval_finsetSum]
      refine Finset.sum_congr rfl fun m _ => ?_
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
        smul_eq_mul, sub_zero]
      ring

end PositivityTheory.SiegelWeilFormula.KFPB

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.PolyGaussOfLines

section

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace

namespace PositivityTheory.SiegelWeilFormula.KFP

theorem poly_of_rot (q : Polynomial ℂ) (hq : q ≠ 0) (μ ω : ℂ) (hμ : μ ≠ 0) (hω0 : ω ≠ 0)
    (hω : ∀ j : ℕ, 0 < j → ω ^ j ≠ 1) :
    ∃ N : ℕ, ∀ E : ℂ → ℂ, Differentiable ℂ E →
      (∀ z, ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * μ ^ i * E (ω ^ i * z) = 0) →
      ∃ p : Polynomial ℂ, p.natDegree ≤ N ∧ ∀ z, E z = p.eval z := by
  exact KFPB.poly_of_rot q hq μ ω hμ hω0 hω

theorem poly_gauss_of_lines {ι : Type} [Fintype ι] (c : ℝ) (hc : 0 < c) (N : ℕ) (h : 𝓢(EuclideanSpace ℝ ι, ℂ))
    (H : ∀ ξ : EuclideanSpace ℝ ι, ∃ p : Polynomial ℂ, p.natDegree ≤ N ∧ ∀ z : ℂ,
      ∫ u, h u * Real.exp (-(c * ‖u‖ ^ 2)) * Complex.exp (z * ⟪ξ, u⟫_ℝ) =
        Complex.exp (z ^ 2 * ‖ξ‖ ^ 2 / (8 * c)) * p.eval z) :
    ∃ P : MvPolynomial ι ℂ, P.totalDegree ≤ N ∧
      ∀ u, h u = MvPolynomial.eval (fun i => ((u i : ℝ) : ℂ)) P * Real.exp (-(c * ‖u‖ ^ 2)) := by
  exact KFPB.poly_gauss_of_lines c hc N h H

theorem entire_laplace {ι : Type} [Fintype ι] (c : ℝ) (hc : 0 < c) (h : 𝓢(EuclideanSpace ℝ ι, ℂ))
    (ξ : EuclideanSpace ℝ ι) :
    Differentiable ℂ (fun z : ℂ => ∫ u, h u * Real.exp (-(c * ‖u‖ ^ 2)) * Complex.exp (z * ⟪ξ, u⟫_ℝ)) := by
  exact KFPB.entire_laplace c hc h ξ

end PositivityTheory.SiegelWeilFormula.KFP

end
end
end
