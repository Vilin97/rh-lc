module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.TriDens
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.VolUFactProdMulLe
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.GaussA
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.CategoryTheory.Countable
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.RingTheory.WittVector.IsPoly
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.GaussB

section

@[expose] public section

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

theorem gaussC_mat :
    ∫⁻ Z : Fin N → Fin N → ℂ, ENNReal.ofReal (Real.exp (-hs (Matrix.of Z))) =
      ENNReal.ofReal (Real.pi ^ (N ^ 2)) := by
  have hpt : ∀ Z : Fin N → Fin N → ℂ, ENNReal.ofReal (Real.exp (-hs (Matrix.of Z))) =
      ENNReal.ofReal (∏ i, (fun (_ : Fin N) (row : Fin N → ℂ) => ∏ j, Real.exp (-‖row j‖ ^ 2)) i (Z i)) := by
    intro Z
    congr 1
    simp only [hs, Matrix.of_apply, ← Real.exp_sum, ← Finset.sum_neg_distrib]
  have hrow : Integrable (fun row : Fin N → ℂ => ∏ j, Real.exp (-‖row j‖ ^ 2)) :=
    Integrable.fintype_prod (fun _ => gaussA_cint)
  have hrowi : ∫ row : Fin N → ℂ, ∏ j, Real.exp (-‖row j‖ ^ 2) = Real.pi ^ N := by
    rw [integral_fintype_prod_volume_eq_prod (fun (_ : Fin N) (z : ℂ) => Real.exp (-‖z‖ ^ 2))]
    simp only [gaussA_cintegral, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp_rw [hpt]
  rw [show (volume : Measure (Fin N → Fin N → ℂ)) = Measure.pi (fun _ => volume) from rfl,
    gaussA_lint_pi_ofReal _ (fun _ => hrow)
      (fun _ _ => Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le)]
  simp only [hrowi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (pow_nonneg Real.pi_pos.le _), ← pow_mul, sq]

theorem gaussC_hs_upMat (t : TriCo N) :
    hs (upMat t) = ∑ j, t.1 j ^ 2 + ∑ ab : {ab : Fin N × Fin N // ab.1 < ab.2}, ‖t.2 ab‖ ^ 2 := by
  have hp : ∀ a b : Fin N, ‖upMat t a b‖ ^ 2 = (if a = b then t.1 a ^ 2 else 0) +
      (if h : a < b then ‖t.2 ⟨(a, b), h⟩‖ ^ 2 else 0) := by
    intro a b
    unfold upMat
    by_cases hab : a = b
    · subst hab; simp [Complex.norm_real, sq_abs]
    · by_cases h : a < b
      · simp [hab, h]
      · simp [hab, h]
  unfold hs
  simp_rw [hp, Finset.sum_add_distrib]
  congr 1
  · simp [Finset.sum_ite_eq]
  · rw [← Finset.sum_product' (f := fun a b => if h : a < b then ‖t.2 ⟨(a, b), h⟩‖ ^ 2 else 0),
      Finset.univ_product_univ,
      ← (Equiv.sumCompl (fun p : Fin N × Fin N => p.1 < p.2)).sum_comp, Fintype.sum_sum_type]
    have h1 : ∀ a : {p : Fin N × Fin N // p.1 < p.2},
        (fun p : Fin N × Fin N => if h : p.1 < p.2 then ‖t.2 ⟨(p.1, p.2), h⟩‖ ^ 2 else 0)
          ((Equiv.sumCompl (fun p : Fin N × Fin N => p.1 < p.2)) (Sum.inl a)) = ‖t.2 a‖ ^ 2 := by
      intro a; obtain ⟨⟨x, y⟩, h⟩ := a; simp [h]
    have h2 : ∀ b : {p : Fin N × Fin N // ¬ p.1 < p.2},
        (fun p : Fin N × Fin N => if h : p.1 < p.2 then ‖t.2 ⟨(p.1, p.2), h⟩‖ ^ 2 else 0)
          ((Equiv.sumCompl (fun p : Fin N × Fin N => p.1 < p.2)) (Sum.inr b)) = 0 := by
      intro b; obtain ⟨⟨x, y⟩, h⟩ := b; simp [h]
    simp only [h1, h2, Finset.sum_const_zero, add_zero]

def gaussRadW (N : ℕ) (j : Fin N) (r : ℝ) : ℝ := Real.exp (-r ^ 2) * |r| ^ (2 * (N - 1 - (j : ℕ)) + 1)

theorem gaussD_integrand (t : TriCo N) (ht : t ∈ triPos N) :
    ENNReal.ofReal (Real.exp (-hs (upMat t))) * ENNReal.ofReal (qrWt t) =
      ENNReal.ofReal (∏ j, gaussRadW N j (t.1 j)) *
        ENNReal.ofReal (∏ ab : {ab : Fin N × Fin N // ab.1 < ab.2}, Real.exp (-‖t.2 ab‖ ^ 2)) := by
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← ENNReal.ofReal_mul' (Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le)]
  congr 1
  rw [gaussC_hs_upMat, neg_add, Real.exp_add, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib,
    Real.exp_sum, Real.exp_sum]
  have hw : ∀ j : Fin N, t.1 j ^ (2 * (N - (j : ℕ)) - 1) = |t.1 j| ^ (2 * (N - 1 - (j : ℕ)) + 1) := by
    intro j
    rw [abs_of_pos (ht j)]
    congr 1
    have := j.2
    omega
  unfold qrWt gaussRadW
  simp_rw [hw, Finset.prod_mul_distrib]
  ring

theorem gaussD_triPos_eq : triPos N = (Set.univ.pi fun _ : Fin N => Set.Ioi (0:ℝ)) ×ˢ Set.univ := by
  ext t
  simp [triPos]

theorem gaussD_tri :
    ∫⁻ t in triPos N, ENNReal.ofReal (Real.exp (-hs (upMat t))) * ENNReal.ofReal (qrWt t) =
      ENNReal.ofReal (Real.pi ^ (N * (N - 1) / 2) * (∏ i ∈ range N, (i.factorial : ℝ)) / 2 ^ N) := by
  have hms : MeasurableSet (triPos N) := by
    rw [gaussD_triPos_eq]
    exact (MeasurableSet.univ_pi fun _ => measurableSet_Ioi).prod MeasurableSet.univ
  rw [setLIntegral_congr_fun hms (fun t ht => gaussD_integrand t ht), gaussD_triPos_eq,
    show (volume : Measure (TriCo N)) = (volume : Measure (Fin N → ℝ)).prod
      (volume : Measure ({ab : Fin N × Fin N // ab.1 < ab.2} → ℂ)) from rfl,
    ← Measure.prod_restrict, Measure.restrict_univ,
    show (volume : Measure (Fin N → ℝ)) = Measure.pi (fun _ => volume) from rfl,
    Measure.restrict_pi_pi]
  rw [lintegral_prod_mul (f := fun x : Fin N → ℝ => ENNReal.ofReal (∏ j, gaussRadW N j (x j)))
    (g := fun y : {ab : Fin N × Fin N // ab.1 < ab.2} → ℂ =>
      ENNReal.ofReal (∏ ab, Real.exp (-‖y ab‖ ^ 2)))
    (by unfold gaussRadW; fun_prop)
    (ENNReal.measurable_ofReal.comp (by fun_prop : Continuous fun y : {ab : Fin N × Fin N // ab.1 < ab.2} → ℂ =>
      ∏ ab, Real.exp (-‖y ab‖ ^ 2)).measurable).aemeasurable]
  rw [gaussA_lint_pi_ofReal (fun j => gaussRadW N j) (fun j => gaussA_rad_int _)
      (fun j r => mul_nonneg (Real.exp_pos _).le (pow_nonneg (abs_nonneg _) _)),
    show (volume : Measure ({ab : Fin N × Fin N // ab.1 < ab.2} → ℂ)) = Measure.pi (fun _ => volume) from rfl,
    gaussA_lint_pi_ofReal (fun (_ : {ab : Fin N × Fin N // ab.1 < ab.2}) (z : ℂ) => Real.exp (-‖z‖ ^ 2))
      (fun _ => gaussA_cint) (fun _ _ => (Real.exp_pos _).le)]
  simp only [gaussRadW, gaussA_rad, gaussA_cintegral, Finset.prod_const, Finset.card_univ, gaussB_card_lt]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => by positivity),
    ← ENNReal.ofReal_pow Real.pi_pos.le, ← ENNReal.ofReal_mul (Finset.prod_nonneg fun _ _ => by positivity),
    gaussB_prod_fact]
  congr 1
  ring

end ReciprocityTheory.ChartRestriction.DS
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.LintegralGaussTri

section

@[expose] public section

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

theorem gaussE_pow_odd (n : ℕ) : (∏ i ∈ range n, Real.pi ^ (2 * i + 1)) = Real.pi ^ (n ^ 2) := by
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    ring

theorem gaussE_volU_mul :
    volU N * (Real.pi ^ (N * (N - 1) / 2) * (∏ i ∈ range N, (i.factorial : ℝ)) / 2 ^ N) =
      Real.pi ^ (N ^ 2) := by
  have hX : Real.pi ^ (N * (N - 1) / 2) * (∏ i ∈ range N, (i.factorial : ℝ)) / 2 ^ N =
      ∏ i ∈ range N, (Real.pi ^ i * (i.factorial : ℝ) / 2) := by
    rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
      Finset.sum_range_id, Finset.prod_const, Finset.card_range]
  rw [hX, volU, ← Finset.prod_mul_distrib, ← gaussE_pow_odd N]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have hf : (i.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero i)
  field_simp
  ring

theorem gaussE_qr_const (μ : Measure (UNgrp N)) [IsProbabilityMeasure μ] (C : ℝ)
    (hC : ∀ f : (Fin N → Fin N → ℂ) → ENNReal, Measurable f →
      ∫⁻ Z, f Z = ENNReal.ofReal C * ∫⁻ k, (∫⁻ t in triPos N, f (qrMap (k, t)) * ENNReal.ofReal (qrWt t)) ∂μ) :
    C = volU N := by
  have hcont : Continuous fun Z : Fin N → Fin N → ℂ => hs (Matrix.of Z) := by
    unfold hs
    simp only [Matrix.of_apply]
    fun_prop
  have h := hC (fun Z => ENNReal.ofReal (Real.exp (-hs (Matrix.of Z))))
    (ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp hcont.neg).measurable)
  have hin : ∀ k : UNgrp N, (∫⁻ t in triPos N, ENNReal.ofReal (Real.exp (-hs (Matrix.of (qrMap (k, t))))) *
      ENNReal.ofReal (qrWt t)) =
      ENNReal.ofReal (Real.pi ^ (N * (N - 1) / 2) * (∏ i ∈ range N, (i.factorial : ℝ)) / 2 ^ N) := by
    intro k
    simp only [qrMap, Equiv.apply_symm_apply, gaussB_hs_unitary_mul]
    exact gaussD_tri
  simp only [hin, lintegral_const, measure_univ, mul_one, gaussC_mat] at h
  set X := Real.pi ^ (N * (N - 1) / 2) * (∏ i ∈ range N, (i.factorial : ℝ)) / 2 ^ N with hXdef
  have hXpos : 0 < X := by
    rw [hXdef]
    have : 0 < ∏ i ∈ range N, (i.factorial : ℝ) :=
      Finset.prod_pos fun i _ => Nat.cast_pos.2 (Nat.factorial_pos i)
    positivity
  have hPpos : 0 < Real.pi ^ (N ^ 2) := pow_pos Real.pi_pos _
  have hCpos : 0 < C := by
    by_contra hc
    rw [ENNReal.ofReal_of_nonpos (not_lt.mp hc), zero_mul, ENNReal.ofReal_eq_zero] at h
    linarith
  rw [← ENNReal.ofReal_mul hCpos.le, ENNReal.ofReal_eq_ofReal_iff hPpos.le (by positivity)] at h
  have h2 := gaussE_volU_mul (N := N)
  rw [← hXdef] at h2
  exact mul_right_cancel₀ hXpos.ne' (h.symm.trans h2.symm)

theorem qr_const (μ : Measure (UNgrp N)) [IsProbabilityMeasure μ] (C : ℝ)
    (hC : ∀ f : (Fin N → Fin N → ℂ) → ENNReal, Measurable f →
      ∫⁻ Z, f Z = ENNReal.ofReal C * ∫⁻ k, (∫⁻ t in triPos N, f (qrMap (k, t)) * ENNReal.ofReal (qrWt t)) ∂μ) :
    C = volU N :=
  gaussE_qr_const μ C hC

end ReciprocityTheory.ChartRestriction.DS
end
end
end
