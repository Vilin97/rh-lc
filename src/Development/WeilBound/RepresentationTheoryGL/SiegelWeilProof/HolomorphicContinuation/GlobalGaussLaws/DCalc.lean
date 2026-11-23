module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DifferenceQuotientIsometryExchangeAlt
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DCalcB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DCalcD
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DCalcC

section

@[expose] public section

noncomputable section

open Matrix MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob

namespace DCalcCH

open DCalcH DCalcBH

variable {m n : ℕ}

theorem mR_one : mR (1 : GR n) = 1 := rfl

theorem cnt_add (ε : Fin m → Bool) : cnt ε true + cnt ε false = m := by
  unfold cnt
  rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  have h : ∀ a : Fin m, ((if ε a = true then 1 else 0) + (if ε a = false then 1 else 0) : ℕ) = 1 := by
    intro a; cases ε a <;> simp
  simp [h]

theorem det_diag_exp (X : Fin n → ℝ) (z : ℂ) :
    (diagonal fun j => Complex.exp (-(z * X j))).det = Complex.exp (-(z * ∑ j, (X j : ℂ))) := by
  rw [det_diagonal, ← Complex.exp_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]

theorem det_aC (X : Fin n → ℝ) (z : ℂ) : (aC X z).det = 1 := by
  unfold aC
  rw [det_fromBlocks_zero₂₁, det_diagonal, det_diagonal, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun j _ => ?_
  rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

theorem zpow_exp_neg (w : ℂ) (p : ℕ) : Complex.exp (-w) ^ (-(p : ℤ)) = Complex.exp ((p : ℂ) * w) := by
  rw [← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

theorem jC_one (e : ℤ) (p q : ℕ) (X : Fin n → ℝ) (z : ℂ) :
    jC e p q 1 X z = Complex.exp (((p : ℂ) + q) * (z * ∑ j, (X j : ℂ))) := by
  unfold jC
  simp only [mR_one, Matrix.one_mul]
  rw [det_aC]
  unfold aC
  simp only [toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, Matrix.zero_mul, zero_add, _root_.one_zpow, one_mul]
  rw [det_diag_exp, zpow_exp_neg, zpow_exp_neg, ← Complex.exp_add]
  congr 1
  ring

theorem inv_diag_exp (X : Fin n → ℝ) (z : ℂ) :
    (diagonal fun j => Complex.exp (-(z * X j)))⁻¹ = diagonal fun j => Complex.exp (z * X j) := by
  refine Matrix.inv_eq_left_inv ?_
  rw [diagonal_mul_diagonal]
  conv_rhs => rw [← diagonal_one]
  congr 1
  funext j
  rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

theorem ptZ_one (X : Fin n → ℝ) (z s₀ : ℂ) :
    ptZ 1 X z s₀ = s₀ • diagonal fun j => Complex.exp (2 * z * X j) := by
  unfold ptZ
  simp only [mR_one, Matrix.one_mul]
  unfold aC
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂,
    Matrix.zero_mul, zero_add, add_zero]
  rw [inv_diag_exp, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, diagonal_mul_diagonal]
  congr 2
  funext j
  rw [← Complex.exp_add]
  congr 1
  ring

theorem gramB_diag (ε : Fin m → Bool) (b : Bool) (u : Fin m → Fin n → ℂ) (j : Fin n) :
    gramB ε b u j j = ∑ a ∈ Finset.univ.filter (fun a => ε a = b), star (u a j) * u a j := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [gramB, Qb, evX, map_sum, eval_X]

theorem trace_sdiag (s₀ : ℂ) (w : Fin n → ℂ) (G : Matrix (Fin n) (Fin n) ℂ) :
    ((s₀ • diagonal w) * G).trace = s₀ * ∑ j, w j * G j j := by
  rw [Matrix.smul_mul, trace_smul, smul_eq_mul]
  congr 1
  simp [trace, diagonal_mul]

theorem famC_one (ε : Fin m → Bool) (t c : ℝ) (e : ℤ) (X : Fin n → ℝ) (u : Fin m → Fin n → ℂ) (s : ℝ) :
    famC ε t c e 1 X (s : ℂ) u = fF c X 1 u s := by
  unfold famC fF fP
  rw [jC_one, ptZ_one, ptZ_one, gs_vS]
  unfold gC
  rw [trace_sdiag, trace_sdiag]
  simp only [gramB_diag, evX_eq, map_one, one_mul]
  have hpq : ((cnt (epsT t ε) true : ℂ) + (cnt (epsT t ε) false : ℂ)) = (m : ℂ) := by
    rw [← Nat.cast_add, cnt_add]
  rw [hpq, ← Complex.exp_add, Complex.ofReal_exp]
  have hsum : ∀ j, (∑ a ∈ Finset.univ.filter (fun a => epsT t ε a = true), star (u a j) * u a j) +
      (∑ a ∈ Finset.univ.filter (fun a => epsT t ε a = false), star (u a j) * u a j) =
      ∑ a, ((‖u a j‖ ^ 2 : ℝ) : ℂ) := by
    intro j
    have := Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin m)))
      (p := fun a => epsT t ε a = true) (f := fun a => star (u a j) * u a j)
    simp only [Bool.not_eq_true] at this
    rw [this]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
    push_cast; ring
  have e2 : ∀ j, Complex.exp (2 * (s : ℂ) * (X j : ℂ)) = ((Real.exp (s * X j) ^ 2 : ℝ) : ℂ) := by
    intro j
    push_cast
    rw [← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  unfold nS
  push_cast
  simp only [e2]
  have key : Complex.I * (c : ℂ) * (Complex.I * ∑ j, ((Real.exp (s * X j) ^ 2 : ℝ) : ℂ) *
        ∑ a ∈ Finset.univ.filter (fun a => epsT t ε a = true), star (u a j) * u a j) -
      Complex.I * (c : ℂ) * (-Complex.I * ∑ j, ((Real.exp (s * X j) ^ 2 : ℝ) : ℂ) *
        ∑ a ∈ Finset.univ.filter (fun a => epsT t ε a = false), star (u a j) * u a j) =
      -((c : ℂ) * ∑ j, ((Real.exp (s * X j) ^ 2 : ℝ) : ℂ) * ∑ a, ((‖u a j‖ ^ 2 : ℝ) : ℂ)) := by
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    simp only [← hsum, mul_add, Finset.sum_add_distrib]
    linear_combination ((c : ℂ) * ∑ j, ((Real.exp (s * X j) ^ 2 : ℝ) : ℂ) *
        ∑ a ∈ Finset.univ.filter (fun a => epsT t ε a = true), star (u a j) * u a j +
      (c : ℂ) * ∑ j, ((Real.exp (s * X j) ^ 2 : ℝ) : ℂ) *
        ∑ a ∈ Finset.univ.filter (fun a => epsT t ε a = false), star (u a j) * u a j) * hI
  rw [key, ← Complex.exp_add]
  have hswap : ∀ (E : Fin n → ℂ) (N : Fin m → Fin n → ℂ), (∑ j, E j * ∑ a, N a j) = ∑ a, ∑ j, N a j * E j := by
    intro E N
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => mul_comm _ _
  congr 1
  push_cast
  rw [hswap]
  ring

end DCalcCH

end PositivityTheory.Rg.Sw.Glob
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DCalcE

section

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob

namespace DCalcEH

open DCalcH DCalcBH DCalcDH

variable {m n : ℕ}

theorem crd_cont (X : Fin n → ℝ) (s : ℝ) : Continuous fun u : Fin m → Fin n → ℂ => crd (vS u X s) := by
  refine continuous_pi fun k => ?_
  unfold crd vS
  split_ifs <;> fun_prop

theorem fF_cont (c : ℝ) (X : Fin n → ℝ) (Q : PX m n) (s : ℝ) : Continuous fun u : Fin m → Fin n → ℂ => fF c X Q u s := by
  unfold fF fP
  refine continuous_const.mul (Continuous.mul ?_ ?_)
  · simp only [evX_eq]
    exact (MvPolynomial.continuous_eval Q).comp (crd_cont X s)
  · simp only [gs, vS]
    fun_prop

theorem norm_gs (c : ℝ) (v : Fin m → Fin n → ℂ) : ‖gs c v‖ = Real.exp (-(c * sqN v)) := by
  simp only [gs, sqN]
  rw [← Complex.ofReal_neg, Complex.norm_exp_ofReal]

theorem sq_vS_le (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (s R : ℝ) (hs : |s| ≤ R) :
    Real.exp (-(2 * R * ∑ j, |X j|)) * sqN u ≤ sqN (vS u X s) ∧ sqN (vS u X s) ≤ Real.exp (2 * R * ∑ j, |X j|) * sqN u := by
  have hR : 0 ≤ R := (abs_nonneg s).trans hs
  have hX : ∀ j, |2 * s * X j| ≤ 2 * R * ∑ j, |X j| := by
    intro j
    have h1 : |X j| ≤ ∑ j, |X j| := Finset.single_le_sum (f := fun j => |X j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    rw [abs_mul, abs_mul, abs_two]
    have := mul_le_mul hs h1 (abs_nonneg _) hR
    nlinarith
  have hterm : ∀ a j, ‖vS u X s a j‖ ^ 2 = ‖u a j‖ ^ 2 * Real.exp (2 * s * X j) := by
    intro a j
    rw [norm_vS, ← Real.exp_nat_mul]; push_cast; ring_nf
  unfold sqN
  simp only [hterm]
  constructor
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
    linarith [neg_abs_le (2 * s * X j), hX j]
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity) |>.trans_eq (mul_comm _ _)
    linarith [le_abs_self (2 * s * X j), hX j]

theorem fF_bound (c : ℝ) (hc : 0 < c) (X : Fin n → ℝ) (Q : PX m n) (s : ℝ) :
    ∃ K a, 0 ≤ K ∧ 0 < a ∧ ∀ u, ∀ s' ∈ Set.Icc (s - 1) (s + 1), ‖fF c X Q u s'‖ ≤ K * Real.exp (-(a * sqN u)) := by
  set R := |s| + 1
  set M := ∑ j, |X j|
  set κ := Real.exp (-(2 * R * M))
  set κ' := Real.exp (2 * R * M)
  have hκ : 0 < κ := Real.exp_pos _
  have hκ' : 1 ≤ κ' := Real.one_le_exp (by positivity)
  obtain ⟨C, N, hC, hev⟩ := evX_growth Q
  obtain ⟨C2, hC2, hpe⟩ := poly_exp N (c * κ) (by positivity)
  refine ⟨Real.exp (R * m * M) * (C * (κ' ^ N * C2)), c * κ / 2, by positivity, by positivity, fun u s' hs' => ?_⟩
  have hs'R : |s'| ≤ R := by
    rw [abs_le]; constructor <;> linarith [hs'.1, hs'.2, neg_abs_le s, le_abs_self s]
  obtain ⟨hlo, hhi⟩ := sq_vS_le u X s' R hs'R
  have hS := sqN_nonneg u
  have h1 : ‖((Real.exp (s' * (m : ℝ) * ∑ j, X j) : ℝ) : ℂ)‖ ≤ Real.exp (R * m * M) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.2 ?_
    have : |∑ j, X j| ≤ M := Finset.abs_sum_le_sum_abs _ _
    have h2 : s' * (m : ℝ) * ∑ j, X j ≤ |s'| * m * |∑ j, X j| := by
      calc s' * (m : ℝ) * ∑ j, X j ≤ |s' * (m : ℝ) * ∑ j, X j| := le_abs_self _
        _ = |s'| * m * |∑ j, X j| := by rw [abs_mul, abs_mul, Nat.abs_cast]
    have h3 : |s'| * m * |∑ j, X j| ≤ R * m * M :=
      mul_le_mul (mul_le_mul_of_nonneg_right hs'R (by positivity)) this (abs_nonneg _) (by positivity)
    linarith
  have h2 : ‖evX Q (vS u X s')‖ ≤ C * (κ' ^ N * (1 + sqN u) ^ N) := by
    refine (hev _).trans (mul_le_mul_of_nonneg_left ?_ hC)
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by linarith [sqN_nonneg (vS u X s')]) ?_ N
    nlinarith
  have h3 : ‖gs c (vS u X s')‖ ≤ Real.exp (-(c * κ * sqN u)) := by
    rw [norm_gs]; refine Real.exp_le_exp.2 ?_
    have := mul_le_mul_of_nonneg_left hlo hc.le
    linarith
  unfold fF fP
  rw [norm_mul, norm_mul]
  calc ‖((Real.exp (s' * (m : ℝ) * ∑ j, X j) : ℝ) : ℂ)‖ * (‖evX Q (vS u X s')‖ * ‖gs c (vS u X s')‖)
      ≤ Real.exp (R * m * M) * (C * (κ' ^ N * (1 + sqN u) ^ N) * Real.exp (-(c * κ * sqN u))) :=
        mul_le_mul h1 (mul_le_mul h2 h3 (norm_nonneg _)
          (mul_nonneg hC (mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg (by linarith) _))))
          (by positivity) (by positivity)
    _ = Real.exp (R * m * M) * (C * (κ' ^ N * ((1 + sqN u) ^ N * Real.exp (-(c * κ * sqN u))))) := by ring
    _ ≤ Real.exp (R * m * M) * (C * (κ' ^ N * (C2 * Real.exp (-(c * κ / 2 * sqN u))))) := by
        have := hpe (sqN u) hS
        gcongr
    _ = Real.exp (R * m * M) * (C * (κ' ^ N * C2)) * Real.exp (-(c * κ / 2 * sqN u)) := by ring

end DCalcEH

end PositivityTheory.Rg.Sw.Glob
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.HasDeriv

section

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob

namespace DCalc2H

open DCalcH DCalcBH DCalcDH DCalcEH

variable {m n : ℕ}

theorem hasDeriv (c : ℝ) (X : Fin n → ℝ) (P : PX m n) (u : Fin m → Fin n → ℂ) (t : ℝ) :
    HasDerivAt (fun t => fF c X P u t) (fF c X (dil c X P) u t) t :=
  fF_hasDeriv c X P u t

theorem quot_le (c : ℝ) (X : Fin n → ℝ) (P : PX m n) (u : Fin m → Fin n → ℂ) (s B : ℝ)
    (hB : ∀ t ∈ Set.Icc (s - 1) (s + 1), ‖fF c X (dil c X P) u t‖ ≤ B) (h : ℝ) (hh : |h| ≤ 1) :
    ‖fF c X P u (s + h) - fF c X P u s‖ ≤ B * |h| := by
  have hcv : Convex ℝ (Set.Icc (s - 1) (s + 1)) := convex_Icc _ _
  have hs : s ∈ Set.Icc (s - 1) (s + 1) := ⟨by linarith, by linarith⟩
  have hsh : s + h ∈ Set.Icc (s - 1) (s + 1) := by
    rw [abs_le] at hh; exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
  have := hcv.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun t => fF c X P u t)
    (fun t _ => (hasDeriv c X P u t).hasDerivWithinAt) hB hs hsh
  simpa [Real.norm_eq_abs] using this

theorem l2conv (c : ℝ) (hc : 0 < c) (X : Fin n → ℝ) (P : PX m n) (s : ℝ) :
    Tendsto (fun h : ℝ => ∫ u, ‖(fF c X P u (s + h) - fF c X P u s) / (h : ℂ) - fF c X (dil c X P) u s‖ ^ 2)
      (𝓝[≠] 0) (𝓝 0) := by
  obtain ⟨K, a, hK, ha, hb⟩ := fF_bound c hc X (dil c X P) s
  suffices key : Tendsto (fun h : ℝ => ∫ u, ‖(fF c X P u (s + h) - fF c X P u s) / (h : ℂ) - fF c X (dil c X P) u s‖ ^ 2)
      (𝓝[≠] 0) (𝓝 (∫ _u : Fin m → Fin n → ℂ, (0 : ℝ))) by simpa using key
  refine tendsto_integral_filter_of_dominated_convergence
    (fun u => (2 * K) ^ 2 * Real.exp (-(2 * a * sqN u))) ?_ ?_ ?_ ?_
  · refine Eventually.of_forall fun h => ?_
    refine Continuous.aestronglyMeasurable ?_
    have h1 := fF_cont c X P (s + h)
    have h2 := fF_cont c X P s
    have h3 := fF_cont c X (dil c X P) s
    fun_prop
  · have hev : ∀ᶠ h in 𝓝[≠] (0 : ℝ), |h| ≤ 1 ∧ h ≠ 0 := by
      refine (eventually_nhdsWithin_of_eventually_nhds ?_).and self_mem_nhdsWithin
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with h hh
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hh
      exact hh.le
    filter_upwards [hev] with h ⟨hh, h0⟩
    refine Eventually.of_forall fun u => ?_
    have hB : ∀ t ∈ Set.Icc (s - 1) (s + 1), ‖fF c X (dil c X P) u t‖ ≤ K * Real.exp (-(a * sqN u)) := fun t ht => hb u t ht
    have hq := quot_le c X P u s _ hB h hh
    have hhpos : 0 < |h| := abs_pos.2 h0
    have e1 : ‖(fF c X P u (s + h) - fF c X P u s) / (h : ℂ)‖ ≤ K * Real.exp (-(a * sqN u)) := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, div_le_iff₀ hhpos]
      exact hq
    have e2 : ‖fF c X (dil c X P) u s‖ ≤ K * Real.exp (-(a * sqN u)) := hb u s ⟨by linarith, by linarith⟩
    have e3 : ‖(fF c X P u (s + h) - fF c X P u s) / (h : ℂ) - fF c X (dil c X P) u s‖ ≤ 2 * K * Real.exp (-(a * sqN u)) := by
      calc _ ≤ ‖(fF c X P u (s + h) - fF c X P u s) / (h : ℂ)‖ + ‖fF c X (dil c X P) u s‖ := norm_sub_le _ _
        _ ≤ _ := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ‖(fF c X P u (s + h) - fF c X P u s) / (h : ℂ) - fF c X (dil c X P) u s‖ ^ 2
        ≤ (2 * K * Real.exp (-(a * sqN u))) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) e3 2
      _ = (2 * K) ^ 2 * Real.exp (-(2 * a * sqN u)) := by
        rw [mul_pow, ← Real.exp_nat_mul]; push_cast; ring_nf
  · exact (integrable_gauss (2 * a) (by positivity)).const_mul _
  · refine Eventually.of_forall fun u => ?_
    have : Tendsto (fun h : ℝ => (fF c X P u (s + h) - fF c X P u s) / (h : ℂ) - fF c X (dil c X P) u s) (𝓝[≠] 0) (𝓝 0) := by
      have h2 := (hasDeriv c X P u s).tendsto_slope_zero
      have h3 := h2.sub_const (fF c X (dil c X P) u s)
      rw [sub_self] at h3
      refine h3.congr' (Eventually.of_forall fun h => ?_)
      show h⁻¹ • (fF c X P u (s + h) - fF c X P u s) - fF c X (dil c X P) u s =
        (fF c X P u (s + h) - fF c X P u s) / (h : ℂ) - fF c X (dil c X P) u s
      rw [Complex.real_smul, Complex.ofReal_inv, div_eq_inv_mul]
    have := (this.norm).pow 2
    simpa using this

end DCalc2H

end PositivityTheory.Rg.Sw.Glob

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DCalc

section

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace PositivityTheory.Rg.Sw.Glob

open DCalcBH DCalcCH in
theorem dCalc : DCalc := by
  intro m n ε t c e X hc _
  have hfun : ∀ u : Fin m → Fin n → ℂ, (fun s' : ℝ => famC ε t c e 1 X (↑s') u) = fF c X 1 u :=
    fun u => funext fun s => famC_one ε t c e X u s
  refine ⟨fun s r u => ?_, fun r s => ?_⟩
  · rw [hfun, fF_iter]
    rfl
  · simp only [hfun, fF_iter]
    rw [pow_succ']
    exact DCalc2H.l2conv c hc X ((dil c X ^ r) 1) s

end PositivityTheory.Rg.Sw.Glob
end
end
end
