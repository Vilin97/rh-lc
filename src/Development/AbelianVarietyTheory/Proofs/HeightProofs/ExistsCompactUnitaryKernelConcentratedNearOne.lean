module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryHaarSmallBallLowerBoundStatement
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
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
public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
public import Formalism.LocalRingCardinality.DataHost
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.HilbertSchmidtCompactUnitarySubOneLeFourMulStatement
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.ExpNegMulSqrtDivPowLe

section

@[expose] public section

namespace GlobalTheory

theorem exp_neg_mul_sqrt_div_pow_le (a : ℝ) (D : ℕ) (ha : 0 < a) :
    ∃ C : ℝ, ∀ m : ℕ, Real.exp (-(a * m * ((m : ℝ) + 1) ^ (-(1 / 2 : ℝ)))) /
      (((m : ℝ) + 1) ^ (-(1 / 2 : ℝ))) ^ D ≤ C * Real.sqrt (((m : ℝ) + 1) ^ (-(1 / 2 : ℝ))) := by
  refine ⟨Real.exp a * ((D + 1).factorial : ℝ) / a ^ (D + 1), fun m => ?_⟩
  set s : ℝ := (m : ℝ) + 1 with hs
  have hs1 : 1 ≤ s := by rw [hs]; have := m.cast_nonneg (α := ℝ); linarith
  have hs0 : 0 < s := by linarith
  set x : ℝ := s ^ (-(1 / 2 : ℝ)) with hxdef
  have hx0 : 0 < x := Real.rpow_pos_of_pos hs0 _
  have hx1 : x ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hs1 (by norm_num)
  have hx2 : x ^ 2 * s = 1 := by
    rw [hxdef, ← Real.rpow_natCast, ← Real.rpow_mul hs0.le]
    norm_num
    rw [Real.rpow_neg_one]; field_simp
  have hmx : (m : ℝ) * x = x⁻¹ - x := by
    have : (m : ℝ) = s - 1 := by rw [hs]; ring
    rw [this]; field_simp; nlinarith [hx2]
  set n := D + 1 with hn
  have hK : 0 < Real.exp a * (n.factorial : ℝ) / a ^ n := by positivity

  have hpow := Real.pow_div_factorial_le_exp (a / x) (by positivity) n
  have hexp : Real.exp (-(a * m * x)) * Real.exp (a / x) ≤ Real.exp a := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : a * m * x = a * (x⁻¹ - x) := by rw [mul_assoc, hmx]
    rw [this, div_eq_mul_inv]
    nlinarith
  have hfac : (0 : ℝ) < n.factorial := by positivity
  have h1 : Real.exp (-(a * m * x)) * ((a / x) ^ n / n.factorial) ≤ Real.exp a :=
    le_trans (mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le) hexp
  have h2 : Real.exp (-(a * m * x)) / x ^ D ≤ Real.exp a * (n.factorial : ℝ) / a ^ n * x := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_pow, div_div, mul_div_assoc', div_le_iff₀ (by positivity)] at h1
    have e : Real.exp a * (n.factorial : ℝ) / a ^ n * x * x ^ D
        = Real.exp a * (x ^ n * n.factorial) / a ^ n := by
      rw [hn, pow_succ]; ring
    rw [e, le_div_iff₀ (by positivity)]
    nlinarith [h1]

  have hxs : x ≤ Real.sqrt x := by
    calc x = Real.sqrt (x ^ 2) := (Real.sqrt_sq hx0.le).symm
      _ ≤ Real.sqrt x := Real.sqrt_le_sqrt (by nlinarith)
  calc Real.exp (-(a * m * x)) / x ^ D ≤ Real.exp a * (n.factorial : ℝ) / a ^ n * x := h2
    _ ≤ Real.exp a * (n.factorial : ℝ) / a ^ n * Real.sqrt x :=
      mul_le_mul_of_nonneg_left hxs hK.le

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.ExpNegMulSqrtDivPowLeStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.exists_exp_neg_mul_div_rpow_pow_le_mul_sqrt : ∀ (a : ℝ) (D : ℕ), 0 < a → ∃ C : ℝ, ∀ m : ℕ, Real.exp (-(a * m * ((m : ℝ) + 1) ^ (-(1 / 2 : ℝ)))) / (((m : ℝ) + 1) ^ (-(1 / 2 : ℝ))) ^ D ≤ C * Real.sqrt (((m : ℝ) + 1) ^ (-(1 / 2 : ℝ))) := by
  first | exact @GlobalTheory.exp_neg_mul_sqrt_div_pow_le | exact GlobalTheory.exp_neg_mul_sqrt_div_pow_le | (intros; apply GlobalTheory.exp_neg_mul_sqrt_div_pow_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.HilbertSchmidtCompactUnitarySubOneEqTrace

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

namespace GlobalTheory

theorem hs_toMK_sub_one {n : ℕ} (ε : Fin n → Bool) (k : KG ε) :
    Formalism.REAL.hs (toMK k - 1) = 2 * (n : ℝ) - 2 * (Matrix.trace (toMK k)).re := by
  have hu : star (toMK k) * toMK k = 1 := Unitary.star_mul_self_of_mem k.2.1
  have hcol : ∀ j, ∑ i, ‖toMK k i j‖ ^ 2 = (1 : ℝ) := by
    intro j
    have h := congrArg Complex.re (congrFun (congrFun hu j) j)
    rw [Matrix.mul_apply, Matrix.one_apply_eq, Complex.re_sum, Complex.one_re] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.star_apply, Complex.star_def, Complex.conj_mul']
    norm_cast
  have hentry : ∀ i j, ‖(toMK k - 1) i j‖ ^ 2 =
      ‖toMK k i j‖ ^ 2 + (if i = j then 1 - 2 * (toMK k i j).re else 0) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [Matrix.sub_apply, Matrix.one_apply_eq, if_pos rfl, Complex.sq_norm, Complex.sq_norm,
        Complex.normSq_sub]
      simp
      ring
    · rw [Matrix.sub_apply, Matrix.one_apply_ne hij, if_neg hij, sub_zero, add_zero]
  unfold Formalism.REAL.hs
  simp_rw [hentry]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_add_distrib, hcol]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [Matrix.trace, Complex.re_sum]
  simp [Matrix.diag]
  ring

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.HilbertSchmidtCompactUnitarySubOneEqTraceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory


theorem _root_.GlobalTheory.T.hilbertSchmidt_compactUnitary_sub_one_eq_trace : ∀ {n : ℕ} (ε : Fin n → Bool) (k : KG ε), Formalism.REAL.hs (toMK k - 1) = 2 * (n : ℝ) - 2 * (Matrix.trace (toMK k)).re := by
  first | exact @GlobalTheory.hs_toMK_sub_one | exact GlobalTheory.hs_toMK_sub_one | (intros; apply GlobalTheory.hs_toMK_sub_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactUnitaryKernelConcentratedNearOne

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

noncomputable section

namespace GlobalTheory.KFourier

theorem retr_mem {n : ℕ} (ε : Fin n → Bool) :
    (fun k : KG ε => (((Matrix.trace (toMK k)).re : ℝ) : ℂ)) ∈ polyV ε 1 := by
  have e : (fun k : KG ε => (((Matrix.trace (toMK k)).re : ℝ) : ℂ)) =
      ∑ a : Fin n, ((1/2 : ℂ) • coord ε (a, a, true) + (1/2 : ℂ) • coord ε (a, a, false)) := by
    funext k
    rw [Complex.re_eq_add_conj]
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, coord]

    simp only [if_true, Bool.false_eq_true, if_false, Matrix.trace, Matrix.diag, map_sum,
    ← Finset.sum_add_distrib, Finset.sum_div, Complex.star_def]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [e]
  exact Submodule.sum_mem _ fun a _ => add_mem (Submodule.smul_mem _ _ (coord_mem ε _))
    (Submodule.smul_mem _ _ (coord_mem ε _))

theorem phipow_mem {n : ℕ} (ε : Fin n → Bool) (A : ℝ) (m : ℕ) :
    (fun k : KG ε => (((1 - Formalism.REAL.hs (toMK k - 1) / A) ^ m : ℝ) : ℂ)) ∈ polyV ε m := by
  have h1 : (fun k : KG ε => (((1 - Formalism.REAL.hs (toMK k - 1) / A) : ℝ) : ℂ)) ∈ polyV ε 1 := by
    have e : (fun k : KG ε => (((1 - Formalism.REAL.hs (toMK k - 1) / A) : ℝ) : ℂ)) =
        (fun _ => ((1 - 2 * n / A : ℝ) : ℂ)) +
          ((2 / A : ℝ) : ℂ) • (fun k : KG ε => (((Matrix.trace (toMK k)).re : ℝ) : ℂ)) := by
      funext k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, GlobalTheory.T.hilbertSchmidt_compactUnitary_sub_one_eq_trace]
      push_cast
      ring
    rw [e]
    exact add_mem (const_mem ε 1 _) (Submodule.smul_mem _ _ (retr_mem ε))
  induction m with
  | zero => simpa using const_mem ε 0 1
  | succ m ih =>
    have := mul_mem ih h1
    convert this using 1
    funext k
    simp [pow_succ]

theorem kernel_near_one : ∀ {n : ℕ} (ε : Fin n → Bool), ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, ∃ κ : KG ε → ℝ,
    Continuous κ ∧ (∀ k, 0 ≤ κ k) ∧ ∫ k, κ k ∂(muK ε) = 1 ∧ (fun k => (κ k : ℂ)) ∈ polyV ε m ∧
    ∫ k, κ k * Real.sqrt (Formalism.REAL.hs (toMK k - 1)) ∂(muK ε) ≤ C * ((m : ℝ) + 1) ^ (-(1 / 4 : ℝ)) := by
  intro n ε
  set A : ℝ := 4 * n + 4 with hA
  have hApos : 0 < A := by positivity
  obtain ⟨c, hc, D, hball⟩ := GlobalTheory.T.compactUnitaryHaar_smallBall_lower_bound ε
  obtain ⟨C5, hC5⟩ := GlobalTheory.T.exists_exp_neg_mul_div_rpow_pow_le_mul_sqrt (1 / (2 * A)) D (by positivity)
  have hC5pos : 0 ≤ C5 := by
    have := hC5 0
    simp at this
    linarith
  refine ⟨1 + 2 * Real.sqrt n * 2 ^ D / c * C5, by positivity, fun m => ?_⟩
  set h : KG ε → ℝ := fun k => Formalism.REAL.hs (toMK k - 1) with hh
  have hcont : Continuous h := by
    have : Continuous (fun g : Matrix (Fin n) (Fin n) ℂ => Formalism.REAL.hs g) := by
      unfold Formalism.REAL.hs; fun_prop
    exact this.comp ((GlobalTheory.TypeSum.continuous_toMK ε).sub continuous_const)
  have h0 : ∀ k, 0 ≤ h k := fun k =>
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have h4 : ∀ k, h k ≤ 4 * n := fun k => GlobalTheory.T.hilbertSchmidt_compactUnitary_sub_one_le_four_mul ε k
  set φ : KG ε → ℝ := fun k => 1 - h k / A with hφ
  have φpos : ∀ k, 1 / ((n : ℝ) + 1) ≤ φ k := by
    intro k
    have : h k / A ≤ 4 * n / A := div_le_div_of_nonneg_right (h4 k) hApos.le
    have e : 1 - 4 * (n : ℝ) / A = 1 / ((n : ℝ) + 1) := by
      rw [hA]; field_simp; ring
    simp only [hφ]; linarith
  have φle : ∀ k, φ k ≤ 1 := fun k => by
    have := div_nonneg (h0 k) hApos.le
    simp only [hφ]; linarith
  have φcont : Continuous φ := continuous_const.sub (hcont.div_const A)
  have hint : ∀ f : KG ε → ℝ, Continuous f → Integrable f (muK ε) := fun f hf =>
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  set Z := ∫ k, φ k ^ m ∂(muK ε) with hZ
  have Zpos : 0 < Z := by
    have := integral_mono (μ := muK ε) (integrable_const ((1 / ((n : ℝ) + 1)) ^ m)) (hint _ (φcont.pow m))
      (fun k => pow_le_pow_left₀ (by positivity) (φpos k) m)
    rw [integral_const] at this
    simp only [probReal_univ, measure_univ, ENNReal.toReal_one, one_smul, Measure.real] at this
    exact lt_of_lt_of_le (by positivity) this
  refine ⟨fun k => φ k ^ m / Z, (φcont.pow m).div_const Z,
    fun k => div_nonneg (pow_nonneg (le_trans (by positivity) (φpos k)) m) Zpos.le, ?_, ?_, ?_⟩
  · rw [integral_div, ← hZ, div_self Zpos.ne']
  · have := Submodule.smul_mem _ ((Z⁻¹ : ℝ) : ℂ) (phipow_mem ε A m)
    convert this using 1
    funext k
    simp only [hφ, hh, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring

  · set δ : ℝ := ((m : ℝ) + 1) ^ (-(1 / 2 : ℝ)) with hδ
    have hm1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by have := (Nat.cast_nonneg m : (0:ℝ) ≤ m); linarith
    have δpos : 0 < δ := Real.rpow_pos_of_pos (by linarith) _
    have δle : δ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hm1 (by norm_num)
    have hA1 : δ / A < 1 := by rw [div_lt_one hApos]; linarith

    have hpt : ∀ k, φ k ^ m * Real.sqrt (h k) ≤
        Real.sqrt δ * φ k ^ m + 2 * Real.sqrt n * (1 - δ / A) ^ m := by
      intro k
      have φ0 : 0 ≤ φ k := le_trans (by positivity) (φpos k)
      have pm0 : 0 ≤ φ k ^ m := pow_nonneg φ0 m
      rcases le_or_gt (h k) δ with hk | hk
      · have := Real.sqrt_le_sqrt hk
        have : 0 ≤ 2 * Real.sqrt n * (1 - δ / A) ^ m := by
          have : 0 ≤ 1 - δ / A := by linarith
          positivity
        nlinarith
      · have hφk : φ k ≤ 1 - δ / A := by
          have : δ / A ≤ h k / A := div_le_div_of_nonneg_right hk.le hApos.le
          simp only [hφ]; linarith
        have hp : φ k ^ m ≤ (1 - δ / A) ^ m := pow_le_pow_left₀ φ0 hφk m
        have hs : Real.sqrt (h k) ≤ 2 * Real.sqrt n := by
          have : Real.sqrt (h k) ≤ Real.sqrt (4 * n) := Real.sqrt_le_sqrt (h4 k)
          rwa [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at this
        have : 0 ≤ Real.sqrt δ * φ k ^ m := by positivity
        have hsq0 : 0 ≤ Real.sqrt (h k) := Real.sqrt_nonneg _
        calc φ k ^ m * Real.sqrt (h k) ≤ (1 - δ / A) ^ m * (2 * Real.sqrt n) :=
              mul_le_mul hp hs hsq0 (pow_nonneg (by linarith) m)
          _ ≤ _ := by nlinarith
    have hup : ∫ k, φ k ^ m * Real.sqrt (h k) ∂(muK ε) ≤
        Real.sqrt δ * Z + 2 * Real.sqrt n * (1 - δ / A) ^ m := by
      have := integral_mono (μ := muK ε) (f := fun k => φ k ^ m * Real.sqrt (h k))
        (g := fun k => Real.sqrt δ * φ k ^ m + 2 * Real.sqrt n * (1 - δ / A) ^ m)
        (hint _ ((φcont.pow m).mul (Real.continuous_sqrt.comp hcont)))
        ((hint (fun k => φ k ^ m) (φcont.pow m)).const_mul (Real.sqrt δ) |>.add (integrable_const _)) hpt
      rw [integral_add ((hint (fun k => φ k ^ m) (φcont.pow m)).const_mul (Real.sqrt δ)) (integrable_const _),
        integral_const_mul, integral_const] at this
      simpa only [probReal_univ, measure_univ, ENNReal.toReal_one, one_smul, Measure.real] using this

    set B : Set (KG ε) := {k | Formalism.REAL.hs (toMK k - 1) ≤ δ / 2} with hB
    have hBm : MeasurableSet B := (isClosed_le hcont continuous_const).measurableSet
    have hlow : (1 - δ / (2 * A)) ^ m * (muK ε B).toReal ≤ Z := by
      have hpt2 : ∀ k, B.indicator (fun _ => (1 - δ / (2 * A)) ^ m) k ≤ φ k ^ m := by
        intro k
        by_cases hk : k ∈ B
        · rw [Set.indicator_of_mem hk]
          have hk' : h k ≤ δ / 2 := hk
          have h1 : 0 ≤ 1 - δ / (2 * A) := by
            have : δ / (2 * A) ≤ δ / A := div_le_div_of_nonneg_left δpos.le hApos (by linarith)
            linarith
          have h2 : 1 - δ / (2 * A) ≤ φ k := by
            have : h k / A ≤ δ / 2 / A := div_le_div_of_nonneg_right hk' hApos.le
            rw [div_div] at this
            simp only [hφ]; linarith
          exact pow_le_pow_left₀ h1 h2 m
        · rw [Set.indicator_of_notMem hk]
          exact pow_nonneg (le_trans (by positivity) (φpos k)) m
      have := integral_mono (μ := muK ε) (g := fun k => φ k ^ m) ((integrable_const _).indicator hBm)
        (hint (fun k => φ k ^ m) (φcont.pow m)) hpt2
      rw [integral_indicator_const _ hBm] at this
      simpa only [smul_eq_mul, Measure.real, mul_comm] using this
    have hball' := hball (δ / 2) (by positivity) (by linarith)

    have hC : Real.exp (-(1 / (2 * A) * m * δ)) / δ ^ D ≤ C5 * Real.sqrt δ := hC5 m
    have hq0 : 0 < 1 - δ / (2 * A) := by
      have : δ / (2 * A) ≤ δ / A := div_le_div_of_nonneg_left δpos.le hApos (by linarith)
      linarith
    have hratio : (1 - δ / A) ^ m ≤ (1 - δ / (2 * A)) ^ m * Real.exp (-(1 / (2 * A) * m * δ)) := by
      have hexp : 1 - δ / (2 * A) ≤ Real.exp (-(δ / (2 * A))) := by
        have := Real.add_one_le_exp (-(δ / (2 * A))); linarith
      have h1 : 1 - δ / A ≤ (1 - δ / (2 * A)) * Real.exp (-(δ / (2 * A))) := by
        have e : 1 - δ / A = (1 - δ / (2 * A)) * (1 - δ / (2 * A)) - (δ / (2 * A)) ^ 2 := by
          field_simp; ring
        have : (1 - δ / (2 * A)) * (1 - δ / (2 * A)) ≤ (1 - δ / (2 * A)) * Real.exp (-(δ / (2 * A))) :=
          mul_le_mul_of_nonneg_left hexp hq0.le
        nlinarith [sq_nonneg (δ / (2 * A))]
      calc (1 - δ / A) ^ m ≤ ((1 - δ / (2 * A)) * Real.exp (-(δ / (2 * A)))) ^ m :=
            pow_le_pow_left₀ (by linarith) h1 m
        _ = (1 - δ / (2 * A)) ^ m * Real.exp (-(1 / (2 * A) * m * δ)) := by
            rw [mul_pow, ← Real.exp_nat_mul]; congr 2; ring
    have hL : (1 - δ / (2 * A)) ^ m * (c * (δ / 2) ^ D) ≤ Z :=
      le_trans (mul_le_mul_of_nonneg_left hball' (pow_nonneg hq0.le m)) hlow
    have hLpos : 0 < (1 - δ / (2 * A)) ^ m * (c * (δ / 2) ^ D) := by positivity
    have e1 : ∫ k, (fun k => φ k ^ m / Z) k * Real.sqrt (Formalism.REAL.hs (toMK k - 1)) ∂(muK ε) =
        (∫ k, φ k ^ m * Real.sqrt (h k) ∂(muK ε)) / Z := by
      rw [← integral_div]; congr 1; funext k; simp only [hh]; ring
    have hsq : Real.sqrt δ = ((m : ℝ) + 1) ^ (-(1 / 4 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, hδ, ← Real.rpow_mul (by linarith)]; norm_num
    have hK0 : 0 ≤ 2 * Real.sqrt n * 2 ^ D / c := by positivity
    have hT : 2 * Real.sqrt n * (1 - δ / A) ^ m / Z ≤
        2 * Real.sqrt n * 2 ^ D / c * (Real.exp (-(1 / (2 * A) * m * δ)) / δ ^ D) := by
      have hE : 0 ≤ Real.exp (-(1 / (2 * A) * m * δ)) := (Real.exp_pos _).le
      calc 2 * Real.sqrt n * (1 - δ / A) ^ m / Z
          ≤ 2 * Real.sqrt n * ((1 - δ / (2 * A)) ^ m * Real.exp (-(1 / (2 * A) * m * δ))) /
              ((1 - δ / (2 * A)) ^ m * (c * (δ / 2) ^ D)) := by
            apply div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hratio (by positivity)) hLpos hL
        _ = 2 * Real.sqrt n * 2 ^ D / c * (Real.exp (-(1 / (2 * A) * m * δ)) / δ ^ D) := by
            have hq : (1 - δ / (2 * A)) ^ m ≠ 0 := (pow_pos hq0 m).ne'
            have hd : δ ^ D ≠ 0 := (pow_pos δpos D).ne'
            have h2 : (2 : ℝ) ^ D ≠ 0 := by positivity
            rw [div_pow]
            generalize (1 - δ / (2 * A)) ^ m = q at hq ⊢
            generalize Real.exp (-(1 / (2 * A) * m * δ)) = E
            generalize δ ^ D = d at hd ⊢
            field_simp
    rw [e1]
    calc (∫ k, φ k ^ m * Real.sqrt (h k) ∂(muK ε)) / Z
        ≤ (Real.sqrt δ * Z + 2 * Real.sqrt n * (1 - δ / A) ^ m) / Z := div_le_div_of_nonneg_right hup Zpos.le
      _ = Real.sqrt δ + 2 * Real.sqrt n * (1 - δ / A) ^ m / Z := by field_simp
      _ ≤ Real.sqrt δ + 2 * Real.sqrt n * 2 ^ D / c * (C5 * Real.sqrt δ) := by
            have := mul_le_mul_of_nonneg_left hC hK0
            linarith
      _ = (1 + 2 * Real.sqrt n * 2 ^ D / c * C5) * ((m : ℝ) + 1) ^ (-(1 / 4 : ℝ)) := by
            rw [← hsq]; ring

end GlobalTheory.KFourier

end
end
end
