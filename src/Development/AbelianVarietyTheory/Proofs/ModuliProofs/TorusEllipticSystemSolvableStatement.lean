module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsEventuallyNormRiemannThetaTermLe
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.PSeries
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
import Mathlib.Topology.Compactness.DeltaGeneratedSpace
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsRapidFourierSeriesOfIntPeriodic
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FourierCoeffEqZeroOfTsumEqZeroFin
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Lemma

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ContDiffAndFderivTsumFourierOfRapid

section

@[expose] public section

open Complex Matrix
open scoped ContDiff BigOperators Real

namespace GlobalTheory
namespace RapidFourier

noncomputable def linForm {n : ℕ} (ν : Fin n → ℤ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ k, (ν k : ℝ) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) k

theorem linForm_apply {n : ℕ} (ν : Fin n → ℤ) (x : Fin n → ℝ) :
    linForm ν x = ∑ k, (ν k : ℝ) * x k := by
  simp [linForm]

theorem norm_linForm_le {n : ℕ} (ν : Fin n → ℤ) : ‖linForm ν‖ ≤ ∑ k, |(ν k : ℝ)| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun k _ => abs_nonneg _) fun x => ?_
  calc ‖linForm ν x‖ = |∑ k, (ν k : ℝ) * x k| := by rw [linForm_apply, Real.norm_eq_abs]
    _ ≤ ∑ k, |(ν k : ℝ) * x k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, |(ν k : ℝ)| * ‖x‖ := Finset.sum_le_sum fun k _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using norm_le_pi_norm x k)
          (abs_nonneg _)
    _ = (∑ k, |(ν k : ℝ)|) * ‖x‖ := by rw [Finset.sum_mul]

noncomputable def wave (a : ℂ) (t : ℝ) : ℂ := a * cexp (2 * π * I * t)

theorem hasDerivAt_wave (a : ℂ) (t : ℝ) :
    HasDerivAt (wave a) (wave (2 * π * I * a) t) t := by
  have h := (((hasDerivAt_id (t : ℂ)).const_mul (2 * π * I)).cexp.const_mul a).comp_ofReal
  convert (preTransparency := .reducible) h using 1
  · funext y
    simp [wave]
  · simp only [wave, id]
    ring

theorem contDiff_wave (a : ℂ) : ContDiff ℝ ∞ (wave a) := by
  have h : ContDiff ℝ ∞ fun t : ℝ => ((t : ℝ) : ℂ) := Complex.ofRealCLM.contDiff
  exact contDiff_const.mul ((contDiff_const.mul h).cexp)

theorem iteratedDeriv_wave (m : ℕ) (a : ℂ) :
    iteratedDeriv m (wave a) = wave ((2 * π * I) ^ m * a) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    rw [(hasDerivAt_wave _ t).deriv, pow_succ]
    ring_nf

theorem norm_wave (a : ℂ) (t : ℝ) : ‖wave a t‖ = ‖a‖ := by
  have h : (2 * π * I * t : ℂ) = ((2 * π * t : ℝ) : ℂ) * I := by push_cast; ring
  rw [wave, norm_mul, h, Complex.norm_exp_ofReal_mul_I, mul_one]

theorem norm_two_pi_I : ‖(2 * π * I : ℂ)‖ = 2 * π := by
  rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
    mul_one]
  norm_num

theorem term_eq {n : ℕ} (a : ℂ) (ν : Fin n → ℤ) (x : Fin n → ℝ) :
    a * cexp (2 * π * I * ∑ k, (ν k : ℂ) * (x k : ℂ)) = wave a (linForm ν x) := by
  rw [wave, linForm_apply]
  push_cast
  rfl

theorem norm_iteratedFDeriv_term_le {n : ℕ} (a : ℂ) (ν : Fin n → ℤ) (m : ℕ) (x : Fin n → ℝ) :
    ‖iteratedFDeriv ℝ m (wave a ∘ linForm ν) x‖
      ≤ (2 * π) ^ m * (‖a‖ * (1 + ∑ k, |(ν k : ℝ)|) ^ m) := by
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right _ (contDiff_wave a) x
    (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_wave, norm_wave, norm_mul,
    norm_pow, norm_two_pi_I, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hL : ‖linForm ν‖ ≤ 1 + ∑ k, |(ν k : ℝ)| := (norm_linForm_le ν).trans (le_add_of_nonneg_left zero_le_one)
  have hpow : ‖linForm ν‖ ^ m ≤ (1 + ∑ k, |(ν k : ℝ)|) ^ m := pow_le_pow_left₀ (norm_nonneg _) hL m
  calc (2 * π) ^ m * ‖a‖ * ‖linForm ν‖ ^ m ≤ (2 * π) ^ m * ‖a‖ * (1 + ∑ k, |(ν k : ℝ)|) ^ m :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = (2 * π) ^ m * (‖a‖ * (1 + ∑ k, |(ν k : ℝ)|) ^ m) := by ring

theorem summable_inv_one_add_abs_sq : Summable fun m : ℤ => ((1 + |(m : ℝ)|) ^ 2)⁻¹ := by
  have hN : Summable fun k : ℕ => ((1 + (k : ℝ)) ^ 2)⁻¹ := by
    have h := (summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr one_lt_two)
    refine h.congr fun k => ?_
    push_cast
    ring_nf
  refine Summable.of_nat_of_neg ?_ ?_
  · refine hN.congr fun k => ?_
    simp
  · refine hN.congr fun k => ?_
    simp

theorem summable_inv_pow (n : ℕ) :
    Summable fun ν : Fin n → ℤ => ((1 + ∑ k, |(ν k : ℝ)|) ^ (2 * n))⁻¹ := by
  have hprod : Summable fun ν : Fin n → ℤ => ∏ k, ((1 + |(ν k : ℝ)|) ^ 2)⁻¹ :=
    GlobalTheory.summable_pi_prod_of_nonneg (f := fun _ (m : ℤ) => ((1 + |(m : ℝ)|) ^ 2)⁻¹)
      (fun _ _ => by positivity) fun _ => summable_inv_one_add_abs_sq
  refine Summable.of_nonneg_of_le (fun ν => by positivity) (fun ν => ?_) hprod
  rw [Finset.prod_inv_distrib]
  apply inv_anti₀ (Finset.prod_pos fun k _ => by positivity)
  calc ∏ k, (1 + |(ν k : ℝ)|) ^ 2 ≤ ∏ _k : Fin n, (1 + ∑ k, |(ν k : ℝ)|) ^ 2 :=
        Finset.prod_le_prod₀ (fun k _ => by positivity) fun k _ =>
          pow_le_pow_left₀ (by positivity)
            (add_le_add le_rfl (Finset.single_le_sum (f := fun k => |(ν k : ℝ)|)
              (fun _ _ => abs_nonneg _) (Finset.mem_univ k))) 2
    _ = (1 + ∑ k, |(ν k : ℝ)|) ^ (2 * n) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_comm]

theorem summable_weighted {n : ℕ} {c : (Fin n → ℤ) → ℂ}
    (hc : ∀ N : ℕ, ∃ C : ℝ, ∀ ν, ‖c ν‖ * (1 + ∑ k, |(ν k : ℝ)|) ^ N ≤ C) (m : ℕ) :
    Summable fun ν => ‖c ν‖ * (1 + ∑ k, |(ν k : ℝ)|) ^ m := by
  obtain ⟨C, hC⟩ := hc (m + 2 * n)
  refine Summable.of_nonneg_of_le (fun ν => by positivity) (fun ν => ?_)
    ((summable_inv_pow n).mul_left C)
  have hpos : 0 < (1 + ∑ k, |(ν k : ℝ)|) ^ (2 * n) := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hpos, mul_assoc, ← pow_add]
  exact hC ν

theorem hasFDerivAt_term {n : ℕ} (a : ℂ) (ν : Fin n → ℤ) (x : Fin n → ℝ) :
    HasFDerivAt (wave a ∘ linForm ν)
      ((linForm ν).smulRight (wave (2 * π * I * a) (linForm ν x))) x := by
  have h := (hasDerivAt_wave a (linForm ν x)).hasFDerivAt.comp x (linForm ν).hasFDerivAt
  refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  simp

end RapidFourier


open RapidFourier in
theorem contDiff_and_fderiv_tsum_fourier_of_rapid :
    ∀ (n : ℕ) (c : (Fin n → ℤ) → ℂ), (∀ N : ℕ, ∃ C : ℝ, ∀ ν, ‖c ν‖ * (1 + ∑ k, |(ν k : ℝ)|) ^ N ≤ C) → ContDiff ℝ ∞ (fun x : Fin n → ℝ => ∑' ν, c ν * cexp (2 * π * I * ∑ k, (ν k : ℂ) * (x k : ℂ))) ∧ ∀ (x : Fin n → ℝ) (j : Fin n), fderiv ℝ (fun x : Fin n → ℝ => ∑' ν, c ν * cexp (2 * π * I * ∑ k, (ν k : ℂ) * (x k : ℂ))) x (Pi.single j 1) = ∑' ν, 2 * π * I * (ν j : ℂ) * c ν * cexp (2 * π * I * ∑ k, (ν k : ℂ) * (x k : ℂ)) :=
  open RapidFourier in
  by
  intro n c hc
  have hfun : (fun x : Fin n → ℝ => ∑' ν, c ν * cexp (2 * π * I * ∑ k, (ν k : ℂ) * (x k : ℂ))) =
      fun x => ∑' ν, (wave (c ν) ∘ linForm ν) x := by
    funext x
    exact tsum_congr fun ν => term_eq (c ν) ν x
  have hL : ∀ ν : Fin n → ℤ, ‖linForm ν‖ ≤ 1 + ∑ k, |(ν k : ℝ)| := fun ν =>
    (norm_linForm_le ν).trans (le_add_of_nonneg_left zero_le_one)
  have hsum : ∀ m : ℕ, Summable fun ν : Fin n → ℤ =>
      (2 * π) ^ m * (‖c ν‖ * (1 + ∑ k, |(ν k : ℝ)|) ^ m) := fun m =>
    (summable_weighted hc m).mul_left _
  have hD : ∀ (ν : Fin n → ℤ) (y : Fin n → ℝ),
      ‖(linForm ν).smulRight (wave (2 * π * I * c ν) (linForm ν y))‖ ≤
        (2 * π) ^ 1 * (‖c ν‖ * (1 + ∑ k, |(ν k : ℝ)|) ^ 1) := by
    intro ν y
    rw [ContinuousLinearMap.norm_smulRight_apply, norm_wave, norm_mul, norm_two_pi_I, pow_one,
      pow_one]
    calc ‖linForm ν‖ * (2 * π * ‖c ν‖) ≤ (1 + ∑ k, |(ν k : ℝ)|) * (2 * π * ‖c ν‖) :=
          mul_le_mul_of_nonneg_right (hL ν) (by positivity)
      _ = 2 * π * (‖c ν‖ * (1 + ∑ k, |(ν k : ℝ)|)) := by ring
  rw [hfun]
  refine ⟨contDiff_tsum (fun ν => (contDiff_wave (c ν)).comp (linForm ν).contDiff)
    (fun m _ => hsum m) (fun m ν x _ => norm_iteratedFDeriv_term_le (c ν) ν m x), fun x j => ?_⟩
  have h0 : Summable fun ν : Fin n → ℤ => (wave (c ν) ∘ linForm ν) x := by
    refine Summable.of_norm_bounded (hsum 0) fun ν => ?_
    simp [norm_wave]
  have hder := hasFDerivAt_tsum (hsum 1) (fun ν y => hasFDerivAt_term (c ν) ν y) hD h0 x
  have hs : Summable fun ν : Fin n → ℤ =>
      (linForm ν).smulRight (wave (2 * π * I * c ν) (linForm ν x)) :=
    Summable.of_norm_bounded (hsum 1) fun ν => hD ν x
  have hap := (ContinuousLinearMap.apply ℝ ℂ (Pi.single j (1 : ℝ))).map_tsum hs
  simp only [ContinuousLinearMap.apply_apply] at hap
  rw [hder.fderiv, hap]
  refine tsum_congr fun ν => ?_
  rw [ContinuousLinearMap.smulRight_apply, ← term_eq, linForm_apply]
  simp [Pi.single_apply, Complex.real_smul]
  ring

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorusEllipticSystemSolvable

section

@[expose] public section

open Complex Matrix
open scoped ContDiff BigOperators Real

namespace GlobalTheory
namespace TorusElliptic

def Rapid {n : ℕ} (c : (Fin n → ℤ) → ℂ) : Prop :=
  ∀ N : ℕ, ∃ C : ℝ, ∀ ν, ‖c ν‖ * (1 + ∑ k, |(ν k : ℝ)|) ^ N ≤ C

noncomputable def ch {n : ℕ} (ν : Fin n → ℤ) (x : Fin n → ℝ) : ℂ :=
  cexp (2 * π * I * ∑ k, (ν k : ℂ) * (x k : ℂ))

lemma norm_ch {n : ℕ} (ν : Fin n → ℤ) (x : Fin n → ℝ) : ‖ch ν x‖ = 1 := by
  have : (2 * π * I * ∑ k, (ν k : ℂ) * (x k : ℂ)) = ((2 * π * ∑ k, (ν k : ℝ) * x k : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [ch, this, Complex.norm_exp_ofReal_mul_I]

lemma ch_periodic {n : ℕ} (ν μ : Fin n → ℤ) (x : Fin n → ℝ) :
    ch ν (x + fun k => (μ k : ℝ)) = ch ν x := by
  have : (2 * π * I * ∑ k, (ν k : ℂ) * (((x + fun k => (μ k : ℝ)) k : ℝ) : ℂ))
      = (2 * π * I * ∑ k, (ν k : ℂ) * (x k : ℂ)) + ((∑ k, ν k * μ k : ℤ) : ℂ) * (2 * π * I) := by
    simp only [Pi.add_apply]
    push_cast
    simp only [mul_add, Finset.sum_add_distrib]
    ring
  rw [ch, this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, ch]

lemma summable_int_weight : Summable (fun j : ℤ => 1 / (1 + |(j : ℝ)|) ^ 2) := by
  have h : Summable (fun j : ℕ => 1 / (1 + (j : ℝ)) ^ 2) := by
    have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 2))
    refine this.congr fun j => ?_
    push_cast; rw [add_comm]
  refine Summable.of_nat_of_neg ?_ ?_
  · simpa using h
  · simpa using h

lemma summable_pi_weight (n : ℕ) :
    Summable (fun ν : Fin n → ℤ => ∏ k, 1 / (1 + |(ν k : ℝ)|) ^ 2) := by
  classical
  refine summable_of_sum_le (c := ∏ _k : Fin n, ∑' j : ℤ, 1 / (1 + |(j : ℝ)|) ^ 2)
    (fun ν => by positivity) fun s => ?_
  calc ∑ ν ∈ s, ∏ k, 1 / (1 + |(ν k : ℝ)|) ^ 2
      ≤ ∑ ν ∈ Fintype.piFinset (fun k => (s.image (fun ν => ν k) : Finset ℤ)),
          ∏ k, 1 / (1 + |(ν k : ℝ)|) ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun ν hν => ?_) (fun _ _ _ => by positivity)
        exact Fintype.mem_piFinset.2 fun k => Finset.mem_image_of_mem _ hν
    _ = ∏ k, ∑ j ∈ (s.image (fun ν => ν k) : Finset ℤ), 1 / (1 + |(j : ℝ)|) ^ 2 := by
        exact (Finset.prod_univ_sum (fun k => (s.image (fun ν => ν k) : Finset ℤ))
          (fun _ j => 1 / (1 + |(j : ℝ)|) ^ 2)).symm
    _ ≤ _ := by
        refine Finset.prod_le_prod₀ (fun k _ => by positivity) fun k _ => ?_
        exact summable_int_weight.sum_le_tsum _ (fun _ _ => by positivity)

lemma Rapid.summable {n : ℕ} {c : (Fin n → ℤ) → ℂ} (h : Rapid c) :
    Summable (fun ν => ‖c ν‖) := by
  obtain ⟨C, hC⟩ := h (2 * n)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ν => ?_)
    ((summable_pi_weight n).mul_left C)
  have h1 : ∏ k, (1 + |(ν k : ℝ)|) ^ 2 ≤ (1 + ∑ k, |(ν k : ℝ)|) ^ (2 * n) := by
    calc ∏ k, (1 + |(ν k : ℝ)|) ^ 2 ≤ ∏ _k : Fin n, (1 + ∑ k, |(ν k : ℝ)|) ^ 2 := by
          refine Finset.prod_le_prod₀ (fun k _ => by positivity) fun k _ => ?_
          gcongr
          exact Finset.single_le_sum (f := fun k => |(ν k : ℝ)|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ k)
      _ = _ := by simp [pow_mul]
  rw [Finset.prod_div_distrib, Finset.prod_const_one, mul_one_div, le_div_iff₀ (by positivity)]
  exact le_trans (by gcongr) (hC ν)

lemma Rapid.mul {n : ℕ} {c : (Fin n → ℤ) → ℂ} (h : Rapid c) (z : ℂ) (j : Fin n) :
    Rapid (fun ν => z * (ν j : ℂ) * c ν) := by
  intro N
  obtain ⟨C, hC⟩ := h (N + 1)
  refine ⟨‖z‖ * C, fun ν => ?_⟩
  have h1 : ‖(ν j : ℂ)‖ ≤ 1 + ∑ k, |(ν k : ℝ)| := by
    have := Finset.single_le_sum (f := fun k => |(ν k : ℝ)|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ j)
    rw [Complex.norm_intCast]
    linarith
  calc ‖z * (ν j : ℂ) * c ν‖ * (1 + ∑ k, |(ν k : ℝ)|) ^ N
      = ‖z‖ * (‖c ν‖ * ((1 + ∑ k, |(ν k : ℝ)|) ^ N * ‖(ν j : ℂ)‖)) := by
        simp only [norm_mul]; ring
    _ ≤ ‖z‖ * (‖c ν‖ * ((1 + ∑ k, |(ν k : ℝ)|) ^ N * (1 + ∑ k, |(ν k : ℝ)|))) := by gcongr
    _ ≤ ‖z‖ * C := by rw [← pow_succ]; gcongr; exact hC ν

lemma summable_ch {n : ℕ} {c : (Fin n → ℤ) → ℂ} (h : Summable (fun ν => ‖c ν‖))
    (x : Fin n → ℝ) : Summable (fun ν => c ν * ch ν x) := by
  refine Summable.of_norm ?_
  simpa [norm_ch] using h

lemma summable_symb {n : ℕ} {c : (Fin n → ℤ) → ℂ} (h : Rapid c) (q : Fin n → ℂ) :
    Summable (fun ν : Fin n → ℤ => ‖2 * π * I * (∑ k, q k * (ν k : ℂ)) * c ν‖) := by
  have : Summable (fun ν : Fin n → ℤ => ∑ k, (q k * (2 * π * I)) * (ν k : ℂ) * c ν) :=
    summable_sum fun k _ => (h.mul _ k).summable.of_norm
  refine (summable_norm_iff.2 this).congr fun ν => ?_
  congr 1
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

lemma sum_fderiv {n : ℕ} {c : (Fin n → ℤ) → ℂ} (h : Rapid c) (q : Fin n → ℂ) (x : Fin n → ℝ) :
    ∑ k, q k * fderiv ℝ (fun x : Fin n → ℝ => ∑' ν, c ν * ch ν x) x (Pi.single k 1)
      = ∑' ν, 2 * π * I * (∑ k, q k * (ν k : ℂ)) * c ν * ch ν x := by
  have h1 : ∀ k, q k * fderiv ℝ (fun x : Fin n → ℝ => ∑' ν, c ν * ch ν x) x (Pi.single k 1)
      = ∑' ν : Fin n → ℤ, (q k * (2 * π * I)) * (ν k : ℂ) * c ν * ch ν x := by
    intro k
    have := (GlobalTheory.contDiff_and_fderiv_tsum_fourier_of_rapid n c h).2 x k
    unfold ch
    rw [this, ← tsum_mul_left]
    exact tsum_congr fun ν => by ring
  simp_rw [h1]
  rw [← Summable.tsum_finsetSum fun k _ => summable_ch (h.mul _ k).summable x]
  refine tsum_congr fun ν => ?_
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

lemma symbol_lower {n m : ℕ} (p : Fin m → Fin n → ℂ)
    (hp : ∀ ξ : Fin n → ℝ, (∀ a, ∑ k, p a k * (ξ k : ℂ) = 0) → ξ = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ ν : Fin n → ℤ, ν ≠ 0 → ∃ a, ε ≤ ‖∑ k, p a k * (ν k : ℂ)‖ := by
  let L : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℂ) :=
    { toFun := fun ξ a => ∑ k, p a k * (ξ k : ℂ)
      map_add' := fun ξ η => by
        funext a; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun r ξ => by
        funext a
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Complex.real_smul, Finset.mul_sum]
        push_cast
        exact Finset.sum_congr rfl fun k _ => by ring }
  have hL : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro ξ hξ
    exact hp ξ fun a => congrFun hξ a
  obtain ⟨K, hK, hA⟩ := L.exists_antilipschitzWith hL
  have hK' : (0 : ℝ) < K := hK
  refine ⟨1 / K, by positivity, fun ν hν => ?_⟩
  by_contra hcon
  push Not at hcon
  have h1 : ‖L (fun k => (ν k : ℝ))‖ < 1 / K := by
    rw [pi_norm_lt_iff (by positivity)]
    intro a
    simpa [L] using hcon a
  have h2 := hA.le_mul_dist (fun k => (ν k : ℝ)) 0
  rw [map_zero, dist_zero_right, dist_zero_right] at h2
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hν
  have h3 : (1 : ℝ) ≤ ‖(fun k => (ν k : ℝ))‖ := by
    refine le_trans ?_ (norm_le_pi_norm (fun k => (ν k : ℝ)) k)
    rw [Real.norm_eq_abs]
    exact_mod_cast Int.one_le_abs hk
  rw [lt_div_iff₀ hK'] at h1
  linarith

end TorusElliptic


open TorusElliptic in
theorem torus_elliptic_system_solvable : ∀ (n m : ℕ) (p : Fin m → Fin n → ℂ), (∀ ξ : Fin n → ℝ, (∀ a, ∑ k, p a k * (ξ k : ℂ) = 0) → ξ = 0) → ∀ w : Fin m → (Fin n → ℝ) → ℂ, (∀ a, ContDiff ℝ ∞ (w a) ∧ (∀ (ν : Fin n → ℤ) x, w a (x + fun k => (ν k : ℝ)) = w a x)) → (∀ a b x, ∑ k, p a k * fderiv ℝ (w b) x (Pi.single k 1) = ∑ k, p b k * fderiv ℝ (w a) x (Pi.single k 1)) → ∃ (t : Fin m → ℂ) (f : (Fin n → ℝ) → ℂ), ContDiff ℝ ∞ f ∧ (∀ (ν : Fin n → ℤ) x, f (x + fun k => (ν k : ℝ)) = f x) ∧ ∀ a x, ∑ k, p a k * fderiv ℝ f x (Pi.single k 1) = w a x - t a := by
  classical
  intro n m p hp w hw hcomp
  choose c hc hwc using fun a => GlobalTheory.exists_rapid_fourierSeries_of_int_periodic n (w a) (hw a).1 (hw a).2
  have hc' : ∀ a, Rapid (c a) := hc
  have hwf : ∀ a, w a = fun x => ∑' ν, c a ν * ch ν x := fun a => funext (hwc a)
  have h2pi : (2 * π * I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have hsym : ∀ a b ν, (∑ k, p a k * (ν k : ℂ)) * c b ν = (∑ k, p b k * (ν k : ℂ)) * c a ν := by
    intro a b ν
    have hs1 := summable_symb (hc' b) (p a)
    have hs2 := summable_symb (hc' a) (p b)
    have := GlobalTheory.fourier_coeff_eq_zero_of_tsum_eq_zero_fin n (fun ν => 2 * π * I * (∑ k, p a k * (ν k : ℂ)) * c b ν
      - 2 * π * I * (∑ k, p b k * (ν k : ℂ)) * c a ν)
      (summable_norm_iff.2 (hs1.of_norm.sub hs2.of_norm)) (fun x => by
        have h := hcomp a b x
        rw [hwf a, hwf b, sum_fderiv (hc' b), sum_fderiv (hc' a)] at h
        have h' := (summable_ch hs1 x).tsum_sub (summable_ch hs2 x)
        rw [h, sub_self] at h'
        rw [← h']
        exact tsum_congr fun ν => by unfold ch; ring) ν
    apply mul_left_cancel₀ h2pi
    linear_combination this
  obtain ⟨ε, hε, hlow⟩ := symbol_lower p hp
  choose α hα using hlow
  let d : (Fin n → ℤ) → ℂ := fun ν =>
    if h : ν = 0 then 0 else c (α ν h) ν / (2 * π * I * ∑ k, p (α ν h) k * (ν k : ℂ))
  have hd : Rapid d := by
    intro N
    choose C hC using fun a => hc' a N
    have hC0 : ∀ a, 0 ≤ C a := fun a => le_trans (by positivity) (hC a 0)
    refine ⟨(∑ a, C a) / (‖(2 * π * I : ℂ)‖ * ε), fun ν => ?_⟩
    have hn : 0 < ‖(2 * π * I : ℂ)‖ := norm_pos_iff.2 h2pi
    have hS : 0 ≤ ∑ a, C a := Finset.sum_nonneg fun a _ => hC0 a
    by_cases h : ν = 0
    · simp only [d, dif_pos h, norm_zero, zero_mul]
      positivity
    · simp only [d, dif_neg h]
      rw [norm_div, norm_mul (2 * π * I : ℂ), div_mul_eq_mul_div]
      have h1 := Finset.single_le_sum (f := C) (fun a _ => hC0 a) (Finset.mem_univ (α ν h))
      have h2 := hα ν h
      have h3 := hC (α ν h) ν
      gcongr
      linarith
  refine ⟨fun a => c a 0, fun x => ∑' ν, d ν * ch ν x, (GlobalTheory.contDiff_and_fderiv_tsum_fourier_of_rapid n d hd).1, ?_, ?_⟩
  · intro μ x
    simp only [ch_periodic]
  · intro a x
    rw [sum_fderiv hd, hwf a]
    have hs := summable_ch (hc' a).summable x
    have h0 := hs.tsum_eq_add_tsum_ite 0
    have hch : ch (0 : Fin n → ℤ) x = 1 := by simp [ch]
    rw [hch, mul_one] at h0
    simp only []
    rw [h0, add_sub_cancel_left]
    refine tsum_congr fun ν => ?_
    by_cases h : ν = 0
    · simp only [d, dif_pos h, if_pos h, mul_zero, zero_mul]
    · simp only [d, dif_neg h, if_neg h]
      have h2 : (∑ k, p (α ν h) k * (ν k : ℂ)) ≠ 0 := by
        intro h0
        have := hα ν h
        rw [h0, norm_zero] at this
        linarith
      have h3 := hsym a (α ν h) ν
      congr 1
      rw [mul_div_assoc', div_eq_iff (mul_ne_zero h2pi h2)]
      linear_combination (2 * π * I) * h3

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorusEllipticSystemSolvableStatement

section

@[expose] public section

open Complex Matrix
open scoped ContDiff BigOperators Real

theorem _root_.GlobalTheory.T.exists_periodic_smooth_solution_torus_system : ∀ (n m : ℕ) (p : Fin m → Fin n → ℂ), (∀ ξ : Fin n → ℝ, (∀ a, ∑ k, p a k * (ξ k : ℂ) = 0) → ξ = 0) → ∀ w : Fin m → (Fin n → ℝ) → ℂ, (∀ a, ContDiff ℝ ∞ (w a) ∧ (∀ (ν : Fin n → ℤ) x, w a (x + fun k => (ν k : ℝ)) = w a x)) → (∀ a b x, ∑ k, p a k * fderiv ℝ (w b) x (Pi.single k 1) = ∑ k, p b k * fderiv ℝ (w a) x (Pi.single k 1)) → ∃ (t : Fin m → ℂ) (f : (Fin n → ℝ) → ℂ), ContDiff ℝ ∞ f ∧ (∀ (ν : Fin n → ℤ) x, f (x + fun k => (ν k : ℝ)) = f x) ∧ ∀ a x, ∑ k, p a k * fderiv ℝ f x (Pi.single k 1) = w a x - t a := by
  first | exact @GlobalTheory.torus_elliptic_system_solvable | exact GlobalTheory.torus_elliptic_system_solvable | (intros; apply GlobalTheory.torus_elliptic_system_solvable <;> assumption)
end
end
