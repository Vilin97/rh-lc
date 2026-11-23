module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PropAA
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Data.Nat.Choose.Multinomial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.FourierProjections.PaIPZeroRight
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.FourierProjections.PaPolyTranslate

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.FourierProjections.IteratedFDerivTailZero

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.I2.FPw

open MeasureTheory Complex

noncomputable section

variable {ι : Type} [Fintype ι]

open Classical

def expN (N : ℕ) (z : ℂ) : ℂ := ∑ n ∈ Finset.range (N + 1), z ^ n / (n.factorial : ℂ)

def gN (N : ℕ) (z : ℂ) : ℂ := cexp z - expN N z

theorem expN_hasDerivAt (N : ℕ) (z : ℂ) : HasDerivAt (expN (N + 1)) (expN N z) z := by
  induction N with
  | zero =>
    show HasDerivAt (expN 1) (expN 0 z) z
    have h0 : expN 1 = fun w => 1 + w := by
      funext w; simp [expN, Finset.sum_range_succ]
    have h1 : expN 0 z = 1 := by simp [expN]
    rw [h0, h1]
    exact (hasDerivAt_id z).const_add 1
  | succ N ih =>
    have hf : expN (N + 1 + 1) = fun w => expN (N + 1) w + w ^ (N + 1 + 1) / ((N + 1 + 1).factorial : ℂ) := by
      funext w; simp only [expN]; exact Finset.sum_range_succ _ (N + 1 + 1)
    rw [hf]
    have h2 := ih.add ((hasDerivAt_pow (N + 1 + 1) z).div_const ((N + 1 + 1).factorial : ℂ))
    refine h2.congr_deriv ?_
    have hf1 : ((N + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (N + 1)
    have hne : ((N + 1 + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (N + 1)
    simp only [expN, Finset.sum_range_succ _ (N + 1), Nat.factorial_succ (N + 1), Nat.add_sub_cancel]
    first
      | (congr 1; rw [Nat.cast_mul]; exact mul_div_mul_left _ _ hne)
      | (push_cast; field_simp; ring)
      | (push_cast; field_simp)

theorem contDiff_expN (N : ℕ) : ContDiff ℂ (⊤ : ℕ∞) (expN N) := by
  unfold expN
  first
    | exact ContDiff.sum fun n _ => (contDiff_id.pow n).div_const _
    | fun_prop

theorem contDiff_gN (N : ℕ) : ContDiff ℂ (⊤ : ℕ∞) (gN N) := by
  unfold gN
  exact Complex.contDiff_exp.sub (contDiff_expN N)

theorem deriv_gN (N : ℕ) : deriv (gN (N + 1)) = gN N := by
  funext z
  have h : HasDerivAt (gN (N + 1)) (cexp z - expN N z) z := by
    unfold gN
    exact (Complex.hasDerivAt_exp z).sub (expN_hasDerivAt N z)
  rw [h.deriv]
  rfl

theorem gN_zero (N : ℕ) : gN N 0 = 0 := by
  simp [gN, expN, Finset.sum_range_succ']

theorem iteratedDeriv_gN : ∀ i N : ℕ, i ≤ N → iteratedDeriv i (gN N) 0 = 0 := by
  intro i
  induction i with
  | zero => intro N _; rw [iteratedDeriv_zero]; exact gN_zero N
  | succ i ih =>
    intro N hN
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    rw [iteratedDeriv_succ', deriv_gN]
    exact ih M (by omega)

def ellL (q : ℕ) (a : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι →L[ℂ] ℂ :=
  ((q : ℂ) * (Real.pi : ℂ)) • innerSL ℂ a

theorem ellL_apply (q : ℕ) (a v : EuclideanSpace ℂ ι) : ellL q a v = q * Real.pi * Hf v a := by
  simp [ellL, Hf]
  left
  first
    | (rw [PiLp.inner_apply]; exact Finset.sum_congr rfl fun x _ => by simp [mul_comm])
    | (simp [PiLp.inner_apply, mul_comm]; done)
    | (simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]; done)

theorem iteratedFDeriv_tail_zero (q : ℕ) (a : EuclideanSpace ℂ ι) (N : ℕ) {P : EuclideanSpace ℂ ι → ℂ}
    (hP : ContDiff ℂ (⊤ : ℕ∞) P) {k : ℕ} (hk : k ≤ N) :
    iteratedFDeriv ℂ k (fun v => gN N (ellL q a v) * P v) 0 = 0 := by
  have hg : ContDiff ℂ (⊤ : ℕ∞) (fun v => gN N (ellL q a v)) := (contDiff_gN N).comp (ellL q a).contDiff
  have hz : ∀ i, i ≤ N → ‖iteratedFDeriv ℂ i (fun v => gN N (ellL q a v)) 0‖ = 0 := by
    intro i hi
    have h1 := (ellL q a).iteratedFDeriv_comp_right (contDiff_gN N) (0 : EuclideanSpace ℂ ι)
      (i := i) (by first | exact le_top | exact WithTop.coe_le_coe.mpr le_top | exact_mod_cast (le_top : (i : ℕ∞) ≤ ⊤) | simp)
    have h2 : iteratedFDeriv ℂ i (gN N) 0 = 0 := by
      rw [← norm_eq_zero, norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_gN i N hi, norm_zero]
    rw [map_zero, h2] at h1
    rw [show (fun v => gN N (ellL q a v)) = gN N ∘ ellL q a from rfl, h1, norm_eq_zero]
    ext m
    simp
  refine norm_le_zero_iff.mp ((norm_iteratedFDeriv_mul_le hg hP 0
    (by first | exact le_top | simp | exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))).trans_eq ?_)
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [hz i (by have := Finset.mem_range.mp hi; omega)]
  simp

theorem paD_tail_zero (q : ℕ) (a : EuclideanSpace ℂ ι) (N : ℕ) {P : EuclideanSpace ℂ ι → ℂ}
    (hP : ContDiff ℂ (⊤ : ℕ∞) P) {α : ι →₀ ℕ} (hα : α.degree ≤ N) :
    paD α (fun v => gN N (ellL q a v) * P v) = 0 := by
  unfold paD polyDeriv
  refine Finset.sum_eq_zero fun m hm => ?_
  have hmα : m = α := by
    first
      | (simp [MvPolynomial.support_monomial] at hm; exact hm)
      | (rw [MvPolynomial.support_monomial] at hm; split_ifs at hm with h
         · simp at hm
         · simpa using hm)
  subst hmα
  have hk : Multiset.card (Finsupp.toMultiset m) ≤ N := by
    rw [Finsupp.card_toMultiset]
    first
      | exact hα
      | simpa [Finsupp.degree, Finsupp.sum] using hα
  rw [iteratedFDeriv_tail_zero q a N hP hk]
  simp

end

end ReciprocityTheory.ChartRestriction.G.I2.FPw
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.FourierProjections.ExpNEllMem

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.I2.FPw

open MeasureTheory Complex Filter Topology

noncomputable section

variable {ι : Type} [Fintype ι]

open Classical

def Pf (q : ℕ) (a : EuclideanSpace ℂ ι) (F : EuclideanSpace ℂ ι → ℂ) (v : EuclideanSpace ℂ ι) : ℂ :=
  F (v - a) / cexp (q * Real.pi * Hf a a / 2)

theorem paU_eq (q : ℕ) (a : EuclideanSpace ℂ ι) (F : EuclideanSpace ℂ ι → ℂ) (v : EuclideanSpace ℂ ι) :
    paU q a F v = expN 0 0 * 0 + (expN 0 0 - 1) * 0 + cexp (ellL q a v) * Pf q a F v := by
  have h0 : expN 0 0 = 1 := by simp [expN]
  rw [h0, paU, Pf, ellL_apply, Complex.exp_sub]; ring

theorem paU_split (q : ℕ) (a : EuclideanSpace ℂ ι) (F : EuclideanSpace ℂ ι → ℂ) (N : ℕ) (v : EuclideanSpace ℂ ι) :
    paU q a F v = expN N (ellL q a v) * Pf q a F v + gN N (ellL q a v) * Pf q a F v := by
  rw [paU_eq]
  unfold gN
  ring

theorem Pf_mem {q c : ℕ} (a : EuclideanSpace ℂ ι) {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c) :
    Pf q a F ∈ paPoly c := by
  have : Pf q a F = (cexp (q * Real.pi * Hf a a / 2))⁻¹ • (fun v => F (v - a)) := by
    funext v; simp [Pf, div_eq_inv_mul]
  rw [this]; exact Submodule.smul_mem _ _ (paPoly_translate hF a)

theorem ell_mem (q : ℕ) (a : EuclideanSpace ℂ ι) : (fun v => ellL q a v) ∈ paPoly 1 := by
  have : (fun v => ellL q a v) = ((q : ℂ) * (Real.pi : ℂ)) • (fun v : EuclideanSpace ℂ ι => Hf v a) := by
    funext v; simp [ellL_apply, mul_assoc]
  rw [this]; exact Submodule.smul_mem _ _ (paPoly_Hf a)

theorem expN_ell_mem (q : ℕ) (a : EuclideanSpace ℂ ι) (N : ℕ) :
    (fun v => expN N (ellL q a v)) ∈ paPoly N := by
  have : (fun v => expN N (ellL q a v)) = ∑ n ∈ Finset.range (N + 1),
      ((n.factorial : ℂ))⁻¹ • (fun v => ellL q a v) ^ n := by
    funext v; simp [expN, Finset.sum_apply, div_eq_inv_mul]
  rw [this]
  refine Submodule.sum_mem _ fun n hn => Submodule.smul_mem _ _ ?_
  have h := paPoly_pow (ell_mem q a) n
  rw [mul_one] at h
  exact paPoly_mono (by have := Finset.mem_range.1 hn; omega) h

theorem S_mem {q c : ℕ} (a : EuclideanSpace ℂ ι) {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c) (N : ℕ) :
    (fun v => expN N (ellL q a v) * Pf q a F v) ∈ paPoly (N + c) :=
  paPoly_mul (expN_ell_mem q a N) (Pf_mem a hF)

theorem Pf_contDiff {q c : ℕ} (a : EuclideanSpace ℂ ι) {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c) :
    ContDiff ℂ (⊤ : ℕ∞) (Pf q a F) := paPoly_contDiff (Pf_mem a hF)

theorem T_contDiff {q c : ℕ} (a : EuclideanSpace ℂ ι) {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c) (N : ℕ) :
    ContDiff ℂ (⊤ : ℕ∞) (fun v => gN N (ellL q a v) * Pf q a F v) :=
  ((contDiff_gN N).comp (ellL q a).contDiff).mul (Pf_contDiff a hF)

theorem jet_eq {q c : ℕ} (a : EuclideanSpace ℂ ι) {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c) {N : ℕ}
    (hN : c ≤ N) : paJet c (paU q a F) = paJet c (fun v => expN N (ellL q a v) * Pf q a F v) := by
  have hs : paU q a F = (fun v => expN N (ellL q a v) * Pf q a F v) +
      (fun v => gN N (ellL q a v) * Pf q a F v) := by
    funext v; rw [paU_split q a F N v]; rfl
  rw [hs, paJet_add c (paPoly_contDiff (S_mem a hF N)) (T_contDiff a hF N)]
  have hT : paJet c (fun v => gN N (ellL q a v) * Pf q a F v) = 0 := by
    unfold paJet
    refine Finset.sum_eq_zero fun α hα => ?_
    rw [paD_tail_zero q a N (Pf_contDiff a hF) ((paS_deg hα).trans hN), zero_div, zero_smul]
  rw [hT, add_zero]

theorem gN_norm_le (N : ℕ) (z : ℂ) : ‖gN N z‖ ≤ Real.exp ‖z‖ := by
  have h := Complex.norm_exp_sub_sum_le_exp_norm_sub_sum z (N + 1)
  have h2 : 0 ≤ ∑ i ∈ Finset.range (N + 1), ‖z‖ ^ i / (i.factorial : ℝ) :=
    Finset.sum_nonneg fun i _ => by positivity
  unfold gN expN
  linarith

theorem gN_tendsto (z : ℂ) : Tendsto (fun N => gN N z) atTop (𝓝 0) := by
  unfold gN
  have h := (NormedSpace.expSeries_div_hasSum_exp z).tendsto_sum_nat
  rw [← Complex.exp_eq_exp_ℂ] at h
  have h2 : Tendsto (fun N => expN N z) atTop (𝓝 (cexp z)) := by
    unfold expN
    exact h.comp (tendsto_add_atTop_nat 1)
  have h3 := (tendsto_const_nhds (x := cexp z)).sub h2
  rw [sub_self] at h3
  exact h3

theorem ell_norm_le (q : ℕ) (a v : EuclideanSpace ℂ ι) : ‖ellL q a v‖ ≤ q * Real.pi * (‖a‖ * ‖v‖) := by
  unfold ellL
  rw [ContinuousLinearMap.smul_apply, norm_smul]
  have h1 : ‖((innerSL ℂ) a) v‖ ≤ ‖a‖ * ‖v‖ := norm_inner_le_norm (𝕜 := ℂ) a v
  have h2 : ‖((q : ℂ) * (Real.pi : ℂ))‖ = q * Real.pi := by
    rw [norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [h2]
  exact mul_le_mul_of_nonneg_left h1 (by positivity)

theorem tail_tendsto {q c : ℕ} (hq : 1 ≤ q) (a : EuclideanSpace ℂ ι) {F G : EuclideanSpace ℂ ι → ℂ}
    (hF : F ∈ paPoly c) (hG : G ∈ paPoly c) :
    (∀ N, Integrable (fun v => gN N (ellL q a v) * Pf q a F v * (starRingEnd ℂ) (G v) * (paW q v : ℂ))) ∧
    Tendsto (fun N => paIP q (fun v => gN N (ellL q a v) * Pf q a F v) G) atTop (𝓝 0) := by
  obtain ⟨C1, hC1, h1⟩ := paPoly_growth hF
  obtain ⟨C2, hC2, h2⟩ := paPoly_growth hG
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hb : 0 < (q : ℝ) * Real.pi / 2 := by positivity
  set κ : ℝ := ‖cexp (q * Real.pi * Hf a a / 2)‖⁻¹ with hκ
  have hκ0 : 0 ≤ κ := by positivity
  set K : ℝ := κ * C1 * C2 * (1 + ‖a‖) ^ c * Real.exp (q * Real.pi * ‖a‖ ^ 2 / 2) with hK
  have hK0 : 0 ≤ K := by positivity
  set B : EuclideanSpace ℂ ι → ℝ := fun v => K * ((1 + ‖v‖) ^ (2 * c) *
    Real.exp (-((q : ℝ) * Real.pi / 2) * ‖v‖ ^ 2)) with hB
  have hBi : Integrable B := by
    refine Integrable.const_mul (pa_integrable_of_le (by fun_prop) (2 * c) hb zero_le_one (fun v => ?_)) K
    rw [one_mul, Real.norm_of_nonneg (by positivity)]
  set Fn : ℕ → EuclideanSpace ℂ ι → ℂ := fun N v =>
    gN N (ellL q a v) * Pf q a F v * (starRingEnd ℂ) (G v) * (paW q v : ℂ) with hFn
  have hcont : ∀ N, Continuous (Fn N) := by
    intro N
    have := (T_contDiff (q := q) a hF N).continuous
    have := paPoly_continuous hG
    have := paW_continuous (ι := ι) q
    simp only [hFn]
    fun_prop
  have hbound : ∀ N v, ‖Fn N v‖ ≤ B v := by
    intro N v
    have hg := (gN_norm_le N (ellL q a v)).trans (Real.exp_le_exp.2 (ell_norm_le q a v))
    have hP : ‖Pf q a F v‖ ≤ κ * (C1 * ((1 + ‖v‖) ^ c * (1 + ‖a‖) ^ c)) := by
      rw [Pf, norm_div, div_eq_mul_inv, mul_comm, hκ]
      refine mul_le_mul_of_nonneg_left ((h1 _).trans (mul_le_mul_of_nonneg_left ?_ hC1)) hκ0
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity)
        (by nlinarith [norm_sub_le v a, norm_nonneg v, norm_nonneg a,
          mul_nonneg (norm_nonneg v) (norm_nonneg a)]) c
    have hGv := h2 v
    have hw : Real.exp (q * Real.pi * (‖a‖ * ‖v‖)) * paW q v ≤
        Real.exp (q * Real.pi * ‖a‖ ^ 2 / 2) * Real.exp (-((q : ℝ) * Real.pi / 2) * ‖v‖ ^ 2) := by
      rw [paW, ← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.2
      have : 0 ≤ (q : ℝ) * Real.pi * (‖v‖ - ‖a‖) ^ 2 := by positivity
      nlinarith
    simp only [hFn, hB, hK, norm_mul, RCLike.norm_conj, Complex.norm_real,
      Real.norm_of_nonneg (paW_pos q v).le]
    have e0 := norm_nonneg (gN N (ellL q a v))
    have e1 := norm_nonneg (Pf q a F v)
    have e2 := norm_nonneg (G v)
    have e3 := (paW_pos q v).le
    have e4 := Real.exp_pos (q * Real.pi * (‖a‖ * ‖v‖))
    calc ‖gN N (ellL q a v)‖ * ‖Pf q a F v‖ * ‖G v‖ * paW q v
        ≤ Real.exp (q * Real.pi * (‖a‖ * ‖v‖)) * (κ * (C1 * ((1 + ‖v‖) ^ c * (1 + ‖a‖) ^ c))) *
            (C2 * (1 + ‖v‖) ^ c) * paW q v := by gcongr
      _ = κ * C1 * C2 * (1 + ‖a‖) ^ c * ((1 + ‖v‖) ^ c * (1 + ‖v‖) ^ c) *
            (Real.exp (q * Real.pi * (‖a‖ * ‖v‖)) * paW q v) := by ring
      _ ≤ κ * C1 * C2 * (1 + ‖a‖) ^ c * ((1 + ‖v‖) ^ c * (1 + ‖v‖) ^ c) *
            (Real.exp (q * Real.pi * ‖a‖ ^ 2 / 2) * Real.exp (-((q : ℝ) * Real.pi / 2) * ‖v‖ ^ 2)) := by
          gcongr
      _ = _ := by rw [two_mul, pow_add]; ring
  have hint : ∀ N, Integrable (Fn N) := fun N =>
    hBi.mono' (hcont N).aestronglyMeasurable (Filter.Eventually.of_forall (hbound N))
  refine ⟨hint, ?_⟩
  have hlim : ∀ v, Tendsto (fun N => Fn N v) atTop (𝓝 0) := by
    intro v
    have := (((gN_tendsto (ellL q a v)).mul_const (Pf q a F v)).mul_const ((starRingEnd ℂ) (G v))).mul_const
      ((paW q v : ℝ) : ℂ)
    simpa only [zero_mul] using this
  have := tendsto_integral_of_dominated_convergence B (fun N => (hcont N).aestronglyMeasurable) hBi
    (fun N => Filter.Eventually.of_forall (hbound N)) (Filter.Eventually.of_forall hlim)
  rw [integral_zero] at this
  exact this

theorem gaussianInner_jet' {q c : ℕ} (hq : 1 ≤ q) (a : EuclideanSpace ℂ ι) {F G : EuclideanSpace ℂ ι → ℂ}
    (hF : F ∈ paPoly c) (hG : G ∈ paPoly c) :
    paIP q (paU q a F) G = paIP q (paJet c (paU q a F)) G := by
  obtain ⟨hTi, hT⟩ := tail_tendsto hq a hF hG
  have hD : ∀ N, c ≤ N → paIP q (paU q a F) G - paIP q (paJet c (paU q a F)) G =
      paIP q (fun v => gN N (ellL q a v) * Pf q a F v) G := by
    intro N hN
    have hS := S_mem (q := q) a hF N
    have hGS : G ∈ paPoly (N + c) := paPoly_mono (by omega) hG
    have hSi := gaussianInner_integrable hq hS hGS
    have e1 : paIP q (paU q a F) G = paIP q (fun v => expN N (ellL q a v) * Pf q a F v) G +
        paIP q (fun v => gN N (ellL q a v) * Pf q a F v) G := by
      unfold paIP
      rw [← integral_add hSi (hTi N)]
      congr 1; funext v
      rw [paU_split q a F N v]; ring
    rw [e1, jet_eq a hF hN, ← gaussianInner_polynomial_jet hq hS hG]
    ring
  have hev : (fun N => paIP q (fun v => gN N (ellL q a v) * Pf q a F v) G) =ᶠ[atTop]
      (fun _ => paIP q (paU q a F) G - paIP q (paJet c (paU q a F)) G) :=
    Filter.eventually_atTop.2 ⟨c, fun N hN => (hD N hN).symm⟩
  have h0 := tendsto_nhds_unique (hT.congr' hev) tendsto_const_nhds
  exact sub_eq_zero.1 h0.symm

end

end ReciprocityTheory.ChartRestriction.G.I2.FPw
end
end
