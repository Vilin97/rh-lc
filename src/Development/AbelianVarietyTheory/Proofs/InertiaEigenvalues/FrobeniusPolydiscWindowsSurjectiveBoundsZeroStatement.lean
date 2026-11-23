module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MooreNorm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowTEqRowS
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdditiveSystemGeneralLemmaAllOrdersStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardWindowZerosInnerEqShiftedOuterStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWindowRadii
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusWindowSeriesTermNormLeRowBoundStatement
import Mathlib.Tactic.TypeStar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalOfInvMulStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedRowCoefficientMatricesDetNormStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WindowSummedRowPowEqAdditiveSystemPowerSumStatement
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.HaveILetI
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardWindowZerosEqIntegralAdditiveSystem

section

@[expose] public section

open GlobalTheory.PMonE

namespace GlobalTheory.PMonE

theorem winPt_card (F : Type) [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (h : ℕ) (ϖ : F)
    (lam π : Fin h → F) (hπ : ∀ j, π j ≠ 0) (L U : ℕ) (M : ℕ → Matrix (Fin h) (Fin h) F)
    (hM : ∀ z, gsum (p ^ h) (L + U) M z = 0 ↔ ∀ r, rowS p ϖ lam L U (winPt p π L z) r = 0) :
    Nat.card {x : Fin h → F // (∀ j, ‖x j‖ ≤ ‖π j‖) ∧ ∀ r, rowS p ϖ lam L U x r = 0} =
      Nat.card {z : Fin h → F // Integral z ∧ gsum (p ^ h) (L + U) M z = 0} := by
  set φ := iterateFrobeniusEquiv F p (h * (L - 1)) with hφ
  have hpow : ∀ y : F, φ y = y ^ (p ^ h) ^ (L - 1) := fun y => by
    rw [hφ, iterateFrobeniusEquiv_def, pow_mul]
  have hN : (p ^ h) ^ (L - 1) ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  have hwin : ∀ z : Fin h → F, ∀ j, winPt p π L z j = π j * φ (z j) := fun z j => by
    simp only [winPt, hpow]
  symm
  refine Nat.card_congr
    { toFun := fun z => ⟨winPt p π L z.1, fun j => ?_, (hM z.1).1 z.2.2⟩
      invFun := fun x => ⟨fun j => φ.symm (x.1 j / π j), fun j => ?_, ?_⟩
      left_inv := fun z => ?_
      right_inv := fun x => ?_ }
  · rw [hwin, norm_mul, hpow, norm_pow]
    have h0 : 0 ≤ ‖z.1 j‖ := norm_nonneg _
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ h0 (z.2.1 j))
  · have hx : ‖φ (φ.symm (x.1 j / π j))‖ ≤ 1 := by
      rw [RingEquiv.apply_symm_apply, norm_div, div_le_one (norm_pos_iff.2 (hπ j))]
      exact x.2.1 j
    rw [hpow, norm_pow] at hx
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hN).1 hx
  · rw [hM]
    have : winPt p π L (fun j => φ.symm (x.1 j / π j)) = x.1 := by
      funext j
      rw [hwin, RingEquiv.apply_symm_apply, mul_div_cancel₀ _ (hπ j)]
    rw [this]; exact x.2.2
  · apply Subtype.ext
    funext j
    simp only [hwin]
    rw [mul_div_cancel_left₀ _ (hπ j), RingEquiv.symm_apply_apply]
  · apply Subtype.ext
    funext j
    simp only [hwin]
    rw [RingEquiv.apply_symm_apply, mul_div_cancel₀ _ (hπ j)]

end GlobalTheory.PMonE
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardWindowZerosEqIntegralAdditiveSystemStatement

section

@[expose] public section

open GlobalTheory.PMonE

theorem _root_.GlobalTheory.T.card_windowZeros_eq_integral_additiveSystem : ∀ (F : Type) [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (h : ℕ) (ϖ : F) (lam π : Fin h → F), (∀ j, π j ≠ 0) → ∀ (L U : ℕ) (M : ℕ → Matrix (Fin h) (Fin h) F), (∀ z, gsum (p ^ h) (L + U) M z = 0 ↔ ∀ r, rowS p ϖ lam L U (winPt p π L z) r = 0) → Nat.card {x : Fin h → F // (∀ j, ‖x j‖ ≤ ‖π j‖) ∧ ∀ r, rowS p ϖ lam L U x r = 0} = Nat.card {z : Fin h → F // Integral z ∧ gsum (p ^ h) (L + U) M z = 0} := by
  first | exact @GlobalTheory.PMonE.winPt_card | exact GlobalTheory.PMonE.winPt_card | (intros; apply GlobalTheory.PMonE.winPt_card <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormFrobeniusWindowSeriesTermMono

section

@[expose] public section

open GlobalTheory.PMonE

namespace GlobalTheory.PMonE

theorem iter_frobSymm_pow {F : Type*} [CommRing F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]
    (m : ℕ) (y : F) : (((frobeniusEquiv F p).symm)^[m] y) ^ p ^ m = y := by
  induction m generalizing y with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply, pow_succ, pow_mul, ih, frobeniusEquiv_symm_pow_p]

theorem norm_pw_mono {F : Type*} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]
    (k : ℤ) (y y' : F) (hy : ‖y‖ ≤ ‖y'‖) : ‖pw p k y‖ ≤ ‖pw p k y'‖ := by
  unfold pw
  split_ifs with hk
  · rw [norm_pow, norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hy _
  · set m := (-k).toNat
    have hN : p ^ m ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
    have e1 := iter_frobSymm_pow p m y
    have e2 := iter_frobSymm_pow p m y'
    by_contra hc
    push_neg at hc
    have := pow_lt_pow_left₀ hc (norm_nonneg _) hN
    rw [← norm_pow, ← norm_pow, e1, e2] at this
    linarith

theorem term_norm_mono : ∀ (F : Type) [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (h : ℕ) (ϖ : F) (lam π x : Fin h → F), (∀ j, ‖x j‖ ≤ ‖π j‖) → ∀ (r j : Fin h) (n : ℤ), ‖term p ϖ lam x r j n‖ ≤ ‖term p ϖ lam π r j n‖ := by
  intro F _ p _ _ _ h ϖ lam π x hx r j n
  unfold term
  rw [norm_mul, norm_mul (lam j * _)]
  exact mul_le_mul_of_nonneg_left (norm_pw_mono p _ _ _ (hx j)) (norm_nonneg _)

end GlobalTheory.PMonE
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormFrobeniusWindowSeriesTermMonoStatement

section

@[expose] public section

open GlobalTheory.PMonE

theorem _root_.GlobalTheory.T.norm_frobeniusWindowSeriesTerm_mono : ∀ (F : Type) [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (h : ℕ) (ϖ : F) (lam π x : Fin h → F), (∀ j, ‖x j‖ ≤ ‖π j‖) → ∀ (r j : Fin h) (n : ℤ), ‖term p ϖ lam x r j n‖ ≤ ‖term p ϖ lam π r j n‖ := by
  first | exact @GlobalTheory.PMonE.term_norm_mono | exact GlobalTheory.PMonE.term_norm_mono | (intros; apply GlobalTheory.PMonE.term_norm_mono <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusPolydiscWindowsSurjectiveBoundsZero

section

@[expose] public section

noncomputable section

namespace GlobalTheory.PMonE

open Finset Matrix

theorem coefB_norm {F : Type} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] {h : ℕ}
    (ϖ : F) (lam π : Fin h → F) (L U : ℕ)
    (hb : ∀ (r j : Fin h) (n : ℤ), ‖term p ϖ lam π r j n‖ ≤ ‖lam r * π r ^ p ^ (r : ℕ)‖ ∧
      (0 < n → ‖term p ϖ lam π r j n‖ < ‖lam r * π r ^ p ^ (r : ℕ)‖)) :
    (∀ m r j, ‖coefB p ϖ lam π L U m r j‖ ≤ 1) ∧ (∀ m, L < m → ∀ r j, ‖coefB p ϖ lam π L U m r j‖ < 1) := by
  have key : ∀ m r j, ‖coefB p ϖ lam π L U m r j‖ ≤ 1 ∧ (L < m → ‖coefB p ϖ lam π L U m r j‖ < 1) := by
    intro m r j
    simp only [coefB, Matrix.of_apply]
    split_ifs with hm
    · rw [norm_pow, norm_div]
      obtain ⟨h1, h2⟩ := hb r j ((m : ℤ) - L)
      have hpos : p ^ (h - (r : ℕ)) ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
      rcases eq_or_lt_of_le (norm_nonneg (lam r * π r ^ p ^ (r : ℕ))) with hc | hc
      · rw [← hc, div_zero, zero_pow hpos]
        exact ⟨zero_le_one, fun _ => zero_lt_one⟩
      · refine ⟨pow_le_one₀ (div_nonneg (norm_nonneg _) hc.le) ((div_le_one hc).2 h1), fun hLm => ?_⟩
        exact pow_lt_one₀ (div_nonneg (norm_nonneg _) hc.le) ((div_lt_one hc).2 (h2 (by omega))) hpos
    · simp
  exact ⟨fun m r j => (key m r j).1, fun m hm r j => (key m r j).2 hm⟩

theorem gsum_mul_left {F : Type} [NormedField F] {m : Type} [Fintype m] (q D : ℕ) (A : Matrix m m F)
    (B : ℕ → Matrix m m F) (z : m → F) :
    gsum q D (fun n => A * B n) z = A *ᵥ gsum q D B z := by
  simp only [gsum, Matrix.mulVec_sum, Matrix.mulVec_mulVec]

theorem normalize {F : Type} [NormedField F] [IsUltrametricDist F] (p : ℕ) [Fact p.Prime] [CharP F p]
    [PerfectRing F p] {h : ℕ} (ϖ : F) (hϖ : ϖ ≠ 0) (lam π : Fin h → F) (hlam : ∀ j, lam j ≠ 0)
    (hπ : ∀ j, π j ≠ 0) (hanti : Antitone (fun j => ‖lam j‖)) (horth : Orth p lam) (L U : ℕ) (hL : 1 ≤ L)
    (hb : ∀ (r j : Fin h) (n : ℤ), ‖term p ϖ lam π r j n‖ ≤ ‖lam r * π r ^ p ^ (r : ℕ)‖ ∧
      (0 < n → ‖term p ϖ lam π r j n‖ < ‖lam r * π r ^ p ^ (r : ℕ)‖)) :
    ∃ M : ℕ → Matrix (Fin h) (Fin h) F, Normal L M ∧ (M 0).det ≠ 0 ∧
      ∃ Φ : (Fin h → F) → (Fin h → F), (∀ b, (∀ r, ‖b r‖ ≤ ‖lam r * π r ^ p ^ (r : ℕ)‖) → Integral (Φ b)) ∧
        Φ 0 = 0 ∧ ∀ z b, gsum (p ^ h) (L + U) M z = Φ b ↔ ∀ r, rowS p ϖ lam L U (winPt p π L z) r = b r := by
  set B := coefB p ϖ lam π L U with hBdef
  obtain ⟨hB1, hB2⟩ := coefB_norm p ϖ lam π L U hb
  obtain ⟨hdet, hdet0⟩ := GlobalTheory.T.normalizedRowCoefficientMatrices_det_norm F p h ϖ hϖ lam π hlam hπ hanti horth L U
  obtain ⟨hN, hinv⟩ := GlobalTheory.T.normal_inv_mul_and_norm_inv_le_one F (Fin h) L B hB1 hB2 hdet
  have hdne : (B L).det ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hdet
    exact zero_ne_one hdet
  have hdu : IsUnit (B L).det := isUnit_iff_ne_zero.2 hdne
  have hc : ∀ r, lam r * π r ^ p ^ (r : ℕ) ≠ 0 := fun r => mul_ne_zero (hlam r) (pow_ne_zero _ (hπ r))
  let nb : (Fin h → F) → (Fin h → F) := fun b r => (b r / (lam r * π r ^ p ^ (r : ℕ))) ^ p ^ (h - (r : ℕ))
  refine ⟨fun n => (B L)⁻¹ * B n, hN, ?_, fun b => (B L)⁻¹ *ᵥ nb b, ?_, ?_, ?_⟩
  · rw [Matrix.det_mul]
    exact mul_ne_zero (Matrix.isUnit_nonsing_inv_det (B L) hdu).ne_zero hdet0
  · intro b hbb i
    simp only [Matrix.mulVec, dotProduct]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
    intro j _
    rw [norm_mul]
    have h1 : ‖nb b j‖ ≤ 1 := by
      simp only [nb]
      rw [norm_pow, norm_div]
      exact pow_le_one₀ (div_nonneg (norm_nonneg _) (norm_nonneg _))
        ((div_le_one (norm_pos_iff.2 (hc j))).2 (hbb j))
    exact mul_le_one₀ (hinv i j) (norm_nonneg _) h1
  · have : nb 0 = 0 := by
      funext r
      simp only [nb, Pi.zero_apply, zero_div]
      exact zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
    simp only [this, Matrix.mulVec_zero]
  · intro z b
    rw [gsum_mul_left]
    constructor
    · intro H r
      have H2 : gsum (p ^ h) (L + U) B z = nb b := by
        have := congrArg (fun v => B L *ᵥ v) H
        simpa only [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdu, Matrix.one_mulVec] using this
      have H3 := congrFun H2 r
      rw [← GlobalTheory.T.windowSummedRow_pow_eq_additiveSystemPowerSum F p h ϖ lam π L U hL z r] at H3
      have H4 := (iterateFrobenius_inj F p (h - (r : ℕ))).eq_iff.1 (by simpa [iterateFrobenius_def] using H3)
      exact (div_left_inj' (hc r)).1 H4
    · intro H
      have H2 : gsum (p ^ h) (L + U) B z = nb b := by
        funext r
        rw [← GlobalTheory.T.windowSummedRow_pow_eq_additiveSystemPowerSum F p h ϖ lam π L U hL z r, H r]
      rw [H2]

theorem winThm : WinThm := by
  intro F _ _ _ _ p _ _ _ h ϖ hh hϖ lam hlam hanti horth hlt
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
  obtain ⟨π, hπ, hrel1, hrel2⟩ := exists_window_radii F p k ϖ hϖ lam hlam hanti hlt
  have hp := (Fact.out : p.Prime)
  have hϖ0 : ϖ ≠ 0 := by
    have : (0 : ℝ) < ‖ϖ‖ := by
      rw [hϖ]
      exact inv_pos.2 (by exact_mod_cast hp.pos)
    exact norm_pos_iff.1 this
  have hbd := GlobalTheory.T.frobeniusWindowSeriesTerm_norm_le_rowBound F p k ϖ hϖ lam π hlam hanti hlt hπ hrel1 hrel2
  have hb : ∀ (r j : Fin (k + 1)) (n : ℤ), ‖term p ϖ lam π r j n‖ ≤ ‖lam r * π r ^ p ^ (r : ℕ)‖ ∧
      (0 < n → ‖term p ϖ lam π r j n‖ < ‖lam r * π r ^ p ^ (r : ℕ)‖) :=
    fun r j n => ⟨(hbd r j n).1, (hbd r j n).2.1⟩
  have hπ0 : ∀ j, π j ≠ 0 := fun j => (hπ j).1
  have hGL := GlobalTheory.T.additiveSystem_generalLemma_all_orders
  refine ⟨fun j => ‖π j‖, fun r => ‖lam r * π r ^ p ^ (r : ℕ)‖, 2,
    fun j => ⟨norm_pos_iff.2 (hπ j).1, (hπ j).2⟩,
    fun r => norm_pos_iff.2 (mul_ne_zero (hlam r) (pow_ne_zero _ (hπ r).1)), ?_, ?_, ?_⟩
  · intro x hx r j n
    have hm := GlobalTheory.T.norm_frobeniusWindowSeriesTerm_mono F p (k + 1) ϖ lam π x hx r j n
    exact ⟨hm.trans (hbd r j n).1, fun hn => hm.trans ((hbd r j n).2.2 (by exact_mod_cast hn))⟩
  · intro b hbnd
    obtain ⟨M, hM, _, Φ, hΦ, _, hiff⟩ :=
      normalize p ϖ hϖ0 lam π hlam hπ0 hanti horth 2 2 (by norm_num) hb
    obtain ⟨z, hz, hzb⟩ := (hGL 2).1 F p (Fin (k + 1)) (k + 1) (2 + 2) (by omega) (by omega) M hM (Φ b)
      (hΦ b hbnd)
    refine ⟨winPt p π 2 z, ?_, fun r => ?_⟩
    · intro j
      simp only [winPt]
      rw [norm_mul, norm_pow]
      exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) (hz j))
    · rw [rowT_eq_rowS]
      exact (hiff z b).1 hzb r
  · obtain ⟨M, hM, hM0, Φ, _, hΦ0, hiff⟩ :=
      normalize p ϖ hϖ0 lam π hlam hπ0 hanti horth 2 2 (by norm_num) hb
    obtain ⟨M', hM', hM0', Φ', _, hΦ0', hiff'⟩ :=
      normalize p ϖ hϖ0 lam π hlam hπ0 hanti horth (2 - 1) (2 + 1) (by norm_num) hb
    have c1 := (hGL 2).2 F p (Fin (k + 1)) (k + 1) (2 + 2) (by omega) (by omega) M hM hM0
    have c2 := (hGL (2 - 1)).2 F p (Fin (k + 1)) (k + 1) ((2 - 1) + (2 + 1)) (by omega) (by omega) M' hM' hM0'
    have d1 := GlobalTheory.T.card_windowZeros_eq_integral_additiveSystem F p (k + 1) ϖ lam π hπ0 2 2 M (fun z => by simpa [hΦ0] using hiff z 0)
    have d2 := GlobalTheory.T.card_windowZeros_eq_integral_additiveSystem F p (k + 1) ϖ lam π hπ0 (2 - 1) (2 + 1) M' (fun z => by simpa [hΦ0'] using hiff' z 0)
    have e1 := GlobalTheory.T.card_windowZeros_inner_eq_shifted_outer F p (k + 1) 2 ϖ hϖ0 (by norm_num) lam π
    have hq1 : 1 < p ^ (k + 1) := Nat.one_lt_pow (by omega) hp.one_lt
    have cS : Nat.card {x : Fin (k + 1) → F // (∀ j, ‖x j‖ ≤ ‖π j‖) ∧ ∀ r, rowS p ϖ lam 2 2 x r = 0} =
        (p ^ (k + 1)) ^ ((k + 1) * 2) := by
      rw [d1, c1, Fintype.card_fin]
    have cI : Nat.card {x : Fin (k + 1) → F // (∀ j, ‖x j‖ ≤ ‖π j‖ ^ p ^ (k + 1)) ∧
        ∀ r, rowT p ϖ lam 2 x r = 0} = (p ^ (k + 1)) ^ ((k + 1) * (2 - 1)) := by
      rw [e1, d2, c2, Fintype.card_fin]
    by_contra hcon
    have hsub : ∀ x : {x : Fin (k + 1) → F // (∀ j, ‖x j‖ ≤ ‖π j‖) ∧ ∀ r, rowS p ϖ lam 2 2 x r = 0},
        ∀ j, ‖x.1 j‖ ≤ ‖π j‖ ^ p ^ (k + 1) := by
      intro x
      by_contra hx
      push_neg at hx
      exact hcon ⟨x.1, x.2.1, hx, x.2.2⟩
    haveI : Finite {x : Fin (k + 1) → F // (∀ j, ‖x j‖ ≤ ‖π j‖ ^ p ^ (k + 1)) ∧
        ∀ r, rowT p ϖ lam 2 x r = 0} := Nat.finite_of_card_ne_zero (by rw [cI]; positivity)
    have hle := Nat.card_le_card_of_injective
      (fun x : {x : Fin (k + 1) → F // (∀ j, ‖x j‖ ≤ ‖π j‖) ∧ ∀ r, rowS p ϖ lam 2 2 x r = 0} =>
        (⟨x.1, hsub x, x.2.2⟩ : {x : Fin (k + 1) → F // (∀ j, ‖x j‖ ≤ ‖π j‖ ^ p ^ (k + 1)) ∧
          ∀ r, rowT p ϖ lam 2 x r = 0}))
      (fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab))
    rw [cS, cI] at hle
    exact absurd hle (not_le.2 (Nat.pow_lt_pow_right hq1 (by omega)))

end GlobalTheory.PMonE
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusPolydiscWindowsSurjectiveBoundsZeroStatement

section

@[expose] public section

open GlobalTheory.PMonE

theorem _root_.GlobalTheory.T.frobenius_polydisc_windows_surjective_bounds_zero : WinThm := by
  first | exact @GlobalTheory.PMonE.winThm | exact GlobalTheory.PMonE.winThm | (intros; apply GlobalTheory.PMonE.winThm <;> assumption)
end
end
