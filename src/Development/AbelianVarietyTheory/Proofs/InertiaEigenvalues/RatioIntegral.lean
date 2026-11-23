module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisSubUnitLeDigit
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisValuationSubEqIntMulRadiusStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisRadiusPosDefiniteStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisSubUnitLeDigit
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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ISupMonomialHolderLogConvexStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGaussGCTarget
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisFrobeniusFixedEqPadicInt
import Mathlib.Algebra.Order.Star.Real
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisLoc
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisMulEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaussNormExtensionAcris
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltNormUltrametricEqZero
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Kernel

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisSubUnitLeDigitStatement

section

@[expose] public section

open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.gaussNormAcris_sub_unit_le_digit : ∀ (l : ℕ) [Fact l.Prime] (h s : ℕ), s < h → ∀ w w' : Formalism.Per.Acris l, (φc l)^[h] w' = (l : Formalism.Per.Acris l) ^ s * w' → w' ≠ 0 → φc l w * w' = w * φc l w' → (∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ w = gC l ρ w') → ∃ c : ℤ_[l], IsUnit c ∧ ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ (w - zc l c * w') ≤ ρ * gC l ρ w' := by
  first | exact @GlobalTheory.PMon.Gauss.one_digit | exact GlobalTheory.PMon.Gauss.one_digit | (intros; apply GlobalTheory.PMon.Gauss.one_digit <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RatioProportionalTarget

section

@[expose] public section

open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon.Gauss

namespace RatioProp

variable {l : ℕ} [Fact l.Prime]

theorem one_lt_l : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt

theorem inv_l_pos : (0 : ℝ) < (l : ℝ)⁻¹ := inv_pos.2 (by linarith [(one_lt_l : (1 : ℝ) < l)])

theorem inv_l_lt_one : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ one_lt_l

theorem rho_pos {ρ : ℝ} (h0 : (l : ℝ)⁻¹ ≤ ρ) : 0 < ρ := lt_of_lt_of_le inv_l_pos h0

theorem gauss {ρ : ℝ} (h0 : (l : ℝ)⁻¹ ≤ ρ) (h1 : ρ < 1) : IsGauss l ρ (gC l ρ) :=
  isGauss_gC_target l ρ h0 h1

theorem phi_zc (c : ℤ_[l]) : φc l (zc l c) = zc l c :=
  (GlobalTheory.MemLoc.PhiFix.phiA_alg l _).trans (congrArg _ (GlobalTheory.MemLoc.PhiFix.φA_zA l c))

theorem iter_lpow (m j : ℕ) (x : Formalism.Per.Acris l) :
    (φc l)^[m] ((l : Formalism.Per.Acris l) ^ j * x) = (l : Formalism.Per.Acris l) ^ j * (φc l)^[m] x := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_mul, map_pow, map_natCast]

theorem gC_zero {ρ : ℝ} (h0 : (l : ℝ)⁻¹ ≤ ρ) (h1 : ρ < 1) : gC l ρ 0 = 0 := by
  have hm := (gauss h0 h1).2.2.2.1 0 (l : Formalism.Per.Acris l)
  rw [zero_mul, (GlobalTheory.T.gaussNormAcris_basic_values l ρ h0 h1).2.1] at hm
  have e : gC l ρ 0 * (1 - ρ) = 0 := by linear_combination hm
  rcases mul_eq_zero.1 e with h | h
  · exact h
  · exact absurd h (by linarith)

theorem gC_lpow {ρ : ℝ} (h0 : (l : ℝ)⁻¹ ≤ ρ) (h1 : ρ < 1) (m : ℕ) (x : Formalism.Per.Acris l) :
    gC l ρ ((l : Formalism.Per.Acris l) ^ m * x) = ρ ^ m * gC l ρ x := by
  induction m with
  | zero => rw [pow_zero, one_mul, pow_zero, one_mul]
  | succ m ih =>
    rw [pow_succ', mul_assoc, (gauss h0 h1).2.2.2.1, (GlobalTheory.T.gaussNormAcris_basic_values l ρ h0 h1).2.1, ih, pow_succ']
    ring

theorem lpow_ne_zero {x : Formalism.Per.Acris l} (hx : x ≠ 0) (m : ℕ) : (l : Formalism.Per.Acris l) ^ m * x ≠ 0 := by
  intro e
  have h := gC_lpow le_rfl inv_l_lt_one m x
  rw [e, gC_zero le_rfl inv_l_lt_one] at h
  have hp := GlobalTheory.T.gaussNormAcrisRadius_pos_definite l x hx _ le_rfl inv_l_lt_one
  have : (0 : ℝ) < (l : ℝ)⁻¹ ^ m * gC l (l : ℝ)⁻¹ x := mul_pos (pow_pos inv_l_pos m) hp
  linarith

theorem pert {ρ : ℝ} (h0 : (l : ℝ)⁻¹ ≤ ρ) (h1 : ρ < 1) (W W' : Formalism.Per.Acris l) (c y : ℤ_[l]) (k : ℕ) :
    gC l ρ (W - zc l (c + (l : ℤ_[l]) ^ k * y) * W') ≤ max (gC l ρ (W - zc l c * W')) (ρ ^ k * gC l ρ W') := by
  have e : W - zc l (c + (l : ℤ_[l]) ^ k * y) * W' =
      (W - zc l c * W') + -((l : Formalism.Per.Acris l) ^ k * (zc l y * W')) := by
    simp only [map_add (f := _), map_mul, map_pow, map_natCast]
    ring
  rw [e]
  refine ((gauss h0 h1).2.1 _ _).trans (max_le_max le_rfl ?_)
  rw [(gauss h0 h1).2.2.1, gC_lpow h0 h1, (gauss h0 h1).2.2.2.1]
  exact mul_le_mul_of_nonneg_left
    (mul_le_of_le_one_left ((gauss h0 h1).1 _).1 ((gauss h0 h1).1 _).2) (pow_nonneg (rho_pos h0).le _)

def digitSet (W W' : Formalism.Per.Acris l) (k : ℕ) : Set ℤ_[l] :=
  {c | ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ (W - zc l c * W') ≤ ρ ^ k * gC l ρ W'}

theorem isClosed_digitSet (W W' : Formalism.Per.Acris l) (k : ℕ) : IsClosed (digitSet W W' k) := by
  rw [← isOpen_compl_iff, Metric.isOpen_iff]
  intro c hc
  simp only [digitSet, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_le] at hc
  obtain ⟨ρ, h0, h1, hlt⟩ := hc
  refine ⟨(l : ℝ) ^ (-(k : ℤ)), zpow_pos (by linarith [(one_lt_l : (1 : ℝ) < l)]) _, fun c' hc' hT => ?_⟩
  rw [Metric.mem_ball, dist_eq_norm] at hc'
  have hmem : c - c' ∈ Ideal.span {(l : ℤ_[l]) ^ k} := by
    rw [← PadicInt.norm_le_pow_iff_mem_span_pow, norm_sub_rev]
    exact hc'.le
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hmem
  have hp := pert h0 h1 W W' c' y k
  have e : c' + (l : ℤ_[l]) ^ k * y = c := by rw [mul_comm, hy]; ring
  rw [e] at hp
  exact absurd (hp.trans (max_le (hT ρ h0 h1) le_rfl)) (not_le.2 hlt)

theorem gC_eq_of_vr {V W' : Formalism.Per.Acris l} (hV : V ≠ 0) (hW' : W' ≠ 0) (n : ℤ)
    (hn : ∀ r ∈ Set.Ioc (0 : ℝ) 1, vr l r V - vr l r W' = n * r) {ρ : ℝ} (h0 : (l : ℝ)⁻¹ ≤ ρ) (h1 : ρ < 1) :
    gC l ρ V = ρ ^ n * gC l ρ W' := by
  apply GlobalTheory.PMon.Gauss.gC_eq_zpow_mul_of_vr <;> assumption

theorem digit_step {h s : ℕ} (hs : s < h) {W W' : Formalism.Per.Acris l}
    (he : (φc l)^[h] W' = (l : Formalism.Per.Acris l) ^ s * W') (hW' : W' ≠ 0)
    (hr : φc l W * W' = W * φc l W') (k : ℕ) (c : ℤ_[l]) (hc : c ∈ digitSet W W' k) :
    (digitSet W W' (k + 1)).Nonempty := by
  have hrV : φc l (W - zc l c * W') * W' = (W - zc l c * W') * φc l W' := by
    rw [map_sub, map_mul, phi_zc]
    linear_combination hr
  by_cases hV0 : W - zc l c * W' = 0
  · refine ⟨c, fun ρ h0 h1 => ?_⟩
    rw [hV0, gC_zero h0 h1]
    exact mul_nonneg (pow_nonneg (rho_pos h0).le _) ((gauss h0 h1).1 _).1
  obtain ⟨n, hn⟩ := GlobalTheory.T.acrisValuation_sub_eq_int_mul_radius l h s hs _ W' he hV0 hW' hrV
  have hg : ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ (W - zc l c * W') = ρ ^ n * gC l ρ W' :=
    fun ρ h0 h1 => gC_eq_of_vr hV0 hW' n hn h0 h1
  have hW0 := GlobalTheory.T.gaussNormAcrisRadius_pos_definite l W' hW' _ le_rfl inv_l_lt_one
  have hk : (k : ℤ) ≤ n := by
    have a := hc _ le_rfl inv_l_lt_one
    rw [hg _ le_rfl inv_l_lt_one] at a
    have b := le_of_mul_le_mul_right a hW0
    rw [← zpow_natCast] at b
    exact (zpow_le_zpow_iff_right_of_lt_one₀ inv_l_pos inv_l_lt_one).1 b
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m := ⟨n.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  have hkm : k ≤ m := by exact_mod_cast hk
  obtain ⟨u, -, hu⟩ := GlobalTheory.T.gaussNormAcris_sub_unit_le_digit l h s hs (W - zc l c * W') ((l : Formalism.Per.Acris l) ^ m * W')
    (by rw [iter_lpow, he]; ring) (lpow_ne_zero hW' m)
    (by rw [map_mul, map_pow, map_natCast]; linear_combination (l : Formalism.Per.Acris l) ^ m * hrV)
    (fun ρ h0 h1 => by rw [hg ρ h0 h1, gC_lpow h0 h1, zpow_natCast])
  refine ⟨c + u * (l : ℤ_[l]) ^ m, fun ρ h0 h1 => ?_⟩
  have e : W - zc l (c + u * (l : ℤ_[l]) ^ m) * W' =
      (W - zc l c * W') - zc l u * ((l : Formalism.Per.Acris l) ^ m * W') := by
    simp only [map_add (f := _), map_mul, map_pow, map_natCast]
    ring
  rw [e]
  refine (hu ρ h0 h1).trans ?_
  rw [gC_lpow h0 h1, ← mul_assoc, ← pow_succ']
  exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (rho_pos h0).le h1.le (by omega))
    ((gauss h0 h1).1 _).1

theorem eq_zc_mul {h s : ℕ} (hs : s < h) {W W' : Formalism.Per.Acris l}
    (he : (φc l)^[h] W' = (l : Formalism.Per.Acris l) ^ s * W') (hW' : W' ≠ 0)
    (hr : φc l W * W' = W * φc l W')
    (hg : ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ W = gC l ρ W') :
    ∃ c : ℤ_[l], W = zc l c * W' := by
  have hmono : ∀ i, digitSet W W' (i + 1) ⊆ digitSet W W' i := fun i c hc ρ h0 h1 =>
    (hc ρ h0 h1).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_of_le_one (rho_pos h0).le h1.le (Nat.le_succ i)) ((gauss h0 h1).1 _).1)
  have hne : ∀ i, (digitSet W W' i).Nonempty := by
    intro i
    induction i with
    | zero => exact ⟨0, fun ρ h0 h1 => by rw [map_zero, zero_mul, sub_zero, pow_zero, one_mul, hg ρ h0 h1]⟩
    | succ i ih =>
      obtain ⟨c, hc⟩ := ih
      exact digit_step hs he hW' hr i c hc
  obtain ⟨c, hc⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed _ hmono hne
    (isCompact_univ.of_isClosed_subset (isClosed_digitSet W W' 0) (Set.subset_univ _))
    (isClosed_digitSet W W')
  rw [Set.mem_iInter] at hc
  refine ⟨c, ?_⟩
  by_contra hne'
  have hpos := GlobalTheory.T.gaussNormAcrisRadius_pos_definite l (W - zc l c * W') (sub_ne_zero.2 hne') _ le_rfl inv_l_lt_one
  have hlim : Filter.Tendsto (fun i : ℕ => (l : ℝ)⁻¹ ^ i * gC l (l : ℝ)⁻¹ W') Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one inv_l_pos.le inv_l_lt_one).mul_const
      (gC l (l : ℝ)⁻¹ W')
  have := ge_of_tendsto' hlim (fun i => hc i _ le_rfl inv_l_lt_one)
  linarith

end RatioProp


open RatioProp in
theorem ratio_proportional_target : ∀ (l : ℕ) [Fact l.Prime] (h s : ℕ), s < h → ∀ w w' : Formalism.Per.Acris l,
    (φc l)^[h] w = (l : Formalism.Per.Acris l) ^ s * w → (φc l)^[h] w' = (l : Formalism.Per.Acris l) ^ s * w' → w' ≠ 0 →
    φc l w * w' = w * φc l w' → ∃ c d : ℤ_[l], c ≠ 0 ∧ zc l c * w = zc l d * w' := by
  intro l _ h s hs w w' _ he' hw' hr
  by_cases hw : w = 0
  · exact ⟨1, 0, one_ne_zero, by rw [hw, mul_zero, map_zero, zero_mul]⟩
  obtain ⟨n, hn⟩ := GlobalTheory.T.acrisValuation_sub_eq_int_mul_radius l h s hs w w' he' hw hw' hr
  have hg : ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ w = ρ ^ n * gC l ρ w' :=
    fun ρ h0 h1 => gC_eq_of_vr hw hw' n hn h0 h1
  rcases le_or_gt 0 n with hn0 | hn0
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m := ⟨n.toNat, (Int.toNat_of_nonneg hn0).symm⟩
    obtain ⟨c, hc⟩ := eq_zc_mul hs (W := w) (W' := (l : Formalism.Per.Acris l) ^ m * w')
      (by rw [iter_lpow, he']; ring) (lpow_ne_zero hw' m)
      (by rw [map_mul, map_pow, map_natCast]; linear_combination (l : Formalism.Per.Acris l) ^ m * hr)
      (fun ρ h0 h1 => by rw [hg ρ h0 h1, gC_lpow h0 h1, zpow_natCast])
    refine ⟨1, c * (l : ℤ_[l]) ^ m, one_ne_zero, ?_⟩
    rw [map_one, one_mul, hc, map_mul, map_pow, map_natCast]
    ring
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = -n := ⟨(-n).toNat, Int.toNat_of_nonneg (by omega)⟩
    obtain ⟨c, hc⟩ := eq_zc_mul hs (W := (l : Formalism.Per.Acris l) ^ m * w) (W' := w') he' hw'
      (by rw [map_mul, map_pow, map_natCast]; linear_combination (l : Formalism.Per.Acris l) ^ m * hr)
      (fun ρ h0 h1 => by
        rw [gC_lpow h0 h1, hg ρ h0 h1, ← mul_assoc, ← zpow_natCast, hm,
          ← zpow_add₀ (ne_of_gt (rho_pos h0)), neg_add_cancel, zpow_zero, one_mul])
    refine ⟨(l : ℤ_[l]) ^ m, c, pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero), ?_⟩
    rw [map_pow, map_natCast, hc]

end GlobalTheory.PMon.Gauss
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TmSubOneNeZeroPt

section

@[expose] public section

noncomputable section

open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

namespace GlobalTheory.PMon.Trans

variable (l : ℕ) [Fact l.Prime]

theorem map_ne_zero_pt : ∀ y : Formalism.Per.Ainf l, y ≠ 0 →
    algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) y ≠ 0 := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hr1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl
  obtain ⟨N, h01, -, -, hmul, hA⟩ := GlobalTheory.GaussExt.exists_gauss_acris l _ le_rfl hr1
  have hbdd : ∀ a : Formalism.Per.Ainf l, BddAbove (Set.range fun n : ℕ =>
      ‖(((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * ((l : ℝ)⁻¹) ^ n) := by
    intro a
    refine ⟨1, ?_⟩
    rintro _ ⟨n, rfl⟩
    have h1 : ‖(((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ≤ 1 :=
      (GlobalTheory.RingBasics.mem_OC _).1 ((a.coeff n).untilt).2
    have h2 : ‖(((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) ≤ 1 :=
      Real.rpow_le_one (norm_nonneg _) h1 (by positivity)
    have h3 : ((l : ℝ)⁻¹) ^ n ≤ 1 := pow_le_one₀ (by positivity) hr1.le
    calc _ ≤ 1 * 1 := mul_le_mul h2 h3 (by positivity) zero_le_one
      _ = 1 := one_mul 1
  have hpos : ∀ a : Formalism.Per.Ainf l, a ≠ 0 → 0 < N (algebraMap _ _ a) := by
    intro a ha0
    obtain ⟨n, ha⟩ : ∃ n, a.coeff n ≠ 0 := by
      by_contra hc
      apply ha0
      refine WittVector.ext fun n => ?_
      rw [WittVector.zero_coeff]
      by_contra hn
      exact hc ⟨n, hn⟩
    rw [hA]
    refine lt_of_lt_of_le ?_ (le_ciSup (hbdd a) n)
    have hne : (((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l]) ≠ 0 := by
      intro h
      apply ha
      refine (GlobalTheory.TiltAbs.untilt_ultrametric_definite l (a.coeff n) 0).2 ?_
      exact Subtype.ext h
    have hl0 : (0 : ℝ) < l := lt_trans one_pos hl
    exact mul_pos (Real.rpow_pos_of_pos (norm_pos_iff.2 hne) _) (pow_pos (inv_pos.2 hl0) _)
  have hN0 : N 0 = 0 := by
    have hz : ∀ n : ℕ, (0 : ℝ) ^ ((1 : ℝ) / (l : ℝ) ^ n) = 0 := fun n => Real.zero_rpow (by positivity)
    rw [← map_zero (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l)), hA]
    have hz' : ∀ n : ℕ, (0 : ℝ) ^ (((l : ℝ) ^ n)⁻¹) = 0 := fun n => Real.zero_rpow (by positivity)
    simp [hz, hz', GlobalTheory.GaussExt.untilt_zero]
  intro y hy h0
  have := hpos y hy
  rw [h0, hN0] at this
  exact lt_irrefl _ this

theorem tm_sub_one_ne_zero_pt (e : Formalism.Per.Fl l) (he : e ≠ 1) : (Formalism.Per.tm e - 1 : Formalism.Per.Ainf l) ≠ 0 := by
  intro h
  apply he
  have h' := congrArg (fun w : Formalism.Per.Ainf l => w.coeff 0) (sub_eq_zero.1 h)
  simpa using h'

theorem one_ne_zero_pt : (1 : Formalism.Per.Ainf l) ≠ 0 := by
  intro h
  have h' := congrArg (fun w : Formalism.Per.Ainf l => w.coeff 0) h
  simp at h'

theorem map_prod_ne_zero_pt : ∀ s : List (Formalism.Per.Fl l), (∀ e ∈ s, e ≠ 1) →
    algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) (s.map fun e => Formalism.Per.tm e - 1).prod ≠ 0 := by
  intro s
  induction s with
  | nil =>
    intro _
    rw [List.map_nil, List.prod_nil]
    exact map_ne_zero_pt l 1 (one_ne_zero_pt l)
  | cons e s ih =>
    intro hs
    rw [List.map_cons, List.prod_cons, map_mul]
    intro h
    exact (GlobalTheory.T.acris_eq_zero_or_eq_zero_of_mul_eq_zero l _ _ h).elim
      (map_ne_zero_pt l _ (tm_sub_one_ne_zero_pt l e (hs e List.mem_cons_self)))
      (ih fun e' he' => hs e' (List.mem_cons_of_mem _ he'))

end GlobalTheory.PMon.Trans

theorem GlobalTheory.PMon.Trans.acris_bcris : ∀ (l : ℕ) [Fact l.Prime], Function.Injective (algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l)) ∧ (∀ x : Formalism.Per.Acris l, Formalism.Per.φB l (algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) x) = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) (φc l x)) ∧ ∀ c : ℤ_[l], algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) (zc l c) = Formalism.Per.zB l c := by
  intro l _
  refine ⟨?_, fun x => GlobalTheory.CrisMaps.φB_phiA l x, fun c => (GlobalTheory.RingIface.zB_alg l c).symm⟩
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨e, he, hne⟩ := GlobalTheory.CrisLoc.exists_root_ne_one l
  obtain ⟨n, h⟩ := GlobalTheory.CrisLoc.exists_pow_mul_eq_zero l e he hne hx
  refine (GlobalTheory.T.acris_eq_zero_or_eq_zero_of_mul_eq_zero l _ _ h).resolve_left ?_
  have h1 := GlobalTheory.PMon.Trans.map_prod_ne_zero_pt l (List.replicate n e)
    fun e' he' => (List.eq_of_mem_replicate he').symm ▸ hne
  rwa [List.map_replicate, List.prod_replicate, map_pow] at h1
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RatioIntegral

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.RatioTransport

open GlobalTheory.PMon.Gauss

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)

theorem lift_phi {b : P.R.B} {y : Formalism.Per.Acris l}
    (h : T.eB b = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) y) :
    T.eB (P.φB b) = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) (φc l y) := by
  rw [T.frob, h, (GlobalTheory.PMon.Trans.acris_bcris l).2.1]

theorem lift_iter {b : P.R.B} {y : Formalism.Per.Acris l}
    (h : T.eB b = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) y) (j : ℕ) :
    T.eB (P.φB^[j] b) = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) ((φc l)^[j] y) := by
  induction j with
  | zero => exact h
  | succ j ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply']; exact lift_phi T ih

theorem iter_lpow (m j : ℕ) (x : P.R.B) :
    P.φB^[m] ((l : P.R.B) ^ j * x) = (l : P.R.B) ^ j * P.φB^[m] x := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_mul, map_pow, map_natCast]

theorem isUnit_lpow (m : ℕ) : IsUnit ((l : P.R.B) ^ m) := by
  have h : IsUnit (l : ℚ_[l]) := (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero : (l : ℚ_[l]) ≠ 0).isUnit
  have h2 := h.map (algebraMap ℚ_[l] P.R.B)
  rw [map_natCast] at h2
  exact h2.pow m

theorem ratio_integral {h s : ℕ} (hs : s < h) {b b' : P.R.B} {y y' : Formalism.Per.Acris l}
    (hb : T.eB b = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) y)
    (hb' : T.eB b' = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) y')
    (he : P.φB^[h] b = (l : P.R.B) ^ s * b) (he' : P.φB^[h] b' = (l : P.R.B) ^ s * b')
    (h0 : b' ≠ 0) (hr : P.φB b * b' = b * P.φB b') : ∃ c : ℚ_[l], b = c • b' := by
  obtain ⟨hinj, -, hz⟩ := GlobalTheory.PMon.Trans.acris_bcris l
  have e1 : (φc l)^[h] y = (l : Formalism.Per.Acris l) ^ s * y := by
    apply hinj
    rw [← lift_iter T hb, he, map_mul, map_pow, map_natCast, hb, map_mul, map_pow, map_natCast]
  have e2 : (φc l)^[h] y' = (l : Formalism.Per.Acris l) ^ s * y' := by
    apply hinj
    rw [← lift_iter T hb', he', map_mul, map_pow, map_natCast, hb', map_mul, map_pow, map_natCast]
  have e3 : y' ≠ 0 := by
    rintro rfl
    apply h0
    apply T.eB.injective
    rw [hb', map_zero, map_zero]
  have e4 : φc l y * y' = y * φc l y' := by
    apply hinj
    rw [map_mul, map_mul, ← lift_phi T hb, ← lift_phi T hb', ← hb, ← hb', ← map_mul, ← map_mul, hr]
  obtain ⟨c, d, hc, hcd⟩ := ratio_proportional_target l h s hs y y' e1 e2 e3 e4
  have e5 : algebraMap ℚ_[l] P.R.B (c : ℚ_[l]) * b = algebraMap ℚ_[l] P.R.B (d : ℚ_[l]) * b' := by
    apply T.eB.injective
    rw [map_mul, map_mul, T.zB, T.zB, hb, hb', ← hz, ← hz, ← map_mul, ← map_mul, hcd]
  have hc' : (c : ℚ_[l]) ≠ 0 := fun e => hc (Subtype.ext e)
  refine ⟨(c : ℚ_[l])⁻¹ * d, ?_⟩
  rw [Algebra.smul_def, map_mul, mul_assoc, ← e5, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc', map_one, one_mul]

theorem ratio_of_acris : Ratio := by
  intro l _ P AI T h s hs ω ω' hω hω' he he' h0 hr
  obtain ⟨N, x, hx⟩ := hω
  obtain ⟨M, x', hx'⟩ := hω'
  have hb : T.eB ((l : P.R.B) ^ (N + M) * ω) =
      algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) ((l : Formalism.Per.Acris l) ^ M * x) := by
    have e : (l : P.R.B) ^ (N + M) * ω = (l : P.R.B) ^ M * ((l : P.R.B) ^ N * ω) := by ring
    rw [e, map_mul T.eB ((l : P.R.B) ^ M), hx]
    simp only [map_mul, map_pow, map_natCast]
  have hb' : T.eB ((l : P.R.B) ^ (N + M) * ω') =
      algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) ((l : Formalism.Per.Acris l) ^ N * x') := by
    have e : (l : P.R.B) ^ (N + M) * ω' = (l : P.R.B) ^ N * ((l : P.R.B) ^ M * ω') := by ring
    rw [e, map_mul T.eB ((l : P.R.B) ^ N), hx']
    simp only [map_mul, map_pow, map_natCast]
  have hu := isUnit_lpow (P := P) (N + M)
  obtain ⟨c, hc⟩ := ratio_integral T hs hb hb'
    (by rw [iter_lpow, he]; ring) (by rw [iter_lpow, he']; ring)
    (fun e => h0 ((hu.mul_right_eq_zero).1 e))
    (by
      simp only [map_mul, map_pow, map_natCast]
      linear_combination ((l : P.R.B) ^ (N + M)) ^ 2 * hr)
  refine ⟨c, hu.mul_left_cancel ?_⟩
  rw [hc, Algebra.smul_def, Algebra.smul_def]
  ring

end GlobalTheory.PMon.RatioTransport
end
end
