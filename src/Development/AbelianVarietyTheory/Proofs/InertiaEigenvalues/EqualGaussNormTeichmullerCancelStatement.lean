module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaussNormExtensionAcris
public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltNormUltrametricEqZero
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorRes
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
import Mathlib.Data.Nat.Choose.Multinomial
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisLocallyMonomialStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ISupMonomialHolderLogConvexStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ISupPowEqPowISupNonnegStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltNormUltrametricEqZero
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Kernel
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTiltRootOfUnityApproxRatio

section

@[expose] public section

open GlobalTheory.PMon.Gauss

open scoped Formalism.Per

namespace GlobalTheory.TiltRootApprox

open Ideal

variable {l : ℕ} [Fact l.Prime]

theorem pow_pow_add_mul {M : Type*} [Monoid M] {ξ : M} {o : ℕ} (h : ξ ^ (l ^ o) = ξ) (a k : ℕ) :
    ξ ^ (l ^ (a + o * k)) = ξ ^ (l ^ a) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show a + o * (k + 1) = (a + o * k) + o by ring, pow_add, mul_comm, pow_mul, h, ih]

theorem exists_pow_pow_eq {M : Type*} [Monoid M] {ξ : M} {n : ℕ} (hn : 0 < n) (hl : ¬ l ∣ n)
    (h : ξ ^ n = 1) : ∃ o : ℕ, 0 < o ∧ ξ ^ (l ^ o) = ξ := by
  have hcop : l.Coprime n := (Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)).2 hl
  refine ⟨n.totient, Nat.totient_pos.2 hn, ?_⟩
  have hmod : l ^ n.totient % n = 1 % n := Nat.ModEq.pow_totient hcop
  rw [← Nat.div_add_mod (l ^ n.totient) n, hmod, pow_add, pow_mul, h, one_pow, one_mul]
  rcases Nat.lt_or_ge 1 n with h1 | h1
  · rw [Nat.mod_eq_of_lt h1, pow_one]
  · have : n = 1 := by omega
    subst this
    simp only [pow_one] at h
    simp [h]

theorem exists_tilt_lift (ξ : Formalism.Per.OC l) {o : ℕ} (ho : 0 < o) (hξ : ξ ^ (l ^ o) = ξ) :
    ∃ ζ : Formalism.Per.Fl l, ζ ^ (l ^ o) = ζ ∧ ζ.untilt = ξ := by
  obtain ⟨q, rfl⟩ : ∃ q, o = q + 1 := ⟨o - 1, by omega⟩
  have hper := pow_pow_add_mul (l := l) hξ
  let s : ℕ → ModP (Formalism.Per.OC l) l := fun m =>
    Ideal.Quotient.mk (span {((l : ℕ) : Formalism.Per.OC l)}) (ξ ^ (l ^ (q * m)))
  have hs : ∀ m, s (m + 1) ^ l = s m := by
    intro m
    simp only [s, ← map_pow]
    congr 1
    rw [← pow_mul, ← pow_succ, show q * (m + 1) + 1 = q * m + (q + 1) * 1 by ring, hper]
  let ζ : Formalism.Per.Fl l := ⟨s, hs⟩
  refine ⟨ζ, ?_, ?_⟩
  · refine Perfection.ext fun m => ?_
    erw [map_pow]
    change s m ^ l ^ (q + 1) = s m
    simp only [s, ← map_pow]
    congr 1
    rw [← pow_mul, ← pow_add, show q * m + (q + 1) = q * m + (q + 1) * 1 by ring, hper]
  · refine Perfection.teichmuller_spec (I := span {((l : ℕ) : Formalism.Per.OC l)}) fun n => ?_
    refine ⟨ξ ^ (l ^ (q * n)), rfl, ?_⟩
    rw [← pow_mul, ← pow_add, show q * n + n = 0 + (q + 1) * n by ring, hper, pow_zero, pow_one]

end GlobalTheory.TiltRootApprox

namespace GlobalTheory.TiltRootApprox

open Ideal

theorem exists_root_approx : ∀ (l : ℕ) [Fact l.Prime] (y y' : Formalism.Per.Fl l), y' ≠ 0 →
    ‖(((y).untilt : Formalism.Per.OC l) : ℂ_[l])‖ = ‖(((y').untilt : Formalism.Per.OC l) : ℂ_[l])‖ →
    ∃ (ζ : Formalism.Per.Fl l) (o : ℕ), 0 < o ∧ ζ ^ (l ^ o) = ζ ∧ ζ ≠ 0 ∧
      ‖(((y - ζ * y').untilt : Formalism.Per.OC l) : ℂ_[l])‖ <
        ‖(((y').untilt : Formalism.Per.OC l) : ℂ_[l])‖ := by
  intro l _ y y' hy' hn
  have h0 : ((y'.untilt : Formalism.Per.OC l) : ℂ_[l]) ≠ 0 := fun h =>
    hy' (GlobalTheory.TiltAbs.eq_zero_of_untilt y' (Subtype.ext h))
  have hpos : 0 < ‖((y'.untilt : Formalism.Per.OC l) : ℂ_[l])‖ := norm_pos_iff.2 h0
  have hd : y'.untilt ∣ y.untilt := by
    refine ⟨⟨((y.untilt : Formalism.Per.OC l) : ℂ_[l]) / ((y'.untilt : Formalism.Per.OC l) : ℂ_[l]),
      (GlobalTheory.RingBasics.mem_OC _).2 ?_⟩, Subtype.ext ?_⟩
    · rw [norm_div, hn, div_self hpos.ne']
    · change _ = ((y'.untilt : Formalism.Per.OC l) : ℂ_[l]) * (_ / _)
      field_simp
  obtain ⟨u, rfl⟩ := GlobalTheory.TiltAlgClosed.dvd_of_untilt_dvd hd
  have hmul : ∀ a b : Formalism.Per.Fl l, (((a * b).untilt : Formalism.Per.OC l) : ℂ_[l]) =
      ((a.untilt : Formalism.Per.OC l) : ℂ_[l]) * ((b.untilt : Formalism.Per.OC l) : ℂ_[l]) := by
    intro a b
    rw [map_mul]
    rfl
  have hu : ‖((u.untilt : Formalism.Per.OC l) : ℂ_[l])‖ = 1 := by
    rw [hmul, norm_mul] at hn
    have := hn
    field_simp at this
    nlinarith [this]
  obtain ⟨ξ, hξ, hclose⟩ := ReciprocityTheory.ChartRestriction.L1.res_full l _ hu.le
  have hξn : ‖ξ‖ ≤ 1 := by
    calc ‖ξ‖ = ‖((u.untilt : Formalism.Per.OC l) : ℂ_[l]) - (((u.untilt : Formalism.Per.OC l) : ℂ_[l]) - ξ)‖ := by
          rw [sub_sub_cancel]
      _ ≤ max ‖((u.untilt : Formalism.Per.OC l) : ℂ_[l])‖ ‖((u.untilt : Formalism.Per.OC l) : ℂ_[l]) - ξ‖ := by
          have := IsUltrametricDist.norm_add_le_max (((u.untilt : Formalism.Per.OC l) : ℂ_[l]))
            (-(((u.untilt : Formalism.Per.OC l) : ℂ_[l]) - ξ))
          rwa [← sub_eq_add_neg, norm_neg] at this
      _ ≤ 1 := max_le hu.le hclose.le
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    rw [sub_zero, hu] at hclose
    exact lt_irrefl _ hclose
  obtain ⟨n, hn0, hln, hξpow⟩ : ∃ n : ℕ, 0 < n ∧ ¬ l ∣ n ∧ ξ ^ n = 1 := by
    rcases Set.mem_insert_iff.1 hξ with h | h
    · exact absurd h hξ0
    · exact h
  obtain ⟨o, ho, hξo⟩ := exists_pow_pow_eq hn0 hln hξpow
  let ξ' : Formalism.Per.OC l := ⟨ξ, (GlobalTheory.RingBasics.mem_OC _).2 hξn⟩
  have hξ'o : ξ' ^ (l ^ o) = ξ' := Subtype.ext (by
    change ξ ^ (l ^ o) = ξ
    exact hξo)
  obtain ⟨ζ, hζo, hζu⟩ := exists_tilt_lift ξ' ho hξ'o
  refine ⟨ζ, o, ho, hζo, ?_, ?_⟩
  · rintro rfl
    apply hξ0
    have h00 : (0 : Formalism.Per.Fl l).untilt = 0 := Perfection.teichmuller_zero
    rw [h00] at hζu
    have := congrArg Subtype.val hζu
    exact this.symm
  · have e : y' * u - ζ * y' = (u - ζ) * y' := by ring
    rw [e, hmul, norm_mul]
    have hlt : ‖(((u - ζ).untilt : Formalism.Per.OC l) : ℂ_[l])‖ < 1 := by
      have hmk : Ideal.Quotient.mk (span {((l : ℕ) : Formalism.Per.OC l)}) ((u - ζ).untilt) =
          Ideal.Quotient.mk (span {((l : ℕ) : Formalism.Per.OC l)}) (u.untilt - ζ.untilt) := by
        rw [PreTilt.mk_untilt_eq_coeff_zero, map_sub, map_sub, PreTilt.mk_untilt_eq_coeff_zero,
          PreTilt.mk_untilt_eq_coeff_zero]
      rw [Ideal.Quotient.eq, ← pow_one (span {((l : ℕ) : Formalism.Per.OC l)}),
        GlobalTheory.RingBasics.mem_span_pow_OC, pow_one] at hmk
      have e2 : (((u - ζ).untilt : Formalism.Per.OC l) : ℂ_[l]) =
          ((((u - ζ).untilt - (u.untilt - ζ.untilt) : Formalism.Per.OC l)) : ℂ_[l]) +
            (((u.untilt : Formalism.Per.OC l) : ℂ_[l]) - ξ) := by
        rw [hζu]
        push_cast
        ring
      rw [e2]
      refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ hclose)
      exact lt_of_le_of_lt hmk GlobalTheory.RingBasics.norm_p_lt
    calc ‖(((u - ζ).untilt : Formalism.Per.OC l) : ℂ_[l])‖ * ‖((y'.untilt : Formalism.Per.OC l) : ℂ_[l])‖
        < 1 * ‖((y'.untilt : Formalism.Per.OC l) : ℂ_[l])‖ := mul_lt_mul_of_pos_right hlt hpos
      _ = _ := one_mul _

end GlobalTheory.TiltRootApprox
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTiltRootOfUnityApproxRatioStatement

section

@[expose] public section

open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_tilt_root_of_unity_approx_ratio : ∀ (l : ℕ) [Fact l.Prime] (y y' : Formalism.Per.Fl l), y' ≠ 0 → ‖(((y).untilt : Formalism.Per.OC l) : ℂ_[l])‖ = ‖(((y').untilt : Formalism.Per.OC l) : ℂ_[l])‖ → ∃ (ζ : Formalism.Per.Fl l) (o : ℕ), 0 < o ∧ ζ ^ (l ^ o) = ζ ∧ ζ ≠ 0 ∧ ‖(((y - ζ * y').untilt : Formalism.Per.OC l) : ℂ_[l])‖ < ‖(((y').untilt : Formalism.Per.OC l) : ℂ_[l])‖ := by
  first | exact @GlobalTheory.TiltRootApprox.exists_root_approx | exact GlobalTheory.TiltRootApprox.exists_root_approx | (intros; apply GlobalTheory.TiltRootApprox.exists_root_approx <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqualGaussNormTeichmullerCancel

section

@[expose] public section

open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.GaussCancel

variable {l : ℕ} [Fact l.Prime]

theorem untilt_zero' : (0 : Formalism.Per.Fl l).untilt = 0 := by
  rw [← WittVector.fontaineTheta_teichmuller, WittVector.teichmuller_zero, map_zero]

theorem isGauss_gC {ρ : ℝ} (h1 : (l : ℝ)⁻¹ ≤ ρ) (h2 : ρ < 1) : IsGauss l ρ (gC l ρ) := by
  have h : ∃ N, IsGauss l ρ N := by
    obtain ⟨N, hN⟩ := GlobalTheory.GaussExt.exists_gauss_acris l ρ h1 h2
    exact ⟨N, hN⟩
  have hfun : gC l ρ = Classical.choose h := by
    funext x
    unfold gC
    rw [dite_eq_left h]
  rw [hfun]
  exact Classical.choose_spec h

theorem gC_sub_le {ρ : ℝ} (hG : IsGauss l ρ (gC l ρ)) (x y : Formalism.Per.Acris l) :
    gC l ρ (x - y) ≤ max (gC l ρ x) (gC l ρ y) := by
  rw [sub_eq_add_neg]
  calc _ ≤ max (gC l ρ x) (gC l ρ (-y)) := hG.2.1 _ _
    _ = _ := by rw [hG.2.2.1]

theorem gC_pow {ρ : ℝ} (hG : IsGauss l ρ (gC l ρ)) (h1 : gC l ρ 1 = 1) (x : Formalism.Per.Acris l) (n : ℕ) :
    gC l ρ (x ^ n) = gC l ρ x ^ n := by
  induction n with
  | zero => simp [h1]
  | succ n ih => rw [pow_succ, hG.2.2.2.1, ih, pow_succ]

theorem gA_le_of_coeff_zero {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (a : Formalism.Per.Ainf l)
    (ha : a.coeff 0 = 0) : gA l ρ a ≤ ρ := by
  unfold gA
  apply ciSup_le
  intro n
  rcases n with _ | n
  · simpa [ha, untilt_zero'] using h0
  · have hn : ‖(((a.coeff (n + 1)).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ (n + 1)) ≤ 1 :=
      Real.rpow_le_one (norm_nonneg _) (GlobalTheory.TiltAbs.norm_le_one _) (by positivity)
    calc _ ≤ 1 * ρ ^ (n + 1) := mul_le_mul_of_nonneg_right hn (pow_nonneg h0 _)
      _ ≤ ρ := by rw [one_mul]; exact pow_le_of_le_one h0 h1 (Nat.succ_ne_zero n)

theorem tc_mul (a b : Formalism.Per.Fl l) : tc l (a * b) = tc l a * tc l b := by
  unfold tc
  rw [Formalism.Per.tm, map_mul, map_mul]

end GlobalTheory.GaussCancel

namespace GlobalTheory.GaussCancel

variable {l : ℕ} [Fact l.Prime]

theorem equal_gauss_cancel : ∀ (l : ℕ) [Fact l.Prime] (w w' : Formalism.Per.Acris l), w' ≠ 0 →
    (∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ w = gC l ρ w') →
    ∃ (ζ : Formalism.Per.Fl l) (o : ℕ) (ρ₀ : ℝ), 0 < o ∧ ζ ^ (l ^ o) = ζ ∧ ζ ≠ 0 ∧ (l : ℝ)⁻¹ < ρ₀ ∧ ρ₀ < 1 ∧
      gC l ρ₀ (w - tc l ζ * w') < gC l ρ₀ w' := by
  intro l _ w w' hw' heq
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hlinv : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  have hlpos : (0 : ℝ) < (l : ℝ)⁻¹ := by positivity
  obtain ⟨⟨c, k, ρ₂, hc, hρ₂, hρ₂1, hm'⟩, -⟩ := GlobalTheory.T.gaussNormAcris_locally_monomial l w' hw' (l : ℝ)⁻¹ le_rfl hlinv
  have hm : ∀ ρ ∈ Set.Icc (l : ℝ)⁻¹ ρ₂, gC l ρ w = c * ρ ^ k := fun ρ hρ => by
    rw [heq ρ hρ.1 (lt_of_le_of_lt hρ.2 hρ₂1)]; exact hm' ρ hρ
  obtain ⟨y', j', hkj', hy', hL'⟩ := GlobalTheory.T.exists_teichmuller_lower_gaussNorm_of_locally_monomial l w' c (l : ℝ)⁻¹ ρ₂ k le_rfl hρ₂ hρ₂1 hc hm'
  obtain ⟨y, j, hkj, hy, hL⟩ := GlobalTheory.T.exists_teichmuller_lower_gaussNorm_of_locally_monomial l w c (l : ℝ)⁻¹ ρ₂ k le_rfl hρ₂ hρ₂1 hc hm

  have hy'0 : ((y'.untilt : Formalism.Per.OC l) : ℂ_[l]) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hy'
    linarith
  have hdvd : y' ∣ y := by
    apply GlobalTheory.TiltAlgClosed.dvd_of_untilt_dvd
    have hq : ((y.untilt : Formalism.Per.OC l) : ℂ_[l]) / ((y'.untilt : Formalism.Per.OC l) : ℂ_[l]) ∈ 𝓞_ℂ_[l] := by
      rw [GlobalTheory.RingBasics.mem_OC, norm_div, hy, hy', div_self hc.ne']
    refine ⟨⟨_, hq⟩, Subtype.ext ?_⟩
    change ((y.untilt : Formalism.Per.OC l) : ℂ_[l]) = ((y'.untilt : Formalism.Per.OC l) : ℂ_[l]) *
      (((y.untilt : Formalism.Per.OC l) : ℂ_[l]) / ((y'.untilt : Formalism.Per.OC l) : ℂ_[l]))
    field_simp
  obtain ⟨u, hu⟩ := hdvd
  have hu1 : ‖((u.untilt : Formalism.Per.OC l) : ℂ_[l])‖ = ‖(((1 : Formalism.Per.Fl l).untilt : Formalism.Per.OC l) : ℂ_[l])‖ := by
    have h := hy
    rw [hu, map_mul] at h
    push_cast at h
    rw [norm_mul, hy'] at h
    rw [map_one]
    simp only [OneMemClass.coe_one, norm_one]
    have : c * ‖((u.untilt : Formalism.Per.OC l) : ℂ_[l])‖ = c * 1 := by rw [h, mul_one]
    exact mul_left_cancel₀ hc.ne' this
  obtain ⟨ζ, o, ho, hζ, hζ0, hlt⟩ := GlobalTheory.T.exists_tilt_root_of_unity_approx_ratio l u 1 one_ne_zero hu1
  rw [mul_one, map_one] at hlt
  simp only [OneMemClass.coe_one, norm_one] at hlt

  set ρ₀ : ℝ := ((l : ℝ)⁻¹ + ρ₂) / 2 with hρ₀def
  have hρ₀a : (l : ℝ)⁻¹ < ρ₀ := by rw [hρ₀def]; linarith
  have hρ₀b : ρ₀ < ρ₂ := by rw [hρ₀def]; linarith
  have hρ₀1 : ρ₀ < 1 := lt_trans hρ₀b hρ₂1
  have hρ₀pos : 0 < ρ₀ := lt_trans hlpos hρ₀a
  have hIoo : ρ₀ ∈ Set.Ioo (l : ℝ)⁻¹ ρ₂ := ⟨hρ₀a, hρ₀b⟩
  have hIcc : ρ₀ ∈ Set.Icc (l : ℝ)⁻¹ ρ₂ := ⟨hρ₀a.le, hρ₀b.le⟩
  refine ⟨ζ, o, ρ₀, ho, hζ, hζ0, hρ₀a, hρ₀1, ?_⟩
  have hG := isGauss_gC (l := l) hρ₀a.le hρ₀1
  obtain ⟨hb1, hbl, -, hbt, -⟩ := GlobalTheory.T.gaussNormAcris_basic_values l ρ₀ hρ₀a.le hρ₀1
  have hlpow : ∀ n : ℕ, gC l ρ₀ ((l : Formalism.Per.Acris l) ^ n) = ρ₀ ^ n := fun n => by
    rw [gC_pow hG hb1, hbl]
  have hGw' : gC l ρ₀ w' = c * ρ₀ ^ k := hm' ρ₀ hIcc
  have hGw : gC l ρ₀ w = c * ρ₀ ^ k := hm ρ₀ hIcc
  set T : ℝ := ρ₀ ^ (max j j') * (c * ρ₀ ^ k) with hTdef
  set J : ℕ := max j j' with hJ
  set m : ℕ := (k + J).toNat with hmdef

  have hA : ∀ (x : Formalism.Per.Acris l) (z : Formalism.Per.Fl l) (i : ℕ), 0 ≤ k + i → i ≤ J → gC l ρ₀ x = c * ρ₀ ^ k →
      gC l ρ₀ ((l : Formalism.Per.Acris l) ^ i * x - (l : Formalism.Per.Acris l) ^ (k + i).toNat * tc l z) < ρ₀ ^ i * gC l ρ₀ x →
      gC l ρ₀ ((l : Formalism.Per.Acris l) ^ J * x - (l : Formalism.Per.Acris l) ^ m * tc l z) < T := by
    intro x z i hki hiJ hx hlt'
    have hmi : m = (J - i) + (k + i).toNat := by rw [hmdef]; omega
    have heqA : (l : Formalism.Per.Acris l) ^ J * x - (l : Formalism.Per.Acris l) ^ m * tc l z =
        (l : Formalism.Per.Acris l) ^ (J - i) * ((l : Formalism.Per.Acris l) ^ i * x -
          (l : Formalism.Per.Acris l) ^ (k + i).toNat * tc l z) := by
      have e : (l : Formalism.Per.Acris l) ^ J = (l : Formalism.Per.Acris l) ^ (J - i) * (l : Formalism.Per.Acris l) ^ i := by
        rw [← pow_add, Nat.sub_add_cancel hiJ]
      rw [hmi, e, pow_add]
      ring
    rw [heqA, hG.2.2.2.1, hlpow, hTdef, ← hx]
    calc ρ₀ ^ (J - i) * gC l ρ₀ _ < ρ₀ ^ (J - i) * (ρ₀ ^ i * gC l ρ₀ x) :=
          mul_lt_mul_of_pos_left hlt' (pow_pos hρ₀pos _)
      _ = ρ₀ ^ J * gC l ρ₀ x := by rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hiJ]
  have hAw := hA w y j hkj (le_max_left _ _) hGw (hL ρ₀ hIoo)
  have hAw' := hA w' y' j' hkj' (le_max_right _ _) hGw' (hL' ρ₀ hIoo)

  have hζ1 : gC l ρ₀ (tc l ζ) ≤ 1 := (hG.1 _).2
  have hdiff : gC l ρ₀ (tc l u - tc l ζ) < 1 := by
    have hsplit : tc l u - tc l ζ = tc l (u - ζ) + algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l)
        (Formalism.Per.tm u - Formalism.Per.tm ζ - Formalism.Per.tm (u - ζ)) := by
      unfold tc
      rw [map_sub, map_sub]
      ring
    have hc0 : (Formalism.Per.tm u - Formalism.Per.tm ζ - Formalism.Per.tm (u - ζ)).coeff 0 = 0 := by
      change WittVector.constantCoeff (Formalism.Per.tm u - Formalism.Per.tm ζ - Formalism.Per.tm (u - ζ)) = 0
      rw [map_sub, map_sub]
      change (Formalism.Per.tm u).coeff 0 - (Formalism.Per.tm ζ).coeff 0 - (Formalism.Per.tm (u - ζ)).coeff 0 = 0
      simp [Formalism.Per.tm, WittVector.teichmuller_coeff_zero]
    rw [hsplit]
    refine lt_of_le_of_lt (hG.2.1 _ _) (max_lt ?_ ?_)
    · rw [hbt]; exact hlt
    · rw [hG.2.2.2.2]
      exact lt_of_le_of_lt (gA_le_of_coeff_zero hρ₀pos.le hρ₀1.le _ hc0) hρ₀1
  have hmz : ((m : ℕ) : ℤ) = k + J := by rw [hmdef]; exact Int.toNat_of_nonneg (by omega)
  have hD : gC l ρ₀ ((l : Formalism.Per.Acris l) ^ m * (tc l y - tc l ζ * tc l y')) < T := by
    have : tc l y - tc l ζ * tc l y' = tc l y' * (tc l u - tc l ζ) := by
      rw [hu, tc_mul]; ring
    rw [this, hG.2.2.2.1, hG.2.2.2.1, hlpow, hbt, hy']
    have hT : ρ₀ ^ m * c = T := by
      rw [hTdef, ← zpow_natCast, hmz, zpow_add₀ hρ₀pos.ne', zpow_natCast]
      ring
    rw [← hT, ← mul_assoc]
    exact mul_lt_of_lt_one_right (mul_pos (pow_pos hρ₀pos _) hc) hdiff
  have hB : gC l ρ₀ (tc l ζ * ((l : Formalism.Per.Acris l) ^ J * w' - (l : Formalism.Per.Acris l) ^ m * tc l y')) < T := by
    rw [hG.2.2.2.1]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (hG.1 _).1 hζ1) hAw'
  have hid : (l : Formalism.Per.Acris l) ^ J * (w - tc l ζ * w') =
      ((l : Formalism.Per.Acris l) ^ J * w - (l : Formalism.Per.Acris l) ^ m * tc l y) -
        tc l ζ * ((l : Formalism.Per.Acris l) ^ J * w' - (l : Formalism.Per.Acris l) ^ m * tc l y') +
        (l : Formalism.Per.Acris l) ^ m * (tc l y - tc l ζ * tc l y') := by ring
  have hbig : gC l ρ₀ ((l : Formalism.Per.Acris l) ^ J * (w - tc l ζ * w')) < T := by
    rw [hid]
    refine lt_of_le_of_lt (hG.2.1 _ _) (max_lt (lt_of_le_of_lt (gC_sub_le hG _ _) (max_lt hAw hB)) ?_)
    exact hD
  rw [hG.2.2.2.1, hlpow, hTdef, ← hGw'] at hbig
  exact lt_of_mul_lt_mul_left hbig (pow_nonneg hρ₀pos.le _)

end GlobalTheory.GaussCancel
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqualGaussNormTeichmullerCancelStatement

section

@[expose] public section

open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.equal_gaussNorm_teichmuller_cancel : ∀ (l : ℕ) [Fact l.Prime] (w w' : Formalism.Per.Acris l), w' ≠ 0 → (∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ w = gC l ρ w') → ∃ (ζ : Formalism.Per.Fl l) (o : ℕ) (ρ₀ : ℝ), 0 < o ∧ ζ ^ (l ^ o) = ζ ∧ ζ ≠ 0 ∧ (l : ℝ)⁻¹ < ρ₀ ∧ ρ₀ < 1 ∧ gC l ρ₀ (w - tc l ζ * w') < gC l ρ₀ w' := by
  first | exact @GlobalTheory.GaussCancel.equal_gauss_cancel | exact GlobalTheory.GaussCancel.equal_gauss_cancel | (intros; apply GlobalTheory.GaussCancel.equal_gauss_cancel <;> assumption)
end
end
