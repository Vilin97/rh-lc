module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisValuationSubEqIntMulRadiusStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqualGaussNormTeichmullerCancelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisRadiusPosDefiniteStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ISupMonomialHolderLogConvex
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsTerFurther
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGaussGCTarget
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RootCancelPowEqSelfAcrisGaussNorm
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
import Mathlib.Algebra.Order.Star.Real

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RootCancelPowEqSelfAcrisGaussNormStatement

section

@[expose] public section

open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.rootCancel_pow_eq_self_acris_gaussNorm : ∀ (l : ℕ) [Fact l.Prime] (h s : ℕ), s < h → ∀ (w w' : Formalism.Per.Acris l) (ζ : Formalism.Per.Fl l) (o : ℕ) (ρ₀ : ℝ), (φc l)^[h] w' = (l : Formalism.Per.Acris l) ^ s * w' → w' ≠ 0 → φc l w * w' = w * φc l w' → (∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ w = gC l ρ w') → 0 < o → ζ ^ (l ^ o) = ζ → ζ ≠ 0 → (l : ℝ)⁻¹ ≤ ρ₀ → ρ₀ < 1 → gC l ρ₀ (w - tc l ζ * w') < gC l ρ₀ w' → ζ ^ l = ζ := by
  first | exact @GlobalTheory.PMon.Gauss.root_cancel_pow_eq_self | exact GlobalTheory.PMon.Gauss.root_cancel_pow_eq_self | (intros; apply GlobalTheory.PMon.Gauss.root_cancel_pow_eq_self <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerRootUnityEqUnit

section

@[expose] public section

open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss


open Polynomial in
theorem exists_zmod_of_pow_eq_self {F : Type} [CommRing F] [IsDomain F] (l : ℕ) [Fact l.Prime] [CharP F l]
    (ζ : F) (h : ζ ^ l = ζ) : ∃ a : ZMod l, ZMod.castHom (dvd_refl l) F a = ζ := by
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  set P : (ZMod l)[X] := X ^ l - X with hP
  have hmon : P.Monic := by
    apply Polynomial.monic_X_pow_sub
    simp [hl]
  have hroots : P.roots = Finset.univ.val := by
    have := FiniteField.roots_X_pow_card_sub_X (ZMod l)
    rwa [ZMod.card] at this
  have hdeg : P.natDegree = l := Polynomial.natDegree_X_pow_sub_X (R := (ZMod l)) hl
  have hprod : (Multiset.map (fun a => X - C a) P.roots).prod = P :=
    Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon
      (by rw [hroots, hdeg]; simp [ZMod.card])
  have hev := congrArg (fun Q : (ZMod l)[X] => Q.eval₂ (ZMod.castHom (dvd_refl l) F) ζ) hprod
  simp only [hP, eval₂_sub, eval₂_X_pow, eval₂_X, h, sub_self] at hev
  rw [Polynomial.eval₂_multiset_prod, Multiset.map_map] at hev
  obtain ⟨q, hq, hq0⟩ : ∃ q ∈ _, q = (0:F) := ⟨0, Multiset.prod_eq_zero_iff.1 hev, rfl⟩
  rw [Multiset.mem_map] at hq
  obtain ⟨a, -, rfl⟩ := hq
  refine ⟨a, ?_⟩
  simp only [Function.comp, eval₂_sub, eval₂_X, eval₂_C] at hq0
  exact (sub_eq_zero.1 hq0).symm

theorem padicInt_ringHom_witt_ext_pt {l : ℕ} [Fact l.Prime] {F : Type} [CommRing F] [CharP F l]
    (f g : ℤ_[l] →+* WittVector l F) : f = g := by
  ext x n
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec (n + 1) x)
  have hx : x = (x.appr (n + 1) : ℤ_[l]) + y * (l : ℤ_[l]) ^ (n + 1) := by rw [hy]; ring
  have hd : f x = g x + (f y - g y) * (l : WittVector l F) ^ (n + 1) := by
    conv_lhs => rw [hx]
    conv_rhs => rw [hx]
    simp only [map_add (f := _), map_mul, map_pow, map_natCast]
    ring
  have ht : WittVector.truncate (n + 1) ((f y - g y) * (l : WittVector l F) ^ (n + 1)) = 0 := by
    rw [← RingHom.mem_ker, WittVector.mem_ker_truncate]
    intro i hi
    exact WittVector.mul_pow_charP_coeff_zero _ hi
  have he : WittVector.truncate (n + 1) (f x) = WittVector.truncate (n + 1) (g x) := by
    rw [hd, map_add (f := _), ht, add_zero]
  have := congrArg (fun z => TruncatedWittVector.coeff (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) z) he
  simpa only [WittVector.coeff_truncate] using this

theorem teichmuller_root_unity_eq_unit : ∀ (l : ℕ) [Fact l.Prime] (ζ : Formalism.Per.Fl l), ζ ^ l = ζ → ζ ≠ 0 →
    ∃ c : ℤ_[l], IsUnit c ∧ zc l c = tc l ζ := by
  intro l _ ζ h hne
  obtain ⟨a, rfl⟩ := exists_zmod_of_pow_eq_self l ζ h
  have ha : a ≠ 0 := by rintro rfl; exact hne (map_zero _)
  refine ⟨WittVector.toPadicInt l (WittVector.teichmuller l a), ?_, ?_⟩
  · exact ((Ne.isUnit ha).map (WittVector.teichmuller l)).map (WittVector.toPadicInt l)
  · have hz : Formalism.Per.zA l = (WittVector.map (ZMod.castHom (dvd_refl l) (Formalism.Per.Fl l))).comp
        (WittVector.fromPadicInt l) := padicInt_ringHom_witt_ext_pt _ _
    simp only [zc, tc, RingHom.comp_apply, hz, Formalism.Per.tm]
    have hft : WittVector.fromPadicInt l (WittVector.toPadicInt l (WittVector.teichmuller l a)) =
        WittVector.teichmuller l a :=
      RingHom.congr_fun (WittVector.fromPadicInt_comp_toPadicInt (p := l)) _
    rw [hft, WittVector.map_teichmuller]

end GlobalTheory.PMon.Gauss
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisSubUnitLeDigit

section

@[expose] public section

open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon.Gauss

theorem gC_zero_of_radius (l : ℕ) [Fact l.Prime] {ρ : ℝ} (h0 : (l : ℝ)⁻¹ ≤ ρ) (h1 : ρ < 1) :
    gC l ρ (0 : Formalism.Per.Acris l) = 0 := by
  have hN := isGauss_gC_of_le l ρ h0 h1
  have hl : gC l ρ (l : Formalism.Per.Acris l) = ρ := (gC_basic_values l ρ h0 h1).2.1
  have hm := hN.2.2.2.1 ((l : Formalism.Per.Acris l)) 0
  rw [mul_zero, hl] at hm
  have : (1 - ρ) * gC l ρ 0 = 0 := by linarith
  rcases mul_eq_zero.1 this with h' | h'
  · linarith
  · exact h'

theorem gC_eq_zpow_mul_of_vr (l : ℕ) [Fact l.Prime] (x y : Formalism.Per.Acris l) (hx : x ≠ 0) (hy : y ≠ 0) (n : ℤ)
    (hn : ∀ r ∈ Set.Ioc (0 : ℝ) 1, vr l r x - vr l r y = n * r) (ρ : ℝ) (h0 : (l : ℝ)⁻¹ ≤ ρ) (h1 : ρ < 1) :
    gC l ρ x = ρ ^ n * gC l ρ y := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have hρ : 0 < ρ := (inv_pos.2 hl0).trans_le h0
  set r := -Real.logb l ρ with hr
  have hρr : (l : ℝ) ^ (-r) = ρ := by
    rw [hr, neg_neg, Real.rpow_logb hl0 hl1.ne' hρ]
  have hr0 : 0 < r := by
    have := Real.logb_neg hl1 hρ h1
    linarith
  have hr1 : r ≤ 1 := by
    have h := (Real.logb_le_logb hl1 (inv_pos.2 hl0) hρ).2 h0
    rw [Real.logb_inv, Real.logb_self_eq_one hl1] at h
    linarith
  have hv := hn r ⟨hr0, hr1⟩
  simp only [vr, hρr] at hv
  have hgx := GlobalTheory.T.gaussNormAcrisRadius_pos_definite l x hx ρ h0 h1
  have hgy := GlobalTheory.T.gaussNormAcrisRadius_pos_definite l y hy ρ h0 h1
  apply Real.logb_injOn_pos hl1 hgx (Set.mem_Ioi.2 (mul_pos (zpow_pos hρ n) hgy))
  have hz : Real.logb l (ρ ^ n) = n * Real.logb l ρ := by
    rw [Real.logb, Real.logb, Real.log_zpow, mul_div_assoc]
  rw [Real.logb_mul (zpow_pos hρ n).ne' hgy.ne', hz]
  rw [hr] at hv
  linarith

end GlobalTheory.PMon.Gauss

theorem GlobalTheory.PMon.Gauss.one_digit : ∀ (l : ℕ) [Fact l.Prime] (h s : ℕ), s < h → ∀ w w' : Formalism.Per.Acris l, (φc l)^[h] w' = (l : Formalism.Per.Acris l) ^ s * w' → w' ≠ 0 → φc l w * w' = w * φc l w' → (∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ w = gC l ρ w') → ∃ c : ℤ_[l], IsUnit c ∧ ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ (w - zc l c * w') ≤ ρ * gC l ρ w' := by
  intro l _ h s hsh w w' hφh hw' hrat hg
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  obtain ⟨ζ, o, ρ₀, ho, hζo, hζ0, hρ₀l, hρ₀1, hlt⟩ := GlobalTheory.T.equal_gaussNorm_teichmuller_cancel l w w' hw' hg
  have hζl : ζ ^ l = ζ := GlobalTheory.T.rootCancel_pow_eq_self_acris_gaussNorm l h s hsh w w' ζ o ρ₀ hφh hw' hrat hg ho hζo hζ0 hρ₀l.le hρ₀1 hlt
  obtain ⟨c, hcu, hc⟩ := GlobalTheory.PMon.Gauss.teichmuller_root_unity_eq_unit l ζ hζl hζ0
  refine ⟨c, hcu, fun ρ h0 h1 => ?_⟩
  have hρ : 0 < ρ := (inv_pos.2 hl0).trans_le h0
  have hN := isGauss_gC_of_le l ρ h0 h1
  by_cases hw1 : w - zc l c * w' = 0
  · rw [hw1, gC_zero_of_radius l h0 h1]
    exact mul_nonneg hρ.le (hN.1 w').1
  have hφz : φc l (zc l c) = zc l c := by
    rw [hc, frob_teich, hζl]
  have hrat1 : φc l (w - zc l c * w') * w' = (w - zc l c * w') * φc l w' := by
    rw [map_sub, map_mul, hφz]
    linear_combination hrat
  obtain ⟨n, hn⟩ := GlobalTheory.T.acrisValuation_sub_eq_int_mul_radius l h s hsh (w - zc l c * w') w' hφh hw1 hw' hrat1
  have hmono := gC_eq_zpow_mul_of_vr l _ w' hw1 hw' n hn
  have hρ₀ : 0 < ρ₀ := (inv_pos.2 hl0).trans hρ₀l
  have hn1 : 1 ≤ n := by
    by_contra hcon
    push_neg at hcon
    have hle : n ≤ 0 := by omega
    have e := hmono ρ₀ hρ₀l.le hρ₀1
    rw [← hc] at hlt
    rw [e] at hlt
    have hg0 := GlobalTheory.T.gaussNormAcrisRadius_pos_definite l w' hw' ρ₀ hρ₀l.le hρ₀1
    have : (1 : ℝ) ≤ ρ₀ ^ n := one_le_zpow_of_nonpos₀ hρ₀ hρ₀1.le hle
    nlinarith
  rw [hmono ρ h0 h1]
  have hle : ρ ^ n ≤ ρ ^ (1 : ℤ) := zpow_le_zpow_right_of_le_one₀ hρ h1.le hn1
  rw [zpow_one] at hle
  exact mul_le_mul_of_nonneg_right hle (hN.1 w').1
end
end
end
