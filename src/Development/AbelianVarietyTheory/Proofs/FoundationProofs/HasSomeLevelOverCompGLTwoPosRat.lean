module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QAllQConjOfDvd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmpPropsStatement
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
public import Mathlib.LinearAlgebra.Matrix.Integer
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import Mathlib.Geometry.Manifold.StructureGroupoid
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.ModularForms.SlashActions
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Lemma
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatMobiusUpperHalfPlanePropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionAllCoeffsDeltaPowAffineSubstStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatConjPrincipalCongruence

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.FN

open Matrix CongruenceSubgroup


set_option backward.isDefEq.respectTransparency false in
theorem conj_Gamma_den_mul (g : GL (Fin 2) ℚ) (M : ℕ) (y : SL(2, ℤ))
    (hy' : y ∈ Gamma ((g.1.den * (g⁻¹).1.den) * M)) :
    ∃ z ∈ Gamma M, ((z : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ)) =
      g.1 * ((y : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ)) * (g⁻¹).1 := by
  obtain ⟨y, hy⟩ := y
  let A₁ := g.1
  let A₂ := (g⁻¹).1
  have hA₁₂ : A₁ * A₂ = 1 := by simp only [← Matrix.GeneralLinearGroup.coe_mul,
    mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one, A₁, A₂]
  let a₁ := A₁.den
  let a₂ := A₂.den
  obtain ⟨k, hk⟩ : ∃ k, y = 1 + (a₁ * a₂ * M) • k := by
    replace hy' : y.map (Int.cast : ℤ → ZMod (a₁ * a₂ * M)) = 1 := by
      rw [CongruenceSubgroup.Gamma_mem', Subtype.ext_iff] at hy'
      simpa using! hy'
    use Matrix.of fun i j ↦ (y - 1) i j / (a₁ * a₂ * M)
    rw [← sub_eq_iff_eq_add']
    ext i j
    simp_rw [Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul, Nat.cast_mul]
    refine (Int.mul_ediv_cancel_of_dvd ?_).symm
    rw [← Matrix.map_one Int.cast (by simp) (by simp), ← sub_eq_zero,
      ← Matrix.map_sub _ (by simp)] at hy'
    simpa only [Matrix.zero_apply, Matrix.map_apply, ZMod.intCast_zmod_eq_zero_iff_dvd,
      Nat.cast_mul] using! congr_fun₂ hy' i j
  let z := 1 + M • (A₁.num * k * A₂.num)
  have hz_coe : z.map Int.cast = A₁ * (y.map Int.cast) * A₂ := by
    simp only [Matrix.map_add _ Int.cast_add, Matrix.map_one _ Int.cast_zero Int.cast_one, hk,
      mul_add, mul_one, add_mul, hA₁₂, add_right_inj, z]
    conv_rhs => rw [← A₁.inv_denom_smul_num, ← A₂.inv_denom_smul_num, Matrix.map_smul _ _ (by simp)]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.map_smul (Int.cast : ℤ → ℚ) M (by simp),
      Matrix.map_mul_intCast]
    rw [← Nat.cast_smul_eq_nsmul ℚ (_ * M), ← mul_smul, ← mul_smul,
      mul_comm a₁ a₂, Nat.cast_mul, Nat.cast_mul, mul_assoc _ _ (M : ℚ), mul_comm _ (M : ℚ),
      inv_mul_cancel_left₀ (mod_cast A₂.den_ne_zero),
      mul_inv_cancel_right₀ (mod_cast A₁.den_ne_zero), Nat.cast_smul_eq_nsmul]
  have hz_det : z.det = 1 := by
    have := congr_arg Matrix.det hz_coe
    simp_rw [Matrix.det_mul, ← Int.cast_det] at this
    rwa [mul_right_comm, ← Matrix.det_mul, hA₁₂, Matrix.det_one, one_mul, hy, Int.cast_inj] at this
  refine ⟨⟨z, hz_det⟩, ?_, hz_coe⟩
  rw [CongruenceSubgroup.Gamma_mem', Subtype.ext_iff]
  change z.map (Int.cast : ℤ → ZMod M) = 1
  ext i j
  change (↑((1 : Matrix (Fin 2) (Fin 2) ℤ) i j +
    M • (A₁.num * k * A₂.num) i j) : ZMod M) = (1 : Matrix (Fin 2) (Fin 2) (ZMod M)) i j
  simp [nsmul_eq_mul, Matrix.one_apply]

theorem exists_conj_principal_congruence :
    ∀ g : GQ, ∃ n : ℕ, 0 < n ∧ ∀ N : ℕ, ∀ δ ∈ CongruenceSubgroup.Gamma (N * n),
      ∃ δ' ∈ CongruenceSubgroup.Gamma N, g * ofSL δ = ofSL δ' * g := by
  intro g
  let G : GL (Fin 2) ℚ := g
  refine ⟨G.1.den * (G⁻¹).1.den, Nat.mul_pos (Nat.pos_of_ne_zero (Matrix.den_ne_zero _)) (Nat.pos_of_ne_zero (Matrix.den_ne_zero _)), fun N δ hδ => ?_⟩
  rw [mul_comm] at hδ
  obtain ⟨z, hz, hzc⟩ := conj_Gamma_den_mul G N δ hδ
  refine ⟨z, hz, ?_⟩
  apply Subtype.ext
  apply Units.ext
  have h21 : (G⁻¹).1 * G.1 = 1 := by
    simp only [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.GeneralLinearGroup.coe_one]
  show G.1 * ((δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ)) =
    ((z : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ)) * G.1
  have e1 : ((z : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ)) =
      ((z : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ)) := rfl
  have e2 : ((δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ)) =
      ((δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ)) := rfl
  rw [e1, e2, hzc, Matrix.mul_assoc, h21, Matrix.mul_one]

end GlobalTheory.FN
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatConjPrincipalCongruenceStatement

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.glTwoPosRat_conj_principal_congruence : ∀ g : GQ, ∃ n : ℕ, 0 < n ∧ ∀ N : ℕ, ∀ δ ∈ CongruenceSubgroup.Gamma (N * n), ∃ δ' ∈ CongruenceSubgroup.Gamma N, g * ofSL δ = ofSL δ' * g := by
  first | exact @GlobalTheory.FN.exists_conj_principal_congruence | exact GlobalTheory.FN.exists_conj_principal_congruence | (intros; apply GlobalTheory.FN.exists_conj_principal_congruence <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatHermiteNormalFormMobius

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.HermFN

lemma lin_ne_zero (c e : ℤ) (z : ℂ) (hz : 0 < z.im) (h : c ≠ 0 ∨ e ≠ 0) : (c : ℂ) * z + e ≠ 0 := by
  intro h0
  have him := congrArg Complex.im h0
  have hre := congrArg Complex.re h0
  simp at him hre
  rcases him with hc | hc
  · subst hc; simp at hre; rcases h with h | h <;> simp_all
  · linarith

lemma common_den (g : GQ) : ∃ N : ℕ, 0 < N ∧ ∀ i j, ∃ z : ℤ, (N : ℚ) * ent g i j = z := by
  refine ⟨∏ i : Fin 2, ∏ j : Fin 2, (ent g i j).den, ?_, ?_⟩
  · exact Finset.prod_pos (fun i _ => Finset.prod_pos (fun j _ => (ent g i j).den_pos))
  · intro i j
    have hdv : (ent g i j).den ∣ ∏ i : Fin 2, ∏ j : Fin 2, (ent g i j).den :=
      (Finset.dvd_prod_of_mem (fun j => (ent g i j).den) (Finset.mem_univ j)).trans
        (Finset.dvd_prod_of_mem (fun i => ∏ j : Fin 2, (ent g i j).den) (Finset.mem_univ i))
    obtain ⟨k, hk⟩ := hdv
    refine ⟨k * (ent g i j).num, ?_⟩
    rw [hk]
    have := Rat.mul_den_eq_num (ent g i j)
    push_cast
    rw [← this]; ring

lemma upper_step (p p' x b dd q : ℤ) (a : ℕ) (τ : ℂ) (hd0 : (dd : ℂ) ≠ 0) (hpC : (p : ℂ) = a * p')
    (hq'C : (p' : ℂ) * b + x * dd = q) :
    ((p' : ℤ) : ℂ) * (((a : ℂ) * τ + b) / dd) + ((x : ℤ) : ℂ) = ((p : ℂ) * τ + q) / dd := by
  rw [hpC, ← hq'C]; field_simp; ring

lemma left_step (m0 m1 A B C D : ℤ) (N : ℕ) (τ : ℂ) (hN : (N : ℂ) ≠ 0) (hD : (C : ℂ) * τ + D ≠ 0) :
    (m0 : ℂ) / N * (((A : ℂ) * τ + B) / ((C : ℂ) * τ + D)) + (m1 : ℂ) / N =
      (((m0 * A + m1 * C : ℤ) : ℂ) * τ + ((m0 * B + m1 * D : ℤ) : ℂ)) / (N * ((C : ℂ) * τ + D)) := by
  have hD' : τ * (C : ℂ) + D ≠ 0 := by rwa [mul_comm]
  rw [eq_div_iff (mul_ne_zero hN hD)]
  push_cast
  field_simp
  ring

end GlobalTheory.HermFN

namespace GlobalTheory.HermFN

theorem hermite (g : GQ) : ∃ n : ℕ, 0 < n ∧ ∀ γ₀ : SL(2, ℤ), ∃ (γ : SL(2, ℤ)) (a d : ℕ) (b : ℤ), a * d = n ∧
    ∀ τ : ℍ, mob g ((γ₀ • τ : ℍ) : ℂ) = mob (ofSL γ) (((a : ℂ) * τ + b) / d) := by
  obtain ⟨N, hN, hm⟩ := common_den g
  choose m hm using hm
  have hdetg : 0 < ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0 := by
    have h := g.2
    rw [Matrix.mem_glpos, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two] at h
    exact h
  set nI : ℤ := m 0 0 * m 1 1 - m 0 1 * m 1 0 with hnI
  have hn : 0 < nI := by
    have hq : (nI : ℚ) = (N : ℚ) ^ 2 * (ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0) := by
      rw [hnI]; push_cast; rw [← hm 0 0, ← hm 0 1, ← hm 1 0, ← hm 1 1]; ring
    have hNq : (0 : ℚ) < N := by exact_mod_cast hN
    have : (0 : ℚ) < nI := by rw [hq]; positivity
    exact_mod_cast this
  refine ⟨nI.toNat, by omega, ?_⟩
  intro γ₀
  have hdet0 : γ₀ 0 0 * γ₀ 1 1 - γ₀ 0 1 * γ₀ 1 0 = 1 := by
    have := γ₀.2; rwa [Matrix.det_fin_two] at this
  set p : ℤ := m 0 0 * γ₀ 0 0 + m 0 1 * γ₀ 1 0 with hp_def
  set r : ℤ := m 1 0 * γ₀ 0 0 + m 1 1 * γ₀ 1 0 with hr_def
  set q : ℤ := m 0 0 * γ₀ 0 1 + m 0 1 * γ₀ 1 1 with hq_def
  set s : ℤ := m 1 0 * γ₀ 0 1 + m 1 1 * γ₀ 1 1 with hs_def
  have hps : p * s - q * r = nI := by
    rw [hp_def, hr_def, hq_def, hs_def, hnI]; linear_combination (m 0 0 * m 1 1 - m 0 1 * m 1 0) * hdet0
  have hpr : p ≠ 0 ∨ r ≠ 0 := by
    by_contra h; push_neg at h; rw [h.1, h.2] at hps; omega
  have hrs : r ≠ 0 ∨ s ≠ 0 := by
    by_contra h; push_neg at h; rw [h.1, h.2] at hps; omega
  set a : ℕ := Int.gcd p r with ha_def
  have ha : 0 < a := Int.gcd_pos_iff.mpr hpr
  set p' : ℤ := p / a
  set r' : ℤ := r / a
  have hp : p = a * p' := (Int.mul_ediv_cancel' (Int.gcd_dvd_left p r)).symm
  have hr : r = a * r' := (Int.mul_ediv_cancel' (Int.gcd_dvd_right p r)).symm
  have cop : IsCoprime p' r' := Int.isCoprime_iff_gcd_eq_one.mpr (Int.gcd_div_gcd_div_gcd ha)
  obtain ⟨γ, h0, h1⟩ := cop.exists_SL2_col 0
  have hγ : p' * γ 1 1 - γ 0 1 * r' = 1 := by
    have := γ.2; rw [Matrix.det_fin_two, h0, h1] at this; linear_combination this
  set b : ℤ := γ 1 1 * q - γ 0 1 * s with hb_def
  set dd : ℤ := p' * s - r' * q with hdd_def
  have had : (a : ℤ) * dd = nI := by
    rw [hdd_def, ← hps]; linear_combination (-s) * hp + q * hr
  have hd : 0 < dd := by
    have : (0 : ℤ) < a := by exact_mod_cast ha
    nlinarith
  have hq' : p' * b + γ 0 1 * dd = q := by rw [hb_def, hdd_def]; linear_combination q * hγ
  have hs' : r' * b + γ 1 1 * dd = s := by rw [hb_def, hdd_def]; linear_combination s * hγ
  refine ⟨γ, a, dd.toNat, b, ?_, ?_⟩
  · zify; rw [Int.toNat_of_nonneg hd.le, Int.toNat_of_nonneg hn.le]; exact had
  · intro τ
    have hz : 0 < (τ : ℂ).im := τ.im_pos
    have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    have hdC : ((dd.toNat : ℕ) : ℂ) = (dd : ℂ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hd.le]
    have hd0 : (dd : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    have hc : ∀ i j, ((ent g i j : ℚ) : ℂ) = (m i j : ℂ) / N := by
      intro i j
      have : ent g i j = (m i j : ℚ) / N := by
        rw [← hm i j]; field_simp
      rw [this]; push_cast; rfl
    have hD0 : ((γ₀ 1 0 : ℤ) : ℂ) * τ + ((γ₀ 1 1 : ℤ) : ℂ) ≠ 0 := by
      apply lin_ne_zero _ _ _ hz
      by_contra h; push_neg at h; rw [h.1, h.2] at hdet0; simp at hdet0
    have hRS : (r : ℂ) * τ + s ≠ 0 := lin_ne_zero r s _ hz hrs
    have hpC : (p : ℂ) = a * p' := by exact_mod_cast hp
    have hrC : (r : ℂ) = a * r' := by exact_mod_cast hr
    have hq'C : (p' : ℂ) * b + γ 0 1 * dd = q := by exact_mod_cast hq'
    have hs'C : (r' : ℂ) * b + γ 1 1 * dd = s := by exact_mod_cast hs'
    rw [UpperHalfPlane.coe_specialLinearGroup_apply, hdC]
    simp only [mob, hc, algebraMap_int_eq, eq_intCast, Complex.ofReal_intCast]
    have eL : ((m 0 0 : ℂ) / N * ((((γ₀ 0 0 : ℤ) : ℂ) * τ + ((γ₀ 0 1 : ℤ) : ℂ)) / (((γ₀ 1 0 : ℤ) : ℂ) * τ + ((γ₀ 1 1 : ℤ) : ℂ))) + (m 0 1 : ℂ) / N) /
        ((m 1 0 : ℂ) / N * ((((γ₀ 0 0 : ℤ) : ℂ) * τ + ((γ₀ 0 1 : ℤ) : ℂ)) / (((γ₀ 1 0 : ℤ) : ℂ) * τ + ((γ₀ 1 1 : ℤ) : ℂ))) + (m 1 1 : ℂ) / N)
        = ((p : ℂ) * τ + q) / ((r : ℂ) * τ + s) := by
      have e1 : (m 0 0 : ℂ) / N * ((((γ₀ 0 0 : ℤ) : ℂ) * τ + ((γ₀ 0 1 : ℤ) : ℂ)) / (((γ₀ 1 0 : ℤ) : ℂ) * τ + ((γ₀ 1 1 : ℤ) : ℂ))) + (m 0 1 : ℂ) / N
          = ((p : ℂ) * τ + q) / (N * (((γ₀ 1 0 : ℤ) : ℂ) * τ + ((γ₀ 1 1 : ℤ) : ℂ))) := by
        exact left_step (m 0 0) (m 0 1) (γ₀ 0 0) (γ₀ 0 1) (γ₀ 1 0) (γ₀ 1 1) N τ hNC hD0
      have e2 : (m 1 0 : ℂ) / N * ((((γ₀ 0 0 : ℤ) : ℂ) * τ + ((γ₀ 0 1 : ℤ) : ℂ)) / (((γ₀ 1 0 : ℤ) : ℂ) * τ + ((γ₀ 1 1 : ℤ) : ℂ))) + (m 1 1 : ℂ) / N
          = ((r : ℂ) * τ + s) / (N * (((γ₀ 1 0 : ℤ) : ℂ) * τ + ((γ₀ 1 1 : ℤ) : ℂ))) := by
        exact left_step (m 1 0) (m 1 1) (γ₀ 0 0) (γ₀ 0 1) (γ₀ 1 0) (γ₀ 1 1) N τ hNC hD0
      rw [e1, e2, div_div_div_cancel_right₀ (mul_ne_zero hNC hD0)]
    have eR : ((γ 0 0 : ℤ) : ℂ) * (((a : ℂ) * τ + b) / dd) + ((γ 0 1 : ℤ) : ℂ) = ((p : ℂ) * τ + q) / dd := by
      rw [h0]; exact upper_step p p' (γ 0 1) b dd q a τ hd0 hpC hq'C
    have eR2 : ((γ 1 0 : ℤ) : ℂ) * (((a : ℂ) * τ + b) / dd) + ((γ 1 1 : ℤ) : ℂ) = ((r : ℂ) * τ + s) / dd := by
      rw [h1]; exact upper_step r r' (γ 1 1) b dd s a τ hd0 hrC hs'C
    have hofSL : ∀ i j, ((ent (ofSL γ) i j : ℚ) : ℂ) = ((γ i j : ℤ) : ℂ) := by
      intro i j; show (((γ i j : ℤ) : ℚ) : ℂ) = _; push_cast; rfl
    simp only [hofSL]
    rw [eL, eR, eR2, div_div_div_cancel_right₀ hd0]

end GlobalTheory.HermFN
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatHermiteNormalFormMobiusStatement

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.glTwoPosRat_hermite_normal_form_mobius : ∀ g : GQ, ∃ n : ℕ, 0 < n ∧ ∀ γ₀ : SL(2, ℤ), ∃ (γ : SL(2, ℤ)) (a d : ℕ) (b : ℤ), a * d = n ∧ ∀ τ : ℍ, mob g ((γ₀ • τ : ℍ) : ℂ) = mob (ofSL γ) (((a : ℂ) * τ + b) / d) := by
  first | exact @GlobalTheory.HermFN.hermite | exact GlobalTheory.HermFN.hermite | (intros; apply GlobalTheory.HermFN.hermite <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSomeLevelOverCompGLTwoPosRat

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem gamma_mul_le (m k : ℕ) : CongruenceSubgroup.Gamma (m * k) ≤ CongruenceSubgroup.Gamma m := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma_mem] at hγ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hγ
  have c := fun (x : ℤ) (y : ZMod (m * k)) (e : (x : ZMod (m * k)) = y) =>
    congrArg (ZMod.castHom (dvd_mul_right m k) (ZMod m)) e
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using c _ _ h1
  · simpa using c _ _ h2
  · simpa using c _ _ h3
  · simpa using c _ _ h4

theorem inR_cmp : ∀ (E : Subring ℂ) (g : GQ) (f : ℍ → ℂ), (∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ E) →
    InR E f → InR E (GlobalTheory.FN.cmp g f) := by
  intro E g f hE ⟨N, w, hN, hinv, hexp⟩
  obtain ⟨n₁, hn₁, hH⟩ := GlobalTheory.T.glTwoPosRat_hermite_normal_form_mobius g
  obtain ⟨n₂, hn₂, hC⟩ := GlobalTheory.T.glTwoPosRat_conj_principal_congruence g
  obtain ⟨mob_hs, mob_mul, mob_one, mob_sl, mob_diff, mob_up⟩ := GlobalTheory.T.glTwoPosRatMobius_upperHalfPlane_properties
  obtain ⟨cmp_one, cmp_mul, cmp_sl, cmp_up⟩ := GlobalTheory.T.cmp_mul_ofSL_and_up_cmp_eq_up_mob
  refine ⟨N * n₁ * n₂, w * n₁, by positivity, ?_, ?_⟩
  · intro δ hδ τ
    have hδ' : δ ∈ CongruenceSubgroup.Gamma (N * n₂) := by
      have : N * n₁ * n₂ = N * n₂ * n₁ := by ring
      rw [this] at hδ
      exact gamma_mul_le _ _ hδ
    obtain ⟨δ', hδ'm, hgδ⟩ := hC N δ hδ'
    have e1 : GlobalTheory.FN.cmp (g * ofSL δ) f = fun τ => GlobalTheory.FN.cmp g f (δ • τ) := by
      rw [cmp_mul, cmp_sl]
    have e2 : GlobalTheory.FN.cmp (ofSL δ' * g) f = GlobalTheory.FN.cmp g f := by
      rw [cmp_mul, cmp_sl]
      congr 1
      funext σ
      exact hinv δ' hδ'm σ
    have := congrFun (e1.symm.trans (hgδ ▸ e2)) τ
    exact this
  · intro γ₀
    obtain ⟨γ, a, d, b, had, hmob⟩ := hH γ₀
    have ha : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; simp at had; omega)
    have hd : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at had; omega)
    have key := GlobalTheory.T.qExpansionAllCoeffs_deltaPow_affineSubst E N w a d b (fun τ => f (γ • τ)) hE hN ha hd (hexp γ)
    rw [had] at key
    have hlift := QAll.of_dvd (N := N * n₁) (N' := N * n₁ * n₂) (by positivity) (dvd_mul_right _ _)
      (p := (· ∈ E)) (Subring.zero_mem E) key
    convert hlift using 2 with τ
    congr 1
    have hz : (((a : ℂ) * τ + b) / d).im > 0 := by
      have : (((a : ℂ) * τ + b) / d) = ((a : ℝ) / d : ℝ) * (τ : ℂ) + ((b : ℝ) / d : ℝ) := by
        push_cast; field_simp
      rw [this]
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      have : (0 : ℝ) < (a : ℝ) / d := by positivity
      have := τ.im_pos
      simp only [UpperHalfPlane.coe_im]
      positivity
    show up f (mob g ((γ₀ • τ : ℍ) : ℂ)) = up (fun τ => f (γ • τ)) (((a : ℂ) * τ + b) / d)
    have hzc : ((UpperHalfPlane.ofComplex (((a : ℂ) * τ + b) / d) : ℍ) : ℂ) = ((a : ℂ) * τ + b) / d := by
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
    have hm : mob (ofSL γ) (((a : ℂ) * τ + b) / d) =
        ((γ • UpperHalfPlane.ofComplex (((a : ℂ) * τ + b) / d) : ℍ) : ℂ) := by
      rw [← mob_sl, hzc]
    simp only [up]
    rw [hmob τ, hm, UpperHalfPlane.ofComplex_apply]

end GlobalTheory.FN
end
end
