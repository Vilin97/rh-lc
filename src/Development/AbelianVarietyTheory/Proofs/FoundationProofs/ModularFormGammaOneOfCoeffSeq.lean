module

public import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
public import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
public import Mathlib.NumberTheory.ModularForms.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasModerateGrowthQExpansionOfCoeffPolynomialGrowStatement
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import Mathlib.Analysis.Complex.Periodic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.SelbergSieve
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
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MdifferentiableQExpansionOfCoeffPolynomialGrowth
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsBoundedAtImInftyOfPeriodicPolynomialBound

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

theorem periodic_comp_ofComplex_of_vadd' {f : ℍ → ℂ} {M : ℝ} (hper : ∀ τ : ℍ, f (M +ᵥ τ) = f τ) :
    Function.Periodic (f ∘ ofComplex) M := by
  intro w
  by_cases hw : 0 < w.im
  · have hw' : 0 < (w + M).im := by simpa using hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw', ofComplex_apply_of_im_pos hw]
    rw [← hper ⟨w, hw⟩]
    congr 1
    ext
    simp [coe_vadd, add_comm]
  · push_neg at hw
    have hw' : (w + M).im ≤ 0 := by simpa using hw
    simp [ofComplex_apply_of_im_nonpos hw', ofComplex_apply_of_im_nonpos hw]

theorem qParam_add_period {M : ℝ} (hM : M ≠ 0) (z : ℂ) :
    Function.Periodic.qParam M (z + M) = Function.Periodic.qParam M z := by
  unfold Function.Periodic.qParam
  have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM
  rw [show 2 * π * Complex.I * (z + M) / M = 2 * π * Complex.I * z / M + 2 * π * Complex.I by field_simp,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem isBoundedAtImInfty_of_periodic_of_polyBound :
    ∀ (f : ℍ → ℂ) (h : ℕ) (C : ℝ) (A : ℕ), 0 < h → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f →
      (∀ τ : ℍ, f ((h : ℝ) +ᵥ τ) = f τ) →
      (∀ τ : ℍ, 1 ≤ τ.im → |τ.re| ≤ h → ‖f τ‖ ≤ C * τ.im ^ A) → IsBoundedAtImInfty f := by
  intro f h C A hh hf hper hbd
  set M : ℝ := (h : ℝ) with hMdef
  have hM : 0 < M := by simp [hMdef, hh]
  have hperF : Function.Periodic (f ∘ ofComplex) M := periodic_comp_ofComplex_of_vadd' hper

  have hbd' : ∀ τ : ℍ, 1 ≤ τ.im → ‖f τ‖ ≤ C * τ.im ^ A := by
    intro τ hτ
    set n : ℤ := ⌊τ.re / M⌋
    have h1 : (n : ℝ) ≤ τ.re / M := Int.floor_le _
    have h2 : τ.re / M < n + 1 := Int.lt_floor_add_one _
    have hw : 0 < ((τ : ℂ) - n * M).im := by simpa using τ.im_pos
    set σ : ℍ := ⟨(τ : ℂ) - n * M, hw⟩
    have hσ : f σ = f τ := by
      have := hperF.sub_int_mul_eq (x := (τ : ℂ)) n
      simp only [Function.comp_apply, ofComplex_apply] at this
      rw [← this, ofComplex_apply_of_im_pos hw]
    have hσim : σ.im = τ.im := by
      change ((τ : ℂ) - (n : ℂ) * (M : ℂ)).im = τ.im
      simp
    have hσre : σ.re = τ.re - n * M := by
      change ((τ : ℂ) - (n : ℂ) * (M : ℂ)).re = τ.re - n * M
      simp
    have hre1 : n * M ≤ τ.re := by rwa [le_div_iff₀ hM] at h1
    have hre2 : τ.re < (n + 1) * M := by rwa [div_lt_iff₀ hM] at h2
    have habs : |σ.re| ≤ h := by
      rw [hσre, abs_le]
      constructor <;> nlinarith
    rw [← hσ, ← hσim]
    exact hbd σ (hσim ▸ hτ) habs

  set g : ℍ → ℂ := fun τ ↦ f τ * Function.Periodic.qParam M τ with hg
  have hnormg : ∀ τ : ℍ, ‖g τ‖ = ‖f τ‖ * Real.exp (-2 * π * τ.im / M) := by
    intro τ
    simp [hg, norm_mul, Function.Periodic.norm_qParam]
  have hgdiff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g :=
    hf.mul ((Function.Periodic.differentiable_qParam (h := M)).comp_mdifferentiable
      UpperHalfPlane.mdifferentiable_coe)
  have hgper : ∀ τ : ℍ, g (M +ᵥ τ) = g τ := by
    intro τ
    simp only [hg, hper, coe_vadd]
    rw [add_comm, qParam_add_period hM.ne']
  have hgzero : IsZeroAtImInfty g := by
    set c : ℝ := 2 * π / M with hc
    have hcpos : 0 < c := by positivity
    have hT : Tendsto (fun y : ℝ ↦ C * (c⁻¹) ^ A * ((c * y) ^ A * Real.exp (-(c * y)))) atTop (𝓝 0) := by
      simpa using ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero A).comp
        (tendsto_id.const_mul_atTop hcpos)).const_mul (C * (c⁻¹) ^ A)
    have heq : ∀ y : ℝ, C * (c⁻¹) ^ A * ((c * y) ^ A * Real.exp (-(c * y))) =
        C * y ^ A * Real.exp (-2 * π * y / M) := by
      intro y
      have : -(c * y) = -2 * π * y / M := by rw [hc]; ring
      rw [this, mul_pow, ← mul_assoc, ← mul_assoc, mul_assoc C, ← mul_pow, inv_mul_cancel₀ hcpos.ne',
        one_pow, mul_one]
    simp_rw [heq] at hT
    have hT' : Tendsto (fun τ : ℍ ↦ C * τ.im ^ A * Real.exp (-2 * π * τ.im / M)) atImInfty (𝓝 0) :=
      hT.comp tendsto_comap
    refine squeeze_zero_norm' ?_ hT'
    refine (atImInfty_mem _).2 ⟨1, fun τ hτ ↦ ?_⟩
    rw [Set.mem_setOf_eq, hnormg]
    exact mul_le_mul_of_nonneg_right (hbd' τ hτ) (Real.exp_pos _).le
  have hgbdd : IsBoundedAtImInfty g := hgzero.boundedAtFilter
  have hdecay := hgzero.exp_decay_atImInfty hM (periodic_comp_ofComplex_of_vadd' hgper) hgdiff hgbdd
  obtain ⟨K, hK⟩ := hdecay.bound
  obtain ⟨B, hB⟩ := (atImInfty_mem _).1 hK
  refine isBoundedAtImInfty_iff.2 ⟨K, B, fun τ hτ ↦ ?_⟩
  have h1 := hB τ hτ
  simp only [Set.mem_setOf_eq, hnormg, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h1
  exact le_of_mul_le_mul_right h1 (Real.exp_pos _)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsBoundedAtImInftyOfPeriodicPolynomialBoundStatement

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.isBoundedAtImInfty_of_periodic_polynomial_bound : ∀ (f : ℍ → ℂ) (h : ℕ) (C : ℝ) (A : ℕ), 0 < h → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → (∀ τ : ℍ, f ((h : ℝ) +ᵥ τ) = f τ) → (∀ τ : ℍ, 1 ≤ τ.im → |τ.re| ≤ h → ‖f τ‖ ≤ C * τ.im ^ A) → IsBoundedAtImInfty f := by
  first | exact @GlobalTheory.isBoundedAtImInfty_of_periodic_of_polyBound | exact GlobalTheory.isBoundedAtImInfty_of_periodic_of_polyBound | (intros; apply GlobalTheory.isBoundedAtImInfty_of_periodic_of_polyBound <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.MdifferentiableQExpansionOfCoeffPolynomialGrowthStatement

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.mdifferentiable_qExpansion_of_coeffPolynomialGrowth : ∀ a : ℕ → ℂ, PolyB a → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (qs a) := by
  first | exact @GlobalTheory.EisM.qs_mdifferentiable | exact GlobalTheory.EisM.qs_mdifferentiable | (intros; apply GlobalTheory.EisM.qs_mdifferentiable <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormGammaOneOfCoeffSeq

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM.OnGammaOne

theorem slash_inv {k L N : ℕ} {ε : DirichletCharacter ℂ N} (hNL : N ∣ L) {f : ℍ → ℂ}
    (hf : Inv k L (ch ε) f) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma1 L) : f ∣[(k : ℤ)] γ = f := by
  obtain ⟨-, h11, h10⟩ := (Gamma1_mem L γ).1 hγ
  have hc : (L : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h10
  have hd1 : (L : ℤ) ∣ γ 1 1 - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [h11, sub_self]
  have hd : ch ε (γ 1 1) = 1 := by
    have h2 : (N : ℤ) ∣ γ 1 1 - 1 := (Int.natCast_dvd_natCast.2 hNL).trans hd1
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at h2
    push_cast at h2
    have h3 : ((γ 1 1 : ℤ) : ZMod N) = 1 := sub_eq_zero.1 h2
    simp [ch, h3]
  funext τ
  rw [ModularForm.slash_action_eq'_iff, hf γ hc τ, hd, one_mul, zpow_natCast]

theorem periodic {k L : ℕ} {f : ℍ → ℂ} (hinv : ∀ γ ∈ Gamma1 L, f ∣[(k : ℤ)] γ = f)
    (γ : SL(2, ℤ)) (τ : ℍ) : (f ∣[(k : ℤ)] γ) ((L : ℝ) +ᵥ τ) = (f ∣[(k : ℤ)] γ) τ := by
  have hT : (ModularGroup.T ^ (L : ℤ)) • τ = (L : ℝ) +ᵥ τ := by
    rw [modular_T_zpow_smul]; simp
  have hδ : γ * ModularGroup.T ^ (L : ℤ) * γ⁻¹ ∈ Gamma1 L := by
    have h1 : ModularGroup.T ^ (L : ℤ) ∈ CongruenceSubgroup.Gamma L := by
      simpa using ModularGroup_T_pow_mem_Gamma (L : ℤ) (L : ℤ) dvd_rfl
    have h2 := (Gamma_normal L).conj_mem _ h1 γ
    rw [Gamma_mem] at h2
    rw [Gamma1_mem]
    exact ⟨h2.1, h2.2.2.2, h2.2.2.1⟩
  have e : (f ∣[(k : ℤ)] γ) ∣[(k : ℤ)] (ModularGroup.T ^ (L : ℤ)) = f ∣[(k : ℤ)] γ := by
    rw [← SlashAction.slash_mul,
      (inv_mul_cancel_right (γ * ModularGroup.T ^ (L : ℤ)) γ).symm,
      SlashAction.slash_mul, hinv _ hδ]
  have h := congrFun e τ
  have hden : denom (ModularGroup.T ^ (L : ℤ) : SL(2, ℤ)) τ = 1 := by
    rw [ModularGroup.denom_apply, ModularGroup.coe_T_zpow]; simp
  rw [ModularForm.SL_slash_apply (f := f ∣[(k : ℤ)] γ), hT, hden, one_zpow, mul_one] at h
  exact h

end GlobalTheory.EisM.OnGammaOne

namespace GlobalTheory.EisM.OnGammaOne

theorem normSq_denom_bounds (L : ℕ) (γ : SL(2, ℤ)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ τ : ℍ, 1 ≤ τ.im → |τ.re| ≤ L →
      1 ≤ Complex.normSq (denom γ τ) ∧ Complex.normSq (denom γ τ) ≤ K * τ.im ^ 2 := by
  set c : ℝ := ((γ 1 0 : ℤ) : ℝ)
  set d : ℝ := ((γ 1 1 : ℤ) : ℝ)
  refine ⟨(|c| * L + |d|) ^ 2 + c ^ 2, by positivity, fun τ h1 h2 => ?_⟩
  have hns : Complex.normSq (denom γ τ) = (c * τ.re + d) ^ 2 + (c * τ.im) ^ 2 := by
    rw [ModularGroup.denom_apply, Complex.normSq_apply]
    simp [c, d]
    ring
  rw [hns]
  have hy0 : 0 ≤ τ.im := τ.im_pos.le
  have hy2 : 1 ≤ τ.im ^ 2 := by nlinarith
  constructor
  · by_cases hc : γ 1 0 = 0
    · have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
        have := γ.2; rw [Matrix.det_fin_two] at this; exact this
      rw [hc, mul_zero, sub_zero] at hdet
      have hd : γ 1 1 = 1 ∨ γ 1 1 = -1 := by
        rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with h | h
        · exact Or.inl h.2
        · exact Or.inr h.2
      have hc' : c = 0 := by simp [c, hc]
      have hd' : d ^ 2 = 1 := by rcases hd with h | h <;> simp [d, h]
      rw [hc']; nlinarith
    · have hc1 : 1 ≤ c ^ 2 := by
        have : (1 : ℤ) ≤ (γ 1 0) ^ 2 := by
          have := Int.one_le_abs hc
          nlinarith [sq_abs (γ 1 0)]
        have : ((1 : ℤ) : ℝ) ≤ (((γ 1 0) ^ 2 : ℤ) : ℝ) := by exact_mod_cast this
        simpa [c] using this
      nlinarith [sq_nonneg (c * τ.re + d)]
  · have hM : |c * τ.re + d| ≤ |c| * L + |d| := by
      calc |c * τ.re + d| ≤ |c * τ.re| + |d| := abs_add_le _ _
        _ = |c| * |τ.re| + |d| := by rw [abs_mul]
        _ ≤ |c| * L + |d| := by gcongr
    have hM2 : (c * τ.re + d) ^ 2 ≤ (|c| * L + |d|) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hM 2
    have hM0 : 0 ≤ (|c| * L + |d|) ^ 2 := by positivity
    nlinarith

theorem growth {f : ℍ → ℂ} (hf : Mod f) (k L : ℕ) (γ : SL(2, ℤ)) :
    ∃ (C : ℝ) (A : ℕ), ∀ τ : ℍ, 1 ≤ τ.im → |τ.re| ≤ L → ‖(f ∣[(k : ℤ)] γ) τ‖ ≤ C * τ.im ^ A := by
  obtain ⟨C, A, hC⟩ := hf
  obtain ⟨K, hK0, hK⟩ := normSq_denom_bounds L γ
  refine ⟨|C| * (1 + K ^ A), A, fun τ h1 h2 => ?_⟩
  obtain ⟨hD1, hDK⟩ := hK τ h1 h2
  set D := Complex.normSq (denom γ τ) with hD
  set y := τ.im with hy
  have hy0 : 0 < y := τ.im_pos
  have hD0 : 0 < D := by linarith
  have him : (γ • τ).im = y / D := ModularGroup.im_smul_eq_div_normSq γ τ
  have hw1 : (γ • τ).im ^ A ≤ y ^ A := by
    rw [him]
    exact pow_le_pow_left₀ (by positivity) (div_le_self hy0.le hD1) A
  have hw2 : ((γ • τ).im ^ A)⁻¹ ≤ K ^ A * y ^ A := by
    rw [him, ← inv_pow, inv_div, ← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ A
    rw [div_le_iff₀ hy0]
    nlinarith
  have hden : ‖denom γ τ ^ (-(k : ℤ))‖ ≤ 1 := by
    have hn : 1 ≤ ‖denom γ τ‖ := by
      have : 1 ≤ ‖denom γ τ‖ ^ 2 := by rw [← Complex.normSq_eq_norm_sq]; exact hD1
      nlinarith [norm_nonneg (denom γ τ)]
    rw [norm_zpow, zpow_neg, zpow_natCast]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hn)
  rw [ModularForm.SL_slash_apply, norm_mul]
  have hfw := hC (γ • τ)
  have hpos : 0 ≤ (γ • τ).im ^ A + ((γ • τ).im ^ A)⁻¹ := by
    have := (γ • τ).im_pos; positivity
  calc ‖f (γ • τ)‖ * ‖denom γ τ ^ (-(k : ℤ))‖ ≤ ‖f (γ • τ)‖ * 1 :=
        mul_le_mul_of_nonneg_left hden (norm_nonneg _)
    _ ≤ |C| * ((γ • τ).im ^ A + ((γ • τ).im ^ A)⁻¹) := by
        rw [mul_one]; exact hfw.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hpos)
    _ ≤ |C| * (y ^ A + K ^ A * y ^ A) := by gcongr
    _ = |C| * (1 + K ^ A) * y ^ A := by ring

end GlobalTheory.EisM.OnGammaOne


open GlobalTheory.EisM.OnGammaOne in
theorem GlobalTheory.EisM.modularForm_gammaOne_of_MF :
    ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N) (a : ℕ → ℂ), 0 < L → N ∣ L → MF k L (ch ε) a →
      ∃ f : ModularForm (Gamma1 L) (k : ℤ), ⇑f = qs a := by
  intro k L N ε a hL hNL ha
  haveI : NeZero L := ⟨hL.ne'⟩
  have hinv : ∀ γ ∈ Gamma1 L, qs a ∣[(k : ℤ)] γ = qs a := fun γ hγ => slash_inv hNL ha.2 γ hγ
  have hhol := GlobalTheory.T.mdifferentiable_qExpansion_of_coeffPolynomialGrowth a ha.1
  refine ⟨{ toFun := qs a, slash_action_eq' := ?_, holo' := hhol, bdd_at_cusps' := ?_ }, rfl⟩
  · rintro _ ⟨A, (hA : A ∈ Gamma1 L), rfl⟩
    exact hinv A hA
  · intro c hc
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    obtain ⟨C, A, hC⟩ := growth (GlobalTheory.T.hasModerateGrowth_qExpansion_of_coeffPolynomialGrowth a ha.1) k L γ
    have hs : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (qs a ∣[(k : ℤ)] γ) := by
      rw [ModularForm.SL_slash]; exact hhol.slash _ _
    exact GlobalTheory.T.isBoundedAtImInfty_of_periodic_polynomial_bound _ L C A hL hs (periodic hinv γ) hC
end
end
end
