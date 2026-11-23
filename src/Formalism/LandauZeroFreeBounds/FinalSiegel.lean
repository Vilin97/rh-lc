module

public import Formalism.LandauZeroFreeBounds.SameCharacterLFunctionOne
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.BqCoeff
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.BqGrowth
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.BqKeyOf
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LDerivNearOne
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.TrivReal
public import Mathlib.NumberTheory.LSeries.Injectivity
import Mathlib.Tactic.Lemma
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.SameCharacterLFunctionOne
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.SiegelProductCharacterInequality
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ZetaNegReal

-- Source module: Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.BqEntire

section

@[expose] public section

open Complex Filter Topology

noncomputable section

namespace Formalism.ZeroFreeDirichlet

def zetaSubPole : ℂ → ℂ :=
  Function.update (fun s : ℂ => riemannZeta s - 1 / (s - 1)) 1 (Real.eulerMascheroniConstant : ℂ)

theorem zeta_sub_pole_differentiable : Differentiable ℂ zetaSubPole := by
  rw [← differentiableOn_univ,
    ← Complex.differentiableOn_compl_singleton_and_continuousAt_iff (c := 1) Filter.univ_mem]
  refine ⟨fun s hs => ?_, ?_⟩
  · have hs1 : s ≠ 1 := hs.2
    have hev : zetaSubPole =ᶠ[𝓝 s] fun z => riemannZeta z - 1 / (z - 1) := by
      filter_upwards [isOpen_ne.mem_nhds hs1] with z hz
      exact Function.update_of_ne hz _ _
    have hd : DifferentiableAt ℂ (fun z => riemannZeta z - 1 / (z - 1)) s :=
      (differentiableAt_riemannZeta hs1).sub
        ((differentiableAt_const _).div (differentiableAt_id.sub_const 1) (sub_ne_zero.mpr hs1))
    exact (hd.congr_of_eventuallyEq hev).differentiableWithinAt
  · unfold zetaSubPole
    exact continuousAt_update_same.mpr tendsto_riemannZeta_sub_one_div

theorem zeta_minus_pole_eq {s : ℂ} (hs : s ≠ 1) : zetaSubPole s = riemannZeta s - 1 / (s - 1) := by
  unfold zetaSubPole
  exact Function.update_of_ne hs _ _

theorem dirichlet_product_entire : BqEntire := by
  intro q₁ q₂ _ _ _ χ₁ χ₂ ψ h₁ h₂ hψ
  obtain ⟨P, hP⟩ : ∃ P : ℂ → ℂ, P = fun s => DirichletCharacter.LFunction χ₁ s *
      DirichletCharacter.LFunction χ₂ s * DirichletCharacter.LFunction ψ s := ⟨_, rfl⟩
  have hPd : Differentiable ℂ P := by
    rw [hP]
    exact ((DirichletCharacter.differentiable_LFunction h₁).mul
      (DirichletCharacter.differentiable_LFunction h₂)).mul
      (DirichletCharacter.differentiable_LFunction hψ)
  have hds : Differentiable ℂ (dslope P 1) := by
    rw [← differentiableOn_univ, Complex.differentiableOn_dslope Filter.univ_mem]
    exact hPd.differentiableOn
  refine ⟨fun s => zetaSubPole s * P s + dslope P 1 s,
    (zeta_sub_pole_differentiable.mul hPd).add hds, fun s hs => ?_⟩
  have hs' : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  show _ = zetaSubPole s * P s + dslope P 1 s + _
  rw [dslope_of_ne _ hs, slope_def_field, zeta_minus_pole_eq hs]
  simp only [Fbq, lamBq, hP]
  field_simp
  ring

end Formalism.ZeroFreeDirichlet
end
end
end

-- Source module: Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.CharExists

section

@[expose] public section

open Complex
noncomputable section
namespace Formalism.ZeroFreeDirichlet

theorem isProdChar_changeLevel_mul {q₁ q₂ : ℕ} (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂) :
    IsProdChar χ₁ χ₂ (DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁ *
      DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂) := by
  intro n
  rw [MulChar.mul_apply]
  by_cases h : IsUnit (n : ZMod (q₁ * q₂))
  · have h1 : ∀ {q : ℕ} (hq : q ∣ q₁ * q₂) (χ : DirichletCharacter ℂ q),
        DirichletCharacter.changeLevel hq χ (n : ZMod (q₁ * q₂)) = χ (n : ZMod q) := by
      intro q hq χ
      have := DirichletCharacter.changeLevel_eq_cast_of_dvd (χ := χ) hq h.unit
      rw [IsUnit.unit_spec] at this
      rw [this]
      congr 1
      first
        | exact ZMod.cast_natCast hq n
        | exact ZMod.cast_natCast hq _ n
        | exact ZMod.cast_nat_cast hq n
    rw [h1, h1]
  · rw [MulChar.map_nonunit _ h]
    rw [ZMod.isUnit_iff_coprime, Nat.coprime_mul_iff_right] at h
    rcases not_and_or.mp h with h' | h'
    · rw [MulChar.map_nonunit χ₁ (by rwa [ZMod.isUnit_iff_coprime])]
      simp
    · rw [MulChar.map_nonunit χ₂ (by rwa [ZMod.isUnit_iff_coprime])]
      simp

theorem exists_product_character : ProdCharExists :=
  fun _ _ χ₁ χ₂ => ⟨_, isProdChar_changeLevel_mul χ₁ χ₂⟩

def characterModFour : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

theorem characterModFour_apply (a : ZMod 4) :
    characterModFour a = ((ZMod.χ₄ a : ℤ) : ℂ) := rfl

theorem characterModFour_sq : characterModFour ^ 2 = 1 := by
  first
    | exact (ZMod.isQuadratic_χ₄.comp _).sq_eq_one
    | exact (ZMod.isQuadratic_χ₄.comp (Int.castRingHom ℂ)).sq_eq_one

theorem characterModFour_ne_one : characterModFour ≠ 1 := by
  intro h
  have hu : IsUnit (3 : ZMod 4) := ⟨⟨3, 3, by decide, by decide⟩, rfl⟩
  have h3 := DFunLike.congr_fun h (3 : ZMod 4)
  rw [characterModFour_apply, MulChar.one_apply hu] at h3
  have hv : ZMod.χ₄ (3 : ZMod 4) = -1 := by decide
  rw [hv] at h3
  norm_num at h3

theorem exists_real_nontrivial_character : RealCharExists :=
  ⟨4, ⟨by norm_num⟩, characterModFour, characterModFour_sq, characterModFour_ne_one⟩

end Formalism.ZeroFreeDirichlet
end
end
end

-- Source module: Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LFunctionOneUpperBound

section

@[expose] public section

open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

theorem lfunction_one_upper_bound : LFunctionOneUpperBound := by
  refine ⟨38 * Real.exp (3 / 2), ?_⟩
  intro q _ χ hχ
  have hq : 3 ≤ q := three_le_modulus_of_ne_one χ hχ
  have hlog : 2 ≤ Real.log (3 * (q : ℝ)) := two_le_log_three_mul q hq
  have hd : 0 < 3 / (2 * Real.log (3 * (q : ℝ))) := div_pos (by norm_num) (by linarith)
  exact lfunction_norm_le_near_one χ hχ 1 (by rw [Complex.one_re]; linarith)
    (by rw [Complex.one_re]; norm_num) (by rw [norm_one]; norm_num)

end Formalism.ZeroFreeDirichlet
end
end
end

-- Source module: Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LRealPos

section

@[expose] public section

open Complex Filter Topology

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma real_character_lfunction_im_eq_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1) (hχ1 : χ ≠ 1)
    (σ : ℝ) : (DirichletCharacter.LFunction χ σ).im = 0 := by
  have h := realCharConj q χ hχ hχ1 (σ : ℂ)
  rw [Complex.conj_ofReal] at h
  exact Complex.conj_eq_iff_im.1 h.symm

lemma lfunction_tendsto_one_atTop {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    Tendsto (fun x : ℝ ↦ DirichletCharacter.LFunction χ x) atTop (𝓝 1) := by
  have ha : LSeries.abscissaOfAbsConv (fun n : ℕ => χ n) < ⊤ := by
    rw [DirichletCharacter.absicssaOfAbsConv_eq_one (NeZero.ne q) χ]
    exact EReal.coe_lt_top 1
  have ht := LSeries.tendsto_atTop ha
  simp only [Nat.cast_one, map_one] at ht
  refine ht.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  exact (DirichletCharacter.LFunction_eq_LSeries χ (by simpa using hx)).symm

theorem real_lfunction_real_on_reals : LRealPos := by
  intro q _ χ hχ hχ1 σ₀ hnz σ hσ
  have him : ∀ t : ℝ, (DirichletCharacter.LFunction χ t).im = 0 := real_character_lfunction_im_eq_zero χ hχ hχ1
  refine ⟨him σ, ?_⟩
  by_contra hneg
  rw [not_lt] at hneg
  have hcont : Continuous fun t : ℝ => (DirichletCharacter.LFunction χ t).re :=
    Complex.continuous_re.comp
      ((DirichletCharacter.differentiable_LFunction hχ1).continuous.comp Complex.continuous_ofReal)
  obtain ⟨x, hx1, hx⟩ : ∃ x : ℝ, σ ≤ x ∧ 0 < (DirichletCharacter.LFunction χ x).re := by
    have hev : ∀ᶠ x : ℝ in atTop, 0 < (DirichletCharacter.LFunction χ x).re :=
      ((Complex.continuous_re.tendsto 1).comp (lfunction_tendsto_one_atTop χ)).eventually
        (lt_mem_nhds (by norm_num))
    obtain ⟨x, hx⟩ := (hev.and (eventually_ge_atTop σ)).exists
    exact ⟨x, hx.2, hx.1⟩
  obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc hx1 hcont.continuousOn ⟨hneg, hx.le⟩
  apply hnz c (le_trans hσ hc.1)
  exact Complex.ext (by simpa using hc0) (by simpa using him c)

end Formalism.ZeroFreeDirichlet
end
end
end

-- Source module: Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.SiegelOf

section

@[expose] public section

open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

theorem siegel_theorem_of : SiegelOf := by
  intro hP hR hB hL1 hZ hLP hS ε hε
  obtain ⟨C, K, hK0, hKey⟩ := hB
  obtain ⟨CL, hL⟩ := hL1
  set σ₀ : ℝ := max (7 / 8) (1 - ε / (2 * (K + 1))) with hσ₀
  have hK1 : 0 < K + 1 := by linarith
  have h78 : 7 / 8 ≤ σ₀ := le_max_left _ _
  have hσ₀1 : σ₀ < 1 := by
    apply max_lt (by norm_num)
    have : 0 < ε / (2 * (K + 1)) := by positivity
    linarith
  have hKa : ∀ σ : ℝ, σ₀ ≤ σ → σ < 1 → K * (1 - σ) ≤ ε / 2 := by
    intro σ hσ hσ1
    have h1 : 1 - ε / (2 * (K + 1)) ≤ σ := le_trans (le_max_right _ _) hσ
    have h2 : 1 - σ ≤ ε / (2 * (K + 1)) := by linarith
    have h3 : 0 ≤ 1 - σ := by linarith
    have h4 : (K + 1) * (ε / (2 * (K + 1))) = ε / 2 := by
      field_simp
    calc K * (1 - σ) ≤ (K + 1) * (1 - σ) := by nlinarith
      _ ≤ (K + 1) * (ε / (2 * (K + 1))) := mul_le_mul_of_nonneg_left h2 hK1.le
      _ = ε / 2 := h4
  by_cases hex : ∃ (q₁ : ℕ) (_ : NeZero q₁) (χ₁ : DirichletCharacter ℂ q₁) (β : ℝ),
      χ₁ ^ 2 = 1 ∧ χ₁ ≠ 1 ∧ σ₀ ≤ β ∧ β < 1 ∧ DirichletCharacter.LFunction χ₁ β = 0
  ·
    obtain ⟨q₁, hq₁, χ₁, β, h1sq, h1ne, hβ0, hβ1, hzero⟩ := hex
    refine siegel_product_character_inequality hP hS hKey hL hε χ₁ h1sq h1ne (le_trans h78 hβ0) hβ1
      (hKa β hβ0 hβ1) ?_
    intro q _ χ ψ _ _ _ _
    simp [Fbq, hzero]
  ·
    push_neg at hex
    obtain ⟨q₁, hq₁, χ₁, h1sq, h1ne⟩ := hR
    have hnz : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ^ 2 = 1 → χ ≠ 1 →
        ∀ σ : ℝ, σ₀ ≤ σ → DirichletCharacter.LFunction χ σ ≠ 0 := by
      intro q _ χ hsq hne σ hσ
      rcases lt_or_ge σ 1 with h | h
      · exact hex q inferInstance χ σ hsq hne hσ h
      · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hne) (by simpa using h)
    have hpos : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ^ 2 = 1 → χ ≠ 1 →
        (DirichletCharacter.LFunction χ σ₀).im = 0 ∧ 0 < (DirichletCharacter.LFunction χ σ₀).re := by
      intro q _ χ hsq hne
      exact hLP q χ hsq hne σ₀ (hnz q χ hsq hne) σ₀ le_rfl
    refine siegel_product_character_inequality hP hS hKey hL hε χ₁ h1sq h1ne h78 hσ₀1 (hKa σ₀ le_rfl hσ₀1) ?_
    intro q _ χ ψ hsq hne hψne hψ
    have hψsq := product_real_characters_sq_eq_one χ₁ χ ψ h1sq hsq hψ
    obtain ⟨hz_im, hz_re⟩ := hZ σ₀ (by linarith) hσ₀1
    obtain ⟨a_im, a_re⟩ := hpos q₁ χ₁ h1sq h1ne
    obtain ⟨b_im, b_re⟩ := hpos q χ hsq hne
    obtain ⟨c_im, c_re⟩ := hpos (q₁ * q) ψ hψsq hψne
    have hre : (Fbq χ₁ χ ψ σ₀).re = (riemannZeta σ₀).re * (DirichletCharacter.LFunction χ₁ σ₀).re *
        (DirichletCharacter.LFunction χ σ₀).re * (DirichletCharacter.LFunction ψ σ₀).re := by
      simp [Fbq, Complex.mul_re, Complex.mul_im, hz_im, a_im, b_im, c_im]
    rw [hre]
    have hp := mul_pos (mul_pos a_re b_re) c_re
    have hn := mul_neg_of_neg_of_pos hz_re hp
    nlinarith

end Formalism.ZeroFreeDirichlet
end
end
end

-- Source module: Formalism.LandauZeroFreeBounds.FinalSiegel

section

@[expose] public section

namespace Formalism.ZeroFreeDirichlet

theorem bqKey : BqKey :=
  product_lfunction_key_inequality dirichlet_product_coefficients dirichlet_product_entire product_lfunction_growth_bound lfunction_one_upper_bound

theorem siegelLower : SiegelLower :=
  siegel_theorem_of exists_product_character exists_real_nontrivial_character bqKey lfunction_one_upper_bound zeta_negative_real_axis
    real_lfunction_real_on_reals lfunction_one_same_character

end Formalism.ZeroFreeDirichlet
end
end
