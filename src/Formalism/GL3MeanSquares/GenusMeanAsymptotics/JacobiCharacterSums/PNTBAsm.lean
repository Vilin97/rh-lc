module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.DeuringHeilbronnM
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTBAsmA
public import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTEOf
import Mathlib.NumberTheory.LSeries.Nonvanishing

-- Source module: Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTBAsmB

section

@[expose] public section

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

def excI {M : ℕ} (e : Option (DirichletCharacter ℂ M × ℝ)) (χ : DirichletCharacter ℂ M) : ℝ :=
  match e with
  | none => 0
  | some (χ₁, _) => if χ = χ₁ then 1 else 0

def excT {M : ℕ} (e : Option (DirichletCharacter ℂ M × ℝ)) (χ : DirichletCharacter ℂ M) (y : ℝ) : ℂ :=
  match e with
  | none => 0
  | some (χ₁, β₁) => if χ = χ₁ then (y : ℂ) ^ (β₁ : ℂ) / (β₁ : ℂ) else 0

theorem mainPsi_eq {M : ℕ} (e : Option (DirichletCharacter ℂ M × ℝ)) (χ : DirichletCharacter ℂ M) (y : ℝ) :
    mainPsi e χ y = (if χ = 1 then (y : ℂ) else 0) - excT e χ y := rfl

theorem sum_excI_le {M : ℕ} [NeZero M] (e : Option (DirichletCharacter ℂ M × ℝ)) :
    ∑ χ : DirichletCharacter ℂ M, excI e χ ≤ 1 := by
  rcases e with _ | ⟨χ₁, β₁⟩
  · simp [excI]
  · have h : (∑ χ : DirichletCharacter ℂ M, excI (some (χ₁, β₁)) χ) = excI (some (χ₁, β₁)) χ₁ :=
      Finset.sum_eq_single χ₁ (fun b _ hb => if_neg hb) (fun h => absurd (Finset.mem_univ _) h)
    rw [h]
    exact (if_pos rfl).le

theorem excW_le_one {M : ℕ} (e : Option (DirichletCharacter ℂ M × ℝ)) (χ : DirichletCharacter ℂ M) (ρ : ℂ) :
    excW e χ ρ ≤ 1 := by
  rcases e with _ | ⟨χ₁, β₁⟩
  · simp [excW]
  · simp only [excW]; split_ifs <;> norm_num

theorem card_char_le (M : ℕ) [NeZero M] :
    ((Finset.univ : Finset (DirichletCharacter ℂ M)).card : ℝ) ≤ M := by
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
    DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ M]
  exact_mod_cast Nat.totient_le M

theorem sum_excW_le {M : ℕ} (e : Option (DirichletCharacter ℂ M × ℝ)) (χ : DirichletCharacter ℂ M)
    (Z : Finset ℂ) (y : ℝ) (hy : 1 ≤ y) (hZ : ∀ ρ ∈ Z, ρ.re < 1) :
    ∑ ρ ∈ Z, (excW e χ ρ : ℝ) * y ^ (ρ.re - 1) ≤ excI e χ := by
  rcases e with _ | ⟨χ₁, β₁⟩
  · simp [excW, excI]
  · simp only [excW, excI]
    by_cases h : χ = χ₁
    · simp only [h, true_and, if_true]
      have : ∀ ρ ∈ Z, (((if ρ = (β₁ : ℂ) then 1 else 0 : ℕ) : ℝ)) * y ^ (ρ.re - 1)
          = if ρ = (β₁ : ℂ) then y ^ (ρ.re - 1) else 0 := by
        intro ρ _; split_ifs <;> simp
      rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
      split_ifs with hm
      · exact Real.rpow_le_one_of_one_le_of_nonpos hy (by linarith [hZ _ hm])
      · norm_num
    · simp [h]

theorem excT_sub_le {M : ℕ} [NeZero M] (hM : 3 ≤ M) (e : Option (DirichletCharacter ℂ M × ℝ))
    (he : ∀ p, e = some p → IsExcPair p.1 p.2) (χ : DirichletCharacter ℂ M)
    (Z : Finset ℂ) (y κ T : ℝ) (hy : 1 ≤ y) (hT : 0 ≤ T)
    (hZ : ∀ ρ : ℂ, IsLZero χ ρ → 1 - κ / 2 ≤ ρ.re → |ρ.im| ≤ T → ρ ∈ Z) :
    ‖excT e χ y - ∑ ρ ∈ Z, (excW e χ ρ : ℂ) * (y : ℂ) ^ ρ / ρ‖ ≤ excI e χ * (2 * y * y ^ (-(κ / 2))) := by
  rcases e with _ | ⟨χ₁, β₁⟩
  · simp [excW, excI, excT]
  · obtain ⟨-, hne, hz, hlo, hhi⟩ := he _ rfl
    simp only at hne hz hlo hhi
    simp only [excW, excI, excT]
    by_cases h : χ = χ₁
    · subst h
      simp only [true_and, if_true]
      have : ∀ ρ ∈ Z, (((if ρ = (β₁ : ℂ) then 1 else 0 : ℕ) : ℂ)) * (y : ℂ) ^ ρ / ρ
          = if ρ = (β₁ : ℂ) then (y : ℂ) ^ ρ / ρ else 0 := by
        intro ρ _; split_ifs <;> simp
      rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
      have hy0 : 0 < y := by linarith
      split_ifs with hm
      · simp only [sub_self, norm_zero, one_mul]; positivity
      · have hb : β₁ < 1 - κ / 2 := by
          by_contra hcon
          push Not at hcon
          exact hm (hZ _ ⟨Or.inl hne, hz⟩ (by simpa using hcon) (by simpa using hT))
        have hl : 1 ≤ Real.log M := by
          rw [Real.le_log_iff_exp_le (by positivity)]
          have : (3 : ℝ) ≤ M := by exact_mod_cast hM
          linarith [Real.exp_one_lt_d9]
        have hb2 : 1 / 2 ≤ β₁ := by
          have : 1 / (8 * Real.log M) ≤ 1 / 8 := by
            apply one_div_le_one_div_of_le (by norm_num); linarith
          linarith
        rw [sub_zero, one_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy0, Complex.ofReal_re,
          Complex.norm_real, Real.norm_of_nonneg (by linarith)]
        have h1 : y ^ β₁ ≤ y ^ (1 - κ / 2) := Real.rpow_le_rpow_of_exponent_le hy hb.le
        have h2 : y ^ (1 - κ / 2) = y * y ^ (-(κ / 2)) := by
          rw [sub_eq_add_neg, Real.rpow_add hy0, Real.rpow_one]
        rw [div_le_iff₀ (by linarith)]
        have h3 : 0 ≤ y * y ^ (-(κ / 2)) := by positivity
        nlinarith
    · simp [h]

theorem one_char {M : ℕ} [NeZero M] (hM : 3 ≤ M) (e : Option (DirichletCharacter ℂ M × ℝ))
    (he : ∀ p, e = some p → IsExcPair p.1 p.2) (χ : DirichletCharacter ℂ M)
    (Z : Finset ℂ) (m : ℂ → ℕ) (y κ T R : ℝ) (hy : 1 ≤ y) (hT : 0 ≤ T)
    (hZ : ∀ ρ : ℂ, IsLZero χ ρ → 1 - κ / 2 ≤ ρ.re → |ρ.im| ≤ T → ρ ∈ Z)
    (hre : ∀ ρ ∈ Z, 1 / 2 ≤ ρ.re) (hm : ∀ ρ ∈ Z, 1 ≤ m ρ)
    (hR : ‖psiChi χ y - (if χ = 1 then (y : ℂ) else 0) + ∑ ρ ∈ Z, (m ρ : ℂ) * (y : ℂ) ^ ρ / ρ‖ ≤ R) :
    ‖psiChi χ y - mainPsi e χ y‖ ≤
      R + 2 * y * ∑ ρ ∈ Z, ((m ρ : ℝ) - (excW e χ ρ : ℝ)) * y ^ (ρ.re - 1)
        + excI e χ * (2 * y * y ^ (-(κ / 2))) := by
  have hy0 : 0 < y := by linarith
  have e1 : psiChi χ y - mainPsi e χ y
      = (psiChi χ y - (if χ = 1 then (y : ℂ) else 0) + ∑ ρ ∈ Z, (m ρ : ℂ) * (y : ℂ) ^ ρ / ρ)
        - ∑ ρ ∈ Z, ((m ρ : ℂ) - (excW e χ ρ : ℂ)) * (y : ℂ) ^ ρ / ρ
        + (excT e χ y - ∑ ρ ∈ Z, (excW e χ ρ : ℂ) * (y : ℂ) ^ ρ / ρ) := by
    rw [mainPsi_eq]
    have : ∑ ρ ∈ Z, ((m ρ : ℂ) - (excW e χ ρ : ℂ)) * (y : ℂ) ^ ρ / ρ
        = ∑ ρ ∈ Z, (m ρ : ℂ) * (y : ℂ) ^ ρ / ρ - ∑ ρ ∈ Z, (excW e χ ρ : ℂ) * (y : ℂ) ^ ρ / ρ := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun ρ _ => by ring)
    rw [this]
    by_cases hχ : χ = 1
    · simp only [if_pos hχ]; ring
    · simp only [if_neg hχ]; ring
  have h2 : ‖∑ ρ ∈ Z, ((m ρ : ℂ) - (excW e χ ρ : ℂ)) * (y : ℂ) ^ ρ / ρ‖
      ≤ 2 * y * ∑ ρ ∈ Z, ((m ρ : ℝ) - (excW e χ ρ : ℝ)) * y ^ (ρ.re - 1) := by
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
    intro ρ hρ
    have hw : (0 : ℝ) ≤ (m ρ : ℝ) - (excW e χ ρ : ℝ) := by
      have : ((excW e χ ρ : ℕ) : ℝ) ≤ (m ρ : ℝ) := by exact_mod_cast (excW_le_one e χ ρ).trans (hm ρ hρ)
      linarith
    have hn : ‖(m ρ : ℂ) - (excW e χ ρ : ℂ)‖ = (m ρ : ℝ) - (excW e χ ρ : ℝ) := by
      have : (m ρ : ℂ) - (excW e χ ρ : ℂ) = (((m ρ : ℝ) - (excW e χ ρ : ℝ) : ℝ) : ℂ) := by push_cast; rfl
      rw [this, Complex.norm_real, Real.norm_of_nonneg hw]
    have hρn : 1 / 2 ≤ ‖ρ‖ := (hre ρ hρ).trans ((le_abs_self _).trans (Complex.abs_re_le_norm ρ))
    rw [norm_div, norm_mul, hn, Complex.norm_cpow_eq_rpow_re_of_pos hy0]
    have h3 : y ^ ρ.re = y * y ^ (ρ.re - 1) := by
      rw [Real.rpow_sub hy0, Real.rpow_one]; field_simp
    rw [div_le_iff₀ (by linarith), h3]
    have h4 : 0 ≤ ((m ρ : ℝ) - (excW e χ ρ : ℝ)) * (y * y ^ (ρ.re - 1)) := by positivity
    nlinarith
  rw [e1]
  refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add hR h2)) ?_)
  exact excT_sub_le hM e he χ Z y κ T hy hT hZ

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end
end

-- Source module: Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTBAsm

section

@[expose] public section

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet



theorem psi_relative_far_range : PsiRelBOf := by
  intro hE hS hZS cA hcA
  obtain ⟨κ, hκ, hκ', hZ⟩ := hZS
  obtain ⟨C, hC, hEx⟩ := hE κ hκ hκ'
  obtain ⟨cz, Az, Cz, hcz, hZ⟩ := hZ C 12 (by norm_num)
  obtain ⟨C₀, B, hC₀, hB, hnum⟩ := num_main cA κ C hcA hκ hC
  obtain ⟨c₁, hc₁, heta⟩ := etaOf_lower 1 one_pos
  refine ⟨min cz (cA ^ 2), 22 * |Az| + B / c₁, max Cz C₀, lt_min hcz (by positivity), ?_⟩
  intro M _ h8 y hy hr1 hr2
  have hM8 : 8 ≤ M := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) h8
  have hM8r : (8 : ℝ) ≤ M := by exact_mod_cast hM8
  have hM3 : 3 ≤ M := by omega
  have hM0 : (0 : ℝ) < M := by linarith
  have hy0 : 0 < y := by linarith
  have hT8 : (8 : ℝ) ≤ (M : ℝ) ^ (12 : ℝ) := by
    calc (8 : ℝ) ≤ (M : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]; exact hM8r
      _ ≤ (M : ℝ) ^ (12 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hδ0 : 0 < ((M : ℝ) ^ 5)⁻¹ := by positivity
  have hδ : ((M : ℝ) ^ 5)⁻¹ ≤ 1 / 2 := by
    rw [one_div]
    apply inv_anti₀ (by norm_num)
    calc (2 : ℝ) ≤ (M : ℝ) ^ 1 := by rw [pow_one]; linarith
      _ ≤ (M : ℝ) ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
  choose Z m K h1 h2 h3 h4 h5 h6 using fun χ => hEx M χ ((M : ℝ) ^ (12 : ℝ)) hM3 (by linarith)
  have hl : 1 ≤ Real.log M := one_le_log_of_three_le (by linarith)
  have hll : 1 ≤ Real.log (Real.log M + 2) := one_le_log_of_three_le (by linarith)
  have hL : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hrz : Cz * Real.log M * Real.log (Real.log M + 2) ≤ Real.log y := by
    refine le_trans ?_ hr1
    have : Cz ≤ max Cz C₀ := le_max_left _ _
    gcongr
  have hrn : C₀ * Real.log M * Real.log (Real.log M + 2) ≤ Real.log y := by
    refine le_trans ?_ hr1
    have : C₀ ≤ max Cz C₀ := le_max_right _ _
    gcongr
  have hZS := hZ M Z m h8 h1 h3 h4 h5 y hy hrz
  have hN := hnum M y hM8r hy hrn hr2
  generalize hTdef : (M : ℝ) ^ (12 : ℝ) = T at *
  generalize hδdef : ((M : ℝ) ^ 5)⁻¹ = δ at *
  generalize htdef : y ^ (-(κ / 2)) = t at *
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = C * (((M : ℝ) * T) ^ C * t
      + Real.log (2 * y) * Real.log ((M : ℝ) * T) ^ 2 / T) := ⟨_, rfl⟩
  rw [← hEdef] at hN
  have hT0 : 0 < T := by linarith
  have ht0 : 0 ≤ t := by rw [← htdef]; positivity
  have hlg : 0 ≤ Real.log (2 * y) := Real.log_nonneg (by linarith)
  have hE0 : 0 ≤ E := by rw [hEdef]; positivity
  have hre : ∀ χ, ∀ ρ ∈ Z χ, 1 / 2 ≤ ρ.re ∧ ρ.re < 1 := by
    intro χ ρ hρ
    obtain ⟨hz, hlo, -⟩ := h1 χ ρ hρ
    refine ⟨by linarith, ?_⟩
    by_contra hcon
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ hz.1 (not_lt.1 hcon) hz.2
  have hEu : ∀ u : ℝ, y ≤ u → u ≤ 2 * y →
      C * (((M : ℝ) * T) ^ C * u ^ (-(κ / 2)) + Real.log u * Real.log ((M : ℝ) * T) ^ 2 / T) ≤ E := by
    intro u hu1 hu2
    rw [hEdef]
    have a1 : u ^ (-(κ / 2)) ≤ t := by
      rw [← htdef]; exact Real.rpow_le_rpow_of_nonpos hy0 hu1 (by linarith)
    have a2 : Real.log u ≤ Real.log (2 * y) := Real.log_le_log (by linarith) hu2
    gcongr
  have hsharp : ∀ χ : DirichletCharacter ℂ M,
      ‖psiChi χ y - (if χ = 1 then (y : ℂ) else 0) + ∑ ρ ∈ Z χ, (m χ ρ : ℂ) * (y : ℂ) ^ ρ / ρ‖ ≤
      4 * y * E / δ + 20 * δ * y * ∑ ρ ∈ Z χ, (m χ ρ : ℝ) * y ^ (ρ.re - 1)
        + 4 * (δ * y + 1) * Real.log (2 * y) := by
    intro χ
    refine hS M χ (Z χ) (m χ) (K χ) E y δ (hre χ) hy hδ0 hδ ?_
    intro u hu
    have hu1 : y ≤ u := by
      rcases hu with rfl | rfl
      · exact le_rfl
      · nlinarith
    have hu2 : u ≤ 2 * y := by
      rcases hu with rfl | rfl
      · linarith
      · nlinarith
    exact (h6 χ u (by linarith)).trans (hEu u hu1 hu2)
  obtain ⟨W, hW⟩ : ∃ W : DirichletCharacter ℂ M → ℝ, W = fun χ =>
      ∑ ρ ∈ Z χ, ((m χ ρ : ℝ) - (excW (eOf M) χ ρ : ℝ)) * y ^ (ρ.re - 1) := ⟨_, rfl⟩
  have hW0 : ∀ χ, 0 ≤ W χ := by
    intro χ
    rw [hW]
    apply Finset.sum_nonneg
    intro ρ hρ
    have : ((excW (eOf M) χ ρ : ℕ) : ℝ) ≤ (m χ ρ : ℝ) := by
      exact_mod_cast (excW_le_one (eOf M) χ ρ).trans (h3 χ ρ hρ)
    have h0 : (0 : ℝ) ≤ (m χ ρ : ℝ) - (excW (eOf M) χ ρ : ℝ) := by linarith
    positivity
  have hmW : ∀ χ, ∑ ρ ∈ Z χ, (m χ ρ : ℝ) * y ^ (ρ.re - 1) ≤ W χ + excI (eOf M) χ := by
    intro χ
    have := sum_excW_le (eOf M) χ (Z χ) y (by linarith) (fun ρ hρ => (hre χ ρ hρ).2)
    have e : ∑ ρ ∈ Z χ, (m χ ρ : ℝ) * y ^ (ρ.re - 1)
        = W χ + ∑ ρ ∈ Z χ, (excW (eOf M) χ ρ : ℝ) * y ^ (ρ.re - 1) := by
      rw [hW, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun ρ _ => by ring)
    linarith
  have hper : ∀ χ : DirichletCharacter ℂ M, ‖psiChi χ y - mainPsi (eOf M) χ y‖ ≤
      (4 * y * E / δ + 4 * (δ * y + 1) * Real.log (2 * y)) + 22 * y * W χ
        + excI (eOf M) χ * (20 * δ * y + 2 * y * t) := by
    intro χ
    have a := one_char hM3 (eOf M) (fun p hp => eOf_exc M p hp) χ (Z χ) (m χ) y κ T _ (by linarith)
      hT0.le (h2 χ) (fun ρ hρ => (hre χ ρ hρ).1) (h3 χ) (hsharp χ)
    rw [htdef] at a
    have a' : ‖psiChi χ y - mainPsi (eOf M) χ y‖ ≤
        4 * y * E / δ + 20 * δ * y * ∑ ρ ∈ Z χ, (m χ ρ : ℝ) * y ^ (ρ.re - 1)
        + 4 * (δ * y + 1) * Real.log (2 * y) + 2 * y * W χ + excI (eOf M) χ * (2 * y * t) := by
      rw [hW]; exact a
    have b : 20 * δ * y * ∑ ρ ∈ Z χ, (m χ ρ : ℝ) * y ^ (ρ.re - 1)
        ≤ 20 * δ * y * (W χ + excI (eOf M) χ) := mul_le_mul_of_nonneg_left (hmW χ) (by positivity)
    have c : 20 * δ * y * W χ ≤ 20 * y * W χ := by
      have : 0 ≤ y * W χ := mul_nonneg hy0.le (hW0 χ)
      nlinarith
    linarith
  have hsum : ∑ χ : DirichletCharacter ℂ M, ‖psiChi χ y - mainPsi (eOf M) χ y‖ ≤
      (M : ℝ) * (4 * y * E / δ + 4 * (δ * y + 1) * Real.log (2 * y)) + 22 * y * ∑ χ, W χ
        + (20 * δ * y + 2 * y * t) := by
    refine (Finset.sum_le_sum (fun χ _ => hper χ)).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      ← Finset.mul_sum, ← Finset.sum_mul]
    have q0 : 0 ≤ 4 * y * E / δ + 4 * (δ * y + 1) * Real.log (2 * y) := by positivity
    have q1 : 0 ≤ 20 * δ * y + 2 * y * t := by positivity
    have r1 := mul_le_mul_of_nonneg_right (card_char_le M) q0
    have r2 := mul_le_mul_of_nonneg_right (sum_excI_le (eOf M)) q1
    linarith
  have hη0 : 0 < etaOf M := etaOf_pos M (by omega)
  have hex := inv_le_exp hcA (lt_min hcz (by positivity : 0 < cA ^ 2)) (min_le_right _ _) hM8r hy hr2
  have hηM : (M : ℝ)⁻¹ ≤ etaOf M / c₁ := by
    have := heta M hM3
    rw [Real.rpow_neg_one] at this
    rw [le_div_iff₀ hc₁]; linarith
  have hMi : 0 < (M : ℝ)⁻¹ := by positivity
  have hWs : ∑ χ, W χ ≤ |Az| * etaOf M * Real.exp (-(min cz (cA ^ 2) * Real.log y / Real.log M)) := by
    rw [hW]
    refine hZS.trans ?_
    have e1 : Real.exp (-(cz * Real.log y / Real.log M))
        ≤ Real.exp (-(min cz (cA ^ 2) * Real.log y / Real.log M)) := by
      apply Real.exp_le_exp.2
      apply neg_le_neg
      have : min cz (cA ^ 2) ≤ cz := min_le_left _ _
      gcongr
    have e2 : Az ≤ |Az| := le_abs_self _
    gcongr
  have hfin : B * y * ((M : ℝ)⁻¹ * (M : ℝ)⁻¹)
      ≤ B * y * (etaOf M / c₁ * Real.exp (-(min cz (cA ^ 2) * Real.log y / Real.log M))) := by
    gcongr
  generalize Real.exp (-(min cz (cA ^ 2) * Real.log y / Real.log M)) = ex at *
  have f1 : 22 * y * ∑ χ, W χ ≤ 22 * y * (|Az| * etaOf M * ex) :=
    mul_le_mul_of_nonneg_left hWs (by positivity)
  have f2 : (22 * |Az| + B / c₁) * y * etaOf M * ex
      = 22 * y * (|Az| * etaOf M * ex) + B * y * (etaOf M / c₁ * ex) := by ring
  rw [f2]
  linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end
end
