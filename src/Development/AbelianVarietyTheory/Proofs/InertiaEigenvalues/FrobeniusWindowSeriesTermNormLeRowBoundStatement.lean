module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MooreNorm
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
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
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Order.Interval.Finset.Box
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WindowAdditive

section

@[expose] public section

namespace GlobalTheory.PMonE

theorem window_additive (q : ℝ) (hq : 2 ≤ q) (r : ℤ) (α f : ℤ → ℝ) (hα : Antitone α)
    (hf : ∀ J, f (J + 1) - f J = (α J - α (J + 1)) * (q ^ (r - J) - 1)) :
    (∀ J, J ≤ r → f J + α J ≤ f r + α r) ∧
    (∀ J, r + 1 ≤ J → f J - α J / 2 ≤ f r - α (r + 1) / 2) := by
  have hd : ∀ J, 0 ≤ α J - α (J + 1) := fun J => sub_nonneg.2 (hα (by omega))
  have hq1 : (1 : ℝ) ≤ q := by linarith
  constructor
  · intro J hJ
    induction J, hJ using Int.leInductionDown with
    | base => exact le_rfl
    | pred n hn ih =>
      have h1 := hf (n - 1)
      have h2 := hd (n - 1)
      rw [sub_add_cancel] at h1 h2
      have h3 : q ^ (1 : ℤ) ≤ q ^ (r - (n - 1)) := zpow_le_zpow_right₀ hq1 (by omega)
      rw [zpow_one] at h3
      nlinarith [mul_nonneg h2 (show 0 ≤ q ^ (r - (n - 1)) - 2 by linarith)]
  · intro J hJ
    induction J, hJ using Int.leInduction with
    | base =>
      have h1 := hf r
      rw [sub_self, zpow_zero, sub_self, mul_zero] at h1
      linarith
    | succ n hn ih =>
      have h1 := hf n
      have h2 := hd n
      have h3 : q ^ (r - n) ≤ q ^ (-1 : ℤ) := zpow_le_zpow_right₀ hq1 (by omega)
      rw [zpow_neg_one] at h3
      have h4 : q⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hq
      nlinarith [mul_nonneg h2 (show 0 ≤ 2⁻¹ - q ^ (r - n) by linarith)]

theorem window_ineq : ∀ (p h : ℕ), 1 < p → 0 < h → ∀ a ρ : ℤ → ℝ, (∀ J, 0 < a J) → (∀ J, 0 < ρ J) → Antitone a → a 0 < p * a ((h : ℤ) - 1) → (∀ J, a (J + h) = a J / p) → (∀ J, ρ (J + h) = ρ J ^ ((p : ℝ) ^ h)⁻¹) → (∀ J, a (J + 1) * ρ (J + 1) ^ ((p : ℝ) ^ J) = a J * ρ J ^ ((p : ℝ) ^ J)) → ∀ r : ℕ, r < h → ∀ J : ℤ, a J * ρ J ^ ((p : ℝ) ^ r) ≤ a r * ρ r ^ ((p : ℝ) ^ r) ∧ (J < 0 → a J * ρ J ^ ((p : ℝ) ^ r) < a r * ρ r ^ ((p : ℝ) ^ r)) ∧ (J ≤ -(h : ℤ) → a J * ρ J ^ ((p : ℝ) ^ r) ≤ a r * ρ r ^ ((p : ℝ) ^ r) / p) ∧ (3 * (h : ℤ) ≤ J → a J * ρ J ^ ((p : ℝ) ^ r) ≤ a r * ρ r ^ ((p : ℝ) ^ r) / p) := by
  intro p h hp hh a ρ ha hρ hanti hlt hper _ hrel r hr J
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  set α : ℤ → ℝ := fun J => Real.log (a J) with hαdef
  set f : ℤ → ℝ := fun J => Real.log (a J * ρ J ^ ((p : ℝ) ^ r)) with hfdef
  have hα : Antitone α := fun i j hij => Real.log_le_log (ha j) (hanti hij)
  have hpos : ∀ J, 0 < a J * ρ J ^ ((p : ℝ) ^ r) := fun J =>
    mul_pos (ha J) (Real.rpow_pos_of_pos (hρ J) _)
  have hlog : ∀ (J : ℤ) (e : ℝ), Real.log (a J * ρ J ^ e) = α J + e * Real.log (ρ J) := by
    intro J e
    rw [Real.log_mul (ha J).ne' (Real.rpow_pos_of_pos (hρ J) _).ne', Real.log_rpow (hρ J)]
  have hf : ∀ J, f (J + 1) - f J = (α J - α (J + 1)) * ((p : ℝ) ^ ((r : ℤ) - J) - 1) := by
    intro J
    have h1 := congrArg Real.log (hrel J)
    rw [hlog, hlog] at h1
    have h2 : (p : ℝ) ^ r = (p : ℝ) ^ ((r : ℤ) - J) * (p : ℝ) ^ J := by
      rw [← zpow_add₀ hp0.ne', sub_add_cancel, zpow_natCast]
    simp only [hfdef, hlog]
    rw [h2]
    linear_combination (p : ℝ) ^ ((r : ℤ) - J) * h1
  obtain ⟨hL, hR⟩ := window_additive p hp2 r α f hα hf
  have hαper : ∀ J, α (J + h) = α J - Real.log p := by
    intro J
    simp only [hαdef]
    rw [hper, Real.log_div (ha J).ne' hp0.ne']
  have hdiv : f J ≤ f r - Real.log p →
      a J * ρ J ^ ((p : ℝ) ^ r) ≤ a r * ρ r ^ ((p : ℝ) ^ r) / p := by
    intro H
    rw [← Real.log_le_log_iff (hpos J) (div_pos (hpos r) hp0),
      Real.log_div (hpos r).ne' hp0.ne']
    exact H
  have hr0 : α r ≤ α 0 := hα (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Real.log_le_log_iff (hpos J) (hpos r)]
    change f J ≤ f r
    rcases le_or_gt J r with hJ | hJ
    · have := hL J hJ
      have := hα hJ
      linarith
    · have := hR J hJ
      have := hα (show (r : ℤ) + 1 ≤ J from hJ)
      linarith
  · intro hJ
    rw [← Real.log_lt_log_iff (hpos J) (hpos r)]
    change f J < f r
    have h1 := hL J (by omega)
    have h2 : α (-1) ≤ α J := hα (by omega)
    have h3 : α 0 < α (-1) := by
      apply Real.log_lt_log (ha 0)
      have h4 := hlt
      have h5 := hper (-1)
      rw [show (-1 : ℤ) + h = (h : ℤ) - 1 by ring] at h5
      rw [h5, mul_div_cancel₀ _ hp0.ne'] at h4
      exact h4
    linarith
  · intro hJ
    apply hdiv
    have h1 := hL J (by omega)
    have h2 : α (-h) ≤ α J := hα hJ
    have h3 := hαper (-h)
    rw [neg_add_cancel] at h3
    linarith
  · intro hJ
    apply hdiv
    have h1 := hR J (by omega)
    have h2 : α J ≤ α (h + h + h) := hα (by omega)
    have h3 := hαper (h + h)
    have h4 := hαper h
    have h5 : α h ≤ α (r + 1) := hα (by omega)
    linarith

end GlobalTheory.PMonE
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusWindowSeriesTermNormLeRowBound

section

@[expose] public section

noncomputable section

namespace GlobalTheory.PMonE.WinBounds

open GlobalTheory.PMonE

theorem pow_iter_frobeniusEquiv_symm {F : Type} [CommRing F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]
    (x : F) (m : ℕ) : (((frobeniusEquiv F p).symm)^[m] x) ^ p ^ m = x := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', pow_succ', pow_mul]
    have h := frobenius_apply_frobeniusEquiv_symm F p (((frobeniusEquiv F p).symm)^[m] x)
    rw [frobenius_def] at h
    rw [h, ih]

variable {F : Type} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]

theorem norm_pw (k : ℤ) (x : F) : ‖pw p k x‖ = ‖x‖ ^ ((p : ℝ) ^ k) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  unfold pw
  split_ifs with hk
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [norm_pow, Int.toNat_natCast, zpow_natCast, ← Nat.cast_pow, Real.rpow_natCast]
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, k = -(m : ℤ) := ⟨(-k).toNat, by omega⟩
    subst hm
    rw [neg_neg, Int.toNat_natCast]
    have hy := pow_iter_frobeniusEquiv_symm p x m
    conv_rhs => rw [← hy]
    rw [norm_pow, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), Nat.cast_pow, zpow_neg, zpow_natCast,
      mul_inv_cancel₀ (by positivity), Real.rpow_one]

theorem norm_term (k : ℕ) (ϖ : F) (hϖ : ‖ϖ‖ = (p : ℝ)⁻¹) (lam π : Fin (k + 1) → F) (r j : Fin (k + 1)) (n : ℤ) :
    ‖term p ϖ lam π r j n‖ = ‖lam j‖ * (p : ℝ) ^ n * ‖π j‖ ^ ((p : ℝ) ^ (((r : ℕ) : ℤ) + n * ((k : ℤ) + 1))) := by
  unfold term
  rw [norm_mul, norm_mul, norm_zpow, hϖ, norm_pw, inv_zpow', neg_neg]
  push_cast
  rfl

def idx (k : ℕ) (J : ℤ) : Fin (k + 1) :=
  ⟨(J % ((k : ℤ) + 1)).toNat, by
    have h1 := Int.emod_nonneg J (show ((k : ℤ) + 1) ≠ 0 by omega)
    have h2 := Int.emod_lt_of_pos J (show (0 : ℤ) < (k : ℤ) + 1 by omega)
    omega⟩

theorem idx_spec (k : ℕ) (j : Fin (k + 1)) (m : ℤ) :
    idx k (((j : ℕ) : ℤ) + ((k : ℤ) + 1) * m) = j ∧ (((j : ℕ) : ℤ) + ((k : ℤ) + 1) * m) / ((k : ℤ) + 1) = m := by
  have hj := j.isLt
  have h0 : ((j : ℕ) : ℤ) / ((k : ℤ) + 1) = 0 := Int.ediv_eq_zero_of_lt (by omega) (by omega)
  have h1 : ((j : ℕ) : ℤ) % ((k : ℤ) + 1) = j := Int.emod_eq_of_lt (by omega) (by omega)
  constructor
  · ext
    simp [idx, Int.add_mul_emod_self_left, h1]
  · rw [Int.add_mul_ediv_left _ _ (by omega), h0, zero_add]

theorem decomp (k : ℕ) (J : ℤ) : ∃ j : Fin (k + 1), ∃ m : ℤ, J = ((j : ℕ) : ℤ) + ((k : ℤ) + 1) * m := by
  refine ⟨idx k J, J / ((k : ℤ) + 1), ?_⟩
  have h1 := Int.emod_nonneg J (show ((k : ℤ) + 1) ≠ 0 by omega)
  have h2 : J % ((k : ℤ) + 1) = J - ((k : ℤ) + 1) * (J / ((k : ℤ) + 1)) := Int.emod_def _ _
  show J = (((J % ((k : ℤ) + 1)).toNat : ℕ) : ℤ) + _
  rw [Int.toNat_of_nonneg h1]
  linarith

def aW (k : ℕ) (lam : Fin (k + 1) → F) (J : ℤ) : ℝ :=
  ‖lam (idx k J)‖ * (p : ℝ) ^ (-(J / ((k : ℤ) + 1)))

def rW (k : ℕ) (π : Fin (k + 1) → F) (J : ℤ) : ℝ :=
  ‖π (idx k J)‖ ^ ((p : ℝ) ^ (-(((k : ℤ) + 1) * (J / ((k : ℤ) + 1)))))

theorem aW_at (k : ℕ) (lam : Fin (k + 1) → F) (j : Fin (k + 1)) (m : ℤ) :
    aW p k lam (((j : ℕ) : ℤ) + ((k : ℤ) + 1) * m) = ‖lam j‖ * (p : ℝ) ^ (-m) := by
  obtain ⟨h1, h2⟩ := idx_spec k j m
  simp only [aW, h1, h2]

theorem rW_at (k : ℕ) (π : Fin (k + 1) → F) (j : Fin (k + 1)) (m : ℤ) :
    rW p k π (((j : ℕ) : ℤ) + ((k : ℤ) + 1) * m) = ‖π j‖ ^ ((p : ℝ) ^ (-(((k : ℤ) + 1) * m))) := by
  obtain ⟨h1, h2⟩ := idx_spec k j m
  simp only [rW, h1, h2]

end GlobalTheory.PMonE.WinBounds

namespace GlobalTheory.PMonE.WinBounds

open GlobalTheory.PMonE

theorem term_le_bound : ∀ (F : Type) [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (k : ℕ) (ϖ : F), ‖ϖ‖ = (p : ℝ)⁻¹ → ∀ lam π : Fin (k + 1) → F, (∀ j, lam j ≠ 0) → Antitone (fun j => ‖lam j‖) → (∀ i j, ‖lam i‖ < p * ‖lam j‖) → (∀ j, π j ≠ 0 ∧ ‖π j‖ < 1) → (∀ j : Fin k, ‖lam j.succ‖ * ‖π j.succ‖ ^ p ^ (j : ℕ) = ‖lam j.castSucc‖ * ‖π j.castSucc‖ ^ p ^ (j : ℕ)) → (‖lam 0‖ / p) ^ p * ‖π 0‖ = (‖lam (Fin.last k)‖ * ‖π (Fin.last k)‖ ^ p ^ k) ^ p → ∀ (r j : Fin (k + 1)) (n : ℤ), ‖term p ϖ lam π r j n‖ ≤ ‖lam r * π r ^ p ^ (r : ℕ)‖ ∧ (0 < n → ‖term p ϖ lam π r j n‖ < ‖lam r * π r ^ p ^ (r : ℕ)‖) ∧ (2 < |n| → ‖term p ϖ lam π r j n‖ ≤ ‖lam r * π r ^ p ^ (r : ℕ)‖ / p) := by
  intro F _ p _ _ _ k ϖ hϖ lam π hlam hanti hratio hπ hrel1 hrel2 r j n
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hpne : (p : ℝ) ≠ 0 := hp0.ne'
  have ha : ∀ J, 0 < aW p k lam J := by
    intro J; unfold aW; exact mul_pos (norm_pos_iff.2 (hlam _)) (zpow_pos hp0 _)
  have hρ : ∀ J, 0 < rW p k π J := by
    intro J; unfold rW; exact Real.rpow_pos_of_pos (norm_pos_iff.2 (hπ _).1) _
  have hrp : ∀ (x : ℝ), 0 ≤ x → ∀ c d : ℤ, (x ^ ((p : ℝ) ^ c)) ^ ((p : ℝ) ^ d) = x ^ ((p : ℝ) ^ (c + d)) := by
    intro x hx c d; rw [← Real.rpow_mul hx, zpow_add₀ hpne]
  have hnat : ∀ (x : ℝ) (e : ℕ), x ^ ((p : ℝ) ^ (e : ℤ)) = x ^ (p ^ e) := by
    intro x e; rw [zpow_natCast, ← Nat.cast_pow, Real.rpow_natCast]
  have hstep : ∀ J, aW p k lam (J + 1) ≤ aW p k lam J := by
    intro J
    obtain ⟨i, m, rfl⟩ := decomp k J
    induction i using Fin.lastCases with
    | last =>
      have e1 : (((Fin.last k : ℕ)) : ℤ) + ((k : ℤ) + 1) * m + 1
          = (((0 : Fin (k + 1)) : ℕ) : ℤ) + ((k : ℤ) + 1) * (m + 1) := by
        push_cast [Fin.val_last, Fin.val_zero]; ring
      rw [e1, aW_at, aW_at, neg_add, zpow_add₀ hpne, zpow_neg_one]
      have h1 := hratio 0 (Fin.last k)
      have hz := zpow_pos hp0 (-m)
      calc ‖lam 0‖ * ((p : ℝ) ^ (-m) * (p : ℝ)⁻¹) = (‖lam 0‖ / p) * (p : ℝ) ^ (-m) := by ring
        _ ≤ ‖lam (Fin.last k)‖ * (p : ℝ) ^ (-m) := by
          gcongr
          rw [div_le_iff₀ hp0]; linarith
    | cast i =>
      have e1 : (((Fin.castSucc i : ℕ)) : ℤ) + ((k : ℤ) + 1) * m + 1 = ((i.succ : ℕ) : ℤ) + ((k : ℤ) + 1) * m := by
        push_cast [Fin.coe_castSucc, Fin.val_succ]; ring
      rw [e1, aW_at, aW_at]
      have h1 : ‖lam i.succ‖ ≤ ‖lam (Fin.castSucc i)‖ := hanti (Fin.castSucc_lt_succ (i := i)).le
      have hz := zpow_pos hp0 (-m)
      gcongr
  have hA : Antitone (aW p k lam) := antitone_int_of_succ_le hstep
  have hA0 : aW p k lam 0 < (p : ℝ) * aW p k lam (((k + 1 : ℕ) : ℤ) - 1) := by
    have h1 : aW p k lam 0 = ‖lam 0‖ := by simpa using aW_at p k lam 0 0
    have h2 : aW p k lam (k : ℤ) = ‖lam (Fin.last k)‖ := by simpa using aW_at p k lam (Fin.last k) 0
    rw [h1, show ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) by push_cast; ring, h2]
    exact hratio 0 (Fin.last k)
  have hperA : ∀ J, aW p k lam (J + ((k + 1 : ℕ) : ℤ)) = aW p k lam J / p := by
    intro J
    obtain ⟨i, m, rfl⟩ := decomp k J
    rw [show ((i : ℕ) : ℤ) + ((k : ℤ) + 1) * m + ((k + 1 : ℕ) : ℤ) = ((i : ℕ) : ℤ) + ((k : ℤ) + 1) * (m + 1) by
      push_cast; ring, aW_at, aW_at, neg_add, zpow_add₀ hpne, zpow_neg_one]
    ring
  have hperR : ∀ J, rW p k π (J + ((k + 1 : ℕ) : ℤ)) = rW p k π J ^ (((p : ℝ) ^ (k + 1))⁻¹) := by
    intro J
    obtain ⟨i, m, rfl⟩ := decomp k J
    rw [show ((i : ℕ) : ℤ) + ((k : ℤ) + 1) * m + ((k + 1 : ℕ) : ℤ) = ((i : ℕ) : ℤ) + ((k : ℤ) + 1) * (m + 1) by
      push_cast; ring, rW_at, rW_at]
    have e3 : ((p : ℝ) ^ (k + 1))⁻¹ = (p : ℝ) ^ (-((k : ℤ) + 1)) := by
      rw [zpow_neg]; norm_cast
    rw [e3, hrp _ (norm_nonneg _), show -(((k : ℤ) + 1) * (m + 1)) = -(((k : ℤ) + 1) * m) + -((k : ℤ) + 1) by ring]
  have hrelW : ∀ J, aW p k lam (J + 1) * rW p k π (J + 1) ^ ((p : ℝ) ^ J)
      = aW p k lam J * rW p k π J ^ ((p : ℝ) ^ J) := by
    intro J
    obtain ⟨i, m, rfl⟩ := decomp k J
    induction i using Fin.lastCases with
    | last =>
      have e1 : (((Fin.last k : ℕ)) : ℤ) + ((k : ℤ) + 1) * m + 1
          = (((0 : Fin (k + 1)) : ℕ) : ℤ) + ((k : ℤ) + 1) * (m + 1) := by
        push_cast [Fin.val_last, Fin.val_zero]; ring
      rw [e1, aW_at, aW_at, rW_at, rW_at, hrp _ (norm_nonneg _), hrp _ (norm_nonneg _)]
      have e2 : -(((k : ℤ) + 1) * (m + 1)) + ((((Fin.last k : ℕ)) : ℤ) + ((k : ℤ) + 1) * m) = -1 := by
        push_cast [Fin.val_last]; ring
      have e3 : -(((k : ℤ) + 1) * m) + ((((Fin.last k : ℕ)) : ℤ) + ((k : ℤ) + 1) * m) = ((k : ℕ) : ℤ) := by
        push_cast [Fin.val_last]; ring
      rw [e2, e3, hnat, zpow_neg_one]
      have hXY : ‖lam 0‖ / p * ‖π 0‖ ^ ((p : ℝ)⁻¹) = ‖lam (Fin.last k)‖ * ‖π (Fin.last k)‖ ^ p ^ k := by
        have hx : 0 ≤ ‖lam 0‖ / p * ‖π 0‖ ^ ((p : ℝ)⁻¹) := by positivity
        have hy : 0 ≤ ‖lam (Fin.last k)‖ * ‖π (Fin.last k)‖ ^ p ^ k := by positivity
        refine (pow_left_inj₀ hx hy (Fact.out : p.Prime).ne_zero).1 ?_
        rw [mul_pow, ← hrel2, ← Real.rpow_natCast (‖π 0‖ ^ ((p : ℝ)⁻¹)) p, ← Real.rpow_mul (norm_nonneg _),
          inv_mul_cancel₀ hpne, Real.rpow_one]
      rw [neg_add, zpow_add₀ hpne, zpow_neg_one]
      linear_combination (p : ℝ) ^ (-m) * hXY
    | cast i =>
      have e1 : (((Fin.castSucc i : ℕ)) : ℤ) + ((k : ℤ) + 1) * m + 1 = ((i.succ : ℕ) : ℤ) + ((k : ℤ) + 1) * m := by
        push_cast [Fin.coe_castSucc, Fin.val_succ]; ring
      rw [e1, aW_at, aW_at, rW_at, rW_at, hrp _ (norm_nonneg _), hrp _ (norm_nonneg _)]
      have e2 : -(((k : ℤ) + 1) * m) + ((((Fin.castSucc i : ℕ)) : ℤ) + ((k : ℤ) + 1) * m) = ((i : ℕ) : ℤ) := by
        push_cast [Fin.coe_castSucc]; ring
      rw [e2, hnat, hnat]
      have h := hrel1 i
      linear_combination (p : ℝ) ^ (-m) * h
  have hJ := window_ineq p (k + 1) (by exact_mod_cast (Fact.out : p.Prime).one_lt) (Nat.succ_pos k) (aW p k lam)
    (rW p k π) ha hρ hA hA0 hperA hperR hrelW (r : ℕ) r.isLt (((j : ℕ) : ℤ) + ((k : ℤ) + 1) * (-n))
  rw [aW_at p k lam j (-n), rW_at p k π j (-n)] at hJ
  have hR1 : aW p k lam ((r : ℕ) : ℤ) = ‖lam r‖ := by simpa using aW_at p k lam r 0
  have hR2 : rW p k π ((r : ℕ) : ℤ) = ‖π r‖ := by simpa using rW_at p k π r 0
  rw [hR1, hR2] at hJ
  have hT : ‖term p ϖ lam π r j n‖
      = ‖lam j‖ * (p : ℝ) ^ (-(-n)) * (‖π j‖ ^ ((p : ℝ) ^ (-(((k : ℤ) + 1) * -n)))) ^ ((p : ℝ) ^ (r : ℕ)) := by
    rw [norm_term p k ϖ hϖ, ← zpow_natCast (p : ℝ) (r : ℕ), hrp _ (norm_nonneg _), neg_neg,
      show -(((k : ℤ) + 1) * -n) + ((r : ℕ) : ℤ) = ((r : ℕ) : ℤ) + n * ((k : ℤ) + 1) by ring]
  have hRt : ‖lam r * π r ^ p ^ (r : ℕ)‖ = ‖lam r‖ * ‖π r‖ ^ ((p : ℝ) ^ (r : ℕ)) := by
    rw [norm_mul, norm_pow, ← Real.rpow_natCast ‖π r‖ (p ^ (r : ℕ)), Nat.cast_pow]
  rw [hT, hRt]
  obtain ⟨W1, W2, W3, W4⟩ := hJ
  have hj1 : ((j : ℕ) : ℤ) < (k : ℤ) + 1 := by exact_mod_cast j.isLt
  have hj0 : (0 : ℤ) ≤ ((j : ℕ) : ℤ) := by positivity
  refine ⟨W1, fun hn => W2 (by nlinarith), fun hn => ?_⟩
  rcases lt_abs.1 hn with hn | hn
  · exact W3 (by push_cast; nlinarith)
  · exact W4 (by push_cast; nlinarith)

end GlobalTheory.PMonE.WinBounds
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusWindowSeriesTermNormLeRowBoundStatement

section

@[expose] public section

open GlobalTheory.PMonE

theorem _root_.GlobalTheory.T.frobeniusWindowSeriesTerm_norm_le_rowBound : ∀ (F : Type) [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (k : ℕ) (ϖ : F), ‖ϖ‖ = (p : ℝ)⁻¹ → ∀ lam π : Fin (k + 1) → F, (∀ j, lam j ≠ 0) → Antitone (fun j => ‖lam j‖) → (∀ i j, ‖lam i‖ < p * ‖lam j‖) → (∀ j, π j ≠ 0 ∧ ‖π j‖ < 1) → (∀ j : Fin k, ‖lam j.succ‖ * ‖π j.succ‖ ^ p ^ (j : ℕ) = ‖lam j.castSucc‖ * ‖π j.castSucc‖ ^ p ^ (j : ℕ)) → (‖lam 0‖ / p) ^ p * ‖π 0‖ = (‖lam (Fin.last k)‖ * ‖π (Fin.last k)‖ ^ p ^ k) ^ p → ∀ (r j : Fin (k + 1)) (n : ℤ), ‖term p ϖ lam π r j n‖ ≤ ‖lam r * π r ^ p ^ (r : ℕ)‖ ∧ (0 < n → ‖term p ϖ lam π r j n‖ < ‖lam r * π r ^ p ^ (r : ℕ)‖) ∧ (2 < |n| → ‖term p ϖ lam π r j n‖ ≤ ‖lam r * π r ^ p ^ (r : ℕ)‖ / p) := by
  first | exact @GlobalTheory.PMonE.WinBounds.term_le_bound | exact GlobalTheory.PMonE.WinBounds.term_le_bound | (intros; apply GlobalTheory.PMonE.WinBounds.term_le_bound <;> assumption)
end
end
