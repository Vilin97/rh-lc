module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimeSetBoundDataOfPrimitiveChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.ConductorBoundsOfIsChiField
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.ErrorTermsLeSqrtExpRpow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.IsCMFieldOfIsChiField
public import Development.AutomorphicArithmetic.CharacterBoxes.ExistsPageN
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.StmtFields
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Polynomial.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.StmtFields
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.LogConductorMulHeightLeOfPageN

section

@[expose] public section

open NumberField Formalism.HC UpperTheory.Top UpperTheory.V

theorem UpperTheory.V.log_conductor_mul_height_le_of_pageN :
    ∀ (eps Ct : ℝ) (m : ℕ), 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ N t e q d : ℕ, 1 ≤ N → N ≤ 2 ^ (e + 2) * m * q * d →
      PageN eps x e → 1 ≤ t → (t : ℝ) ≤ x ^ Ct → Real.log ((q : ℝ) * d) ≤ x ^ (eps / 4) → Real.log ((N : ℝ) * t) ≤ 2 * x ^ (eps / 4) := by
  intro eps Ct m heps heps1
  have hr : 0 < eps / 4 := by positivity
  have hK0 : 0 < 3 + |Ct| := by positivity
  have h1 := (isLittleO_log_rpow_atTop hr).bound (by positivity : (0:ℝ) < 1 / (2 * (3 + |Ct|)))
  have h2 := (tendsto_rpow_atTop hr).eventually_ge_atTop (2 * (3 * Real.log 2 + Real.log m))
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1 ((h1.and h2).and (Filter.eventually_ge_atTop 1))
  refine ⟨x0, fun x hx N t e q d hN hNle hP ht htx hqd => ?_⟩
  obtain ⟨⟨hl, hg⟩, hx1⟩ := hx0 x hx
  have hxpos : 0 < x := by linarith
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hX : 0 < x ^ (eps / 4) := Real.rpow_pos_of_pos hxpos _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlogx, abs_of_pos hX] at hl
  have hKl : (3 + |Ct|) * Real.log x ≤ x ^ (eps / 4) / 2 := by
    calc (3 + |Ct|) * Real.log x ≤ (3 + |Ct|) * (1 / (2 * (3 + |Ct|)) * x ^ (eps / 4)) :=
          mul_le_mul_of_nonneg_left hl hK0.le
      _ = x ^ (eps / 4) / 2 := by
          field_simp
  have hprod : 1 ≤ 2 ^ (e + 2) * m * q * d := le_trans hN hNle
  have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.2 (by rintro rfl; simp at hprod)
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.2 (by rintro rfl; simp at hprod)
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.2 (by rintro rfl; simp at hprod)
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN
  have htr : (1:ℝ) ≤ t := by exact_mod_cast ht
  have hmr : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hqr : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hdr : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hNle' : (N:ℝ) ≤ 2 ^ (e + 2) * m * (q * d) := by
    rw [← mul_assoc]
    exact_mod_cast hNle
  rw [Real.log_mul (by linarith) (by linarith)]
  have hlogN : Real.log N ≤ ((e:ℝ) + 2) * Real.log 2 + Real.log m + Real.log ((q:ℝ) * d) := by
    calc Real.log N ≤ Real.log (2 ^ (e + 2) * m * ((q:ℝ) * d)) :=
          Real.log_le_log (by linarith) hNle'
      _ = ((e:ℝ) + 2) * Real.log 2 + Real.log m + Real.log ((q:ℝ) * d) := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by linarith),
            Real.log_pow]
          push_cast
          ring
  have hlogt : Real.log t ≤ Ct * Real.log x := by
    calc Real.log t ≤ Real.log (x ^ Ct) := Real.log_le_log (by linarith) htx
      _ = Ct * Real.log x := Real.log_rpow hxpos _
  have hE : (e:ℝ) * Real.log 2 ≤ Real.log 2 + (2 + 8 * eps) * Real.log x := by
    have h := Real.log_le_log (by positivity) hP.2
    rw [Real.log_pow, Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hxpos _).ne',
      Real.log_rpow hxpos] at h
    exact h
  have hC : Ct * Real.log x ≤ |Ct| * Real.log x := mul_le_mul_of_nonneg_right (le_abs_self Ct) hlogx
  nlinarith [mul_nonneg hlogx (by linarith : (0:ℝ) ≤ 1 - 8 * eps)]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.bigpair

section

@[expose] public section

open NumberField Formalism.HC UpperTheory.Top UpperTheory.V

theorem UpperTheory.V.eventually_winPair_gt_power :
    ∀ eps J Ct P : ℝ, 0 < eps → 0 < J → ∃ X0 : ℝ, ∀ X ≥ X0, ∀ q d : ℕ, WinPair eps (X ^ (1 / J)) q d →
      2 * X ^ Ct + 1 < (q : ℝ) ∧ 2 * X ^ Ct + 1 < (d : ℝ) ∧ P < (q : ℝ) ∧ P < (d : ℝ) := by
  intro eps J Ct P heps hJ
  set δ : ℝ := 1 / J * (eps / 5) with hδ
  have hδpos : 0 < δ := by positivity
  set mC : ℝ := max Ct 0 with hmC
  set n : ℕ := ⌈(mC + 1) / δ⌉₊ with hn_def
  have hn : mC + 1 ≤ δ * n := by
    have h := Nat.le_ceil ((mC + 1) / δ)
    rw [div_le_iff₀ hδpos] at h
    linarith
  set M : ℝ := 2 ^ n * (n.factorial : ℝ) with hM_def
  have hM : 0 < M := by positivity
  refine ⟨max (Real.exp J) (M * (|P| + 3) + 1), fun X hX q d hw => ?_⟩
  have hXe : Real.exp J ≤ X := le_trans (le_max_left _ _) hX
  have hXM : M * (|P| + 3) + 1 ≤ X := le_trans (le_max_right _ _) hX
  have hX1 : 1 ≤ X := by
    have := Real.add_one_le_exp J
    linarith
  have hX0 : 0 < X := by linarith
  have hY : (X ^ (1 / J)) ^ (eps / 5) = X ^ δ := by
    rw [← Real.rpow_mul hX0.le]
  have hlogY : 1 ≤ Real.log (X ^ (1 / J)) := by
    rw [Real.log_rpow hX0]
    have hJl : J ≤ Real.log X := (Real.le_log_iff_exp_le hX0).2 hXe
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hJ]
    linarith
  set y : ℝ := X ^ δ / 2 with hy_def
  have hy0 : 0 ≤ y := by positivity
  have hfac := Real.pow_div_factorial_le_exp y hy0 n
  have hyn : y ^ n = X ^ (δ * n) / 2 ^ n := by
    rw [hy_def, div_pow, ← Real.rpow_natCast (X ^ δ), ← Real.rpow_mul hX0.le]
  have hlow : X ^ (δ * n) / M ≤ Real.exp y := by
    rw [hyn, div_div] at hfac
    exact hfac
  have hpow : X ^ mC * X ≤ X ^ (δ * n) := by
    rw [← Real.rpow_add_one hX0.ne']
    exact Real.rpow_le_rpow_of_exponent_le hX1 hn
  have hCt : X ^ Ct ≤ X ^ mC := Real.rpow_le_rpow_of_exponent_le hX1 (le_max_left _ _)
  have hmC1 : 1 ≤ X ^ mC := Real.one_le_rpow hX1 (le_max_right _ _)
  have hXdiv : |P| + 3 < X / M := by
    rw [lt_div_iff₀ hM]
    linarith
  have hmain : X ^ mC * (|P| + 3) < Real.exp y := by
    have h1 : X ^ mC * (|P| + 3) < X ^ mC * (X / M) :=
      mul_lt_mul_of_pos_left hXdiv (by linarith)
    have h2 : X ^ mC * (X / M) = X ^ mC * X / M := by ring
    have h3 : X ^ mC * X / M ≤ X ^ (δ * n) / M := div_le_div_of_nonneg_right hpow hM.le
    linarith
  have hP0 : 0 ≤ |P| := abs_nonneg P
  have hB1 : 2 * X ^ Ct + 1 < Real.exp y := by nlinarith
  have hB2 : P < Real.exp y := by
    have := le_abs_self P
    nlinarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hw.q_prime.pos
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hw.d_prime.pos
  have hqlo := hw.q_lo
  have hdlo := hw.d_lo
  rw [hY] at hqlo hdlo
  have hq : Real.exp y < q := by
    rw [← Real.exp_log hq0]
    exact Real.exp_lt_exp.2 (by rw [hy_def]; exact hqlo)
  have hd : Real.exp y < d := by
    rw [← Real.exp_log hd0]
    apply Real.exp_lt_exp.2
    have hXd : 0 ≤ X ^ δ := by positivity
    have hl2 : 1 ≤ Real.log (X ^ (1 / J)) ^ 2 := by nlinarith
    have : X ^ δ / 2 ≤ X ^ δ * Real.log (X ^ (1 / J)) ^ 2 / 2 := by nlinarith
    rw [hy_def]
    linarith
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.logpair

section

@[expose] public section

open NumberField Formalism.HC UpperTheory.Top UpperTheory.V

theorem UpperTheory.V.log_mul_le_rpow_of_winPair :
    ∀ eps : ℝ, 0 < eps → ∃ Y0 : ℝ, ∀ Y ≥ Y0, ∀ q d : ℕ, WinPair eps Y q d → Real.log ((q : ℝ) * d) ≤ Y ^ (eps / 4) := by
  intro eps heps
  have hs : 0 < eps / 20 := by positivity
  have h1 := (isLittleO_log_rpow_rpow_atTop 2 hs).bound (by norm_num : (0:ℝ) < 1 / 2)
  have h2 := (tendsto_rpow_atTop hs).eventually_ge_atTop 2
  obtain ⟨Y0, hY0⟩ := Filter.eventually_atTop.1 ((h1.and h2).and (Filter.eventually_gt_atTop 0))
  refine ⟨Y0, fun Y hY q d hw => ?_⟩
  obtain ⟨⟨hl, hg⟩, hpos⟩ := hY0 Y hY
  have hq : (0:ℝ) < q := by exact_mod_cast hw.q_prime.pos
  have hd : (0:ℝ) < d := by exact_mod_cast hw.d_prime.pos
  rw [Real.log_mul hq.ne' hd.ne']
  have hA : 0 < Y ^ (eps / 5) := Real.rpow_pos_of_pos hpos _
  have hB : 0 < Y ^ (eps / 20) := Real.rpow_pos_of_pos hpos _
  rw [Real.rpow_two, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
    abs_of_pos hB] at hl
  have hsplit : Y ^ (eps / 4) = Y ^ (eps / 5) * Y ^ (eps / 20) := by
    rw [← Real.rpow_add hpos]
    ring_nf
  rw [hsplit]
  have hq' := hw.q_up
  have hd' := hw.d_up
  nlinarith [mul_le_mul_of_nonneg_left hl hA.le, mul_le_mul_of_nonneg_left hg hA.le]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.minusle

section

@[expose] public section

open NumberField Formalism.HC UpperTheory.Top UpperTheory.V

theorem UpperTheory.V.minusBound_le_exp_of_log_le :
    ∀ (C : ℝ) (o : ℕ), ∃ K : ℝ, 0 ≤ K ∧ ∀ (n N t : ℕ) (W : ℝ), 1 ≤ N → 1 ≤ t → n ≤ N → Real.log ((N : ℝ) * t) ≤ 2 * W →
      minusBound C o n N t ≤ K * Real.exp (8 * W) := by
  intro C o
  refine ⟨3 + |C| * ∑ l ∈ o.primeFactors.erase 2, (l : ℝ) ^ 3, by positivity, ?_⟩
  intro n N t W hN ht hn hW
  unfold minusBound
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hn' : (n : ℝ) ≤ N := by exact_mod_cast hn
  have hX1 : (1 : ℝ) ≤ (N : ℝ) * t := one_le_mul_of_one_le_of_one_le hN1 ht1
  have hXpos : 0 < (N : ℝ) * t := by linarith
  have hXe : (N : ℝ) * t ≤ Real.exp (2 * W) := by
    rw [← Real.exp_log hXpos]
    exact Real.exp_le_exp.mpr hW
  have hX4 : ((N : ℝ) * t) ^ 4 ≤ Real.exp (8 * W) := by
    have e : Real.exp (8 * W) = Real.exp (2 * W) ^ 4 := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [e]
    exact pow_le_pow_left₀ hXpos.le hXe 4
  have hnt : (n : ℝ) * t ≤ (N : ℝ) * t := mul_le_mul_of_nonneg_right hn' (by positivity)
  have htX : (t : ℝ) ≤ (N : ℝ) * t := by nlinarith
  have hlog : Real.log ((t : ℝ) * N) ≤ (N : ℝ) * t := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < t * N by linarith)
    linarith
  have hlog0 : 0 ≤ Real.log ((t : ℝ) * N) := Real.log_nonneg (by linarith)
  have h1 : 3 * (n : ℝ) * t ^ 2 * Real.log (t * N) ≤ 3 * ((N : ℝ) * t) ^ 4 := by
    have h3 : (n : ℝ) * t * t * Real.log (t * N) ≤ ((N : ℝ) * t) ^ 3 := by
      calc (n : ℝ) * t * t * Real.log (t * N)
          ≤ ((N : ℝ) * t) * ((N : ℝ) * t) * ((N : ℝ) * t) :=
            mul_le_mul (mul_le_mul hnt htX (by positivity) (by positivity)) hlog hlog0 (by positivity)
        _ = ((N : ℝ) * t) ^ 3 := by ring
    have h34 : ((N : ℝ) * t) ^ 3 ≤ ((N : ℝ) * t) ^ 4 := pow_le_pow_right₀ hX1 (by norm_num)
    have e : 3 * (n : ℝ) * t ^ 2 * Real.log (t * N) = 3 * ((n : ℝ) * t * t * Real.log (t * N)) := by ring
    rw [e]
    linarith
  have h2 : ∑ l ∈ o.primeFactors.erase 2, (l : ℝ) * n ^ 2 * t ^ 2 * Real.log (t * l * N) ^ 2
      ≤ (∑ l ∈ o.primeFactors.erase 2, (l : ℝ) ^ 3) * ((N : ℝ) * t) ^ 4 := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro l hl
    have hl1 : (1 : ℝ) ≤ l := by
      have := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hl)
      exact_mod_cast this.one_lt.le
    have hge : (1 : ℝ) ≤ t * l * N :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le ht1 hl1) hN1
    have hlg : Real.log ((t : ℝ) * l * N) ≤ l * ((N : ℝ) * t) := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < t * l * N by linarith)
      linarith
    have hlg0 : 0 ≤ Real.log ((t : ℝ) * l * N) := Real.log_nonneg hge
    have hsq : Real.log ((t : ℝ) * l * N) ^ 2 ≤ (l * ((N : ℝ) * t)) ^ 2 := pow_le_pow_left₀ hlg0 hlg 2
    have hnt2 : ((n : ℝ) * t) ^ 2 ≤ ((N : ℝ) * t) ^ 2 := pow_le_pow_left₀ (by positivity) hnt 2
    calc (l : ℝ) * n ^ 2 * t ^ 2 * Real.log (t * l * N) ^ 2
        = (l : ℝ) * ((n : ℝ) * t) ^ 2 * Real.log (t * l * N) ^ 2 := by ring
      _ ≤ (l : ℝ) * ((N : ℝ) * t) ^ 2 * (l * ((N : ℝ) * t)) ^ 2 := by gcongr
      _ = (l : ℝ) ^ 3 * ((N : ℝ) * t) ^ 4 := by ring
  have hS0 : 0 ≤ ∑ l ∈ o.primeFactors.erase 2, (l : ℝ) * n ^ 2 * t ^ 2 * Real.log (t * l * N) ^ 2 :=
    Finset.sum_nonneg (fun l _ => by positivity)
  have hK0 : 0 ≤ 3 + |C| * ∑ l ∈ o.primeFactors.erase 2, (l : ℝ) ^ 3 := by positivity
  calc 3 * (n : ℝ) * t ^ 2 * Real.log (t * N)
        + C * ∑ l ∈ o.primeFactors.erase 2, (l : ℝ) * n ^ 2 * t ^ 2 * Real.log (t * l * N) ^ 2
      ≤ 3 * ((N : ℝ) * t) ^ 4 + |C| * ((∑ l ∈ o.primeFactors.erase 2, (l : ℝ) ^ 3) * ((N : ℝ) * t) ^ 4) :=
        add_le_add h1 ((mul_le_mul_of_nonneg_right (le_abs_self C) hS0).trans
          (mul_le_mul_of_nonneg_left h2 (abs_nonneg C)))
    _ = (3 + |C| * ∑ l ∈ o.primeFactors.erase 2, (l : ℝ) ^ 3) * ((N : ℝ) * t) ^ 4 := by ring
    _ ≤ (3 + |C| * ∑ l ∈ o.primeFactors.erase 2, (l : ℝ) ^ 3) * Real.exp (8 * W) :=
        mul_le_mul_of_nonneg_left hX4 hK0
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.AdmissibleOfPageN

section

@[expose] public section

noncomputable section

open NumberField

namespace UpperTheory.V

open Formalism.HC UpperTheory.Top

theorem VVminusLe.mono {E : Type} [Field E] [NumberField E] [IsCMField E] {t : ℕ} {B B' : ℝ} (h : VVminusLe E t B)
    (hB : B ≤ B') : VVminusLe E t B' := by
  intro Ω _ _ _ ld
  obtain ⟨h1, h2⟩ := h Ω ld
  exact ⟨h1, fun S hS => (h2 S hS).trans hB⟩

theorem admissible_of_pageN {eps Ct : ℝ} (h0 : 0 < eps) (h1 : eps < 1 / 52) (hC : 1 ≤ Ct) {e : ℝ → ℕ}
    (he : ∀ x ≥ (1 : ℝ), PageN eps x (e x)) : admitted 4 Ct e fun x => ⌊x ^ Ct⌋₊ := by
  intro x hx
  have hx1 : (1 : ℝ) ≤ x := by linarith
  obtain ⟨a, b⟩ := he x hx1
  have h2 : x ^ (2 : ℝ) ≤ x ^ (2 + 8 * eps) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have h3 : x ^ (2 + 8 * eps) ≤ x ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have h4 : x ^ (4 : ℝ) = x * x ^ (3 : ℝ) := by
    rw [show (4 : ℝ) = 1 + 3 by norm_num, Real.rpow_add (by linarith), Real.rpow_one]
  have h5 : (0 : ℝ) ≤ x ^ (3 : ℝ) := by positivity
  have h6 : x ≤ x ^ Ct := Real.self_le_rpow_of_one_le hx1 hC
  have h8 : 2 * x ^ (3 : ℝ) ≤ x * x ^ (3 : ℝ) := mul_le_mul_of_nonneg_right hx h5
  refine ⟨?_, b.trans ((mul_le_mul_of_nonneg_left h3 zero_le_two).trans (h8.trans h4.ge)), Nat.le_floor (by push_cast; linarith), Nat.floor_le (by linarith)⟩
  rw [Real.rpow_two] at h2
  have h7 : (2 : ℝ) ^ 2 ≤ 2 ^ e x := by nlinarith
  exact (pow_le_pow_iff_right₀ (by norm_num)).1 h7

theorem vwinAt_of_joint {Ct : ℝ} (hC : 1 ≤ Ct) (hJ : JointWin Ct) (hc : ThmBc Ct) (ψ : PChar) : VWinAt ψ Ct := by
  intro eps h0 h1 e he
  set t : ℝ → ℕ := fun x => ⌊x ^ Ct⌋₊ with ht
  have hadm : admitted 4 Ct e t := admissible_of_pageN h0 h1 hC he
  obtain ⟨J, C, P, XJ, hJ0, hmain⟩ := hJ ψ eps 4 h0 h1 e t hadm
  obtain ⟨Cb, hCb⟩ := hc
  obtain ⟨K, hK0, hK⟩ := minusBound_le_exp_of_log_le Cb (AbF.ofChar ψ).deg
  obtain ⟨xT, hxT⟩ := error_terms_le_sqrt_exp_rpow eps K C h0
  obtain ⟨xN, hxN⟩ := log_conductor_mul_height_le_of_pageN eps Ct ψ.N h0 h1
  obtain ⟨Y0, hY0⟩ := log_mul_le_rpow_of_winPair eps h0
  obtain ⟨J', hJ'1, hJJ'⟩ : ∃ J' : ℝ, 1 ≤ J' ∧ J ≤ J' := ⟨max J 1, le_max_right _ _, le_max_left _ _⟩
  have hJ'0 : 0 < J' := by linarith
  obtain ⟨P', hPP', hNP'⟩ : ∃ P' : ℝ, P ≤ P' ∧ (ψ.N : ℝ) ≤ P' := ⟨max P (ψ.N : ℝ), le_max_left _ _, le_max_right _ _⟩
  obtain ⟨XB, hXB⟩ := eventually_winPair_gt_power eps J' Ct P' h0 hJ'0
  obtain ⟨L, hxTL, hxNL, hY0L, h2L⟩ : ∃ L : ℝ, xT ≤ L ∧ xN ≤ L ∧ Y0 ≤ L ∧ 2 ≤ L :=
    ⟨max (max xT xN) (max Y0 2), le_max_of_le_left (le_max_left _ _), le_max_of_le_left (le_max_right _ _),
      le_max_of_le_right (le_max_left _ _), le_max_of_le_right (le_max_right _ _)⟩
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hL0 : (0 : ℝ) ≤ L := by linarith
  refine ⟨J', hJ'1, max (max XJ XB) (L ^ J'), ?_⟩
  intro X hX q d hw
  have hXJ : XJ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXB' : XB ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXL : L ^ J' ≤ X := le_trans (le_max_right _ _) hX
  have hLX : L ≤ X ^ (1 / J') := by
    have := Real.rpow_le_rpow (Real.rpow_nonneg hL0 _) hXL (le_of_lt (one_div_pos.mpr hJ'0))
    rwa [← Real.rpow_mul hL0, mul_one_div_cancel hJ'0.ne', Real.rpow_one] at this
  have hX1 : 1 ≤ X := by
    have : 1 ≤ L ^ J' := Real.one_le_rpow hL1 hJ'0.le
    linarith
  have hX0 : (0 : ℝ) ≤ X := by linarith
  obtain ⟨hq3, hd3, hPq, hPd⟩ := hXB X hXB' q d hw
  have hlog := hY0 _ (hY0L.trans hLX) q d hw
  have hpow : (X ^ (1 / J')) ^ (eps / 4) = X ^ (eps / (4 * J')) := by
    rw [← Real.rpow_mul hX0]
    congr 1
    field_simp
  have hmono : X ^ (eps / (4 * J')) ≤ X ^ (eps / (4 * J)) :=
    Real.rpow_le_rpow_of_exponent_le hX1 (div_le_div_of_nonneg_left h0.le (by positivity) (by linarith))
  have hlogJ : Real.log (↑q * ↑d) ≤ X ^ (eps / (4 * J)) := by
    rw [hpow] at hlog
    exact hlog.trans hmono
  have hN0 : 0 < ψ.N := (AbF.ofChar ψ).pos
  have hcop : ∀ r : ℕ, Nat.Prime r → (ψ.N : ℝ) < r → Nat.Coprime r ψ.N := by
    intro r hr hlt
    have hlt' : ψ.N < r := by exact_mod_cast hlt
    exact (Nat.Prime.coprime_iff_not_dvd hr).2 (fun hdvd => absurd (Nat.le_of_dvd hN0 hdvd) (not_le.2 hlt'))
  have hpp : PrimePair ψ.N q d :=
    ⟨hw.q_prime, hw.q_mod, hw.d_prime, hw.d_mod,
      Nat.Coprime.mul_left (hcop q hw.q_prime (lt_of_le_of_lt hNP' hPq)) (hcop d hw.d_prime (lt_of_le_of_lt hNP' hPd))⟩
  obtain ⟨Y, ⟨hYlo, hYhi⟩, hY⟩ :=
    hmain X hXJ q d hpp hq3 hd3 (lt_of_le_of_lt hPP' hPq) (lt_of_le_of_lt hPP' hPd) hlogJ
  have hWY : X ^ (1 / J') ≤ Y :=
    le_trans (Real.rpow_le_rpow_of_exponent_le hX1 (one_div_le_one_div_of_le (by linarith) hJJ')) hYlo
  refine ⟨Y, hWY, hYhi, ?_⟩
  intro x hxY hxY2
  have hWx : X ^ (1 / J') ≤ x := hWY.trans hxY
  have hLx : L ≤ x := hLX.trans hWx
  have hx2 : 2 ≤ x := h2L.trans hLx
  have hx1 : 1 ≤ x := by linarith
  obtain ⟨hBa, hHV⟩ := hY x hxY hxY2
  intro E _ _ hE
  have hq0 : 0 < q := hw.q_prime.pos
  have hd0 : 0 < d := hw.d_prime.pos
  have hq4 : q % 4 = 3 := by
    have := hw.q_mod
    omega
  haveI : IsCMField E := isCMField_of_isChiField ψ (e x) q d hw.q_prime hq4 E hE
  have hE' : IsCompField (AbF.ofChar ψ) (e x) q d E := (isCompField_ofChar ψ (e x) q d E).2 hE
  have h2 := hBa E hE'
  have hp := hHV E hE
  have hm := hCb (AbF.ofChar ψ) 4 e t hadm x hx2 q d hpp E hE'
  obtain ⟨hc1, hc2, hc3⟩ := conductor_bounds_of_isChiField ψ (e x) q d hq0 hd0 E hE
  obtain ⟨-, -, ht2, htle⟩ := hadm x hx2
  have ht1 : 1 ≤ t x := by omega
  have hWpos : (0 : ℝ) ≤ X ^ (1 / J') := Real.rpow_nonneg hX0 _
  have hqd : Real.log (↑q * ↑d) ≤ x ^ (eps / 4) := by
    have hlog0 := hY0 _ (hY0L.trans hLX) q d hw
    exact hlog0.trans (Real.rpow_le_rpow hWpos hWx (by linarith))
  have hNt := hxN x (hxNL.trans hLx) (condF E) (t x) (e x) q d hc1 hc2 (he x hx1) ht1 htle hqd
  have hmb := hK (Module.finrank ℚ E) (condF E) (t x) (x ^ (eps / 4)) hc1 ht1 hc3 hNt
  have hm' := VVminusLe.mono hm hmb
  have hv := vvle_of_parts h2 hm' hp
  have hu1 : (1 : ℝ) ≤ ↑(condF E) * ↑(t x) := by
    have a : (1 : ℝ) ≤ condF E := by exact_mod_cast hc1
    have b : (1 : ℝ) ≤ t x := by exact_mod_cast ht1
    nlinarith
  have htot := hxT x (hxTL.trans hLx) _ hu1 hNt
  exact VVle.mono hv le_rfl htot

theorem vwin_of_joint (hJ : JointWin 401) (hc : ThmBc 401) : VWin := by
  intro ψ
  exact vwinAt_of_joint (by norm_num) hJ hc ψ

end UpperTheory.V

end
end
end
