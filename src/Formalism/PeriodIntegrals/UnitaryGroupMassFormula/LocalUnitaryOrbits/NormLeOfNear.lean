module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Fintype.Defs
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LandherrUnitNorm.UnitNormLoc

section

@[expose] public section

noncomputable section

open Filter Topology

namespace PI.Landherr₃

theorem unitNormLoc_norm_add_eq_left {K : Type} [NormedField K] [IsUltrametricDist K] (x y : K)
    (h : ‖y‖ < ‖x‖) : ‖x + y‖ = ‖x‖ := by
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne', max_eq_left h.le]

theorem unitNormLoc_norm_two_le {K : Type} [NormedField K] [IsUltrametricDist K] : ‖(2 : K)‖ ≤ 1 := by
  have h := IsUltrametricDist.norm_add_le_max (1 : K) 1
  rw [one_add_one_eq_two, norm_one, max_self] at h
  exact h

theorem unitNormLoc_add_lt {K : Type} [NormedField K] [IsUltrametricDist K] {x y : K} {r : ℝ}
    (hx : ‖x‖ < r) (hy : ‖y‖ < r) : ‖x + y‖ < r := (IsUltrametricDist.norm_add_le_max x y).trans_lt (max_lt hx hy)

theorem unitNormLoc_add_le {K : Type} [NormedField K] [IsUltrametricDist K] {x y : K} {r : ℝ}
    (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) : ‖x + y‖ ≤ r := (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)

theorem unitNormLoc_mul_lt {K : Type} [NormedField K] {x y : K} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ < 1) :
    ‖x * y‖ < 1 := by
  rw [norm_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) hx) hy

theorem unitNormLoc_mul_le {K : Type} [NormedField K] {x y : K} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖x * y‖ ≤ 1 := by
  rw [norm_mul]
  nlinarith [norm_nonneg x, norm_nonneg y]

theorem unitNormLoc_newton {K : Type} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
    (α β γ a : K) (hα : ‖α‖ ≤ 1) (h : ‖α * a ^ 2 + β * a + γ‖ < ‖2 * α * a + β‖ ^ 2) :
    ∃ x : K, α * x ^ 2 + β * x + γ = 0 := by
  obtain ⟨f, hf⟩ : ∃ f : K → K, ∀ x, f x = α * x ^ 2 + β * x + γ := ⟨_, fun _ => rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : K → K, ∀ x, g x = 2 * α * x + β := ⟨_, fun _ => rfl⟩
  obtain ⟨s, hs0, hs⟩ : ∃ s : ℕ → K, s 0 = a ∧ ∀ n, s (n + 1) = s n - f (s n) / g (s n) :=
    ⟨fun n => Nat.rec a (fun _ b => b - f b / g b) n, rfl, fun _ => rfl⟩
  have alg : ∀ b q : K, g b * q = f b → f (b - q) = α * q ^ 2 := by
    intro b q hq
    rw [hg b, hf b] at hq
    rw [hf (b - q)]
    linear_combination (-1 : K) * hq
  have galg : ∀ b q : K, g (b - q) = g b + -(2 * α * q) := by
    intro b q
    rw [hg, hg]
    ring
  rw [← hf a, ← hg a] at h
  obtain ⟨d, hd⟩ : ∃ d, d = ‖g a‖ := ⟨_, rfl⟩
  rw [← hd] at h
  have hd0 : 0 < d := by
    have h1 : 0 < d ^ 2 := lt_of_le_of_lt (norm_nonneg _) h
    by_contra hc
    have h3 : d = 0 := le_antisymm (not_lt.1 hc) (hd ▸ norm_nonneg _)
    rw [h3] at h1
    norm_num at h1
  have hdne : d ≠ 0 := hd0.ne'
  obtain ⟨t, ht⟩ : ∃ t, t = ‖f a‖ / d ^ 2 := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have ht1 : t < 1 := by rw [ht, div_lt_one (by positivity)]; exact h
  have h2 : ‖(2 : K)‖ ≤ 1 := unitNormLoc_norm_two_le
  have inv : ∀ n, ‖g (s n)‖ = d ∧ ‖f (s n)‖ ≤ d ^ 2 * t ^ (n + 1) := by
    intro n
    induction n with
    | zero =>
      refine ⟨by rw [hs0, hd], ?_⟩
      rw [hs0, zero_add, pow_one, ht]
      exact le_of_eq (by field_simp)
    | succ n ih =>
      obtain ⟨hgn, hfn⟩ := ih
      have hne : g (s n) ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at hgn
        exact hdne hgn.symm
      have hft : ‖f (s n)‖ ≤ d ^ 2 * t := by
        refine hfn.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
        exact pow_le_of_le_one ht0 ht1.le (Nat.succ_ne_zero n)
      have hh : ‖f (s n) / g (s n)‖ = ‖f (s n)‖ / d := by rw [norm_div, hgn]
      have hhd : ‖f (s n) / g (s n)‖ < d := by
        rw [hh, div_lt_iff₀ hd0]
        calc ‖f (s n)‖ ≤ d ^ 2 * t := hft
          _ < d ^ 2 * 1 := mul_lt_mul_of_pos_left ht1 (by positivity)
          _ = d * d := by ring
      have h2a : ‖-(2 * α * (f (s n) / g (s n)))‖ < ‖g (s n)‖ := by
        rw [norm_neg, norm_mul, norm_mul, hgn]
        calc ‖(2 : K)‖ * ‖α‖ * ‖f (s n) / g (s n)‖ ≤ 1 * 1 * ‖f (s n) / g (s n)‖ := by gcongr
          _ < d := by rw [one_mul, one_mul]; exact hhd
      have e1 : g (s n) * (f (s n) / g (s n)) = f (s n) := by field_simp
      refine ⟨?_, ?_⟩
      · rw [hs, galg, unitNormLoc_norm_add_eq_left _ _ h2a, hgn]
      · rw [hs, alg _ _ e1, norm_mul, norm_pow, hh]
        have e4 : (‖f (s n)‖ / d) ^ 2 = ‖f (s n)‖ * (‖f (s n)‖ / d ^ 2) := by field_simp
        have e5 : ‖f (s n)‖ / d ^ 2 ≤ t := by
          rw [div_le_iff₀ (by positivity)]
          linarith [hft]
        calc ‖α‖ * (‖f (s n)‖ / d) ^ 2 ≤ 1 * (‖f (s n)‖ / d) ^ 2 :=
              mul_le_mul_of_nonneg_right hα (sq_nonneg _)
          _ = ‖f (s n)‖ * (‖f (s n)‖ / d ^ 2) := by rw [one_mul, e4]
          _ ≤ ‖f (s n)‖ * t := mul_le_mul_of_nonneg_left e5 (norm_nonneg _)
          _ ≤ d ^ 2 * t ^ (n + 1) * t := mul_le_mul_of_nonneg_right hfn ht0
          _ = d ^ 2 * t ^ (n + 1 + 1) := by ring
  have hdist : ∀ n, dist (s n) (s (n + 1)) ≤ (d * t) * t ^ n := by
    intro n
    obtain ⟨hgn, hfn⟩ := inv n
    rw [dist_eq_norm, hs, sub_sub_cancel, norm_div, hgn, div_le_iff₀ hd0]
    calc ‖f (s n)‖ ≤ d ^ 2 * t ^ (n + 1) := hfn
      _ = d * t * t ^ n * d := by ring
  have hc : CauchySeq s := cauchySeq_of_le_geometric t (d * t) ht1 hdist
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
  have hcont : Continuous f := by
    have e : f = fun x => α * x ^ 2 + β * x + γ := funext hf
    rw [e]
    fun_prop
  have h1 : Tendsto (fun n => f (s n)) atTop (𝓝 (f L)) := (hcont.tendsto L).comp hL
  have hlim : Tendsto (fun n : ℕ => d ^ 2 * t * t ^ n) atTop (𝓝 0) := by
    have h3 := (tendsto_pow_atTop_nhds_zero_of_lt_one ht0 ht1).const_mul (d ^ 2 * t)
    rwa [mul_zero] at h3
  have h0 : Tendsto (fun n => f (s n)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) hlim
    calc ‖f (s n)‖ ≤ d ^ 2 * t ^ (n + 1) := (inv n).2
      _ = d ^ 2 * t * t ^ n := by ring
  have hfL : f L = 0 := tendsto_nhds_unique h1 h0
  exact ⟨L, by rw [← hf]; exact hfL⟩

end PI.Landherr₃
end
end
end

-- Source module: Lemmata.GeneralBFactLeft.Imports

section

@[expose] public section

namespace Bl.general_b_fact_left

theorem goal1 :
  ∀ {k : Type} [inst : Field.{0} k] [Fintype.{0} k] (t m e : k),
  Ne.{1} (HSub.hSub.{0, 0, 0} (HPow.hPow.{0, 0, 0} t 2) (HMul.hMul.{0, 0, 0} 4 m)) 0 →
    Exists.{1} fun (x : k) ↦
      Exists.{1} fun (y : k) ↦
        Eq.{1}
          (HAdd.hAdd.{0, 0, 0}
            (HAdd.hAdd.{0, 0, 0} (HPow.hPow.{0, 0, 0} x 2) (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} t x) y))
            (HMul.hMul.{0, 0, 0} m (HPow.hPow.{0, 0, 0} y 2)))
          e := by
  intro k _ _ t m e hd
  by_cases hc : ringChar k = 2
  · have h2 : (2 : k) = 0 := by
      have := ringChar.Nat.cast_ringChar (R := k)
      rwa [hc, Nat.cast_ofNat] at this
    have h4 : (4 : k) = 0 := by
      have : (4 : k) = 2 * 2 := by norm_num
      rw [this, h2, zero_mul]
    rw [h4, zero_mul, sub_zero] at hd
    have ht : t ≠ 0 := fun h => hd (by rw [h]; ring)
    by_cases hm : m = 0
    · refine ⟨1, (e - 1) / t, ?_⟩
      rw [hm]
      field_simp
      ring
    · obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two hc (e / m)
      refine ⟨0, r, ?_⟩
      have : r ^ 2 = e / m := by rw [hr]; ring
      rw [this]
      field_simp
      ring
  · have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hc
    have h4 : (4 : k) ≠ 0 := by
      have : (4 : k) = 2 * 2 := by norm_num
      rw [this]; exact mul_ne_zero h2 h2
    set D : k := m - t ^ 2 / 4 with hD
    have hD0 : D ≠ 0 := by
      intro h0
      apply hd
      have : t ^ 2 - 4 * m = -4 * D := by rw [hD]; field_simp; ring
      rw [this, h0, mul_zero]
    have hf : Polynomial.degree (Polynomial.X ^ 2 - Polynomial.C e : Polynomial k) = 2 := by
      rw [Polynomial.degree_sub_C] <;> rw [Polynomial.degree_X_pow] <;> norm_num
    have hg : Polynomial.degree (Polynomial.C D * Polynomial.X ^ 2 : Polynomial k) = 2 := by
      rw [Polynomial.degree_C_mul_X_pow 2 hD0]; rfl
    obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic hf hg
      (FiniteField.odd_card_of_char_ne_two hc)
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
      Polynomial.eval_mul] at hab
    refine ⟨a - t * b / 2, b, ?_⟩
    have key : a ^ 2 + D * b ^ 2 = e := by linear_combination hab
    rw [← key, hD]
    field_simp
    ring

end Bl.general_b_fact_left
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.NormLeOfNear

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain
open PI.Landherr₃

namespace PI.OmLocU.Nrm

theorem ff_binary {k : Type} [Field k] [Fintype k] (t m e : k) (hD : t ^ 2 - 4 * m ≠ 0) :
    ∃ x y : k, x ^ 2 + t * x * y + m * y ^ 2 = e := by
  first | exact Bl.general_b_fact_left.goal1 .. | (apply Bl.general_b_fact_left.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_left.goal1 <;> assumption)

theorem near_root {K : Type} [NormedField K] [IsUltrametricDist K] (α β γ y₀ y : K)
    (hg : ‖2 * α * y₀ + β‖ = 1) (hf : ‖α * y₀ ^ 2 + β * y₀ + γ‖ < 1) (hy : α * y ^ 2 + β * y + γ = 0) :
    ∃ z, α * z ^ 2 + β * z + γ = 0 ∧ ‖z - y₀‖ < 1 := by
  by_cases hα : α = 0
  · subst hα
    refine ⟨y, hy, ?_⟩
    have hβ : ‖β‖ = 1 := by simpa using hg
    have e : β * (y - y₀) = -(0 * y₀ ^ 2 + β * y₀ + γ) := by linear_combination hy
    have := congrArg norm e
    rw [norm_mul, hβ, one_mul, norm_neg] at this
    rw [this]; exact hf
  · set y' := -(β / α) - y with hy'
    have hq : α * y' ^ 2 + β * y' = α * y ^ 2 + β * y := by rw [hy']; field_simp; ring
    have hroot' : α * y' ^ 2 + β * y' + γ = 0 := by linear_combination hq + hy
    obtain ⟨a, ha_def⟩ : ∃ a, a = α * (y₀ - y) := ⟨_, rfl⟩
    obtain ⟨b, hb_def⟩ : ∃ b, b = α * (y₀ - y') := ⟨_, rfl⟩
    have hb' : b = α * y₀ + β + α * y := by rw [hb_def, hy']; field_simp; ring
    have hab : a + b = 2 * α * y₀ + β := by rw [ha_def, hb']; ring
    have hprod : a * b = α * (α * y₀ ^ 2 + β * y₀ + γ) := by
      rw [ha_def, hb']; linear_combination (-α) * hy
    have hαpos : 0 < ‖α‖ := norm_pos_iff.mpr hα
    have hpr : ‖a * b‖ < ‖α‖ := by
      rw [hprod, norm_mul]
      calc ‖α‖ * ‖α * y₀ ^ 2 + β * y₀ + γ‖ < ‖α‖ * 1 := by gcongr
        _ = ‖α‖ := mul_one _
    have hmax : 1 ≤ max ‖a‖ ‖b‖ := by
      rw [← hg, ← hab]; exact IsUltrametricDist.norm_add_le_max a b
    rcases le_max_iff.mp hmax with ha | hb
    · refine ⟨y', hroot', ?_⟩
      have hb : ‖b‖ < ‖α‖ := by
        have : ‖b‖ ≤ ‖a * b‖ := by
          rw [norm_mul a b]; exact le_mul_of_one_le_left (norm_nonneg b) ha
        exact this.trans_lt hpr
      have : ‖α‖ * ‖y₀ - y'‖ < ‖α‖ * 1 := by
        rw [← norm_mul, mul_one, ← hb_def]; exact hb
      rw [← norm_neg, neg_sub]
      exact lt_of_mul_lt_mul_left this hαpos.le
    · refine ⟨y, hy, ?_⟩
      have ha : ‖a‖ < ‖α‖ := by
        have : ‖a‖ ≤ ‖a * b‖ := by
          rw [norm_mul a b]; exact le_mul_of_one_le_right (norm_nonneg a) hb
        exact this.trans_lt hpr
      have : ‖α‖ * ‖y₀ - y‖ < ‖α‖ * 1 := by
        rw [← norm_mul, mul_one, ← ha_def]; exact ha
      rw [← norm_neg, neg_sub]
      exact lt_of_mul_lt_mul_left this hαpos.le

theorem norm_le_of_near {K : Type} [NormedField K] [IsUltrametricDist K] {z y₀ : K} (h : ‖z - y₀‖ < 1)
    (h0 : ‖y₀‖ ≤ 1) : ‖z‖ ≤ 1 := by
  have e : z = (z - y₀) + y₀ := by ring
  rw [e]; exact unitNormLoc_add_le h.le h0

theorem solve_int {K : Type} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
    (T M ε x₀ y₀ : K) (hT : ‖T‖ ≤ 1) (hM : ‖M‖ ≤ 1) (hD : ‖T ^ 2 - 4 * M‖ = 1) (hε : ‖ε‖ = 1)
    (hx : ‖x₀‖ ≤ 1) (hy : ‖y₀‖ ≤ 1) (h0 : ‖x₀ ^ 2 + T * x₀ * y₀ + M * y₀ ^ 2 - ε‖ < 1) :
    ∃ x y : K, ‖x‖ ≤ 1 ∧ ‖y‖ ≤ 1 ∧ x ^ 2 + T * x * y + M * y ^ 2 = ε := by
  have h2 : ‖(2 : K)‖ ≤ 1 := unitNormLoc_norm_two_le
  have hgx : ‖2 * x₀ + T * y₀‖ ≤ 1 :=
    unitNormLoc_add_le (unitNormLoc_mul_le h2 hx) (unitNormLoc_mul_le hT hy)
  rcases hgx.lt_or_eq with hlt | heq
  · have hgy : ‖2 * M * y₀ + T * x₀‖ = 1 := by
      have hle : ‖2 * M * y₀ + T * x₀‖ ≤ 1 :=
        unitNormLoc_add_le (unitNormLoc_mul_le (unitNormLoc_mul_le h2 hM) hy) (unitNormLoc_mul_le hT hx)
      rcases hle.lt_or_eq with hlt' | h'
      · exfalso
        have ey : (T ^ 2 - 4 * M) * y₀ = T * (2 * x₀ + T * y₀) + (-2) * (2 * M * y₀ + T * x₀) := by ring
        have ex : (T ^ 2 - 4 * M) * x₀ = T * (2 * M * y₀ + T * x₀) + (-2 * M) * (2 * x₀ + T * y₀) := by ring
        have hn2 : ‖(-2 : K)‖ ≤ 1 := by rw [norm_neg]; exact h2
        have hy1 : ‖y₀‖ < 1 := by
          have := unitNormLoc_add_lt (unitNormLoc_mul_lt hT hlt) (unitNormLoc_mul_lt hn2 hlt')
          rwa [← ey, norm_mul, hD, one_mul] at this
        have hx1 : ‖x₀‖ < 1 := by
          have := unitNormLoc_add_lt (unitNormLoc_mul_lt hT hlt')
            (unitNormLoc_mul_lt (unitNormLoc_mul_le hn2 hM) hlt)
          rwa [← ex, norm_mul, hD, one_mul] at this
        have hq : ‖x₀ ^ 2 + T * x₀ * y₀ + M * y₀ ^ 2‖ < 1 := by
          refine unitNormLoc_add_lt (unitNormLoc_add_lt ?_ ?_) ?_
          · rw [pow_two]; exact unitNormLoc_mul_lt hx hx1
          · exact unitNormLoc_mul_lt (unitNormLoc_mul_le hT hx) hy1
          · rw [pow_two, ← mul_assoc]; exact unitNormLoc_mul_lt (unitNormLoc_mul_le hM hy) hy1
        have : ‖ε‖ < 1 := by
          have e : ε = (x₀ ^ 2 + T * x₀ * y₀ + M * y₀ ^ 2) + -(x₀ ^ 2 + T * x₀ * y₀ + M * y₀ ^ 2 - ε) := by ring
          rw [e]; exact unitNormLoc_add_lt hq (by rw [norm_neg]; exact h0)
        rw [hε] at this; exact lt_irrefl _ this
      · exact h'
    have hf : ‖M * y₀ ^ 2 + T * x₀ * y₀ + (x₀ ^ 2 - ε)‖ < 1 := by
      have e : M * y₀ ^ 2 + T * x₀ * y₀ + (x₀ ^ 2 - ε) = x₀ ^ 2 + T * x₀ * y₀ + M * y₀ ^ 2 - ε := by ring
      rw [e]; exact h0
    obtain ⟨y, hy'⟩ := unitNormLoc_newton M (T * x₀) (x₀ ^ 2 - ε) y₀ hM (by rw [hgy, one_pow]; exact hf)
    obtain ⟨z, hz, hzn⟩ := near_root M (T * x₀) (x₀ ^ 2 - ε) y₀ y hgy hf hy'
    exact ⟨x₀, z, hx, norm_le_of_near hzn hy, by linear_combination hz⟩
  · have hf : ‖1 * x₀ ^ 2 + T * y₀ * x₀ + (M * y₀ ^ 2 - ε)‖ < 1 := by
      have e2 : 1 * x₀ ^ 2 + T * y₀ * x₀ + (M * y₀ ^ 2 - ε) = x₀ ^ 2 + T * x₀ * y₀ + M * y₀ ^ 2 - ε := by ring
      rw [e2]; exact h0
    have hg : ‖2 * 1 * x₀ + T * y₀‖ = 1 := by rw [mul_one]; exact heq
    obtain ⟨x, hx'⟩ := unitNormLoc_newton 1 (T * y₀) (M * y₀ ^ 2 - ε) x₀ (by rw [norm_one])
      (by rw [hg, one_pow]; exact hf)
    obtain ⟨z, hz, hzn⟩ := near_root 1 (T * y₀) (M * y₀ ^ 2 - ε) x₀ x hg hf hx'
    exact ⟨z, y₀, norm_le_of_near hzn hx, hy, by linear_combination hz⟩

end PI.OmLocU.Nrm
end
end
end
