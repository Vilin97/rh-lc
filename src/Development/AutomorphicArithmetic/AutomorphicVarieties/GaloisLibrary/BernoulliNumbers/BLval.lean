module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar
public import Mathlib.NumberTheory.LSeries.HurwitzZeta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Termdiff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Termsum
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LSeries.RiemannZeta
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Sumicc
import Mathlib.Algebra.Algebra.Field
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Hurzero

section

@[expose] public section

open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_hurzero :
    ∀ (x : ℝ), 0 < x → x ≤ 1 → HurwitzZeta.hurwitzZeta (x : UnitAddCircle) 0 = 1 / 2 - (x : ℂ) := by
  intro x hx0 hx1
  set U : Set ℂ := {s | -1 / 2 < s.re} ∩ Metric.ball 0 3 with hU
  have hUo : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
  have hUc : IsPreconnected U := ((convex_halfSpace_re_gt _).inter (convex_ball _ _)).isPreconnected
  have hG : DifferentiableOn ℂ (fun s => HurwitzZeta.hurwitzZeta (x : UnitAddCircle) s
      - HurwitzZeta.hurwitzZeta ((1 : ℝ) : UnitAddCircle) s - (1 - (x : ℂ))) U := by
    intro s _
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.sub_const
    rcases eq_or_ne s 1 with rfl | hs
    · have := (HurwitzZeta.differentiableAt_hurwitzZeta_sub_one_div (x : UnitAddCircle)).sub
        (HurwitzZeta.differentiableAt_hurwitzZeta_sub_one_div ((1 : ℝ) : UnitAddCircle))
      exact this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => by
        simp only [Pi.sub_apply]; ring)
    · exact (HurwitzZeta.differentiableAt_hurwitzZeta _ hs).sub
        (HurwitzZeta.differentiableAt_hurwitzZeta _ hs)
  have hev : ∀ᶠ s in nhds (2 : ℂ), 1 < s.re :=
    (Complex.continuous_re.tendsto 2).eventually (lt_mem_nhds (by norm_num))
  have h2 : (2 : ℂ) ∈ U := ⟨by simp; norm_num, by simp; norm_num⟩
  have heq := ((b_termdiff x hx0 hx1).analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq
    (hG.analyticOnNhd hUo) hUc h2 (hev.mono fun s hs => b_termsum x hx0 hx1 s hs)
  have h0 := heq (show (0 : ℂ) ∈ U from ⟨by simp; norm_num, by simp⟩)
  have h1 : HurwitzZeta.hurwitzZeta ((1 : ℝ) : UnitAddCircle) 0 = -1 / 2 := by
    rw [AddCircle.coe_period, HurwitzZeta.hurwitzZeta_zero, riemannZeta_zero]
  simp only [neg_zero, Complex.cpow_zero, sub_self, mul_zero, tsum_zero] at h0
  rw [h1] at h0
  linear_combination -h0
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.BLval

section

@[expose] public section

open Finset UpperTheory.V.Bern

private theorem hurwitzZeta_one_sub_eq_bernoulli (k : ℕ) (hk : 1 ≤ k) (x : ℝ) (h0 : 0 < x) (h1 : x ≤ 1) :
    HurwitzZeta.hurwitzZeta (x : UnitAddCircle) (1 - k) =
      -1 / k * ((Polynomial.bernoulli k).map (algebraMap ℚ ℂ)).eval (x : ℂ) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have e : (1 : ℂ) - ((0 + 1 : ℕ) : ℂ) = 0 := by push_cast; ring
    rw [e, b_hurzero x h0 h1]
    simp [Polynomial.bernoulli_one]
  · have := HurwitzZeta.hurwitzZeta_neg_nat (k := m) (x := x) hm.ne' ⟨h0.le, h1⟩
    have e : (1 : ℂ) - ((m + 1 : ℕ) : ℂ) = -(m : ℂ) := by push_cast; ring
    rw [e, this]
    push_cast
    ring

theorem UpperTheory.V.Bern.b_lval :
    ∀ {N : ℕ} [NeZero N] (Φ : ZMod N → ℂ) (k : ℕ), 1 ≤ k → ZMod.LFunction Φ (1 - k) = -genB k Φ / k := by
  intro N _ Φ k hk
  have hN : (0:ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hpow : (N : ℂ) ^ (-(1 - (k:ℂ))) = (N:ℂ) ^ ((k:ℤ) - 1) := by
    rw [show -(1 - (k:ℂ)) = (((k:ℤ) - 1 : ℤ) : ℂ) by push_cast; ring, Complex.cpow_intCast]
  rw [ZMod.LFunction, hpow, ← b_sumicc, genB, Finset.mul_sum, neg_div, Finset.sum_div,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mem_Icc] at ha
  have hx0 : (0:ℝ) < a / N := div_pos (by exact_mod_cast ha.1) hN
  have hx1 : (a:ℝ) / N ≤ 1 := (div_le_one hN).mpr (by exact_mod_cast ha.2)
  rw [ZMod.toAddCircle_natCast, hurwitzZeta_one_sub_eq_bernoulli k hk _ hx0 hx1, bcoef, map_mul, map_zpow₀,
    map_natCast, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map]
  have hk0 : (k:ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hq : (algebraMap ℚ ℂ) ((a:ℚ) / N) = (((a:ℝ) / N : ℝ) : ℂ) := by push_cast; rfl
  rw [hq]
  field_simp
end
end
