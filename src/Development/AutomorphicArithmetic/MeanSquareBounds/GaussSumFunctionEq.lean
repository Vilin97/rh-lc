module

public import Development.AutomorphicArithmetic.CharacterBoxes.PairGood
public import Formalism.GL3MeanSquares.SecondEstimateOfIntervalHypothesis
public import Development.AutomorphicArithmetic.MeanSquareBounds.SmallZeros
public import Development.AutomorphicArithmetic.MeanSquareBounds.PrimeSetTwoBounds
public import Development.AutomorphicArithmetic.MeanSquareBounds.GIntegral
public import Development.AutomorphicArithmetic.MeanSquareBounds.IntThin
public import Development.AutomorphicArithmetic.MeanSquareBounds.PsiThin
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
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MeanSquareHypWIff
public import Development.AutomorphicArithmetic.MeanSquareBounds.realCond
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicArithmetic.MeanSquareBounds.Thin

section

@[expose] public section

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

theorem thin :
    ∀ ε A c c₀ : ℝ, 0 < ε → 0 < A → 0 < c → 0 < c₀ → ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
      Real.log N ≤ A * x ^ (ε / 5) * Real.log x ^ 2 → (χ ^ 2 = 1 → χ ≠ 1 → NoExc c₀ χ) →
      ∀ y : ℝ, Real.exp (x ^ (ε / 3)) / 3 ≤ y → ‖G0 χ y‖ ≤ y * Real.exp (-(c * x ^ (ε / 8))) := by
  intro ε A c c₀ hε hA hc hc₀
  obtain ⟨C, c1, hC, hc1, hpsi⟩ := psi_thin c₀ hc₀
  obtain ⟨x1, hx1⟩ := int_thin ε c1 C (A + 1) c hε hc1 hC (by linarith) hc
  refine ⟨max x1 (max (Real.exp 1) ((3 : ℝ) ^ (3 / ε))), ?_⟩
  intro x hx N _ χ hprim hN hexc y hy
  have hx1' : x1 ≤ x := le_trans (le_max_left _ _) hx
  have hxe : Real.exp 1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx3 : (3 : ℝ) ^ (3 / ε) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have he1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hxone : 1 ≤ x := he1.trans hxe
  have hpow3 : (3 : ℝ) ≤ x ^ (ε / 3) := by
    calc (3 : ℝ) = ((3 : ℝ) ^ (3 / ε)) ^ (ε / 3) := by
          rw [← Real.rpow_mul (by norm_num)]
          have : 3 / ε * (ε / 3) = 1 := by field_simp
          rw [this, Real.rpow_one]
      _ ≤ x ^ (ε / 3) := Real.rpow_le_rpow (by positivity) hx3 (by positivity)
  have hy1 : Real.exp 1 ≤ y := by
    have h2 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
    have h3 : Real.exp 3 = Real.exp 1 * Real.exp 2 := by rw [← Real.exp_add]; norm_num
    have h4 : Real.exp 3 ≤ Real.exp (x ^ (ε / 3)) := Real.exp_le_exp.2 hpow3
    have h5 : Real.exp 1 * 3 ≤ Real.exp 3 := by rw [h3]; nlinarith [Real.exp_pos 1]
    linarith
  have hy1' : 1 ≤ y := he1.trans hy1
  have hlogx : 1 ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 1) hxe
    rwa [Real.log_exp] at this
  have hxε : 1 ≤ x ^ (ε / 5) := Real.one_le_rpow hxone (by positivity)
  have hP : 1 ≤ x ^ (ε / 5) * Real.log x ^ 2 := one_le_mul_of_one_le_of_one_le hxε (one_le_pow₀ hlogx)
  have hlam : max 1 (Real.log N) ≤ (A + 1) * x ^ (ε / 5) * Real.log x ^ 2 := by
    rw [mul_assoc]
    rw [mul_assoc] at hN
    refine max_le (by nlinarith) (by nlinarith)
  have hψ := hpsi N χ (max 1 (Real.log N)) hprim (le_max_left _ _) (le_max_right _ _) hexc
  rw [g_integral N χ hprim y hy1', neg_mul, norm_neg]
  exact hx1 x hx1' y (max 1 (Real.log N)) (PI.psi0 χ) hy (le_max_left _ _) hlam
    (fun u hu => hψ u (hy1.trans hu))

end QH
end
end

-- Source module: Development.AutomorphicArithmetic.MeanSquareBounds.GaussSumFunctionEq

section

@[expose] public section

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

private theorem gauss_sum_function_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (y : ℝ) :
    Formalism.HC.An.gChi χ y = G0 χ y := by
  have key : ∀ n ∈ Icc 1 ⌊y⌋₊, max (y / (n : ℝ) - 1) 0 = y / n - 1 := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hy1 : 1 ≤ y := Nat.floor_pos.1 (by omega)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
    have hny : (n : ℝ) ≤ y := (Nat.cast_le.2 hn.2).trans (Nat.floor_le (by linarith))
    have : 1 ≤ y / n := by rw [le_div_iff₀ (by linarith)]; linarith
    exact max_eq_left (by linarith)
  unfold Formalism.HC.An.gChi G0
  by_cases h : χ = 1
  · simp only [h, if_true]
    congr 1
    unfold Formalism.HC.An.G G1
    congr 1
    exact Finset.sum_congr rfl fun n hn => by rw [key n hn]
  · simp only [h, if_false]
    unfold Formalism.HC.An.sumLamChi Gchi
    congr 1
    exact Finset.sum_congr rfl fun n hn => by rw [key n hn]

private theorem isReal_of_sq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (h2 : χ ^ 2 = 1) (a : ZMod N) :
    (χ a).im = 0 := by
  by_cases ha : IsUnit a
  · have h := congrArg (fun f : DirichletCharacter ℂ N => f a) h2
    simp only [pow_two, MulChar.one_apply ha] at h
    rw [MulChar.mul_apply] at h
    have hz : χ a = 1 ∨ χ a = -1 := by
      have : (χ a - 1) * (χ a + 1) = 0 := by ring_nf; rw [← pow_two] at h; rw [h]; ring
      rcases mul_eq_zero.1 this with h1 | h1
      · left; linear_combination h1
      · right; linear_combination h1
    rcases hz with hz | hz <;> simp [hz]
  · simp [MulChar.map_nonunit χ ha]

private theorem level_dvd {φ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (h : H.IsCharE χ) : N ∣ H.condN := by
  obtain ⟨θ, hθ⟩ := h
  have hp : (Formalism.HC.PChar.mk N χ hθ.1) = H.prim θ := (H.isPrimOf_iff θ (Formalism.HC.PChar.mk N χ hθ.1)).1 hθ
  have hN : N = (H.prim θ).N := congrArg Formalism.HC.PChar.N hp
  rw [hN]
  exact DirichletCharacter.conductor_dvd_level (H.dir θ)

theorem thinH :
    UpperTheory.Top.ThinH := by
  refine ⟨1, one_pos, fun B eps he he52 => ?_⟩
  obtain ⟨c₀s, hc₀s, hsmall⟩ := small_zeros (8 * ⌊B⌋₊)
  have hc₀ : 0 < min c₀s (1 / 400) := lt_min hc₀s (by norm_num)
  obtain ⟨x₀, hx₀⟩ := thin eps 2 1 (min c₀s (1 / 400)) he two_pos one_pos hc₀
  refine ⟨x₀, fun x hx φ H hB hlog hRB => ?_⟩
  intro N _ χ hχ y hy
  rw [gauss_sum_function_eq]
  have hprim : χ.IsPrimitive := by
    obtain ⟨θ, hθ⟩ := hχ
    exact hθ.1
  have hNd : N ∣ H.condN := level_dvd H χ hχ
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hlogN : Real.log N ≤ 2 * x ^ (eps / 5) * Real.log x ^ 2 :=
    (Real.log_le_log (by exact_mod_cast hNpos)
      (by exact_mod_cast Nat.le_of_dvd H.condN_pos hNd)).trans hlog
  refine hx₀ x hx N χ hprim hlogN ?_ y hy
  intro h2 h1 β hβ hβ1
  have hq : H.q.Prime := H.hyp.1
  have hd : H.d.Prime := H.hyp.2.1
  by_cases hqd : H.q ∣ N ∨ H.d ∣ N
  · exact hRB (Formalism.HC.PChar.mk N χ hprim) hχ (isReal_of_sq χ h2) hqd β
      (by have := min_le_right c₀s (1 / 400); linarith)
  · push_neg at hqd
    have hQ0 : H.QS ≠ 0 := (H.QS_pos).ne'
    have hsplitQ := Nat.ordProj_mul_ordCompl_eq_self H.QS 2
    have hprimes : ∀ p : ℕ, p.Prime → p ∣ N → p ∣ 8 * (H.QS / 2 ^ H.QS.factorization 2) ∨ p = H.q ∨ p = H.d := by
      intro p hp hpN
      have hpc : p ∣ H.QS * H.q * H.d := hpN.trans hNd
      rcases (Nat.Prime.dvd_mul hp).1 hpc with h | h
      · rcases (Nat.Prime.dvd_mul hp).1 h with h' | h'
        · left
          by_cases hp2 : p = 2
          · subst hp2
            exact Dvd.dvd.mul_right (by norm_num) _
          · apply Dvd.dvd.mul_left
            rw [← hsplitQ] at h'
            have hcop : Nat.Coprime p (2 ^ H.QS.factorization 2) :=
              Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
            exact hcop.dvd_of_dvd_mul_left h'
        · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp hq).1 h'))
      · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp hd).1 h))
    have hdiv := real_cond (8 * (H.QS / 2 ^ H.QS.factorization 2)) H.q H.d N χ hprim h2
      (dvd_mul_right 8 _) hq hd hprimes
    have hcq : Nat.Coprime N H.q := ((Nat.Prime.coprime_iff_not_dvd hq).2 hqd.1).symm
    have hcd : Nat.Coprime N H.d := ((Nat.Prime.coprime_iff_not_dvd hd).2 hqd.2).symm
    have hN0 : N ∣ 8 * (H.QS / 2 ^ H.QS.factorization 2) :=
      hcq.dvd_of_dvd_mul_right (hcd.dvd_of_dvd_mul_right hdiv)
    have hopos : 0 < H.QS / 2 ^ H.QS.factorization 2 := Nat.ordCompl_pos 2 hQ0
    have hofl : H.QS / 2 ^ H.QS.factorization 2 ≤ ⌊B⌋₊ := Nat.le_floor hB
    have hNle : N ≤ 8 * ⌊B⌋₊ := (Nat.le_of_dvd (by omega) hN0).trans (by omega)
    exact hsmall N χ hNle h1 β (by have := min_le_left c₀s (1 / 400); linarith) hβ1

end QH
end
end
