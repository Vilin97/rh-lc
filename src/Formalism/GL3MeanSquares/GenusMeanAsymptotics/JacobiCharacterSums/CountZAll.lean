module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountSt
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZBlock
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZDetect
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZDual
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZDefs
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
public import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZMoll
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZNum
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZPair
public import Formalism.LFunctionBounds.LFunctionBoundsProofs.LFunctionEqGOfOneLt
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Lemma
public import Formalism.LFunctionBounds.PositivityBound
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar

-- Source module: Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZFinal

section

@[expose] public section

open Complex Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD

attribute [local irreducible] q0 pY pJ pN in
theorem final_bound_of_assembly : FinalOf := by
  rintro ⟨C, hC0, hC⟩ hDet hBC hNum
  obtain ⟨Q₀, C', hQ₀, hN⟩ := hNum C hC0
  classical

  let F : Finset PC := (range ⌈Q₀⌉₊).sigma (fun N => @Finset.univ (DirichletCharacter ℂ (N + 1)) (Fintype.ofFinite _))
  refine ⟨max C' ((F.card : ℝ) + 1), fun Q S hQ hS => ?_⟩
  have hQ14 : (1 : ℝ) ≤ Q ^ (1 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hQ14' : (0 : ℝ) ≤ Q ^ (1 / 4 : ℝ) := by linarith
  rcases lt_or_ge Q Q₀ with hQQ | hQQ
  ·
    have hsub : S ⊆ F := by
      intro p hp
      obtain ⟨-, hpQ, -⟩ := hS p hp
      simp only [F, mem_sigma, mem_range, mem_univ, and_true]
      have h1 : ((p.1 : ℕ) : ℝ) < Q₀ := by push_cast at hpQ; linarith
      have h2 : (Q₀ : ℝ) ≤ (⌈Q₀⌉₊ : ℝ) := Nat.le_ceil Q₀
      exact_mod_cast h1.trans_le h2
    have hc : (S.card : ℝ) ≤ F.card := by exact_mod_cast card_le_card hsub
    calc (S.card : ℝ) ≤ (F.card : ℝ) + 1 := by linarith
      _ ≤ max C' ((F.card : ℝ) + 1) := le_max_right _ _
      _ = max C' ((F.card : ℝ) + 1) * 1 := (mul_one _).symm
      _ ≤ max C' ((F.card : ℝ) + 1) * Q ^ (1 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_left hQ14 (le_trans (by positivity) (le_max_right _ _))
  ·
    obtain ⟨hsm, hfin⟩ := hN Q hQQ
    have hQ20 : (20 : ℝ) ≤ Q := le_trans hQ₀ hQQ
    set J := pJ Q with hJdef
    have hJ1 : 1 ≤ J := by rw [hJdef]; unfold pJ; omega
    have hY1 : 1 ≤ pY Q := by
      unfold pY
      have : 1 ≤ q0 Q := by unfold q0; exact Nat.one_le_iff_ne_zero.mpr (by
        intro h; rw [Nat.ceil_eq_zero] at h; linarith)
      exact Nat.one_le_pow _ _ (by omega)

    have hcard := Finset.card_filter_add_card_filter_not (s := S) (fun p : PC => p.1 = 0)
    set S' := S.filter (fun p : PC => ¬ p.1 = 0) with hS'
    have h0 : (S.filter (fun p : PC => p.1 = 0)).card ≤ 1 := by
      refine Finset.card_le_one.mpr (fun a ha b hb => ?_)
      obtain ⟨Na, χa⟩ := a
      obtain ⟨Nb, χb⟩ := b
      simp only [mem_filter] at ha hb
      obtain ⟨-, rfl⟩ := ha
      obtain ⟨-, rfl⟩ := hb
      have e1 : χa = 1 := DirichletCharacter.level_one' _ rfl
      have e2 : χb = 1 := DirichletCharacter.level_one' _ rfl
      rw [e1, e2]

    let ρ : PC → ℂ := fun p => if h : (∃ s : ℂ, 1 - 1 / 400 < s.re ∧ |s.im| ≤ Q ∧
        DirichletCharacter.LFunction p.2 s = 0) then h.choose else 0
    have hρ : ∀ p ∈ S, 1 - 1 / 400 < (ρ p).re ∧ |(ρ p).im| ≤ Q ∧ DirichletCharacter.LFunction p.2 (ρ p) = 0 := by
      intro p hp
      have h := (hS p hp).2.2
      simp only [ρ, dif_pos h]
      exact h.choose_spec
    let jf : PC → ℕ := fun p => if h : (∃ j ∈ range J, 1 / (2 * (J : ℝ)) ≤
        ‖blk (pY Q) (pN Q) (pY Q * 2 ^ j) p (ρ p)‖) then h.choose else 0
    have hne1 : ∀ p ∈ S', p.2 ≠ 1 := by
      intro p hp h
      simp only [hS', mem_filter] at hp
      have hc : p.2.conductor = p.1 + 1 := (hS p hp.1).1
      rw [h, DirichletCharacter.conductor_one] at hc
      omega
    have hjf : ∀ p ∈ S', jf p ∈ range J ∧
        1 / (2 * (J : ℝ)) ≤ ‖blk (pY Q) (pN Q) (pY Q * 2 ^ (jf p)) p (ρ p)‖ := by
      intro p hp
      have hpS : p ∈ S := (mem_filter.1 hp).1
      have hp0 : p.1 ≠ 0 := (mem_filter.1 hp).2
      obtain ⟨hprim, hlev, -⟩ := hS p hpS
      obtain ⟨h1, h2, h3⟩ := hρ p hpS
      have h := hDet Q hQ20 p hprim hp0 hlev (ρ p) (by unfold s0; exact h1) h2 h3
      rw [← hJdef] at h
      simp only [jf, dif_pos h]
      exact h.choose_spec
    have hre1 : ∀ p ∈ S', (ρ p).re < 1 := by
      intro p hp
      by_contra hc
      push Not at hc
      have hpS : p ∈ S := (mem_filter.1 hp).1
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re p.2 (Or.inl (hne1 p hp)) hc (hρ p hpS).2.2

    have hfib := Finset.card_eq_sum_card_fiberwise (f := jf) (s := S') (t := range J) (fun p hp => (hjf p hp).1)
    set K : ℕ := pY Q * 2 ^ J with hK
    have hKpos : (0 : ℝ) ≤ K := Nat.cast_nonneg _
    have hblock : ∀ j ∈ range J, ((S'.filter (fun p => jf p = j)).card : ℝ) ≤
        8 * (J : ℝ) ^ 2 * C * (K : ℝ) ^ (3 / 200 : ℝ) := by
      intro j hj
      have hU : 1 ≤ pY Q * 2 ^ j := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by positivity))
      have h := hBC C hC0 hC Q (by linarith) (pY Q) (pN Q) (pY Q * 2 ^ j) J hU hJ1 (hsm j hj)
        (S'.filter (fun p => jf p = j)) ρ (by
          intro p hp
          obtain ⟨hpS', hpj⟩ := mem_filter.1 hp
          have hpS : p ∈ S := (mem_filter.1 hpS').1
          obtain ⟨hprim, hlev, -⟩ := hS p hpS
          obtain ⟨h1, h2, -⟩ := hρ p hpS
          refine ⟨hprim, hlev, by unfold s0; exact h1, hre1 p hpS', h2, ?_⟩
          have := (hjf p hpS').2
          rw [hpj] at this
          exact this)
      refine h.trans ?_
      have hUK : ((pY Q * 2 ^ j : ℕ) : ℝ) ≤ K := by
        have : 2 ^ j ≤ 2 ^ J := Nat.pow_le_pow_right (by norm_num) (mem_range.1 hj).le
        exact_mod_cast Nat.mul_le_mul_left _ this
      have hrp : ((pY Q * 2 ^ j : ℕ) : ℝ) ^ (3 / 200 : ℝ) ≤ (K : ℝ) ^ (3 / 200 : ℝ) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hUK (by norm_num)
      have : (0 : ℝ) ≤ 8 * (J : ℝ) ^ 2 * C := by positivity
      exact mul_le_mul_of_nonneg_left hrp this
    have hS'card : (S'.card : ℝ) ≤ (J : ℝ) * (8 * (J : ℝ) ^ 2 * C * (K : ℝ) ^ (3 / 200 : ℝ)) := by
      rw [hfib]; push_cast
      refine (sum_le_sum hblock).trans ?_
      rw [sum_const, card_range, nsmul_eq_mul]
    have htot : (S.card : ℝ) ≤ 1 + (J : ℝ) * (8 * (J : ℝ) ^ 2 * C * (K : ℝ) ^ (3 / 200 : ℝ)) := by
      have : (S.card : ℝ) = (S.filter (fun p : PC => p.1 = 0)).card + S'.card := by
        rw [← hcard]; push_cast; ring
      rw [this]
      have : ((S.filter (fun p : PC => p.1 = 0)).card : ℝ) ≤ 1 := by exact_mod_cast h0
      linarith
    calc (S.card : ℝ) ≤ C' * Q ^ (1 / 4 : ℝ) := htot.trans hfin
      _ ≤ max C' ((F.card : ℝ) + 1) * Q ^ (1 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hQ14'

end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
end
end
end

-- Source module: Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZTwist

section

@[expose] public section

open Complex Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD

lemma norm_cpow_neg_le_one {n : ℕ} (hn : 1 ≤ n) {w : ℂ} (hw : 0 ≤ w.re) : ‖(n : ℂ) ^ (-w)‖ ≤ 1 := by
  rw [norm_natCast_cpow_of_pos (by omega), neg_re]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by linarith)

lemma norm_cpow_step_le {i U : ℕ} (hU : 1 ≤ U) (hi : U ≤ i) {w : ℂ} (hw : 0 < w.re) :
    ‖(((i + 1 : ℕ) : ℂ) ^ (-w) - (i : ℂ) ^ (-w))‖ ≤ ‖w‖ / U := by
  have hi0 : (0 : ℝ) < i := by exact_mod_cast (by omega : 0 < i)
  have h := Formalism.FX.LFunctionPartialSum.norm_cpow_sub_le' hi0 hw
  have e1 : (((i : ℝ) : ℂ)) = (i : ℂ) := by push_cast; rfl
  have e2 : ((((i : ℝ) + 1 : ℝ)) : ℂ) = ((i + 1 : ℕ) : ℂ) := by push_cast; rfl
  rw [e1, e2, norm_sub_rev] at h
  refine h.trans ?_
  have hUi : (U : ℝ) ≤ i := by exact_mod_cast hi
  have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
  have h1 : (i : ℝ) ^ (-w.re - 1) ≤ (i : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ i)) (by linarith)
  have h2 : (i : ℝ) ^ (-1 : ℝ) ≤ 1 / U := by
    rw [Real.rpow_neg_one, one_div]
    exact inv_anti₀ hU0 hUi
  calc ‖w‖ * (i : ℝ) ^ (-w.re - 1) ≤ ‖w‖ * (1 / U) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (norm_nonneg _)
    _ = ‖w‖ / U := by ring

theorem pair_twist_bound : PairTwistOf := by
  intro hPS p p' hp hp' hne w hw U hU
  set m : ℝ := (((p.1 + 1) * (p'.1 + 1) : ℕ) : ℝ) with hm
  set g : ℕ → ℂ := fun n => cv p n * (starRingEnd ℂ) (cv p' n) with hg
  set f : ℕ → ℂ := fun n => (n : ℂ) ^ (-w) with hf
  have hGs : ∀ k, ‖∑ i ∈ range k, g i‖ ≤ m := fun k => hPS p p' hp hp' hne k
  have hm0 : 0 ≤ m := by positivity
  have hrw : ∑ n ∈ Ioc U (2 * U), cv p n * (starRingEnd ℂ) (cv p' n) * (n : ℂ) ^ (-w) =
      ∑ n ∈ Ioc U (2 * U), f n • g n := by
    refine sum_congr rfl (fun n _ => ?_); simp only [hf, hg, smul_eq_mul]; ring
  rw [hrw, Finset.sum_Ioc_by_parts f g (by omega : U < 2 * U)]
  have hb1 : ‖f (2 * U) • ∑ i ∈ range (2 * U + 1), g i‖ ≤ m := by
    rw [smul_eq_mul, norm_mul]
    calc ‖f (2 * U)‖ * ‖∑ i ∈ range (2 * U + 1), g i‖ ≤ 1 * m :=
          mul_le_mul (norm_cpow_neg_le_one (by omega) hw.le) (hGs _) (norm_nonneg _) zero_le_one
      _ = m := one_mul m
  have hb2 : ‖f (U + 1) • ∑ i ∈ range (U + 1), g i‖ ≤ m := by
    rw [smul_eq_mul, norm_mul]
    calc ‖f (U + 1)‖ * ‖∑ i ∈ range (U + 1), g i‖ ≤ 1 * m :=
          mul_le_mul (norm_cpow_neg_le_one (by omega) hw.le) (hGs _) (norm_nonneg _) zero_le_one
      _ = m := one_mul m
  have hb3 : ‖∑ i ∈ Ioc U (2 * U - 1), (f (i + 1) - f i) • ∑ k ∈ range (i + 1), g k‖ ≤ m * ‖w‖ := by
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ i ∈ Ioc U (2 * U - 1),
        ‖(f (i + 1) - f i) • ∑ k ∈ range (i + 1), g k‖ ≤ ‖w‖ / U * m := by
      intro i hi
      rw [smul_eq_mul, norm_mul]
      have hi' : U ≤ i := by have := (mem_Ioc.1 hi).1; omega
      exact mul_le_mul (norm_cpow_step_le hU hi' hw) (hGs _) (norm_nonneg _) (by positivity)
    refine (sum_le_sum hterm).trans ?_
    rw [sum_const, Nat.card_Ioc, nsmul_eq_mul]
    have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
    have hcnt : ((2 * U - 1 - U : ℕ) : ℝ) ≤ U := by exact_mod_cast (by omega : 2 * U - 1 - U ≤ U)
    calc ((2 * U - 1 - U : ℕ) : ℝ) * (‖w‖ / U * m) ≤ U * (‖w‖ / U * m) :=
          mul_le_mul_of_nonneg_right hcnt (by positivity)
      _ = m * ‖w‖ := by field_simp
  calc ‖f (2 * U) • ∑ i ∈ range (2 * U + 1), g i - f (U + 1) • ∑ i ∈ range (U + 1), g i -
        ∑ i ∈ Ioc U (2 * U - 1), (f (i + 1) - f i) • ∑ k ∈ range (i + 1), g k‖
      ≤ m + m + m * ‖w‖ := by
        refine (norm_sub_le _ _).trans ?_
        refine add_le_add ((norm_sub_le _ _).trans (add_le_add hb1 hb2)) hb3
    _ ≤ 2 * m * (1 + ‖w‖) := by nlinarith [norm_nonneg w]

end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
end
end
end

-- Source module: Formalism.LFunctionBounds.LFunctionBoundsProofs.DivisorBound

section

@[expose] public section

namespace Formalism.FX

open Finset

theorem succ_le_max_mul_exp (a : ℝ) (ha : 0 < a) (k : ℕ) :
    ((k : ℝ) + 1) ≤ max 1 (1 / a) * Real.exp (a * k) := by
  have hM1 : (1 : ℝ) ≤ max 1 (1 / a) := le_max_left _ _
  have hMa : 1 ≤ max 1 (1 / a) * a := by
    calc (1 : ℝ) = (1 / a) * a := by field_simp
      _ ≤ max 1 (1 / a) * a := mul_le_mul_of_nonneg_right (le_max_right _ _) ha.le
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  calc ((k : ℝ) + 1) ≤ max 1 (1 / a) * (1 + a * k) := by nlinarith
    _ ≤ max 1 (1 / a) * Real.exp (a * k) :=
      mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (a * k)]) (by linarith)

theorem succ_le_max_mul_pow (e : ℝ) (he : 0 < e) (p k : ℕ) (hp : 2 ≤ p) :
    ((k : ℝ) + 1) ≤ max 1 (1 / (e * Real.log 2)) * ((p : ℝ) ^ e) ^ k := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hlog : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) (by exact_mod_cast hp)
  have ha : 0 < e * Real.log 2 := mul_pos he (Real.log_pos (by norm_num))
  refine (succ_le_max_mul_exp _ ha k).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (le_trans zero_le_one (le_max_left _ _))
  rw [Real.rpow_def_of_pos hp0, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  calc e * Real.log 2 * k ≤ e * Real.log p * k :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog he.le) hk
    _ = k * (Real.log p * e) := by ring

theorem succ_le_pow_of_two_le (e : ℝ) (p k : ℕ) (hp : 2 ≤ (p : ℝ) ^ e) :
    ((k : ℝ) + 1) ≤ ((p : ℝ) ^ e) ^ k := by
  have hx : (0 : ℝ) ≤ (p : ℝ) ^ e := by positivity
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    have h1 : ((k : ℝ) + 1) * 2 ≤ ((p : ℝ) ^ e) ^ k * (p : ℝ) ^ e :=
      mul_le_mul ih hp (by norm_num) (by positivity)
    have hk : (0 : ℝ) ≤ k := k.cast_nonneg
    push_cast
    linarith

theorem rpow_eq_prod_primeFactors (e : ℝ) {n : ℕ} (hn0 : n ≠ 0) :
    (n : ℝ) ^ e = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ e) ^ (n.factorization p) := by
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn0]
  rw [Finsupp.prod, Nat.support_factorization]
  push_cast
  rw [← Real.finsetProd_rpow _ _ (fun p _ => by positivity)]
  refine Finset.prod_congr rfl fun p _ => ?_
  have hx : (0 : ℝ) ≤ p := p.cast_nonneg
  rw [← Real.rpow_natCast (p : ℝ) (n.factorization p), ← Real.rpow_mul hx,
    mul_comm ((n.factorization p : ℕ) : ℝ) e, Real.rpow_mul hx, Real.rpow_natCast]

theorem divisor_weight_bound : DivisorBound := by
  intro e he
  set M := max 1 (1 / (e * Real.log 2)) with hM
  set K := ⌈(2 : ℝ) ^ (1 / e)⌉₊ with hK
  refine ⟨M ^ K, fun n hn => ?_⟩
  have hn0 : n ≠ 0 := by omega
  have hM1 : (1 : ℝ) ≤ M := le_max_left _ _
  have hcard : ((n.divisors.card : ℕ) : ℝ) =
      ∏ p ∈ n.primeFactors, (((n.factorization p : ℕ) : ℝ) + 1) := by
    rw [Nat.card_divisors hn0]
    norm_cast
  rw [hcard, rpow_eq_prod_primeFactors e hn0]
  have hfac : ∀ p ∈ n.primeFactors, (((n.factorization p : ℕ) : ℝ) + 1) ≤
      (if p < K then M else 1) * ((p : ℝ) ^ e) ^ (n.factorization p) := by
    intro p hp
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    split_ifs with hpK
    · exact succ_le_max_mul_pow e he p _ hp2
    · rw [one_mul]
      apply succ_le_pow_of_two_le
      have h1 : (2 : ℝ) ^ (1 / e) ≤ p :=
        (Nat.le_ceil _).trans (by exact_mod_cast (not_lt.mp hpK))
      calc (2 : ℝ) = ((2 : ℝ) ^ (1 / e)) ^ e := by
            rw [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ he.ne', Real.rpow_one]
        _ ≤ (p : ℝ) ^ e := Real.rpow_le_rpow (by positivity) h1 he.le
  calc ∏ p ∈ n.primeFactors, (((n.factorization p : ℕ) : ℝ) + 1)
      ≤ ∏ p ∈ n.primeFactors, ((if p < K then M else 1) * ((p : ℝ) ^ e) ^ (n.factorization p)) :=
        Finset.prod_le_prod₀ (fun p _ => by positivity) hfac
    _ = (∏ p ∈ n.primeFactors, (if p < K then M else 1)) *
          ∏ p ∈ n.primeFactors, ((p : ℝ) ^ e) ^ (n.factorization p) := Finset.prod_mul_distrib
    _ ≤ M ^ K * ∏ p ∈ n.primeFactors, ((p : ℝ) ^ e) ^ (n.factorization p) := by
        refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun p _ => by positivity)
        rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
        apply pow_le_pow_right₀ hM1
        calc (n.primeFactors.filter (fun p => p < K)).card ≤ (Finset.range K).card :=
              Finset.card_le_card fun p hp => Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
          _ = K := Finset.card_range K

end Formalism.FX
end
end

-- Source module: Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZAll

section

@[expose] public section

namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD

theorem zero_density_box : Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZeroDensityBox :=
  final_bound_of_assembly (coefficient_square_bound Formalism.FX.divisor_weight_bound) (zero_detection mollifier_identity)
    (blockCountOf_statement duality_inequality (pair_twist_bound pair_sum_bound)) numeric_constants

end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
end
end
