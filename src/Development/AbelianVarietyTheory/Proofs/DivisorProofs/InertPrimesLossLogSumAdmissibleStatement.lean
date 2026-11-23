module

public import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
public import Formalism.SharpRestriction.ParConsts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OtherLossSum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalRingCardinality.DataAmbForm
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OneLeLetterBlockLength

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertLossPrimeSum

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

namespace GlobalTheory.OtherLoss

theorem inertLoss_primeSum : ∀ {eps : ℝ} (Fm : FamP eps), 0 < eps → eps < 1 / 52 → ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x, ∀ j ∈ SizeData₂.lifts (Fm.D x i), ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ (G.IsResidueClassZero (Fm.D x i) p ∨ G.IsSg (Fm.D x i) p) ∧ (p : ℝ) ≤ (Fm.L x i).sc.X'' (Fm.D x i).R.n ∧ ¬ (G.IsResidueClassZero (Fm.D x i) p ∧ G.hP (Fm.D x i) p = 0)) → ∑ p ∈ P, 2 * Real.log (p : ℝ) * |EatI (Fm.L x i) Fm.GK Fm.cX.err j p| ≤ C * (Fm.L x i).B0 := by
  intro eps Fm _ _
  refine ⟨848, 0, by norm_num, fun x _ hx i j hj P hP => ?_⟩
  have h := sum_eatI (K := Fm.GK) (c := Fm.cX.err) (Fm.sizes x hx i) Fm.fixed.2.1 Fm.fixed.2.2.1 Fm.fixed.2.2.2.2.1 hj P
    (fun p hp => ⟨(hP p hp).1, (hP p hp).2.2.1⟩)
  calc _ = 2 * ∑ p ∈ P, |EatI (Fm.L x i) Fm.GK Fm.cX.err j p| * Real.log (p : ℝ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun p _ => by ring
    _ ≤ _ := by linarith

end GlobalTheory.OtherLoss
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumPadicLogLe

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

noncomputable section

namespace GlobalTheory.ConjLoss

theorem sum_padic_log_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n : ℕ) :
    ∑ p ∈ P, Real.log p * (padicValNat p n : ℝ) ≤ Real.log n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Nat.padicValNat_def]
  · have hd : ∏ p ∈ P, p ^ padicValNat p n ∣ n := by
      refine Finset.prod_dvd_of_isRelPrime ?_ fun p _ => (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _))
      intro p hp q hq hpq
      exact Nat.coprime_iff_isRelPrime.1
        (Nat.Coprime.pow _ _ ((Nat.coprime_primes (hP p hp) (hP q hq)).2 hpq))
    have h1 : ∑ p ∈ P, Real.log p * (padicValNat p n : ℝ) =
        Real.log (∏ p ∈ P, (p : ℝ) ^ padicValNat p n) := by
      rw [Real.log_prod]
      · exact Finset.sum_congr rfl fun p _ => by rw [Real.log_pow, mul_comm]
      · intro p hp
        have : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
        positivity
    rw [h1]
    apply Real.log_le_log
    · refine Finset.prod_pos fun p hp => ?_
      have : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
      positivity
    · exact_mod_cast Nat.le_of_dvd hn hd

theorem sum_primes_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n : ℕ) (X a A W : ℝ) (hX : 0 ≤ X) (hXa : X ≤ a)
    (ha : 1 ≤ a) (hA : 0 ≤ A) (hW : 0 ≤ W) :
    ∑ p ∈ P, Real.log p * |(padicValNat p n : ℝ) +
      (if (p : ℝ) ≤ X then A * Real.logb p a + W / ((p : ℝ) ^ 2 - 1) else 0)| ≤
      Real.log n + X * (A * Real.log a) + 2 * (W * Real.log a) := by
  have hla : 0 ≤ Real.log a := Real.log_nonneg ha
  have h1 : ∀ p ∈ P, Real.log p * |(padicValNat p n : ℝ) +
      (if (p : ℝ) ≤ X then A * Real.logb p a + W / ((p : ℝ) ^ 2 - 1) else 0)| ≤
      Real.log p * (padicValNat p n : ℝ) +
      (if (p : ℝ) ≤ X then A * Real.log a + 2 * (W * Real.log a) * ((p : ℝ) ^ 2)⁻¹ else 0) := by
    intro p hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
    have hl : 0 < Real.log p := Real.log_pos (by linarith)
    have hq : 0 < (p : ℝ) ^ 2 - 1 := by nlinarith
    split_ifs with h
    · have hb : 0 ≤ Real.logb p a := Real.logb_nonneg (by linarith) ha
      rw [abs_of_nonneg (by positivity), mul_add, mul_add]
      have e1 : Real.log p * (A * Real.logb p a) = A * Real.log a := by
        unfold Real.logb; field_simp
      have e2 : Real.log p ≤ Real.log a := Real.log_le_log (by linarith) (h.trans hXa)
      have e3 : W / ((p : ℝ) ^ 2 - 1) ≤ 2 * W * ((p : ℝ) ^ 2)⁻¹ := by
        rw [← div_eq_mul_inv, div_le_div_iff₀ hq (by positivity)]
        have : 0 ≤ (p : ℝ) ^ 2 - 2 := by nlinarith
        nlinarith [mul_nonneg hW this]
      have e4 := mul_le_mul e2 e3 (by positivity) hla
      rw [e1]
      nlinarith
    · rw [add_zero, add_zero, abs_of_nonneg (Nat.cast_nonneg _)]
  refine (Finset.sum_le_sum h1).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.sum_filter, add_assoc]
  refine add_le_add (sum_padic_log_le P hP n) ?_
  have hsub : P.filter (fun p : ℕ => (p : ℝ) ≤ X) ⊆ Finset.Ioo 1 (⌊X⌋₊ + 1) := by
    intro p hp
    obtain ⟨a1, a2⟩ := Finset.mem_filter.1 hp
    exact Finset.mem_Ioo.2 ⟨(hP p a1).one_lt, Nat.lt_succ_of_le (Nat.le_floor a2)⟩
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => by positivity).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum, nsmul_eq_mul]
  have c1 : ((Finset.Ioo 1 (⌊X⌋₊ + 1)).card : ℝ) ≤ X := by
    refine le_trans ?_ (Nat.floor_le hX)
    rw [Nat.card_Ioo]
    exact_mod_cast (by omega : ⌊X⌋₊ + 1 - 1 - 1 ≤ ⌊X⌋₊)
  have c2 : ∑ p ∈ Finset.Ioo 1 (⌊X⌋₊ + 1), ((p : ℝ) ^ 2)⁻¹ ≤ 1 := by
    have := sum_Ioo_inv_sq_le (α := ℝ) 1 (⌊X⌋₊ + 1)
    norm_num at this ⊢
    exact this
  exact add_le_add (mul_le_mul_of_nonneg_right c1 (by positivity))
    (mul_le_of_le_one_right (by positivity) c2)

end GlobalTheory.ConjLoss

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LossSumPrimes

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

noncomputable section

namespace GlobalTheory.ConjLossPrimes

theorem bound_one {D : D7} {L : SizeData₂ D} {c : ErrC}
    (hc : c.dig = 3) (P : ParameterChoice' D L) (hS : SizesAt L) (hx : 2 ≤ L.sc.x) (j : ℕ)
    (hj : j ∈ SizeData₂.lifts D) (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime ∧ (p : ℝ) ≤ L.sc.X'' D.R.n) :
    ∑ p ∈ Q, 2 * Real.log (p : ℝ) * |EatC L c j p| ≤ 2 * (9 * (1 / L.sc.eps + 1)) * L.B0 := by
  have hEg : ∀ p ∈ Q, 2 * Real.log (p : ℝ) * |EatC L c j p| = 2 * (Real.log (p : ℝ) * |(padicValNat p 1 : ℝ) +
    (if (p : ℝ) ≤ L.sc.X'' D.R.n then 3 * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * Real.logb p L.sc.a +
      (∑ τ : D.what₂.Tau, wj D j τ) / ((p : ℝ) ^ 2 - 1) else 0)|) := by
    intro p hp
    have e0 : padicValNat p 1 = 0 := by simp [_root_.Nat.padicValNat_def (n := 1)]
    rw [if_pos (hQ p hp).2, e0, Nat.cast_zero, zero_add]
    unfold EatC Formalism.MainNotions.G.Nm
    rw [hc, mul_assoc]
  rw [Finset.sum_congr rfl hEg]
  rw [← Finset.mul_sum, mul_assoc (2 : ℝ)]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  have hL := HCEntries.one_le_scL L
  have hb := HCEntries.one_le_b L
  have hk := HCEntries.one_le_k D
  have ht := HCEntries.one_le_letterBlockLength D
  have hmn := D.R.two_le_m
  have hkn := D.R.m_add_three_le_k
  have hmfn : D.R.m ≤ D.R.f := D.R.m_le_f
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast (by omega : 1 ≤ D.R.f)
  have hN : (1 : ℝ) ≤ D.R.N D.R.m := by
    exact_mod_cast (by unfold Ranks.N; omega : 1 ≤ D.R.N D.R.m)
  have hη0 := L.etaSz_pos.le
  have hNη : (D.R.N D.R.m : ℝ) ^ 2 ≤ L.etaSz := by
    have a1 := P.h0_ge.2.2.2.2.1
    have a2 : LevelStarExponents.h0 L ≤ L.etaSz := div_le_self hη0 hm
    have a3 : (D.R.N D.R.m : ℝ) ^ 2 ≤ (D.R.N D.R.m : ℝ) ^ 3 := pow_le_pow_right₀ hN (by norm_num)
    have a4 : 0 ≤ (D.R.N D.R.m : ℝ) ^ 3 := by positivity
    linarith
  have hx0 : 0 < L.sc.x := by linarith
  have ha : L.sc.a = L.sc.x * L.sc.b := rfl
  have ha1 : 1 ≤ L.sc.a := by rw [ha]; exact one_le_mul_of_one_le_of_one_le (by linarith) hb
  have hN2 : (1 : ℝ) ≤ (D.R.N D.R.m : ℝ) ^ 2 := one_le_pow₀ hN
  have hw : (D.R.N D.R.m : ℝ) ^ 2 * L.sc.x ≤ L.sc.w'' D.R.n := by
    have a1 := P.teta
    rw [le_div_iff₀ hx0] at a1
    exact (mul_le_mul_of_nonneg_right (hNη.trans (le_mul_of_one_le_left hη0 ht)) hx0.le).trans a1
  have hw1 : 1 ≤ L.sc.w'' D.R.n := (one_le_mul_of_one_le_of_one_le hN2 (by linarith)).trans hw
  have hX0 : 0 ≤ L.sc.X'' D.R.n := by unfold Scale.X''; positivity
  have hXa : L.sc.X'' D.R.n ≤ L.sc.a := div_le_self (by linarith) hw1
  have hXN : L.sc.X'' D.R.n * (D.R.N D.R.m : ℝ) ^ 2 ≤ L.sc.b := by
    unfold Scale.X''
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith), ha]
    have := mul_le_mul_of_nonneg_left hw (by linarith : 0 ≤ L.sc.b)
    linarith
  obtain ⟨hj1, hjm⟩ := Finset.mem_Icc.1 hj
  have hwj := HCEntries.wj_bounds hS hx j hj1 hjm
  have hW0 : 0 ≤ ∑ τ : D.what₂.Tau, wj D j τ := Finset.sum_nonneg fun τ _ => (hwj τ).1
  have hcard : Fintype.card D.what₂.Tau = D.R.f := D.what₂.card_Tau
  have hW : ∑ τ : D.what₂.Tau, wj D j τ ≤ D.R.f * (3 * L.sc.b) := by
    have := Finset.sum_le_card_nsmul Finset.univ (fun τ : D.what₂.Tau => wj D j τ) _ fun τ _ => (hwj τ).2
    rwa [Finset.card_univ, hcard, nsmul_eq_mul] at this
  have hla0 : 0 ≤ Real.log L.sc.a := Real.log_nonneg ha1
  have he := L.sc.eps_pos
  have hla : Real.log L.sc.a ≤ (1 / L.sc.eps + 1) * L.sc.L := by
    rw [ha, Real.log_mul hx0.ne' (by linarith)]
    have a1 : Real.log L.sc.b = L.sc.L := Real.log_exp _
    have a2 : Real.log L.sc.x ≤ L.sc.L / L.sc.eps := Real.log_le_rpow_div hx0.le he
    rw [a1]
    calc _ ≤ L.sc.L / L.sc.eps + L.sc.L := by linarith
      _ = _ := by ring
  have hB : L.B0 = D.R.f * D.R.m * L.sc.b * L.sc.L := rfl
  have hfb : 0 ≤ (D.R.f : ℝ) * L.sc.b := by positivity
  have hB1 : D.R.f * L.sc.b * L.sc.L ≤ L.B0 := by
    have : L.B0 = D.R.m * (D.R.f * L.sc.b * L.sc.L) := by rw [hB]; ring
    rw [this]
    exact le_mul_of_one_le_left (by positivity) hm
  have hfl : D.R.f * L.sc.b * Real.log L.sc.a ≤ (1 / L.sc.eps + 1) * L.B0 := by
    calc _ ≤ D.R.f * L.sc.b * ((1 / L.sc.eps + 1) * L.sc.L) := mul_le_mul_of_nonneg_left hla hfb
      _ = (1 / L.sc.eps + 1) * (D.R.f * L.sc.b * L.sc.L) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hB1 (by positivity)
  have t2 : L.sc.X'' D.R.n * (3 * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * Real.log L.sc.a) ≤
      3 * (D.R.f * L.sc.b * Real.log L.sc.a) := by
    calc _ = 3 * (D.R.f * (L.sc.X'' D.R.n * (D.R.N D.R.m : ℝ) ^ 2) * Real.log L.sc.a) := by ring
      _ ≤ _ := by gcongr
  have t3 : (∑ τ : D.what₂.Tau, wj D j τ) * Real.log L.sc.a ≤ 3 * (D.R.f * L.sc.b * Real.log L.sc.a) := by
    calc _ ≤ D.R.f * (3 * L.sc.b) * Real.log L.sc.a := mul_le_mul_of_nonneg_right hW hla0
      _ = _ := by ring
  have key := GlobalTheory.ConjLoss.sum_primes_le Q (fun p hp => (hQ p hp).1)
    1 (L.sc.X'' D.R.n) L.sc.a (3 * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2)
    (∑ τ : D.what₂.Tau, wj D j τ) hX0 hXa ha1 (by positivity) hW0
  refine key.trans ?_
  rw [Nat.cast_one, Real.log_one]
  linarith

theorem loss_sum_primes : ∀ {eps : ℝ} (Fm : FamP eps), 0 < eps → eps < 1 / 52 → ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x, ∀ j ∈ SizeData₂.lifts (Fm.D x i), ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ (Fm.L x i).sc.X'' (Fm.D x i).R.n) → ∑ p ∈ P, 2 * Real.log (p : ℝ) * |EatC (Fm.L x i) Fm.cX.err j p| ≤ C * (Fm.L x i).B0 := by
  intro eps Fm h0 h1
  refine ⟨2 * (9 * (1 / eps + 1)), 2, by positivity, ?_⟩
  intro x hx0 hx i j hj Q hQ
  have hsx : (Fm.L x i).sc.x = x := Fm.L_x x i hx
  have hse : (Fm.L x i).sc.eps = eps := Fm.L_eps x i
  have := bound_one (c := Fm.cX.err) Fm.fixed.2.2.2.2.2.1 (Fm.params x hx i) (Fm.sizes x hx i)
    (by rw [hsx]; exact hx0) j hj Q hQ
  rwa [hse] at this

end GlobalTheory.ConjLossPrimes

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPrimesLossLogSumAdmissible

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

namespace GlobalTheory.InertLossAdm

theorem inertPrimes_loss_log_sum_admissible : ∀ {eps : ℝ} (Fm : FamP eps), 0 < eps → eps < 1 / 52 → ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x, Formalism.MainNotions.WeightDegreeSizes.InertPrimeLossBound (Fm.D x i) (Fm.L x i) Fm.GK Fm.cX.err C := by
  intro eps Fm h0 h1
  obtain ⟨C1, x1, hC1, hc⟩ := GlobalTheory.ConjLossPrimes.loss_sum_primes Fm h0 h1
  obtain ⟨C2, x2, hC2, hi⟩ := GlobalTheory.OtherLoss.inertLoss_primeSum Fm h0 h1
  refine ⟨C1 + C2, max x1 x2, add_nonneg hC1 hC2, ?_⟩
  intro x hx hx1 i j hj P hP
  rw [← Finset.sum_filter_add_sum_filter_not P
    (fun p => G.IsResidueClassZero (Fm.D x i) p ∧ G.hP (Fm.D x i) p = 0)]
  have A := hc x (le_trans (le_max_left _ _) hx) hx1 i j hj (P.filter
    (fun p => G.IsResidueClassZero (Fm.D x i) p ∧ G.hP (Fm.D x i) p = 0))
    (fun p hp => by
      rw [Finset.mem_filter] at hp
      exact ⟨(hP p hp.1).1, (hP p hp.1).2.2⟩)
  have B := hi x (le_trans (le_max_right _ _) hx) hx1 i j hj (P.filter
    (fun p => ¬ (G.IsResidueClassZero (Fm.D x i) p ∧ G.hP (Fm.D x i) p = 0)))
    (fun p hp => by
      rw [Finset.mem_filter] at hp
      exact ⟨(hP p hp.1).1, (hP p hp.1).2.1, (hP p hp.1).2.2, hp.2⟩)
  have eA : ∑ p ∈ P.filter (fun p => G.IsResidueClassZero (Fm.D x i) p ∧ G.hP (Fm.D x i) p = 0),
      2 * Real.log (p : ℝ) * |Formalism.MainNotions.WeightDegreeSizes.EatCI (Fm.L x i) Fm.GK Fm.cX.err j p| =
      ∑ p ∈ P.filter (fun p => G.IsResidueClassZero (Fm.D x i) p ∧ G.hP (Fm.D x i) p = 0),
      2 * Real.log (p : ℝ) * |EatC (Fm.L x i) Fm.cX.err j p| := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_filter] at hp
    unfold Formalism.MainNotions.WeightDegreeSizes.EatCI
    rw [if_pos hp.2]
  have eB : ∑ p ∈ P.filter (fun p => ¬ (G.IsResidueClassZero (Fm.D x i) p ∧ G.hP (Fm.D x i) p = 0)),
      2 * Real.log (p : ℝ) * |Formalism.MainNotions.WeightDegreeSizes.EatCI (Fm.L x i) Fm.GK Fm.cX.err j p| =
      ∑ p ∈ P.filter (fun p => ¬ (G.IsResidueClassZero (Fm.D x i) p ∧ G.hP (Fm.D x i) p = 0)),
      2 * Real.log (p : ℝ) * |EatI (Fm.L x i) Fm.GK Fm.cX.err j p| := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_filter] at hp
    unfold Formalism.MainNotions.WeightDegreeSizes.EatCI
    rw [if_neg hp.2]
  rw [eA, eB, add_mul]
  exact add_le_add A B

end GlobalTheory.InertLossAdm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPrimesLossLogSumAdmissibleStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

theorem _root_.GlobalTheory.T.inertPrimeLossBound_eventually : ∀ {eps : ℝ} (Fm : FamP eps), 0 < eps → eps < 1 / 52 → ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x, Formalism.MainNotions.WeightDegreeSizes.InertPrimeLossBound (Fm.D x i) (Fm.L x i) Fm.GK Fm.cX.err C := by
  first | exact @GlobalTheory.InertLossAdm.inertPrimes_loss_log_sum_admissible | exact GlobalTheory.InertLossAdm.inertPrimes_loss_log_sum_admissible | (intros; apply GlobalTheory.InertLossAdm.inertPrimes_loss_log_sum_admissible <;> assumption)
end
end
