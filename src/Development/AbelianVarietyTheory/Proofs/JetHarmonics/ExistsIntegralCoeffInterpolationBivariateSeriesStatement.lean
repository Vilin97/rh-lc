module

public import Development.AbelianVarietyTheory.Definitions.Jets.PowerSeriesHasSumAt
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Analysis.Normed.Field.Basic
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.CoeffProdXSubCNormLe

section

@[expose] public section

namespace GlobalTheory.RootProductCoeffBound

open Polynomial

theorem coeff_prod_X_sub_C_norm_le {K : Type} [NormedField K] [IsUltrametricDist K]
    (θ : ℝ) (h0 : (0 : ℝ) ≤ θ) (h1 : θ ≤ (1 : ℝ)) (S : Finset K)
    (hS : ∀ x ∈ S, ‖x‖ ≤ θ) (a : ℕ) :
    ‖AddMonoidAlgebra.coeff (∏ x ∈ S, (Polynomial.X - (Polynomial.C : K → Polynomial K) x)) a‖
      ≤ θ ^ (Finset.card S - a) := by
  classical
  induction S using Finset.induction_on generalizing a with
  | empty =>
    rcases a with _ | k
    · simp
    · simp [Polynomial.coeff_one]
  | insert y S hy ih =>
    have ihS : ∀ b, ‖(∏ x ∈ S, (X - C x)).coeff b‖ ≤ θ ^ (S.card - b) :=
      fun b => ih (fun x hx => hS x (Finset.mem_insert_of_mem hx)) b
    have hyθ : ‖y‖ ≤ θ := hS y (Finset.mem_insert_self y S)
    rw [Finset.prod_insert hy, Finset.card_insert_of_notMem hy]
    set P := ∏ x ∈ S, (X - C x) with hP
    rw [sub_mul, coeff_sub, coeff_C_mul]
    have hyb : ∀ b, ‖y * P.coeff b‖ ≤ θ ^ (S.card + 1 - (b + 1)) * θ := by
      intro b
      rw [norm_mul, mul_comm]
      refine mul_le_mul ?_ hyθ (norm_nonneg _) (pow_nonneg h0 _)
      simpa using ihS b
    rcases a with _ | k
    · rw [coeff_X_mul_zero, zero_sub, norm_neg]
      calc ‖y * P.coeff 0‖ ≤ θ ^ (S.card + 1 - (0 + 1)) * θ := hyb 0
        _ = θ ^ (S.card + 1 - 0) := by simp [pow_succ]
    · rw [coeff_X_mul]
      rw [sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · simpa using ihS k
      · rw [norm_neg]
        calc ‖y * P.coeff (k + 1)‖ ≤ θ ^ (S.card - (k + 1)) * θ := by
              have := hyb (k + 1); simpa using this
          _ = θ ^ (S.card - (k + 1) + 1) := by rw [pow_succ]
          _ ≤ θ ^ (S.card + 1 - (k + 1)) := by
              apply pow_le_pow_of_le_one h0 h1
              omega

theorem main : ∀ {K : Type} [inst : NormedField K] [IsUltrametricDist K] (θ : ℝ), (0 : ℝ) ≤ θ → θ ≤ (1 : ℝ) → ∀ (S : Finset K), (∀ x ∈ S, ‖x‖ ≤ θ) → ∀ (a : ℕ), ‖AddMonoidAlgebra.coeff (∏ x ∈ S, (Polynomial.X - (Polynomial.C : K → Polynomial K) x)) a‖ ≤ θ ^ (Finset.card S - a) :=
  fun θ h0 h1 S hS a => coeff_prod_X_sub_C_norm_le θ h0 h1 S hS a

end GlobalTheory.RootProductCoeffBound
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralCoeffInterpolationBivariateSeries

section

@[expose] public section

open GlobalTheory.ConvSer Polynomial

namespace GlobalTheory.ConvSer

theorem norm_coeff_prod_X_sub_C_le_pow {K : Type} [NormedField K] [IsUltrametricDist K]
    (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (S : Finset K) (hS : ∀ x ∈ S, ‖x‖ ≤ θ) (a : ℕ) :
    ‖(∏ x ∈ S, (X - C x) : K[X]).coeff a‖ ≤ θ ^ (S.card - a) := by
  first
  | exact @_root_.GlobalTheory.RootProductCoeffBound.main
  | exact _root_.GlobalTheory.RootProductCoeffBound.main
  | (apply _root_.GlobalTheory.RootProductCoeffBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.RootProductCoeffBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RootProductCoeffBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RootProductCoeffBound.main ..)

theorem exists_pow_eq_interpolation {K : Type} [NormedField K] [IsUltrametricDist K]
    (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (S : Finset K) (hS : ∀ x ∈ S, ‖x‖ ≤ θ)
    (hN : 0 < S.card) (k : ℕ) :
    ∃ Q : K[X], (∀ a, S.card ≤ a → Q.coeff a = 0) ∧ (∀ a, ‖Q.coeff a‖ ≤ θ ^ (k - a)) ∧
      ∀ x ∈ S, Q.eval x = x ^ k := by
  induction k with
  | zero =>
    refine ⟨1, fun a ha => ?_, fun a => ?_, by simp⟩
    · rw [coeff_one, if_neg (by omega)]
    · rw [coeff_one]; split_ifs <;> simp
  | succ k ih =>
    obtain ⟨Q, hQ0, hQ1, hQ2⟩ := ih
    obtain ⟨n, hn⟩ : ∃ n, S.card = n + 1 := ⟨S.card - 1, by omega⟩
    set P : K[X] := ∏ x ∈ S, (X - C x) with hP
    have hPm : P.Monic := monic_prod_of_monic _ _ (fun x _ => monic_X_sub_C x)
    have hPd : P.natDegree = n + 1 := by
      rw [hP, natDegree_prod_of_monic _ _ (fun x _ => monic_X_sub_C x)]
      simp [hn]
    refine ⟨X * Q - C (Q.coeff n) * P, fun a ha => ?_, fun a => ?_, fun x hx => ?_⟩
    · obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
      rw [coeff_sub, coeff_X_mul, coeff_C_mul]
      rcases (show n = b ∨ n < b by omega) with rfl | h
      · have : P.coeff (n + 1) = 1 := by rw [← hPd]; exact hPm.coeff_natDegree
        rw [this]; simp
      · rw [hQ0 b (by omega), coeff_eq_zero_of_natDegree_lt (p := P) (by omega)]; simp
    · by_cases ha : n + 1 < a
      · obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
        rw [coeff_sub, coeff_X_mul, coeff_C_mul, hQ0 b (by omega),
          coeff_eq_zero_of_natDegree_lt (p := P) (by omega)]
        simp; positivity
      rw [coeff_sub, coeff_C_mul, sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · cases a with
        | zero => simp; positivity
        | succ a =>
          rw [coeff_X_mul]
          simpa using hQ1 a
      · rw [norm_neg, norm_mul]
        calc _ ≤ θ ^ (k - n) * θ ^ (S.card - a) :=
              mul_le_mul (hQ1 n) (norm_coeff_prod_X_sub_C_le_pow θ h0 h1 S hS a) (norm_nonneg _)
                (by positivity)
          _ = θ ^ (k - n + (S.card - a)) := by ring
          _ ≤ _ := pow_le_pow_of_le_one h0 h1 (by omega)
    · have : P.eval x = 0 := by
        rw [hP, eval_prod]
        exact Finset.prod_eq_zero hx (by simp)
      simp [this, hQ2 x hx, pow_succ']

theorem exists_integral_interpolation_two :
    ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (S : Finset K)
      (H : MvPowerSeries (Fin 2) K), (∀ x ∈ S, ‖x‖ < 1) → Intg H →
      ∃ c : Fin S.card → Fin S.card → K, (∀ a b, ‖c a b‖ ≤ 1) ∧ ∀ x ∈ S, ∀ y ∈ S,
        ev H ![x, y] = ∑ a, ∑ b, c a b * x ^ (a : ℕ) * y ^ (b : ℕ) := by
  intro K _ _ _ S H hS hH
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun _ _ => 0, by simp, by simp⟩
  obtain ⟨x0, hx0, hmax⟩ := S.exists_max_image (fun x => ‖x‖) hne
  set θ := ‖x0‖
  have h0 : 0 ≤ θ := norm_nonneg _
  have h1 : θ < 1 := hS x0 hx0
  choose Q hQ0 hQ1 hQ2 using
    exists_pow_eq_interpolation θ h0 h1.le S hmax hne.card_pos
  have hev : ∀ k, ∀ x ∈ S, x ^ k = ∑ a : Fin S.card, (Q k).coeff a * x ^ (a : ℕ) := by
    intro k x hx
    rw [← hQ2 k x hx, Fin.sum_univ_eq_sum_range (fun a => (Q k).coeff a * x ^ a)]
    apply eval_eq_sum_range'
    have := hne.card_pos
    have h : (Q k).natDegree ≤ S.card - 1 :=
      natDegree_le_iff_coeff_eq_zero.2 (fun a ha => hQ0 k a (by omega))
    omega
  have hg : ∀ a : ℕ, Summable (fun k : ℕ => θ ^ (k - a)) := by
    intro a
    rw [← summable_nat_add_iff a]
    simpa using summable_geometric_of_lt_one h0 h1
  let T : ℕ → ℕ → (Fin 2 →₀ ℕ) → K := fun a b ν =>
    MvPowerSeries.coeff ν H * (Q (ν 0)).coeff a * (Q (ν 1)).coeff b
  have hT : ∀ a b ν, ‖T a b ν‖ ≤ θ ^ (ν 0 - a) * θ ^ (ν 1 - b) := by
    intro a b ν
    simp only [T, norm_mul]
    refine mul_le_mul ?_ (hQ1 _ _) (norm_nonneg _) (by positivity)
    exact (mul_le_of_le_one_left (norm_nonneg _) (hH ν)).trans (hQ1 _ _)
  have hsum : ∀ a b, Summable (T a b) := by
    intro a b
    refine Summable.of_norm_bounded ?_ (hT a b)
    have h : Summable (fun p : ℕ × ℕ => θ ^ (p.1 - a) * θ ^ (p.2 - b)) :=
      Summable.mul_of_nonneg (f := fun k : ℕ => θ ^ (k - a)) (g := fun k : ℕ => θ ^ (k - b))
        (hg a) (hg b) (fun _ => pow_nonneg h0 _) (fun _ => pow_nonneg h0 _)
    have hinj : Function.Injective (fun ν : Fin 2 →₀ ℕ => (ν 0, ν 1)) := by
      intro ν μ h
      simp only [Prod.mk.injEq] at h
      ext i
      fin_cases i
      · exact h.1
      · exact h.2
    have h' := h.comp_injective hinj
    simpa only [Function.comp_def] using h'
  refine ⟨fun a b => ∑' ν, T a b ν, fun a b => ?_, fun x hx y hy => ?_⟩
  · refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg zero_le_one (fun ν => ?_)
    exact (hT a b ν).trans (mul_le_one₀ (pow_le_one₀ h0 h1.le) (by positivity)
      (pow_le_one₀ h0 h1.le))
  · have h : HasSum (fun ν => ∑ a : Fin S.card, ∑ b : Fin S.card,
        T a b ν * x ^ (a : ℕ) * y ^ (b : ℕ))
        (∑ a : Fin S.card, ∑ b : Fin S.card, (∑' ν, T a b ν) * x ^ (a : ℕ) * y ^ (b : ℕ)) :=
      hasSum_sum fun a _ => hasSum_sum fun b _ =>
        ((hsum a b).hasSum.mul_right _).mul_right _
    rw [← h.tsum_eq, ev]
    congr 1
    funext ν
    rw [Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hev (ν 0) x hx, hev (ν 1) y hy, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [T]
    ring

end GlobalTheory.ConvSer
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralCoeffInterpolationBivariateSeriesStatement

section

@[expose] public section

open GlobalTheory.ConvSer

theorem _root_.GlobalTheory.T.exists_integral_coeff_interpolation_bivariate_series : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (S : Finset K) (H : MvPowerSeries (Fin 2) K), (∀ x ∈ S, ‖x‖ < 1) → Intg H → ∃ c : Fin S.card → Fin S.card → K, (∀ a b, ‖c a b‖ ≤ 1) ∧ ∀ x ∈ S, ∀ y ∈ S, ev H ![x, y] = ∑ a, ∑ b, c a b * x ^ (a : ℕ) * y ^ (b : ℕ) := by
  first | exact @GlobalTheory.ConvSer.exists_integral_interpolation_two | exact GlobalTheory.ConvSer.exists_integral_interpolation_two | (intros; apply GlobalTheory.ConvSer.exists_integral_interpolation_two <;> assumption)
end
end
