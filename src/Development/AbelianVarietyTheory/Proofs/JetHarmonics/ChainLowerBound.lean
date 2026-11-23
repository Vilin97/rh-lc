module

public import Development.AbelianVarietyTheory.Definitions.Jets.Imports
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.InvSqLeWignerCoeffSqLowering
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
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.InvSqLeWignerCoeffSqLoweringStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.inv_sq_le_wignerCoeffSqLowering : ∀ (n : ℕ) (L : Fin (n+1) → ℤ) (M : Fin n → ℤ) (l : Fin (n+1)) (D : ℝ), StrictAnti L → (∀ j : Fin n, L j.succ < M j ∧ M j ≤ L j.castSucc) → (∀ j, M j ≠ L l) → 1 ≤ D → ((L 0 : ℝ) - L l ≤ D) → ((L l : ℝ) - L (Fin.last n) ≤ D) → (D ^ 2)⁻¹ ≤ GlobalTheory.WigSh.wM L M l := by
  first | exact @GlobalTheory.WigSh.inv_sq_le_wM | exact GlobalTheory.WigSh.inv_sq_le_wM | (intros; apply GlobalTheory.WigSh.inv_sq_le_wM <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Definitions.Jets.FactorNonneg

section

@[expose] public section

open Finset

noncomputable section

namespace GlobalTheory.WigSh.Model

def Box {n : ℕ} (L : Fin (n + 1) → ℤ) (M : Fin n → ℤ) : Prop :=
  ∀ j : Fin n, L j.succ < M j ∧ M j ≤ L j.castSucc

theorem Box.strictAnti {n : ℕ} {L : Fin (n + 1) → ℤ} {M : Fin n → ℤ} (h : Box L M) :
    StrictAnti L := by
  rw [Fin.strictAnti_iff_succ_lt]
  intro j
  exact lt_of_lt_of_le (h j).1 (h j).2

theorem prod_erase_eq {n : ℕ} (f : Fin (n + 1) → ℝ) (l : Fin (n + 1)) :
    ∏ j ∈ univ.erase l, f j = ∏ j : Fin n, f (l.succAbove j) := by
  rw [← Finset.compl_singleton, ← Fin.image_succAbove_univ,
    Finset.prod_image (fun a _ b _ hab => Fin.succAbove_right_injective hab)]

theorem factor_nonneg {n : ℕ} {L : Fin (n + 1) → ℤ} {M : Fin n → ℤ} (h : Box L M)
    (l : Fin (n + 1)) (j : Fin n) (e : ℤ) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    0 ≤ ((M j : ℝ) - e - L l) / ((L (l.succAbove j) : ℝ) - L l) := by
  have hA := h.strictAnti
  have he0' : (0 : ℝ) ≤ e := by exact_mod_cast he0
  have he1' : (e : ℝ) ≤ 1 := by exact_mod_cast he1
  rcases lt_or_ge (Fin.castSucc j) l with hj | hj
  · rw [Fin.succAbove_of_castSucc_lt l j hj]
    have h1 : L l ≤ L j.succ := hA.antitone (Fin.castSucc_lt_iff_succ_le.mp hj)
    have h2 : L l < L j.castSucc := hA hj
    have h3 := (h j).1
    have h4 : (L l : ℝ) + 1 ≤ M j := by exact_mod_cast (by omega : L l + 1 ≤ M j)
    have h5 : (L l : ℝ) < L j.castSucc := by exact_mod_cast h2
    apply div_nonneg <;> linarith
  · rw [Fin.succAbove_of_le_castSucc l j hj]
    have h1 : L j.castSucc ≤ L l := hA.antitone hj
    have h2 : L j.succ < L l := hA (lt_of_le_of_lt hj Fin.castSucc_lt_succ)
    have h4 : (M j : ℝ) ≤ L l := by exact_mod_cast le_trans (h j).2 h1
    have h5 : (L j.succ : ℝ) < L l := by exact_mod_cast h2
    apply div_nonneg_of_nonpos <;> linarith

theorem placeWeight_nonneg {n : ℕ} {L : Fin (n + 1) → ℤ} {M : Fin n → ℤ} (h : Box L M)
    (l : Fin (n + 1)) : 0 ≤ wP L M l := by
  unfold GlobalTheory.WigSh.wP
  rw [prod_erase_eq, ← Finset.prod_div_distrib]
  refine Finset.prod_nonneg fun j _ => ?_
  simpa using factor_nonneg h l j 1 zero_le_one le_rfl

end GlobalTheory.WigSh.Model
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.InvSqLeWignerCoeffSqRaising

section

@[expose] public section

open Finset

noncomputable section

namespace GlobalTheory.WigSh

theorem prod_other_neighbour_raise {n : ℕ} (d : Fin (n + 1) → ℝ) (l : Fin (n + 1))
    (hd : ∀ i, 0 < d i) (hl : d l = 1) :
    (∏ j : Fin n, d (if j.castSucc < l then j.succ else j.castSucc)) * (d 0 * d (Fin.last n))
      = ∏ j : Fin n, d (l.succAbove j) := by
  have hP : ∏ i, d i = ∏ j : Fin n, d (l.succAbove j) := by
    rw [Fin.prod_univ_succAbove d l, hl, one_mul]
  have h1 := Fin.prod_univ_succ d
  have h2 := Fin.prod_univ_castSucc d
  have h3 : (∏ j : Fin n, d (if j.castSucc < l then j.succ else j.castSucc))
      * ∏ j : Fin n, d (l.succAbove j) = (∏ j : Fin n, d j.succ) * ∏ j : Fin n, d j.castSucc := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    unfold Fin.succAbove
    split_ifs
    · rfl
    · exact mul_comm _ _
  have hpos : 0 < ∏ j : Fin n, d (l.succAbove j) := Finset.prod_pos fun j _ => hd _
  apply mul_right_cancel₀ hpos.ne'
  calc _ = ((∏ j : Fin n, d (if j.castSucc < l then j.succ else j.castSucc))
      * ∏ j : Fin n, d (l.succAbove j)) * (d 0 * d (Fin.last n)) := by ring
    _ = (d 0 * ∏ j : Fin n, d j.succ) * ((∏ j : Fin n, d j.castSucc) * d (Fin.last n)) := by
      rw [h3]; ring
    _ = _ := by rw [← h1, ← h2, hP]

theorem inv_sq_le_wP (n : ℕ) (L : Fin (n+1) → ℤ) (M : Fin n → ℤ) (l : Fin (n+1)) (D : ℝ)
    (hL : StrictAnti L) (hM : ∀ j : Fin n, L j.succ < M j ∧ M j ≤ L j.castSucc)
    (hne : ∀ j, M j ≠ L l + 1) (hD : 1 ≤ D) (h0 : (L 0 : ℝ) - L l ≤ D)
    (hn : (L l : ℝ) - L (Fin.last n) ≤ D) : (D ^ 2)⁻¹ ≤ wP L M l := by
  set e : Fin (n + 1) → ℤ := fun i => max |L i - L l| 1 with he
  set d : Fin (n + 1) → ℝ := fun i => (e i : ℝ) with hd
  have hdpos : ∀ i, 0 < d i := fun i => by
    have : 0 < e i := lt_of_lt_of_le one_pos (le_max_right _ _)
    simp only [hd]; exact_mod_cast this
  have hdl : d l = 1 := by simp [hd, he]
  have key := prod_other_neighbour_raise d l hdpos hdl
  have hd0 : d 0 ≤ D := by
    have a : L l ≤ L 0 := hL.antitone (Fin.zero_le _)
    have a' : (L l : ℝ) ≤ L 0 := by exact_mod_cast a
    simp only [hd, he]
    push_cast
    exact max_le (by rw [abs_of_nonneg (by linarith)]; exact h0) hD
  have hdn : d (Fin.last n) ≤ D := by
    have a : L (Fin.last n) ≤ L l := hL.antitone (Fin.le_last _)
    have a' : (L (Fin.last n) : ℝ) ≤ L l := by exact_mod_cast a
    simp only [hd, he]
    push_cast
    exact max_le (by rw [abs_of_nonpos (by linarith)]; linarith) hD
  have hden : ∏ j : Fin n, |(L (l.succAbove j) : ℝ) - L l| = ∏ j : Fin n, d (l.succAbove j) := by
    refine Finset.prod_congr rfl fun j _ => ?_
    have a : L (l.succAbove j) ≠ L l := fun h => Fin.succAbove_ne l j (hL.injective h)
    have b : 1 ≤ |L (l.succAbove j) - L l| := Int.one_le_abs (sub_ne_zero.2 a)
    simp only [hd, he, max_eq_left b]
    push_cast
    rfl
  have hnum : (∏ j : Fin n, d (if j.castSucc < l then j.succ else j.castSucc))
      ≤ ∏ j : Fin n, |(M j : ℝ) - 1 - L l| := by
    refine Finset.prod_le_prod₀ (fun j _ => (hdpos _).le) fun j _ => ?_
    obtain ⟨h1, h2⟩ := hM j
    have h3 := hne j
    have : e (if j.castSucc < l then j.succ else j.castSucc) ≤ |M j - 1 - L l| := by
      split_ifs with hl
      · have a2 : L l ≤ L j.succ := hL.antitone (Fin.castSucc_lt_iff_succ_le.1 hl)
        simp only [he]
        rw [abs_of_nonneg (by omega), abs_of_nonneg (by omega)]
        omega
      · have a2 : L j.castSucc ≤ L l := hL.antitone (not_lt.1 hl)
        simp only [he]
        rw [abs_of_nonpos (by omega), abs_of_nonpos (by omega)]
        omega
    simp only [hd]
    exact_mod_cast this
  rw [← abs_of_nonneg (Model.placeWeight_nonneg hM l)]
  unfold wP
  rw [Model.prod_erase_eq, abs_div, Finset.abs_prod, Finset.abs_prod, hden, ← key]
  have hQ : 0 < ∏ j : Fin n, d (if j.castSucc < l then j.succ else j.castSucc) :=
    Finset.prod_pos fun j _ => hdpos _
  have hm : d 0 * d (Fin.last n) ≤ D ^ 2 := by
    rw [sq]; exact mul_le_mul hd0 hdn (hdpos _).le (by linarith)
  have hmpos : 0 < d 0 * d (Fin.last n) := mul_pos (hdpos _) (hdpos _)
  calc (D ^ 2)⁻¹ ≤ (d 0 * d (Fin.last n))⁻¹ := inv_anti₀ hmpos hm
    _ = (∏ j : Fin n, d (if j.castSucc < l then j.succ else j.castSucc)) /
        ((∏ j : Fin n, d (if j.castSucc < l then j.succ else j.castSucc))
          * (d 0 * d (Fin.last n))) := by
      rw [div_mul_eq_div_div, div_self hQ.ne', one_div]
    _ ≤ _ := div_le_div_of_nonneg_right hnum (mul_pos hQ hmpos).le

end GlobalTheory.WigSh
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.InvSqLeWignerCoeffSqRaisingStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.inv_sq_le_wignerCoeffSqRaising : ∀ (n : ℕ) (L : Fin (n+1) → ℤ) (M : Fin n → ℤ) (l : Fin (n+1)) (D : ℝ), StrictAnti L → (∀ j : Fin n, L j.succ < M j ∧ M j ≤ L j.castSucc) → (∀ j, M j ≠ L l + 1) → 1 ≤ D → ((L 0 : ℝ) - L l ≤ D) → ((L l : ℝ) - L (Fin.last n) ≤ D) → (D ^ 2)⁻¹ ≤ GlobalTheory.WigSh.wP L M l := by
  first | exact @GlobalTheory.WigSh.inv_sq_le_wP | exact GlobalTheory.WigSh.inv_sq_le_wP | (intros; apply GlobalTheory.WigSh.inv_sq_le_wP <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.ChainLowerBound

section

@[expose] public section

open Finset

namespace GlobalTheory.WigSh

private theorem strictAnti_of_box {n : ℕ} {L : Fin (n+1) → ℤ} {M : Fin n → ℤ}
    (h : ∀ j : Fin n, L j.succ < M j ∧ M j ≤ L j.castSucc) : StrictAnti L :=
  Fin.strictAnti_iff_succ_lt.2 fun j => (h j).1.trans_le (h j).2

private theorem chain_prod_le {n₀ : ℕ} {D : ℝ} (hD : 1 ≤ D) (f : ℕ → ℝ)
    (hf : ∀ j < n₀, (D ^ 2)⁻¹ ≤ f j) : (D ^ (2 * n₀))⁻¹ ≤ ∏ j ∈ Finset.range n₀, f j := by
  have h1 : (D ^ (2 * n₀))⁻¹ = ∏ _j ∈ Finset.range n₀, (D ^ 2)⁻¹ := by
    rw [Finset.prod_const, Finset.card_range, pow_mul, inv_pow]
  rw [h1]
  exact Finset.prod_le_prod₀ (fun _ _ => by positivity)
    (fun j hj => hf j (Finset.mem_range.1 hj))

theorem chain_lower_bound : ∀ (n : ℕ) (L : Fin (n+1) → ℤ) (M : Fin n → ℤ) (i : Fin n) (n₀ : ℕ) (b : ℝ), StrictAnti L → (∀ j : Fin n, L j.succ < M j ∧ M j ≤ L j.castSucc) → L i.succ + 2 * (n₀ : ℤ) + 1 ≤ L i.castSucc → 1 ≤ b → (n₀ : ℝ) ≤ b → ((L 0 : ℝ) - L (Fin.last n) ≤ 2 * b) → (((3 * b) ^ (2 * n₀))⁻¹ ≤ ∏ j ∈ Finset.range n₀, GlobalTheory.WigSh.wP (Function.update L i.succ (L i.succ + (j : ℤ))) M i.succ) ∨ (((3 * b) ^ (2 * n₀))⁻¹ ≤ ∏ j ∈ Finset.range n₀, GlobalTheory.WigSh.wM (Function.update L i.castSucc (L i.castSucc - (j : ℤ))) M i.castSucc) := by
  intro n L M i n₀ b hL hbox hgap hb hn hspan
  have hD : (1 : ℝ) ≤ 3 * b := by linarith
  have h0 : ∀ k, (L k : ℝ) ≤ L 0 := fun k => by
    exact_mod_cast hL.antitone (Fin.zero_le k)
  have hl : ∀ k, (L (Fin.last n) : ℝ) ≤ L k := fun k => by
    exact_mod_cast hL.antitone (Fin.le_last k)
  have hlt : ∀ k : Fin n, k < i → L i.castSucc < M k := fun k hk =>
    lt_of_le_of_lt (hL.antitone (by
      rw [Fin.le_def]; simp only [Fin.val_succ, Fin.val_castSucc]; exact hk)) (hbox k).1
  have hgt : ∀ k : Fin n, i < k → M k ≤ L i.succ := fun k hk =>
    le_trans (hbox k).2 (hL.antitone (by
      rw [Fin.le_def]; simp only [Fin.val_succ, Fin.val_castSucc]; exact hk))
  by_cases hc : L i.succ + n₀ + 1 ≤ M i
  · left
    refine chain_prod_le hD _ fun j hj => ?_
    have hjZ : (j : ℤ) < n₀ := by exact_mod_cast hj
    have hjR : (j : ℝ) ≤ b := le_trans (by exact_mod_cast hj.le) hn
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hbox' : ∀ k : Fin n, Function.update L i.succ (L i.succ + (j : ℤ)) k.succ < M k ∧
        M k ≤ Function.update L i.succ (L i.succ + (j : ℤ)) k.castSucc := by
      intro k
      constructor
      · by_cases hk : k = i
        · subst hk
          rw [Function.update_self]; omega
        · rw [Function.update_of_ne (fun h => hk (Fin.succ_injective _ h))]
          exact (hbox k).1
      · by_cases hk : k.castSucc = i.succ
        · have := (hbox k).2
          rw [hk] at this ⊢
          rw [Function.update_self]; omega
        · rw [Function.update_of_ne hk]
          exact (hbox k).2
    refine GlobalTheory.T.inv_sq_le_wignerCoeffSqRaising n _ M i.succ (3 * b) (strictAnti_of_box hbox') hbox' ?_ hD ?_ ?_
    · intro k
      rw [Function.update_self]
      rcases lt_trichotomy k i with hk | hk | hk
      · have := hlt k hk; omega
      · subst hk; omega
      · have := hgt k hk; omega
    · rw [Function.update_self, Function.update_of_ne (Fin.succ_ne_zero i).symm]
      push_cast
      have := hl i.succ
      linarith
    · rw [Function.update_self]
      by_cases hk : Fin.last n = i.succ
      · rw [hk, Function.update_self]; linarith
      · rw [Function.update_of_ne hk]
        push_cast
        have := h0 i.succ
        linarith
  · right
    refine chain_prod_le hD _ fun j hj => ?_
    have hjZ : (j : ℤ) < n₀ := by exact_mod_cast hj
    have hjR : (j : ℝ) ≤ b := le_trans (by exact_mod_cast hj.le) hn
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hbox' : ∀ k : Fin n,
        Function.update L i.castSucc (L i.castSucc - (j : ℤ)) k.succ < M k ∧
        M k ≤ Function.update L i.castSucc (L i.castSucc - (j : ℤ)) k.castSucc := by
      intro k
      constructor
      · by_cases hk : k.succ = i.castSucc
        · have hki : k < i := by
            have := congrArg Fin.val hk
            simp only [Fin.val_succ, Fin.val_castSucc] at this
            rw [Fin.lt_def]; omega
          have := hlt k hki
          rw [hk, Function.update_self]; omega
        · rw [Function.update_of_ne hk]
          exact (hbox k).1
      · by_cases hk : k = i
        · subst hk
          rw [Function.update_self]; omega
        · rw [Function.update_of_ne (fun h => hk (Fin.castSucc_injective _ h))]
          exact (hbox k).2
    refine GlobalTheory.T.inv_sq_le_wignerCoeffSqLowering n _ M i.castSucc (3 * b) (strictAnti_of_box hbox') hbox' ?_ hD ?_ ?_
    · intro k
      rw [Function.update_self]
      rcases lt_trichotomy k i with hk | hk | hk
      · have := hlt k hk; omega
      · subst hk; omega
      · have := hgt k hk; omega
    · rw [Function.update_self]
      by_cases hk : 0 = i.castSucc
      · rw [hk, Function.update_self]; linarith
      · rw [Function.update_of_ne hk]
        push_cast
        have := hl i.castSucc
        linarith
    · rw [Function.update_self, Function.update_of_ne (Fin.castSucc_lt_last i).ne']
      push_cast
      have := h0 i.castSucc
      linarith

end GlobalTheory.WigSh
end
end
