module

public import Development.AutomorphicArithmetic.ThickFrames.MarkedLow
public import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting
public import Development.AutomorphicArithmetic.ThickFrames.NotGoodLe
public import Mathlib.Basic.Real.Basic
public import Mathlib.GroupTheory.Index
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.ThickFrames.MarkedLow
import Formalism.SubspaceCounting.Statement
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Development.AutomorphicArithmetic.ThickFrames.orbitSum
public import Development.AutomorphicArithmetic.ThickFrames.orbitTerms
public import Development.AutomorphicArithmetic.ThickFrames.select

-- Source module: Development.AutomorphicArithmetic.ThickFrames.SharesOfCounts

section

@[expose] public section

open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0
open Classical

theorem UpperTheory.BernoulliSumsFrobeniusOrbits.shares_of_counts :
    ∀ (A : Type) [Fintype A] [DecidableEq A] [AddCommGroup A] (A0 : AddSubgroup A) (T : Finset A) (δ η D : ℝ),
      0 < δ → η ≤ 1 → 0 ≤ D → 4 * A0.index * D ≤ η * (δ * Nat.card A0) →
      (∀ γ : A, |((T.filter fun t => t - γ ∈ A0).card : ℝ) - (if γ ∈ A0 then δ else 3 / 4 * δ) * Nat.card A0| ≤ D) →
      δ * Fintype.card A / 2 ≤ (T.card : ℝ) ∧ (T.card : ℝ) ≤ 2 * δ * Fintype.card A ∧
        ∀ γ : A, |((T.filter fun t => t - γ ∈ A0).card : ℝ) -
          (if γ ∈ A0 then 4 else 3) / (3 * (A0.index : ℝ) + 1) * (T.card : ℝ)| ≤ η * (T.card : ℝ) := by
  intro A _ _ _ A0 T δ η D hδ hη hD hDη hc
  set m : ℕ := A0.index with hm_def
  set n : ℕ := Nat.card A0 with hn_def
  have hm : (1:ℝ) ≤ m := by
    have h0 : A0.index ≠ 0 := AddSubgroup.index_ne_zero_of_finite
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
  have hn : (1:ℝ) ≤ n := by
    have h0 : 0 < Nat.card A0 := Nat.card_pos
    exact_mod_cast h0
  have hA : (Fintype.card A : ℝ) = m * n := by
    have h1 : n * m = Fintype.card A := by
      rw [hn_def, hm_def, A0.card_mul_index, Nat.card_eq_fintype_card]
    rw [← h1]
    push_cast
    ring
  have hcardA0 : (Finset.univ.filter fun x : A => x ∈ A0).card = n := by
    rw [hn_def, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hsumN : ∑ γ : A, (T.filter fun t => t - γ ∈ A0).card = T.card * n := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    have inner : ∀ t : A, (∑ γ : A, if t - γ ∈ A0 then 1 else 0) = n := by
      intro t
      have h2 := Equiv.sum_comp (Equiv.subLeft t) (fun x => if x ∈ A0 then (1:ℕ) else 0)
      simp only [Equiv.subLeft_apply] at h2
      rw [h2, ← Finset.card_filter]
      exact hcardA0
    rw [Finset.sum_congr rfl (fun t _ => inner t), Finset.sum_const, smul_eq_mul]
  have hsum : (∑ γ : A, ((T.filter fun t => t - γ ∈ A0).card : ℝ)) = n * T.card := by
    have h3 := congrArg (Nat.cast : ℕ → ℝ) hsumN
    push_cast at h3
    rw [h3]
    ring
  have hf : (∑ γ : A, (if γ ∈ A0 then δ else 3 / 4 * δ) * (n:ℝ)) = (3 * m + 1) / 4 * δ * n * n := by
    have hpt : ∀ γ : A, (if γ ∈ A0 then δ else 3 / 4 * δ) * (n:ℝ)
        = 3 / 4 * δ * n + (if γ ∈ A0 then δ / 4 * n else 0) := by
      intro γ
      split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun γ _ => hpt γ), Finset.sum_add_distrib, ← Finset.sum_filter,
      Finset.sum_const, Finset.sum_const, hcardA0, Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul, hA]
    ring
  have hdiff : |(n:ℝ) * T.card - (3 * m + 1) / 4 * δ * n * n| ≤ m * n * D := by
    rw [← hsum, ← hf, ← Finset.sum_sub_distrib]
    calc _ ≤ ∑ γ : A, |((T.filter fun t => t - γ ∈ A0).card : ℝ) - (if γ ∈ A0 then δ else 3 / 4 * δ) * n| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ γ : A, D := Finset.sum_le_sum fun γ _ => hc γ
      _ = m * n * D := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hA]
  have hn0 : (0:ℝ) < n := by linarith
  have hT : |(T.card : ℝ) - (3 * m + 1) / 4 * δ * n| ≤ m * D := by
    have he : (n:ℝ) * T.card - (3 * m + 1) / 4 * δ * n * n = n * ((T.card : ℝ) - (3 * m + 1) / 4 * δ * n) := by ring
    rw [he, abs_mul, abs_of_pos hn0] at hdiff
    have h4 : (n:ℝ) * |(T.card : ℝ) - (3 * m + 1) / 4 * δ * n| ≤ n * (m * D) := by linarith
    exact le_of_mul_le_mul_left h4 hn0
  have hδn : 0 < δ * n := mul_pos hδ hn0
  have hηδ : η * (δ * n) ≤ δ * n := mul_le_of_le_one_left (le_of_lt hδn) hη
  have hmD : 0 ≤ (m:ℝ) * D := mul_nonneg (by linarith) hD
  have hmδn : 0 ≤ (m:ℝ) * (δ * n) := mul_nonneg (by linarith) (le_of_lt hδn)
  have hm1δn : 0 ≤ ((m:ℝ) - 1) * (δ * n) := mul_nonneg (by linarith) (le_of_lt hδn)
  rw [abs_le] at hT
  have hX1 : 3 * m * δ * n / 4 ≤ (T.card : ℝ) := by nlinarith
  have hη0 : 0 ≤ η := by
    by_contra hneg
    push_neg at hneg
    have h5 : η * (δ * n) < 0 := mul_neg_of_neg_of_pos hneg hδn
    linarith
  have hηX : 3 * D ≤ η * T.card := by
    have hmm : 0 ≤ D * ((m:ℝ) * m - 1) := mul_nonneg hD (by nlinarith)
    calc 3 * D ≤ 3 * m * m * D := by nlinarith
      _ = (3 * m / 4) * (4 * m * D) := by ring
      _ ≤ (3 * m / 4) * (η * (δ * n)) := mul_le_mul_of_nonneg_left hDη (by positivity)
      _ = η * (3 * m * δ * n / 4) := by ring
      _ ≤ η * T.card := mul_le_mul_of_nonneg_left hX1 hη0
  have hK : (0:ℝ) < 3 * m + 1 := by linarith
  have key : ∀ w c : ℝ, 0 ≤ w → w ≤ 4 → |c - w * δ * n / 4| ≤ D →
      |c - w / (3 * m + 1) * T.card| ≤ η * T.card := by
    intro w c hw0 hw4 hcw
    have hE : w / (3 * m + 1) * (T.card : ℝ)
        = w * δ * n / 4 + w * ((T.card : ℝ) - (3 * m + 1) / 4 * δ * n) / (3 * m + 1) := by
      field_simp
      ring
    have h1 : |w * ((T.card : ℝ) - (3 * m + 1) / 4 * δ * n) / (3 * m + 1)| ≤ 2 * D := by
      rw [abs_div, abs_mul, abs_of_nonneg hw0, abs_of_pos hK, div_le_iff₀ hK]
      have habs : |(T.card : ℝ) - (3 * m + 1) / 4 * δ * n| ≤ m * D := abs_le.mpr hT
      calc w * |(T.card : ℝ) - (3 * m + 1) / 4 * δ * n| ≤ 4 * (m * D) :=
            mul_le_mul hw4 habs (abs_nonneg _) (by norm_num)
        _ ≤ 2 * D * (3 * m + 1) := by nlinarith
    rw [hE]
    rw [abs_le] at hcw h1 ⊢
    constructor <;> linarith [hcw.1, hcw.2, h1.1, h1.2]
  refine ⟨?_, ?_, ?_⟩
  · rw [hA]; nlinarith
  · rw [hA]; nlinarith
  · intro γ
    have hcγ := hc γ
    by_cases hγ : γ ∈ A0
    · simp only [if_pos hγ] at hcγ ⊢
      have e : (4:ℝ) * δ * n / 4 = δ * n := by ring
      exact key 4 _ (by norm_num) le_rfl (by rw [e]; exact hcγ)
    · simp only [if_neg hγ] at hcγ ⊢
      have e : (3:ℝ) * δ * n / 4 = 3 / 4 * δ * n := by ring
      exact key 3 _ (by norm_num) (by norm_num) (by rw [e]; exact hcγ)
end
end

-- Source module: Development.AutomorphicArithmetic.ThickFrames.topsGroup

section

@[expose] public section

open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0
open Classical

private theorem tg_num (x eps Co δ N o n0 : ℝ) (he : 0 < eps) (hx : 1 ≤ x) (hbig : 64 * Co ^ 4 ≤ x ^ eps)
    (hδe : δ = x ^ (-(eps / 8))) (hN : x ^ (2 + 8 * eps) / 2 ≤ N) (ho1 : 1 ≤ o) (ho : o ≤ Co) (hn : o * n0 = N) :
    4 * o * Real.sqrt (2 * δ * N) ≤ x⁻¹ * (δ * n0) := by
  have hx0 : 0 < x := by linarith
  have hδ : 0 < δ := by rw [hδe]; positivity
  have hN0 : 0 < N := lt_of_lt_of_le (by positivity) hN
  have ho0 : 0 < o := by linarith
  have hn0 : n0 = N / o := by rw [← hn]; field_simp
  have h1 : x ^ 2 * x ^ eps ≤ δ * x ^ (2 + 8 * eps) := by
    rw [hδe, ← Real.rpow_add hx0, ← Real.rpow_two, ← Real.rpow_add hx0]
    exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have h2 : o ^ 4 ≤ Co ^ 4 := pow_le_pow_left₀ ho0.le ho 4
  have h3 : 32 * o ^ 4 * x ^ 2 ≤ δ * N := by
    have a1 := mul_le_mul_of_nonneg_left hN hδ.le
    have a2 : x ^ 2 * (64 * o ^ 4) ≤ x ^ 2 * x ^ eps :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith
  have h4 : Real.sqrt (2 * δ * N) ≤ δ * N / (4 * o ^ 2 * x) := by
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    rw [div_pow, le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ δ * N)
    calc 2 * δ * N * (4 * o ^ 2 * x) ^ 2 = δ * N * (32 * o ^ 4 * x ^ 2) := by ring
      _ ≤ δ * N * (δ * N) := this
      _ = _ := by ring
  calc 4 * o * Real.sqrt (2 * δ * N) ≤ 4 * o * (δ * N / (4 * o ^ 2 * x)) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = _ := by rw [hn0]; field_simp

private theorem tg_class_sum (A : Type) [Fintype A] [DecidableEq A] [AddCommGroup A] (A0 : AddSubgroup A)
    (u v : ℝ) (γ : A) :
    ∑ a ∈ univ.filter (fun a : A => a - γ ∈ A0), (if a ∈ A0 then u else v) =
      (if γ ∈ A0 then u else v) * Nat.card A0 := by
  have hc : (univ.filter (fun a : A => a - γ ∈ A0)).card = Nat.card A0 := by
    have e : {a : A // a - γ ∈ A0} ≃ A0 :=
      { toFun := fun a => ⟨a.1 - γ, a.2⟩
        invFun := fun b => ⟨b.1 + γ, by simp⟩
        left_inv := fun a => by ext; simp
        right_inv := fun b => by ext; simp }
    rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Finset.sum_congr rfl (g := fun _ => if γ ∈ A0 then u else v), Finset.sum_const, nsmul_eq_mul, hc, mul_comm]
  intro a ha
  rw [Finset.mem_filter] at ha
  have hiff : a ∈ A0 ↔ γ ∈ A0 := by
    constructor
    · intro h
      have := A0.sub_mem h ha.2
      simpa using this
    · intro h
      have := A0.add_mem ha.2 h
      simpa using this
  simp only [hiff]

theorem UpperTheory.BernoulliSumsFrobeniusOrbits.topsGroup :
    ∀ eps Co Lb : ℝ, 0 < eps → ∃ Cb x₀ : ℝ, 0 < Cb ∧ ∀ x ≥ x₀,
      ∀ (A : Type) [Fintype A] [DecidableEq A] [AddCommGroup A] (A0 : AddSubgroup A) (L₂ : ℕ),
      x ^ hE eps / 2 ≤ (Fintype.card A : ℝ) → (Fintype.card A : ℝ) ≤ Co * x ^ hE eps → (A0.index : ℝ) ≤ Co → (L₂ : ℝ) ≤ Lb →
      ∀ bs : A → A → A, (∀ h t, ∃ i : ℕ, bs h t + i • h = t) →
      ∀ (PP : Finset ℕ) (hp : ℕ → A) (ω : ℕ → ℝ), (∀ p, 0 ≤ ω p) → (∀ p ∈ PP, x ^ (eps / 4) ≤ (addOrderOf (hp p) : ℝ)) →
      ∃ TT : Finset A, dE eps x * Fintype.card A / 2 ≤ (TT.card : ℝ) ∧ (TT.card : ℝ) ≤ 2 * dE eps x * Fintype.card A ∧
        (∀ γ : A, |((TT.filter fun t => t - γ ∈ A0).card : ℝ) -
          (if γ ∈ A0 then 4 else 3) / (3 * (A0.index : ℝ) + 1) * (TT.card : ℝ)| ≤ x ^ (-1 + eps) * (TT.card : ℝ)) ∧
        ∑ p ∈ PP, ω p * (({t : A | t ∈ TT ∧ ¬ Formalism.MainNotions.G.IsGoodOrbit (addOrderOf (hp p))
            (Finset.univ.filter (fun i : Fin (addOrderOf (hp p)) => bs (hp p) t + (i : ℕ) • hp p ∈ TT)) L₂ (KE eps) (rE eps)
            (dE eps x) (hE eps) x}.ncard : ℕ) : ℝ) ≤ 4 * (Cb * x ^ (-2 : ℝ)) * dE eps x * Fintype.card A * ∑ p ∈ PP, ω p := by
  intro eps Co Lb he
  obtain ⟨Cb, x₀, hCb, hnum⟩ := UpperTheory.BernoulliSumsFrobeniusOrbits.orbit_terms eps Co Lb he
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop he).eventually_ge_atTop (64 * Co ^ 4))
  refine ⟨Cb, max x₀ (max x₁ 1), hCb, ?_⟩
  intro x hx A _ _ _ A0 L₂ hlo hhi hidx hL bs hbs PP hp ω hω hPP
  have hx1 : 1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hxx1 : x₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hxx0 : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx0 : 0 < x := by linarith
  have hδ : 0 < dE eps x := Real.rpow_pos_of_pos hx0 _
  have hδ1 : dE eps x ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
  have hN0 : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hβ : 0 ≤ Cb * x ^ (-2 : ℝ) := by positivity
  have hp1 : ∀ a : A, 3 / 4 * dE eps x ≤ (if a ∈ A0 then dE eps x else 3 / 4 * dE eps x) ∧
      (if a ∈ A0 then dE eps x else 3 / 4 * dE eps x) ≤ dE eps x := by
    intro a
    split_ifs <;> constructor <;> linarith
  have hD : 0 < Real.sqrt (2 * dE eps x * Fintype.card A) := Real.sqrt_pos.2 (by positivity)
  obtain ⟨T, hT1, hT2⟩ := UpperTheory.BernoulliSumsFrobeniusOrbits.select A (A ⧸ A0) ℕ (fun a => (a : A ⧸ A0))
    (fun a => if a ∈ A0 then dE eps x else 3 / 4 * dE eps x) (dE eps x) (Cb * x ^ (-2 : ℝ))
    (Real.sqrt (2 * dE eps x * Fintype.card A)) PP ω
    (fun p t T => ¬ Formalism.MainNotions.G.IsGoodOrbit (addOrderOf (hp p)) (Finset.univ.filter
      (fun i : Fin (addOrderOf (hp p)) => bs (hp p) t + (i : ℕ) • hp p ∈ T)) L₂ (KE eps) (rE eps)
      (dE eps x) (hE eps) x)
    (fun a => ⟨le_trans (by positivity) (hp1 a).1, (hp1 a).2⟩) hδ.le hδ1 hβ hω hD
    (le_of_eq (Real.sq_sqrt (by positivity)).symm) (by
      intro p hpp t
      have hn : ((addOrderOf (hp p) : ℕ) : ℝ) ≤ Co * x ^ hE eps :=
        le_trans (Nat.cast_le.mpr addOrderOf_le_card_univ) hhi
      obtain ⟨h1, h2⟩ := hnum x hxx0 (addOrderOf (hp p)) L₂ (hPP p hpp) hn hL
      obtain ⟨i₀, _, _, hsum⟩ := UpperTheory.BernoulliSumsFrobeniusOrbits.orbit_sum A
        (fun a => if a ∈ A0 then dE eps x else 3 / 4 * dE eps x) (bs (hp p) t) (hp p) t (hbs _ _)
        (fun T => ¬ GoodOrbitIntervalTileCondition (addOrderOf (hp p)) T L₂ (KE eps) (rE eps)
          (Formalism.MainNotions.G.goodU (dE eps x)) (Formalism.MainNotions.G.orbitSmallMultiplicity (rE eps) (hE eps) x)
          (Formalism.MainNotions.G.goodG' (rE eps) (dE eps x) (hE eps) x)
          (Formalism.MainNotions.G.orbitWindowCount (rE eps) (dE eps x) (hE eps) x))
      have hu : 1 ≤ Formalism.MainNotions.G.goodU (dE eps x) := Nat.ceil_pos.mpr (by positivity)
      have h3 := UpperTheory.BernoulliSumsFrobeniusOrbits.not_good_le
        (fun i => if bs (hp p) t + i • hp p ∈ A0 then dE eps x else 3 / 4 * dE eps x) (dE eps x)
        (addOrderOf (hp p)) L₂ (KE eps) (rE eps)
        (Formalism.MainNotions.G.goodU (dE eps x)) (Formalism.MainNotions.G.orbitSmallMultiplicity (rE eps) (hE eps) x)
        (Formalism.MainNotions.G.goodG' (rE eps) (dE eps x) (hE eps) x)
        (Formalism.MainNotions.G.orbitWindowCount (rE eps) (dE eps x) (hE eps) x) i₀ (fun i => hp1 _) hδ.le hδ1 hu h1
      refine le_trans (le_of_eq hsum) ?_
      rw [mul_comm (Cb * x ^ (-2 : ℝ))]
      exact le_trans (mul_le_mul_of_nonneg_left (h3.trans h2)
        (le_trans (by positivity) (hp1 t).1)) (mul_le_mul_of_nonneg_right (hp1 t).2 hβ))
  have hidx1 : (1 : ℝ) ≤ A0.index := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 AddSubgroup.index_ne_zero_of_finite
  have hmul : (A0.index : ℝ) * Nat.card A0 = Fintype.card A := by
    rw [← Nat.card_eq_fintype_card]
    exact_mod_cast A0.index_mul_card
  have hnumD := tg_num x eps Co (dE eps x) (Fintype.card A) A0.index (Nat.card A0) he hx1
    (hx₁ x hxx1) rfl hlo hidx1 hidx hmul
  obtain ⟨hS1, hS2, hS3⟩ := UpperTheory.BernoulliSumsFrobeniusOrbits.shares_of_counts A A0 T (dE eps x) x⁻¹
    (Real.sqrt (2 * dE eps x * Fintype.card A)) hδ (inv_le_one_of_one_le₀ hx1) hD.le hnumD (by
      intro γ
      have hc : ∀ a : A, ((a : A ⧸ A0) = (γ : A ⧸ A0)) ↔ a - γ ∈ A0 := fun a =>
        QuotientAddGroup.eq_iff_sub_mem
      have := hT1 (γ : A ⧸ A0)
      simp only [hc] at this
      rw [← tg_class_sum A A0 (dE eps x) (3 / 4 * dE eps x) γ]
      convert this)
  refine ⟨T, hS1, hS2, fun γ => le_trans (hS3 γ) ?_, hT2⟩
  refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
  rw [← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
end
end
