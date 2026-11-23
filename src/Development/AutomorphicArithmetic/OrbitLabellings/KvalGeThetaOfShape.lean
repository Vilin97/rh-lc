module

public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Formalism.IncomingBounds.IncomingBound
public import Development.AutomorphicArithmetic.OrbitLabellings.ExistsMaxFlowAttainedAndIsOptDual
public import Formalism.IncomingBounds.FlowDegreeBounds.LemmaFd
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
public import Development.AutomorphicArithmetic.OrbitLabellings.KvalGeOfNormMfactMulCoeffLe
public import Development.AutomorphicArithmetic.OrbitLabellings.NormMfactMulCoeffLeOfB0S
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AutomorphicArithmetic.OrbitLabellings.SumDemandFilterTwoDivLeOfIsOptDual

section

@[expose] public section

open scoped BigOperators
open Formalism.IncomingBounds

theorem UpperTheory.sum_demand_filter_two_div_le_of_isOptDual :
    ∀ (l d : ℕ) [NeZero d], 3 ≤ l → ∀ D sig : ZMod d → ℝ, 0 ≤ D → IsOptDual l d D sig →
    (∑ s ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sig s), D s) ≤ (∑ s : ZMod d, D s) / l := by
  intro l d _ hl D sig hD hopt
  obtain ⟨⟨x, hx, hxv⟩, -⟩ := UpperTheory.exists_maxFlow_attained_and_isOptDual l d hl D hD
  have hl0 : (0 : ℝ) < l := by
    have : (3 : ℝ) ≤ l := by exact_mod_cast hl
    linarith
  have hl1 : (1 : ℝ) ≤ l := by
    have : (3 : ℝ) ≤ l := by exact_mod_cast hl
    linarith
  have hin_nn : ∀ s : ZMod d, 0 ≤ ∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i :=
    fun s => Finset.sum_nonneg fun i _ => hx.1 _ _
  have hF : ∑ s ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sig s), D s ≤ flowVal d x := by
    calc ∑ s ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sig s), D s
        = ∑ s ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sig s),
            ∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i := by
          refine Finset.sum_congr rfl fun s hs => ?_
          exact (FlowDualityReindexing.fd_part1 hl D sig hopt s (Finset.mem_filter.mp hs).2 x hx hxv).2
      _ ≤ ∑ s, ∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun s _ _ => hin_nn s
      _ = flowVal d x := by
          unfold flowVal
          exact FlowDualityReindexing.in_reindex x
  have hout : ∀ s : ZMod d, (l : ℝ) * ∑ i ∈ oddLevels d, x s i
      ≤ ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x s i := by
    intro s
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have hodd : Odd i := (Finset.mem_filter.mp hi).2
    have hi1 : 1 ≤ i := hodd.pos
    have hpow : (l : ℝ) ≤ (l : ℝ) ^ i := by
      calc (l : ℝ) = (l : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (l : ℝ) ^ i := pow_le_pow_right₀ hl1 hi1
    exact mul_le_mul_of_nonneg_right hpow (hx.1 s i)
  have htot : (l : ℝ) * flowVal d x + flowVal d x ≤ ∑ s, D s := by
    have h := Finset.sum_le_sum fun s (_ : s ∈ (Finset.univ : Finset (ZMod d))) => hx.2 s
    rw [Finset.sum_add_distrib, FlowDualityReindexing.in_reindex x] at h
    have h2 : (l : ℝ) * flowVal d x ≤ ∑ s, ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x s i := by
      unfold flowVal
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun s _ => hout s
    unfold flowVal at h2 ⊢
    linarith
  have hFnn : 0 ≤ flowVal d x :=
    Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun i _ => hx.1 _ _
  rw [le_div_iff₀ hl0]
  nlinarith
end
end

-- Source module: Development.AutomorphicArithmetic.OrbitLabellings.ExistsNonnegDualFnumSubLeOfDemandNearMul

section

@[expose] public section

open scoped BigOperators
open Formalism.IncomingBounds

theorem UpperTheory.exists_nonneg_dual_fnum_sub_le_of_demand_near_mul :
    ∀ (l d : ℕ) [NeZero d], 5 ≤ l → 2 ≤ d → ∀ (κ : ℝ) (w D : ZMod d → ℝ), 0 < κ → (∀ s, 0 ≤ w s) →
    (∀ s, κ * w s ≤ D s ∧ D s ≤ κ * w s + 4 * w s) →
    ∃ sig : ZMod d → ℝ, (∀ s, 0 ≤ sig s) ∧ IsDualAll l d sig ∧
      Fnum l d (fun s => κ * w s) - κ * (∑ s, w s) / (l : ℝ) ^ 3 - 8 * (∑ s, w s) / l ≤ ∑ s, D s * (gam l - sig s) := by
  intro l d _ hl hd κ w D hκ hw hD
  have hl3 : 3 ≤ l := by omega
  have hlR : (5 : ℝ) ≤ l := by exact_mod_cast hl
  have hl0 : (0 : ℝ) < l := by linarith
  have hκw : (0 : ZMod d → ℝ) ≤ fun s => κ * w s := fun s => mul_nonneg hκ.le (hw s)
  obtain ⟨-, sig, hdual, hF⟩ := UpperTheory.exists_maxFlow_attained_and_isOptDual l d hl3 (fun s => κ * w s) hκw
  have hheavy := UpperTheory.sum_demand_filter_two_div_le_of_isOptDual l d hl3 (fun s => κ * w s) sig hκw ⟨hdual, hF⟩
  set c : ℝ := 1 / (l : ℝ) ^ 3 with hc
  have hc0 : 0 < c := by positivity
  have hsig0 : ∀ s, 0 ≤ sig s := fun s => (hdual.1 s).1
  have hsig1 : ∀ s, sig s ≤ 1 := fun s => (hdual.1 s).2
  have hgam1 : 1 / (l : ℝ) ≤ gam l := by
    unfold gam
    have hden : (0 : ℝ) < (l : ℝ) ^ 2 - 1 := by nlinarith
    rw [div_le_div_iff₀ hl0 hden]
    nlinarith
  have hgam0 : 0 ≤ gam l := le_trans (by positivity) hgam1
  have hc2 : c < 2 / (l : ℝ) := by
    rw [hc, div_lt_div_iff₀ (by positivity) hl0]
    have h3 : (l : ℝ) ^ 3 = l * (l * l) := by ring
    have hll : (1 : ℝ) ≤ l * l := by nlinarith
    rw [h3]
    nlinarith
  have h2l : 2 / (l : ℝ) ≤ 1 := by
    rw [div_le_one hl0]; linarith
  refine ⟨fun s => max (sig s) c, fun s => le_trans (hsig0 s) (le_max_left _ _), ?_, ?_⟩
  · intro s i hi
    by_cases hid : i < d
    · have hmem : i ∈ oddLevels d := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hid, hi⟩
      have h := hdual.2 s i hmem
      have hp : (0 : ℝ) ≤ (l : ℝ) ^ i := by positivity
      have h1 := mul_le_mul_of_nonneg_left (le_max_left (sig s) c) hp
      have h2 := le_max_left (sig (s + (i : ZMod d))) c
      linarith
    · have hi3 : 3 ≤ i := by
        obtain ⟨k, rfl⟩ := hi
        omega
      have hpow : (l : ℝ) ^ 3 ≤ (l : ℝ) ^ i := pow_le_pow_right₀ (by linarith) hi3
      have hlc : (l : ℝ) ^ 3 * c = 1 := by
        rw [hc]
        field_simp
      have hp3 : (0 : ℝ) ≤ (l : ℝ) ^ 3 := by positivity
      have h1 : (l : ℝ) ^ 3 * c ≤ (l : ℝ) ^ i * max (sig s) c :=
        mul_le_mul hpow (le_max_right _ _) hc0.le (le_trans hp3 hpow)
      have h2 : 0 ≤ max (sig (s + (i : ZMod d))) c := le_trans hc0.le (le_max_right _ _)
      linarith
  · have hpt : ∀ s, κ * w s * (gam l - sig s) - κ * w s * c - 4 * w s / l
        - 4 * (if 2 / (l : ℝ) ≤ sig s then w s else 0) ≤ D s * (gam l - max (sig s) c) := by
      intro s
      obtain ⟨hD1, hD2⟩ := hD s
      have hws := hw s
      have hmx : max (sig s) c - sig s ≤ c := by
        rcases le_total (sig s) c with h | h
        · rw [max_eq_right h]; linarith [hsig0 s]
        · rw [max_eq_left h]; linarith
      have hkw : κ * w s * (max (sig s) c - sig s) ≤ κ * w s * c :=
        mul_le_mul_of_nonneg_left hmx (mul_nonneg hκ.le hws)
      have hsplit : D s * (gam l - max (sig s) c) = κ * w s * (gam l - sig s)
          - κ * w s * (max (sig s) c - sig s) + (D s - κ * w s) * (gam l - max (sig s) c) := by ring
      have he0 : 0 ≤ D s - κ * w s := by linarith
      have he4 : D s - κ * w s ≤ 4 * w s := by linarith
      have h4l : 0 ≤ 4 * w s / l := by positivity
      split_ifs with hh
      · have hmx1 : max (sig s) c ≤ 1 := max_le (hsig1 s) (by linarith)
        have ht : -1 ≤ gam l - max (sig s) c := by linarith
        have hm := mul_le_mul_of_nonneg_left ht he0
        have : -(4 * w s) ≤ (D s - κ * w s) * (gam l - max (sig s) c) := by
          linarith
        linarith
      · push_neg at hh
        have hlt : max (sig s) c < 2 / (l : ℝ) := max_lt hh hc2
        have hlow : -(1 / (l : ℝ)) ≤ gam l - max (sig s) c := by
          have : 2 / (l : ℝ) = 1 / l + 1 / l := by ring
          linarith
        have hm := mul_le_mul_of_nonneg_left hlow he0
        have hil : (0 : ℝ) ≤ 1 / l := by positivity
        have hm2 := mul_le_mul_of_nonneg_right he4 hil
        have : -(4 * w s / l) ≤ (D s - κ * w s) * (gam l - max (sig s) c) := by
          have e : 4 * w s / l = 4 * w s * (1 / l) := by ring
          rw [e]
          have e2 : (D s - κ * w s) * -(1 / (l : ℝ)) = -((D s - κ * w s) * (1 / l)) := by ring
          linarith
        linarith
    have hsum := Finset.sum_le_sum fun s (_ : s ∈ (Finset.univ : Finset (ZMod d))) => hpt s
    simp only [Finset.sum_sub_distrib] at hsum
    rw [← Finset.mul_sum, ← Finset.sum_filter] at hsum
    have hFs : Fnum l d (fun s => κ * w s) = ∑ s, κ * w s * (gam l - sig s) := hF
    have hH : ∑ s ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sig s), w s
        ≤ (∑ s, w s) / l := by
      have e1 : ∑ s ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sig s), κ * w s
          = κ * ∑ s ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sig s), w s :=
        (Finset.mul_sum _ _ _).symm
      have e2 : (∑ s, κ * w s) / l = κ * ((∑ s, w s) / l) := by
        rw [← Finset.mul_sum]; ring
      have h := hheavy
      rw [e1, e2] at h
      exact le_of_mul_le_mul_left h hκ
    have e3 : ∑ s, κ * w s * c = κ * (∑ s, w s) / (l : ℝ) ^ 3 := by
      rw [hc, ← Finset.sum_mul, ← Finset.mul_sum]; ring
    have e4 : ∑ s, 4 * w s / (l : ℝ) = 4 * (∑ s, w s) / l := by
      rw [Finset.mul_sum, Finset.sum_div]
    rw [e3, e4] at hsum
    have hW : 0 ≤ (∑ s, w s) / l := by
      have := Finset.sum_nonneg fun s (_ : s ∈ (Finset.univ : Finset (ZMod d))) => hw s
      positivity
    have e5 : 8 * (∑ s, w s) / l = 4 * (∑ s, w s) / l + 4 * ((∑ s, w s) / l) := by ring
    rw [hFs, e5]
    linarith
end
end

-- Source module: Development.AutomorphicArithmetic.OrbitLabellings.KvalGeThetaOfShape

section

@[expose] public section

open scoped BigOperators
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G UpperTheory.G2 Classical

namespace UpperTheory.OrbitRadiiBounds

open Formalism.IncomingBounds in
private theorem lpF_eq (l d : ℕ) [NeZero d] (D : ZMod d → ℝ) : Formalism.BasicNotions.lpF l d D = Fnum l d D := by
  unfold Formalism.BasicNotions.lpF Fnum maxFlow Formalism.IncomingBounds.gam
  congr 2
  ext y
  simp only [Formalism.BasicNotions.lpFeasible, Set.mem_ofPred_eq, IsFlow, flowVal, oddLevels]
  constructor
  · rintro ⟨xs, h0, hz, hD, rfl⟩
    have hf : ∀ (f : ℕ → ℝ), (∀ i, ¬ Odd i → f i = 0) →
        ∑ i ∈ (Finset.range d).filter Odd, f i = ∑ i ∈ Finset.range d, f i := by
      intro f hf0
      exact Finset.sum_filter_of_ne (fun i _ h => by by_contra ho; exact h (hf0 i ho))
    refine ⟨xs, ⟨h0, fun s => ?_⟩, ?_⟩
    · rw [hf _ (fun i ho => by rw [hz s i (Or.inl ho), mul_zero]),
        hf _ (fun i ho => hz _ i (Or.inl ho))]
      exact hD s
    · apply Finset.sum_congr rfl; intro s _
      exact hf _ (fun i ho => hz s i (Or.inl ho))
  · rintro ⟨x, ⟨h0, hD⟩, rfl⟩
    have e1 : ∀ (f : ℕ → ℝ), ∑ i ∈ Finset.range d, (if Odd i ∧ i < d then f i else 0) =
        ∑ i ∈ (Finset.range d).filter Odd, f i := by
      intro f; rw [Finset.sum_filter]; apply Finset.sum_congr rfl; intro i hi
      rw [Finset.mem_range] at hi; by_cases ho : Odd i <;> simp [ho, hi]
    refine ⟨fun s i => if Odd i ∧ i < d then x s i else 0, ?_, ?_, ?_, ?_⟩
    · intro s i; dsimp only; split_ifs <;> simp [h0]
    · intro s i h; dsimp only; rw [if_neg]; rintro ⟨h1, h2⟩; rcases h with h | h; exact h h1; omega
    · intro s
      have h2 : ∀ i, (l : ℝ) ^ i * (if Odd i ∧ i < d then x s i else 0) =
          (if Odd i ∧ i < d then (l : ℝ) ^ i * x s i else 0) := by intro i; split_ifs <;> simp
      simp only [h2]
      rw [e1 (fun i => (l : ℝ) ^ i * x s i), e1 (fun i => x (s - (i : ZMod d)) i)]
      exact hD s
    · apply Finset.sum_congr rfl; intro s _
      exact (e1 (fun i => x s i)).symm

private theorem orbit (D : D7) (L : SizeData₂ D) (X : Inst D L) (E : OrbitPlaces.Ent D) (hS : OrbitPlaces.Shape D L X E)
    (p : ℕ) (h5 : 5 ≤ p) (hc : IsResidueClassZero D p) (hh : hP D p ≠ 0) (u : D.what₂.Word) (i : ℕ) (hi : i < D.R.m) (r : OrbitPlaces.Pl D) :
    ∃ sig : ZMod (nP D p) → ℝ, (∀ s, 0 ≤ sig s) ∧ Formalism.IncomingBounds.IsDualAll p (nP D p) sig ∧
      (if r ∉ kindA D p then FOrb D (i + 1) p r -
          ((D.R.k : ℝ) - 1) * (∑ s, wPl D (i + 1) (OrbitPlaces.orbMap D p r s)) / (p : ℝ) ^ 3 -
          8 * (∑ s, wPl D (i + 1) (OrbitPlaces.orbMap D p r s)) / p else 0) ≤
        ∑ s, E.size u i (OrbitPlaces.orbMap D p r s) * (Formalism.IncomingBounds.gam p - sig s) := by
  have hs : ¬ IsSg D p := by
    intro h4
    have h3 : D.host.cls p = _ := hc
    have h4' : D.host.cls p = _ := h4
    rw [h4'] at h3; simp at h3
  have hp5 : (5 : ℝ) ≤ p := by exact_mod_cast h5
  split_ifs with hr
  · refine ⟨fun _ => 1 / ((p : ℝ) + 1), fun _ => by positivity, ?_, ?_⟩
    · intro s e he
      have h1 : (p : ℝ) ≤ (p : ℝ) ^ e := le_self_pow₀ (by linarith) he.pos.ne'
      have h2 : (p : ℝ) * (1 / ((p : ℝ) + 1)) + 1 / ((p : ℝ) + 1) = 1 := by field_simp
      have h3 : (p : ℝ) * (1 / ((p : ℝ) + 1)) ≤ (p : ℝ) ^ e * (1 / ((p : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      show 1 ≤ (p : ℝ) ^ e * (1 / ((p : ℝ) + 1)) + 1 / ((p : ℝ) + 1)
      linarith
    · refine Finset.sum_nonneg fun s _ => mul_nonneg (Nat.cast_nonneg _) ?_
      unfold Formalism.IncomingBounds.gam
      rw [sub_nonneg, div_le_div_iff₀ (by linarith) (by nlinarith)]
      nlinarith
  · have hn : nP D p = addOrderOf (hP D p) := if_neg hs
    have h2 : 2 ≤ nP D p := by
      have h0 : nP D p ≠ 0 := NeZero.ne _
      have h1 : nP D p ≠ 1 := by rw [hn]; exact fun h => hh (AddMonoid.addOrderOf_eq_one_iff.1 h)
      omega
    have hk : (0 : ℝ) < (D.R.k : ℝ) - 1 := by
      have h1 := hS.rankA
      have h2 : 0 ≤ Real.logb 5 (L.sc.a ^ 2) := Real.logb_nonneg (by norm_num) (by nlinarith [hS.xa.2])
      linarith
    have hnt : ∀ s, ¬ IsTopPl D (OrbitPlaces.orbMap D p r s) := by
      intro s ht
      apply hr
      rw [← OrbitPlaces.memA_orb p r s]
      unfold kindA
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hs, ht.1⟩
    obtain ⟨sig, h0, hd, hb⟩ := UpperTheory.exists_nonneg_dual_fnum_sub_le_of_demand_near_mul p (nP D p) h5 h2 ((D.R.k : ℝ) - 1)
      (fun s => wPl D (i + 1) (OrbitPlaces.orbMap D p r s)) (fun s => E.size u i (OrbitPlaces.orbMap D p r s)) hk
      (fun s => (hS.wpos i hi _).le)
      (fun s => by obtain ⟨a, b⟩ := hS.low u i hi _ (hnt s); constructor <;> linarith)
    refine ⟨sig, h0, hd, ?_⟩
    rw [← lpF_eq] at hb
    exact hb

private theorem radii (D : D7) (L : SizeData₂ D) (X : Inst D L) (E : OrbitPlaces.Ent D) (hS : OrbitPlaces.Shape D L X E)
    (p : ℕ) (h5 : 5 ≤ p) (hc : IsResidueClassZero D p) (hh : hP D p ≠ 0) (u : D.what₂.Word) (i : ℕ) (hi : i < D.R.m) :
    ∃ sig : OrbitPlaces.Pl D → ℝ, IsRadii p (posPl D p) sig ∧
      (∑ z ∈ kindBC D p, FOrb D (i + 1) p z) / (nP D p : ℝ) -
        ((D.R.k : ℝ) - 1) * (∑ z ∈ kindBC D p, wPl D (i + 1) z) / (p : ℝ) ^ 3 -
        8 * (∑ z ∈ kindBC D p, wPl D (i + 1) z) / p ≤ ∑ z, E.size u i z * (Formalism.IncomingBounds.gam p - sig z) := by
  choose σ h0 hd hb using orbit D L X E hS p h5 hc hh u i hi
  have hR := OrbitPlaces.isReps_repsPl X p
  set R := OrbitPlaces.repsPl X p
  have hpos : 0 < nP D p := Nat.pos_of_ne_zero (NeZero.ne _)
  have hex : ∀ z, ∃ r ∈ R, ∃ s, OrbitPlaces.orbMap D p r s = z := by
    intro z
    obtain ⟨r, ⟨hr, e, he⟩, -⟩ := hR z
    exact ⟨r, hr, (e : ZMod (nP D p)), by unfold OrbitPlaces.orbMap; rw [ZMod.val_natCast, posPl_mod, he]⟩
  choose rr hrr ss hss using hex
  have key : ∀ r ∈ R, ∀ s, σ (rr (OrbitPlaces.orbMap D p r s)) (ss (OrbitPlaces.orbMap D p r s)) = σ r s := by
    intro r hr s
    have h := hss (OrbitPlaces.orbMap D p r s)
    have h1 : rr (OrbitPlaces.orbMap D p r s) = r :=
      (hR (OrbitPlaces.orbMap D p r s)).unique ⟨hrr _, _, h⟩ ⟨hr, s.val, rfl⟩
    rw [h1] at h ⊢
    rw [ZMod.val_injective _ (posPl_inj D p r _ _ (ZMod.val_lt _) (ZMod.val_lt _) h)]
  refine ⟨fun z => σ (rr z) (ss z), ⟨fun z => h0 _ _, fun z e he => ?_⟩, ?_⟩
  · have e1 : posPl D p z e = OrbitPlaces.orbMap D p (rr z) (ss z + (e : ZMod (nP D p))) := by
      conv_lhs => rw [← hss z]
      unfold OrbitPlaces.orbMap
      rw [posPl_add, ZMod.val_add, ZMod.val_natCast, posPl_mod, ← posPl_add D p _ _ (e % nP D p), posPl_mod, posPl_add]
    show 1 ≤ (p : ℝ) ^ e * σ (rr z) (ss z) + σ (rr (posPl D p z e)) (ss (posPl D p z e))
    rw [e1, key _ (hrr z)]
    exact hd _ _ e he
  · have hn : (nP D p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne _)
    have eF : (∑ z ∈ kindBC D p, FOrb D (i + 1) p z) / (nP D p : ℝ) =
        ∑ r ∈ R.filter (fun r => r ∉ kindA D p), FOrb D (i + 1) p r := by
      rw [← OrbitPlaces.sum_orbBC p _ R hR, Finset.sum_div]
      refine Finset.sum_congr rfl fun r _ => ?_
      have hc : ∀ s : ZMod (nP D p), FOrb D (i + 1) p (OrbitPlaces.orbMap D p r s) = FOrb D (i + 1) p r :=
        fun s => FOrb_step D (i + 1) p r s.val
      rw [Finset.sum_congr rfl (fun s _ => hc s), Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul,
        mul_div_cancel_left₀ _ hn]
    have hsum := Finset.sum_le_sum (fun r (_ : r ∈ R) => hb r)
    rw [← Finset.sum_filter] at hsum
    rw [eF, ← OrbitPlaces.sum_orbBC p (wPl D (i + 1)) R hR, ← OrbitPlaces.sum_orb p _ R hR]
    refine le_trans (le_of_eq ?_) (le_trans hsum (le_of_eq ?_))
    · rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div, ← Finset.mul_sum,
        ← Finset.mul_sum]
    · exact Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun s _ => by simp only [key r hr s]

private theorem NN_le (D : D7) (i : ℕ) (hi : i < D.R.m) : (D.R.N i : ℝ) * (D.R.N (i + 1) : ℝ) ≤ Nm D ^ 2 := by
  have h1 : D.R.N i ≤ D.R.N D.R.m := Nat.add_le_add_left (Nat.mul_le_mul_right _ hi.le) _
  have h2 : D.R.N (i + 1) ≤ D.R.N D.R.m := Nat.add_le_add_left (Nat.mul_le_mul_right _ hi) _
  have h1' : (D.R.N i : ℝ) ≤ Nm D := by unfold Nm; exact_mod_cast h1
  have h2' : (D.R.N (i + 1) : ℝ) ≤ Nm D := by unfold Nm; exact_mod_cast h2
  rw [sq]
  exact mul_le_mul h1' h2' (by positivity) (le_trans (by positivity) h1')

end UpperTheory.OrbitRadiiBounds

open UpperTheory.OrbitRadiiBounds in
theorem UpperTheory.kvalGe_theta_of_shape :
    ∀ (D : D7) (L : SizeData₂ D) (X : Inst D L) (E : OrbitPlaces.Ent D), OrbitPlaces.Shape D L X E →
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → IsResidueClassZero D p → hP D p ≠ 0 → ∀ [NeZero (nP D p)], (p : ℝ) ≤ L.sc.X'' D.R.n → ∀ u, ∀ i < D.R.m,
    ∀ Th : MvPowerSeries (OrbitPlaces.Pl D × Fin (D.R.N i) × Fin (D.R.N (i + 1))) ℂ_[p], HasThetaProductForm p (nP D p) (posPl D p) Th →
    product_zeroth_first_parts.KvalGe (D.R.N i) (D.R.N (i + 1)) p (E.nu u i) Th
      ((∑ z ∈ kindBC D p, FOrb D (i + 1) p z) / (nP D p : ℝ) -
        ((D.R.k : ℝ) - 1) * (∑ z ∈ kindBC D p, wPl D (i + 1) z) / (p : ℝ) ^ 3 - 8 * (∑ z ∈ kindBC D p, wPl D (i + 1) z) / p -
        3 * (D.R.f : ℝ) * Nm D ^ 2 * Real.logb p L.sc.a) := by
  intro D L X E hS p hp h5 hc hh _ hpX u i hi Th hTh
  obtain ⟨sig, hsig, hb⟩ := radii D L X E hS p h5 hc hh u i hi
  refine UpperTheory.kvalGe_of_norm_mfact_mul_coeff_le p _ _ _ _ _ _ fun κ hκ => ?_
  have hp5 : (5 : ℝ) ≤ p := by exact_mod_cast h5
  have hp1 : (1 : ℝ) < p := by linarith
  have hp0 : (0 : ℝ) < p := by linarith
  have hnorm : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]) p, norm_algebraMap', Padic.norm_p]
  have hodd : Odd p := hp.out.odd_of_ne_two (by omega)
  have hA : ∀ v, (κ v : ℝ) ≤ L.sc.a ^ 2 := by
    rintro ⟨t, ab⟩
    refine le_trans ?_ (hS.sizeA u i hi t)
    unfold OrbitPlaces.Ent.size
    rw [← hκ t]
    exact_mod_cast Finset.single_le_sum (f := fun ab => κ (t, ab)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ ab)
  have h := UpperTheory.norm_mfact_mul_coeff_le_of_B0S ℂ_[p] p (nP D p) hp.out hodd (by rw [hnorm]; exact inv_lt_one_of_one_lt₀ hp1)
    _ _ (posPl D p) ⟨posPl_zero D p, posPl_add D p, posPl_period D p⟩ Th hTh sig hsig κ (L.sc.a ^ 2)
    (by nlinarith [hS.xa.2]) hA
  refine h.trans ?_
  rw [hnorm, Real.inv_rpow hp0.le, ← Real.rpow_neg hp0.le]
  refine Real.rpow_le_rpow_of_exponent_le hp1.le (neg_le_neg ?_)
  have e1 : (∑ v : OrbitPlaces.Pl D × Fin (D.R.N i) × Fin (D.R.N (i + 1)), (κ v : ℝ) * (Formalism.IncomingBounds.gam p - sig v.1)) =
      ∑ z, E.size u i z * (Formalism.IncomingBounds.gam p - sig z) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun z _ => ?_
    unfold OrbitPlaces.Ent.size
    rw [← hκ z, Nat.cast_sum, Finset.sum_mul]
  have e2 : (Fintype.card (OrbitPlaces.Pl D × Fin (D.R.N i) × Fin (D.R.N (i + 1))) : ℝ) =
      (D.R.f : ℝ) * ((D.R.N i : ℝ) * (D.R.N (i + 1) : ℝ)) := by
    rw [Fintype.card_prod, Fintype.card_prod (Fin _), Fintype.card_fin, Fintype.card_fin, Nat.cast_mul, Nat.cast_mul,
      OrbitPlaces.card_Pl]
  have hpa : (p : ℝ) ≤ L.sc.a := le_trans hpX hS.xa.1
  have hLg : 1 ≤ Real.logb p L.sc.a := by
    rw [Real.le_logb_iff_rpow_le hp1 (by linarith), Real.rpow_one]; exact hpa
  have hlog2 : Real.logb p (L.sc.a ^ 2) = 2 * Real.logb p L.sc.a := by
    unfold Real.logb; rw [Real.log_pow]; push_cast; ring
  have hf : (0 : ℝ) ≤ D.R.f := by positivity
  have hB : (D.R.f : ℝ) * ((D.R.N i : ℝ) * (D.R.N (i + 1) : ℝ)) * (2 * Real.logb p L.sc.a + 1) ≤
      ((D.R.f : ℝ) * Nm D ^ 2) * (3 * Real.logb p L.sc.a) :=
    mul_le_mul (mul_le_mul_of_nonneg_left (NN_le D i hi) hf) (by linarith) (by linarith) (by positivity)
  rw [e1, e2, hlog2]
  linarith
end
end
