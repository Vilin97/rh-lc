module

public import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPthPowerScaleThinShellStatement
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.RingTheory.Valuation.Basic
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
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.NatCastEqOneOfCoprime

section

@[expose] public section

open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem valuation_nnreal_natCast_le_one {L : Type} [Field L] (v : Valuation L ℝ≥0) (n : ℕ) : v (n : L) ≤ 1 := by
  induction n with
  | zero => simp
  | succ k ih =>
    push_cast
    exact le_trans (v.map_add _ _) (max_le ih (by simp))

theorem valuation_nnreal_intCast_le_one {L : Type} [Field L] (v : Valuation L ℝ≥0) (z : ℤ) : v (z : L) ≤ 1 := by
  cases z with
  | ofNat n => simpa using valuation_nnreal_natCast_le_one v n
  | negSucc n =>
    rw [Int.cast_negSucc, Valuation.map_neg]
    exact_mod_cast valuation_nnreal_natCast_le_one v (n + 1)

theorem natCast_eq_one_of_coprime :
    ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p l : ℕ), v (p : L) < 1 → Nat.Coprime l p → v (l : L) = 1 := by
  intro L _ v p l hp hlp
  refine le_antisymm (valuation_nnreal_natCast_le_one v l) ?_
  by_contra hlt
  push_neg at hlt
  have hb : ((Nat.gcd l p : ℕ) : ℤ) = (l : ℤ) * Nat.gcdA l p + (p : ℤ) * Nat.gcdB l p := Nat.gcd_eq_gcd_ab l p
  rw [hlp, Nat.cast_one] at hb
  have hL : (1 : L) = (l : L) * (Nat.gcdA l p : L) + (p : L) * (Nat.gcdB l p : L) := by
    have := congrArg (fun z : ℤ => (z : L)) hb
    push_cast at this
    exact this
  have h1 : v (1 : L) < 1 := by
    rw [hL]
    refine lt_of_le_of_lt (v.map_add _ _) (max_lt ?_ ?_)
    · rw [v.map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right (by positivity) (valuation_nnreal_intCast_le_one v (Nat.gcdA l p))) hlt
    · rw [v.map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right (by positivity) (valuation_nnreal_intCast_le_one v (Nat.gcdB l p))) hp
  simp at h1

end GlobalTheory.AlmostEt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.NatCastEqOneOfCoprimeStatement

section

@[expose] public section

open GlobalTheory.AlmostEt
open scoped NNReal

theorem _root_.GlobalTheory.T.valuation_natCast_eq_one_of_coprime' : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p l : ℕ), v (p : L) < 1 → Nat.Coprime l p → v (l : L) = 1 := by
  first | exact @GlobalTheory.AlmostEt.natCast_eq_one_of_coprime | exact GlobalTheory.AlmostEt.natCast_eq_one_of_coprime | (intros; apply GlobalTheory.AlmostEt.natCast_eq_one_of_coprime <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.MovesIntegersAlmostUnitOfCoprimeOrder

section

@[expose] public section

open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem moves_top_of_coprime_order : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime →
    ∀ F : Subfield L, ApproxRoot p v F → 0 < v (p : L) → v (p : L) < 1 →
    ∀ (G : Type) [Group G] [MulSemiringAction G L], (∀ (g : G) (x : L), v (g • x) = v x) →
    ∀ σ : G, (∀ x ∈ F, σ • x = x) → ∀ l : ℕ, Nat.Coprime l p → σ ^ l = 1 →
    (∃ y : L, σ • y ≠ y) → Moves v ⊤ σ := by
  intro L _ v p hp F hF hp0 hp1 G _ _ hv σ hσF l hl hσl ⟨y, hy⟩ r hr
  obtain ⟨d, hdF, _hd0, hrx, hx1⟩ :=
    GlobalTheory.T.exists_pth_power_scale_thin_shell L v p hp F hF hp0 hp1 r hr (σ • y - y) (sub_ne_zero.mpr hy)
  set x := (σ • y - y) * d ^ p with hxdef
  refine ⟨x, Subfield.mem_top x, hx1, ?_⟩
  by_contra hle
  push_neg at hle
  have hfix : ∀ j : ℕ, (σ ^ j) • d = d := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, mul_smul, hσF d hdF, ih]
  have hterm : ∀ j : ℕ, (σ ^ j) • x = ((σ ^ (j + 1)) • y - (σ ^ j) • y) * d ^ p := by
    intro j
    rw [hxdef, smul_mul', smul_pow', hfix, smul_sub, pow_succ, mul_smul]
  have hsum : ∑ j ∈ Finset.range l, (σ ^ j) • x = 0 := by
    simp_rw [hterm]
    rw [← Finset.sum_mul, Finset.sum_range_sub (fun j => (σ ^ j) • y), hσl, one_smul, pow_zero,
      one_smul, sub_self, zero_mul]
  have hstep : ∀ j : ℕ, v ((σ ^ j) • x - x) ≤ r := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have e : (σ ^ (j + 1)) • x - x = σ • ((σ ^ j) • x - x) + (σ • x - x) := by
        rw [smul_sub, pow_succ', mul_smul]; ring
      rw [e]
      refine le_trans (Valuation.map_add _ _ _) (max_le ?_ hle)
      rw [hv]; exact ih
  have hlx : (l : L) * x = ∑ j ∈ Finset.range l, (x - (σ ^ j) • x) := by
    rw [Finset.sum_sub_distrib, hsum, sub_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h1 : v ((l : L) * x) ≤ r := by
    rw [hlx]
    apply Valuation.map_sum_le
    intro j _
    rw [← Valuation.map_neg, neg_sub]
    exact hstep j
  rw [map_mul, GlobalTheory.T.valuation_natCast_eq_one_of_coprime' L v p l hp1 hl, one_mul] at h1
  exact absurd (lt_of_lt_of_le hrx h1) (lt_irrefl _)

end GlobalTheory.AlmostEt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.MovesIntegersAlmostUnitOfCoprimeOrderStatement

section

@[expose] public section

open GlobalTheory.AlmostEt
open scoped NNReal

theorem _root_.GlobalTheory.T.movesIntegersAlmostUnit_of_coprime_order : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → ∀ F : Subfield L, ApproxRoot p v F → 0 < v (p : L) → v (p : L) < 1 → ∀ (G : Type) [Group G] [MulSemiringAction G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ σ : G, (∀ x ∈ F, σ • x = x) → ∀ l : ℕ, Nat.Coprime l p → σ ^ l = 1 → (∃ y : L, σ • y ≠ y) → Moves v ⊤ σ := by
  first | exact @GlobalTheory.AlmostEt.moves_top_of_coprime_order | exact GlobalTheory.AlmostEt.moves_top_of_coprime_order | (intros; apply GlobalTheory.AlmostEt.moves_top_of_coprime_order <;> assumption)
end
end
