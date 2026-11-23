module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsLocalCoeffLocal
public import Mathlib.RingTheory.Ideal.Height
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
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.MemDivSuppOfDivCycleNeZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.LengthCokerEqKerAddDimOneOrderSum

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MemMinimalPrimesIff

section

@[expose] public section

theorem UpperTheory.Reformulated.B.Yhd1.mem_minimalPrimes_iff.{u_1} :
    ∀ {A : Type u_1} [inst : CommRing A] [IsDomain A] [IsNoetherianRing A] {z : A},
      z ≠ (0 : A) → ∀ (W : Ideal A), W ∈ (Ideal.span {z}).minimalPrimes ↔ W.IsPrime ∧ W.height = (1 : ℕ∞) ∧ z ∈ W := by
  intro A _ _ _ z hz
  have key : ∀ P : Ideal A, P.IsPrime → z ∈ P → (1 : ℕ∞) ≤ P.height := by
    intro P hP hzP
    have hlt : (⊥ : Ideal A) < P := by
      refine bot_lt_iff_ne_bot.mpr fun h => hz ?_
      rw [h] at hzP
      exact Ideal.mem_bot.mp hzP
    have := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    exact le_trans le_add_self this
  intro W
  constructor
  · intro hW
    have hP : W.IsPrime := hW.1.1
    have hzW : z ∈ W := hW.1.2 (Ideal.mem_span_singleton_self z)
    exact ⟨hP, le_antisymm
      (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hW) (key W hP hzW), hzW⟩
  · rintro ⟨hP, hh, hzW⟩
    obtain ⟨P, hPm, hPW⟩ := Ideal.exists_minimalPrimes_le
      ((Ideal.span_singleton_le_iff_mem W).mpr hzW)
    have hP' : P.IsPrime := hPm.1.1
    have hzP : z ∈ P := hPm.1.2 (Ideal.mem_span_singleton_self z)
    rcases hPW.eq_or_lt with h | h
    · exact h ▸ hPm
    · exfalso
      have h1 := Ideal.height_add_one_le_of_lt_of_isPrime h
      have h2 : (1 : ℕ∞) + 1 ≤ 1 := by
        calc (1 : ℕ∞) + 1 ≤ P.height + 1 := by gcongr; exact key P hP' hzP
          _ ≤ W.height := h1
          _ = 1 := hh
      exact absurd h2 (by decide)
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocCycleSpanMul

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

theorem LocCycleSpanMul.mem_minimalPrimes_iff {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {z : A} (hz : z ≠ 0) (W : Ideal A) :
    W ∈ (Ideal.span {z}).minimalPrimes ↔ W.IsPrime ∧ W.height = 1 ∧ z ∈ W :=
  _root_.UpperTheory.Reformulated.B.Yhd1.mem_minimalPrimes_iff hz W

theorem LocCycleSpanMul.proof : LocCycleSpanMul.Statement := by
  intro A _ _ _ x y hx hy W
  by_cases hP : W.IsPrime ∧ W.height = 1
  · obtain ⟨hp, h1⟩ := hP
    have key : ∀ z : A, z ≠ 0 →
        locCycle (Ideal.span {z}) W = ((locLen (A ⧸ Ideal.span {z}) ⟨W, hp⟩).toNat : ℤ) ∧
          locLen (A ⧸ Ideal.span {z}) ⟨W, hp⟩ ≠ ⊤ := by
      intro z hz
      by_cases hzW : z ∈ W
      · have hm : W ∈ (Ideal.span {z}).minimalPrimes :=
          (LocCycleSpanMul.mem_minimalPrimes_iff hz W).mpr ⟨hp, h1, hzW⟩
        refine ⟨?_, locLen_ne_top hm⟩
        unfold locCycle
        rw [dite_eq_left hm]
        rfl
      · have hm : W ∉ (Ideal.span {z}).minimalPrimes := fun h =>
          hzW ((LocCycleSpanMul.mem_minimalPrimes_iff hz W).mp h).2.2
        have h0 : locLen (A ⧸ Ideal.span {z}) ⟨W, hp⟩ = 0 := by
          have := locLen_quot_eq_zero (V := (⊥ : Ideal A)) (g := z) ⟨W, hp⟩ hzW
          rwa [bot_sup_eq] at this
        refine ⟨?_, by rw [h0]; exact ENat.zero_ne_top⟩
        unfold locCycle
        rw [dite_eq_right hm, h0]
        simp
    obtain ⟨ex, fx⟩ := key x hx
    obtain ⟨ey, fy⟩ := key y hy
    obtain ⟨exy, -⟩ := key (x * y) (mul_ne_zero hx hy)
    have hmul := locLen_mul (V := (⊥ : Ideal A)) Ideal.isPrime_bot (f := x)
      (by rw [Ideal.mem_bot]; exact hx) y ⟨W, hp⟩
    rw [bot_sup_eq, bot_sup_eq, bot_sup_eq] at hmul
    rw [exy, ex, ey, hmul, ENat.toNat_add fy fx]
    push_cast
    ring
  · have hz : ∀ z : A, z ≠ 0 → locCycle (Ideal.span {z}) W = 0 := by
      intro z hz
      unfold locCycle
      rw [dite_eq_right]
      intro hm
      have h := (LocCycleSpanMul.mem_minimalPrimes_iff hz W).mp hm
      exact hP ⟨h.1, h.2.1⟩
    rw [hz _ (mul_ne_zero hx hy), hz x hx, hz y hy]
    simp

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end
