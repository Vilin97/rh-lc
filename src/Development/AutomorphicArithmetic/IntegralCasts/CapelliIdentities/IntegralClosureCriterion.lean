module

public import Formalism.LocalToGlobal.KernelLattices.ColumnData
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
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
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegralQuadraticHalfInt

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AdjoinSqrtEqRatSpan

section

@[expose] public section

theorem UpperTheory.adjoin_sqrt_eq_rat_span :
    ∀ (E : Type) [Field E] [CharZero E] (d : ℕ) (s : E), s ^ 2 = -(d : E) → ∀ x : E, x ∈ IntermediateField.adjoin ℚ ({s} : Set E) → ∃ a b : ℚ, x = (a : E) + (b : E) * s := by
  intro E _ _ d s hs x hx
  have hint : IsIntegral ℚ s := by
    apply IsIntegral.of_pow (n := 2) (by norm_num)
    rw [hs]
    have h : (-(d : E)) = algebraMap ℚ E (-(d : ℚ)) := by simp
    rw [h]
    exact isIntegral_algebraMap
  have hx' : x ∈ Algebra.adjoin ℚ ({s} : Set E) := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
    exact hx
  clear hx
  induction hx' using Algebra.adjoin_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff] at hy
    exact ⟨0, 1, by simp [hy]⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, b, rfl⟩ := hy
    obtain ⟨c, e, rfl⟩ := hz
    exact ⟨a + c, b + e, by push_cast; ring⟩
  | mul y z _ _ hy hz =>
    obtain ⟨a, b, rfl⟩ := hy
    obtain ⟨c, e, rfl⟩ := hz
    refine ⟨a * c - d * b * e, a * e + b * c, ?_⟩
    push_cast
    linear_combination (b : E) * (e : E) * hs
end
end

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegralClosureCriterion

section

@[expose] public section

@[reducible] noncomputable def UpperTheory.Reformulated.B.IntegralClosureCriterion.be :
    Formalism.L2.Ker.Car → ℂ :=
    fun (D : Formalism.L2.Ker.Car) ↦ Complex.I * (↑√(↑D.host.d : ℝ) : ℂ)

noncomputable def UpperTheory.Reformulated.B.IntegralClosureCriterion.OKc :
    Formalism.L2.Ker.Car → ℂ → Prop :=
    fun (D : Formalism.L2.Ker.Car) (z : ℂ) ↦
      ∃ (x : ℤ) (y : ℤ), Even (x - y) ∧ z = ((↑x : ℂ) + (↑y : ℂ) * UpperTheory.Reformulated.B.IntegralClosureCriterion.be D) / (2 : ℂ)

theorem UpperTheory.Reformulated.B.IntegralClosureCriterion.okc_of :
    ∀ (D : Formalism.L2.Ker.Car) (u : NumberField.RingOfIntegers ↥D.host.K),
      UpperTheory.Reformulated.B.IntegralClosureCriterion.OKc D ((D.host.φ₀ : D.host.E → ℂ) (↑(↑u : ↥D.host.K) : D.host.E)) := by
  intro D u
  have hφ : D.host.φ₀ D.host.sqd = Complex.I * ((Real.sqrt (D.host.d : ℝ) : ℝ) : ℂ) := D.host.φ₀_mem
  obtain ⟨a, b, hab⟩ := UpperTheory.adjoin_sqrt_eq_rat_span D.host.E D.host.d D.host.sqd D.host.sqd_sq
    ((u : D.host.K) : D.host.E) (u : D.host.K).2
  have hval : D.host.φ₀ ((u : D.host.K) : D.host.E)
      = (a : ℂ) + (b : ℂ) * (Complex.I * ((Real.sqrt (D.host.d : ℝ) : ℝ) : ℂ)) := by
    rw [hab, map_add (f := _), map_mul, map_ratCast, map_ratCast, hφ]
  have hint : IsIntegral ℤ (D.host.φ₀ ((u : D.host.K) : D.host.E)) :=
    (u.isIntegral_coe).map
      (D.host.φ₀.comp (algebraMap D.host.K D.host.E)).toIntAlgHom
  rw [hval] at hint
  obtain ⟨x, y, hxy, h⟩ := UpperTheory.integral_quadratic_half_int D.host.d D.host.hyp.2.1 a b hint
  exact ⟨x, y, hxy, hval.trans h⟩
end
end
