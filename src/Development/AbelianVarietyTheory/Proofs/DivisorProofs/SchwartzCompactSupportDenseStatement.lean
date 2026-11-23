module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.CompactSupport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzContinuousAtOfPointwiseOfBounded
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Data.Nat.Choose.Multinomial

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzDenseHasCompactSupport

section

@[expose] public section

open Filter Topology
open scoped ContDiff

namespace GlobalTheory

theorem schwartz_dense_hasCompactSupport :
    ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V],
    Dense {f : SchwartzMap V ℂ | HasCompactSupport (f : V → ℂ)} := by
  intro V _ _ _
  exact SchwartzMap.dense_hasCompactSupport

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzCompactSupportDense

section

@[expose] public section

open MeasureTheory Filter Topology
open scoped SchwartzMap

namespace GlobalTheory

theorem schwartz_mem_closure_hasCompactSupport :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (f : SchwartzMap V ℂ),
    f ∈ closure {g : SchwartzMap V ℂ | HasCompactSupport (g : V → ℂ)} := by
  intro V _ _ _ f
  exact schwartz_dense_hasCompactSupport f

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzCompactSupportDenseStatement

section

@[expose] public section

open MeasureTheory Filter Topology
open scoped SchwartzMap

theorem _root_.GlobalTheory.T.schwartz_compact_support_dense : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (f : SchwartzMap V ℂ),
    f ∈ closure {g : SchwartzMap V ℂ | HasCompactSupport (g : V → ℂ)} := by
  first | exact @GlobalTheory.schwartz_mem_closure_hasCompactSupport | exact GlobalTheory.schwartz_mem_closure_hasCompactSupport | (intros; apply GlobalTheory.schwartz_mem_closure_hasCompactSupport <;> assumption)
end
end
