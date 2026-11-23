module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.NefIntersectionNonnegAllDimsStatement
public import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.NefRiemannRochAsymptotic
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefNumericsOfRiemannRoch

section

@[expose] public section

set_option autoImplicit false

namespace GlobalTheory.Published

theorem nefNumerics_of_product_of_riemannRoch
    (h₁ : NefProductNonneg) (h₂ : NefRiemannRoch) : NefNumerics :=
  ⟨h₁, h₂.nefBigIff, h₂⟩

end GlobalTheory.Published
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.NefProductNonneg

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem nefProductNonneg : GlobalTheory.Published.NefProductNonneg := by
  intro k _ _ X _ d hp hd N hN
  exact GlobalTheory.T.nef_intersection_nonneg_all_dims k X hp d (structureModule X) (by rw [suppDim_structureModule, hd]) N hN

end GlobalTheory
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.NefProductNonnegStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
theorem _root_.GlobalTheory.T.nef_product_nonneg : GlobalTheory.Published.NefProductNonneg := by
  first | exact @_root_.GlobalTheory.nefProductNonneg | exact _root_.GlobalTheory.nefProductNonneg | (intros; apply _root_.GlobalTheory.nefProductNonneg <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.NefRiemannRoch

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem nefRiemannRoch : GlobalTheory.Published.NefRiemannRoch := by
  intro k _ _ X _ D hP hdim L hL
  obtain ⟨C, hC⟩ := NefRiemannRoch.abs_factorial_mul_sections_sub_top_le k X hP D hdim.le L hL
  rcases D with _ | n
  · have hz : ∀ m : ℕ, (lbH0 k (lbPow L m) : ℤ) = topSelfIntersection k L 0 := by
      intro m
      have h := hC m
      simp only [Nat.factorial_zero, Nat.cast_one, one_mul, pow_zero, mul_one, Nat.cast_zero,
        zero_mul, mul_zero, abs_nonpos_iff, sub_eq_zero] at h
      exact h
    refine (Asymptotics.isBigO_zero _ _).congr_left ?_
    intro m
    have h' : ((lbH0 k (lbPow L m) : ℕ) : ℝ) = ((topSelfIntersection k L 0 : ℤ) : ℝ) := by
      exact_mod_cast hz m
    rw [h']
    simp
  · have he : ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) := by push_cast; ring
    simp only [he, zpow_natCast]
    refine Asymptotics.IsBigO.of_bound ((C : ℝ) * (n + 1) * 2 ^ n / (n + 1).factorial) ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with m hm
    have h := hC m
    rw [Nat.add_sub_cancel] at h
    have hR : |((n + 1).factorial : ℝ) * (lbH0 k (lbPow L m) : ℝ) - (topSelfIntersection k L (n + 1) : ℝ) * (m : ℝ) ^ (n + 1)|
        ≤ (C : ℝ) * (((n : ℝ) + 1) * ((m : ℝ) + 1) ^ n) := by
      exact_mod_cast h
    have hf : (0 : ℝ) < (n + 1).factorial := by exact_mod_cast Nat.factorial_pos _
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hpow : ((m : ℝ) + 1) ^ n ≤ 2 ^ n * (m : ℝ) ^ n := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) n
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (m : ℝ) ^ n)]
    have key : (lbH0 k (lbPow L m) : ℝ) - (topSelfIntersection k L (n + 1) : ℝ) * (m : ℝ) ^ (n + 1) / ((n + 1).factorial : ℝ)
        = (((n + 1).factorial : ℝ) * (lbH0 k (lbPow L m) : ℝ) - (topSelfIntersection k L (n + 1) : ℝ) * (m : ℝ) ^ (n + 1))
          / ((n + 1).factorial : ℝ) := by
      field_simp
    rw [key, abs_div, abs_of_pos hf, div_le_iff₀ hf]
    have hrhs : (C : ℝ) * (n + 1) * 2 ^ n / ((n + 1).factorial : ℝ) * (m : ℝ) ^ n * ((n + 1).factorial : ℝ)
        = (C : ℝ) * (((n : ℝ) + 1) * (2 ^ n * (m : ℝ) ^ n)) := by
      field_simp
    rw [hrhs]
    calc _ ≤ (C : ℝ) * (((n : ℝ) + 1) * ((m : ℝ) + 1) ^ n) := hR
      _ ≤ _ := by gcongr

end GlobalTheory
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.NefRiemannRochStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
theorem _root_.GlobalTheory.T.nef_riemann_roch : GlobalTheory.Published.NefRiemannRoch := by
  first | exact @_root_.GlobalTheory.nefRiemannRoch | exact _root_.GlobalTheory.nefRiemannRoch | (intros; apply _root_.GlobalTheory.nefRiemannRoch <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.NefLineBundleNumericalTheoremsProof

section

@[expose] public section

set_option autoImplicit false

namespace GlobalTheory

theorem nefNumerics_outright : GlobalTheory.Published.NefNumerics :=
  GlobalTheory.Published.nefNumerics_of_product_of_riemannRoch GlobalTheory.T.nef_product_nonneg GlobalTheory.T.nef_riemann_roch

end GlobalTheory
end
end
