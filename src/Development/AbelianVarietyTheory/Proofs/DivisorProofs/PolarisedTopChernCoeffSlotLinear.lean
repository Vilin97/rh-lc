module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedTopChernCoeffUpdateAdd

section

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

set_option autoImplicit false

namespace GlobalTheory.GoodTop

theorem mixTop_update_add : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K : Fin n → EndValuedForm11Coeffs n r) (j : Fin n) (L L' : EndValuedForm11Coeffs n r), mixTop (Function.update K j (L + L')) = mixTop (Function.update K j L) + mixTop (Function.update K j L') := by
  intro n r _ _ K j L L'
  have key : ∀ (M : EndValuedForm11Coeffs n r) (p : Fin n → r) (π u : Equiv.Perm (Fin n)),
      (Matrix.of fun i b => Function.update K j M i (u i) b (p i) (p (π i))) =
        (Matrix.of fun i b => K i (u i) b (p i) (p (π i))).updateRow j
          (fun b => M (u j) b (p j) (p (π j))) := by
    intro M p π u
    ext i b
    by_cases h : i = j
    · subst h
      simp
    · simp [Matrix.updateRow_ne h, Function.update_of_ne h]
  unfold mixTop
  rw [← mul_add]
  congr 1
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun π _ => Finset.sum_congr rfl fun u _ => ?_
  rw [key, key, key, ← mul_add, ← Matrix.det_updateRow_add]
  rfl

end GlobalTheory.GoodTop
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedTopChernCoeffUpdateAddStatement

section

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.polarisedTopChernCoeff_update_add : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K : Fin n → EndValuedForm11Coeffs n r) (j : Fin n) (L L' : EndValuedForm11Coeffs n r), mixTop (Function.update K j (L + L')) = mixTop (Function.update K j L) + mixTop (Function.update K j L') := by
  first | exact @GlobalTheory.GoodTop.mixTop_update_add | exact GlobalTheory.GoodTop.mixTop_update_add | (intros; apply GlobalTheory.GoodTop.mixTop_update_add <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedTopChernCoeffUpdateSmul

section

@[expose] public section

set_option autoImplicit false

open GlobalTheory.GoodTop

namespace GlobalTheory.GoodTop

theorem mixTop_update_smul {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K : Fin n → EndValuedForm11Coeffs n r) (j : Fin n)
    (t : ℂ) (L : EndValuedForm11Coeffs n r) :
    mixTop (Function.update K j (t • L)) = t * mixTop (Function.update K j L) := by
  have key : ∀ (M : EndValuedForm11Coeffs n r) (p : Fin n → r) (π u : Equiv.Perm (Fin n)),
      (Matrix.of fun i b => Function.update K j M i (u i) b (p i) (p (π i))) =
        (Matrix.of fun i b => K i (u i) b (p i) (p (π i))).updateRow j
          (fun b => M (u j) b (p j) (p (π j))) := by
    intro M p π u
    ext i b
    by_cases h : i = j
    · subst h; simp
    · simp [Matrix.updateRow_ne h, Function.update_of_ne h]
  have h2 : ∀ (p : Fin n → r) (π u : Equiv.Perm (Fin n)),
      (Matrix.of fun i b => Function.update K j (t • L) i (u i) b (p i) (p (π i))).det =
        t * (Matrix.of fun i b => Function.update K j L i (u i) b (p i) (p (π i))).det := by
    intro p π u
    rw [key, key, ← Matrix.det_updateRow_smul]
    rfl
  unfold mixTop
  simp only [h2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun π _ => Finset.sum_congr rfl fun u _ => ?_
  ring

end GlobalTheory.GoodTop
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedTopChernCoeffUpdateSmulStatement

section

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.polarisedTopChernCoeff_update_smul : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K : Fin n → EndValuedForm11Coeffs n r) (j : Fin n) (t : ℂ) (L : EndValuedForm11Coeffs n r), mixTop (Function.update K j (t • L)) = t * mixTop (Function.update K j L) := by
  first | exact @GlobalTheory.GoodTop.mixTop_update_smul | exact GlobalTheory.GoodTop.mixTop_update_smul | (intros; apply GlobalTheory.GoodTop.mixTop_update_smul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedTopChernCoeffSlotLinear

section

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem position_eq_update {n : ℕ} {α : Type} [Zero α] (K₁ L K₀ : α) (j : Fin n) :
    intersection_update_fsHerm_neg_one K₁ L K₀ j = Function.update (intersection_update_fsHerm_neg_one K₁ 0 K₀ j) j L := by
  funext i
  by_cases h : i = j
  · subst h; simp [intersection_update_fsHerm_neg_one]
  · simp [intersection_update_fsHerm_neg_one, Function.update_of_ne h, h]

theorem mixTop_position_linear {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K₁ K₀ L L' : EndValuedForm11Coeffs n r)
    (s t : ℂ) (j : Fin n) :
    mixTop (intersection_update_fsHerm_neg_one K₁ (s • L + t • L') K₀ j) = s * mixTop (intersection_update_fsHerm_neg_one K₁ L K₀ j) + t * mixTop (intersection_update_fsHerm_neg_one K₁ L' K₀ j) := by
  rw [position_eq_update, position_eq_update K₁ L, position_eq_update K₁ L', GlobalTheory.T.polarisedTopChernCoeff_update_add, GlobalTheory.T.polarisedTopChernCoeff_update_smul, GlobalTheory.T.polarisedTopChernCoeff_update_smul]

end GlobalTheory.GoodTop
end
end
