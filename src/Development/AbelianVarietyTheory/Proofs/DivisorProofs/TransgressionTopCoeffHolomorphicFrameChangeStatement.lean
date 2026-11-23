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

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedTopChernCoeffConj

section

@[expose] public section

set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem sum_prod_perm_mul_comm {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (A : Fin n → Matrix r r ℂ)
    (P : Matrix r r ℂ) (π : Equiv.Perm (Fin n)) :
    ∑ p : Fin n → r, ∏ i, (A i * P) (p i) (p (π i)) = ∑ p : Fin n → r, ∏ i, (P * A i) (p i) (p (π i)) := by
  simp only [Matrix.mul_apply]
  have h1 : ∀ f : Fin n → r → ℂ, ∏ i, ∑ j, f i j = ∑ s : Fin n → r, ∏ i, f i (s i) := fun f => by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  simp only [h1]
  rw [Finset.sum_comm]
  symm
  refine Fintype.sum_equiv (Equiv.arrowCongr π.symm (Equiv.refl r)) _ _ fun t => ?_
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Finset.prod_mul_distrib, Equiv.arrowCongr_apply, Equiv.symm_symm, Equiv.coe_refl, Function.comp, id]
  rw [mul_comm, Equiv.prod_comp π fun i => P (t i) (p i)]

theorem mixTop_conj {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K : Fin n → EndValuedForm11Coeffs n r) (P : Matrix r r ℂ)
    (hP : IsUnit P.det) : mixTop (fun i a b => P⁻¹ * K i a b * P) = mixTop K := by
  unfold mixTop
  congr 1
  have hdet : ∀ M : Fin n → Fin n → ℂ, (Matrix.of M).det =
      ∑ w : Equiv.Perm (Fin n), ((Equiv.Perm.sign w : ℤ) : ℂ) * ∏ i, M i (w i) := fun M => by
    rw [← Matrix.det_transpose, Matrix.det_apply']
    simp
  simp only [hdet, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [← Finset.mul_sum]
  congr 2
  rw [sum_prod_perm_mul_comm (fun i => P⁻¹ * K i (u i) (w i)) P π]
  simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv P hP, Matrix.one_mul]

end GlobalTheory.GoodTop
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedTopChernCoeffConjStatement

section

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.polarisedTopChernCoeff_conj : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K : Fin n → EndValuedForm11Coeffs n r) (P : Matrix r r ℂ), IsUnit P.det → mixTop (fun i a b => P⁻¹ * K i a b * P) = mixTop K := by
  first | exact @GlobalTheory.GoodTop.mixTop_conj | exact GlobalTheory.GoodTop.mixTop_conj | (intros; apply GlobalTheory.GoodTop.mixTop_conj <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionTopCoeffHolomorphicFrameChange

section

@[expose] public section

set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem corrC_changeFrame {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (ρ : V n → ℝ)
    {G₀ G₁ A : V n → Matrix r r ℂ} {v : V n} (h₀ : MContDiffAt 2 G₀ v) (u₀ : IsUnit (G₀ v).det)
    (h₁ : MContDiffAt 2 G₁ v) (u₁ : IsUnit (G₁ v).det) (hA : MContDiffAt 2 A v) (hAu : IsUnit (A v).det)
    (hA0 : ∀ᶠ x in 𝓝 v, ∀ η, mdbar A x η = 0) :
    corrC ρ (fun x => (A x)ᵀ * G₀ x * (A x)ᴴᵀ) (fun x => (A x)ᵀ * G₁ x * (A x)ᴴᵀ) v = corrC ρ G₀ G₁ v := by
  unfold corrC
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← GlobalTheory.T.polarisedTopChernCoeff_conj (intersection_update_fsHerm_neg_one (curvAt G₁ v) (cutForm ρ G₀ G₁ v) (curvAt G₀ v) j) (A v) hAu]
  congr 1
  funext i a b
  unfold intersection_update_fsHerm_neg_one
  split_ifs
  · exact curv_changeFrame h₁ u₁ hA hAu hA0 _ _
  · simp only [cutForm]
    rw [conn_changeFrame (h₁.of_le one_le_two) u₁ (hA.of_le one_le_two) hAu hA0.self_of_nhds,
      conn_changeFrame (h₀.of_le one_le_two) u₀ (hA.of_le one_le_two) hAu hA0.self_of_nhds,
      ← Matrix.mul_sub, add_sub_add_right_eq_sub, ← Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_assoc]
  · exact curv_changeFrame h₀ u₀ hA hAu hA0 _ _

end GlobalTheory.GoodTop
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionTopCoeffHolomorphicFrameChangeStatement

section

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.transgressionTopCoeff_holomorphic_frame_change : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (ρ : V n → ℝ) {G₀ G₁ A : V n → Matrix r r ℂ} {v : V n}, MContDiffAt 2 G₀ v → IsUnit (G₀ v).det → MContDiffAt 2 G₁ v → IsUnit (G₁ v).det → MContDiffAt 2 A v → IsUnit (A v).det → (∀ᶠ x in 𝓝 v, ∀ η, mdbar A x η = 0) → corrC ρ (fun x => (A x)ᵀ * G₀ x * (A x)ᴴᵀ) (fun x => (A x)ᵀ * G₁ x * (A x)ᴴᵀ) v = corrC ρ G₀ G₁ v := by
  first | exact @GlobalTheory.GoodTop.corrC_changeFrame | exact GlobalTheory.GoodTop.corrC_changeFrame | (intros; apply GlobalTheory.GoodTop.corrC_changeFrame <;> assumption)
end
end
