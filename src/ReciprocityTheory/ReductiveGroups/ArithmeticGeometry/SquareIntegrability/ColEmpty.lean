module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GaussianTailBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PropASt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColAbel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColTorus
public import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Bernstein

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.EpsilonLeHalf

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex NumberField

noncomputable section

theorem epsilon_le_half {E : Type} [Field E] [NumberField E] {X : PT E} {DF : ℕ} (P : Par X DF) :
    P.eps1 ≤ 1 / 2 := by
  have h6 := P.C6
  have hr0 : (0:ℝ) ≤ X.r := Nat.cast_nonneg _
  have hr : 0 ≤ (X.r : ℝ) * Real.log X.r := mul_nonneg hr0 (Real.log_natCast_nonneg _)
  have hrest : 0 ≤ ((DF : ℝ) + 1) * (X.r * Real.log X.r + 3 * X.r + 3) :=
    mul_nonneg (by positivity) (by linarith)
  have e1 := Real.exp_one_gt_d9
  have e2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  have e3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  have p2 : (2.7:ℝ) ^ 2 ≤ Real.exp 1 ^ 2 := by gcongr; linarith
  have p3 : (2.7:ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := by gcongr; linarith
  have hl43 : Real.log 4.3 ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by norm_num), e2]
    norm_num at p2
    linarith
  have hl14 : Real.log 7 + Real.log 2 ≤ 3 := by
    rw [← Real.log_mul (by norm_num) (by norm_num), Real.log_le_iff_le_exp (by norm_num), e3]
    norm_num at p3
    linarith
  have hds : (dstar (E := E) P.m : ℝ) * Real.log 4.3 ≤ 2 * dstar (E := E) P.m := by
    have h := mul_le_mul_of_nonneg_left hl43 (Nat.cast_nonneg (α := ℝ) (dstar (E := E) P.m))
    linarith
  have key : (7:ℝ) * 2 ^ X.gA * (4.3:ℝ) ^ dstar (E := E) P.m =
      Real.exp (Real.log 7 + X.gA * Real.log 2 + dstar (E := E) P.m * Real.log 4.3) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num), Real.exp_nat_mul, Real.exp_nat_mul,
      Real.exp_log (by norm_num), Real.exp_log (by norm_num)]
  unfold Par.eps1
  rw [key, ← Real.exp_add]
  have half : (1:ℝ) / 2 = Real.exp (-Real.log 2) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  rw [half, Real.exp_le_exp]
  linarith

end

end ReciprocityTheory.ChartRestriction.G.I2
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColEmpty

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex

theorem colTorus (hx : Ext.All) (hA : PropAStatement) (hS : GSupStatement) : ColTorusStatement := by
  obtain ⟨hP, hGT, -⟩ := hx
  intro E _ _ _ X DF P I hI c hc σ x0 u hx0 hu n hn hun hc6
  exact ct_core hP hGT hA hS hI c hc σ x0 u hx0 hu n hn hun hc6

theorem colAbel (hx : Ext.All) (hA : PropAStatement) (hS : GSupStatement) : ColAbelStatement := by
  obtain ⟨hP, hGT, -⟩ := hx
  intro E _ _ _ X DF P I hI c hc σ ξ _ hξ1 hξI
  exact cab_core hP hGT hA hS hI c hc σ ξ hξ1 hξI

theorem colEmpty (hx : Ext.All) (hA : PropAStatement) (hS : GSupStatement) : ColEmptyStatement := by
  obtain ⟨hP, hGT, -⟩ := hx
  intro E _ _ _ X DF P I hI
  obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hM : 0 ≤ M1 (E := E) P.m := by
    unfold M1 PT.rd
    positivity
  have hu0 : IsU I (0 : Vsp X.dim) 0 := ⟨Submodule.zero_mem _, fun a _ => by simp [Hf]⟩
  obtain ⟨s', hs', ζ, hζ, hd, hl⟩ := ct_core hP hGT hA hS hI 0 (Nat.zero_le _) σ 0 0
    (Submodule.zero_mem _) hu0 1 le_rfl (by norm_num)
    (fun y _ uy _ => by simpa using mul_nonneg hM (sq_nonneg ‖uy‖))
  have h0 := hd Fin.elim0 (fun k => k.elim0)
  simp only [d1, iteratedFDeriv_zero_apply, pow_zero, Finset.univ_eq_empty, Finset.prod_empty,
    mul_one] at h0
  refine ⟨s', hs', ?_, by simpa using hl⟩
  have h1 := norm_sub_norm_le ζ (s' 0)
  rw [norm_sub_rev] at h1
  have h2 := epsilon_le_half P
  linarith

end ReciprocityTheory.ChartRestriction.G.I2
end
end
