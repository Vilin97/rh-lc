module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ContinuousHermNormGroup
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.MahlerMul
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
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsScaleStable
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MahlerMinusConeIntegralIndep
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ChowDegree
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PSpecFirstHomog
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.TargetsProjRegularDens
import Mathlib.Algebra.MvPolynomial.Nilpotent

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MahlerMeasureOfProduct

section

@[expose] public section

set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton

theorem mahler_pow_mul {n e : ℕ} (h : HermNorm n) {q g : MvPolynomial (Fin e × Fin n) ℂ}
    (hq : q ≠ 0) (hg : g ≠ 0) (a : ℕ) :
    mahler h e (q ^ a * g) = (a : ℝ) * mahler h e q + mahler h e g := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ', mul_assoc, mahlerMul n e h _ _ hq (mul_ne_zero (pow_ne_zero _ hq) hg), ih]
    push_cast
    ring

theorem mahler_C_mul_prod_pow : ∀ (n e : ℕ) (h : HermNorm n) {ι : Type} (s : Finset ι) (q : ι → MvPolynomial (Fin e × Fin n) ℂ) (d : ι → ℕ) (a : ι → ℕ) (c : ℂ), c ≠ 0 → (∀ i ∈ s, q i ≠ 0 ∧ IsMultiHomog (d i) (q i)) → mahler h e (C c * ∏ i ∈ s, q i ^ a i) = Real.log ‖c‖ + ∑ i ∈ s, (a i : ℝ) * mahler h e (q i) := by
  classical
  intro n e h ι s q d a c hc hq
  revert hq
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp [mahler_C]
  · intro i s hi ih hq
    have hrest : ∀ j ∈ s, q j ≠ 0 ∧ IsMultiHomog (d j) (q j) := fun j hj => hq j (Finset.mem_insert_of_mem hj)
    have hne : C c * ∏ j ∈ s, q j ^ a j ≠ 0 :=
      mul_ne_zero (by simpa using hc) (Finset.prod_ne_zero_iff.2 fun j hj => pow_ne_zero _ (hrest j hj).1)
    rw [Finset.prod_insert hi, Finset.sum_insert hi, mul_left_comm (C c) (q i ^ a i),
      mahler_pow_mul h (hq i (Finset.mem_insert_self i s)).1 hne (a i), ih hrest]
    ring

end GlobalTheory.CompanionTheory.Ar.Short.Crofton
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MahlerMeasureOfProductStatement

section

@[expose] public section

set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal


theorem _root_.GlobalTheory.T.mahler_measure_of_product : ∀ (n e : ℕ) (h : HermNorm n) {ι : Type} (s : Finset ι) (q : ι → MvPolynomial (Fin e × Fin n) ℂ) (d : ι → ℕ) (a : ι → ℕ) (c : ℂ), c ≠ 0 → (∀ i ∈ s, q i ≠ 0 ∧ IsMultiHomog (d i) (q i)) → mahler h e (C c * ∏ i ∈ s, q i ^ a i) = Real.log ‖c‖ + ∑ i ∈ s, (a i : ℝ) * mahler h e (q i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Short.Crofton.mahler_C_mul_prod_pow | exact GlobalTheory.CompanionTheory.Ar.Short.Crofton.mahler_C_mul_prod_pow | (intros; apply GlobalTheory.CompanionTheory.Ar.Short.Crofton.mahler_C_mul_prod_pow <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MahlerMinusConeIntegralIndepStatement

section

@[expose] public section

set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal


theorem _root_.GlobalTheory.T.mahler_minus_cone_integral_indep : ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
  (g : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (u u' : Fin n → ℂ),
  IsProjPrime W → IsChowForm W (e + 1) g → IsMultiHomog δ g → linForm u ∉ W → linForm u' ∉ W →
    mahler h e (specFirst g u) - coneIntegral h W e (fsLog h u) =
      mahler h e (specFirst g u') - coneIntegral h W e (fsLog h u') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Short.Crofton.defect_eq_of_linForm_notMem | exact GlobalTheory.CompanionTheory.Ar.Short.Crofton.defect_eq_of_linForm_notMem | (intros; apply GlobalTheory.CompanionTheory.Ar.Short.Crofton.defect_eq_of_linForm_notMem <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MahlerSectionStatementHolds

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Short

open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial

theorem mahlerDefect_eq_sum {n e δ : ℕ} (h : HermNorm n) {Z : ProjCycle ℂ n}
    {f : MvPolynomial (Fin (e + 1) × Fin n) ℂ} (hd : IsChowCycleData Z e δ f) :
    ∃ (c : ℂ) (g : Ideal (MvPolynomial (Fin n) ℂ) → MvPolynomial (Fin (e + 1) × Fin n) ℂ)
      (d : Ideal (MvPolynomial (Fin n) ℂ) → ℕ),
      (∀ W ∈ Z.support, IsChowForm W (e + 1) (g W) ∧ IsMultiHomog (d W) (g W)) ∧
      ∀ u : Fin n → ℂ, IsAdmissible Z u →
        mahlerDefect h e Z f u = Real.log ‖c‖ + ∑ W ∈ Z.support, (Z W : ℝ) *
          (mahler h e (specFirst (g W) u) - coneIntegral h W e (fsLog h u)) := by
  obtain ⟨c, hc, g, hg, hf⟩ := hd.chow
  have hf0 : C c * ∏ W ∈ Z.support, g W ^ Z W ≠ 0 :=
    mul_ne_zero (C_ne_zero.mpr hc)
      (Finset.prod_ne_zero_iff.mpr fun W hW => pow_ne_zero _ (hg W hW).1)
  have hhom : IsMultiHomog δ (C c * ∏ W ∈ Z.support, g W ^ Z W) := hf ▸ hd.homog
  obtain ⟨d, hdW, -⟩ := exists_degrees_of_chowFormCycle (Nat.succ_pos e) Z c g hg hhom hf0
  refine ⟨c, g, d, fun W hW => ⟨hg W hW, hdW W hW⟩, fun u hu => ?_⟩
  have hspec : specFirst f u = C c * ∏ W ∈ Z.support, specFirst (g W) u ^ Z W := by
    rw [hf]
    simp only [specFirst, map_mul, map_prod, map_pow, bind₁_C_right]
  have hq : ∀ W ∈ Z.support, specFirst (g W) u ≠ 0 ∧ IsMultiHomog (d W) (specFirst (g W) u) :=
    fun W hW => ⟨SpecFirstNe.full ℂ n e W (g W) u (hd.prime W hW) (hg W hW) (hu W hW),
      SpecFirstHomog.proof n e (d W) (g W) u (hdW W hW)⟩
  rw [mahlerDefect, hspec, GlobalTheory.T.mahler_measure_of_product n e h Z.support (fun W => specFirst (g W) u) d (fun W => Z W) c hc hq,
    cycleIntegral]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

theorem defectConstDim (e : ℕ) : DefectConstDim e := by
  intro n δ h Z f u u' hd hu hu'
  obtain ⟨c, g, d, hg, hsum⟩ := mahlerDefect_eq_sum h hd
  have hW : ∀ W ∈ Z.support, (Z W : ℝ) * (mahler h e (specFirst (g W) u) - coneIntegral h W e (fsLog h u)) =
      (Z W : ℝ) * (mahler h e (specFirst (g W) u') - coneIntegral h W e (fsLog h u')) := fun W hW => by
    have := GlobalTheory.T.mahler_minus_cone_integral_indep n e (d W) h W (g W) u u' (hd.prime W hW) (hg W hW).1 (hg W hW).2 (hu W hW)
      (hu' W hW)
    rw [this]
  rw [hsum u hu, hsum u' hu', Finset.sum_congr rfl hW]

theorem mahlerSection : GroundTheory.Heights₂.Heights.MahlerSection.Statement := by
  intro n e δ h Z f u hp hc hm ha
  exact GroundTheory.Heights₂.Heights.AutoClose.MahlerSectionOfConst e (defectConstDim e) n δ h Z f u ⟨hp, hc, hm⟩ ha

end GlobalTheory.CompanionTheory.Ar.Short
end
end
