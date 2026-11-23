module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHR
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHDim
public import Formalism.PeriodIntegrals.LongWeylElementSquare
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaussianUniqueness.GaussUniqMain
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SwPhiDeriv
import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SwSandwichOf

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BigCellConjugation.Monomial

section

@[expose] public section

noncomputable section

open Matrix

namespace PI.SwBig.BigCellGProof

open PI.SwBig

def rhoB (k r : ℕ) (j : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if j.val < r ∨ r + k < j.val then ⟨2 * r + k - j.val, by omega⟩ else j

theorem bigCell_one_apply (k r : ℕ) (c : Fin r → ℂ) (i j : Fin (2 * r + k + 1)) :
    bigCell k r c 1 i j = if i = rhoB k r j then tv k r c j else 0 := by
  unfold bigCell rhoB tv esI
  rcases lt_or_ge j.val r with h1 | h1
  · have ho : j.val < r ∨ r + k < j.val := Or.inl h1
    rw [dite_eq_left h1, if_pos ho, dite_eq_left h1]
  · rcases le_or_gt j.val (r + k) with h2 | h2
    · have ho : ¬ (j.val < r ∨ r + k < j.val) := by omega
      rw [dite_eq_right (show ¬ (j.val < r) by omega), dite_eq_left h2, if_neg ho, dite_eq_right (show ¬ (j.val < r) by omega), dite_eq_left h2]
      by_cases hij : i = j
      · subst hij
        rw [dite_eq_left ⟨h1, h2⟩, if_pos rfl, Matrix.one_apply, if_pos rfl]
      · rw [if_neg hij]
        split_ifs with hi
        · rw [Matrix.one_apply, if_neg]
          intro h
          apply hij
          apply Fin.ext
          have := congrArg Fin.val h
          simp only at this
          omega
        · rfl
    · have ho : j.val < r ∨ r + k < j.val := Or.inr h2
      rw [dite_eq_right (show ¬ (j.val < r) by omega), dite_eq_right (show ¬ (j.val ≤ r + k) by omega), if_pos ho,
        dite_eq_right (show ¬ (j.val < r) by omega), dite_eq_right (show ¬ (j.val ≤ r + k) by omega)]
      by_cases hi : i.val = 2 * r + k - j.val
      · rw [if_pos hi, if_pos (Fin.ext hi)]
      · rw [if_neg hi, if_neg (fun h => hi (congrArg Fin.val h))]

theorem Hpk_rhoB (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    Hpk k r (rhoB k r i) (rhoB k r j) = Hpk k r i j := by
  have hv : ∀ x : Fin (2 * r + k + 1), (rhoB k r x).val =
      if x.val < r ∨ r + k < x.val then 2 * r + k - x.val else x.val := by
    intro x
    unfold rhoB
    split_ifs <;> rfl
  have hi := i.isLt
  have hj := j.isLt
  unfold Hpk
  simp only [Fin.ext_iff, hv]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem tv_Hpk_tv (k r : ℕ) (c : Fin r → ℂ) (hc : ∀ a, c a ≠ 0) (i j : Fin (2 * r + k + 1)) :
    star (tv k r c i) * Hpk k r i j * tv k r c j = Hpk k r i j := by
  by_cases hz : Hpk k r i j = 0
  · simp [hz]
  have key : (i.val < r ∧ i.val + j.val = 2 * r + k) ∨ (j.val < r ∧ i.val + j.val = 2 * r + k) ∨
      (r ≤ i.val ∧ i.val ≤ r + k ∧ i = j) := by
    unfold Hpk at hz
    split_ifs at hz <;> first | tauto | simp at hz
  rcases key with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, rfl⟩
  · have hH : Hpk k r i j = 1 := by unfold Hpk; rw [if_pos ⟨h1, h2⟩]
    have hti : tv k r c i = c ⟨i.val, h1⟩ := by unfold tv; rw [dite_eq_left h1]
    have htj : tv k r c j = (star (c ⟨i.val, h1⟩))⁻¹ := by
      have e : (⟨2 * r + k - j.val, by omega⟩ : Fin r) = ⟨i.val, h1⟩ :=
        Fin.ext (show 2 * r + k - j.val = i.val by omega)
      unfold tv
      rw [dite_eq_right (show ¬ (j.val < r) by omega), dite_eq_right (show ¬ (j.val ≤ r + k) by omega), e]
    rw [hti, htj, hH, mul_one, mul_inv_cancel₀ (star_ne_zero.mpr (hc _))]
  · have hH : Hpk k r i j = 1 := by unfold Hpk; rw [if_neg (by omega), if_pos ⟨h1, h2⟩]
    have htj : tv k r c j = c ⟨j.val, h1⟩ := by unfold tv; rw [dite_eq_left h1]
    have hti : tv k r c i = (star (c ⟨j.val, h1⟩))⁻¹ := by
      have e : (⟨2 * r + k - i.val, by omega⟩ : Fin r) = ⟨j.val, h1⟩ :=
        Fin.ext (show 2 * r + k - i.val = j.val by omega)
      unfold tv
      rw [dite_eq_right (show ¬ (i.val < r) by omega), dite_eq_right (show ¬ (i.val ≤ r + k) by omega), e]
    rw [hti, htj, hH]
    simp [hc]
  · have hti : tv k r c i = 1 := by unfold tv; rw [dite_eq_right (by omega), dite_eq_left h2]
    rw [hti]
    simp

theorem conjTranspose_mul_mul_monomial {n : Type*} [Fintype n] [DecidableEq n]
    (g H : Matrix n n ℂ) (ρ : n → n) (v : n → ℂ)
    (hg : ∀ b j, g b j = if b = ρ j then v j else 0) (i j : n) :
    (gᴴ * H * g) i j = star (v i) * H (ρ i) (ρ j) * v j := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hg]
  simp [apply_ite star, Finset.sum_ite_eq', ite_mul, mul_ite, Finset.sum_mul]

theorem bigCellG : BigCellG := by
  intro k r c hc
  show (bigCell k r c 1)ᴴ * Hpk k r * bigCell k r c 1 = Hpk k r
  ext i j
  rw [conjTranspose_mul_mul_monomial _ _ (rhoB k r) (tv k r c) (bigCell_one_apply k r c), Hpk_rhoB,
    tv_Hpk_tv k r c hc]

end PI.SwBig.BigCellGProof
end
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SwBigCellG

section

@[expose] public section

theorem big_cell_g : PI.SwBig.BigCellG := PI.SwBig.BigCellGProof.bigCellG
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SwGaussUniq

section

@[expose] public section

theorem gauss_sum_unique : PI.SwBig.GaussUniq := PI.SwBig.GU.gaussUniq_main
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PhiBigCellForm.BigCellEqW0BMulTM

section

@[expose] public section

noncomputable section

open Matrix

namespace PI.SwBig.PhiFormProof

open PI.SwBig

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

theorem bigCell_eq_w0B_mul_tM (k r : ℕ) (c : Fin r → ℂ) :
    bigCell k r c 1 = w0B k r * tM k r c := by
  ext i j
  simp only [w0B, tM, Matrix.mul_diagonal, bigCell, tv]
  split_ifs <;> simp_all

theorem exp_neg_eq_inv (k r : ℕ) (X : Mat k r) :
    NormedSpace.exp (-X) = (NormedSpace.exp X)⁻¹ :=
  Matrix.exp_neg X

theorem phiForm : PhiForm := by
  intro k r X x Z X'
  rw [Phi, exp_neg_eq_inv, bigCell_eq_w0B_mul_tM]
  simp only [Matrix.mul_assoc]

end PI.SwBig.PhiFormProof
end
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SwPhiForm

section

@[expose] public section

theorem phi_form' : PI.SwBig.PhiForm := PI.SwBig.PhiFormProof.phiForm
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstSandwich

section

@[expose] public section

namespace Formalism.L2.SG.Pf.BH

theorem sandwich' : Sandwich := by
  refine sandwich_of_chart Sw.lieG' Sw.lieWb' gauss_sum_unique phi_form' big_cell_g
    (phiDeriv_of Sw.w0Sq) Sw.lIso Sw.w0Sq ?_ ?_
  · unfold PI.SwSand.LieEN
    intros
    exact Formalism.MainNotions.BridgeCSB.lieE_N
  · intros
    apply Formalism.MainNotions.BridgeCSB.exp_mem_N

end Formalism.L2.SG.Pf.BH
end
end
