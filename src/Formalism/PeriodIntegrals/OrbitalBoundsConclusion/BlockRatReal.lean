module

public import Formalism.PeriodIntegrals.BlockRatReal
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RationalRealBlocks.EvenStep
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
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RationalRealBlocks.MapDetGenM
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RationalRealBlocks.Bridge
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Formalism.GradedWeylDivisibility.StatementA

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RationalRealBlocks.AntitoneStar

section

@[expose] public section

open MvPolynomial Matrix

noncomputable section

namespace PI.BlockRatReal

theorem reM_rfl {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) : reM (m := m) rfl A = A := by
  ext i j
  rfl

theorem detShift_eq {m : ℕ} (w : Fin (m + 1) → ℤ) : detShift w = w (Fin.last m) := by
  rw [detShift, dite_eq_left (Nat.succ_pos m)]
  rfl

theorem natW_eq {m : ℕ} (w : Fin (m + 1) → ℤ) : natW w = nuOf w := by
  funext i
  rw [natW, nuOf, detShift_eq]

theorem antitone_star {m : ℕ} {lam : Fin (m + 1) → ℤ} (h : Antitone lam) : Antitone fun i : Fin (m + 1) => -lam i.rev :=
  fun _ _ hij => neg_le_neg (h (Fin.rev_le_rev.mpr hij))

theorem stmt_of (hE : EvenStep) (hO : OddStep) : Stmt := by
  intro nV n' m lam0 Tau _ n LL _ h pos G M embLL lam hanti htie hM
  subst h
  intro v s f hf
  set τ := pos ⟨v, s⟩ with hτ
  have hl : lam0 v s = lam τ := funext fun i => by rw [htie v s i]; rfl
  obtain ⟨M0, hM0⟩ := hM τ
  have hf' : f ∈ weyl ℤ (m + 1) (m + 1) le_rfl (nuOf (lam τ)) := by
    rw [← natW_eq]; exact hf
  by_cases hs : Even s.val
  · have hla : lamAt (lam0 v) s = lam τ := by rw [lamAt, if_pos hs, hl]
    obtain ⟨F, hF, hFe⟩ := hE m LL embLL (lam τ) (hanti τ) M0 f hf'
    refine ⟨F, ?_, fun y => ?_⟩
    · rw [blkMod, hla, if_pos (hanti τ)]; exact hF
    · have h1 := hFe (y.1 τ) (y.2 τ)
      rw [zAt, if_pos hs, reM_rfl, eAt, hla, detShift_eq, hM0]
      exact h1
  · have hla : lamAt (lam0 v) s = fun i => -lam τ i.rev := by rw [lamAt, if_neg hs, hl]
    obtain ⟨F, hF, hFe⟩ := hO m LL embLL (lam τ) (hanti τ) M0 f hf'
    refine ⟨F, ?_, fun y => ?_⟩
    · rw [blkMod, hla, if_pos (antitone_star (hanti τ))]; exact hF
    · have h1 := hFe (y.1 τ) (y.2 τ)
      rw [zAt, if_neg hs, reM_rfl, eAt, hla, detShift_eq, hM0]
      exact h1

end PI.BlockRatReal
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RationalRealBlocks.NuOfAntitone

section

@[expose] public section

open MvPolynomial Matrix

noncomputable section

namespace PI.BlockRatReal.UnitaryGroupMassFormula

theorem nuOf_antitone {m : ℕ} {lam : Fin (m + 1) → ℤ} (h : Antitone lam) : Antitone (nuOf lam) := by
  intro a b hab
  have h1 := h hab
  exact Int.toNat_le_toNat (by omega)

theorem det_map_ne {LL : Type} [Field LL] (embLL : LL →+* ℂ) {k : ℕ} (M0 : GL (Fin k) LL) :
    (M0.1.map embLL).det ≠ 0 := by
  have hu : IsUnit M0.1.det := (Matrix.isUnit_iff_isUnit_det _).mp M0.isUnit
  have hm := RingHom.map_det embLL M0.1
  rw [RingHom.mapMatrix_apply] at hm
  rw [← hm]
  exact (map_ne_zero embLL).mpr hu.ne_zero

theorem evenStep : EvenStep := by
  intro m LL _ embLL lam hl M0 f hf
  refine ⟨C (M0.1.det ^ (-lam (Fin.last m))) * Formalism.GradedWeylDivisibility.rowAct LL (↑M0⁻¹ : Matrix (Fin (m + 1)) (Fin (m + 1)) LL)
    (MvPolynomial.map (Int.castRingHom LL) f), ?_, fun y _ => ?_⟩
  · rw [MvPolynomial.C_mul']
    exact Submodule.smul_mem _ _ (s2 _ _ _ _ (s1 _ _ _ (nuOf_antitone hl) f hf))
  · have hd := det_map_ne embLL M0
    have hmul : (↑M0⁻¹ : Matrix (Fin (m + 1)) (Fin (m + 1)) LL).map embLL * (M0.1.map embLL * y) = y := by
      rw [← Matrix.mul_assoc, ← Matrix.map_mul, M0.inv_mul, Matrix.map_one embLL (map_zero _) (map_one _),
        Matrix.one_mul]
    have hc : embLL (M0.1.det ^ (-lam (Fin.last m))) = (M0.1.map embLL).det ^ (-lam (Fin.last m)) := by
      rw [map_zpow₀, RingHom.map_det, RingHom.mapMatrix_apply]
    rw [map_mul, map_C, eval_mul, eval_C, eval_map_rowAct, hmul, map_map_int, hc, Matrix.det_mul, mul_zpow,
      _root_.zpow_neg]
    field_simp

end PI.BlockRatReal.UnitaryGroupMassFormula
end
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BlockRatReal

section

@[expose] public section

theorem blockRatReal : PI.BlockRatReal.Stmt :=
  PI.BlockRatReal.stmt_of PI.BlockRatReal.UnitaryGroupMassFormula.evenStep PI.BlockRatReal.UnitaryGroupMassFormula.Odd.oddStep
end
end
