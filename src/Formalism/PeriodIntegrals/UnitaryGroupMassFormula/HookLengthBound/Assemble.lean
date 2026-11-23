module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HookLengthBound.DetShiftNormOf
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LGradedLemmas
public import Formalism.PieriBlockIdeals.PieriColumnMinors.HeightDescentMinors
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HookLengthBound.DeterminantAdjugate
import Mathlib.Tactic.Linter.Style
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HookLengthBound.ProdFactorialLe

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HookLengthBound.DetShift

section

@[expose] public section

open MvPolynomial Formalism.GradedWeylDivisibility

noncomputable section

namespace PI.HookSteps

variable {N : ℕ}

theorem rowGen_coeff_zero (a b : Fin N) (f : MvPolynomial (Fin N × Fin N) ℚ) :
    (rowGen ℚ a b f).coeff 0 = f := by
  induction f using MvPolynomial.induction_on
  · next c =>
    simp [rowGen, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
  · next p q hp hq =>
    rw [map_add (f := _), Polynomial.coeff_add, hp, hq]
  · next p v hp =>
    rw [map_mul, Polynomial.mul_coeff_zero, hp]
    simp only [rowGen, MvPolynomial.aeval_X]
    split_ifs <;> simp

theorem rowDiv_one_mul_X (a b : Fin N) (p : MvPolynomial (Fin N × Fin N) ℚ) (v : Fin N × Fin N) :
    rowDiv ℚ a b 1 (p * X v) = rowDiv ℚ a b 1 p * X v + p * (if v.1 = b then X (a, v.2) else 0) := by
  have hX : rowGen ℚ a b (X v : MvPolynomial (Fin N × Fin N) ℚ) = Polynomial.C (X v) +
      (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0) := by
    simp only [rowGen, MvPolynomial.aeval_X]
  have h0 := rowGen_coeff_zero a b p
  simp only [rowDiv, map_mul, hX, Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, Finset.sum_range_zero, zero_add, h0]
  split_ifs with h <;> simp [Polynomial.coeff_C, Polynomial.coeff_X_mul, add_comm]

theorem polE_apply (a b : Fin N) (f : MvPolynomial (Fin N × Fin N) ℚ) :
    polE N a b f = ∑ s : Fin N, X (a, s) * pderiv (b, s) f := by
  simp [polE, LinearMap.sum_apply]

theorem polE_mul_X (a b : Fin N) (p : MvPolynomial (Fin N × Fin N) ℚ) (v : Fin N × Fin N) :
    polE N a b (p * X v) = polE N a b p * X v + p * (if v.1 = b then X (a, v.2) else 0) := by
  have key : ∀ s : Fin N, X (a, s) * pderiv (b, s) (p * X v) =
      X (a, s) * pderiv (b, s) p * X v + p * (if v = (b, s) then X (a, s) else 0) := by
    intro s
    rw [Derivation.leibniz, MvPolynomial.pderiv_X, Pi.single_apply]
    split_ifs <;> simp only [smul_eq_mul] <;> ring
  have hs : (∑ s : Fin N, (if v = (b, s) then (X (a, s) : MvPolynomial (Fin N × Fin N) ℚ) else 0)) =
      if v.1 = b then X (a, v.2) else 0 := by
    obtain ⟨v1, v2⟩ := v
    by_cases h : v1 = b
    · subst h
      simp [Prod.ext_iff, eq_comm]
    · simp [h]
  rw [polE_apply, polE_apply, Finset.sum_mul]
  simp only [key, Finset.sum_add_distrib, ← Finset.mul_sum, hs]

theorem polynomial_eq_divisibility : PolEqRowDiv := by
  intro N a b f
  induction f using MvPolynomial.induction_on
  · next c =>
    rw [polE_apply]
    simp [rowDiv, rowGen, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
  · next p q hp hq =>
    rw [map_add (f := _), hp, hq]
    simp only [rowDiv, map_add (f := _), Polynomial.coeff_add]
  · next p v hp =>
    rw [polE_mul_X, rowDiv_one_mul_X, hp]

theorem fockQ_smul_right {σ : Type*} (c : ℚ) (f g : MvPolynomial σ ℚ) :
    fockQ f (c • g) = c * fockQ f g := by
  simp only [fockQ, MvPolynomial.coeff_smul, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

theorem determinant_shift_norm : DetShiftNormOf := by
  intro hAdj hDD hPol hHw N ν hν
  have hν' : Antitone (fun i : Fin N => ν i + 1) := fun a b hab => Nat.add_le_add_right (hν hab) 1
  have hG' := hHw N ν hν

  have heul : ∀ a : Fin N, rowDiv ℚ a a 1 (hw ℚ le_rfl (fun i => ν i + 1)) =
      (((ν a + 1 : ℕ) : ℚ)) • hw ℚ le_rfl (fun i => ν i + 1) := by
    intro a
    ext m
    rw [lgraded_coeff_euler, MvPolynomial.coeff_smul, smul_eq_mul]
    by_cases hm : AddMonoidAlgebra.coeff (hw ℚ le_rfl (fun i : Fin N => ν i + 1)) m = 0
    · simp [hm]
    · have hW := hwRowWeight ℚ N N le_rfl _ hν' hm
      have hWa := congrFun hW a
      have hr : rowNu (r := N) (fun i : Fin N => ν i + 1) a = ν a + 1 := by
        simp [rowNu]
      rw [hr] at hWa
      congr 1
      rw [← hWa]
      norm_cast
      simp [Finsupp.weight_apply, Finsupp.sum, lgraded_wa, rowW, Pi.single_apply, eq_comm]
  have hcap := Formalism.CohomologicalDescent.HeightDescentMinors.c2_holds_alt ℚ (Module.End ℚ (MvPolynomial (Fin N × Fin N) ℚ))
    (MvPolynomial (Fin N × Fin N) ℚ) N (polE N) ((N : ℚ) - 1) (fun i => ((ν i + 1 : ℕ) : ℚ))
    (hw ℚ le_rfl (fun i => ν i + 1))
    (fun i j hij => by
      rw [Module.End.smul_def, hPol]
      exact hwRaise ℚ N N le_rfl _ i j 1 hij le_rfl)
    (fun i => by rw [Module.End.smul_def, hPol, heul])
  rw [← hDD N, Module.End.smul_def, Module.End.mul_apply, LinearMap.mulLeft_apply] at hcap
  have hdet0 : detX N ≠ 0 := by
    intro h0
    have h1 := hHw N (fun _ => 0) (fun _ _ _ => le_rfl)
    rw [h0, zero_mul] at h1
    exact hwNe ℚ N N le_rfl _ h1
  have hD : detD N (detX N * hw ℚ le_rfl ν) =
      (∏ i : Fin N, ((N : ℚ) - 1 + ((ν i + 1 : ℕ) : ℚ) - ((i : ℕ) : ℚ))) • hw ℚ le_rfl ν := by
    apply mul_left_cancel₀ hdet0
    rw [← hG', hcap, hG', mul_smul_comm]
  rw [hAdj N (hw ℚ le_rfl ν) (detX N * hw ℚ le_rfl ν), hD, fockQ_smul_right]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  have hi : (i : ℕ) ≤ ν i + N := by omega
  rw [Nat.cast_sub hi]
  push_cast
  ring

end PI.HookSteps
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HookLengthBound.HighestWeightLastZero

section

@[expose] public section

open MvPolynomial Formalism.GradedWeylDivisibility

noncomputable section

namespace PI.HookSteps

theorem highest_weight_det_mul : HwDetMul := by
  intro N ν _
  cases N with
  | zero => simp [hw, detX]
  | succ n =>
    simp only [hw]
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
    have hlast : ∀ μ : Fin (n + 1) → ℕ, nuNext μ (Fin.last n) = 0 := by
      intro μ; simp [nuNext]
    have hcs : ∀ s : Fin n, (ν s.castSucc + 1) - nuNext (fun i => ν i + 1) s.castSucc =
        ν s.castSucc - nuNext ν s.castSucc := by
      intro s
      have hs := s.isLt
      simp only [nuNext, Fin.val_castSucc]
      rw [dite_eq_left (show (s : ℕ) + 1 < n + 1 by omega), dite_eq_left (show (s : ℕ) + 1 < n + 1 by omega)]
      omega
    simp only [hlast, hcs, Nat.sub_zero]
    have hL : lpMinor ℚ ((Fin.last n : ℕ) + 1) (r := n + 1) (n := n + 1) (by simp) (by simp) =
        detX (n + 1) := rfl
    rw [hL, pow_succ]
    ring

theorem lpMinor_rename (n s : ℕ) (h1 h2 : s ≤ n) (h3 h4 : s ≤ n + 1) :
    rename (fun v : Fin n × Fin n => (Fin.castSucc v.1, Fin.castSucc v.2)) (lpMinor ℚ s h1 h2) =
      lpMinor ℚ s h3 h4 := by
  unfold lpMinor
  rw [AlgHom.map_det]
  congr 1
  ext p q
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, rename_X]
  rfl

theorem highest_weight_last_zero : HwLastZero := by
  intro n ν _ hl
  simp only [hw]
  rw [Fin.prod_univ_castSucc, map_prod]
  have hlast : nuNext ν (Fin.last n) = 0 := by simp [nuNext]
  rw [hlast, hl, Nat.sub_zero, pow_zero, mul_one]
  refine Finset.prod_congr rfl fun s _ => ?_
  have hs := s.isLt
  rw [map_pow, lpMinor_rename n ((s : ℕ) + 1) _ _ (by omega) (by omega)]
  congr 1
  simp only [nuNext, Fin.val_castSucc]
  rw [dite_eq_left (show (s : ℕ) + 1 < n + 1 by omega)]
  by_cases h : (s : ℕ) + 1 < n
  · rw [dite_eq_left h]; rfl
  · rw [dite_eq_right h]
    have : (⟨s.val + 1, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext (by simp; omega)
    rw [this, hl]

theorem rename_isomorphism : RenameIso := by
  intro σ τ φ hφ f g
  classical
  unfold fockQ
  rw [support_rename_of_injective hφ, Finset.sum_image (fun a _ b _ h => Finsupp.mapDomain_injective hφ h)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_rename_mapDomain φ hφ, coeff_rename_mapDomain φ hφ]
  congr 2
  rw [Finsupp.mapDomain_support_of_injective hφ, Finset.prod_image (fun a _ b _ h => hφ h)]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finsupp.mapDomain_apply_of_injective hφ]

end PI.HookSteps
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HookLengthBound.HookBoundOfSteps

section

@[expose] public section

namespace PI.HookSteps

theorem hookBound_of_steps (hB : HookBoundOf) (hN : HookNormOf) (hS : DetShiftNormOf)
    (hR : RenameIso) (hH : HwDetMul) (hL : HwLastZero) (hA : DetAdj) (hD : DetDetId)
    (hP : PolEqRowDiv) : PI.HookBound :=
  hB (hN hR hH hL (hS hA hD hP hH))

end PI.HookSteps
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HookLengthBound.HookNorm

section

@[expose] public section

open MvPolynomial Formalism.GradedWeylDivisibility

noncomputable section

namespace PI.HookSteps

def Pn {N : ℕ} (ν : Fin N → ℕ) : ℕ := ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (ν i - ν j + (j - i) : ℕ)

def Qn {N : ℕ} (ν : Fin N → ℕ) : ℕ := ∏ i : Fin N, (ν i + (N - 1 - i)).factorial

theorem Pn_succ_shift {N : ℕ} (μ : Fin N → ℕ) : Pn (fun i => μ i + 1) = Pn μ := by
  unfold Pn
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  dsimp only
  omega

theorem Qn_succ_shift {N : ℕ} (μ : Fin N → ℕ) :
    Qn (fun i => μ i + 1) = (∏ i : Fin N, (μ i + N - i)) * Qn μ := by
  unfold Qn
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hi := i.isLt
  have e : μ i + 1 + (N - 1 - (i : ℕ)) = (μ i + (N - 1 - (i : ℕ))) + 1 := by omega
  have e2 : μ i + N - (i : ℕ) = μ i + (N - 1 - (i : ℕ)) + 1 := by omega
  rw [e, e2, Nat.factorial_succ]

theorem Ioi_eq_filter {m : ℕ} (x : Fin m) : Finset.Ioi x = Finset.univ.filter (fun j => x < j) := by
  ext j
  simp

theorem prod_Ioi_castSucc {M : Type*} [CommMonoid M] (n : ℕ) (i : Fin n) (g : Fin (n + 1) → M) :
    ∏ j ∈ Finset.Ioi (Fin.castSucc i), g j = (∏ j ∈ Finset.Ioi i, g (Fin.castSucc j)) * g (Fin.last n) := by
  rw [Ioi_eq_filter, Ioi_eq_filter, Finset.prod_filter, Finset.prod_filter, Fin.prod_univ_castSucc]
  simp only [Fin.castSucc_lt_castSucc_iff, Fin.castSucc_lt_last, if_true]

theorem Pn_last_zero (n : ℕ) (ν : Fin (n + 1) → ℕ) (h : ν (Fin.last n) = 0) :
    Pn ν = Pn (fun i : Fin n => ν (Fin.castSucc i)) * ∏ i : Fin n, (ν (Fin.castSucc i) + (n - i)) := by
  unfold Pn
  rw [Fin.prod_univ_castSucc]
  have hlast : ∏ j ∈ Finset.Ioi (Fin.last n), (ν (Fin.last n) - ν j + ((j : ℕ) - ((Fin.last n : Fin (n + 1)) : ℕ))) = 1 := by
    rw [Finset.eq_empty_of_forall_notMem fun j hj => absurd (Finset.mem_Ioi.mp hj) (not_lt.mpr (Fin.le_last j)), Finset.prod_empty]
  rw [hlast, mul_one, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [prod_Ioi_castSucc]
  simp only [Fin.coe_castSucc, Fin.val_last, h]
  congr 1 <;> omega

theorem Qn_last_zero (n : ℕ) (ν : Fin (n + 1) → ℕ) (h : ν (Fin.last n) = 0) :
    Qn ν = (∏ i : Fin n, (ν (Fin.castSucc i) + (n - i))) * Qn (fun i : Fin n => ν (Fin.castSucc i)) := by
  unfold Qn
  rw [Fin.prod_univ_castSucc, h, ← Finset.prod_mul_distrib]
  have hl : (0 + (n + 1 - 1 - ((Fin.last n : Fin (n + 1)) : ℕ))).factorial = 1 := by
    simp
  rw [hl, mul_one]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hi := i.isLt
  simp only [Fin.coe_castSucc]
  have e : ν (Fin.castSucc i) + (n + 1 - 1 - (i : ℕ)) = (ν (Fin.castSucc i) + (n - 1 - (i : ℕ))) + 1 := by omega
  rw [e, Nat.factorial_succ]
  congr 1
  omega

theorem castSucc2_injective (n : ℕ) :
    Function.Injective (fun v : Fin n × Fin n => (Fin.castSucc v.1, Fin.castSucc v.2)) := by
  intro a b h
  simp only [Prod.mk.injEq, Fin.castSucc_inj] at h
  exact Prod.ext h.1 h.2

theorem hook_norm : HookNormOf := by
  intro hR hH hL hS
  suffices key : ∀ (N : ℕ) (ν : Fin N → ℕ), Antitone ν →
      fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) * (Pn ν : ℚ) = (Qn ν : ℚ) by
    intro N ν hν
    have := key N ν hν
    unfold Pn Qn at this
    simp only [Nat.cast_prod] at this
    exact this
  intro N
  induction N with
  | zero => intro ν _; simp [Pn, Qn, hw, fockQ]
  | succ n ih =>
    suffices hk : ∀ (k : ℕ) (ν : Fin (n + 1) → ℕ), Antitone ν → ν (Fin.last n) = k →
        fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) * (Pn ν : ℚ) = (Qn ν : ℚ) by
      intro ν hν; exact hk _ ν hν rfl
    intro k
    induction k with
    | zero =>
      intro ν hν h0
      have hν' : Antitone (fun i : Fin n => ν i.castSucc) :=
        fun a b hab => hν (Fin.castSucc_le_castSucc_iff.2 hab)
      rw [hL n ν hν h0, hR _ _ _ (castSucc2_injective n), Pn_last_zero n ν h0, Qn_last_zero n ν h0,
        Nat.cast_mul, Nat.cast_mul, ← ih _ hν']
      ring
    | succ k ihk =>
      intro ν hν hk
      have hge : ∀ i, 1 ≤ ν i := fun i => by have := hν (Fin.le_last i); omega
      obtain ⟨μ, rfl⟩ : ∃ μ : Fin (n + 1) → ℕ, ν = fun i => μ i + 1 :=
        ⟨fun i => ν i - 1, funext fun i => by have := hge i; show ν i = ν i - 1 + 1; omega⟩
      have hμ : Antitone μ := fun a b hab => by have := hν hab; simp only at this; omega
      have hμk : μ (Fin.last n) = k := by simp only at hk; omega
      rw [Pn_succ_shift, Qn_succ_shift, hH _ μ hμ, hS _ μ hμ, Nat.cast_mul, Nat.cast_prod,
        ← ihk μ hμ hμk]
      ring

end PI.HookSteps
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HookLengthBound.Assemble

section

@[expose] public section

namespace PI.HookSteps

theorem hookBound_of (hD : DetDetId) : PI.HookBound :=
  hookBound_of_steps hook_bound hook_norm determinant_shift_norm rename_isomorphism
    highest_weight_det_mul highest_weight_last_zero determinant_adjugate hD polynomial_eq_divisibility

end PI.HookSteps
end
end
