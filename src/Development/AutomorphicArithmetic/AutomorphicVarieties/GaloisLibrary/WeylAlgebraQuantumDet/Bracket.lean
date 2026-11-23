module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.IsTop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.Curve
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
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
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.IsTop
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.LineDeriv

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.InvCurve

section

@[expose] public section

open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.invCurve :
    ∀ (n : ℕ) (a b : Fin n), ∃ P Q : ℂ → Matrix (Fin n) (Fin n) ℂ, P 0 = 1 ∧ Q 0 = 1 ∧ (∀ t, Q t * P t = 1) ∧
      ∀ i j, HasDerivAt (fun t => P t i j) (Matrix.single a b (1 : ℂ) i j) 0 ∧ HasDerivAt (fun t => Q t i j) (-Matrix.single a b (1 : ℂ) i j) 0 := by
  intro n a b
  by_cases hab : a = b
  · subst hab
    set E : Matrix (Fin n) (Fin n) ℂ := Matrix.single a a 1 with hEdef
    have hE : E * E = E := by
      rw [hEdef, Matrix.single_mul_single_same, one_mul]
    refine ⟨fun t => 1 + (Complex.exp t - 1) • E, fun t => 1 + (Complex.exp (-t) - 1) • E,
      by simp, by simp, ?_, ?_⟩
    · intro t
      have key : (Complex.exp (-t) - 1) + ((Complex.exp t - 1)
          + (Complex.exp (-t) - 1) * (Complex.exp t - 1)) = 0 := by
        have h1 : Complex.exp (-t) * Complex.exp t = 1 := by
          rw [← Complex.exp_add]; simp
        linear_combination h1
      simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, hE]
      rw [add_assoc, ← add_smul, ← add_smul, key, zero_smul, add_zero]
    · intro i j
      constructor
      · have h := (((Complex.hasDerivAt_exp 0).sub_const 1).mul_const (E i j)).const_add ((1 : Matrix (Fin n) (Fin n) ℂ) i j)
        simpa [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using h
      · have h0 : HasDerivAt (fun t : ℂ => Complex.exp (-t)) (-1) 0 := by
          simpa using (hasDerivAt_neg (0 : ℂ)).cexp
        have h := ((h0.sub_const 1).mul_const (E i j)).const_add ((1 : Matrix (Fin n) (Fin n) ℂ) i j)
        simpa [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using h
  · set E : Matrix (Fin n) (Fin n) ℂ := Matrix.single a b 1 with hEdef
    have hE : E * E = 0 := by
      rw [hEdef]
      simp [Ne.symm hab]
    refine ⟨fun t => 1 + t • E, fun t => 1 - t • E, by simp, by simp, ?_, ?_⟩
    · intro t
      simp only [sub_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, hE, smul_zero]
      abel
    · intro i j
      constructor
      · have h := ((hasDerivAt_id (0 : ℂ)).mul_const (E i j)).const_add ((1 : Matrix (Fin n) (Fin n) ℂ) i j)
        simpa [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using h
      · have h := ((hasDerivAt_id (0 : ℂ)).mul_const (E i j)).const_sub ((1 : Matrix (Fin n) (Fin n) ℂ) i j)
        simpa [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] using h
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.Bracket

section

@[expose] public section

open Matrix UpperTheory.V.Weyl

private theorem hasDerivAt_mul_mul_entry {n : ℕ} (P Q : ℂ → Matrix (Fin n) (Fin n) ℂ)
    (P' Q' Y : Matrix (Fin n) (Fin n) ℂ)
    (hP : ∀ i j, HasDerivAt (fun t => P t i j) (P' i j) 0)
    (hQ : ∀ i j, HasDerivAt (fun t => Q t i j) (Q' i j) 0) (p q : Fin n) :
    HasDerivAt (fun t => (P t * Y * Q t) p q) ((P' * Y * Q 0 + P 0 * Y * Q') p q) 0 := by
  have h : HasDerivAt (fun t => ∑ m, (∑ l, P t p l * Y l m) * Q t m q)
      (∑ m, ((∑ l, P' p l * Y l m) * Q 0 m q + (∑ l, P 0 p l * Y l m) * Q' m q)) 0 :=
    HasDerivAt.fun_sum fun m _ =>
      (HasDerivAt.fun_sum fun l _ => (hP p l).mul_const (Y l m)).mul (hQ m q)
  have e : (P' * Y * Q 0 + P 0 * Y * Q') p q =
      ∑ m, ((∑ l, P' p l * Y l m) * Q 0 m q + (∑ l, P 0 p l * Y l m) * Q' m q) := by
    rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_add_distrib]
    simp only [Matrix.mul_apply]
  have ef : (fun t => (P t * Y * Q t) p q) = fun t => ∑ m, (∑ l, P t p l * Y l m) * Q t m q := by
    funext t
    simp only [Matrix.mul_apply]
  rw [e, ef]
  exact h

private theorem pre_D_eq_sum_single {n : ℕ} (Ξ : Pre n) (M : Matrix (Fin n) (Fin n) ℂ) (i k : Fin Ξ.d) :
    Ξ.D M i k = ∑ p, ∑ q, M p q * Ξ.D (Matrix.single p q 1) i k := by
  have hM : M = ∑ p, ∑ q, M p q • Matrix.single p q (1 : ℂ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single M]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  conv_lhs => rw [hM]

  simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

theorem UpperTheory.V.Weyl.bracket :
    ∀ (n : ℕ) (Ξ : Pre n) (a b : Fin n) (Y : Matrix (Fin n) (Fin n) ℂ),
      Ξ.E a b * Ξ.D Y - Ξ.D Y * Ξ.E a b = Ξ.D (Matrix.single a b 1 * Y - Y * Matrix.single a b 1) := by
  intro n Ξ a b Y
  obtain ⟨P, Q, hP0, hQ0, hQP, hd⟩ := invCurve n a b
  set s : Matrix (Fin n) (Fin n) ℂ := Matrix.single a b 1 with hs
  set c : Matrix (Fin n) (Fin n) ℂ := s * Y - Y * s with hc
  have hE : ∀ t, Ξ.mat (P t) * Ξ.D Y = Ξ.D (P t * Y * Q t) * Ξ.mat (P t) := fun t =>
    adEq n Ξ (P t) Y (P t * Y * Q t) (by rw [Matrix.mul_assoc (P t * Y), hQP t, Matrix.mul_one])
  have hmat := curve n Ξ P s hP0 (fun i j => (hd i j).1)
  have hM : ∀ p q, HasDerivAt (fun t => (P t * Y * Q t) p q) (c p q) 0 := by
    intro p q
    have h := hasDerivAt_mul_mul_entry P Q s (-s) Y
      (fun i j => (hd i j).1) (fun i j => by simpa using (hd i j).2) p q
    simpa [hP0, hQ0, hc, sub_eq_add_neg, Matrix.mul_neg] using h
  have hdD : ∀ i k, HasDerivAt (fun t => Ξ.D (P t * Y * Q t) i k) (Ξ.D c i k) 0 := by
    intro i k
    have h : HasDerivAt (fun t => ∑ p, ∑ q, (P t * Y * Q t) p q * Ξ.D (Matrix.single p q 1) i k)
        (∑ p, ∑ q, c p q * Ξ.D (Matrix.single p q 1) i k) 0 :=
      HasDerivAt.fun_sum fun p _ => HasDerivAt.fun_sum fun q _ => (hM p q).mul_const _
    rw [pre_D_eq_sum_single Ξ c i k]
    convert h using 1
    funext t
    exact pre_D_eq_sum_single Ξ _ i k
  ext i j
  have hL : HasDerivAt (fun t => (Ξ.mat (P t) * Ξ.D Y) i j)
      (∑ k, Ξ.D s i k * Ξ.D Y k j) 0 := by
    simp only [Matrix.mul_apply]
    exact HasDerivAt.fun_sum fun k _ => (hmat i k).mul_const _
  have hR : HasDerivAt (fun t => (Ξ.D (P t * Y * Q t) * Ξ.mat (P t)) i j)
      (∑ k, (Ξ.D c i k * Ξ.mat (P 0) k j + Ξ.D (P 0 * Y * Q 0) i k * Ξ.D s k j)) 0 := by
    simp only [Matrix.mul_apply]
    exact HasDerivAt.fun_sum fun k _ => (hdD i k).mul (hmat k j)
  have hfun : (fun t => (Ξ.mat (P t) * Ξ.D Y) i j) =
      fun t => (Ξ.D (P t * Y * Q t) * Ξ.mat (P t)) i j :=
    funext fun t => by rw [hE t]
  rw [hfun] at hL
  have hu := hL.unique hR
  simp only [hP0, hQ0, Matrix.mul_one, Matrix.one_mul, map_one, Finset.sum_add_distrib] at hu
  simp only [Matrix.sub_apply, Pre.E, Matrix.mul_apply]
  rw [hu]
  simp [Matrix.one_apply, s]
end
end
