module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurEqJtDet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurMulDetEqDet
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacobiTrudiAlternantExpansionStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurPolynomialPadZerosEqJacobiTrudiDeterminant

section

@[expose] public section

noncomputable section

namespace GlobalTheory.JSW

theorem jacobi_trudi_det_pad_zeros {A : Type*} [CommRing A] (h : ℕ → A) (h0 : h 0 = 1) {m n : ℕ} (hmn : m ≤ n)
    (l : Fin m → ℕ) : jtDet n h (padTo hmn l) = jtDet m h l := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  unfold jtDet
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv]
  set M := (Matrix.of fun i j : Fin (m + k) =>
    if ((padTo hmn l i : ℤ) - i + j) < 0 then 0 else h (((padTo hmn l i : ℤ) - i + j).toNat)).submatrix
      finSumFinEquiv finSumFinEquiv with hM
  have h21 : M.toBlocks₂₁ = 0 := by
    ext i j
    simp only [hM, Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.submatrix_apply, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, Matrix.zero_apply, padTo]
    have hj := j.2
    simp
    omega
  have h22 : M.toBlocks₂₂.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular]
    · apply Finset.prod_eq_one
      intro i _
      simp [hM, Matrix.toBlocks₂₂, padTo, h0]
    · intro i j hij
      simp only [hM, Matrix.toBlocks₂₂, Matrix.of_apply, Matrix.submatrix_apply, finSumFinEquiv_apply_right, padTo]
      have : (j : ℕ) < i := hij
      simp
      omega
  have h11 : M.toBlocks₁₁ = Matrix.of fun i j : Fin m =>
      if ((l i : ℤ) - i + j) < 0 then 0 else h (((l i : ℤ) - i + j).toNat) := by
    ext i j
    simp [hM, Matrix.toBlocks₁₁, padTo]
  rw [← Matrix.fromBlocks_toBlocks M, h21, Matrix.det_fromBlocks_zero₂₁, h22, h11, mul_one]

theorem schur_padTo_eq_jtDet {m n : ℕ} (hmn : m ≤ n) (l : Fin m → ℕ) :
    schur n (padTo hmn l) = jtDet m (fun k => MvPolynomial.hsymm (Fin n) ℤ k) l := by
  rw [schur_eq_jtDet]
  exact jacobi_trudi_det_pad_zeros _ (MvPolynomial.hsymm_zero _ _) hmn l

end GlobalTheory.JSW
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurPolynomialPadZerosEqJacobiTrudiDeterminantStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.schurPolynomial_padZeros_eq_jacobiTrudiDeterminant : ∀ {m n : ℕ} (hmn : m ≤ n) (l : Fin m → ℕ),
    GlobalTheory.JSW.schur n (GlobalTheory.JSW.padTo hmn l) = GlobalTheory.JSW.jtDet m (fun k => MvPolynomial.hsymm (Fin n) ℤ k) l := by
  first | exact @GlobalTheory.JSW.schur_padTo_eq_jtDet | exact GlobalTheory.JSW.schur_padTo_eq_jtDet | (intros; apply GlobalTheory.JSW.schur_padTo_eq_jtDet <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CauchyIdentitySchurFormalDegree

section

@[expose] public section

noncomputable section

open MvPolynomial

namespace GlobalTheory.JSW.CauchyGlue

theorem map_jtDet {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (m : ℕ) (h : ℕ → A)
    (l : Fin m → ℕ) : f (jtDet m h l) = jtDet m (fun k => f (h k)) l := by
  rw [jtDet, jtDet, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp

theorem map_alternant {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (m : ℕ) (μ : Fin m → ℕ) :
    MvPolynomial.map f (alternant A m μ) = alternant B m μ := by
  rw [alternant, alternant, RingHom.map_det]
  congr 1
  ext i j
  simp

theorem alternant_eq_det (A : Type*) [CommRing A] (m : ℕ) (μ : Fin m → ℕ) :
    alternant A m μ = Matrix.det (Matrix.of fun i j : Fin m => (X i : MvPolynomial (Fin m) A) ^ μ j) := by
  rw [alternant, ← Matrix.det_transpose]
  rfl

theorem alternant_staircase_ne_zero (m : ℕ) : alternant ℂ m (staircase m) ≠ 0 := by
  have e : (Matrix.of fun i j : Fin m => (X j : MvPolynomial (Fin m) ℂ) ^ staircase m i) =
      (Matrix.transpose (Matrix.vandermonde (fun j : Fin m => (X j : MvPolynomial (Fin m) ℂ)))).submatrix Fin.revPerm id := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.of_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.vandermonde_apply,
      Fin.revPerm_apply, id, staircase, Fin.val_rev]
    congr 1
    omega
  rw [alternant, e, Matrix.det_permute, Matrix.det_transpose]
  refine mul_ne_zero ?_ ?_
  · rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin m))) with h | h <;> simp [h]
  · exact (Matrix.det_vandermonde_ne_zero_iff).2 (MvPolynomial.X_injective)

theorem bialt_int (m : ℕ) (l : Fin m → ℕ) (hl : Antitone l) :
    schur m l * alternant ℤ m (staircase m) = alternant ℤ m (fun i => l i + staircase m i) := by
  simp only [alternant_eq_det, staircase]
  rw [schur_mul_det_eq_det m l hl]
  congr 1
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.of_apply]
  congr 1
  have := j.2
  omega

theorem cauchy_formal : ∀ {m n : ℕ} (hmn : m ≤ n) (α : Fin n → ℂ) (β : Fin m → ℂ) (d : ℕ),
    ∑ l ∈ GlobalTheory.JSW.antiParts m d, GlobalTheory.JSW.schurAt (GlobalTheory.JSW.padTo hmn l) α * GlobalTheory.JSW.schurAt l β =
      ∑ k ∈ Finset.Nat.antidiagonalTuple m d,
        ∏ j, MvPolynomial.eval₂ (Int.castRingHom ℂ) α (MvPolynomial.hsymm (Fin n) ℤ (k j)) * β j ^ (k j) := by
  intro m n hmn α β d
  set hC : ℕ → ℂ := fun k => eval₂ (Int.castRingHom ℂ) α (hsymm (Fin n) ℤ k) with hhC
  have hA := GlobalTheory.T.jacobi_trudi_alternant_expansion (A := ℂ) m d hC
  have hpad : ∀ l : Fin m → ℕ, schurAt (padTo hmn l) α = jtDet m hC l := by
    intro l
    rw [schurAt, GlobalTheory.T.schurPolynomial_padZeros_eq_jacobiTrudiDeterminant hmn l, ← MvPolynomial.coe_eval₂Hom, map_jtDet]
    rfl
  have hbi : ∀ l ∈ antiParts m d, alternant ℂ m (fun i => l i + staircase m i) =
      MvPolynomial.map (Int.castRingHom ℂ) (schur m l) * alternant ℂ m (staircase m) := by
    intro l hl
    have := congrArg (MvPolynomial.map (Int.castRingHom ℂ)) (bialt_int m l (mem_antiParts.1 hl).2)
    rw [map_mul, map_alternant, map_alternant] at this
    exact this.symm
  have hR : ∑ l ∈ antiParts m d, C (jtDet m hC l) * alternant ℂ m (fun i => l i + staircase m i) =
      alternant ℂ m (staircase m) *
        ∑ l ∈ antiParts m d, C (jtDet m hC l) * MvPolynomial.map (Int.castRingHom ℂ) (schur m l) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [hbi l hl]
    ring
  rw [hR] at hA
  have hP := mul_left_cancel₀ (alternant_staircase_ne_zero m) hA
  have hE := congrArg (MvPolynomial.eval β) hP

  simp only [map_sum, map_prod, map_mul, eval_C, eval_X, map_pow, MvPolynomial.eval_map] at hE
  refine (Finset.sum_congr rfl fun l _ => ?_).trans hE.symm
  rw [hpad]
  rfl

end GlobalTheory.JSW.CauchyGlue
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CauchyIdentitySchurFormalDegreeStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.cauchy_identity_schur_formal_degree : ∀ {m n : ℕ} (hmn : m ≤ n) (α : Fin n → ℂ) (β : Fin m → ℂ) (d : ℕ),
    ∑ l ∈ GlobalTheory.JSW.antiParts m d, GlobalTheory.JSW.schurAt (GlobalTheory.JSW.padTo hmn l) α * GlobalTheory.JSW.schurAt l β =
      ∑ k ∈ Finset.Nat.antidiagonalTuple m d,
        ∏ j, MvPolynomial.eval₂ (Int.castRingHom ℂ) α (MvPolynomial.hsymm (Fin n) ℤ (k j)) * β j ^ (k j) := by
  exact @GlobalTheory.JSW.CauchyGlue.cauchy_formal
end
end
