module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurMulDetEqDet
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EsymmEqSumFilterPerm

section

@[expose] public section

open scoped Classical

namespace GlobalTheory.JSW

theorem esymm_eq_sum_filter_perm (n j : ℕ) (σ : Equiv.Perm (Fin n)) :
    MvPolynomial.esymm (Fin n) ℤ j =
      ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j),
        ∏ k ∈ J, (MvPolynomial.X (σ k) : MvPolynomial (Fin n) ℤ) := by
  rw [← MvPolynomial.rename_esymm (Fin n) ℤ j σ]

  simp only [MvPolynomial.esymm, map_sum, map_prod, MvPolynomial.rename_X,
  Finset.powersetCard_eq_filter, Finset.powerset_univ]

theorem esymm_mul_alternant (n : ℕ) (m : Fin n → ℕ) (j : ℕ) :
    MvPolynomial.esymm (Fin n) ℤ j *
        Matrix.det (Matrix.of fun i k : Fin n =>
          (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ m k) =
      ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j),
        Matrix.det (Matrix.of fun i k : Fin n =>
          (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ (m k + if k ∈ J then 1 else 0)) := by
  simp only [Matrix.det_apply, Matrix.of_apply]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [esymm_eq_sum_filter_perm n j σ, Finset.sum_mul]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [mul_smul_comm]
  congr 1
  simp only [pow_add, Finset.prod_mul_distrib, pow_ite, pow_one, pow_zero,
    Finset.prod_ite_mem, Finset.univ_inter]
  ring

end GlobalTheory.JSW
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EsymmEqSumFilterPermStatement

section

@[expose] public section

open scoped Classical

theorem _root_.GlobalTheory.T.esymm_mul_det_pow_eq_sum_det_shifted : ∀ (n : ℕ) (m : Fin n → ℕ) (j : ℕ), MvPolynomial.esymm (Fin n) ℤ j * Matrix.det (Matrix.of fun i k : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ m k) = ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j), Matrix.det (Matrix.of fun i k : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ (m k + if k ∈ J then 1 else 0)) := by
  first | exact @GlobalTheory.JSW.esymm_mul_alternant | exact GlobalTheory.JSW.esymm_mul_alternant | (intros; apply GlobalTheory.JSW.esymm_mul_alternant <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurMulDetEqDetStatement

section

@[expose] public section

open scoped Classical

theorem _root_.GlobalTheory.T.schur_mul_vandermonde_det_eq_det : ∀ (n : ℕ) (l : Fin n → ℕ), Antitone l → GlobalTheory.JSW.schur n l * Matrix.det (Matrix.of fun i j : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ (n - 1 - (j : ℕ))) = Matrix.det (Matrix.of fun i j : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ (l j + n - 1 - (j : ℕ))) := by
  first | exact @GlobalTheory.JSW.schur_mul_det_eq_det | exact GlobalTheory.JSW.schur_mul_det_eq_det | (intros; apply GlobalTheory.JSW.schur_mul_det_eq_det <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EsymmMulSchurPolynomialJacobiTrudi

section

@[expose] public section

open scoped Classical

open MvPolynomial in
theorem GlobalTheory.JSW.PieriDeterminant.vdm_ne (n : ℕ) : Matrix.det (Matrix.of fun i j : Fin n => (X i : MvPolynomial (Fin n) ℤ) ^ (n - 1 - (j : ℕ))) ≠ 0 := by
  have h : (Matrix.of fun i j : Fin n => (X i : MvPolynomial (Fin n) ℤ) ^ (n - 1 - (j : ℕ))) =
      (Matrix.vandermonde (fun i => (X i : MvPolynomial (Fin n) ℤ))).submatrix id Fin.revPerm := by
    ext i j
    simp only [Matrix.of_apply, Matrix.submatrix_apply, Matrix.vandermonde_apply, id, Fin.revPerm_apply, Fin.val_rev]
    rw [show n - 1 - (j : ℕ) = n - ((j : ℕ) + 1) by omega]
  rw [h, Matrix.det_permute']
  refine mul_ne_zero (by simp [Units.ne_zero]) ?_
  rw [Matrix.det_vandermonde_ne_zero_iff]
  exact MvPolynomial.X_injective

namespace GlobalTheory.JSW.PieriDeterminant

theorem adj {n : ℕ} (l : Fin n → ℕ) (hl : Antitone l) (J : Finset (Fin n)) :
    ∀ d : ℕ, ∀ a b : Fin n, (b : ℕ) = a + d + 1 → l a = l b → a ∉ J → b ∈ J →
      ∃ a' b' : Fin n, (b' : ℕ) = a' + 1 ∧ l a' = l b' ∧ a' ∉ J ∧ b' ∈ J := by
  intro d
  induction d with
  | zero => intro a b h1 h2 h3 h4; exact ⟨a, b, by omega, h2, h3, h4⟩
  | succ d ih =>
    intro a b h1 h2 h3 h4
    have hc : (a : ℕ) + 1 < n := by have := b.isLt; omega
    let c : Fin n := ⟨a + 1, hc⟩
    have hac : a ≤ c := by show (a : ℕ) ≤ a + 1; omega
    have hcb : c ≤ b := by show (a : ℕ) + 1 ≤ b; omega
    have hlc : l c = l a := le_antisymm (hl hac) (h2 ▸ hl hcb)
    by_cases hcJ : c ∈ J
    · exact ⟨a, c, rfl, hlc.symm, h3, hcJ⟩
    · exact ih c b (by show (b : ℕ) = a + 1 + d + 1; omega) (hlc.trans h2) hcJ h4

theorem det_zero {n : ℕ} (l : Fin n → ℕ) (hl : Antitone l) (J : Finset (Fin n))
    (hJ : ¬ Antitone (l + (fun i => if i ∈ J then 1 else 0))) :
    Matrix.det (Matrix.of fun i k : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^
      ((l k + n - 1 - (k : ℕ)) + if k ∈ J then 1 else 0)) = 0 := by
  obtain ⟨a, b, hab, hlt⟩ : ∃ a b : Fin n, a ≤ b ∧ ((l + (fun i => if i ∈ J then 1 else 0) : Fin n → ℕ)) a <
      ((l + (fun i => if i ∈ J then 1 else 0) : Fin n → ℕ)) b := by
    simp only [Antitone, not_forall, not_le] at hJ
    obtain ⟨a, b, h1, h2⟩ := hJ; exact ⟨a, b, h1, h2⟩
  simp only [Pi.add_apply] at hlt
  have hla := hl hab
  have hA : a ∉ J := by intro h; simp only [h, if_true] at hlt; split_ifs at hlt <;> omega
  have hB : b ∈ J := by by_contra h; simp only [h, if_false] at hlt; split_ifs at hlt <;> omega
  have hE : l a = l b := by simp only [hA, hB, if_true, if_false] at hlt; omega
  have hne : a ≠ b := by rintro rfl; exact hA hB
  obtain ⟨a', b', h1, h2, h3, h4⟩ :=
    adj l hl J ((b : ℕ) - a - 1) a b (by have : (a : ℕ) < b := lt_of_le_of_ne hab (fun h => hne (Fin.ext h)); omega) hE hA hB
  refine Matrix.det_zero_of_column_eq (i := a') (j := b') (fun h => by rw [h] at h1; omega) (fun i => ?_)
  simp only [Matrix.of_apply, h3, h4, if_true, if_false]
  congr 1
  have := b'.isLt
  omega

end GlobalTheory.JSW.PieriDeterminant

open MvPolynomial in
theorem GlobalTheory.JSW.esymm_mul_schur : ∀ (n : ℕ) (l : Fin n → ℕ), Antitone l → ∀ j ≤ n, MvPolynomial.esymm (Fin n) ℤ j * GlobalTheory.JSW.schur n l = ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j ∧ Antitone (l + (fun i => if i ∈ J then 1 else 0))), GlobalTheory.JSW.schur n (l + (fun i => if i ∈ J then 1 else 0)) := by
  intro n l hl j _
  apply mul_right_cancel₀ (GlobalTheory.JSW.PieriDeterminant.vdm_ne n)
  have h1 := GlobalTheory.T.esymm_mul_det_pow_eq_sum_det_shifted n (fun k => l k + n - 1 - k) j
  beta_reduce at h1
  calc MvPolynomial.esymm (Fin n) ℤ j * GlobalTheory.JSW.schur n l * _
      = ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j),
          Matrix.det (Matrix.of fun i k : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^
            ((l k + n - 1 - (k : ℕ)) + if k ∈ J then 1 else 0)) := by
        rw [mul_assoc, GlobalTheory.T.schur_mul_vandermonde_det_eq_det n l hl, h1]
    _ = ∑ J ∈ ((Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j)).filter
          (fun J => Antitone (l + (fun i => if i ∈ J then 1 else 0))),
          Matrix.det (Matrix.of fun i k : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^
            ((l k + n - 1 - (k : ℕ)) + if k ∈ J then 1 else 0)) := by
        refine (Finset.sum_filter_of_ne fun J _ hJ => ?_).symm
        by_contra h
        exact hJ (GlobalTheory.JSW.PieriDeterminant.det_zero l hl J h)
    _ = ∑ J ∈ ((Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j)).filter
          (fun J => Antitone (l + (fun i => if i ∈ J then 1 else 0))),
          GlobalTheory.JSW.schur n (l + (fun i => if i ∈ J then 1 else 0)) *
            Matrix.det (Matrix.of fun i j : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ (n - 1 - (j : ℕ))) := by
        refine Finset.sum_congr rfl fun J hJ => ?_
        rw [GlobalTheory.T.schur_mul_vandermonde_det_eq_det n _ (Finset.mem_filter.1 hJ).2]
        have e : ∀ k : Fin n, ((l + (fun i => if i ∈ J then 1 else 0) : Fin n → ℕ)) k + n - 1 - (k : ℕ) =
            (l k + n - 1 - (k : ℕ)) + if k ∈ J then 1 else 0 := by
          intro k; have := k.isLt; simp only [Pi.add_apply]; split_ifs <;> omega
        simp only [e]
    _ = _ := by rw [Finset.filter_filter, Finset.sum_mul]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EsymmMulSchurPolynomialJacobiTrudiStatement

section

@[expose] public section

open scoped Classical

theorem _root_.GlobalTheory.T.esymm_mul_schurPolynomialJacobiTrudi : ∀ (n : ℕ) (l : Fin n → ℕ), Antitone l → ∀ j ≤ n, MvPolynomial.esymm (Fin n) ℤ j * GlobalTheory.JSW.schur n l = ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j ∧ Antitone (l + (fun i => if i ∈ J then 1 else 0))), GlobalTheory.JSW.schur n (l + (fun i => if i ∈ J then 1 else 0)) := by
  first | exact @GlobalTheory.JSW.esymm_mul_schur | exact GlobalTheory.JSW.esymm_mul_schur | (intros; apply GlobalTheory.JSW.esymm_mul_schur <;> assumption)
end
end
