module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTorusWeightOfPolyRepGLComplexStatement
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TransvectionWeightVecExpansionStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitriangularInductionTransvectionStatement
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTorusWeightMaximizingWeightedSum

section

@[expose] public section

open Matrix GlobalTheory.AlgWtHW

namespace GlobalTheory.AlgWtHW.MaxWeight

noncomputable def twoDiag (n : ℕ) : GL (Fin n) ℂ :=
  ⟨Matrix.diagonal (fun i : Fin n => (2 : ℂ) ^ ((n : ℤ) - ((i : ℕ) : ℤ))),
    Matrix.diagonal (fun i : Fin n => ((2 : ℂ) ^ ((n : ℤ) - ((i : ℕ) : ℤ)))⁻¹),
    by
      rw [Matrix.diagonal_mul_diagonal]
      rw [← Matrix.diagonal_one]
      congr 1
      funext i
      exact mul_inv_cancel₀ (zpow_ne_zero _ two_ne_zero),
    by
      rw [Matrix.diagonal_mul_diagonal]
      rw [← Matrix.diagonal_one]
      congr 1
      funext i
      exact inv_mul_cancel₀ (zpow_ne_zero _ two_ne_zero)⟩

lemma twoDiag_isDiag (n : ℕ) : (twoDiag n).val.IsDiag := Matrix.isDiag_diagonal _

lemma prod_two_zpow {n : ℕ} (ν : Fin n → ℤ) (s : Finset (Fin n)) :
    ∏ i ∈ s, ((2 : ℂ) ^ ((n : ℤ) - ((i : ℕ) : ℤ))) ^ (ν i) =
      (2 : ℂ) ^ (∑ i ∈ s, ((n : ℤ) - ((i : ℕ) : ℤ)) * ν i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ two_ne_zero, ← _root_.zpow_mul]

lemma two_zpow_inj {a b : ℤ} (h : (2 : ℂ) ^ a = (2 : ℂ) ^ b) : a = b := by
  have h' : ((2 : ℝ) ^ a : ℝ) = (2 : ℝ) ^ b := by
    have ha : ((2 : ℂ) ^ a) = (((2 : ℝ) ^ a : ℝ) : ℂ) := by push_cast; rfl
    have hb : ((2 : ℂ) ^ b) = (((2 : ℝ) ^ b : ℝ) : ℂ) := by push_cast; rfl
    rw [ha, hb] at h
    exact_mod_cast h
  exact zpow_right_injective₀ (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) ≠ 1) h'

theorem exists_max_weight : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ) (μ₀ : Fin n → ℤ), IsWt Φ μ₀ →
    ∃ μ : Fin n → ℤ, IsWt Φ μ ∧ ∀ ν : Fin n → ℤ, IsWt Φ ν →
      ∑ i : Fin n, ((n : ℤ) - ((i : ℕ) : ℤ)) * ν i ≤ ∑ i : Fin n, ((n : ℤ) - ((i : ℕ) : ℤ)) * μ i := by
  intro n ι _ _ Φ μ₀ h₀
  let f : (Fin n → ℤ) → ℤ := fun ν => ∑ i : Fin n, ((n : ℤ) - ((i : ℕ) : ℤ)) * ν i
  let A : Module.End ℂ (ι → ℂ) := Matrix.toLin' (Φ (twoDiag n))
  have heig : ∀ ν, IsWt Φ ν → A.HasEigenvalue ((2 : ℂ) ^ f ν) := by
    rintro ν ⟨w, hw0, hw⟩
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := w)
    refine ⟨?_, hw0⟩
    rw [Module.End.mem_eigenspace_iff]
    simp only [A, Matrix.toLin'_apply]
    rw [hw _ (twoDiag_isDiag n)]
    congr 1
    rw [← prod_two_zpow ν Finset.univ]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [twoDiag, Matrix.diagonal_apply_eq]
  let S : Set ℤ := {k | ∃ ν, IsWt Φ ν ∧ f ν = k}
  have hfin : S.Finite := by
    have hF := Module.End.finite_hasEigenvalue A
    refine (hF.preimage (f := fun k : ℤ => (2 : ℂ) ^ k) (fun a _ b _ h => two_zpow_inj h)).subset ?_
    rintro k ⟨ν, hν, rfl⟩
    exact heig ν hν
  obtain ⟨B, hB⟩ := hfin.bddAbove
  obtain ⟨m, ⟨μ, hμ, rfl⟩, hmax⟩ :=
    Int.exists_greatest_of_bdd (P := fun k => k ∈ S) ⟨B, fun z hz => hB hz⟩ ⟨f μ₀, μ₀, h₀, rfl⟩
  exact ⟨μ, hμ, fun ν hν => hmax _ ⟨ν, hν, rfl⟩⟩

end GlobalTheory.AlgWtHW.MaxWeight
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTorusWeightMaximizingWeightedSumStatement

section

@[expose] public section

open Matrix GlobalTheory.AlgWtHW

theorem _root_.GlobalTheory.T.exists_torusWeight_maximizing_weighted_sum : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ) (μ₀ : Fin n → ℤ), IsWt Φ μ₀ → ∃ μ : Fin n → ℤ, IsWt Φ μ ∧ ∀ ν : Fin n → ℤ, IsWt Φ ν → ∑ i : Fin n, ((n : ℤ) - ((i : ℕ) : ℤ)) * ν i ≤ ∑ i : Fin n, ((n : ℤ) - ((i : ℕ) : ℤ)) * μ i := by
  first | exact @GlobalTheory.AlgWtHW.MaxWeight.exists_max_weight | exact GlobalTheory.AlgWtHW.MaxWeight.exists_max_weight | (intros; apply GlobalTheory.AlgWtHW.MaxWeight.exists_max_weight <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GLUpperTriangularEqDiagonalMulUnitriangular

section

@[expose] public section

open Matrix

namespace GlobalTheory

theorem GL_upperTriangular_eq_diagonal_mul_unitriangular :
    ∀ (n : ℕ) (B : GL (Fin n) ℂ), B.val.BlockTriangular id → ∃ D U : GL (Fin n) ℂ,
      B = D * U ∧ D.val.IsDiag ∧ (∀ i, D.val i i = B.val i i) ∧
      U.val.BlockTriangular id ∧ ∀ i, U.val i i = 1 := by
  intro n B hB
  have hdet : B.val.det = ∏ i, B.val i i := Matrix.det_of_upperTriangular hB
  have hdet0 : B.val.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp B.isUnit).ne_zero
  have hne : ∀ i, B.val i i ≠ 0 := by
    intro i h
    apply hdet0
    rw [hdet]
    exact Finset.prod_eq_zero (Finset.mem_univ i) h
  let D : GL (Fin n) ℂ :=
    ⟨diagonal (fun i => B.val i i), diagonal (fun i => (B.val i i)⁻¹),
      by
        rw [diagonal_mul_diagonal, ← diagonal_one]
        congr 1; funext i; exact mul_inv_cancel₀ (hne i),
      by
        rw [diagonal_mul_diagonal, ← diagonal_one]
        congr 1; funext i; exact inv_mul_cancel₀ (hne i)⟩
  have hU : ∀ i j, (D⁻¹ * B).val i j = (B.val i i)⁻¹ * B.val i j := by
    intro i j
    change (diagonal (fun i => (B.val i i)⁻¹) * B.val) i j = _
    rw [diagonal_mul]
  refine ⟨D, D⁻¹ * B, by simp, isDiag_diagonal _, fun i => diagonal_apply_eq _ _, ?_, ?_⟩
  · intro i j hij
    rw [hU, hB hij, mul_zero]
  · intro i
    rw [hU, inv_mul_cancel₀ (hne i)]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GLUpperTriangularEqDiagonalMulUnitriangularStatement

section

@[expose] public section

open Matrix

theorem _root_.GlobalTheory.T.GL_upperTriangular_eq_diagonal_mul_unitriangular' : ∀ (n : ℕ) (B : GL (Fin n) ℂ), B.val.BlockTriangular id → ∃ D U : GL (Fin n) ℂ, B = D * U ∧ D.val.IsDiag ∧ (∀ i, D.val i i = B.val i i) ∧ U.val.BlockTriangular id ∧ ∀ i, U.val i i = 1 := by
  first | exact @GlobalTheory.GL_upperTriangular_eq_diagonal_mul_unitriangular | exact GlobalTheory.GL_upperTriangular_eq_diagonal_mul_unitriangular | (intros; apply GlobalTheory.GL_upperTriangular_eq_diagonal_mul_unitriangular <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBorelEigenvectorOfPolynomialRepGLComplex

section

@[expose] public section

open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory.AlgWtHW

theorem exists_isBEig_of_isPolyRep :
    ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ),
      IsPolyRep Φ → ∃ (v : ι → ℂ) (lam : Fin n → ℤ), IsBEig Φ v lam := by
  intro n ι _ _ _ Φ hΦ
  obtain ⟨μ₀, hμ₀⟩ := GlobalTheory.T.exists_torusWeight_of_polyRep_GL_complex n ι Φ hΦ
  obtain ⟨μ, ⟨v, hv0, hvw⟩, hmax⟩ := GlobalTheory.T.exists_torusWeight_maximizing_weighted_sum n ι Φ μ₀ hμ₀
  refine ⟨v, μ, hv0, fun B hB => ?_⟩
  have hU : ∀ U : GL (Fin n) ℂ, U.val.BlockTriangular id → (∀ i, U.val i i = 1) → Φ U *ᵥ v = v := by
    refine GlobalTheory.T.unitriangular_induction_on_transvections n (fun U => Φ U *ᵥ v = v) (by simp [hΦ.one]) (fun A C hA hC => ?_) ?_
    · show Φ (A * C) *ᵥ v = v
      rw [hΦ.mul, ← mulVec_mulVec, hC, hA]
    · intro i j hij s C hC
      show Φ C *ᵥ v = v
      obtain ⟨K, w, hw0, hww, hsum⟩ := GlobalTheory.T.exists_transvection_weightVec_expansion n ι Φ hΦ i j (ne_of_lt hij) μ v hvw
      have hz : ∀ k, k ≠ 0 → w k = 0 := by
        intro k hk
        by_contra hne
        have := hmax _ ⟨w k, hne, hww k⟩
        have hk' : (0 : ℤ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
        have hij' : ((i : ℕ) : ℤ) < ((j : ℕ) : ℤ) := by exact_mod_cast hij
        have key : ∑ l : Fin n, ((n : ℤ) - ((l : ℕ) : ℤ)) * ((μ + (k : ℤ) • (Pi.single i 1 - Pi.single j 1) : Fin n → ℤ) l)
            = ∑ l : Fin n, ((n : ℤ) - ((l : ℕ) : ℤ)) * μ l + k * (((n : ℤ) - ((i : ℕ) : ℤ)) - ((n : ℤ) - ((j : ℕ) : ℤ))) := by
          simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
            mul_sub, Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
            Finset.mem_univ, if_true]
          ring
        rw [key] at this
        nlinarith
      rw [hsum s C hC, Finset.sum_eq_single 0 (fun k _ hk => by rw [hz k hk, smul_zero]) (by simp), hw0, pow_zero, one_smul]
  obtain ⟨D, U, rfl, hD, hDd, hUb, hU1⟩ := GlobalTheory.T.GL_upperTriangular_eq_diagonal_mul_unitriangular' n B hB
  rw [hΦ.mul, ← mulVec_mulVec, hU U hUb hU1, hvw D hD]
  simp only [hDd]

end GlobalTheory.AlgWtHW
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBorelEigenvectorOfPolynomialRepGLComplexStatement

section

@[expose] public section

open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

theorem _root_.GlobalTheory.T.exists_borelEigenvector_of_polynomialRepGLComplex : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ → ∃ (v : ι → ℂ) (lam : Fin n → ℤ), IsBEig Φ v lam := by
  first | exact @GlobalTheory.AlgWtHW.exists_isBEig_of_isPolyRep | exact GlobalTheory.AlgWtHW.exists_isBEig_of_isPolyRep | (intros; apply GlobalTheory.AlgWtHW.exists_isBEig_of_isPolyRep <;> assumption)
end
end
