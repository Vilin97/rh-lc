module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffPowEqZeroOfDegreeLt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffXMulOfNotMem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableAtInvApply
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
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
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussianPhaseCriticalValueBlocksGeneral
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussianVectorAnnihilatorEquations
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitDetOneSubConjTransposeMulContractions
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.LogDetSt
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.RingTheory.PiTensorProduct

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussianPairingMomentAlgebra

section

@[expose] public section

open Matrix
open scoped ComplexOrder

namespace GlobalTheory

theorem gaussian_pairing_moment_algebra :
    ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (S T : Matrix σ σ ℂ) (x y : σ → ℂ)
      (t f : ℂ) (p q : σ → ℂ) (m n : Matrix σ σ ℂ),
      Sᵀ = S → Tᵀ = T → IsUnit (1 - (t ^ 2) • (T * S)).det →
      p = t • (f • y + T *ᵥ q) → q = t • (f • x + S *ᵥ p) →
      m = (t * f) • (1 : Matrix σ σ ℂ) + t • vecMulVec y q + t • (T * n) →
      n = t • vecMulVec x q + t • (S * m) →
      (let w : σ → ℂ := (1 - (t ^ 2) • (T * S))⁻¹ *ᵥ (y + t • T *ᵥ x)
       let u : σ → ℂ := x + t • S *ᵥ w
       f * (x ⬝ᵥ y) + x ⬝ᵥ T *ᵥ q + y ⬝ᵥ S *ᵥ p + (S * m * Tᵀ).trace =
         f * (u ⬝ᵥ w + t * (T * S * (1 - (t ^ 2) • (T * S))⁻¹).trace)) := by
  intro σ _ _ S T x y t f p q m n hS hT hA hp hq hm hn w u
  set A : Matrix σ σ ℂ := 1 - (t ^ 2) • (T * S) with hAdef
  have hKA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hA
  have hAK : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hA
  have hAv : ∀ v : σ → ℂ, A *ᵥ v = v - (t ^ 2) • T *ᵥ (S *ᵥ v) := by
    intro v
    rw [hAdef, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.mulVec_mulVec]
  have hAp : A *ᵥ p = (t * f) • (y + t • T *ᵥ x) := by
    have h1 : p = t • (f • y + T *ᵥ (t • (f • x + S *ᵥ p))) := by rw [← hq]; exact hp
    rw [hAv]
    rw [Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul] at h1
    rw [sub_eq_iff_eq_add]
    refine h1.trans ?_
    module
  have hpw : p = (t * f) • w := by
    have : p = A⁻¹ *ᵥ (A *ᵥ p) := by rw [Matrix.mulVec_mulVec, hKA, Matrix.one_mulVec]
    rw [this, hAp, Matrix.mulVec_smul]
  have hqu : q = (t * f) • u := by
    rw [hq, hpw, Matrix.mulVec_smul]
    simp only [u]
    module
  have hAw : A *ᵥ w = y + t • T *ᵥ x := by
    simp only [w]
    rw [Matrix.mulVec_mulVec, hAK, Matrix.one_mulVec]
  have hw : w = y + t • T *ᵥ u := by
    rw [hAv, sub_eq_iff_eq_add] at hAw
    refine hAw.trans ?_
    simp only [u]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul]
    module
  have hAm : A * m = (t * f) • (1 : Matrix σ σ ℂ) + t • vecMulVec (y + t • T *ᵥ x) q := by
    have h1 : m = (t * f) • (1 : Matrix σ σ ℂ) + t • vecMulVec y q
        + t • (T * (t • vecMulVec x q + t • (S * m))) := by rw [← hn]; exact hm
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_vecMulVec,
      ← Matrix.mul_assoc] at h1
    rw [hAdef, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, sub_eq_iff_eq_add,
      Matrix.add_vecMulVec, Matrix.smul_vecMulVec]
    refine h1.trans ?_
    module
  have hmK : m = (t * f) • A⁻¹ + t • vecMulVec w q := by
    have : m = A⁻¹ * (A * m) := by rw [← Matrix.mul_assoc, hKA, Matrix.one_mul]
    rw [this, hAm, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.mul_vecMulVec]
  have htr : (S * m * Tᵀ).trace
      = (t * f) * (T * S * A⁻¹).trace + t * ((S *ᵥ w) ⬝ᵥ (T *ᵥ q)) := by
    rw [hmK, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
      Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.trace_vecMulVec, Matrix.vecMul_transpose,
      hT, Matrix.trace_mul_comm (S * A⁻¹) T, Matrix.mul_assoc T S, smul_eq_mul, smul_eq_mul]
  have huw : u ⬝ᵥ w = x ⬝ᵥ y + t * (x ⬝ᵥ T *ᵥ u) + t * (y ⬝ᵥ S *ᵥ w)
      + t ^ 2 * ((S *ᵥ w) ⬝ᵥ (T *ᵥ u)) := by
    have h1 : u ⬝ᵥ w = (x + t • S *ᵥ w) ⬝ᵥ (y + t • T *ᵥ u) := by rw [← hw]
    rw [h1]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [dotProduct_comm (S *ᵥ w) y]
    ring
  rw [htr, huw, hqu, hpw]
  simp only [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  ring

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrthonormalUnitMono

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc Matrix
open scoped ComplexOrder

namespace GlobalTheory.FockParseval

open MvPolynomial GlobalTheory.FockSeq

variable {σ : Type} [DecidableEq σ]

def unitMono (F : Fock σ) (α : σ →₀ ℕ) : F.H := (wt α)⁻¹ • F.ι (monomial α 1)


omit [DecidableEq σ] in
theorem conj_wt (α : σ →₀ ℕ) : (starRingEnd ℂ) (wt α) = wt α := Complex.conj_ofReal _


omit [DecidableEq σ] in
theorem wt_mul_self (α : σ →₀ ℕ) : wt α * wt α = (mfact α : ℕ) := by
  rw [← star_wt_mul, conj_wt]

theorem orthonormal_unitMono (F : Fock σ) : Orthonormal ℂ (unitMono F) := by
  classical
  rw [orthonormal_iff_ite]
  intro α β
  rw [unitMono, unitMono, inner_smul_left, inner_smul_right, F.fockIP, ← mfact_cast, map_inv₀, conj_wt]
  by_cases h : α = β
  · subst h
    have := wt_ne_zero α
    rw [if_pos rfl, if_pos rfl, ← wt_mul_self]
    field_simp
  · simp [h]

theorem dense_span_unitMono (F : Fock σ) :
    ⊤ ≤ (Submodule.span ℂ (Set.range (unitMono F))).topologicalClosure := by
  intro x _
  refine closure_mono ?_ (F.dense x)
  rintro _ ⟨f, rfl⟩
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg => rw [map_add (f := _)]; exact Submodule.add_mem _ hf hg
  | monomial α c =>
    have e : F.ι (monomial α c) = (c * wt α) • unitMono F α := by
      rw [unitMono, smul_smul, mul_assoc, mul_inv_cancel₀ (wt_ne_zero α), mul_one, ← map_smul, smul_monomial]
      simp
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨α, rfl⟩)

theorem inner_unitMono {F : Fock σ} {v : F.H} {E : MvPowerSeries σ ℂ} (h : HasCoeff F v E) (α : σ →₀ ℕ) :
    inner ℂ (unitMono F α) v = wt α * MvPowerSeries.coeff α E := by
  have := wt_ne_zero α
  rw [unitMono, inner_smul_left, h α, ← mfact_cast, map_inv₀, conj_wt, ← wt_mul_self]
  field_simp

theorem parseval (σ : Type) [DecidableEq σ] (F : Fock σ) (v w : F.H) (E E' : MvPowerSeries σ ℂ)
    (hv : HasCoeff F v E) (hw : HasCoeff F w E') :
    Summable (fun α : σ →₀ ℕ => (GlobalTheory.FockSeq.mfact α : ℝ) * ‖MvPowerSeries.coeff α E‖ ^ 2) ∧
      inner ℂ v w = ∑' α : σ →₀ ℕ, (GlobalTheory.FockSeq.mfact α : ℂ) * (starRingEnd ℂ) (MvPowerSeries.coeff α E) *
        MvPowerSeries.coeff α E' := by
  refine ⟨((orthonormal_unitMono F).inner_products_summable v).congr fun α => ?_, ?_⟩
  · rw [inner_unitMono hv, norm_mul, mul_pow, wt, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt (Nat.cast_nonneg _)]
  · let b := HilbertBasis.mk (orthonormal_unitMono F) (dense_span_unitMono F)
    rw [← b.tsum_inner_mul_inner v w]
    refine tsum_congr fun α => ?_
    rw [HilbertBasis.coe_mk, ← inner_conj_symm, inner_unitMono hv, inner_unitMono hw, map_mul, conj_wt,
      ← wt_mul_self]
    ring

end GlobalTheory.FockParseval
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricBlockTraceInverseEqTwoMul

section

@[expose] public section

open Matrix
open scoped ComplexOrder

namespace GlobalTheory.FockDetDer

theorem trace_fromBlocks_diag {m n : Type} [Fintype m] [Fintype n]
    (X : Matrix m m ℂ) (Y : Matrix n n ℂ) :
    (fromBlocks X 0 0 Y).trace = X.trace + Y.trace := by
  simp [Matrix.trace, Fintype.sum_sum_type]

theorem symmetric_block_trace_inverse_eq_two_mul {P Q : ℕ} (C : Matrix (Fin Q) (Fin P) ℂ) (B : Matrix (Fin P) (Fin Q) ℂ) (c : ℂ)
    (h : IsUnit (1 - c • (C * B)).det) :
    IsUnit (1 - c • ((fromBlocks 0 B Bᵀ 0 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) *
      (fromBlocks 0 Cᵀ C 0 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ))).det ∧
    ((fromBlocks 0 B Bᵀ 0 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) *
      (fromBlocks 0 Cᵀ C 0 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) *
      (1 - c • ((fromBlocks 0 B Bᵀ 0 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) *
      (fromBlocks 0 Cᵀ C 0 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)))⁻¹).trace =
      2 * ((1 - c • (C * B))⁻¹ * (C * B)).trace := by
  have hTS : (fromBlocks 0 B Bᵀ 0 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) *
      (fromBlocks 0 Cᵀ C 0 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) =
      fromBlocks (B * C) 0 0 (C * B)ᵀ := by
    rw [fromBlocks_multiply]; simp
  have h1 : (1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) - c • fromBlocks (B * C) 0 0 (C * B)ᵀ =
      fromBlocks (1 - c • (B * C)) 0 0 (1 - c • (C * B))ᵀ := by
    rw [← fromBlocks_one]
    ext (i | i) (j | j) <;> simp [Matrix.one_apply, eq_comm]
  have hd : (1 - c • (B * C)).det = (1 - c • (C * B)).det := by
    rw [← Matrix.smul_mul, det_one_sub_mul_comm, Matrix.mul_smul]
  have h' : IsUnit (1 - c • (B * C)).det := hd ▸ h
  rw [hTS, h1]
  refine ⟨?_, ?_⟩
  · rw [det_fromBlocks_zero₂₁, det_transpose]
    exact h'.mul h
  · have hinv : (fromBlocks (1 - c • (B * C)) 0 0 (1 - c • (C * B))ᵀ)⁻¹ =
        fromBlocks (1 - c • (B * C))⁻¹ 0 0 ((1 - c • (C * B))⁻¹)ᵀ := by
      apply Matrix.inv_eq_left_inv
      rw [fromBlocks_multiply, ← transpose_mul, nonsing_inv_mul _ h', mul_nonsing_inv _ h]
      simp
    have hMB : (1 - c • (B * C))⁻¹ * B = B * (1 - c • (C * B))⁻¹ := by
      have e : B * (1 - c • (C * B)) = (1 - c • (B * C)) * B := by
        simp [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
      calc (1 - c • (B * C))⁻¹ * B
          = (1 - c • (B * C))⁻¹ * B * ((1 - c • (C * B)) * (1 - c • (C * B))⁻¹) := by
            rw [mul_nonsing_inv _ h, Matrix.mul_one]
        _ = (1 - c • (B * C))⁻¹ * (B * (1 - c • (C * B))) * (1 - c • (C * B))⁻¹ := by
            simp only [Matrix.mul_assoc]
        _ = B * (1 - c • (C * B))⁻¹ := by
            rw [e, ← Matrix.mul_assoc, nonsing_inv_mul _ h', Matrix.one_mul]
    rw [hinv, fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    rw [trace_fromBlocks_diag, ← transpose_mul, trace_transpose, two_mul]
    congr 1
    rw [trace_mul_comm (B * C), ← Matrix.mul_assoc, hMB, Matrix.mul_assoc, trace_mul_comm B,
      Matrix.mul_assoc]

theorem hasDerivAt_det_one_sub_sq :
    ∀ (P Q : ℕ) (A B : Matrix (Fin P) (Fin Q) ℂ) (t : ℝ),
      IsUnit (1 - ((t : ℂ) ^ 2) • (Aᴴ * B)).det →
      let S : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ := fromBlocks 0 (Matrix.transpose Aᴴ) Aᴴ 0
      let T : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ := fromBlocks 0 B Bᵀ 0
      IsUnit (1 - ((t : ℂ) ^ 2) • (T * S)).det ∧
        HasDerivAt (fun s : ℝ => (1 - ((s : ℂ) ^ 2) • (Aᴴ * B)).det)
          (-((t : ℂ) * (T * S * (1 - ((t : ℂ) ^ 2) • (T * S))⁻¹).trace) *
            (1 - ((t : ℂ) ^ 2) • (Aᴴ * B)).det) t := by
  intro P Q A B t h S T
  obtain ⟨h1, h2⟩ := symmetric_block_trace_inverse_eq_two_mul Aᴴ B ((t : ℂ) ^ 2) h
  refine ⟨h1, ?_⟩
  have hsq : HasDerivAt (fun s : ℝ => (s : ℂ) ^ 2) (2 * (t : ℂ)) t := by
    have := (hasDerivAt_pow 2 (t : ℂ)).comp_ofReal
    simpa using this
  have hd := ReciprocityTheory.GeometryOfNumbersTheory.hasDerivAt_det (fun s : ℝ => 1 - ((s : ℂ) ^ 2) • (Aᴴ * B))
    (-((2 * (t : ℂ)) • (Aᴴ * B))) t (fun i j => by
      have := (hsq.mul_const ((Aᴴ * B) i j)).const_sub ((1 : Matrix (Fin Q) (Fin Q) ℂ) i j)
      simpa using this)
  refine hd.congr_deriv ?_
  have hne := h.ne_zero
  have hadj : (1 - ((t : ℂ) ^ 2) • (Aᴴ * B)).adjugate =
      (1 - ((t : ℂ) ^ 2) • (Aᴴ * B)).det • (1 - ((t : ℂ) ^ 2) • (Aᴴ * B))⁻¹ := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv', smul_smul, mul_inv_cancel₀ hne, one_smul]
  simp only [S, T]
  rw [h2, hadj, Matrix.smul_mul, Matrix.mul_neg, Matrix.mul_smul, trace_smul, trace_neg, trace_smul]
  simp only [smul_eq_mul]
  ring

end GlobalTheory.FockDetDer
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerGaussianVectorsFockSpace

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc Matrix
open scoped ComplexOrder

namespace GlobalTheory.GaussInner

theorem pairing_mul_eq_exp {σ : Type} [Fintype σ] [DecidableEq σ] (S T : Matrix σ σ ℂ) (x y : σ → ℂ)
    (E E' : MvPowerSeries σ ℂ) (hS : Sᵀ = S) (hT : Tᵀ = T)
    (hE : Summable (fun α : σ →₀ ℕ => (GlobalTheory.FockSeq.mfact α : ℝ) * ‖MvPowerSeries.coeff α E‖ ^ 2))
    (hE' : Summable (fun α : σ →₀ ℕ => (GlobalTheory.FockSeq.mfact α : ℝ) * ‖MvPowerSeries.coeff α E'‖ ^ 2))
    (h0 : MvPowerSeries.coeff 0 E = 1) (h0' : MvPowerSeries.coeff 0 E' = 1)
    (hd : ∀ l α, ((α l : ℂ) + 1) * MvPowerSeries.coeff (α + Finsupp.single l 1) E =
      MvPowerSeries.coeff α (x l • E + ∑ k, S l k • (MvPowerSeries.X k * E)))
    (hd' : ∀ l α, ((α l : ℂ) + 1) * MvPowerSeries.coeff (α + Finsupp.single l 1) E' =
      MvPowerSeries.coeff α (y l • E' + ∑ k, T l k • (MvPowerSeries.X k * E')))
    (D : ℝ → ℂ) (hD0 : D 0 = 1)
    (hD : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsUnit (1 - ((t : ℂ) ^ 2) • (T * S)).det ∧
      HasDerivAt D (-((t : ℂ) * (T * S * (1 - ((t : ℂ) ^ 2) • (T * S))⁻¹).trace) * D t) t) :
    (∑' α : σ →₀ ℕ, (GlobalTheory.FockSeq.mfact α : ℂ) * MvPowerSeries.coeff α E * MvPowerSeries.coeff α E') * D 1 =
      Complex.exp (1 / 2 * (x ⬝ᵥ (1 - T * S)⁻¹ *ᵥ (y + T *ᵥ x) +
        y ⬝ᵥ (x + S *ᵥ ((1 - T * S)⁻¹ *ᵥ (y + T *ᵥ x))))) := by
  obtain ⟨hc, hm⟩ := moments σ S T x y E E' hE hE' hd hd'
  set f : ℝ → ℂ := fun s => ∑' α : σ →₀ ℕ, (s : ℂ) ^ α.degree *
    ((GlobalTheory.FockSeq.mfact α : ℂ) * MvPowerSeries.coeff α E * MvPowerSeries.coeff α E') with hf
  set w : ℝ → σ → ℂ := fun s => (1 - ((s : ℂ) ^ 2) • (T * S))⁻¹ *ᵥ (y + (s : ℂ) • T *ᵥ x) with hw
  set u : ℝ → σ → ℂ := fun s => x + (s : ℂ) • S *ᵥ w s with hu
  set Φ : ℝ → ℂ := fun s => (s : ℂ) / 2 * (x ⬝ᵥ w s + y ⬝ᵥ u s) with hΦ
  have hΦ' : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt Φ (u t ⬝ᵥ w t) t := fun t ht =>
    GlobalTheory.Mem.GaussPhase.hasDerivAt_phase σ S T x y t hS hT (hD t ht).1
  have hg : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (fun s => f s * D s * Complex.exp (-Φ s)) 0 t := by
    intro t ht
    have ht' := Set.Ioo_subset_Icc_self ht
    obtain ⟨p, q, m, n, h1, h2, h3, h4, h5⟩ := hm t ht
    have h6 := GlobalTheory.gaussian_pairing_moment_algebra σ S T x y t (f t) p q m n hS hT (hD t ht').1 h1 h2 h3 h4
    change _ = f t * (u t ⬝ᵥ w t + _) at h6
    rw [h6] at h5
    refine ((h5.fun_mul (hD t ht').2).fun_mul (hΦ' t ht').fun_neg.cexp).congr_deriv ?_
    ring
  have hgc : ContinuousOn (fun s => f s * D s * Complex.exp (-Φ s)) (Set.Icc 0 1) :=
    (hc.mul fun t ht => (hD t ht).2.continuousAt.continuousWithinAt).mul
      fun t ht => (hΦ' t ht).fun_neg.cexp.continuousAt.continuousWithinAt
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hgc hg
    intervalIntegrable_const
  have f0 : f 0 = 1 := by
    simp only [hf]
    rw [tsum_eq_single 0]
    · simp [h0, h0', GlobalTheory.FockSeq.mfact]
    · intro α hα
      have : α.degree ≠ 0 := fun h => hα ((Finsupp.degree_eq_zero_iff α).1 h)
      simp [this]
  have Φ0 : Φ 0 = 0 := by simp [hΦ]
  rw [f0, hD0, Φ0, intervalIntegral.integral_zero, Complex.exp_neg] at key
  have e : f 1 * D 1 = Complex.exp (Φ 1) := by
    have := Complex.exp_ne_zero (Φ 1)
    simp only [neg_zero, Complex.exp_zero, mul_one] at key
    field_simp at key
    linear_combination -key
  simpa [hf, hΦ, hu, hw] using e

theorem deriv_gauss {P Q : ℕ} (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) (l : Ix P Q) (α : Ix P Q →₀ ℕ) :
    ((α l : ℂ) + 1) * MvPowerSeries.coeff (α + Finsupp.single l 1) (expPS (gaussPoly A x)) =
      MvPowerSeries.coeff α (x l • expPS (gaussPoly A x) +
        ∑ k, fromBlocks 0 A Aᵀ 0 l k • (MvPowerSeries.X k * expPS (gaussPoly A x))) := by
  rw [GlobalTheory.OscExpDeriv.coeff_deriv_expPS _ _ (coeff_zero_gaussPoly A x)]
  congr 1
  rcases l with i | j

  · rw [GlobalTheory.OscGauss.pderiv_inl_gaussPoly, ← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_add (f := _), map_sum]
    simp [MvPolynomial.coeToMvPowerSeries.ringHom_apply, Fintype.sum_sum_type, add_mul, Finset.sum_mul, MvPowerSeries.smul_eq_C_mul, mul_assoc]

  · rw [GlobalTheory.OscGauss.pderiv_inr_gaussPoly, ← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_add (f := _), map_sum]
    simp [MvPolynomial.coeToMvPowerSeries.ringHom_apply, Fintype.sum_sum_type, add_mul, Finset.sum_mul, MvPowerSeries.smul_eq_C_mul, mul_assoc]

theorem posDef_smul {P Q : ℕ} {B : Matrix (Fin P) (Fin Q) ℂ} (hB : (1 - Bᴴ * B).PosDef) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : (1 - (((t : ℂ) ^ 2) • B)ᴴ * (((t : ℂ) ^ 2) • B)).PosDef := by
  have h4 : (0 : ℂ) ≤ ((1 - t ^ 4 : ℝ) : ℂ) :=
    Complex.zero_le_real.2 (sub_nonneg.2 (pow_le_one₀ ht.1 ht.2))
  have e : 1 - (((t : ℂ) ^ 2) • B)ᴴ * (((t : ℂ) ^ 2) • B) = (1 - Bᴴ * B) + ((1 - t ^ 4 : ℝ) : ℂ) • (Bᴴ * B) := by
    rw [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have : star ((t : ℂ) ^ 2) * (t : ℂ) ^ 2 = (t : ℂ) ^ 4 := by simp; ring
    rw [this]; push_cast; module
  rw [e]
  exact hB.add_posSemidef ((posSemidef_conjTranspose_mul_self B).smul h4)

theorem inner_gauss_gauss : ∀ (P Q : ℕ) (F : Fock (Ix P Q)) (A B : Matrix (Fin P) (Fin Q) ℂ) (x y : Ix P Q → ℂ), (1 - Aᴴ * A).PosDef → (1 - Bᴴ * B).PosDef → ∀ v w : F.H, HasCoeff F v (expPS (gaussPoly A x)) → HasCoeff F w (expPS (gaussPoly B y)) → let a : Fin P → ℂ := fun i => star (x (Sum.inl i)); let b : Fin Q → ℂ := fun j => star (x (Sum.inr j)); let c : Fin P → ℂ := fun i => y (Sum.inl i); let d : Fin Q → ℂ := fun j => y (Sum.inr j); let M := (1 - B * Aᴴ)⁻¹; let N := (1 - Aᴴ * B)⁻¹; inner ℂ v w = ((1 - Aᴴ * B).det)⁻¹ * Complex.exp (a ⬝ᵥ M *ᵥ c + d ⬝ᵥ N *ᵥ b + a ⬝ᵥ (M * B) *ᵥ b + d ⬝ᵥ (N * Aᴴ) *ᵥ c) := by
  intro P Q F A B x y hA hB v w hv hw a b c d M N
  obtain ⟨s1, hin⟩ := GlobalTheory.FockParseval.parseval _ F v w _ _ hv hw
  obtain ⟨s2, -⟩ := GlobalTheory.FockParseval.parseval _ F w w _ _ hw hw
  have hU : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsUnit (1 - ((t : ℂ) ^ 2) • (Aᴴ * B)).det := fun t ht => by
    simpa only [Matrix.mul_smul] using
      GlobalTheory.isUnit_det_one_sub_conjTranspose_mul_of_contractions P Q A _ hA (posDef_smul hB ht)
  have hU1 : IsUnit (1 - Aᴴ * B).det := by simpa using hU 1 ⟨zero_le_one, le_rfl⟩
  have hy : y = Sum.elim c d := by ext (i | j) <;> rfl
  have key := pairing_mul_eq_exp (fromBlocks 0 Aᴴᵀ Aᴴ 0) (fromBlocks 0 B Bᵀ 0) (Sum.elim a b) y
    (MvPowerSeries.map (starRingEnd ℂ) (expPS (gaussPoly A x))) (expPS (gaussPoly B y))
    (by simp [fromBlocks_transpose]) (by simp [fromBlocks_transpose]) (by simpa using s1) s2
    (by rw [MvPowerSeries.coeff_map]; simp [expPS, MvPowerSeries.coeff_apply]) (by simp [expPS, MvPowerSeries.coeff_apply])
    (fun l α => by
      have := congrArg (starRingEnd ℂ) (deriv_gauss A x l α)
      rw [← MvPowerSeries.coeff_map (f := starRingEnd ℂ) (n := α)] at this
      rcases l with i | j <;>
        simpa [MvPowerSeries.smul_eq_C_mul, Fintype.sum_sum_type, a, b] using this)
    (deriv_gauss B y) (fun s : ℝ => (1 - ((s : ℂ) ^ 2) • (Aᴴ * B)).det) (by simp)
    (fun t ht => GlobalTheory.FockDetDer.hasDerivAt_det_one_sub_sq P Q A B t (hU t ht))
  have hb := GlobalTheory.gaussian_phase_critical_value_blocks P Q A B a c b d hU1
  simp only [← hy] at hb
  rw [hb] at key
  simp only [MvPowerSeries.coeff_map, Complex.ofReal_one, one_pow, one_smul] at key
  rw [hin, ← key, mul_comm, mul_assoc, mul_inv_cancel₀ hU1.ne_zero, mul_one]

end GlobalTheory.GaussInner
end
end
end
