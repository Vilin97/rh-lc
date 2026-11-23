module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SDarb
public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Em0Injective
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
import Development.WeilBound.ThetaLifts.LatticeBasics.Hypotheses2
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Lean.Elab.MutualDef
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.BilinearFormExamples.AdelicCoordinatesEvalZeroFormMemAdmissible
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.BilinearFormExamples.BfEqSumRight
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.BilinearFormExamples.MapCAMul
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.BilinearFormExamples.BfENondeg

section

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ldexa
open PositivityTheory.SiegelWeilFormula.Ald

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable {m n : ℕ}

def BfE (σ : E →ₐ[F] E) (J : Matrix (Fin m) (Fin m) E) : LinearMap.BilinForm F (Matrix (Fin m) (Fin n) E) :=
  LinearMap.mk₂ F (fun x z => Algebra.trace F E (xᵀ * J * z.map σ).trace)
    (fun x x' z => by simp [Matrix.transpose_add, Matrix.add_mul, Matrix.trace_add])
    (fun c x z => by simp [Matrix.transpose_smul, Matrix.smul_mul, Matrix.trace_smul])
    (fun x z z' => by simp [Matrix.map_add _ (map_add σ), Matrix.mul_add, Matrix.trace_add])
    (fun c x z => by
      have : (c • z).map σ = c • z.map σ := by ext i j; exact σ.toLinearMap.map_smul c (z i j)
      simp [this, Matrix.mul_smul, Matrix.trace_smul])

theorem BfE_apply (σ : E →ₐ[F] E) (J : Matrix (Fin m) (Fin m) E) (x z : Matrix (Fin m) (Fin n) E) :
    BfE σ J x z = Algebra.trace F E (xᵀ * J * z.map σ).trace := rfl

theorem BfE_nondeg [FiniteDimensional F E] (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) (J : Matrix (Fin m) (Fin m) E)
    (hJ : J.det ≠ 0) : (BfE (n := n) σ J).Nondegenerate := by
  have hdet : IsUnit J.det := isUnit_iff_ne_zero.mpr hJ
  have hdetT : IsUnit Jᵀ.det := by
    rw [Matrix.det_transpose]
    exact hdet
  have htr1 : Algebra.trace F E 1 ≠ 0 := by
    rw [← map_one (algebraMap F E), Algebra.trace_algebraMap]
    simp only [nsmul_eq_mul, mul_one, ne_eq, Nat.cast_eq_zero]
    exact Module.finrank_pos.ne'
  refine ⟨fun x hx => ?_, fun z hz => ?_⟩
  · by_contra hne
    have hy : Jᵀ * x ≠ 0 := by
      intro h0
      apply hne
      have h2 := congrArg (fun M => (Jᵀ)⁻¹ * M) h0
      simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdetT] using h2
    obtain ⟨b0, j0, hb⟩ : ∃ b j, (Jᵀ * x) b j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hy (Matrix.ext h)
    have h1 := hx ((Matrix.single b0 j0 ((Jᵀ * x) b0 j0)⁻¹).map σ)
    have hσσ : ((Matrix.single b0 j0 ((Jᵀ * x) b0 j0)⁻¹).map σ).map σ =
        Matrix.single b0 j0 ((Jᵀ * x) b0 j0)⁻¹ := by
      ext a b
      simp only [Matrix.map_apply]
      exact hσ _
    have hswap : (xᵀ * J) j0 b0 = (Jᵀ * x) b0 j0 := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    have hv : (xᵀ * J * Matrix.single b0 j0 ((Jᵀ * x) b0 j0)⁻¹).trace = 1 := by
      rw [Matrix.trace_mul_single, hswap, op_smul_eq_mul, mul_inv_cancel₀ hb]
    rw [BfE_apply, hσσ, hv] at h1
    exact htr1 h1
  · by_contra hne
    have hw : J * z.map σ ≠ 0 := by
      intro h0
      apply hne
      have hz0 : z.map σ = 0 := by
        have h2 := congrArg (fun M => J⁻¹ * M) h0
        simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet] using h2
      ext a b
      have := congrFun (congrFun hz0 a) b
      simp only [Matrix.map_apply, Matrix.zero_apply] at this
      rw [Matrix.zero_apply, ← hσ (z a b), this, map_zero]
    obtain ⟨a0, b0, hb⟩ : ∃ a b, (J * z.map σ) a b ≠ 0 := by
      by_contra h
      push_neg at h
      exact hw (Matrix.ext h)
    have h1 := hz (Matrix.single a0 b0 ((J * z.map σ) a0 b0)⁻¹)
    have hv : ((Matrix.single a0 b0 ((J * z.map σ) a0 b0)⁻¹)ᵀ * J * z.map σ).trace = 1 := by
      rw [Matrix.mul_assoc, Matrix.transpose_single, Matrix.trace_single_mul]
      simp [inv_mul_cancel₀ hb, mul_inv_cancel₀ hb]
    rw [BfE_apply, hv] at h1
    exact htr1 h1

end PositivityTheory.SiegelWeilFormula.Ldexa
end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.BilinearFormExamples.EQSymmApply

section

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ldexa
open PositivityTheory.SiegelWeilFormula.Ald

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable {m n : ℕ}

def Gm (σ : E →ₐ[F] E) (J : Matrix (Fin m) (Fin m) E) (bs : Module.Basis (Fin 2) F E) :
    Matrix (Fin m × Fin n × Fin 2) (Fin m × Fin n × Fin 2) F :=
  LinearMap.BilinForm.toMatrix (bs.matrix (Fin m) (Fin n)) (BfE σ J)

theorem Gm_det [FiniteDimensional F E] (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) (J : Matrix (Fin m) (Fin m) E)
    (hJ : J.det ≠ 0) (bs : Module.Basis (Fin 2) F E) : (Gm (n := n) σ J bs).det ≠ 0 :=
  (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero _).1 (BfE_nondeg σ hσ J hJ)

theorem Bf_Ek_Ek [FiniteDimensional F E] (σ : E →ₐ[F] E) (J : Matrix (Fin m) (Fin m) E) (bs : Module.Basis (Fin 2) F E)
    (k k' : Fin m × Fin n × Fin 2) : Bf σ J (Ek bs k) (Ek bs k') = algebraMap F (AF F) (Gm σ J bs k k') := by
  obtain ⟨i, j, l⟩ := k
  obtain ⟨i', j', l'⟩ := k'
  have hE : ∀ (a : Fin m) (b : Fin n) (c : Fin 2), Ek bs (a, b, c) = incM F (Matrix.single a b (bs c)) := by
    intro a b c
    ext x y
    by_cases hx : a = x <;> by_cases hy : b = y <;> simp [Ek, incM, Matrix.single_apply, inclR, hx, hy]
  have hc : ∀ M : Matrix (Fin m) (Fin n) E, (incM F M).map (cA σ) = incM F (M.map σ) := by
    intro M
    ext x y
    simp [incM, cA, inclR]
  have htr : ∀ M : Matrix (Fin m) (Fin n) E, (incM F M)ᵀ = incM F Mᵀ := by
    intro M
    ext x y
    rfl
  have ht : ∀ M : Matrix (Fin n) (Fin n) E, (incM F M).trace = inclR (F := F) (E := E) (AF F) M.trace := by
    intro M
    rw [incM, AddMonoidHom.map_trace]
  rw [Gm, LinearMap.BilinForm.toMatrix_apply, Module.Basis.matrix_apply, Module.Basis.matrix_apply, Bf, hE, hE, hc,
    htr, ← incM_mul, ← incM_mul, ht, trace_inclR']
  rfl

def bM (bs : Module.Basis (Fin 2) F E) : Module.Basis (Fin m × Fin n × Fin 2) (AF F) (Mx F E m n) :=
  (Algebra.TensorProduct.basis (AF F) bs).matrix (Fin m) (Fin n)

theorem bM_repr (bs : Module.Basis (Fin 2) F E) (X : Mx F E m n) (k : Fin m × Fin n × Fin 2) :
    (bM bs).repr X k = crdB bs X k := by
  obtain ⟨i, j, l⟩ := k
  simp [bM, Module.Basis.matrix, crdB, Pi.basis_repr]

theorem incM_one {ι : Type} [Fintype ι] [DecidableEq ι] : incM F (1 : Matrix ι ι E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

def eQ (b : GL (Fin n ⊕ Fin n) E) : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E) ≃ₗ[AF F] Mx F E m n × Mx F E m n :=
  LinearEquiv.ofLinear
    { toFun := fun w => ((w * (incM F (b⁻¹).1)ᵀ).toCols₁, (w * (incM F (b⁻¹).1)ᵀ).toCols₂)
      map_add' := fun w w' => by rw [Matrix.add_mul]; rfl
      map_smul' := fun c w => by rw [Matrix.smul_mul]; rfl }
    { toFun := fun p => p.1 * (incM F b.1.toCols₁)ᵀ + p.2 * (incM F b.1.toCols₂)ᵀ
      map_add' := fun p p' => by simp [Matrix.add_mul]; abel
      map_smul' := fun c p => by simp [Matrix.smul_mul, smul_add] }
    (by
      refine LinearMap.ext fun p => ?_
      obtain ⟨Z, X⟩ := p
      have h1 : (incM F b.1)ᵀ * (incM F (b⁻¹).1)ᵀ = 1 := by
        rw [← Matrix.transpose_mul, ← incM_mul, Units.inv_mul, incM_one, Matrix.transpose_one]
      show (((Z * (incM F b.1.toCols₁)ᵀ + X * (incM F b.1.toCols₂)ᵀ) * (incM F (b⁻¹).1)ᵀ).toCols₁,
        ((Z * (incM F b.1.toCols₁)ᵀ + X * (incM F b.1.toCols₂)ᵀ) * (incM F (b⁻¹).1)ᵀ).toCols₂) = (Z, X)
      rw [show Z * (incM F b.1.toCols₁)ᵀ + X * (incM F b.1.toCols₂)ᵀ = Matrix.fromCols Z X * (incM F b.1)ᵀ by
        rw [incM_b, Matrix.fromCols_mul_fromRows], Matrix.mul_assoc, h1, Matrix.mul_one]
      simp)
    (by
      refine LinearMap.ext fun w => ?_
      have h1 : (incM F (b⁻¹).1)ᵀ * (incM F b.1)ᵀ = 1 := by
        rw [← Matrix.transpose_mul, ← incM_mul, Units.mul_inv, incM_one, Matrix.transpose_one]
      show (w * (incM F (b⁻¹).1)ᵀ).toCols₁ * (incM F b.1.toCols₁)ᵀ + (w * (incM F (b⁻¹).1)ᵀ).toCols₂ * (incM F b.1.toCols₂)ᵀ = w
      rw [← Matrix.fromCols_mul_fromRows, ← incM_b, Matrix.fromCols_toCols, Matrix.mul_assoc, h1, Matrix.mul_one])

theorem eQ_symm_apply (b : GL (Fin n ⊕ Fin n) E) (Z X : Mx F E m n) :
    (eQ b).symm (Z, X) = Z * (incM F b.1.toCols₁)ᵀ + X * (incM F b.1.toCols₂)ᵀ := rfl

theorem eQ_frame (b : GL (Fin n ⊕ Fin n) E) (Z X : Mx F E m n) :
    eQ b (Z * (incM F b.1.toCols₁)ᵀ + X * (incM F b.1.toCols₂)ᵀ) = (Z, X) := by
  rw [← eQ_symm_apply, LinearEquiv.apply_symm_apply]

end PositivityTheory.SiegelWeilFormula.Ldexa
end
end
end
