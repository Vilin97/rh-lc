module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnfoldingConstantsPos
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumNormSqOrthonormalLeHilbertSchmidt

section

@[expose] public section

open Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory

theorem hsNormSq_eq_sum_stdBasis {V H : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (A : V →L[ℂ] H) :
    hsNormSq A = ∑ i, ‖A (stdOrthonormalBasis ℂ V i)‖ ^ 2 := by
  unfold hsNormSq hsInner
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact inner_self_eq_norm_sq (𝕜 := ℂ) _

theorem sum_norm_sq_le_hsNormSq {V H : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (A : V →L[ℂ] H) {ι : Type} [Fintype ι] (v : ι → V) (hv : Orthonormal ℂ v) :
    ∑ i, ‖A (v i)‖ ^ 2 ≤ hsNormSq A := by
  set e := stdOrthonormalBasis ℂ V with he
  set f := stdOrthonormalBasis ℂ H
  have key : ∀ (x : V) (y : H), ‖⟪y, A x⟫_ℂ‖ = ‖⟪x, (ContinuousLinearMap.adjoint A) y⟫_ℂ‖ := by
    intro x y
    rw [← ContinuousLinearMap.adjoint_inner_left, norm_inner_symm]
  calc ∑ i, ‖A (v i)‖ ^ 2
      = ∑ i, ∑ j, ‖⟪f j, A (v i)⟫_ℂ‖ ^ 2 := by
        simp_rw [f.sum_sq_norm_inner_right]
    _ = ∑ j, ∑ i, ‖⟪v i, (ContinuousLinearMap.adjoint A) (f j)⟫_ℂ‖ ^ 2 := by
        rw [Finset.sum_comm]
        simp_rw [key]
    _ ≤ ∑ j, ‖(ContinuousLinearMap.adjoint A) (f j)‖ ^ 2 :=
        Finset.sum_le_sum fun j _ => hv.sum_inner_products_le _
    _ = ∑ j, ∑ i, ‖⟪e i, (ContinuousLinearMap.adjoint A) (f j)⟫_ℂ‖ ^ 2 := by
        simp_rw [e.sum_sq_norm_inner_right]
    _ = ∑ i, ∑ j, ‖⟪f j, A (e i)⟫_ℂ‖ ^ 2 := by
        rw [Finset.sum_comm]
        simp_rw [key]
    _ = hsNormSq A := by
        rw [hsNormSq_eq_sum_stdBasis, ← he]
        simp_rw [f.sum_sq_norm_inner_right]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumNormSqOrthonormalLeHilbertSchmidtStatement

section

@[expose] public section

open Formalism.MainNotions.S
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.sum_norm_sq_orthonormal_le_hilbertSchmidt : ∀ {V H : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (A : V →L[ℂ] H) {ι : Type} [Fintype ι] (v : ι → V), Orthonormal ℂ v → ∑ i, ‖A (v i)‖ ^ 2 ≤ hsNormSq A := by
  first | exact @GlobalTheory.sum_norm_sq_le_hsNormSq | exact GlobalTheory.sum_norm_sq_le_hsNormSq | (intros; apply GlobalTheory.sum_norm_sq_le_hsNormSq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinrankKerLeHilbertSchmidtNormSqSubId

section

@[expose] public section

open Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory

theorem finrank_ker_le_hsNormSq_sub_id {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (K : V →L[ℂ] V) (N : Submodule ℂ V) (hN : ∀ x ∈ N, K x = 0) :
    (Module.finrank ℂ N : ℝ) ≤ hsNormSq (K - ContinuousLinearMap.id ℂ V) := by
  let b := stdOrthonormalBasis ℂ N
  let v : Fin (Module.finrank ℂ N) → V := fun i => (b i : V)
  have hv : Orthonormal ℂ v := b.orthonormal.comp_linearIsometry N.subtypeₗᵢ
  have h := GlobalTheory.T.sum_norm_sq_orthonormal_le_hilbertSchmidt (K - ContinuousLinearMap.id ℂ V) v hv
  have hterm : ∀ i, ‖(K - ContinuousLinearMap.id ℂ V) (v i)‖ ^ 2 = 1 := by
    intro i
    have hK : K (v i) = 0 := hN _ (b i).2
    have hn : ‖v i‖ = 1 := hv.1 i
    simp [hK, hn]
  have hsum : ∑ i, ‖(K - ContinuousLinearMap.id ℂ V) (v i)‖ ^ 2 = (Module.finrank ℂ N : ℝ) := by
    rw [Finset.sum_congr rfl (fun i _ => hterm i)]
    simp
  rw [hsum] at h
  exact h

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinrankKerLeHilbertSchmidtNormSqSubIdStatement

section

@[expose] public section

open Formalism.MainNotions.S
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.finrank_ker_le_hilbertSchmidtNormSq_sub_id : ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (K : V →L[ℂ] V) (N : Submodule ℂ V), (∀ x ∈ N, K x = 0) → (Module.finrank ℂ N : ℝ) ≤ hsNormSq (K - ContinuousLinearMap.id ℂ V) := by
  first | exact @GlobalTheory.finrank_ker_le_hsNormSq_sub_id | exact GlobalTheory.finrank_ker_le_hsNormSq_sub_id | (intros; apply GlobalTheory.finrank_ker_le_hsNormSq_sub_id <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinrankKerPuLeHsDev

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.S GlobalTheory.Core.Rk
open scoped InnerProductSpace

namespace GlobalTheory.Core.Rk

theorem finrank_ker_Pu_le_hsDev (D : D7) (u : D.what₂.Word) :
    (Module.finrank ℂ (LinearMap.ker (D.s.Pu u : D.s.Cu u →ₗ[ℂ] D.s.HH)) : ℝ) ≤ hsDev D u := by
  unfold hsDev
  refine GlobalTheory.T.finrank_ker_le_hilbertSchmidtNormSq_sub_id (Kmat D.s u u) _ ?_
  intro x hx
  rw [LinearMap.mem_ker] at hx
  have hx' : D.s.Pu u x = 0 := hx
  simp [Kmat, hx']

end GlobalTheory.Core.Rk
end
end
