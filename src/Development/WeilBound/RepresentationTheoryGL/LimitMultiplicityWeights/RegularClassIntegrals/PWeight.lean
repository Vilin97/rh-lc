module

public import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.ClosedGraph
public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.Separable
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
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqOfNearOfCharpolyEq

section

@[expose] public section

open MeasureTheory Set Filter Matrix
open scoped ENNReal NNReal Topology

namespace GlobalTheory.CompanionTheory.WeylNear

theorem exists_diag (n : ℕ) (s : Matrix (Fin n) (Fin n) ℂ) (hs : s.charpoly.Separable) :
    ∃ (P Q : Matrix (Fin n) (Fin n) ℂ) (l : Fin n → ℂ), Function.Injective l ∧
      P * Q = 1 ∧ Q * P = 1 ∧ Q * s * P = diagonal l := by
  have hnd : s.charpoly.roots.Nodup := Polynomial.nodup_roots hs
  have hcard : s.charpoly.roots.card = n := by
    have h1 := (IsAlgClosed.splits s.charpoly).natDegree_eq_card_roots
    rw [Matrix.charpoly_natDegree_eq_dim] at h1
    simpa using h1.symm
  have hc2 : s.charpoly.roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup hnd, hcard]
  let e := Finset.equivFinOfCardEq hc2
  let l : Fin n → ℂ := fun i => (e.symm i : ℂ)
  have hl : Function.Injective l := fun i j h =>
    e.symm.injective (Subtype.ext h)
  have hroot : ∀ i, s.charpoly.IsRoot (l i) := fun i => by
    have := (e.symm i).2
    rw [Multiset.mem_toFinset] at this
    exact Polynomial.isRoot_of_mem_roots this
  have hev : ∀ i, ∃ v : Fin n → ℂ, v ≠ 0 ∧ s *ᵥ v = l i • v := by
    intro i
    have h0 : Module.End.HasEigenvalue (Matrix.toLin' s : Module.End ℂ (Fin n → ℂ)) (l i) := by
      rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin']
      exact hroot i
    obtain ⟨v, hv⟩ := h0.exists_hasEigenvector
    refine ⟨v, hv.2, ?_⟩
    have := hv.apply_eq_smul
    simpa using this
  choose v hv0 hv using hev
  have hli : LinearIndependent ℂ v :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' s : Module.End ℂ (Fin n → ℂ)) l hl v
      (fun i => ⟨by
        rw [Module.End.mem_eigenspace_iff]; simpa using hv i, hv0 i⟩)
  let P : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => v j i
  have hcol : P.col = v := by
    ext j i; rfl
  have hP : IsUnit P := Matrix.linearIndependent_cols_iff_isUnit.mp (by rw [hcol]; exact hli)
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 hP
  have hsP : s * P = P * diagonal l := by
    ext i j
    have := congrFun (hv j) i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    rw [Matrix.mul_diagonal]
    simp only [Matrix.mul_apply, P, Matrix.of_apply]
    rw [this, mul_comm]
  refine ⟨P, P⁻¹, l, hl, Matrix.mul_nonsing_inv _ hdet, Matrix.nonsing_inv_mul _ hdet, ?_⟩
  rw [Matrix.mul_assoc, hsP, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]

end GlobalTheory.CompanionTheory.WeylNear
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.PWeight

section

@[expose] public section

open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel.PWeight

variable {n : ℕ}

theorem cancel_l {A B : Matrix (Fin n) (Fin n) ℂ} (h : A * B = 1) (X : Matrix (Fin n) (Fin n) ℂ) :
    A * (B * X) = X := by
  rw [← Matrix.mul_assoc, h, Matrix.one_mul]

def conjHom {H : Type} [Group H] (ι : H →* Matrix (Fin n) (Fin n) ℂ) (Q P : Matrix (Fin n) (Fin n) ℂ)
    (hPQ : P * Q = 1) (hQP : Q * P = 1) : H →* Matrix (Fin n) (Fin n) ℂ where
  toFun h := Q * ι h * P
  map_one' := by simp [hQP]
  map_mul' a b := by simp only [map_mul, Matrix.mul_assoc, cancel_l hPQ]

theorem conjHom_apply {H : Type} [Group H] (ι : H →* Matrix (Fin n) (Fin n) ℂ) (Q P : Matrix (Fin n) (Fin n) ℂ)
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (g : H) : conjHom ι Q P hPQ hQP g = Q * ι g * P := rfl

def conjHomeo (Q P : Matrix (Fin n) (Fin n) ℂ) (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    Matrix (Fin n) (Fin n) ℂ ≃ₜ Matrix (Fin n) (Fin n) ℂ where
  toFun Y := Q * Y * P
  invFun Y := P * Y * Q
  left_inv Y := by simp only [Matrix.mul_assoc, cancel_l hPQ, hPQ, Matrix.mul_one]
  right_inv Y := by simp only [Matrix.mul_assoc, cancel_l hQP, hQP, Matrix.mul_one]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

theorem isUGroup_conj {H : Type} [Group H] [TopologicalSpace H] (ι : H →* Matrix (Fin n) (Fin n) ℂ)
    (J Q P : Matrix (Fin n) (Fin n) ℂ) (hPQ : P * Q = 1) (hQP : Q * P = 1) (hU : IsUGroup ι J) :
    IsUGroup (conjHom ι Q P hPQ hQP) (Pᴴ * J * P) := by
  have hPQh : Qᴴ * Pᴴ = 1 := by rw [← conjTranspose_mul, hPQ, conjTranspose_one]
  have hQPh : Pᴴ * Qᴴ = 1 := by rw [← conjTranspose_mul, hQP, conjTranspose_one]
  have hP : IsUnit P.det := isUnit_iff_exists_inv.2 ⟨Q.det, by rw [← det_mul, hPQ, det_one]⟩
  have hPh : IsUnit Pᴴ.det := isUnit_iff_exists_inv.2 ⟨Qᴴ.det, by rw [← det_mul, hQPh, det_one]⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [det_mul, det_mul]
    exact (hPh.mul hU.1).mul hP
  · exact (conjHomeo Q P hPQ hQP).isClosedEmbedding.comp hU.2.1
  · have key1 : ∀ X : Matrix (Fin n) (Fin n) ℂ,
        (Q * X * P)ᴴ * (Pᴴ * J * P) * (Q * X * P) = Pᴴ * (Xᴴ * J * X) * P := by
      intro X
      simp only [conjTranspose_mul, Matrix.mul_assoc, cancel_l hPQh, cancel_l hPQ]
    have key2 : ∀ X : Matrix (Fin n) (Fin n) ℂ,
        (P * X * Q)ᴴ * J * (P * X * Q) = Qᴴ * (Xᴴ * (Pᴴ * J * P) * X) * Q := by
      intro X
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    have key3 : Qᴴ * (Pᴴ * J * P) * Q = J := by
      simp only [Matrix.mul_assoc, cancel_l hPQh, hPQ, Matrix.mul_one]
    intro M
    constructor
    · rintro ⟨h, rfl⟩
      have hA := (hU.2.2 (ι h)).1 ⟨h, rfl⟩
      rw [conjHom_apply, key1, hA]
    · intro hM
      have hN : (P * M * Q)ᴴ * J * (P * M * Q) = J := by rw [key2, hM, key3]
      obtain ⟨h, hh⟩ := (hU.2.2 _).2 hN
      refine ⟨h, ?_⟩
      rw [conjHom_apply, hh]
      simp only [Matrix.mul_assoc, cancel_l hQP, hQP, Matrix.mul_one]

def conjMx (Q P : Matrix (Fin n) (Fin n) ℂ) (Y : MainStatements.WeightKernel.Mx n) : MainStatements.WeightKernel.Mx n :=
  fun i j => (Q * Matrix.of Y * P) i j

theorem contDiff_conjMx (Q P : Matrix (Fin n) (Fin n) ℂ) : ContDiff ℝ ∞ (conjMx Q P) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  simp only [conjMx, Matrix.mul_apply, Matrix.of_apply]
  exact ContDiff.sum fun x _ => ContDiff.mul (ContDiff.sum fun y _ =>
    contDiff_const.mul ((contDiff_apply ℝ (fun _ => ℂ) x).comp (contDiff_apply ℝ (fun _ => (Fin n → ℂ)) y))) contDiff_const

end MainStatements.WeightKernel.PWeight

namespace MainStatements.WeightKernel

open PWeight in
theorem weight : WeightDiag → Weight := by
  intro hWD H _ _ _ _ _ _ _ _ n ι J hU s hreg hprop
  obtain ⟨P, Q, l, hl, hPQ, hQP, hd⟩ := GlobalTheory.CompanionTheory.WeylNear.exists_diag n (ι s) hreg
  obtain ⟨B', hB'⟩ := hWD H n (conjHom ι Q P hPQ hQP) (Pᴴ * J * P) (isUGroup_conj ι J Q P hPQ hQP hU) s l hl
    hd hprop
  refine ⟨fun z => B' (conjMx Q P z.1, conjMx Q P z.2), ?_, fun z => hB'.nonneg _, hB'.pos, hB'.shift, hB'.proper⟩
  exact hB'.smooth.comp (((contDiff_conjMx Q P).comp contDiff_fst).prodMk ((contDiff_conjMx Q P).comp contDiff_snd))

end MainStatements.WeightKernel

end
end
end
