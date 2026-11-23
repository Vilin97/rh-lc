module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
public import Mathlib.Analysis.Matrix.Spectrum
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankLeCardOfVanish

section

@[expose] public section

open NumberField Matrix

namespace GlobalTheory.SylvesterInertia

theorem re_quad_eq_sum {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.IsHermitian) (u : Fin n → ℂ) :
    (star u ⬝ᵥ M *ᵥ u).re = ∑ i, hM.eigenvalues i * Complex.normSq
      ((star (hM.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ u) i) := by
  set U : Matrix (Fin n) (Fin n) ℂ := (hM.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have hD : star U * M * U = diagonal (RCLike.ofReal ∘ hM.eigenvalues) := by
    have := hM.conjStarAlgAut_star_eigenvectorUnitary
    simpa [Unitary.conjStarAlgAut_apply, hU] using this
  set y := star U *ᵥ u with hy
  have hu : u = U *ᵥ y := by
    rw [hy, mulVec_mulVec, hU, Matrix.mem_unitaryGroup_iff.mp hM.eigenvectorUnitary.2, one_mulVec]
  have h1 : star u ⬝ᵥ M *ᵥ u = star y ⬝ᵥ (star U * M * U) *ᵥ y := by
    conv_lhs => rw [hu]
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, star_eq_conjTranspose, Matrix.mul_assoc]
  rw [h1, hD, dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mulVec_diagonal]
  simp only [Pi.star_apply, Function.comp_apply, Complex.star_def, Complex.normSq_apply, Complex.mul_re,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im]
  have e1 : ((RCLike.ofReal (hM.eigenvalues i) : ℂ)).re = hM.eigenvalues i := by simp
  have e2 : ((RCLike.ofReal (hM.eigenvalues i) : ℂ)).im = 0 := by simp
  simp only [e1, e2]
  ring

theorem finrank_le_card_of_vanish {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (P : Submodule ℂ (Fin n → ℂ))
    (s : Fin n → Prop) [DecidablePred s]
    (h : ∀ u ∈ P, (∀ i, s i → (U *ᵥ u) i = 0) → u = 0) :
    Module.finrank ℂ P ≤ Fintype.card {i // s i} := by
  let f : P →ₗ[ℂ] ({i // s i} → ℂ) :=
    (LinearMap.funLeft ℂ ℂ (Subtype.val : {i // s i} → Fin n)) ∘ₗ (Matrix.mulVecLin U) ∘ₗ P.subtype
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have := h u u.2 (fun i hi => by
      have := congrFun hu ⟨i, hi⟩
      simpa [f, LinearMap.funLeft_apply] using this)
    exact Subtype.ext this
  have := LinearMap.finrank_le_finrank_of_injective hf
  simpa using this

end GlobalTheory.SylvesterInertia
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.HopfOrderScalarExtension

section

@[expose] public section

open NumberField GlobalTheory.LKTrip
open scoped TensorProduct Matrix.Norms.L2Operator

noncomputable section

namespace GlobalTheory.SimSign

open Matrix

variable {n : ℕ}

def extZero (s : Fin n → Prop) [DecidablePred s] : ({i // s i} → ℂ) →ₗ[ℂ] (Fin n → ℂ) where
  toFun w i := if hi : s i then w ⟨i, hi⟩ else 0
  map_add' a b := by funext i; by_cases hi : s i <;> simp [hi]
  map_smul' r a := by funext i; by_cases hi : s i <;> simp [hi]

theorem extZero_apply_mem (s : Fin n → Prop) [DecidablePred s] (w : {i // s i} → ℂ) (i : {i // s i}) :
    extZero s w i = w i := by simp [extZero, i.2]

theorem extZero_apply_not (s : Fin n → Prop) [DecidablePred s] (w : {i // s i} → ℂ) {i : Fin n} (hi : ¬ s i) :
    extZero s w i = 0 := by simp [extZero, hi]

theorem quad_mulVec (h X : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) :
    star (X *ᵥ u) ⬝ᵥ h *ᵥ (X *ᵥ u) = star u ⬝ᵥ (Xᴴ * h * X) *ᵥ u := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc]

theorem re_quad_ext (h : Matrix (Fin n) (Fin n) ℂ) (hh : h.IsHermitian) (s : Fin n → Prop) [DecidablePred s]
    (w : {i // s i} → ℂ) :
    (star ((hh.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ extZero s w) ⬝ᵥ
        h *ᵥ ((hh.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ extZero s w)).re =
      ∑ i, hh.eigenvalues i * Complex.normSq (extZero s w i) := by
  rw [GlobalTheory.SylvesterInertia.re_quad_eq_sum h hh, Matrix.mulVec_mulVec,
    Matrix.mem_unitaryGroup_iff'.mp hh.eigenvectorUnitary.2, Matrix.one_mulVec]

theorem finrank_le_pos (h : Matrix (Fin n) (Fin n) ℂ) (hh : h.IsHermitian) (S : Submodule ℂ (Fin n → ℂ))
    (hS : ∀ u ∈ S, u ≠ 0 → 0 < (star u ⬝ᵥ h *ᵥ u).re) :
    Module.finrank ℂ S ≤ Fintype.card {i : Fin n // 0 < hh.eigenvalues i} := by
  refine GlobalTheory.SylvesterInertia.finrank_le_card_of_vanish
    (star (hh.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)) S _ fun u hu hv => ?_
  by_contra hne
  have hpos := hS u hu hne
  rw [GlobalTheory.SylvesterInertia.re_quad_eq_sum h hh u] at hpos
  refine absurd hpos (not_lt.mpr (Finset.sum_nonpos fun i _ => ?_))
  by_cases hi : 0 < hh.eigenvalues i
  · rw [hv i hi, map_zero, mul_zero]
  · exact mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hi) (Complex.normSq_nonneg _)

end GlobalTheory.SimSign

namespace GlobalTheory.SimSign

open Matrix

variable {n : ℕ}

theorem sum_pos (h : Matrix (Fin n) (Fin n) ℂ) (hh : h.IsHermitian) (w : {i // 0 < hh.eigenvalues i} → ℂ)
    (hw : w ≠ 0) : 0 < ∑ i, hh.eigenvalues i * Complex.normSq (extZero (fun i => 0 < hh.eigenvalues i) w i) := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hw
  have hle : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      (0 : Fin n → ℝ) i ≤ hh.eigenvalues i * Complex.normSq (extZero (fun i => 0 < hh.eigenvalues i) w i) := by
    intro i _
    by_cases hi : 0 < hh.eigenvalues i
    · exact mul_nonneg hi.le (Complex.normSq_nonneg _)
    · rw [extZero_apply_not _ w hi]; simp
  have hlt : ∃ i ∈ (Finset.univ : Finset (Fin n)),
      (0 : Fin n → ℝ) i < hh.eigenvalues i * Complex.normSq (extZero (fun i => 0 < hh.eigenvalues i) w i) := by
    refine ⟨j.1, Finset.mem_univ _, ?_⟩
    rw [extZero_apply_mem]
    exact mul_pos j.2 (Complex.normSq_pos.mpr hj)
  simpa using Finset.sum_lt_sum hle hlt

end GlobalTheory.SimSign

namespace GlobalTheory.HTBetti

end GlobalTheory.HTBetti

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SylvesterInertiaInvariance

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.SigCong

theorem card_pos_le_of_conj {n : ℕ} (A B X : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hX : Xᴴ * A * X = B) :
    Fintype.card {i : Fin n // 0 < hB.eigenvalues i} ≤ Fintype.card {i : Fin n // 0 < hA.eigenvalues i} := by
  set φ : ({i // 0 < hB.eigenvalues i} → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    Matrix.mulVecLin X ∘ₗ Matrix.mulVecLin (hB.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) ∘ₗ
      GlobalTheory.SimSign.extZero (fun i => 0 < hB.eigenvalues i) with hφ
  have hq : ∀ w, w ≠ 0 → 0 < (star (φ w) ⬝ᵥ A *ᵥ φ w).re := fun w hw => by
    simp only [hφ, LinearMap.coe_comp, Function.comp_apply, Matrix.mulVecLin_apply]
    rw [GlobalTheory.SimSign.quad_mulVec, hX, GlobalTheory.SimSign.re_quad_ext]
    exact GlobalTheory.SimSign.sum_pos B hB w hw
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    by_contra hne
    have := hq w hne
    rw [hw] at this
    simp at this
  have hS : ∀ u ∈ LinearMap.range φ, u ≠ 0 → 0 < (star u ⬝ᵥ A *ᵥ u).re := by
    rintro u ⟨w, rfl⟩ hu
    exact hq w (fun h0 => hu (by rw [h0, map_zero]))
  have h1 := GlobalTheory.SimSign.finrank_le_pos A hA _ hS
  rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card] at h1
  exact h1

theorem sigPosH_congr : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian), A.det ≠ 0 →
    ∀ (Z : GL (Fin n) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) (hB : B.IsHermitian),
      B = (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * A * (Z : Matrix (Fin n) (Fin n) ℂ) → sigPosH hB = sigPosH hA := by
  intro n A hA _ Z B hB hBZ
  unfold sigPosH
  refine le_antisymm (card_pos_le_of_conj A B _ hA hB hBZ.symm)
    (card_pos_le_of_conj B A ((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) hB hA ?_)
  have h1 : (Z : Matrix (Fin n) (Fin n) ℂ) * ((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    Units.mul_inv Z
  rw [hBZ]
  calc (((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))ᴴ * ((Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * A *
        (Z : Matrix (Fin n) (Fin n) ℂ)) * ((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
      = ((Z : Matrix (Fin n) (Fin n) ℂ) * ((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))ᴴ * A *
        ((Z : Matrix (Fin n) (Fin n) ℂ) * ((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)) := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = A := by rw [h1]; simp

end GlobalTheory.SigCong
end
end
