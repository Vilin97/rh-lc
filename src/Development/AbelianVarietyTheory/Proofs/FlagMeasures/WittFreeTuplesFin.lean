module

public import Development.AbelianVarietyTheory.Definitions.Foundations.InFrameStabilizer
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WittExtensionHermitianFrames
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WittFreeTuplesSplitQuadraticEtaleStatement
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFieldOrExistsSwappedIdempotentOfQuadraticEtale

section

@[expose] public section

open GlobalTheory.SgAlg Matrix

namespace GlobalTheory.SgAlg

theorem isField_or_exists_idempotent_of_isQA {E : Type} [CommRing E] (σ : E →+* E) (h : IsQA σ) :
    IsField E ∨ ∃ e : E, e * e = e ∧ e + σ e = 1 ∧ ∀ x : E, e * x ≠ 0 → ∃ y, e * x * y = e := by
  obtain ⟨hinv, ⟨x₀, hx₀⟩, hred, -, hunit⟩ := h
  by_cases hN : ∀ y : E, y ≠ 0 → y * σ y ≠ 0
  · left
    refine ⟨⟨σ x₀, x₀, hx₀⟩, mul_comm, ?_⟩
    intro y hy
    have hfix : σ (y * σ y) = y * σ y := by
      rw [map_mul, hinv, mul_comm]
    obtain ⟨u, hu⟩ := hunit _ hfix (hN y hy)
    refine ⟨σ y * (↑u⁻¹ : E), ?_⟩
    rw [← mul_assoc, ← hu]
    exact u.mul_inv
  · right
    push Not at hN
    obtain ⟨y, hy, hyy⟩ := hN
    have hsfix : σ (y + σ y) = y + σ y := by
      rw [map_add (f := _), hinv, add_comm]
    have hs : y + σ y ≠ 0 := by
      intro h0
      have h1 : σ y = -y := eq_neg_of_add_eq_zero_right h0
      rw [h1] at hyy
      have h2 : y ^ 2 = 0 := by
        have : y * y = 0 := by simpa using hyy
        rw [pow_two, this]
      exact hy (pow_eq_zero_iff (two_ne_zero) |>.mp h2)
    obtain ⟨s, hs'⟩ := hunit _ hsfix hs
    have hsum : (↑s⁻¹ : E) * (y + σ y) = 1 := by rw [← hs', Units.inv_mul]
    have hσs : σ (↑s⁻¹ : E) * (y + σ y) = 1 := by
      have : σ ((↑s⁻¹ : E) * (y + σ y)) = 1 := by
        rw [hsum, map_one]
      rwa [map_mul, hsfix] at this
    have hσs' : σ (↑s⁻¹ : E) = ↑s⁻¹ := by
      calc σ (↑s⁻¹ : E) = σ (↑s⁻¹ : E) * ((y + σ y) * ↑s⁻¹) := by
            rw [mul_comm (y + σ y), hsum, mul_one]
        _ = ↑s⁻¹ := by rw [← mul_assoc, hσs, one_mul]
    set e : E := y * ↑s⁻¹ with he
    have hσe : σ e = σ y * ↑s⁻¹ := by rw [he, map_mul, hσs']
    have hadd : e + σ e = 1 := by
      rw [hσe, he, ← add_mul, mul_comm]; exact hsum
    have horth : e * σ e = 0 := by
      rw [hσe, he]
      calc y * ↑s⁻¹ * (σ y * ↑s⁻¹) = (y * σ y) * (↑s⁻¹ * ↑s⁻¹) := by ring
        _ = 0 := by rw [hyy, zero_mul]
    have hidem : e * e = e := by
      have : e * (e + σ e) = e := by rw [hadd, mul_one]
      rwa [mul_add, horth, add_zero] at this
    refine ⟨e, hidem, hadd, ?_⟩
    intro x hx
    have hufix : σ (e * x + σ (e * x)) = e * x + σ (e * x) := by
      rw [map_add (f := _), hinv, add_comm]
    have heu : e * (e * x + σ (e * x)) = e * x := by
      rw [map_mul, mul_add, ← mul_assoc, hidem, ← mul_assoc, horth, zero_mul, add_zero]
    have hu0 : e * x + σ (e * x) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at heu
      exact hx heu.symm
    obtain ⟨u, hu⟩ := hunit _ hufix hu0
    refine ⟨↑u⁻¹, ?_⟩
    rw [← heu, ← hu, mul_assoc, u.mul_inv, mul_one]

end GlobalTheory.SgAlg
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFieldOrExistsSwappedIdempotentOfQuadraticEtaleStatement

section

@[expose] public section

open GlobalTheory.SgAlg Matrix

theorem _root_.GlobalTheory.T.isField_or_exists_swapped_idempotent_of_quadraticEtale : ∀ {E : Type} [CommRing E] (σ : E →+* E), IsQA σ → IsField E ∨ ∃ e : E, e * e = e ∧ e + σ e = 1 ∧ ∀ x : E, e * x ≠ 0 → ∃ y, e * x * y = e := by
  first | exact @GlobalTheory.SgAlg.isField_or_exists_idempotent_of_isQA | exact GlobalTheory.SgAlg.isField_or_exists_idempotent_of_isQA | (intros; apply GlobalTheory.SgAlg.isField_or_exists_idempotent_of_isQA <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.WittExtensionHermitianFramesStatement

section

@[expose] public section

open GlobalTheory.SgAlg Matrix

theorem _root_.GlobalTheory.T.witt_extension_hermitian_frames : ∀ {E : Type} [Field E] (σ : E →+* E), IsQA σ → ∀ {n a : ℕ} (J : Matrix (Fin n) (Fin n) E), IsHermU σ J → ∀ (X X' : Matrix (Fin n) (Fin a) E), Free X → Free X' → pairM σ J X X = pairM σ J X' X' → ∃ g, IsUn σ J g ∧ g * X = X' := by
  first | exact @GlobalTheory.SgAlg.witt_free_field | exact GlobalTheory.SgAlg.witt_free_field | (intros; apply GlobalTheory.SgAlg.witt_free_field <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.WittFreeTuplesFin

section

@[expose] public section

open GlobalTheory.SgAlg Matrix

namespace GlobalTheory

theorem witt_free_tuples_fin {E : Type} [CommRing E] (σ : E →+* E) (hσ : IsQA σ) {n k : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermU σ J) (Y Y' : Matrix (Fin n) (Fin k) E)
    (hY : Free Y) (hY' : Free Y') (hP : pairM σ J Y Y = pairM σ J Y' Y') :
    ∃ g, IsUn σ J g ∧ g * Y = Y' := by
  rcases GlobalTheory.T.isField_or_exists_swapped_idempotent_of_quadraticEtale σ hσ with hF | hS
  · letI := hF.toField
    exact GlobalTheory.T.witt_extension_hermitian_frames σ hσ J hJ Y Y' hY hY' hP
  · exact GlobalTheory.T.witt_free_tuples_split_quadratic_etale σ hσ hS J hJ Y Y' hY hY' hP

theorem free_reindex {E : Type} [CommRing E] {n : ℕ} {a b : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (e : b ≃ a) {X : Matrix (Fin n) a E} (hX : Free X) :
    Free (X.submatrix id e) := by
  obtain ⟨L, hL⟩ := hX
  refine ⟨L.submatrix e id, ?_⟩
  have h : L.submatrix e id * X.submatrix id e = (L * X).submatrix e e := by
    ext i j
    simp [Matrix.mul_apply]
  rw [h, hL]
  simp

theorem pairM_reindex {E : Type} [CommRing E] (σ : E →+* E) {n : ℕ} {a b : Type} [Fintype a]
    (e : b ≃ a) (J : Matrix (Fin n) (Fin n) E) (X X' : Matrix (Fin n) a E) :
    pairM σ J (X'.submatrix id e) (X.submatrix id e) = (pairM σ J X' X).submatrix e e := by
  ext i j
  simp [pairM, cT, Matrix.mul_apply]

theorem witt_free_tuples {E : Type} [CommRing E] (σ : E →+* E) (hσ : IsQA σ) {n : ℕ} {a : Type}
    [Fintype a] [DecidableEq a] (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermU σ J)
    (X X' : Matrix (Fin n) a E) (hX : Free X) (hX' : Free X')
    (hP : pairM σ J X X = pairM σ J X' X') : ∃ g, IsUn σ J g ∧ g * X = X' := by
  let e : Fin (Fintype.card a) ≃ a := (Fintype.equivFin a).symm
  obtain ⟨g, hg, hgX⟩ := witt_free_tuples_fin σ hσ J hJ (X.submatrix id e) (X'.submatrix id e)
    (free_reindex e hX) (free_reindex e hX')
    (by rw [pairM_reindex, pairM_reindex, hP])
  refine ⟨g, hg, ?_⟩
  ext i j
  have h := congrFun (congrFun hgX i) (e.symm j)
  simpa [Matrix.mul_apply] using h

end GlobalTheory
end
end
