module

public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WeightOccurrence.OccSome
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutantAnnihilatingVectorZeroStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutatorCoerciveOnAnnihilatorStatement
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD
public import Formalism.RealPlaceAnalysis.Complexify
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnitaryInterlacingRealization
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
import Mathlib.Algebra.Order.Star.Real
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InterlacingSignatureParityStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialFractionCoefficientSignsStatement
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import Development.WeilBound.CoreStatements.BranchingTraces.ContinuousEmb
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnitaryInterlacingRealizationStatement

section

@[expose] public section

open Finset Matrix PositivityTheory.RgHe.Frame


theorem _root_.GlobalTheory.T.exists_unitary_interlacing_realization : ∀ (n : ℕ) (ε : Fin (n + 1) → Bool) (d : Fin (n + 1) → ℝ) (ε' : Fin n → Bool) (d' : Fin n → ℝ) (e : Fin n ⊕ Unit ≃ Fin (n + 1)), ε (e (Sum.inr ())) = true → (∀ a, ε (e (Sum.inl a)) = ε' a) → Function.Injective (Sum.elim d d') → (∀ i, 0 < (if ε i then (1 : ℝ) else -1) * pfD d d' i) → (∀ j, 0 < -((if ε' j then (1 : ℝ) else -1) * pfR d d' j)) → ∃ g X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, Formalism.REAL.inUJ ε g ∧ X * g = g * diagonal (fun i => ((d i : ℝ) : ℂ)) ∧ (∀ a b, X (e (Sum.inl a)) (e (Sum.inl b)) = if a = b then ((d' a : ℝ) : ℂ) else 0) ∧ ∀ i, ((Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) *ᵥ (Pi.single (e (Sum.inr ())) (1 : ℂ) : Fin (n + 1) → ℂ)) i ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.RgHeFrame.build | exact GlobalTheory.CompanionTheory.RgHeFrame.build | (intros; apply GlobalTheory.CompanionTheory.RgHeFrame.build <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HilbertSchmidtNormSubmultiplicative

section

@[expose] public section

open Finset Matrix PositivityTheory.RgHe.Frame

namespace GlobalTheory.CompanionTheory.RgHe

theorem hs_mul_le_mul {m : ℕ} (P Q : Matrix (Fin m) (Fin m) ℂ) :
    Formalism.REAL.hs (P * Q) ≤ Formalism.REAL.hs P * Formalism.REAL.hs Q := by
  have key : ∀ i j, ‖(P * Q) i j‖ ^ 2 ≤ (∑ k, ‖P i k‖ ^ 2) * (∑ k, ‖Q k j‖ ^ 2) := by
    intro i j
    have h1 : ‖(P * Q) i j‖ ≤ ∑ k, ‖P i k‖ * ‖Q k j‖ := by
      rw [Matrix.mul_apply]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => norm_mul_le _ _)
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans
      (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
  have hQ : Formalism.REAL.hs Q = ∑ j, ∑ k, ‖Q k j‖ ^ 2 := by
    unfold Formalism.REAL.hs
    exact Finset.sum_comm
  rw [hQ]
  unfold Formalism.REAL.hs
  rw [Finset.sum_mul_sum]
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => key i j

end GlobalTheory.CompanionTheory.RgHe
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HilbertSchmidtNormSubmultiplicativeStatement

section

@[expose] public section

open Finset Matrix PositivityTheory.RgHe.Frame

theorem _root_.GlobalTheory.T.hilbert_schmidt_norm_submultiplicative : ∀ {m : ℕ} (P Q : Matrix (Fin m) (Fin m) ℂ), Formalism.REAL.hs (P * Q) ≤ Formalism.REAL.hs P * Formalism.REAL.hs Q := by
  first | exact @GlobalTheory.CompanionTheory.RgHe.hs_mul_le_mul | exact GlobalTheory.CompanionTheory.RgHe.hs_mul_le_mul | (intros; apply GlobalTheory.CompanionTheory.RgHe.hs_mul_le_mul <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceDiagonalBlockConjugateFormula

section

@[expose] public section

open Finset Matrix PositivityTheory.RgHe.Frame

namespace GlobalTheory.CompanionTheory.RgHeFrame

theorem trace_diagonal_block_conjugate (n : ℕ) (e : Fin n ⊕ Unit ≃ Fin (n + 1)) (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ)
    (g X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hg : IsUnit g.det)
    (hX : X * g = g * diagonal (fun i => ((d i : ℝ) : ℂ)))
    (hb : ∀ a b, X (e (Sum.inl a)) (e (Sum.inl b)) = if a = b then ((d' a : ℝ) : ℂ) else 0)
    (Y : Matrix (Fin n) (Fin n) ℂ) :
    trace (diagonal (fun i => ((d i : ℝ) : ℂ)) * (g⁻¹ * Matrix.reindex e e (Matrix.fromBlocks Y 0 0 0) * g))
      = trace (diagonal (fun a => ((d' a : ℝ) : ℂ)) * Y) := by
  set D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := diagonal (fun i => ((d i : ℝ) : ℂ)) with hD
  set B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
    Matrix.reindex e e (Matrix.fromBlocks Y 0 0 0) with hB
  have h1 : g * D * g⁻¹ = X := by
    rw [← hX, Matrix.mul_assoc, Matrix.mul_nonsing_inv g hg, Matrix.mul_one]
  have h2 : trace (D * (g⁻¹ * B * g)) = trace (X * B) := by
    rw [← h1]
    have : D * (g⁻¹ * B * g) = (D * g⁻¹ * B) * g := by
      simp only [Matrix.mul_assoc]
    rw [this, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [h2]
  have h3 : trace (X * B) = ∑ u, ∑ w, X (e u) (e w) *
      (Matrix.fromBlocks Y 0 0 0 : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℂ) w u := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    rw [← Equiv.sum_comp e]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Equiv.sum_comp e]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp [hB, Matrix.reindex_apply]
  rw [h3]
  simp only [Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero,
    Finset.sum_const_zero, add_zero, hb]
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply]

end GlobalTheory.CompanionTheory.RgHeFrame
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceDiagonalBlockConjugateFormulaStatement

section

@[expose] public section

open Finset Matrix PositivityTheory.RgHe.Frame

theorem _root_.GlobalTheory.T.trace_diagonal_block_conjugate_formula : ∀ (n : ℕ) (e : Fin n ⊕ Unit ≃ Fin (n + 1)) (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ) (g X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ), IsUnit g.det → X * g = g * diagonal (fun i => ((d i : ℝ) : ℂ)) → (∀ a b, X (e (Sum.inl a)) (e (Sum.inl b)) = if a = b then ((d' a : ℝ) : ℂ) else 0) → ∀ Y : Matrix (Fin n) (Fin n) ℂ, trace (diagonal (fun i => ((d i : ℝ) : ℂ)) * (g⁻¹ * Matrix.reindex e e (Matrix.fromBlocks Y 0 0 0) * g)) = trace (diagonal (fun a => ((d' a : ℝ) : ℂ)) * Y) := by
  first | exact @GlobalTheory.CompanionTheory.RgHeFrame.trace_diagonal_block_conjugate | exact GlobalTheory.CompanionTheory.RgHeFrame.trace_diagonal_block_conjugate | (intros; apply GlobalTheory.CompanionTheory.RgHeFrame.trace_diagonal_block_conjugate <;> assumption)
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.Assembly

section

@[expose] public section

noncomputable section

open Finset Matrix Formalism.REAL

namespace PositivityTheory.RgHe.FrameA

open PositivityTheory.RgHe.Frame PositivityTheory.UnitaryDecomposition

variable {n : ℕ} {e : Fin n ⊕ Unit ≃ Fin (n + 1)}

theorem hs_nonneg' {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) : 0 ≤ hs A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

theorem hs_emb_sub (a : Matrix (Fin n) (Fin n) ℂ) : hs (emb e a - 1) = hs (a - 1) := by
  have h1 : emb e a - 1 = Matrix.reindex e e (Matrix.fromBlocks (a - 1) 0 0 0) := by
    ext i j
    obtain ⟨i, rfl⟩ := e.surjective i
    obtain ⟨j, rfl⟩ := e.surjective j
    rcases i with i | i <;> rcases j with j | j <;> simp [emb, Matrix.one_apply, e.injective.eq_iff]
  rw [h1]
  unfold hs
  rw [← e.sum_comp, Fintype.sum_sum_type]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  simp [← e.sum_comp, Fintype.sum_sum_type]

theorem emb_mulVec_alt (a : Matrix (Fin n) (Fin n) ℂ) :
    emb e a *ᵥ (Pi.single (e (Sum.inr ())) (1 : ℂ) : Fin (n + 1) → ℂ) = Pi.single (e (Sum.inr ())) 1 := by
  ext i
  rw [Matrix.mulVec_single_one]
  obtain ⟨i, rfl⟩ := e.surjective i
  rcases i with i | i <;> simp [emb]

theorem frame : PositivityTheory.RgHe.Frame := by
  intro n ε d ε' d' e hF hinj hW
  obtain ⟨hs1, hs2⟩ := GlobalTheory.T.interlacing_signature_parity n ε d ε' d' e hF hinj hW
  obtain ⟨ps1, ps2⟩ := GlobalTheory.T.partial_fraction_coefficient_signs d d' hinj
  have hD : ∀ i, 0 < (if ε i then (1 : ℝ) else -1) * pfD d d' i := fun i => by
    have h := ps1 i
    by_cases hi : ε i = true
    · rw [if_pos hi, one_mul]
      rwa [((hs1 i).1 hi).neg_one_pow, one_mul] at h
    · rw [if_neg hi]
      have ho : ¬ Even (above d d' (d i)) := fun h' => hi ((hs1 i).2 h')
      rw [(Nat.not_even_iff_odd.1 ho).neg_one_pow] at h
      linarith
  have hR : ∀ j, 0 < -((if ε' j then (1 : ℝ) else -1) * pfR d d' j) := fun j => by
    have h := ps2 j
    by_cases hj : ε' j = true
    · rw [if_pos hj]
      rw [(Nat.not_even_iff_odd.1 ((hs2 j).1 hj)).neg_one_pow] at h
      linarith
    · rw [if_neg hj]
      have he : Even (above d d' (d' j)) := by
        by_contra h'
        exact hj ((hs2 j).2 h')
      rw [he.neg_one_pow, one_mul] at h
      linarith
  obtain ⟨g, X, hgU, hXg, hblk, hβ⟩ := GlobalTheory.T.exists_unitary_interlacing_realization n ε d ε' d' e hF.1 hF.2 hinj hD hR
  set J := Jm ε with hJ
  have hJJ : J * J = 1 := Jm_mul_self ε
  have h2 : (J * gᴴ * J) * g = 1 := by
    have : (J * gᴴ * J) * g = J * (gᴴ * J * g) := by simp only [Matrix.mul_assoc]
    rw [this, hgU, hJJ]
  have hinv : g⁻¹ = J * gᴴ * J := Matrix.inv_eq_left_inv h2
  have hdet : IsUnit g.det := Matrix.isUnit_det_of_left_inverse h2
  have h1 : g * (J * gᴴ * J) = 1 := by rw [← hinv]; exact Matrix.mul_nonsing_inv g hdet
  let gu : UJ ε := ⟨⟨g, J * gᴴ * J, h1, h2⟩, hgU⟩
  have hgu : um gu = g := rfl
  have hgu' : um gu⁻¹ = g⁻¹ := by
    rw [hinv]; rfl
  refine ⟨gu, fun Y => ?_, ?_⟩
  · rw [hgu, hgu']
    exact GlobalTheory.T.trace_diagonal_block_conjugate_formula n e d d' g X hdet hXg hblk Y
  · set D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := diagonal fun i => ((d i : ℝ) : ℂ) with hDd
    have hX : X = g * D * g⁻¹ := by
      rw [hXg.symm, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
    set v : Fin (n + 1) → ℂ := Pi.single (e (Sum.inr ())) 1 with hv
    have hdi : Function.Injective fun i => ((d i : ℝ) : ℂ) := fun i j h =>
      Sum.inl_injective (hinj (by simpa using h))
    have hcyc : ∀ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, A * X = X * A → A *ᵥ v = 0 → A = 0 := by
      intro A hA hAv
      rw [hX] at hA
      exact GlobalTheory.T.commutant_annihilating_vector_zero g _ v hdet hdi (fun i => by rw [hinv]; exact hβ i) A hA hAv
    obtain ⟨c, hc, hAc⟩ := GlobalTheory.T.commutator_coercive_on_annihilator X v hcyc
    refine ⟨c * hs g * hs g⁻¹ + 1, by have := hs_nonneg' g; have := hs_nonneg' g⁻¹; positivity, fun h => ?_⟩
    set B := emb e (um h) with hB
    set B' := emb e (um h⁻¹) with hB'
    have hBB : B * B' = 1 := by
      rw [hB, hB', ← emb_mul, ← emb_one (e := e)]
      congr 1
      exact Units.mul_inv h.1
    have hBB' : B' * B = 1 := by
      rw [hB, hB', ← emb_mul, ← emb_one (e := e)]
      congr 1
      exact Units.inv_mul h.1
    set δ := dg d - (um gu⁻¹ * B' * um gu) * dg d * (um gu⁻¹ * B * um gu) with hδ
    have hdg : dg d = D := rfl
    have key : (B - 1) * X - X * (B - 1) = B * (g * δ * g⁻¹) := by
      rw [hδ, hgu, hgu', hdg, hX]
      have e1 : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul _ hdet
      have e2 : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
      have e3 : B * (g * (g⁻¹ * (B' * (g * (D * (g⁻¹ * (B * (g * g⁻¹)))))))) = g * (D * (g⁻¹ * B)) := by
        rw [e2, Matrix.mul_one, ← Matrix.mul_assoc g g⁻¹, e2, Matrix.one_mul, ← Matrix.mul_assoc B B', hBB, Matrix.one_mul]
      rw [e3]
      abel
    have hAv : (B - 1) *ᵥ v = 0 := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, hB, emb_mulVec_alt, sub_self]
    have i1 := hAc (B - 1) hAv
    rw [key] at i1
    have i2 : hs (B * (g * δ * g⁻¹)) ≤ hs B * (hs g * hs δ * hs g⁻¹) := by
      refine (GlobalTheory.T.hilbert_schmidt_norm_submultiplicative _ _).trans (mul_le_mul_of_nonneg_left ?_ (hs_nonneg' _))
      refine (GlobalTheory.T.hilbert_schmidt_norm_submultiplicative _ _).trans (mul_le_mul_of_nonneg_right (GlobalTheory.T.hilbert_schmidt_norm_submultiplicative _ _) (hs_nonneg' _))
    have i3 : hs (um h - 1) = hs (B - 1) := (hs_emb_sub (e := e) (um h)).symm
    rw [i3]
    have := hs_nonneg' B; have := hs_nonneg' δ; have := hs_nonneg' g; have := hs_nonneg' g⁻¹
    calc hs (B - 1) ≤ c * (hs B * (hs g * hs δ * hs g⁻¹)) := i1.trans (mul_le_mul_of_nonneg_left i2 hc.le)
      _ = (c * hs g * hs g⁻¹) * hs B * hs δ := by ring
      _ ≤ (c * hs g * hs g⁻¹ + 1) * hs B * hs δ := by gcongr; linarith

end PositivityTheory.RgHe.FrameA
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.Imports

section

@[expose] public section

namespace PositivityTheory.RgHe.FrameF

theorem frame : PositivityTheory.RgHe.Frame := PositivityTheory.RgHe.FrameA.frame

end PositivityTheory.RgHe.FrameF
end
end
