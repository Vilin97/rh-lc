module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsBlockMatrixTwoByTwoFinEq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianBlockSolutionExistsStatement
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
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
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs
import Mathlib.Tactic.ReduceModChar
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SameSpanTransferMatrices

section

@[expose] public section

open scoped Matrix
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions.EC

namespace GlobalTheory.CompanionTheory.BruhatCoeffs

theorem exists_coeff_matrices_of_span_eq {K : Type} [Field K] {n r : ℕ}
    (C : Matrix (Fin n) (Fin n) K) (c : Matrix (Fin r) (Fin n) K)
    (hc : LinearIndependent K c)
    (hs : Submodule.span K (Set.range c) = Submodule.span K (Set.range C)) :
    ∃ (T : Matrix (Fin n) (Fin r) K) (L : Matrix (Fin r) (Fin n) K),
      C = T * c ∧ c = L * C ∧ L * T = 1 := by
  have hT0 : ∀ j, ∃ t : Fin r → K, ∑ i, t i • c i = C j := by
    intro j
    have hj : C j ∈ Submodule.span K (Set.range c) := by
      rw [hs]
      exact Submodule.subset_span (Set.mem_range_self j)
    exact (Submodule.mem_span_range_iff_exists_fun K).mp hj
  have hL0 : ∀ i, ∃ t : Fin n → K, ∑ j, t j • C j = c i := by
    intro i
    have hi : c i ∈ Submodule.span K (Set.range C) := by
      rw [← hs]
      exact Submodule.subset_span (Set.mem_range_self i)
    exact (Submodule.mem_span_range_iff_exists_fun K).mp hi
  obtain ⟨T, hT⟩ : ∃ T : Matrix (Fin n) (Fin r) K, ∀ j, ∑ i, T j i • c i = C j :=
    ⟨fun j => (hT0 j).choose, fun j => (hT0 j).choose_spec⟩
  obtain ⟨L, hL⟩ : ∃ L : Matrix (Fin r) (Fin n) K, ∀ i, ∑ j, L i j • C j = c i :=
    ⟨fun i => (hL0 i).choose, fun i => (hL0 i).choose_spec⟩
  have hCT : C = T * c := by
    ext j k
    rw [← hT j, Matrix.mul_apply]
    simp [Finset.sum_apply]
  have hcL : c = L * C := by
    ext i k
    rw [← hL i, Matrix.mul_apply]
    simp [Finset.sum_apply]
  refine ⟨T, L, hCT, hcL, ?_⟩
  have hLT : L * T * c = c := by rw [Matrix.mul_assoc, ← hCT, ← hcL]
  have hz0 : (L * T - 1) * c = 0 := by rw [Matrix.sub_mul, hLT, Matrix.one_mul, sub_self]
  have hc' := Fintype.linearIndependent_iff.mp hc
  ext i0 i
  have hrow : ∑ i, (L * T - 1 : Matrix (Fin r) (Fin r) K) i0 i • c i = 0 := by
    funext k
    have h0 := congrFun (congrFun hz0 i0) k
    rw [Matrix.mul_apply] at h0
    simpa [Finset.sum_apply] using h0
  have h1 : (L * T - 1 : Matrix (Fin r) (Fin r) K) i0 i = 0 := hc' (fun i => (L * T - 1 : Matrix (Fin r) (Fin r) K) i0 i) hrow i
  rwa [Matrix.sub_apply, sub_eq_zero] at h1

end GlobalTheory.CompanionTheory.BruhatCoeffs
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SameSpanTransferMatricesStatement

section

@[expose] public section

open scoped Matrix
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions.EC

theorem _root_.GlobalTheory.T.same_span_transfer_matrices : ∀ {K : Type} [Field K] {n r : ℕ} (C : Matrix (Fin n) (Fin n) K) (c : Matrix (Fin r) (Fin n) K), LinearIndependent K c → Submodule.span K (Set.range c) = Submodule.span K (Set.range C) → ∃ (T : Matrix (Fin n) (Fin r) K) (L : Matrix (Fin r) (Fin n) K), C = T * c ∧ c = L * C ∧ L * T = 1 := by
  first | exact @GlobalTheory.CompanionTheory.BruhatCoeffs.exists_coeff_matrices_of_span_eq | exact GlobalTheory.CompanionTheory.BruhatCoeffs.exists_coeff_matrices_of_span_eq | (intros; apply GlobalTheory.CompanionTheory.BruhatCoeffs.exists_coeff_matrices_of_span_eq <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpanRangeComplementTransform

section

@[expose] public section

noncomputable section
open scoped Matrix
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions.EC

namespace GlobalTheory.CompanionTheory.BruhatCell

variable {K : Type} [Field K]

theorem span_range_mul_le {n : ℕ} (q M : Matrix (Fin n) (Fin n) K) :
    Submodule.span K (Set.range (q * M)) ≤ Submodule.span K (Set.range M) := by
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  have h : (q * M) i = ∑ k, q i k • M k := by
    funext j
    simp [Matrix.mul_apply, Finset.sum_apply]
  rw [h]
  exact Submodule.sum_mem _ fun k _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem span_range_mul_of_isUnit {n : ℕ} {p : Matrix (Fin n) (Fin n) K} (hp : IsUnit p.det)
    (M : Matrix (Fin n) (Fin n) K) :
    Submodule.span K (Set.range (p * M)) = Submodule.span K (Set.range M) := by
  refine le_antisymm (span_range_mul_le p M) ?_
  have h := span_range_mul_le p⁻¹ (p * M)
  rwa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hp, Matrix.one_mul] at h

theorem span_range_eId_mul {n r : ℕ} (hr : r ≤ n) {c : Matrix (Fin r) (Fin n) K}
    {a : Matrix (Fin n) (Fin n) K} (h : IsCompl c a) :
    Submodule.span K (Set.range (eId K n r * a)) = Submodule.span K (Set.range c) := by
  have row : ∀ i : Fin n, (eId K n r * a) i = if (i : ℕ) < r then a i else 0 := by
    intro i
    funext j
    by_cases hi : (i : ℕ) < r <;> simp [eId, Matrix.diagonal_mul, hi]
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    change (eId K n r * a) i ∈ _
    rw [row i]
    by_cases hi : (i : ℕ) < r
    · rw [if_pos hi, h.2 i hi]
      exact Submodule.subset_span ⟨_, rfl⟩
    · rw [if_neg hi]
      exact Submodule.zero_mem _
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    refine Submodule.subset_span ⟨⟨j, j.2.trans_le hr⟩, ?_⟩
    change (eId K n r * a) ⟨j, j.2.trans_le hr⟩ = c j
    rw [row, if_pos j.2, h.2 ⟨j, j.2.trans_le hr⟩ j.2]

theorem span_range_lowerLeft : ∀ {K : Type} [Field K] {n r : ℕ}, r ≤ n →
    ∀ (c : Matrix (Fin r) (Fin n) K) (a p : Matrix (Fin n) (Fin n) K), IsCompl c a → IsUnit p.det →
      Submodule.span K (Set.range (p * -(eId K n r * a))) = Submodule.span K (Set.range c) := by
  intro K _ n r hr c a p h hp
  have hneg : p * -(eId K n r * a) = (-p) * (eId K n r * a) := by
    rw [Matrix.mul_neg, Matrix.neg_mul]
  have hdet : IsUnit (-p).det := by
    rw [Matrix.det_neg]
    exact ((IsUnit.neg isUnit_one).pow _).mul hp
  rw [hneg, span_range_mul_of_isUnit hdet, span_range_eId_mul hr h]

end GlobalTheory.CompanionTheory.BruhatCell
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpanRangeComplementTransformStatement

section

@[expose] public section

open scoped Matrix
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions.EC

theorem _root_.GlobalTheory.T.span_range_complement_transform : ∀ {K : Type} [Field K] {n r : ℕ}, r ≤ n → ∀ (c : Matrix (Fin r) (Fin n) K) (a p : Matrix (Fin n) (Fin n) K), IsCompl c a → IsUnit p.det → Submodule.span K (Set.range (p * -(eId K n r * a))) = Submodule.span K (Set.range c) := by
  first | exact @GlobalTheory.CompanionTheory.BruhatCell.span_range_lowerLeft | exact GlobalTheory.CompanionTheory.BruhatCell.span_range_lowerLeft | (intros; apply GlobalTheory.CompanionTheory.BruhatCell.span_range_lowerLeft <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinBruhatDecomposition

section

@[expose] public section

noncomputable section
open scoped Matrix
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions.EC

namespace GlobalTheory.CompanionTheory.BruhatCell

variable {K : Type} [Field K]

theorem inv_block_of_unitary (σ : K →+* K) {n : ℕ} {A B C D : Matrix (Fin n) (Fin n) K}
    (h : IsUnitary σ (Jm K n) (blk4 A B C D)) :
    (blk4 A B C D)⁻¹ = blk4 (cT σ D) (-cT σ B) (-cT σ C) (cT σ A) := by
  rw [inv_of_unitary σ h, cT_blk4]
  unfold Jm
  rw [submatrix_fromBlocks_mul, submatrix_fromBlocks_mul, neg_block_matrix]
  congr 1 <;> simp

theorem isotropic_of_unitary (σ : K →+* K) {n : ℕ} {A B C D : Matrix (Fin n) (Fin n) K}
    (h : IsUnitary σ (Jm K n) (blk4 A B C D)) : C * cT σ D = D * cT σ C := by
  have h1 : blk4 A B C D * (blk4 A B C D)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_det_of_unitary σ h)
  rw [inv_block_of_unitary σ h, submatrix_fromBlocks_mul, ← block_matrix_one] at h1
  have := (blockMatrixTwoByTwoFin_injective h1).2.2.1
  rw [Matrix.mul_neg, ← sub_eq_add_neg, sub_eq_zero] at this
  exact this

theorem repMat_unitary (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) {n r : ℕ} (b : Matrix (Fin r) (Fin r) K)
    (a : Matrix (Fin n) (Fin n) K) (hb : cT σ b = b) (ha : IsUnit a.det) :
    IsUnit (repMat σ b a).det ∧ IsUnitary σ (Jm K n) (repMat σ b a) := by
  have hu : IsUnitary σ (Jm K n) (repMat σ b a) := by
    unfold repMat
    refine unitary_mul σ (unitary_mul σ ?_ ?_) ?_
    · unfold IsUnitary wr Jm
      rw [cT_blk4, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
      have e2 := eId_mul_eId (K := K) n r
      simp only [cT_sub, cT_one, cT_neg, cT_eId]
      congr 1
      · simp only [mul_zero, zero_add, add_zero, Matrix.mul_one, Matrix.mul_neg, neg_neg, Matrix.sub_mul,
          Matrix.mul_sub, Matrix.one_mul, Matrix.neg_mul, e2]; abel
      · simp only [mul_zero, zero_add, add_zero, Matrix.mul_one, Matrix.mul_neg, neg_neg, Matrix.sub_mul,
          Matrix.mul_sub, Matrix.one_mul, Matrix.neg_mul, e2]; abel
      · simp only [mul_zero, zero_add, add_zero, Matrix.mul_one, Matrix.mul_neg, neg_neg, Matrix.sub_mul,
          Matrix.mul_sub, Matrix.one_mul, Matrix.neg_mul, e2]; abel
      · simp only [mul_zero, zero_add, add_zero, Matrix.mul_one, Matrix.mul_neg, neg_neg, Matrix.sub_mul,
          Matrix.mul_sub, Matrix.one_mul, Matrix.neg_mul, e2]; abel
    · unfold IsUnitary nB Jm
      have hB : cT σ (extB (n := n) b) = extB b := by rw [cT_extB, hb]
      rw [cT_blk4, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
      simp [cT_one, cT_zero, hB]
    · unfold IsUnitary mA Jm
      have ha' := isUnit_det_cT σ ha
      rw [cT_blk4, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul, cT_inv σ ha', cT_cT σ hσ]
      simp [cT_zero, Matrix.mul_nonsing_inv _ ha', Matrix.nonsing_inv_mul _ ha]
  exact ⟨isUnit_det_of_unitary σ hu, hu⟩

theorem siegel_rep_iff (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) {n r : ℕ} (b : Matrix (Fin r) (Fin r) K)
    (a : Matrix (Fin n) (Fin n) K) (hb : cT σ b = b) (ha : IsUnit a.det) (A B C D : Matrix (Fin n) (Fin n) K) :
    IsSiegelP (blk4 A B C D * (repMat σ b a)⁻¹) ↔
      C * a⁻¹ * (1 - eId K n r - extB b) + D * cT σ a * eId K n r = 0 := by
  have hu := (repMat_unitary σ hσ b a hb ha).2
  rw [repMat_eq] at hu ⊢
  rw [inv_block_of_unitary σ hu, submatrix_fromBlocks_mul, is_siegel_parabolic_block_iff]
  simp only [cT_mul, cT_neg, cT_sub, cT_one, cT_eId, cT_extB, hb, cT_inv σ (isUnit_det_cT σ ha), cT_cT σ hσ,
    neg_neg, Matrix.mul_neg, Matrix.mul_assoc]

theorem factor_of_siegel {n : ℕ} {g h : Matrix (Fin (n + n)) (Fin (n + n)) K} (hg : IsUnit g.det)
    (hh : IsUnit h.det) (hp : IsSiegelP (g * h⁻¹)) {A B C D A' B' C' D' : Matrix (Fin n) (Fin n) K}
    (eg : g = blk4 A B C D) (eh : h = blk4 A' B' C' D') :
    ∃ p : Matrix (Fin n) (Fin n) K, IsUnit p.det ∧ C = p * C' ∧ D = p * D' := by
  obtain ⟨p1, p2, p3, p4, hp'⟩ := exists_blockMatrixTwoByTwoFin_eq (g * h⁻¹)
  rw [hp', is_siegel_parabolic_block_iff] at hp
  subst hp
  have hgp : g = blk4 p1 p2 0 p4 * h := by
    rw [← hp', Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hh, Matrix.mul_one]
  have hdet : IsUnit (blk4 p1 p2 0 p4).det := by
    rw [← hp', Matrix.det_mul]; exact hg.mul (Matrix.isUnit_nonsing_inv_det _ hh)
  rw [det_block_lower_zero] at hdet
  rw [eg, eh, submatrix_fromBlocks_mul] at hgp
  have := blockMatrixTwoByTwoFin_injective hgp
  refine ⟨p4, isUnit_of_mul_isUnit_right hdet, ?_, ?_⟩
  · simpa using this.2.2.1
  · simpa using this.2.2.2

theorem herm_unique (σ : K →+* K) {n r : ℕ} (hr : r ≤ n) (a : Matrix (Fin n) (Fin n) K) (ha : IsUnit a.det)
    (b b' : Matrix (Fin r) (Fin r) K) (p p' : Matrix (Fin n) (Fin n) K) (hp : IsUnit p.det)
    (hC : p * -(eId K n r * a) = p' * -(eId K n r * a))
    (hD : p * ((1 - eId K n r - extB b) * (cT σ a)⁻¹) = p' * ((1 - eId K n r - extB b') * (cT σ a)⁻¹)) :
    b = b' := by
  have ha' := isUnit_det_cT σ ha
  have h1 : p * eId K n r = p' * eId K n r := by
    have := congrArg (· * a⁻¹) hC
    simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ha] using this
  have h2 : p * (1 - eId K n r - extB b) = p' * (1 - eId K n r - extB b') := by
    have := congrArg (· * cT σ a) hD
    simpa [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ha'] using this
  have key : ∀ b₀ : Matrix (Fin r) (Fin r) K,
      (1 - eId K n r - extB b₀) * (1 - eId K n r) = 1 - eId K n r := by
    intro b₀
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, eId_mul_eId, extB_mul_eId]
    abel
  have h3 : p * (1 - eId K n r) = p' * (1 - eId K n r) := by
    calc p * (1 - eId K n r) = p * ((1 - eId K n r - extB b) * (1 - eId K n r)) := by rw [key]
      _ = p * (1 - eId K n r - extB b) * (1 - eId K n r) := by rw [Matrix.mul_assoc]
      _ = p' * (1 - eId K n r - extB b') * (1 - eId K n r) := by rw [h2]
      _ = p' * (1 - eId K n r) := by rw [Matrix.mul_assoc, key]
  have hpp : p = p' := by
    have e1 : ∀ q : Matrix (Fin n) (Fin n) K, q = q * eId K n r + q * (1 - eId K n r) := by
      intro q; rw [← Matrix.mul_add]; simp
    rw [e1 p, e1 p', h1, h3]
  subst hpp
  have := congrArg (p⁻¹ * ·) h2
  simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hp, Matrix.one_mul, sub_right_inj] at this
  exact extB_injective hr this

theorem bruhat : Bruhat := by
  intro K _ σ hσ _ n c hc a ha
  have hr : ∀ U : Submodule K (Fin n → K), Module.finrank K U ≤ n := fun U =>
    (Submodule.finrank_le U).trans (by simp)
  refine ⟨fun U b hb => repMat_unitary σ hσ b (a U) hb (ha U).1, ?_⟩
  intro g hg hgu
  obtain ⟨A, B, C, D, rfl⟩ := exists_blockMatrixTwoByTwoFin_eq g
  have hiso := isotropic_of_unitary σ hgu
  set U := Submodule.span K (Set.range C) with hU
  obtain ⟨T, L, hT, -, hLT⟩ := GlobalTheory.T.same_span_transfer_matrices C (c U) (hc U).1 (hc U).2
  obtain ⟨b, hb, hcond⟩ := GlobalTheory.T.hermitian_block_solution_exists σ hσ (hr U) (c U) (a U) C D T L (ha U) hT hLT hiso
  have hS := (siegel_rep_iff σ hσ b (a U) hb (ha U).1 A B C D).2 hcond
  refine ⟨⟨U, b, hb⟩, hS, ?_⟩
  rintro ⟨U', b', hb'⟩ hq
  have hrep' := repMat_unitary σ hσ b' (a U') hb' (ha U').1
  obtain ⟨p', hp', hC', hD'⟩ := factor_of_siegel hg hrep'.1 hq rfl (repMat_eq σ b' (a U'))
  have hUU : U' = U := by
    rw [← (hc U').2, ← GlobalTheory.T.span_range_complement_transform (hr U') (c U') (a U') p' (ha U') hp', ← hC']
  subst hUU
  have hrep := repMat_unitary σ hσ b (a U) hb (ha U).1
  obtain ⟨p, hp, hC, hD⟩ := factor_of_siegel hg hrep.1 hS rfl (repMat_eq σ b (a U))
  have hbb := herm_unique σ (hr U) (a U) (ha U).1 b' b p' p hp' (hC'.symm.trans hC) (hD'.symm.trans hD)
  subst hbb
  rfl

end GlobalTheory.CompanionTheory.BruhatCell
end
end
end
