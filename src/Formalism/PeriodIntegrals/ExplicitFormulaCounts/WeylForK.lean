module

public import Formalism.PeriodIntegrals.WeylForK
public import Formalism.PeriodIntegrals.ExplicitFormulaCounts.WeylForU
public import Formalism.PeriodIntegrals.WeylForU
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylFormulaCompact.FormulaStep
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylFormulaCompact.TypePlOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylFormulaCompact.DimStep
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylFormulaCompact.Formula
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylFormulaCompact.Weights

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylFormulaCompact.WeylForKOfSteps

section

@[expose] public section

noncomputable section

namespace PI.WeylForKWork

open PI PI.UpqRep Matrix

theorem weylForK_of_steps (hB : Blocks) (hTP : TypePl) (hTM : TypeMi) (hD : DimStep)
    (hF : FormulaStep) (hU : PI.WeylForU) : PI.WeylForK := by
  intro N ε Λ H _ _ σ S hσ hS
  obtain ⟨hB1, hB2, hB3, hB4, hB5⟩ := hB N ε
  obtain ⟨hσP, hσM⟩ := hB5 H σ hσ
  obtain ⟨X, hXS, hX⟩ := hTP N ε Λ H σ S hσ hS
  obtain ⟨Y, hYS, hY⟩ := hTM N ε Λ H σ S hσ hS
  have hmul : ∀ g ∈ Kset ε, ∀ g' ∈ Kset ε, σ (g * g') = (σ g).comp (σ g') := hσ.1.2
  have hSst : IsKStableOn ε σ S := hS.2.1
  have hcomm : ∀ h ∈ Kset (allPos (nPl ε)), ∀ h' ∈ Kset (allPos (nMi ε)),
      (sPl ε σ h).comp (sMi ε σ h') = (sMi ε σ h').comp (sPl ε σ h) := by
    intro h hh h' hh'
    show (σ (iPl ε h)).comp (σ (iMi ε h')) = (σ (iMi ε h')).comp (σ (iPl ε h))
    rw [← hmul _ (hB1 h hh) _ (hB2 h' hh'), ← hmul _ (hB2 h' hh') _ (hB1 h hh), hB3]
  have hstP : IsKStableOn (allPos (nPl ε)) (sPl ε σ) S := fun h hh v hv => hSst _ (hB1 h hh) v hv
  have hstM : IsKStableOn (allPos (nMi ε)) (sMi ε σ) S := fun h hh v hv => hSst _ (hB2 h hh) v hv
  have hirr : ∀ S' : Submodule ℂ H, S' ≤ S → IsKStableOn (allPos (nPl ε)) (sPl ε σ) S' →
      IsKStableOn (allPos (nMi ε)) (sMi ε σ) S' → S' = ⊥ ∨ S' = S := by
    intro S' hS' h1 h2
    refine hS.2.2.1 S' hS' (fun g hg v hv => ?_)
    obtain ⟨h, hh, h', hh', rfl⟩ := hB4 g hg
    rw [hmul _ (hB1 h hh) _ (hB2 h' hh')]
    exact h1 h hh _ (h2 h' hh' v hv)
  have hX0 : X ≠ ⊥ := by
    obtain ⟨v, hv, hv0, _⟩ := hX.2.2.2.1
    intro hbot
    rw [hbot] at hv
    exact hv0 ((Submodule.mem_bot ℂ).1 hv)
  have hY0 : Y ≠ ⊥ := by
    obtain ⟨v, hv, hv0, _⟩ := hY.2.2.2.1
    intro hbot
    rw [hbot] at hv
    exact hv0 ((Submodule.mem_bot ℂ).1 hv)
  have hdim := hD (nPl ε) (nMi ε) H (sPl ε σ) (sMi ε σ) S X Y hσP hσM hcomm hS.1 hstP hstM hirr
    hXS hX0 hX.2.1 hX.2.2.1 hYS hY0 hY.2.1 hY.2.2.1
  have hwX := hU (nPl ε) (fun i => Λ (ePl ε i)) H (sPl ε σ) X hσP hX
  have hwY := hU (nMi ε) (fun j => Λ (eMi ε j)) H (sMi ε σ) Y hσM hY
  rw [hF N ε Λ, hdim, Nat.cast_mul, hwX, hwY]
  rfl

end PI.WeylForKWork
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylFormulaCompact.Assemble

section

@[expose] public section

noncomputable section

namespace PI.WeylForKWork

theorem weylForK_of_leaves (hB : Blocks) (hBD : BlockDiag) (hT : TorusWt) (hW : WtUniq) (hM : MinIrr)
    (hC : CDomRes) (hD : DimStep) (hF : FormulaStep) : PI.WeylForU → PI.WeylForK := by
  exact fun hU => weylForK_of_steps hB (typePl_of hB hBD hT hW hM hC) (typeMi_of hB hBD hT hW hM hC)
    hD hF hU

end PI.WeylForKWork
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylFormulaCompact.Blocks

section

@[expose] public section

noncomputable section

namespace PI.WeylForKWork

open PI PI.UpqRep Matrix

variable {N : ℕ}

abbrev blR (ε : Fin N → Bool) :
    Matrix (Fin (nPl ε) ⊕ Fin (nMi ε)) (Fin (nPl ε) ⊕ Fin (nMi ε)) ℂ ≃ₐ[ℂ] Matrix (Fin N) (Fin N) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ (blk ε)

lemma blR_apply (ε : Fin N → Bool) (M : Matrix (Fin (nPl ε) ⊕ Fin (nMi ε)) (Fin (nPl ε) ⊕ Fin (nMi ε)) ℂ) :
    blR ε M = M.submatrix (blk ε).symm (blk ε).symm := rfl

lemma plusBlock_eq_blockReindex (ε : Fin N → Bool) (h : Matrix (Fin (nPl ε)) (Fin (nPl ε)) ℂ) :
    iPl ε h = blR ε (fromBlocks h 0 0 1) := rfl

lemma minusBlock_eq_blockReindex (ε : Fin N → Bool) (h : Matrix (Fin (nMi ε)) (Fin (nMi ε)) ℂ) :
    iMi ε h = blR ε (fromBlocks 1 0 0 h) := rfl

lemma sign_blockEquiv_inl (ε : Fin N → Bool) (i : Fin (nPl ε)) : ε (blk ε (Sum.inl i)) = true := by
  exact Subtype.prop (p := fun a => ε a = true) _

lemma sign_blockEquiv_inr (ε : Fin N → Bool) (j : Fin (nMi ε)) : ε (blk ε (Sum.inr j)) = false := by
  exact Bool.eq_false_iff.2 (Subtype.prop (p := fun a => ¬ ε a = true) _)

lemma signatureMatrix_eq_blockReindex (ε : Fin N → Bool) : Jm ε = blR ε (fromBlocks 1 0 0 (-1)) := by
  rw [blR_apply]
  ext a c
  obtain ⟨x, rfl⟩ := (blk ε).surjective a
  obtain ⟨y, rfl⟩ := (blk ε).surjective c
  simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply, Jm, Matrix.diagonal_apply,
    (blk ε).injective.eq_iff]
  rcases x with i | j <;> rcases y with i' | j'
  · by_cases h : i = i' <;> simp [h, Matrix.one_apply, sign_blockEquiv_inl]
  · simp
  · simp
  · by_cases h : j = j' <;> simp [h, Matrix.one_apply, sign_blockEquiv_inr]

lemma signatureMatrix_allPos_eq_one (n : ℕ) : Jm (allPos n) = 1 := by
  simp [Jm, allPos]

lemma star_blockReindex (ε : Fin N → Bool) (M : Matrix (Fin (nPl ε) ⊕ Fin (nMi ε)) (Fin (nPl ε) ⊕ Fin (nMi ε)) ℂ) :
    star (blR ε M) = blR ε (star M) := by
  simp only [blR_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix]

lemma blockReindex_mem_unitaryGroup_iff (ε : Fin N → Bool) (M : Matrix (Fin (nPl ε) ⊕ Fin (nMi ε)) (Fin (nPl ε) ⊕ Fin (nMi ε)) ℂ) :
    blR ε M ∈ unitaryGroup (Fin N) ℂ ↔ M ∈ unitaryGroup _ ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.mem_unitaryGroup_iff, star_blockReindex, ← map_mul,
    ← map_one (blR ε), (blR ε).injective.eq_iff]

lemma blockReindex_mem_unitaryCentralizer_iff (ε : Fin N → Bool) (M : Matrix (Fin (nPl ε) ⊕ Fin (nMi ε)) (Fin (nPl ε) ⊕ Fin (nMi ε)) ℂ) :
    blR ε M ∈ Kset ε ↔ M ∈ unitaryGroup _ ℂ ∧ M * fromBlocks 1 0 0 (-1) = fromBlocks 1 0 0 (-1) * M := by
  show blR ε M ∈ unitaryGroup _ ℂ ∧ blR ε M * Jm ε = Jm ε * blR ε M ↔ _
  rw [blockReindex_mem_unitaryGroup_iff, signatureMatrix_eq_blockReindex, ← map_mul, ← map_mul, (blR ε).injective.eq_iff]

lemma mem_unitaryCentralizer_allPos_iff (n : ℕ) (h : Matrix (Fin n) (Fin n) ℂ) : h ∈ Kset (allPos n) ↔ h ∈ unitaryGroup _ ℂ := by
  show h ∈ unitaryGroup _ ℂ ∧ h * Jm (allPos n) = Jm (allPos n) * h ↔ _
  rw [signatureMatrix_allPos_eq_one]
  simp

section blocks

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

lemma fromBlocks_diagonal_mem_unitaryGroup_iff (A : Matrix m m ℂ) (D : Matrix n n ℂ) :
    fromBlocks A 0 0 D ∈ unitaryGroup (m ⊕ n) ℂ ↔ A ∈ unitaryGroup m ℂ ∧ D ∈ unitaryGroup n ℂ := by
  have h1 : (1 : Matrix (m ⊕ n) (m ⊕ n) ℂ) = fromBlocks 1 0 0 1 := Matrix.fromBlocks_one.symm
  simp only [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, h1, Matrix.fromBlocks_inj]
  simp

lemma fromBlocks_diagonal_mul_signature_comm (A : Matrix m m ℂ) (D : Matrix n n ℂ) :
    fromBlocks A 0 0 D * fromBlocks 1 0 0 (-1) = fromBlocks 1 0 0 (-1) * fromBlocks A 0 0 D := by
  simp [Matrix.fromBlocks_multiply]

end blocks

lemma plusBlock_one (ε : Fin N → Bool) : iPl ε 1 = 1 := by
  rw [plusBlock_eq_blockReindex, Matrix.fromBlocks_one, map_one]

lemma minusBlock_one (ε : Fin N → Bool) : iMi ε 1 = 1 := by
  rw [minusBlock_eq_blockReindex, Matrix.fromBlocks_one, map_one]

lemma plusBlock_mul (ε : Fin N → Bool) (a b : Matrix (Fin (nPl ε)) (Fin (nPl ε)) ℂ) :
    iPl ε (a * b) = iPl ε a * iPl ε b := by
  rw [plusBlock_eq_blockReindex, plusBlock_eq_blockReindex, plusBlock_eq_blockReindex, ← map_mul, Matrix.fromBlocks_multiply]
  simp

lemma minusBlock_mul (ε : Fin N → Bool) (a b : Matrix (Fin (nMi ε)) (Fin (nMi ε)) ℂ) :
    iMi ε (a * b) = iMi ε a * iMi ε b := by
  rw [minusBlock_eq_blockReindex, minusBlock_eq_blockReindex, minusBlock_eq_blockReindex, ← map_mul, Matrix.fromBlocks_multiply]
  simp

lemma continuous_plusBlock (ε : Fin N → Bool) : Continuous (iPl ε) := by
  unfold iPl
  exact (continuous_id.matrix_fromBlocks continuous_const continuous_const
    continuous_const).matrix_submatrix _ _

lemma continuous_minusBlock (ε : Fin N → Bool) : Continuous (iMi ε) := by
  unfold iMi
  exact (continuous_const.matrix_fromBlocks continuous_const continuous_const
    continuous_id).matrix_submatrix _ _

lemma plusBlock_mem_unitaryCentralizer (ε : Fin N → Bool) (h : Matrix (Fin (nPl ε)) (Fin (nPl ε)) ℂ)
    (hh : h ∈ Kset (allPos (nPl ε))) : iPl ε h ∈ Kset ε := by
  rw [mem_unitaryCentralizer_allPos_iff] at hh
  rw [plusBlock_eq_blockReindex, blockReindex_mem_unitaryCentralizer_iff]
  exact ⟨(fromBlocks_diagonal_mem_unitaryGroup_iff _ _).2 ⟨hh, one_mem _⟩, fromBlocks_diagonal_mul_signature_comm _ _⟩

lemma minusBlock_mem_unitaryCentralizer (ε : Fin N → Bool) (h : Matrix (Fin (nMi ε)) (Fin (nMi ε)) ℂ)
    (hh : h ∈ Kset (allPos (nMi ε))) : iMi ε h ∈ Kset ε := by
  rw [mem_unitaryCentralizer_allPos_iff] at hh
  rw [minusBlock_eq_blockReindex, blockReindex_mem_unitaryCentralizer_iff]
  exact ⟨(fromBlocks_diagonal_mem_unitaryGroup_iff _ _).2 ⟨one_mem _, hh⟩, fromBlocks_diagonal_mul_signature_comm _ _⟩

lemma isUnitaryRepOn_comp {n : ℕ} (ε : Fin N → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (ι : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin N) (Fin N) ℂ)
    (h1 : ι 1 = 1) (hmul : ∀ a b, ι (a * b) = ι a * ι b) (hmem : ∀ h ∈ Kset (allPos n), ι h ∈ Kset ε)
    (hcont : Continuous ι) (hσ : IsURepOn (Kset ε) σ) : IsURepOn (Kset (allPos n)) (fun h => σ (ι h)) := by
  refine ⟨⟨?_, fun a ha b hb => ?_⟩, fun g hg v => hσ.2.1 (ι g) (hmem g hg) v, fun v => ?_⟩
  · show σ (ι 1) = 1
    rw [h1]
    exact hσ.1.1
  · show σ (ι (a * b)) = (σ (ι a)).comp (σ (ι b))
    rw [hmul]
    exact hσ.1.2 _ (hmem a ha) _ (hmem b hb)
  · exact (hσ.2.2 v).comp hcont.continuousOn hmem

theorem block_reindex_holds : Blocks := by
  intro N ε
  refine ⟨fun h hh => plusBlock_mem_unitaryCentralizer ε h hh, fun h hh => minusBlock_mem_unitaryCentralizer ε h hh, fun h h' => ?_,
    fun g hg => ?_, fun H _ _ σ hσ => ?_⟩
  · rw [plusBlock_eq_blockReindex, minusBlock_eq_blockReindex, ← map_mul, ← map_mul, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp
  · obtain ⟨M, rfl⟩ := (blR ε).surjective g
    rw [blockReindex_mem_unitaryCentralizer_iff] at hg
    obtain ⟨hU, hC⟩ := hg
    have hM := Matrix.fromBlocks_toBlocks M
    set A := M.toBlocks₁₁
    set B := M.toBlocks₁₂
    set C := M.toBlocks₂₁
    set D := M.toBlocks₂₂
    rw [← hM, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj] at hC
    simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      Matrix.mul_neg, Matrix.neg_mul] at hC
    have hB : B = 0 := by
      ext i j
      have h := congr_fun (congr_fun hC.2.1 i) j
      simp only [Matrix.neg_apply] at h
      simp only [Matrix.zero_apply]
      linear_combination (-1 / 2 : ℂ) * h
    have hC0 : C = 0 := by
      ext i j
      have h := congr_fun (congr_fun hC.2.2.1 i) j
      simp only [Matrix.neg_apply] at h
      simp only [Matrix.zero_apply]
      linear_combination (1 / 2 : ℂ) * h
    rw [← hM, hB, hC0, fromBlocks_diagonal_mem_unitaryGroup_iff] at hU
    refine ⟨A, (mem_unitaryCentralizer_allPos_iff _ A).2 hU.1, D, (mem_unitaryCentralizer_allPos_iff _ D).2 hU.2, ?_⟩
    rw [plusBlock_eq_blockReindex, minusBlock_eq_blockReindex, ← map_mul, Matrix.fromBlocks_multiply, ← hM, hB, hC0]
    congr 1
    simp
  · exact ⟨isUnitaryRepOn_comp ε σ (iPl ε) (plusBlock_one ε) (plusBlock_mul ε) (plusBlock_mem_unitaryCentralizer ε) (continuous_plusBlock ε) hσ,
      isUnitaryRepOn_comp ε σ (iMi ε) (minusBlock_one ε) (minusBlock_mul ε) (minusBlock_mem_unitaryCentralizer ε) (continuous_minusBlock ε) hσ⟩

theorem block_diagonal_torus_holds : BlockDiag := by
  intro N ε
  refine ⟨fun f => ?_, fun θ => ?_, fun θ => ?_⟩
  · rw [← Equiv.sum_comp (blk ε), Fintype.sum_sum_type]
    rfl
  · refine ⟨fun a => Sum.elim θ 0 ((blk ε).symm a), fun i => by simp [ePl], fun j => by simp [eMi], ?_⟩
    unfold iPl
    rw [← Matrix.diagonal_one, Matrix.fromBlocks_diagonal, Matrix.submatrix_diagonal_equiv]
    congr 1
    funext a
    rcases h : (blk ε).symm a with i | j <;> simp [h]
  · refine ⟨fun a => Sum.elim 0 θ ((blk ε).symm a), fun i => by simp [ePl], fun j => by simp [eMi], ?_⟩
    unfold iMi
    rw [← Matrix.diagonal_one, Matrix.fromBlocks_diagonal, Matrix.submatrix_diagonal_equiv]
    congr 1
    funext a
    rcases h : (blk ε).symm a with i | j <;> simp [h]

end PI.WeylForKWork
end
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WeylForK

section

@[expose] public section

theorem weylForK_of : PI.WeylForU → PI.WeylForK :=
  PI.WeylForKWork.weylForK_of_leaves PI.WeylForKWork.block_reindex_holds PI.WeylForKWork.block_diagonal_torus_holds
    PI.WeylForKWork.torus_weight_exists PI.WeylForKWork.weight_unique_holds PI.WeylForKWork.minimal_irreducible_exists
    PI.WeylForKWork.dominant_restriction_holds PI.WeylForKWork.dimension_induction_holds PI.WeylForKWork.weyl_formula_compact
end
end

-- Source module: Formalism.PeriodIntegrals.ExplicitFormulaCounts.WeylForK

section

@[expose] public section

theorem weylForK_closed : PI.WeylForK := weylForK_of weylForU_closed
end
end
