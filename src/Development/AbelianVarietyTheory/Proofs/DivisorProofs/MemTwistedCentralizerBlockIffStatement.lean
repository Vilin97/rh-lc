module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParP
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfIntertwineOfIsCoprimeCharpoly

section

@[expose] public section

namespace GlobalTheory.IntertwinerCoprimeCharpoly

open Polynomial

theorem pow_intertwine {K : Type} [Field K] {a b : ℕ} (A : Matrix (Fin a) (Fin a) K)
    (B : Matrix (Fin b) (Fin b) K) (C : Matrix (Fin b) (Fin a) K) (h : C * A = B * C) (n : ℕ) :
    C * A ^ n = B ^ n * C := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, h, ← Matrix.mul_assoc]

theorem aeval_intertwine {K : Type} [Field K] {a b : ℕ} (A : Matrix (Fin a) (Fin a) K)
    (B : Matrix (Fin b) (Fin b) K) (C : Matrix (Fin b) (Fin a) K) (h : C * A = B * C) (p : K[X]) :
    C * aeval A p = aeval B p * C := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), Matrix.mul_add, Matrix.add_mul, hp, hq]
  | monomial n c =>
    simp only [aeval_monomial, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, pow_intertwine A B C h n]

theorem eq_zero_of_intertwine_of_isCoprime_charpoly {K : Type} [Field K] {a b : ℕ}
    (A : Matrix (Fin a) (Fin a) K) (B : Matrix (Fin b) (Fin b) K) (C : Matrix (Fin b) (Fin a) K)
    (hcop : IsCoprime (Matrix.charpoly A) (Matrix.charpoly B)) (h : C * A = B * C) :
    C = (0 : Matrix (Fin b) (Fin a) K) := by
  obtain ⟨u, v, huv⟩ := hcop
  have h1 : aeval B (u * A.charpoly + v * B.charpoly) = 1 := by rw [huv, map_one]
  rw [map_add (f := _), map_mul, map_mul, Matrix.aeval_self_charpoly, mul_zero, add_zero] at h1
  have h2 : aeval B A.charpoly * C = 0 := by
    rw [← aeval_intertwine A B C h, Matrix.aeval_self_charpoly, Matrix.mul_zero]
  calc C = 1 * C := (Matrix.one_mul C).symm
    _ = (aeval B u * aeval B A.charpoly) * C := by rw [h1]
    _ = aeval B u * (aeval B A.charpoly * C) := Matrix.mul_assoc _ _ _
    _ = 0 := by rw [h2, Matrix.mul_zero]

theorem main : ∀ {K : Type} [inst : Field K] {a b : ℕ} (A : Matrix (Fin a) (Fin a) K)
    (B : Matrix (Fin b) (Fin b) K) (C : Matrix (Fin b) (Fin a) K),
    IsCoprime (Matrix.charpoly A) (Matrix.charpoly B) → C * A = B * C →
      C = (0 : Matrix (Fin b) (Fin a) K) :=
  fun A B C hcop h => eq_zero_of_intertwine_of_isCoprime_charpoly A B C hcop h

end GlobalTheory.IntertwinerCoprimeCharpoly
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTwistedCentralizerBlockIff

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LeviDesc.CentPar

theorem intertwiner_eq_zero {K : Type} [Field K] {a b : ℕ}
    (A : Matrix (Fin a) (Fin a) K) (B : Matrix (Fin b) (Fin b) K) (C : Matrix (Fin b) (Fin a) K)
    (hc : IsCoprime A.charpoly B.charpoly) (hC : C * A = B * C) : C = 0 := by
  first
  | exact @_root_.GlobalTheory.IntertwinerCoprimeCharpoly.main
  | exact _root_.GlobalTheory.IntertwinerCoprimeCharpoly.main
  | (apply _root_.GlobalTheory.IntertwinerCoprimeCharpoly.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntertwinerCoprimeCharpoly.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntertwinerCoprimeCharpoly.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntertwinerCoprimeCharpoly.main ..)

variable {E : Type} [Field E] [NumberField E]

theorem blk_zero_val {n a b : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w) :
    ((blk h w m 0 : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
      Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
        (Matrix.fromBlocks m.1.val 0 0 m.2.val) := by
  have hM : IsUnit (Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (Matrix.fromBlocks m.1.val (m.1.val * (0 : Matrix (Fin a) (Fin b) (w.adicCompletion E))) 0 m.2.val)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_reindex_self, Matrix.mul_zero, Matrix.det_fromBlocks_zero₁₂]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp m.1.isUnit).mul ((Matrix.isUnit_iff_isUnit_det _).mp m.2.isUnit)
  simp only [blk]
  rw [dite_eq_left hM]
  simp

theorem blk_zero_mul {n a b : ℕ} (h : a + b = n) (w : Pl E) (x y : GLw a w × GLw b w) :
    blk h w (x * y) 0 = blk h w x 0 * blk h w y 0 := by
  apply Units.ext
  rw [Units.val_mul, blk_zero_val, blk_zero_val, blk_zero_val]
  simp only [Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp [Prod.fst_mul, Prod.snd_mul]

end GlobalTheory.LeviDesc.CentPar


open GlobalTheory.LeviDesc.CentPar in
theorem GlobalTheory.LeviDesc.mem_twistedCentralizer_parabolic_iff : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E)
    (m : GLw a w × GLw b w), (m.1.val.charpoly * m.2.val.charpoly).Separable →
    ∀ (hγ : blk h w m 0 ∈ GlobalTheory.LeviDesc.parP a n w) (p : GlobalTheory.LeviDesc.parP a n w),
      p ∈ twCent (MonoidHom.id _) (⟨blk h w m 0, hγ⟩ : GlobalTheory.LeviDesc.parP a n w) ↔
        ∃ t ∈ twCent (MonoidHom.id _) m, blk h w t 0 = (p : GLw n w) := by
  intro E _ _ n a b h w m hsep hγ p
  have hcop := hsep.isCoprime
  have hmem : p ∈ twCent (MonoidHom.id _) (⟨blk h w m 0, hγ⟩ : GlobalTheory.LeviDesc.parP a n w) ↔
      (p : GLw n w) * blk h w m 0 = blk h w m 0 * (p : GLw n w) := by
    show p * _ = _ * MonoidHom.id _ p ↔ _
    rw [MonoidHom.id_apply, Subtype.ext_iff]
    rfl
  rw [hmem]
  constructor
  · intro hc
    set e := finSumFinEquiv.trans (finCongr h) with he
    set g' := Matrix.reindex e.symm e.symm ((p : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) with hg'
    have hgg : ((p : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = Matrix.reindex e e g' := by
      simp [hg']
    have hcM := congrArg Units.val hc
    rw [Units.val_mul, Units.val_mul, blk_zero_val, ← he, hgg, ← Matrix.fromBlocks_toBlocks g'] at hcM
    have hc2 := congrArg (Matrix.reindex e.symm e.symm) hcM
    simp only [Matrix.reindex_apply, Equiv.symm_symm, Matrix.submatrix_mul_equiv, Matrix.submatrix_submatrix,
      Equiv.symm_comp_self, Matrix.submatrix_id_id, Matrix.fromBlocks_multiply] at hc2
    rw [Matrix.fromBlocks_inj] at hc2
    obtain ⟨h11, h12, h21, h22⟩ := hc2
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at h11 h12 h21 h22
    have hC0 : g'.toBlocks₂₁ = 0 := intertwiner_eq_zero _ _ _ hcop h21
    have hB0 : g'.toBlocks₁₂ = 0 := intertwiner_eq_zero _ _ _ hcop.symm h12
    have hg'2 : g' = Matrix.fromBlocks g'.toBlocks₁₁ 0 0 g'.toBlocks₂₂ := by
      rw [← hB0, ← hC0, Matrix.fromBlocks_toBlocks]
    have hdet : IsUnit g'.det := by
      rw [hg', Matrix.det_reindex_self]
      exact (Matrix.isUnit_iff_isUnit_det _).mp (p : GLw n w).isUnit
    rw [hg'2, Matrix.det_fromBlocks_zero₂₁] at hdet
    have hA : IsUnit g'.toBlocks₁₁ := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_of_mul_isUnit_left hdet)
    have hD : IsUnit g'.toBlocks₂₂ := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_of_mul_isUnit_right hdet)
    refine ⟨(hA.unit, hD.unit), ?_, ?_⟩
    · show (hA.unit, hD.unit) * m = m * MonoidHom.id _ (hA.unit, hD.unit)
      rw [MonoidHom.id_apply]
      refine Prod.ext (Units.ext ?_) (Units.ext ?_)
      · simpa using h11
      · simpa using h22
    · apply Units.ext
      rw [blk_zero_val, ← he, hgg]
      conv_rhs => rw [hg'2]
      rfl
  · rintro ⟨t, ht, hp⟩
    have ht' : t * m = m * t := ht
    rw [← hp, ← blk_zero_mul, ← blk_zero_mul, ht']
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTwistedCentralizerBlockIffStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.mem_twisted_centralizer_block_iff : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w), (m.1.val.charpoly * m.2.val.charpoly).Separable → ∀ (hγ : blk h w m 0 ∈ GlobalTheory.LeviDesc.parP a n w) (p : GlobalTheory.LeviDesc.parP a n w), p ∈ twCent (MonoidHom.id _) (⟨blk h w m 0, hγ⟩ : GlobalTheory.LeviDesc.parP a n w) ↔ ∃ t ∈ twCent (MonoidHom.id _) m, blk h w t 0 = (p : GLw n w) := by
  first | exact @GlobalTheory.LeviDesc.mem_twistedCentralizer_parabolic_iff | exact GlobalTheory.LeviDesc.mem_twistedCentralizer_parabolic_iff | (intros; apply GlobalTheory.LeviDesc.mem_twistedCentralizer_parabolic_iff <;> assumption)
end
end
