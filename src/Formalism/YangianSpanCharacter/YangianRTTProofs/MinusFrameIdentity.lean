module

public import Formalism.YangianSpanCharacter.ExchangeGen
public import Formalism.YangianSpanCharacter.StatementY
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Formalism.YangianSpanCharacter.YangianRTTProofs.DiagonalEntryEqOfModularRelation
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Formalism.YangianSpanCharacter.StatementF

section

@[expose] public section

namespace Formalism.YangianSpanCharacter.F

open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y

def blk {A : Type*} (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) (i j : Fin 2) :
    Matrix (Fin 2) (Fin 2) A :=
  Matrix.of fun k l => M (i, k) (j, l)

def sc {A : Type*} [Ring A] (x : A) : Matrix (Fin 2) (Fin 2) A := Matrix.diagonal fun _ => x

def PlusFrame : Prop :=
  ∀ (𝕜 A : Type) [Field 𝕜] [Ring A] [Algebra 𝕜 A] (t : 𝕜 → Matrix (Fin 2) (Fin 2) A)
    (τinv : 𝕜 → A) (q : 𝕜 → 𝕜) (S : Set 𝕜), ModHyp t τinv q S →
    ∀ Y Ya : 𝕜, Y ∈ S → Ya ∈ S → Y - Ya ≠ 0 → Y - Ya - 1 ≠ 0 →
      let D := Y - Ya
      let tn := E1 (t Y) * ((D - 1)⁻¹ • (D • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Pf A))
      let l := lf t τinv Y
      let M : Matrix (Fin 2) (Fin 2) A := !![algebraMap 𝕜 A D, 0; -l, algebraMap 𝕜 A (D - 1)]
      let N : Matrix (Fin 2) (Fin 2) A := !![(D - 1) • l, -1; 0, D • l]
      let G : Matrix (Fin 2) (Fin 2) A := !![1, 0; lf t τinv Ya, 1]
      let Ginv : Matrix (Fin 2) (Fin 2) A := !![1, 0; -lf t τinv Ya, 1]
      blk tn 1 1 = (D - 1)⁻¹ • (sc (t Y 1 1) * M) ∧
      blk tn 1 0 = (D - 1)⁻¹ • (sc (t Y 1 1) * N) ∧
      G * Ginv = 1 ∧
      G * (sc (t Y 1 1) * M) =
        sc (t Y 1 1) * !![algebraMap 𝕜 A D, 0; 0, algebraMap 𝕜 A (D - 1)] * G ∧
      N * Ginv = M * Ginv *
        !![l - eta t τinv Y Ya, -algebraMap 𝕜 A D⁻¹; 0, l + eta t τinv Y Ya]

def MinusFrame : Prop :=
  ∀ (𝕜 A : Type) [Field 𝕜] [Ring A] [Algebra 𝕜 A] (t : 𝕜 → Matrix (Fin 2) (Fin 2) A)
    (τinv : 𝕜 → A) (q : 𝕜 → 𝕜) (S : Set 𝕜), ModHyp t τinv q S →
    ∀ Y Yb : 𝕜, Y ∈ S → Y + 1 ∈ S → Yb ∈ S → Yb + 1 ∈ S → Yb - 1 ∈ S →
      Yb - Y ≠ 0 → Yb - Y - 1 ≠ 0 →
      let d := Yb - Y
      let tn := ((d - 1)⁻¹ • pt1 (d • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Pf A)) *
        E1 (t Y)
      let τn : Matrix (Fin 2) (Fin 2) A := !![d • t Y 1 1, 0; -t Y 0 1, (d - 1) • t Y 1 1]
      let Ln : Matrix (Fin 2) (Fin 2) A :=
        !![lf t τinv Y, 0; -((d - 1)⁻¹ • hf τinv q Y), lf t τinv Y]
      let Gb : Matrix (Fin 2) (Fin 2) A := !![1, 0; mf t τinv Yb, 1]
      blk tn 1 1 = (d - 1)⁻¹ • τn ∧
      blk tn 1 0 = (d - 1)⁻¹ • !![d • t Y 1 0, 0; -t Y 0 0, (d - 1) • t Y 1 0] ∧
      τn * Ln = !![d • t Y 1 0, 0; -t Y 0 0, (d - 1) • t Y 1 0] ∧
      Gb * τn = !![d • t Y 1 1, 0; 0, (d - 1) • t Y 1 1] * Gb ∧
      Gb * Ln = !![lf t τinv Y, 0; -((d - 1)⁻¹ • hf τinv q (Yb - 1)), lf t τinv Y] * Gb

end Formalism.YangianSpanCharacter.F
end
end

-- Source module: Formalism.YangianSpanCharacter.YangianRTTProofs.MinusFrameIdentity

section

@[expose] public section

namespace Formalism.YangianSpanCharacter.P

open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.YangianSpanCharacter.F

set_option linter.unusedSimpArgs false

theorem minus_frame_identity : Formalism.YangianSpanCharacter.F.MinusFrame := by
  intro 𝕜 A _ _ _ t τinv q S H Y Yb hY hY1 hYb hYb1 hYbm hd hd1 d tn τn Ln Gb
  have hd1' : d - 1 ≠ 0 := hd1
  have hne : Y ≠ Yb := fun h => hd (by rw [h, sub_self])
  have i0 := H.2.2.2.1 Y hY
  have hτl : t Y 1 1 * lf t τinv Y = t Y 1 0 := by
    unfold lf; rw [← mul_assoc, i0.1, one_mul]
  have hτm : t Y 1 1 * mf t τinv Y = t Y 0 1 := by
    unfold mf; rw [← mul_assoc, i0.1, one_mul]
  have QD : t Y 0 0 - t Y 0 1 * lf t τinv Y = q Y • τinv (Y + 1) := by
    have := qdet_mod H hY hY1; unfold lf; rw [← mul_assoc]; exact this
  have hτh : t Y 1 1 * hf τinv q Y = q Y • τinv (Y + 1) := by
    unfold hf; rw [mul_smul_comm, ← mul_assoc, i0.1, one_mul]
  have Y1' : t Y 1 1 * mf t τinv Yb - mf t τinv Yb * t Y 1 1 = t Y 1 1 * mu t τinv Y Yb :=
    y1'_mod H hY hYb hne
  have hμ0 : (Y - Yb) • mu t τinv Y Yb = mf t τinv Y - mf t τinv Yb := by
    unfold mu; exact smul_inv_smul₀ (sub_ne_zero.mpr hne) _
  have hτμ : d • (t Y 1 1 * mu t τinv Y Yb) = t Y 1 1 * mf t τinv Yb - t Y 0 1 := by
    show (Yb - Y) • (t Y 1 1 * mu t τinv Y Yb) = _
    rw [show Yb - Y = -(Y - Yb) by ring, neg_smul, ← mul_smul_comm, hμ0, mul_sub, hτm, neg_sub]
  have Y3 : (d - 1) • (mf t τinv Yb * lf t τinv Y - lf t τinv Y * mf t τinv Yb) =
      hf τinv q Y - hf τinv q (Yb - 1) :=
    yangian_relation_three_holds 𝕜 A t τinv q S H Yb Y hYb hYb1 hYbm hY hY1 (Ne.symm hne)
  have Y3' : mf t τinv Yb * lf t τinv Y - lf t τinv Y * mf t τinv Yb =
      (d - 1)⁻¹ • (hf τinv q Y - hf τinv q (Yb - 1)) := by
    rw [← Y3, inv_smul_smul₀ hd1']
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext k l'
    fin_cases k <;> fin_cases l' <;>
      simp [tn, τn, blk, pt1, E1, Pf, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
        Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, sub_mul, mul_sub, add_mul, mul_add, neg_mul, mul_neg]
    all_goals module
  · ext k l'
    fin_cases k <;> fin_cases l' <;>
      simp [tn, blk, pt1, E1, Pf, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
        Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, sub_mul, mul_sub, add_mul, mul_add, neg_mul, mul_neg]
    all_goals module
  · ext k l'
    fin_cases k <;> fin_cases l' <;>
      simp [τn, Ln, Matrix.mul_apply, Fin.sum_univ_two, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, sub_mul, mul_sub, add_mul, mul_add, neg_mul, mul_neg, hτl]
    rw [inv_smul_smul₀ hd1', hτh]
    linear_combination (norm := module) QD
  · ext k l'
    fin_cases k <;> fin_cases l' <;>
      simp [τn, Gb, Matrix.mul_apply, Fin.sum_univ_two, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, sub_mul, mul_sub, add_mul, mul_add, neg_mul, mul_neg]
    linear_combination (norm := module) (-d) • Y1' - hτμ
  · ext k l'
    fin_cases k <;> fin_cases l' <;>
      simp [Ln, Gb, Matrix.mul_apply, Fin.sum_univ_two, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, sub_mul, mul_sub, add_mul, mul_add, neg_mul, mul_neg]
    linear_combination (norm := module) Y3'

end Formalism.YangianSpanCharacter.P
end
end
