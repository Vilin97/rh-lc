module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianHaarMeasure.Development
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianHaarMeasure.ElementaryGeneratorAdjoint
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianHaarMeasure.ElementaryGeneratorPreservesTest
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianHaarMeasure.SmoothLevZero
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianHaarMeasure.RepOnOfEq
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Formalism.FormalDegreeBessel.FinalG
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianHaarMeasure.RepresentsTransferOneOne

section

@[expose] public section

open Matrix Finset MeasureTheory
open scoped ContDiff

noncomputable section

namespace PI.QnHermHaar

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Gen

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {i : Fin (r + 1)} {μ : Measure (Mt k r)}

theorem repTm (H : Hyp k r z z' i μ) (w : ℂ) (a b : Fin (mdim k r i)) :
    RepOn (hI H) (Tm (EA H) w a b) (Top (EH k r) w (posL k r i a) (posL k r i b)) := by
  have h := repOn_add (hI H) (repOn_ite (hI H) (a = b) (repOn_algebraMap (hI H) w) (repOn_zero (hI H)))
    (repE H a b)
  unfold Tm
  refine repOn_of_eq h fun f => ?_
  funext g
  by_cases hab : a = b
  · subst hab; simp [Formalism.QuantumDeterminants.Top, EOp]
  · have : posL k r i a ≠ posL k r i b := fun h => hab (posL_inj h)
    simp [Formalism.QuantumDeterminants.Top, EOp, hab, this]

theorem repQminor (H : Hyp k r z z' i μ) {t : ℕ} (a b : Fin t → Fin (mdim k r i)) (w : ℂ) :
    RepOn (hI H) (qminor (EA H) a b w) (qminorOp (EH k r) (posL k r i ∘ a) (posL k r i ∘ b) w) := by
  unfold qminor
  exact repOn_sum (hI H) Finset.univ fun σ _ => repOn_mul (hI H) (repOn_intCast (hI H) _)
    (repOn_list (hI H) t _ _ fun k' => repTm H _ _ _)

theorem represents_transfer_zero_zero (H : Hyp k r z z' i μ) (Y : ℂ) :
    RepOn (hI H) (tA (EA H) (YA H) (YbA H) (xv k r z' i) (xbv k r z' i) (uC k r i Y) 0 0)
      (tL k r z z' i Y 0 0) :=
  repQminor H id id _

theorem represents_transfer_zero_one (H : Hyp k r z z' i μ) (Y : ℂ) :
    RepOn (hI H) (tA (EA H) (YA H) (YbA H) (xv k r z' i) (xbv k r z' i) (uC k r i Y) 0 1)
      (tL k r z z' i Y 0 1) := by
  have h := repOn_neg (hI H) (repOn_sum (hI H) (Finset.univ : Finset (Fin (mdim k r i))) fun a _ => repOn_sum (hI H) (Finset.univ : Finset (Fin (mdim k r i))) fun b _ =>
    repOn_smul (hI H) ((-1 : ℂ) ^ ((a : ℕ) + (b : ℕ)) * xv k r z' i b)
      (repOn_mul (hI H) (repYb H a) (repQminor H (skip1 a) (skip1 b) (uC k r i Y - 1))))
  refine repOn_of_eq h fun f => ?_
  funext g
  simp only [tL, chatL, MOp, Pi.neg_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  ring

theorem represents_transfer_one_zero (H : Hyp k r z z' i μ) (Y : ℂ) :
    RepOn (hI H) (tA (EA H) (YA H) (YbA H) (xv k r z' i) (xbv k r z' i) (uC k r i Y) 1 0)
      (tL k r z z' i Y 1 0) := by
  have h := repOn_neg (hI H) (repOn_sum (hI H) (Finset.univ : Finset (Fin (mdim k r i))) fun a _ => repOn_sum (hI H) (Finset.univ : Finset (Fin (mdim k r i))) fun b _ =>
    repOn_smul (hI H) ((-1 : ℂ) ^ ((a : ℕ) + (b : ℕ)) * xbv k r z' i a)
      (repOn_mul (hI H) (repY H b) (repQminor H (skip1 a) (skip1 b) (uC k r i Y))))
  refine repOn_of_eq h fun f => ?_
  funext g
  simp only [tL, chatL, MOp, Pi.neg_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  ring

theorem tA_11 {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (Y Yb : Fin m → A)
    (x xb : Fin m → ℂ) (u : ℂ) : tA E Y Yb x xb u 1 1 = -∑ i : Fin m, ∑ i' : Fin m, ∑ j : Fin m, ∑ j' : Fin m,
      if i < i' ∧ j < j' then
        ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ) + (j : ℕ) + (j' : ℕ))) •
          ((Yb i * algebraMap ℂ A (xb i') - Yb i' * algebraMap ℂ A (xb i)) *
            (Y j * algebraMap ℂ A (x j') - Y j' * algebraMap ℂ A (x j)) *
            qminor E (skip2 i i') (skip2 j j') (u - 1))
      else 0 := rfl

theorem represents_transfer_one_one (H : Hyp k r z z' i μ) (Y : ℂ) :
    RepOn (hI H) (tA (EA H) (YA H) (YbA H) (xv k r z' i) (xbv k r z' i) (uC k r i Y) 1 1)
      (tL k r z z' i Y 1 1) := by
  have h := repOn_neg (hI H) (repOn_sum (hI H) (Finset.univ : Finset (Fin (mdim k r i))) fun a _ => repOn_sum (hI H) (Finset.univ : Finset (Fin (mdim k r i))) fun a' _ =>
    repOn_sum (hI H) (Finset.univ : Finset (Fin (mdim k r i))) fun b _ => repOn_sum (hI H) (Finset.univ : Finset (Fin (mdim k r i))) fun b' _ =>
    repOn_ite (hI H) (a < a' ∧ b < b')
      (repOn_smul (hI H) ((-1 : ℂ) ^ ((a : ℕ) + (a' : ℕ) + (b : ℕ) + (b' : ℕ)))
        (repOn_mul (hI H)
          (repOn_mul (hI H)
            (repOn_sub (hI H) (repOn_mul (hI H) (repYb H a) (repOn_algebraMap (hI H) (xbv k r z' i a')))
              (repOn_mul (hI H) (repYb H a') (repOn_algebraMap (hI H) (xbv k r z' i a))))
            (repOn_sub (hI H) (repOn_mul (hI H) (repY H b) (repOn_algebraMap (hI H) (xv k r z' i b')))
              (repOn_mul (hI H) (repY H b') (repOn_algebraMap (hI H) (xv k r z' i b)))))
          (repQminor H (skip2 a a') (skip2 b b') (uC k r i Y - 1))))
      (repOn_zero (hI H)))
  rw [tA_11]
  refine repOn_of_eq h fun f => ?_
  funext g
  simp only [tL, chat2L, Pi.neg_apply, Finset.sum_apply]
  rw [neg_inj]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro a' _
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro b' _
  split_ifs
  · simp only [MOp, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  · rfl

theorem rep_tL (H : Hyp k r z z' i μ) (Y : ℂ) (p q : Fin 2) :
    RepOn (hI H) (tA (EA H) (YA H) (YbA H) (xv k r z' i) (xbv k r z' i) (uC k r i Y) p q)
      (tL k r z z' i Y p q) := by
  fin_cases p <;> fin_cases q
  · exact represents_transfer_zero_zero H Y
  · exact represents_transfer_zero_one H Y
  · exact represents_transfer_one_zero H Y
  · exact represents_transfer_one_one H Y

theorem uC_star (Y : ℂ) : star (uC k r i Y) = uC k r i (star Y) := by
  simp [uC]

theorem glue_holds_var : Glue := by
  intro hAlg hET hEA hMT hTI hYb hXb hHm hEP hGl hYL k r z z' i μ hμ hz hz' f₁ f₂ hs₁ hs₂ hc₁ hc₂ Y a b
  have H : Hyp k r z z' i μ := ⟨hμ, hz, hz', hET, hEA, hMT, hTI, hYb, hXb, hHm, hEP, hGl, hYL⟩
  have hstar := hAlg (A (hI H)) (mdim k r i) (EA H) (YA H) (YbA H) (Hm k r i) (xv k r z' i) (xbv k r z' i)
    (glRel_A H) (hHm k r i).1 (hHm k r i).2 (starE_A H) (yComm H) (ybComm H) (yybComm H) (eyComm H) (eybComm H)
    (ybStar H) (hXb k r z' i hz') (uC k r i Y) a b
  have hT := rep_tL H Y a b
  have hS : RepOn (hI H) (star (tA (EA H) (YA H) (YbA H) (xv k r z' i) (xbv k r z' i) (uC k r i Y) a b))
      (tL k r z z' i (star Y) b a) := by
    rw [hstar, uC_star]
    exact rep_tL H (star Y) b a
  exact pr_of_repOn (hI H) hT hS (mem_testSub.2 ⟨hs₁, hc₁⟩) (mem_testSub.2 ⟨hs₂, hc₂⟩)

end PI.QnHermHaar
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianHaarMeasure.RestrictedGramHermitianInvolution

section

@[expose] public section

open Matrix Finset

noncomputable section

namespace PI.QnHermHaar

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

theorem rel_posL_val (k r : ℕ) (i : Fin (r + 1)) (l : Fin (mdim k r i)) :
    (posL k r i l).val = l.val + i.val := rfl

theorem rel_posL_injective (k r : ℕ) (i : Fin (r + 1)) : Function.Injective (posL k r i) := by
  intro a b h
  apply Fin.ext
  have h' := congrArg Fin.val h
  rw [rel_posL_val, rel_posL_val] at h'
  omega

theorem rel_posL_bound (k r : ℕ) (i : Fin (r + 1)) (l : Fin (mdim k r i)) :
    i.val ≤ (posL k r i l).val ∧ (posL k r i l).val + i.val ≤ 2 * r + k := by
  rw [rel_posL_val]
  have hl : l.val < 2 * (r - i.val) + k + 1 := l.isLt
  have hi := i.isLt
  omega

theorem rel_hpk_off_left (k r : ℕ) (p q : Fin (2 * r + k + 1)) (j : ℕ)
    (hp : j ≤ p.val ∧ p.val + j ≤ 2 * r + k) (hq : q.val < j ∨ 2 * r + k < q.val + j) :
    Hpk k r q p = 0 := by
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem rel_hpk_off_right (k r : ℕ) (p q : Fin (2 * r + k + 1)) (j : ℕ)
    (hp : j ≤ p.val ∧ p.val + j ≤ 2 * r + k) (hq : q.val < j ∨ 2 * r + k < q.val + j) :
    Hpk k r p q = 0 := by
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem rel_sum_posL (k r : ℕ) (i : Fin (r + 1)) (F : Fin (2 * r + k + 1) → ℂ)
    (hF : ∀ a : Fin (2 * r + k + 1), (a.val < i.val ∨ 2 * r + k < a.val + i.val) → F a = 0) :
    ∑ a, F a = ∑ l : Fin (mdim k r i), F (posL k r i l) := by
  rw [← Finset.sum_image (s := Finset.univ) (g := posL k r i)
    (fun x _ y _ h => rel_posL_injective k r i h)]
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro a _ ha
  apply hF
  by_contra hc
  push_neg at hc
  apply ha
  have hi := i.isLt
  refine Finset.mem_image.2 ⟨⟨a.val - i.val, ?_⟩, Finset.mem_univ _, ?_⟩
  · show a.val - i.val < 2 * (r - i.val) + k + 1
    omega
  · apply Fin.ext
    show a.val - i.val + i.val = a.val
    omega

theorem rel_herm_unitary {n : ℕ} (H g : Matrix (Fin n) (Fin n) ℂ) (hU : gᴴ * H * g = H) (v w : Fin n → ℂ) :
    herm H (g *ᵥ v) (g *ᵥ w) = herm H v w := by
  unfold herm
  rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc, hU]

theorem rel_herm_bvec {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (p : Fin n) (y : Fin n → ℂ) :
    herm H (bvec p) y = ∑ a, star (y a) * H a p := by
  unfold herm bvec
  simp [dotProduct, Matrix.mulVec, Pi.single_apply]

theorem conjugate_y_relation : YbRel := by
  intro k r z i _ g hg c
  have hU : gᴴ * Hpk k r * g = Hpk k r := hg.1
  obtain ⟨_, hI, -⟩ := hpkFacts k r
  have hleft : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    rw [Matrix.mul_assoc (Hpk k r * gᴴ), Matrix.mul_assoc (Hpk k r), ← Matrix.mul_assoc gᴴ, hU, hI]
  have hdet : IsUnit g.det := Matrix.isUnit_det_of_left_inverse hleft
  have hf : fvec k r z i = g *ᵥ (g⁻¹ *ᵥ fvec k r z i) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have key : herm (Hpk k r) (g *ᵥ bvec (posL k r i c)) (fvec k r z i) =
      herm (Hpk k r) (bvec (posL k r i c)) (g⁻¹ *ᵥ fvec k r z i) := by
    conv_lhs => rw [hf]
    exact rel_herm_unitary _ _ hU _ _
  have hsum := rel_sum_posL k r i
    (fun a => star ((g⁻¹ *ᵥ fvec k r z i) a) * Hpk k r a (posL k r i c)) (by
      intro a ha
      show star ((g⁻¹ *ᵥ fvec k r z i) a) * Hpk k r a (posL k r i c) = 0
      rw [rel_hpk_off_left k r (posL k r i c) a i.val (rel_posL_bound k r i c) ha, mul_zero])
  show herm (Hpk k r) (g *ᵥ bvec (posL k r i c)) (fvec k r z i) =
    ∑ l, Hm k r i l c * star ((g⁻¹ *ᵥ fvec k r z i) (posL k r i l))
  rw [key, rel_herm_bvec]
  refine hsum.trans (Finset.sum_congr rfl fun l _ => ?_)
  show star ((g⁻¹ *ᵥ fvec k r z i) (posL k r i l)) * Hpk k r (posL k r i l) (posL k r i c) =
    Hm k r i l c * star ((g⁻¹ *ᵥ fvec k r z i) (posL k r i l))
  rw [mul_comm]
  rfl

theorem conjugate_x_relation : XbRel := by
  intro k r z' i _ c
  have hsum := rel_sum_posL k r i
    (fun a => star (fvec k r z' i a) * Hpk k r a (posL k r i c)) (by
      intro a ha
      show star (fvec k r z' i a) * Hpk k r a (posL k r i c) = 0
      rw [rel_hpk_off_left k r (posL k r i c) a i.val (rel_posL_bound k r i c) ha, mul_zero])
  show herm (Hpk k r) (bvec (posL k r i c)) (fvec k r z' i) =
    ∑ l, Hm k r i l c * star (fvec k r z' i (posL k r i l))
  rw [rel_herm_bvec]
  refine hsum.trans (Finset.sum_congr rfl fun l _ => ?_)
  show star (fvec k r z' i (posL k r i l)) * Hpk k r (posL k r i l) (posL k r i c) =
    Hm k r i l c * star (fvec k r z' i (posL k r i l))
  rw [mul_comm]
  rfl

theorem restricted_gram_hermitian_involution : HmFacts := by
  intro k r i
  obtain ⟨hH, hI, -⟩ := hpkFacts k r
  constructor
  · ext a b
    show star (Hpk k r (posL k r i b) (posL k r i a)) = Hpk k r (posL k r i a) (posL k r i b)
    rw [← Matrix.conjTranspose_apply (Hpk k r), hH]
  · ext a b
    have h1 : (Hm k r i * Hm k r i) a b = (Hpk k r * Hpk k r) (posL k r i a) (posL k r i b) := by
      rw [Matrix.mul_apply, Matrix.mul_apply]
      symm
      refine rel_sum_posL k r i
        (fun q => Hpk k r (posL k r i a) q * Hpk k r q (posL k r i b)) ?_
      intro q hq
      show Hpk k r (posL k r i a) q * Hpk k r q (posL k r i b) = 0
      rw [rel_hpk_off_right k r (posL k r i a) q i.val (rel_posL_bound k r i a) hq, zero_mul]
    rw [h1, hI, Matrix.one_apply, Matrix.one_apply]
    by_cases h : a = b
    · subst h
      simp
    · rw [if_neg h, if_neg (fun e => h (rel_posL_injective k r i e))]

end PI.QnHermHaar
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianHaarMeasure.Assemble

section

@[expose] public section

namespace PI.QnHermHaar

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

theorem qnHermHaar_of_alg (hA : HermAlgFrom) :
    RdSkew → StarMinor → ContractionsCovariant → MoveVec → MoveCov → YLeibniz → EabGlLev → EabPres → HermHaar :=
  qnHermHaar_of hA elementary_generator_adjoint elementary_generator_preserves_test multiplication_preserves_test test_function_pairing_integral conjugate_y_relation conjugate_x_relation restricted_gram_hermitian_involution glue_holds_var

end PI.QnHermHaar
end
end
