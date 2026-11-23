module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QAllQConjOfDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QExpansionCoeffsInSubringRingClosedStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularDiscriminantDivQIntegerQExpansionsStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModBasic

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionAllCoeffsCompUpperTriangular

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNQ

theorem qAll_affine : ∀ (E : Subring ℂ) (N a d : ℕ) (b : ℤ) (f : ℍ → ℂ), (∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ E) → 0 < N → 0 < a → 0 < d → QAll (· ∈ E) N f → QAll (· ∈ E) (N * d) fun τ => up f (((a : ℂ) * τ + b) / d) := by
  intro E N a d b f hE hN ha hd hf
  obtain ⟨c, hc, hcE⟩ := hf
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  let e : ℕ → ℂ := fun k => Complex.exp (2 * Real.pi * Complex.I * (((k : ℚ) * b / (N * d) : ℚ) : ℂ))
  refine ⟨fun m => if a ∣ m then c (m / a) * e (m / a) else 0, ?_, ?_⟩
  · intro τ
    have hz : 0 < (((a : ℂ) * τ + b) / d).im := by
      have : (((a : ℂ) * τ + b) / d).im = a * τ.im / d := by
        simp [Complex.div_ofReal_im]
      rw [this]; have := τ.im_pos; positivity
    have hτ := hc (UpperHalfPlane.ofComplex (((a : ℂ) * τ + b) / d))
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz] at hτ
    have hinj : Function.Injective (fun k : ℕ => a * k) := fun x y h => by
      simpa [ha.ne'] using h
    rw [← hinj.hasSum_iff]
    · show HasSum (fun k => _) (f _)
      convert hτ using 1
      funext k
      simp only [Function.comp_apply, dvd_mul_right, if_true, Nat.mul_div_cancel_left _ ha, e]
      rw [mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      field_simp
      ring
      exact congrArg f (UpperHalfPlane.ofComplex_apply_of_im_pos hz)
    · intro m hm
      have : ¬ a ∣ m := by
        rintro ⟨k, rfl⟩; exact hm ⟨k, rfl⟩
      simp [this]
  · intro m
    by_cases h : a ∣ m
    · simp only [h, if_true]
      exact E.mul_mem (hcE _) (hE _)
    · simp only [h, if_false]; exact E.zero_mem

end GlobalTheory.FNQ
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionAllCoeffsCompUpperTriangularStatement

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.qExpansionAllCoeffs_comp_upper_triangular : ∀ (E : Subring ℂ) (N a d : ℕ) (b : ℤ) (f : ℍ → ℂ), (∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ E) → 0 < N → 0 < a → 0 < d → QAll (· ∈ E) N f → QAll (· ∈ E) (N * d) fun τ => up f (((a : ℂ) * τ + b) / d) := by
  first | exact @GlobalTheory.FNQ.qAll_affine | exact GlobalTheory.FNQ.qAll_affine | (intros; apply GlobalTheory.FNQ.qAll_affine <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionAllCoeffsDeltaPowAffineSubst

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNPole

theorem qAll_monomial (E : Subring ℂ) (M k : ℕ) :
    QAll (· ∈ E) M fun τ => Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * τ / M) := by
  refine ⟨fun n => if n = k then 1 else 0, fun τ => ?_, fun n => ?_⟩
  · have := hasSum_single (f := fun n : ℕ => (if n = k then (1 : ℂ) else 0) *
      Complex.exp (2 * Real.pi * Complex.I * n * τ / M)) k (fun n hn => by simp [hn])
    simpa using this
  · dsimp only; split_ifs
    · exact E.one_mem
    · exact E.zero_mem

theorem qAll_of_int (E : Subring ℂ) {f : ℍ → ℂ} (h : ∃ c : ℕ → ℤ, c 0 = 1 ∧ HasQ 1 f fun n => (c n : ℂ)) :
    QAll (· ∈ E) 1 f := by
  obtain ⟨c, -, hc⟩ := h
  exact ⟨_, hc, fun n => intCast_mem E (c n)⟩

theorem qAll_congr {p : ℂ → Prop} {N : ℕ} {f g : ℍ → ℂ} (hf : QAll p N f) (h : ∀ τ, f τ = g τ) :
    QAll p N g := by
  have : f = g := funext h
  exact this ▸ hf

theorem qAll_pole_affine : ∀ (E : Subring ℂ) (N w a d : ℕ) (b : ℤ) (φ : ℍ → ℂ),
    (∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ E) → 0 < N → 0 < a → 0 < d →
    QAll (· ∈ E) N (fun τ => DD τ ^ w * φ τ) →
    QAll (· ∈ E) (N * (a * d)) fun τ => DD τ ^ (w * (a * d)) * up φ (((a : ℂ) * τ + b) / d) := by
  intro E N w a d b φ hE hN ha hd hφ
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  have hM : 0 < N * (a * (d' + 1)) := by positivity
  have RC := GlobalTheory.T.qExpansionCoeffsInSubring_ring_closed E (N * (a * (d' + 1))) hM
  obtain ⟨hDq, hqD⟩ := GlobalTheory.T.modularDiscriminant_div_q_integer_qExpansions
  have h1 := QAll.of_dvd hM ⟨a, by ring⟩ E.zero_mem
    (GlobalTheory.T.qExpansionAllCoeffs_comp_upper_triangular E N a (d' + 1) b _ hE hN ha (by omega) hφ)
  have h2 := QAll.of_dvd hM ⟨N * a, by ring⟩ E.zero_mem
    (GlobalTheory.T.qExpansionAllCoeffs_comp_upper_triangular E 1 a (d' + 1) b _ hE one_pos ha (by omega) (qAll_of_int E hqD))
  have h3 := QAll.of_dvd hM (one_dvd _) E.zero_mem (qAll_of_int E hDq)
  have h2w := RC.2.2.2.2.1 _ w h2
  have h3w := RC.2.2.2.2.1 _ (w * (a * (d' + 1))) h3
  have h4 := RC.1 _ (hE (-((w : ℚ) * b) / (d' + 1)))
  have h5 := qAll_monomial E (N * (a * (d' + 1))) (N * w * a * a * (d' * (d' + 2)))
  have hP := RC.2.2.2.1 _ _ (RC.2.2.2.1 _ _ (RC.2.2.2.1 _ _ (RC.2.2.2.1 _ _ h1 h2w) h3w) h4) h5
  refine qAll_congr hP fun τ => ?_
  simp only [up]
  set U := UpperHalfPlane.ofComplex (((a : ℂ) * τ + b) / ((d' + 1 : ℕ) : ℂ)) with hUdef
  have him : 0 < (((a : ℂ) * τ + b) / ((d' + 1 : ℕ) : ℂ)).im := by
    have : (((a : ℂ) * τ + b) / ((d' + 1 : ℕ) : ℂ)).im = a * τ.im / (d' + 1) := by
      rw [Complex.div_natCast_im]; simp
    rw [this]; have := τ.im_pos; positivity
  have hU : (U : ℂ) = ((a : ℂ) * τ + b) / ((d' + 1 : ℕ) : ℂ) := by
    rw [hUdef, UpperHalfPlane.ofComplex_apply_of_im_pos him]
  have key : Complex.exp (2 * Real.pi * Complex.I * (U : ℂ)) ^ w *
      Complex.exp (2 * Real.pi * Complex.I * (((-((w : ℚ) * b) / (d' + 1) : ℚ)) : ℂ)) *
      Complex.exp (2 * Real.pi * Complex.I * ((N * w * a * a * (d' * (d' + 2)) : ℕ) : ℂ) * τ /
        ((N * (a * (d' + 1)) : ℕ) : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * (τ : ℂ)) ^ (w * (a * (d' + 1))) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_add, hU]
    congr 1
    have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    have hd' : (d' : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero d')
    push_cast
    field_simp
    ring
  have hDU := ReciprocityTheory.ChartRestriction.L1.DD_ne_zero U
  have hDτ := ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ
  have e1 := Complex.exp_ne_zero (2 * Real.pi * Complex.I * (U : ℂ))
  have e2 := Complex.exp_ne_zero (2 * Real.pi * Complex.I * (τ : ℂ))
  have e3 := Complex.exp_ne_zero (2 * Real.pi * Complex.I * (((-((w : ℚ) * b) / (d' + 1) : ℚ)) : ℂ))
  have e4 := Complex.exp_ne_zero (2 * Real.pi * Complex.I * ((N * w * a * a * (d' * (d' + 2)) : ℕ) : ℂ) * τ /
        ((N * (a * (d' + 1)) : ℕ) : ℂ))
  rw [div_pow, div_pow, ← key]
  field_simp

end GlobalTheory.FNPole
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionAllCoeffsDeltaPowAffineSubstStatement

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.qExpansionAllCoeffs_deltaPow_affineSubst : ∀ (E : Subring ℂ) (N w a d : ℕ) (b : ℤ) (φ : ℍ → ℂ), (∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ E) → 0 < N → 0 < a → 0 < d → QAll (· ∈ E) N (fun τ => DD τ ^ w * φ τ) → QAll (· ∈ E) (N * (a * d)) fun τ => DD τ ^ (w * (a * d)) * up φ (((a : ℂ) * τ + b) / d) := by
  first | exact @GlobalTheory.FNPole.qAll_pole_affine | exact GlobalTheory.FNPole.qAll_pole_affine | (intros; apply GlobalTheory.FNPole.qAll_pole_affine <;> assumption)
end
end
