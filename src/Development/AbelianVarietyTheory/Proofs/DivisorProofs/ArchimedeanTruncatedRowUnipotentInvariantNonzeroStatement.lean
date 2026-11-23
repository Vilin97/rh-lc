module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OnMatInfOfIsUnit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableToGLEntry
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentLowerRowsLeviSetClosedSubgroupStatement
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
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowCutUnipBMulLevSet

section

@[expose] public section

open MeasureTheory GlobalTheory.JSW
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW

theorem truncatedRow_unipotent_mul_and_ne_zero : ∀ (n : ℕ) (ρ : Fin n), ∀ g ∈ levSet n (ρ + 1),
    (∀ u ∈ GlobalTheory.SmGL.unipB ℂ (Fin n), rowCut ρ ((u * g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
      rowCut ρ (g : Matrix (Fin n) (Fin n) ℂ)) ∧
    ∃ j, j ≤ ρ ∧ rowCut ρ (g : Matrix (Fin n) (Fin n) ℂ) j ≠ 0 := by
  intro n ρ g hg
  constructor
  · intro u hu
    obtain ⟨hu0, hu1⟩ := (GlobalTheory.SmGL.mem_unipB ℂ).1 hu
    funext j
    unfold rowCut
    split_ifs with hj
    · rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single ρ]
      · rw [hu1, one_mul]
      · intro k _ hk
        rcases lt_or_gt_of_ne hk with h | h
        · rw [hu0 ρ k h, zero_mul]
        · have h' := Fin.lt_def.1 h
          rw [(hg k (by omega)).1 j (lt_of_le_of_lt hj h), mul_zero]
      · simp
    · rfl
  · by_contra hne
    push_neg at hne
    have hinv := (GlobalTheory.T.unipotentLowerRowsLeviSet_closed_subgroup n (ρ + 1)).2.1 g hg
    have h1 : ((g * g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ρ ρ = 1 := by simp
    rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_zero] at h1
    · exact zero_ne_one h1
    · intro k _
      by_cases hk : k ≤ ρ
      · have := hne k hk
        simp only [rowCut, hk, if_true] at this
        rw [this, zero_mul]
      · push_neg at hk
        have h' := Fin.lt_def.1 hk
        rw [(hinv k (by omega)).1 ρ hk, mul_zero]

end GlobalTheory.JSW
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanTruncatedRowUnipotentInvariantNonzero

section

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf

theorem rowCutInf_unipB_mul_levSetInf : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (ρ : Fin n),
    ∀ g ∈ levSetInf E n (ρ + 1),
    (∀ u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n), rowCutInf ρ ((u * g : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) =
      rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E))) ∧
    ∀ w, ∃ j, j ≤ ρ ∧ rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E)) j w ≠ 0 := by
  intro E _ _ n ρ g hg
  have hw : ∀ w, compGL w g ∈ levSet n (ρ + 1) := hg
  have hc : ∀ w (x : GL (Fin n) (Cinf E)) j,
      rowCut ρ ((compGL w x : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) j =
        rowCutInf ρ (x : Matrix (Fin n) (Fin n) (Cinf E)) j w := by
    intro w x j
    unfold rowCut rowCutInf
    split_ifs <;> rfl
  constructor
  · intro u hu
    obtain ⟨hu0, hu1⟩ := (GlobalTheory.SmGL.mem_unipB (Cinf E)).1 hu
    have hmem : ∀ w, compGL w u ∈ GlobalTheory.SmGL.unipB ℂ (Fin n) := by
      intro w
      refine (GlobalTheory.SmGL.mem_unipB ℂ).2 ⟨fun i j h => ?_, fun i => ?_⟩
      · rw [compGL_apply, hu0 i j h]; rfl
      · rw [compGL_apply, hu1 i]; rfl
    funext j w
    rw [← hc, ← hc, map_mul]
    exact congrFun ((truncatedRow_unipotent_mul_and_ne_zero n ρ _ (hw w)).1 _ (hmem w)) j
  · intro w
    obtain ⟨j, hj, hne⟩ := (truncatedRow_unipotent_mul_and_ne_zero n ρ _ (hw w)).2
    exact ⟨j, hj, by rwa [← hc]⟩

end GlobalTheory.JSW.MirCinf
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanTruncatedRowUnipotentInvariantNonzeroStatement

section

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

theorem _root_.GlobalTheory.T.archimedeanTruncatedRow_unipotent_invariant_nonzero : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (ρ : Fin n), ∀ g ∈ levSetInf E n (ρ + 1), (∀ u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n), rowCutInf ρ ((u * g : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) = rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E))) ∧ ∀ w, ∃ j, j ≤ ρ ∧ rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E)) j w ≠ 0 := by
  first | exact @GlobalTheory.JSW.MirCinf.rowCutInf_unipB_mul_levSetInf | exact GlobalTheory.JSW.MirCinf.rowCutInf_unipB_mul_levSetInf | (intros; apply GlobalTheory.JSW.MirCinf.rowCutInf_unipB_mul_levSetInf; all_goals assumption)
end
end
