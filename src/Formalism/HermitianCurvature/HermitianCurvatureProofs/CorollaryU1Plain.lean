module

public import Formalism.HermitianCurvature.StatementU
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.CompactCurveEstimate
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.CompactRegionEstimate
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.DjCurve
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.DjPoly
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.GfPoly
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.GfWBOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.CoreStar
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.PolynomialBound
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.CoreStarOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.WeightBoundMultiplicative

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.MxLeOne

section

@[expose] public section

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace PI.UnitaryCorollaryDerivatives

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt.P.BetaSesquilinearity

theorem mx_le_one {k r : ℕ} {X : B.Mat k r} (h : B.unitLie k r X) : mx X ≤ 1 := by
  show ‖Matrix.of.symm X‖ ≤ 1
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro j
  exact h.2 i j

theorem dw_dj (h1 : DjCurve) (k j ρ : ℕ) : ∀ w : List (Bool × B.Mat k (j + ρ)),
    (∀ x ∈ w, inLieP k j ρ x.2 ∧ mx x.2 ≤ 1) →
    ∃ K : ℂ, ‖K‖ ≤ (j : ℝ) ^ w.length ∧ ∀ g, Dw w (DjU k j ρ) g = K * DjU k j ρ g := by
  intro w
  induction w with
  | nil => intro _; exact ⟨1, by simp, fun g => by simp [Dw]⟩
  | cons x w ih =>
    intro hw
    obtain ⟨K, hK, hD⟩ := ih fun y hy => hw y (by simp [hy])
    obtain ⟨hxP, hxm⟩ := hw x (by simp)
    obtain ⟨c₁, c₂, hc₁, hc₂, hcur⟩ := h1 k j ρ x.2 hxP
    have hderiv : ∀ (c D : ℂ), HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * c) * D) (c * D) 0 := by
      intro c D
      have h0 : HasDerivAt (fun t : ℝ => (t : ℂ) * c) (1 * c) 0 :=
        (hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const c
      have := (h0.cexp).mul_const D
      simpa using this
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    obtain ⟨b, X⟩ := x
    cases b
    · refine ⟨c₁ * K, ?_, fun g => ?_⟩
      · rw [norm_mul, List.length_cons, pow_succ']
        exact mul_le_mul (hc₁.trans (mul_le_of_le_one_right hj hxm)) hK (norm_nonneg _) hj
      · have e : Dw ((false, X) :: w) (DjU k j ρ) = Dx (false, X) (fun g => K • DjU k j ρ g) := by
          show Dx (false, X) (Dw w (DjU k j ρ)) = _
          congr 1; funext g; rw [hD g, smul_eq_mul]
        rw [e, Dx_smul]
        show K • Dx (false, X) (DjU k j ρ) g = _
        rw [Dx_eq]
        have e2 : (fun t : ℝ => DjU k j ρ (crv (false, X) g t)) =
            fun t : ℝ => Complex.exp ((t : ℂ) * c₁) * DjU k j ρ g := by
          funext t; exact (hcur g t).1
        simp only [e2, (hderiv c₁ _).deriv, smul_eq_mul]
        ring
    · refine ⟨c₂ * K, ?_, fun g => ?_⟩
      · rw [norm_mul, List.length_cons, pow_succ']
        exact mul_le_mul (hc₂.trans (mul_le_of_le_one_right hj hxm)) hK (norm_nonneg _) hj
      · have e : Dw ((true, X) :: w) (DjU k j ρ) = Dx (true, X) (fun g => K • DjU k j ρ g) := by
          show Dx (true, X) (Dw w (DjU k j ρ)) = _
          congr 1; funext g; rw [hD g, smul_eq_mul]
        rw [e, Dx_smul]
        show K • Dx (true, X) (DjU k j ρ) g = _
        rw [Dx_eq]
        have e2 : (fun t : ℝ => DjU k j ρ (crv (true, X) g t)) =
            fun t : ℝ => Complex.exp ((t : ℂ) * c₂) * DjU k j ρ g := by
          funext t; exact (hcur g t).2
        simp only [e2, (hderiv c₂ _).deriv, smul_eq_mul]
        ring

theorem djWB_of (h1 : DjCurve) (h2 : PolyB) (h3 : DjPoly) (h4 : CompC) : DjWB := by
  intro k j ρ χ n hχ
  obtain ⟨hcD, hB⟩ := h2 k (j + ρ) j (DjU k j ρ) (h3 k j ρ)
  obtain ⟨CP, hCP⟩ := hB n
  refine ⟨hχ.1.comp hcD, ?_⟩
  obtain ⟨R, hR⟩ := (hχ.2.1 : IsCompact (tsupport χ)).isBounded.exists_norm_le
  refine h4 k (j + ρ) (DjU k j ρ) χ (costP k j ρ) n (|CP| + (max 1 (j : ℝ)) ^ n * |R|) hcD hχ.1 hχ.2.1 ?_
  intro u v hu hv hl hne g hg hgs
  have hg1 := gN_ge_one hg
  have hS0 : (0 : ℝ) ≤ ((((u ++ v).map (costP k j ρ)).sum : ℕ) : ℝ) := Nat.cast_nonneg _
  have hA : 0 ≤ |CP| := abs_nonneg _
  have hBn : 0 ≤ (max 1 (j : ℝ)) ^ n * |R| := by positivity
  by_cases hall : ∀ X ∈ u ++ v, inLieP k j ρ X
  ·
    have hw : ∀ x ∈ wL u ++ wR v, inLieP k j ρ x.2 ∧ mx x.2 ≤ 1 := by
      intro x hx
      simp only [wL, wR, List.mem_append, List.mem_map] at hx
      rcases hx with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
      · exact ⟨hall X (List.mem_append_left _ hX), mx_le_one (hu X hX)⟩
      · exact ⟨hall X (List.mem_append_right _ hX), mx_le_one (hv X hX)⟩
    obtain ⟨K, hK, hD⟩ := dw_dj h1 k j ρ _ hw
    rw [dLR_eq, hD g, norm_mul]
    have hlen : (wL u ++ wR v).length ≤ n := by rw [len_LR]; exact hl
    have hK' : ‖K‖ ≤ (max 1 (j : ℝ)) ^ n :=
      hK.trans ((pow_le_pow_left₀ (Nat.cast_nonneg _) (le_max_right _ _) _).trans
        (pow_le_pow_right₀ (le_max_left _ _) hlen))
    have hDR : ‖DjU k j ρ g‖ ≤ |R| := (hR _ hgs).trans (le_abs_self _)
    have h1' : 1 ≤ B.gN g ^ ((((u ++ v).map (costP k j ρ)).sum : ℕ) : ℝ) := Real.one_le_rpow hg1 hS0
    calc ‖K‖ * ‖DjU k j ρ g‖ ≤ (max 1 (j : ℝ)) ^ n * |R| :=
          mul_le_mul hK' hDR (norm_nonneg _) (by positivity)
      _ ≤ (|CP| + (max 1 (j : ℝ)) ^ n * |R|) * 1 := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left h1' (by positivity)
  · obtain ⟨X, hX, hXP⟩ : ∃ X ∈ u ++ v, ¬ inLieP k j ρ X := by
      by_contra hc; exact hall (fun X hX => by by_contra h; exact hc ⟨X, hX, h⟩)
    have hcX : costP k j ρ X = j := by simp [costP, hXP]
    have hjS : (j : ℝ) ≤ ((((u ++ v).map (costP k j ρ)).sum : ℕ) : ℝ) := by
      have := List.le_sum_of_mem (List.mem_map_of_mem (f := costP k j ρ) hX)
      rw [hcX] at this; exact_mod_cast this
    have hb := hCP u v hu hv hl g hg
    simp only [List.map_const', List.sum_replicate, smul_eq_mul, mul_zero, Nat.cast_zero, add_zero] at hb
    calc ‖B.dLR u v (DjU k j ρ) g‖ ≤ CP * B.gN g ^ (j : ℝ) := hb
      _ ≤ |CP| * B.gN g ^ ((((u ++ v).map (costP k j ρ)).sum : ℕ) : ℝ) :=
          mul_le_mul (le_abs_self _) (Real.rpow_le_rpow_of_exponent_le hg1 hjS) (by positivity) hA
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)

end PI.UnitaryCorollaryDerivatives
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.StarEstimateUnitary

section

@[expose] public section

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace PI.UnitaryCorollaryDerivatives

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem star_estimate_unitary : CoreStar :=
  coreStar_of polynomial_bound determinant_derivative_polynomial determinant_curve_derivative

end PI.UnitaryCorollaryDerivatives
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.UnitaryCorollaryOfEstimates

section

@[expose] public section

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace PI.UnitaryCorollaryDerivatives

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem unitary_corollary_of_estimates (hC : CoreStar) (hD : DjWB) (hG : GfWB) (hM : WBmul) :
    Formalism.FourierDecayAlt.U.StarBoundOfCutoffOperator ∧ Formalism.FourierDecayAlt.U.StarBoundOfTwoCutoffOperator := by
  constructor
  · intro k j ρ Wp Wq _ _ _ _ _ o κ Θ χ hΘ hχ Q mm₀ A₀ hQ
    obtain ⟨hcd, Cφ, hWB⟩ := hD k j ρ χ (Q + o) hχ
    obtain ⟨C, hCf⟩ := hC k j ρ Wp Wq o κ 0 Θ χ (fun g => χ (DjU k j ρ g)) hΘ hχ Q mm₀ A₀ hQ hcd
      (fun g hg => image_eq_zero_of_notMem_tsupport hg) ⟨Cφ, by simpa using hWB⟩
    refine ⟨C, fun f c hf => ?_⟩
    have := hCf f c hf
    simp only [Nat.cast_zero, zero_mul, sub_zero] at this
    exact this
  · intro k j ρ Wp Wq _ _ _ _ _ z z' o κ Θ χ χε ε hΘ hχ hε Q mm₀ A₀ hQ
    obtain ⟨hcd, C1, h1⟩ := hD k j ρ χ (Q + o) hχ
    obtain ⟨hcg, C2, h2⟩ := hG k (j + ρ) z z' χε ε (Q + o) hε
    obtain ⟨C3, h3⟩ := hM k (j + ρ) _ _ _ _ (Q + o) C1 C2 0 0 hcd hcg h1 h2
    rw [zero_add] at h3
    obtain ⟨C, hCf⟩ := hC k j ρ Wp Wq o κ (2 * (j + ρ + 1)) Θ χ
      (fun g => χ (DjU k j ρ g) * ((χε (Gf k (j + ρ) z z' g) : ℝ) : ℂ)) hΘ hχ Q mm₀ A₀ hQ (hcd.mul hcg)
      (fun g hg => by simp [image_eq_zero_of_notMem_tsupport hg]) ⟨C3, h3⟩
    refine ⟨C, fun f c hf => ?_⟩
    have := hCf f c hf
    convert this using 2
    · rfl
    · push_cast; ring

end PI.UnitaryCorollaryDerivatives
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.UnitaryCorollaryBothForms

section

@[expose] public section

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace PI.UnitaryCorollaryDerivatives

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem unitary_corollary_both_forms : Formalism.FourierDecayAlt.U.StarBoundOfCutoffOperator ∧ Formalism.FourierDecayAlt.U.StarBoundOfTwoCutoffOperator :=
  unitary_corollary_of_estimates star_estimate_unitary (djWB_of determinant_curve_derivative polynomial_bound determinant_derivative_polynomial compact_curve_estimate)
    (gfWB_of generating_function_polynomial polynomial_bound compact_region_estimate) weight_bound_multiplicative

end PI.UnitaryCorollaryDerivatives
end
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CutoffPlainAndSmoothed

section

@[expose] public section

theorem cutoff_plain_and_smoothed : Formalism.FourierDecayAlt.U.StarBoundOfCutoffOperator ∧ Formalism.FourierDecayAlt.U.StarBoundOfTwoCutoffOperator := PI.UnitaryCorollaryDerivatives.unitary_corollary_both_forms
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CorollaryU1Plain

section

@[expose] public section

theorem Formalism.FourierDecayAlt.P.corollary_u1_truncated_alt : Formalism.FourierDecayAlt.U.StarBoundOfTwoCutoffOperator :=
  cutoff_plain_and_smoothed.2
end
end
