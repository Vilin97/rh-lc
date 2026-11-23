module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CharConj
public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.NumberField.Basic
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
import Mathlib.Geometry.Manifold.StructureGroupoid
import Mathlib.Algebra.Order.Star.Real

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AgreeOfAdjoin

section

@[expose] public section

open scoped IntermediateField TensorProduct Matrix Pointwise NumberField Topology ContDiff NNReal ENNReal Polynomial DirectSum BigOperators InnerProductSpace Manifold

theorem UpperTheory.Reformulated.B.Qk58.agree_of_adjoin :
    ∀ {E : Type} [inst : Field E]
    [inst_1 : NumberField E] (φ ψ : E →+* ℂ) {a b : E},
    (φ : E → ℂ) a = (ψ : E → ℂ) a → b ∈ ℚ⟮a⟯ → (φ : E → ℂ) b = (ψ : E → ℂ) b := by
  intro E _ _ φ ψ a b ha hb
  induction hb using IntermediateField.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff.mp hx]
    exact ha
  | algebraMap q => simp
  | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  | inv x _ hx => rw [map_inv₀, map_inv₀, hx]
  | mul x y _ _ hx hy => rw [map_mul, map_mul, hx, hy]
end
end

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjEqNegOfSq

section

@[expose] public section

theorem UpperTheory.Reformulated.B.Qk60.conj_eq_neg_of_sq :
    ∀ {z : ℂ} {d : ℕ},
    (0 : ℕ) < d → z ^ (2 : ℕ) = -(↑d : ℂ) → (starRingEnd ℂ : ℂ → ℂ) z = -z := by
  intro z d hd h
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hre : z.re * z.re - z.im * z.im = -(d : ℝ) := by
    simpa [pow_two] using congrArg Complex.re h
  have him : z.re * z.im + z.im * z.re = 0 := by
    simpa [pow_two] using congrArg Complex.im h
  have h0 : z.re = 0 := by
    have hmul : z.re * z.im = 0 := by linarith
    rcases mul_eq_zero.mp hmul with h1 | h1
    · exact h1
    · rw [h1] at hre
      nlinarith [mul_self_nonneg z.re]
  apply Complex.ext
  · simp [h0]
  · simp
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PEpsIff

section

@[expose] public section

noncomputable section

open NumberField

namespace UpperTheory.Gal.CertificateRingHomMap

private theorem agree_of_adjoin {E : Type} [Field E] [NumberField E] (φ ψ : E →+* ℂ) {a b : E}
    (h : φ a = ψ a) (hb : b ∈ IntermediateField.adjoin ℚ {a}) : φ b = ψ b :=
  _root_.UpperTheory.Reformulated.B.Qk58.agree_of_adjoin φ ψ h hb

private theorem conj_eq_neg_of_sq {z : ℂ} {d : ℕ} (hd : 0 < d) (hz : z ^ 2 = -(d : ℂ)) :
    (starRingEnd ℂ) z = -z :=
  _root_.UpperTheory.Reformulated.B.Qk60.conj_eq_neg_of_sq hd hz

theorem pEpsIff_of : EpsIff := by
  intro E _ _ _ d x ω hd hx hω hx' τ φ
  have hτ : (τ x) ^ 2 = -(d : ℂ) := by
    rw [← map_pow, hx, map_neg, map_natCast]
  have hc : ComplexEmbedding.conjugate τ x = -τ x := by
    rw [ComplexEmbedding.conjugate_coe_eq]
    exact conj_eq_neg_of_sq hd hτ
  constructor
  · intro h
    have h' : φ ω = ComplexEmbedding.conjugate τ ω := by
      rw [ComplexEmbedding.conjugate_coe_eq]
      exact h
    rw [agree_of_adjoin φ _ h' hx', hc]
  · intro h
    have h' : φ x = ComplexEmbedding.conjugate τ x := by rw [h, hc]
    rw [agree_of_adjoin φ _ h' hω, ComplexEmbedding.conjugate_coe_eq]

end UpperTheory.Gal.CertificateRingHomMap

end
end
end
