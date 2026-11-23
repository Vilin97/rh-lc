module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinValueLinearChangeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumRealEmbeddingsEqTraceTotallyRealStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinValueLinearChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumRealEmbeddingsEqTraceTotallyRealStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumHilbertEisensteinShiftedLatticeFourier

section

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

noncomputable def shearSub {F : Type} [Field F] (x : F) : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F) where
  toFun v := ![v 0, v 1 - v 0 * x]
  invFun v := ![v 0, v 1 + v 0 * x]
  map_add' v w := by
    ext i; fin_cases i
    · simp
    · simp; ring
  map_smul' c v := by
    ext i; fin_cases i
    · simp
    · simp; ring
  left_inv v := by ext i; fin_cases i <;> simp
  right_inv v := by ext i; fin_cases i <;> simp

theorem shearSub_zero {F : Type} [Field F] (x : F) (v : Fin 2 → F) : shearSub x v 0 = v 0 := rfl

theorem shearSub_one {F : Type} [Field F] (x : F) (v : Fin 2 → F) : shearSub x v 1 = v 1 - v 0 * x := rfl

theorem hasSum_split_shift : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (w : Emb F → ℂ), Even k → IsCoef k 𝔞 𝔟 a₀ a → w ∈ upperHalf F → HasSum (fun ξ : F ↦ a ξ * eTr (ξ * x) * qPow ξ w) ((cK F k : ℂ) * gval k (split 𝔞 𝔟 x) w 1 / ((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F * (omegaFactor 𝔞 : ℂ)) ^ k) := by
  intro F _ _ _ k 𝔞 𝔟 a₀ a x w hk hc hw
  have hw' : (fun i : Emb F ↦ w i + ((i x : ℝ) : ℂ)) ∈ upperHalf F := by
    intro i
    simpa using hw i
  have hg : gval k (split 𝔞 𝔟 x) w 1 = gval k (split 𝔞 𝔟 0) (fun i : Emb F ↦ w i + ((i x : ℝ) : ℂ)) 1 := by
    have := GlobalTheory.T.hilbertEisensteinValue_linear_change F k (split 𝔞 𝔟 x) (split 𝔞 𝔟 0) (shearSub x) w 1
      (fun i : Emb F ↦ w i + ((i x : ℝ) : ℂ)) 1 1 hk (fun v ↦ by
        change (_ ∧ _) ↔ (_ ∧ _)
        rw [shearSub_zero, shearSub_one, mul_zero, sub_zero]) (fun i ↦ by simp) (fun v i ↦ by
        simp only [coord, shearSub_zero, shearSub_one, Pi.one_apply, map_sub, map_mul]
        push_cast; ring)
    simpa using this
  have h := hc.2.2.2 _ hw'
  rw [hg]
  convert h using 2 with ξ
  rw [mul_assoc]
  congr 1
  unfold eTr qPow
  rw [← Complex.exp_add, ← GlobalTheory.T.sum_realEmbeddings_eq_trace_totallyReal F (ξ * x), ← mul_add, ← Finset.sum_add_distrib]
  congr 2
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_mul]; push_cast; ring

end GlobalTheory.HilbFam
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumHilbertEisensteinShiftedLatticeFourierStatement

section

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

theorem _root_.GlobalTheory.T.hasSum_hilbertEisenstein_shiftedLattice_fourier : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (w : Emb F → ℂ), Even k → IsCoef k 𝔞 𝔟 a₀ a → w ∈ upperHalf F → HasSum (fun ξ : F ↦ a ξ * eTr (ξ * x) * qPow ξ w) ((cK F k : ℂ) * gval k (split 𝔞 𝔟 x) w 1 / ((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F * (omegaFactor 𝔞 : ℂ)) ^ k) := by
  first | exact @GlobalTheory.HilbFam.hasSum_split_shift | exact GlobalTheory.HilbFam.hasSum_split_shift | (intros; apply GlobalTheory.HilbFam.hasSum_split_shift <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumHilbertEisensteinMovedPoint

section

@[expose] public section

set_option autoImplicit false

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem hasSum_movedPoint : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (τ c t : ℂ) (z : Emb F → ℂ), Even k → IsCoef k 𝔞 𝔟 a₀ a → (∀ i, 1 + z i * c ≠ 0 ∧ 0 < (τ + t * z i / (1 + z i * c)).im) → HasSum (fun ξ : F ↦ a ξ * eTr (ξ * x) * Complex.exp ((2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F ξ : ℚ) : ℂ) * τ) * ∏ i : Emb F, ((1 + z i * c)⁻¹ ^ k * Complex.exp ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t * z i / (1 + z i * c)))) ((cK F k : ℂ) * gval k (split 𝔞 𝔟 x) (fun i ↦ τ + z i * (c * τ + t)) (fun i ↦ 1 + z i * c) / ((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F * (omegaFactor 𝔞 : ℂ)) ^ k) := by
  intro F _ _ _ k 𝔞 𝔟 a₀ a x τ c t z hk ha hz
  have hw : (fun i : Emb F ↦ τ + t * z i / (1 + z i * c)) ∈ upperHalf F := fun i ↦ (hz i).2
  have h1 := GlobalTheory.T.hasSum_hilbertEisenstein_shiftedLattice_fourier F k 𝔞 𝔟 a₀ a x _ hk ha hw
  have h2 := GlobalTheory.T.hilbertEisensteinValue_linear_change F k (split 𝔞 𝔟 x) (split 𝔞 𝔟 x) (LinearEquiv.refl F _)
    (fun i ↦ τ + z i * (c * τ + t)) (fun i ↦ 1 + z i * c) (fun i ↦ τ + t * z i / (1 + z i * c)) 1
    (fun i ↦ 1 + z i * c) hk (fun _ ↦ Iff.rfl) (fun i ↦ (hz i).1) (fun v i ↦ by
      have := (hz i).1
      simp only [coord, LinearEquiv.refl_apply, Pi.one_apply]
      field_simp
      ring)
  have h3 := h1.mul_left ((∏ i, (1 + z i * c))⁻¹ ^ k)
  rw [h2]
  convert (preTransparency := .reducible) h3 using 1
  · rfl
  · funext ξ
    have hq : qPow ξ (fun i : Emb F ↦ τ + t * z i / (1 + z i * c)) =
        Complex.exp ((2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F ξ : ℚ) : ℂ) * τ) *
          ∏ i : Emb F, Complex.exp ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t * z i / (1 + z i * c)) := by
      rw [← Complex.exp_sum, ← Complex.exp_add, ← GlobalTheory.T.sum_realEmbeddings_eq_trace_totallyReal F ξ]
      unfold qPow
      congr 1
      simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      ring
    rw [hq, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_inv_distrib]
    ring
  · ring

end GlobalTheory.HilbFam
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumHilbertEisensteinMovedPointStatement

section

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

theorem _root_.GlobalTheory.T.hasSum_hilbertEisenstein_movedPoint : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (τ c t : ℂ) (z : Emb F → ℂ), Even k → IsCoef k 𝔞 𝔟 a₀ a → (∀ i, 1 + z i * c ≠ 0 ∧ 0 < (τ + t * z i / (1 + z i * c)).im) → HasSum (fun ξ : F ↦ a ξ * eTr (ξ * x) * Complex.exp ((2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F ξ : ℚ) : ℂ) * τ) * ∏ i : Emb F, ((1 + z i * c)⁻¹ ^ k * Complex.exp ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t * z i / (1 + z i * c)))) ((cK F k : ℂ) * gval k (split 𝔞 𝔟 x) (fun i ↦ τ + z i * (c * τ + t)) (fun i ↦ 1 + z i * c) / ((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F * (omegaFactor 𝔞 : ℂ)) ^ k) := by
  first | exact @GlobalTheory.HilbFam.hasSum_movedPoint | exact GlobalTheory.HilbFam.hasSum_movedPoint | (intros; apply GlobalTheory.HilbFam.hasSum_movedPoint <;> assumption)
end
end
