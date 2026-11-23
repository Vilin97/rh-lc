module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
public import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.Analysis.Complex.Basic
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.DefiningCoordinates
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSummableBoundHilbertEisensteinTermsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumHilbertEisensteinMovedPointStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumIteratedComplexPartialDerivTermwise
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedDerivZeroEqLaguerreDerivativePolynomialV
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedPartialDerivConstMulReindex
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRadiusMoebiusPerturbationUpperHalfPlane

section

@[expose] public section

namespace GlobalTheory.HilbFam

theorem exists_radius_moebius_perturbation :
    ∀ (τ c t : ℂ), 0 < τ.im → ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, ‖z‖ < r →
      1 / 2 ≤ ‖1 + z * c‖ ∧ τ.im / 2 ≤ (τ + t * z / (1 + z * c)).im := by
  intro τ c t hτ
  have h1 : ContinuousAt (fun z : ℂ => ‖1 + z * c‖) 0 := by fun_prop
  have h2' : ContinuousAt (fun z : ℂ => τ + t * z / (1 + z * c)) 0 := by
    refine continuousAt_const.add (ContinuousAt.div₀ (by fun_prop) (by fun_prop) (by simp))
  have h2 : ContinuousAt (fun z : ℂ => (τ + t * z / (1 + z * c)).im) 0 :=
    Complex.continuous_im.continuousAt.comp h2'
  have e1 : ∀ᶠ z in nhds (0 : ℂ), (1 / 2 : ℝ) < ‖1 + z * c‖ :=
    h1.eventually (lt_mem_nhds (by norm_num))
  have e2 : ∀ᶠ z in nhds (0 : ℂ), τ.im / 2 < (τ + t * z / (1 + z * c)).im :=
    h2.eventually (lt_mem_nhds (by simp; linarith))
  obtain ⟨r, hr, h⟩ := Metric.eventually_nhds_iff.1 (e1.and e2)
  refine ⟨r, hr, fun z hz => ?_⟩
  have := h (y := z) (by simpa using hz)
  exact ⟨this.1.le, this.2.le⟩

end GlobalTheory.HilbFam
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRadiusMoebiusPerturbationUpperHalfPlaneStatement

section

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

theorem _root_.GlobalTheory.T.exists_radius_moebius_perturbation_upperHalfPlane : ∀ (τ c t : ℂ), 0 < τ.im → ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, ‖z‖ < r → 1 / 2 ≤ ‖1 + z * c‖ ∧ τ.im / 2 ≤ (τ + t * z / (1 + z * c)).im := by
  first | exact @GlobalTheory.HilbFam.exists_radius_moebius_perturbation | exact GlobalTheory.HilbFam.exists_radius_moebius_perturbation | (intros; apply GlobalTheory.HilbFam.exists_radius_moebius_perturbation <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumIteratedComplexPartialDerivTermwiseStatement

section

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

theorem _root_.GlobalTheory.T.hasSum_iteratedComplexPartialDeriv_termwise : ∀ (I : Type) [Fintype I] [DecidableEq I] (Ξ : Type) (u : List I) (r : ℝ) (f : Ξ → (I → ℂ) → ℂ) (g : (I → ℂ) → ℂ) (M : Ξ → ℝ), 0 < r → Summable M → (∀ ξ, DifferentiableOn ℂ (f ξ) (Metric.ball 0 r)) → (∀ ξ, ∀ z ∈ Metric.ball (0 : I → ℂ) r, ‖f ξ z‖ ≤ M ξ) → (∀ z ∈ Metric.ball (0 : I → ℂ) r, HasSum (fun ξ ↦ f ξ z) (g z)) → HasSum (fun ξ ↦ iterD u (f ξ) 0) (iterD u g 0) := by
  first | exact @GlobalTheory.HilbFam.hasSum_iterD_termwise | exact GlobalTheory.HilbFam.hasSum_iterD_termwise | (intros; apply GlobalTheory.HilbFam.hasSum_iterD_termwise <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedDerivZeroEqLaguerreDerivativePolynomialVStatement

section

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

theorem _root_.GlobalTheory.T.iteratedDeriv_zero_eq_laguerreDerivativePolynomialValue : ∀ (k n : ℕ) (c y : ℂ), iteratedDeriv n (fun z : ℂ ↦ (1 + z * c)⁻¹ ^ k * Complex.exp (y * z / (1 + z * c))) 0 = lag k n c y := by
  first | exact @GlobalTheory.HilbFam.LagDeriv.iteratedDeriv_zero_eq_lag | exact GlobalTheory.HilbFam.LagDeriv.iteratedDeriv_zero_eq_lag | (intros; apply GlobalTheory.HilbFam.LagDeriv.iteratedDeriv_zero_eq_lag <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedPartialDerivConstMulReindexStatement

section

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

theorem _root_.GlobalTheory.T.iteratedPartialDeriv_const_mul_reindex : ∀ (I J : Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] (e : I ≃ J) (u : List I) (h : (J → ℂ) → ℂ) (A : ℂ) (z : I → ℂ), iterD u (fun z ↦ A * h (fun j ↦ z (e.symm j))) z = A * iterD (u.map e) h (fun j ↦ z (e.symm j)) := by
  first | exact @GlobalTheory.HilbFam.iterD_const_mul_reindex | exact GlobalTheory.HilbFam.iterD_const_mul_reindex | (intros; apply GlobalTheory.HilbFam.iterD_const_mul_reindex <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedPartialDerivProdOneVarAtZero

section

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.IterDProd

theorem diffOn_iteratedDeriv {r : ℝ} {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (Metric.ball 0 r))
    (n : ℕ) : DifferentiableOn ℂ (iteratedDeriv n f) (Metric.ball 0 r) := by
  induction n with
  | zero => simpa using hf
  | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv Metric.isOpen_ball

theorem hasLineDerivAt_prod {I : Type} [Fintype I] [DecidableEq I] (φ : I → ℂ → ℂ) (A : ℂ)
    (z : I → ℂ) (j : I) (hj : DifferentiableAt ℂ (φ j) (z j)) :
    HasLineDerivAt ℂ (fun z : I → ℂ ↦ A * ∏ i, φ i (z i))
      (A * (deriv (φ j) (z j) * ∏ i ∈ Finset.univ.erase j, φ i (z i))) z (Pi.single j 1) := by
  unfold HasLineDerivAt
  have h1 : (fun t : ℂ ↦ A * ∏ i, φ i ((z + t • (Pi.single j (1 : ℂ) : I → ℂ)) i))
      = fun t ↦ A * (φ j (z j + t) * ∏ i ∈ Finset.univ.erase j, φ i (z i)) := by
    funext t
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
    congr 2
    · simp
    · refine Finset.prod_congr rfl fun i hi ↦ ?_
      simp [Pi.single_eq_of_ne (Finset.ne_of_mem_erase hi)]
  have h2 : HasDerivAt (fun t : ℂ ↦ φ j (z j + t)) (deriv (φ j) (z j)) 0 := by
    have h : HasDerivAt (φ j) (deriv (φ j) (z j)) (z j + 0) := by simpa using hj.hasDerivAt
    exact h.comp_const_add (z j) 0
  show HasDerivAt (fun t : ℂ ↦ A * ∏ i, φ i ((z + t • (Pi.single j (1 : ℂ) : I → ℂ)) i)) _ 0
  rw [h1]
  exact (h2.mul_const _).const_mul A

theorem iterD_prod_ball {I : Type} [Fintype I] [DecidableEq I] (u : List I) (r : ℝ)
    (ψ : I → ℂ → ℂ) (A : ℂ) (hr : 0 < r) (hψ : ∀ i, DifferentiableOn ℂ (ψ i) (Metric.ball 0 r)) :
    ∀ z ∈ Metric.ball (0 : I → ℂ) r, iterD u (fun z ↦ A * ∏ i, ψ i (z i)) z
      = A * ∏ i, iteratedDeriv (u.count i) (ψ i) (z i) := by
  induction u with
  | nil => intro z _; simp [iterD]
  | cons j u ih =>
    intro z hz
    have hzj : z j ∈ Metric.ball (0 : ℂ) r := by
      rw [mem_ball_zero_iff] at hz ⊢
      exact (norm_le_pi_norm z j).trans_lt hz
    have hev : iterD u (fun z ↦ A * ∏ i, ψ i (z i)) =ᶠ[nhds z]
        fun z ↦ A * ∏ i, iteratedDeriv (u.count i) (ψ i) (z i) :=
      Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hz) ih
    have hd := hasLineDerivAt_prod (fun i ↦ iteratedDeriv (u.count i) (ψ i)) A z j
      ((diffOn_iteratedDeriv (hψ j) _).differentiableAt (Metric.isOpen_ball.mem_nhds hzj))
    show lineDeriv ℂ (iterD u (fun z ↦ A * ∏ i, ψ i (z i))) z (Pi.single j 1) = _
    rw [hev.lineDeriv_eq, hd.lineDeriv,
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
    congr 2
    · rw [List.count_cons_self, iteratedDeriv_succ]
    · refine Finset.prod_congr rfl fun i hi ↦ ?_
      rw [List.count_cons_of_ne (Finset.ne_of_mem_erase hi).symm]

theorem iterD_prod : ∀ (I : Type) [Fintype I] [DecidableEq I] (u : List I) (r : ℝ) (ψ : I → ℂ → ℂ) (A : ℂ), 0 < r → (∀ i, DifferentiableOn ℂ (ψ i) (Metric.ball 0 r)) → iterD u (fun z ↦ A * ∏ i, ψ i (z i)) 0 = A * ∏ i, iteratedDeriv (u.count i) (ψ i) 0 := by
  intro I _ _ u r ψ A hr hψ
  exact iterD_prod_ball u r ψ A hr hψ 0 (Metric.mem_ball_self hr)

end GlobalTheory.IterDProd
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedPartialDerivProdOneVarAtZeroStatement

section

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

theorem _root_.GlobalTheory.T.iteratedPartialDeriv_prod_oneVar_at_zero : ∀ (I : Type) [Fintype I] [DecidableEq I] (u : List I) (r : ℝ) (ψ : I → ℂ → ℂ) (A : ℂ), 0 < r → (∀ i, DifferentiableOn ℂ (ψ i) (Metric.ball 0 r)) → iterD u (fun z ↦ A * ∏ i, ψ i (z i)) 0 = A * ∏ i, iteratedDeriv (u.count i) (ψ i) 0 := by
  first | exact @GlobalTheory.IterDProd.iterD_prod | exact GlobalTheory.IterDProd.iterD_prod | (intros; apply GlobalTheory.IterDProd.iterD_prod <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumIteratedDerivHilbertEisensteinSplitLattice

section

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem hasSum_iterD_gval_split : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (τ c t : ℂ) (u : List (Emb F)), Even k → IsCoef k 𝔞 𝔟 a₀ a → 0 < τ.im → HasSum (fun ξ : F ↦ a ξ * eTr (ξ * x) * Complex.exp ((2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F ξ : ℚ) : ℂ) * τ) * ∏ i : Emb F, lag k (u.count i) c ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t)) (iterD u (fun z ↦ (cK F k : ℂ) * gval k (split 𝔞 𝔟 x) (fun i ↦ τ + z i * (c * τ + t)) (fun i ↦ 1 + z i * c)) 0 / ((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F * (omegaFactor 𝔞 : ℂ)) ^ k) := by
  intro F _ _ _ k 𝔞 𝔟 a₀ a x τ c t u hk ha hτ
  obtain ⟨r, hr, hrad⟩ := GlobalTheory.T.exists_radius_moebius_perturbation_upperHalfPlane τ c t hτ
  obtain ⟨M, hM, hbd⟩ := GlobalTheory.T.exists_summable_bound_hilbert_eisenstein_terms F k 𝔞 𝔟 a₀ a x τ c t ha hτ
  set D : ℂ := ((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F * (omegaFactor 𝔞 : ℂ)) ^ k with hD
  set G : (Emb F → ℂ) → ℂ := fun z ↦ (cK F k : ℂ) * gval k (split 𝔞 𝔟 x) (fun i ↦ τ + z i * (c * τ + t)) (fun i ↦ 1 + z i * c) with hG
  have hcoord : ∀ z ∈ Metric.ball (0 : Emb F → ℂ) r, ∀ i, ‖z i‖ < r := fun z hz i ↦
    (norm_le_pi_norm z i).trans_lt (mem_ball_zero_iff.1 hz)
  have hne : ∀ w : ℂ, ‖w‖ < r → 1 + w * c ≠ 0 := fun w hw h ↦ by
    have := (hrad w hw).1
    rw [h, norm_zero] at this
    linarith
  have hψ : ∀ y : ℂ, DifferentiableOn ℂ (fun w : ℂ ↦ (1 + w * c)⁻¹ ^ k * Complex.exp (y * w / (1 + w * c))) (Metric.ball 0 r) := by
    intro y w hw
    have h0 := hne w (mem_ball_zero_iff.1 hw)
    have h1 : DifferentiableAt ℂ (fun w : ℂ ↦ 1 + w * c) w := by fun_prop
    have h2 : DifferentiableAt ℂ (fun w : ℂ ↦ y * w) w := by fun_prop
    exact (((h1.inv h0).pow k).mul (h2.div h1 h0).cexp).differentiableWithinAt
  have key := GlobalTheory.T.hasSum_iteratedComplexPartialDeriv_termwise (Emb F) F u r
    (fun ξ z ↦ a ξ * eTr (ξ * x) * Complex.exp ((2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F ξ : ℚ) : ℂ) * τ) * ∏ i : Emb F, ((1 + z i * c)⁻¹ ^ k * Complex.exp ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t * z i / (1 + z i * c))))
    (fun z ↦ D⁻¹ * G z) M hr hM
    (fun ξ z hz ↦ by
      refine (DifferentiableAt.const_mul ?_ _).differentiableWithinAt
      refine (HasFDerivAt.finsetProd (𝕜 := ℂ) (u := (Finset.univ : Finset (Emb F)))
        (g := fun i (z : Emb F → ℂ) ↦ (1 + z i * c)⁻¹ ^ k * Complex.exp ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t * z i / (1 + z i * c)))
        (fun i _ ↦ DifferentiableAt.hasFDerivAt ?_)).differentiableAt
      have h1 := ((hψ ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t)).differentiableAt
        (Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.2 (hcoord z hz i))))
      exact h1.comp z (differentiableAt_apply (𝕜 := ℂ) i z))
    (fun ξ z hz ↦ hbd ξ z (fun i ↦ hrad _ (hcoord z hz i)))
    (fun z hz ↦ by
      have := GlobalTheory.T.hasSum_hilbertEisenstein_movedPoint F k 𝔞 𝔟 a₀ a x τ c t z hk ha (fun i ↦ ⟨hne _ (hcoord z hz i), by
        have := (hrad _ (hcoord z hz i)).2
        linarith⟩)
      rw [div_eq_inv_mul] at this
      exact this)
  have hc := GlobalTheory.T.iteratedPartialDeriv_const_mul_reindex (Emb F) (Emb F) (Equiv.refl _) u G D⁻¹ 0
  simp only [Equiv.refl_symm, Equiv.coe_refl, id_eq, List.map_id, List.map_id_fun] at hc
  have hc' : iterD u (fun z ↦ D⁻¹ * G z) 0 = iterD u G 0 / D := by
    rw [div_eq_inv_mul]; exact hc
  rw [hc'] at key
  convert key using 2 with ξ
  have := GlobalTheory.T.iteratedPartialDeriv_prod_oneVar_at_zero (Emb F) u r
    (fun i w ↦ (1 + w * c)⁻¹ ^ k * Complex.exp ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t * w / (1 + w * c)))
    (a ξ * eTr (ξ * x) * Complex.exp ((2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F ξ : ℚ) : ℂ) * τ)) hr
    (fun i ↦ hψ _)
  rw [this]
  congr 1
  exact Finset.prod_congr rfl (fun i _ ↦ (GlobalTheory.T.iteratedDeriv_zero_eq_laguerreDerivativePolynomialValue k _ c _).symm)

end GlobalTheory.HilbFam
end
end
