module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.DualLatticeIndexEqDiscrPowMulDetPow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPosGramFormIntegralLatticeProperties
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsRealMatrixForLatticeAndDualWithDet
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertSlashRationalMatrixProperties
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsEqTransposeMulDiagonalMul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.ConjugateSelfDual.Statement
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.NeutralLocalFields.Reciprocity
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ThetaSeriesHolomorphicQExpansionOfBoundedCoeff

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.PoissonSummationGaussianConstantOnEvenBlocks

section

@[expose] public section

open Matrix Complex
open scoped Real

namespace GlobalTheory.HilbertThetaSeries

section General

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem dotProduct_transpose_mul_diagonal_mul_mulVec (P : Matrix ι ι ℝ) (t : ι → ℂ) (x : ι → ℝ) :
    (fun i => (x i : ℂ)) ⬝ᵥ ((P.map ofReal)ᵀ * diagonal t * P.map ofReal) *ᵥ (fun i => (x i : ℂ)) =
      ∑ j, t j * (((P *ᵥ x) j : ℝ) : ℂ) ^ 2 := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose,
    ← ofReal_mulVec_eq P x]
  simp only [dotProduct, mulVec_diagonal]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem siegelGaussIntegral_transpose_mul_diagonal_mul {P : Matrix ι ι ℝ} (hP : P.det ≠ 0)
    {t : ι → ℂ} (ht : ∀ i, 0 < (t i).im) :
    siegelGaussIntegral ((P.map ofReal)ᵀ * diagonal t * P.map ofReal) =
      (|P.det⁻¹| : ℝ) * ∏ i, (π / (-(π * I * t i))) ^ (1 / 2 : ℂ) := by
  have hb (i : ι) : 0 < (-(π * I * t i)).re := by simpa using mul_pos Real.pi_pos (ht i)
  have key := GaussianFourier.integral_cexp_neg_sum_mul_add hb fun _ => 0
  have hc := integral_comp_mulVec_of_det_ne_zero hP (f := fun y : ι → ℝ =>
    cexp (-∑ i, -(π * I * t i) * (y i : ℂ) ^ 2 + ∑ i, (0 : ℂ) * y i)) (by fun_prop)
  rw [key] at hc
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, Complex.exp_zero,
    mul_one] at hc
  rw [← hc, siegelGaussIntegral]
  congr 2 with x
  rw [dotProduct_transpose_mul_diagonal_mul_mulVec]
  congr 1
  simp only [Finset.mul_sum, ← Finset.sum_neg_distrib, zero_mul, Finset.sum_const_zero, add_zero]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem tsum_cexp_diagonal_gaussian {B : Matrix ι ι ℝ} (hB : B.det ≠ 0) (u : ι → ℝ) {z : ι → ℂ}
    (hz : ∀ i, 0 < (z i).im) :
    ∑' m : ι → ℤ, cexp (π * I * ∑ j, (-(z j)⁻¹) * (((B *ᵥ fun i => (m i : ℝ)) j + u j : ℝ) : ℂ) ^ 2) =
      ((|B.det| : ℝ) : ℂ)⁻¹ * (∏ j, (-I * z j) ^ (1 / 2 : ℂ)) *
        ∑' m : ι → ℤ, cexp (π * I * ∑ j, z j * (((B⁻¹ᵀ *ᵥ fun i => (m i : ℝ)) j : ℝ) : ℂ) ^ 2) *
          cexp (2 * π * I * ∑ j, (((B⁻¹ᵀ *ᵥ fun i => (m i : ℝ)) j * u j : ℝ) : ℂ)) := by
  have hz0 (i : ι) : z i ≠ 0 := fun h0 => by simpa [h0] using hz i
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have ht (i : ι) : 0 < (-(z i)⁻¹).im := by
    rw [neg_im, inv_im, neg_div, neg_neg]
    exact div_pos (hz i) (normSq_pos.2 (hz0 i))
  have ht0 (i : ι) : -(z i)⁻¹ ≠ 0 := neg_ne_zero.2 (inv_ne_zero (hz0 i))
  have h := (isSiegel_diagonal_iff.2 ht).transpose_mul_mul hB
  have key := h.riemannTheta_eq_neg_inv (B⁻¹ *ᵥ u) 0
  rw [siegelGaussIntegral_transpose_mul_diagonal_mul hB ht, riemannTheta, riemannTheta] at key
  simp only [mulVec_zero, dotProduct_zero, mul_zero, Complex.exp_zero, mul_one,
    riemannThetaTerm_def] at key
  have hinv : ((B.map ofReal)ᵀ * diagonal (fun i => -(z i)⁻¹) * B.map ofReal)⁻¹ =
      ((B⁻¹ᵀ).map ofReal)ᵀ * diagonal (fun i => -z i) * (B⁻¹ᵀ).map ofReal := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, inv_diagonal_of_ne_zero ht0,
      ← transpose_nonsing_inv, inv_map_ofReal hB, transpose_map, transpose_transpose,
      Matrix.mul_assoc]
    simp
  rw [hinv] at key
  have hc : ((|B.det⁻¹| : ℝ) : ℂ) * ∏ i, (π / -(π * I * -(z i)⁻¹)) ^ (1 / 2 : ℂ) =
      ((|B.det| : ℝ) : ℂ)⁻¹ * ∏ j, (-I * z j) ^ (1 / 2 : ℂ) := by
    rw [abs_inv, ofReal_inv]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    congr 1
    field_simp [hz0 i]
    simp
  rw [hc] at key
  refine (tsum_congr fun m => ?_).trans (key.trans (congrArg _ (tsum_congr fun m => ?_)))
  · have e := dotProduct_transpose_mul_diagonal_mul_mulVec B (fun i => -(z i)⁻¹)
      ((fun i => (m i : ℝ)) + B⁻¹ *ᵥ u)
    rw [mulVec_add, mulVec_mulVec, mul_nonsing_inv _ hB.isUnit, one_mulVec] at e
    simp only [Pi.add_apply, ofReal_add, ofReal_intCast] at e
    rw [e]
    simp only [Pi.zero_apply, ofReal_zero, add_zero, dotProduct, mul_zero, Finset.sum_const_zero,
      ofReal_add]
    congr 1
    ring
  · have e := dotProduct_transpose_mul_diagonal_mul_mulVec B⁻¹ᵀ (fun i => -z i)
      (fun i => (m i : ℝ))
    have e2 : (B⁻¹ᵀ *ᵥ fun i => (m i : ℝ)) ⬝ᵥ u = (fun i => (m i : ℝ)) ⬝ᵥ B⁻¹ *ᵥ u := by
      rw [mulVec_transpose, dotProduct_mulVec]
    simp only [ofReal_intCast] at e
    simp only [Pi.zero_apply, ofReal_zero, add_zero, zero_add]
    rw [neg_mulVec, dotProduct_neg, e, ← Complex.exp_add, ← ofReal_sum]
    change _ = cexp (_ + 2 * π * I * (((B⁻¹ᵀ *ᵥ fun i => (m i : ℝ)) ⬝ᵥ u : ℝ) : ℂ))
    rw [e2]
    simp only [dotProduct, neg_mul, Finset.sum_neg_distrib, ofReal_sum, ofReal_mul, ofReal_intCast]
    congr 1
    ring

end General

theorem tsum_cexp_block_gaussian : ∀ (V κ : Type) [Fintype V] [DecidableEq V] [Fintype κ] [DecidableEq κ] (k : ℕ), Fintype.card κ = 2 * k → ∀ (B : Matrix (V × κ) (V × κ) ℝ), B.det ≠ 0 → ∀ (u : V × κ → ℝ) (z : V → ℂ), (∀ v, 0 < (z v).im) → ∑' m : V × κ → ℤ, Complex.exp (Real.pi * Complex.I * ∑ j, (-(z j.1)⁻¹) * (((B *ᵥ fun i => (m i : ℝ)) j + u j : ℝ) : ℂ) ^ 2) = ((|B.det| : ℝ) : ℂ)⁻¹ * (∏ v, (-Complex.I * z v)) ^ k * ∑' m : V × κ → ℤ, Complex.exp (Real.pi * Complex.I * ∑ j, z j.1 * (((B⁻¹ᵀ *ᵥ fun i => (m i : ℝ)) j : ℝ) : ℂ) ^ 2) * Complex.exp (2 * Real.pi * Complex.I * ∑ j, (((B⁻¹ᵀ *ᵥ fun i => (m i : ℝ)) j * u j : ℝ) : ℂ)) := by
  intro V κ _ _ _ _ k hk B hB u z hz
  rw [tsum_cexp_diagonal_gaussian hB u (z := fun j => z j.1) fun j => hz j.1]
  congr 2
  rw [Fintype.prod_prod_type, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun v _ => ?_
  simp only [Finset.prod_const, Finset.card_univ, hk]
  rw [pow_mul, one_div, cpow_ofNat_inv_pow]

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

theorem _root_.GlobalTheory.T.poisson_summation_gaussian_constant_on_even_blocks : ∀ (V κ : Type) [Fintype V] [DecidableEq V] [Fintype κ] [DecidableEq κ] (k : ℕ), Fintype.card κ = 2 * k → ∀ (B : Matrix (V × κ) (V × κ) ℝ), B.det ≠ 0 → ∀ (u : V × κ → ℝ) (z : V → ℂ), (∀ v, 0 < (z v).im) → ∑' m : V × κ → ℤ, Complex.exp (Real.pi * Complex.I * ∑ j, (-(z j.1)⁻¹) * (((B *ᵥ fun i => (m i : ℝ)) j + u j : ℝ) : ℂ) ^ 2) = ((|B.det| : ℝ) : ℂ)⁻¹ * (∏ v, (-Complex.I * z v)) ^ k * ∑' m : V × κ → ℤ, Complex.exp (Real.pi * Complex.I * ∑ j, z j.1 * (((B⁻¹ᵀ *ᵥ fun i => (m i : ℝ)) j : ℝ) : ℂ) ^ 2) * Complex.exp (2 * Real.pi * Complex.I * ∑ j, (((B⁻¹ᵀ *ᵥ fun i => (m i : ℝ)) j * u j : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.HilbertThetaSeries.tsum_cexp_block_gaussian | exact GlobalTheory.HilbertThetaSeries.tsum_cexp_block_gaussian | (intros; apply GlobalTheory.HilbertThetaSeries.tsum_cexp_block_gaussian <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertThetaSeriesCosetInversionFormula

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.WCos
open UpperHalfPlane hiding I

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

noncomputable def sg (v : InfinitePlace F) : F →+* ℝ := (Pi.evalRingHom (fun _ : InfinitePlace F => ℝ) v).comp rhom

theorem reAt_eq (v : InfinitePlace F) (x : F) : reAt v x = sg v x :=
  ((GlobalTheory.T.hilbert_slash_rational_matrix_properties F 0 (fun _ => 0)).1 v x).symm

theorem cmp_wm (c : Fˣ) (v : InfinitePlace F) (i j : Fin 2) :
    ((HilbertThetaSeries.cmp v (toInf (wm c)) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j
      = sg v (((wm c : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j) := rfl

theorem sg_ne (c : Fˣ) (v : InfinitePlace F) : sg v (c : F) ≠ 0 := (map_ne_zero _).2 c.ne_zero

theorem denom_wm (c : Fˣ) (v : InfinitePlace F) (z : ℂ) :
    denom (HilbertThetaSeries.cmp v (toInf (wm c))) z = (sg v (c : F) : ℂ) * z := by
  unfold denom
  rw [cmp_wm, cmp_wm]
  simp [wm]

theorem act_wm (c : Fˣ) (z : Hn F) (v : InfinitePlace F) :
    ((act (toInf (wm c)) z v : ℍ) : ℂ) = -((sg v (c : F) : ℂ) ^ 2 * (z v : ℂ))⁻¹ := by
  have hc : (sg v (c : F) : ℂ) ≠ 0 := by exact_mod_cast sg_ne c v
  have hz : ((z v : ℍ) : ℂ) ≠ 0 := (z v).ne_zero
  unfold HilbertThetaSeries.act
  rw [coe_smul_of_det_pos, denom_wm]
  · unfold num
    rw [cmp_wm, cmp_wm]
    simp [wm]
    field_simp
  · rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, cmp_wm, cmp_wm, cmp_wm, cmp_wm]
    simp [wm]

theorem ez_QF {κ : Type} [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ) (e : (κ → F) →+ (InfinitePlace F × κ → ℝ))
    (he : ∀ x y v, ∑ i, e x (v, i) * e y (v, i) = reAt v (BF G x y)) (b : F) (x : κ → F) (w : Hn F) :
    ez (b * QF G x) w = Complex.exp (Real.pi * Complex.I * ∑ j : InfinitePlace F × κ,
      ((sg j.1 b : ℂ) * (w j.1 : ℂ)) * ((e x j : ℝ) : ℂ) ^ 2) := by
  unfold ez QF
  congr 1
  rw [Fintype.sum_prod_type, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [reAt_eq, map_mul, map_div₀, map_ofNat, ← reAt_eq v (BF G x x), ← he]
  dsimp only
  rw [← Finset.mul_sum]
  push_cast
  simp only [sq]
  ring

theorem et_BF {κ : Type} [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ) (e : (κ → F) →+ (InfinitePlace F × κ → ℝ))
    (he : ∀ x y v, ∑ i, e x (v, i) * e y (v, i) = reAt v (BF G x y)) (x y : κ → F) :
    et (BF G x y) = Complex.exp (2 * Real.pi * Complex.I * ∑ j : InfinitePlace F × κ, ((e x j * e y j : ℝ) : ℂ)) := by
  unfold et
  congr 2
  rw [← Complex.ofReal_ratCast, ← ((GlobalTheory.T.hilbert_slash_rational_matrix_properties F 0 (fun _ => 0)).2.2.2.2 (BF G x y)).2, ← Complex.ofReal_sum,
    Fintype.sum_prod_type]
  simp only [he]

theorem const_eq (k t : ℕ) (a : F) (c : Fˣ) (z : Hn F) (d : ℝ)
    (hd : d = ((Algebra.norm ℚ a : ℚ) : ℝ) ^ (2 * k) * ((discr F).natAbs : ℝ) ^ k * (t : ℝ) ^ Module.finrank ℚ F) :
    (∏ v, (sg v (c : F) : ℂ) * (z v : ℂ))⁻¹ ^ k * ((d : ℂ)⁻¹ * (∏ v, -Complex.I * ((sg v (c : F) : ℂ) ^ 2 * (z v : ℂ))) ^ k)
      = wC k t a (c : F) := by
  have hP : (∏ v, (sg v (c : F) : ℂ) * (z v : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun v _ => mul_ne_zero (by exact_mod_cast sg_ne c v) (z v).ne_zero
  have hcard : Fintype.card (InfinitePlace F) = Module.finrank ℚ F := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, ← InfinitePlace.card_add_two_mul_card_eq_rank,
      IsTotallyReal.nrComplexPlaces_eq_zero]
  have hN : (∏ v, (sg v (c : F) : ℂ)) = ((Algebra.norm ℚ (c : F) : ℚ) : ℂ) := by
    rw [← Complex.ofReal_ratCast, ← ((GlobalTheory.T.hilbert_slash_rational_matrix_properties F 0 (fun _ => 0)).2.2.2.2 (c : F)).1, Complex.ofReal_prod]
    simp only [reAt_eq]
  have h : (∏ v, -Complex.I * ((sg v (c : F) : ℂ) ^ 2 * (z v : ℂ)))
      = (-Complex.I) ^ Module.finrank ℚ F * ((Algebra.norm ℚ (c : F) : ℚ) : ℂ) * ∏ v, (sg v (c : F) : ℂ) * (z v : ℂ) := by
    rw [← hN, ← hcard, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun v _ => by ring
  rw [h, hd, wC]
  generalize (∏ v, (sg v (c : F) : ℂ) * (z v : ℂ)) = P at hP
  push_cast
  rw [mul_pow _ P, mul_pow, ← pow_mul, mul_comm (Module.finrank ℚ F) k, div_eq_mul_inv, inv_pow]
  have : (P ^ k)⁻¹ * P ^ k = 1 := inv_mul_cancel₀ (pow_ne_zero _ hP)
  generalize (P ^ k)⁻¹ = Q at this
  generalize (_ * _ * _ : ℂ)⁻¹ = R
  linear_combination (R * ((-Complex.I) ^ (k * Module.finrank ℚ F) * ((Algebra.norm ℚ (c : F) : ℚ) : ℂ) ^ k)) * this

theorem wcos : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → ∀ t : ℕ, G.det = (t : ℤ) ^ 2 → ∀ k : ℕ, Fintype.card κ = 2 * k → ∀ (a : F) (c : Fˣ) (x₀ : κ → F), a ≠ 0 → sl0 k (toInf (wm c)) (th G fun x => open Classical in if x - x₀ ∈ aL κ a then 1 else 0) = th G (wT G k t a c {x₀} fun _ => 1) := by
  intro F _ _ _ κ _ _ G hG t ht k hk a c x₀ ha
  letI : DecidableEq (InfinitePlace F) := Classical.decEq _
  obtain ⟨e, B, α, β, he, hα, hβ, hB, hdet⟩ := GlobalTheory.T.exists_realMatrix_for_lattice_and_dual_with_det F κ G hG t ht k hk a ha
  have hsm := (GlobalTheory.HilbertThetaSeries.formLatticeProps F κ G hG).2.1
  have hc : (c : F) ≠ 0 := c.ne_zero
  funext z
  have hz : ∀ v, 0 < ((sg v (c : F) : ℂ) ^ 2 * (z v : ℂ)).im := fun v => by
    rw [← Complex.ofReal_pow, Complex.im_ofReal_mul]
    exact mul_pos (sq_pos_of_ne_zero (sg_ne c v)) (z v).im_pos
  have hP := GlobalTheory.T.poisson_summation_gaussian_constant_on_even_blocks (InfinitePlace F) κ k hk B hB (e x₀) (fun v => (sg v (c : F) : ℂ) ^ 2 * (z v : ℂ)) hz
  have hL : ∀ Φ : (κ → F) → ℂ, (∀ x, x - x₀ ∈ aL κ a → Φ x = 1) → (∀ x, x - x₀ ∉ aL κ a → Φ x = 0) →
      th G Φ (HilbertThetaSeries.act (toInf (wm c)) z)
      = ∑' m : InfinitePlace F × κ → ℤ, Complex.exp (Real.pi * Complex.I * ∑ j, (-((sg j.1 (c : F) : ℂ) ^ 2 * (z j.1 : ℂ))⁻¹)
        * (((B *ᵥ fun i => (m i : ℝ)) j + e x₀ j : ℝ) : ℂ) ^ 2) := by
    intro Φ h1 h0
    unfold th
    have hinj : Function.Injective fun m : InfinitePlace F × κ → ℤ => (α m : κ → F) + x₀ := fun m n h =>
      α.injective (Subtype.ext (add_right_cancel h))
    rw [← hinj.tsum_eq]
    · refine tsum_congr fun m => ?_
      rw [h1 _ (by rw [add_sub_cancel_right]; exact (α m).2), one_mul, ← one_mul (QF G _), ez_QF G e he, map_add (f := _), hα]
      simp only [act_wm, map_one, Complex.ofReal_one, one_mul, Pi.add_apply]
    · intro x hx
      have hx' : x - x₀ ∈ aL κ a := by
        by_contra h
        exact hx (by simp [h0 x h])
      exact ⟨α.symm ⟨_, hx'⟩, by simp⟩
  have hR : th G (wT G k t a c {x₀} fun _ => 1) z = wC k t a (c : F) *
      ∑' m : InfinitePlace F × κ → ℤ, Complex.exp (Real.pi * Complex.I * ∑ j, ((sg j.1 (c : F) : ℂ) ^ 2 * (z j.1 : ℂ))
        * (((B⁻¹ᵀ *ᵥ fun i => (m i : ℝ)) j : ℝ) : ℂ) ^ 2) *
        Complex.exp (2 * Real.pi * Complex.I * ∑ j, (((B⁻¹ᵀ *ᵥ fun i => (m i : ℝ)) j * e x₀ j : ℝ) : ℂ)) := by
    unfold th
    have hinj : Function.Injective fun m : InfinitePlace F × κ → ℤ => (c : F) • (β m : κ → F) := fun m n h =>
      β.injective (Subtype.ext (smul_right_injective _ hc h))
    rw [← hinj.tsum_eq, ← tsum_mul_left]
    · refine tsum_congr fun m => ?_
      have h1 : (a / (c : F)) • (c : F) • (β m : κ → F) ∈ dualL F G := by
        rw [smul_smul, div_mul_cancel₀ _ hc]
        exact (β m).2
      rw [wT, if_pos h1, Finset.sum_singleton, one_mul, (hsm _ _ x₀).1, (hsm _ _ x₀).2.1, mul_div_cancel_left₀ _ hc,
        ez_QF G e he, et_BF G e he, hβ, mul_assoc, mul_comm (Complex.exp _)]
      simp only [map_pow, Complex.ofReal_pow]
    · intro y hy
      have hy' : (a / (c : F)) • y ∈ dualL F G := by
        by_contra h
        exact hy (by simp [wT, h])
      refine ⟨β.symm ⟨(c : F)⁻¹ • y, by rwa [smul_smul, ← div_eq_mul_inv]⟩, ?_⟩
      simp [smul_smul, hc]
  unfold sl0
  simp only [denom_wm]
  rw [hL _ (fun x h => if_pos h) (fun x h => if_neg h), hP, hR, ← mul_assoc, const_eq k t a c z _ hdet]

end GlobalTheory.WCos

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

theorem _root_.GlobalTheory.T.hilbertThetaSeries_coset_inversion_formula : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → ∀ t : ℕ, G.det = (t : ℤ) ^ 2 → ∀ k : ℕ, Fintype.card κ = 2 * k → ∀ (a : F) (c : Fˣ) (x₀ : κ → F), a ≠ 0 → sl0 k (toInf (wm c)) (th G fun x => open Classical in if x - x₀ ∈ aL κ a then 1 else 0) = th G (wT G k t a c {x₀} fun _ => 1) := by
  first | exact @GlobalTheory.WCos.wcos | exact GlobalTheory.WCos.wcos | (intros; apply GlobalTheory.WCos.wcos <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertThetaSeriesPeriodicInversionFormula

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

theorem thetaSeries_periodic_slash_frickeMatrix : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → ∀ t : ℕ, G.det = (t : ℤ) ^ 2 → ∀ k : ℕ, Fintype.card κ = 2 * k → ∀ (a b : F) (c : Fˣ) (T : Finset (κ → F)) (Φ : (κ → F) → ℂ), a ≠ 0 → b ≠ 0 → aL κ a ≤ aL κ b → IsReps (aL κ a) (aL κ b) T → (∀ x, Φ x ≠ 0 → x ∈ aL κ b) → (∀ x, ∀ l ∈ aL κ a, Φ (x + l) = Φ x) → sl0 k (toInf (wm c)) (th G Φ) = th G (wT G k t a c T Φ) := by
  classical
  intro F _ _ _ κ _ _ G hG t ht k hk a b c T Φ ha hb hab hT hsupp hper
  have hdec : ∀ x, Φ x = ∑ x₀ ∈ T, Φ x₀ * (if x - x₀ ∈ aL κ a then (1:ℂ) else 0) := by
    intro x
    have e2 : ∀ x₀ ∈ T, Φ x₀ * (if x - x₀ ∈ aL κ a then (1:ℂ) else 0) = Φ x * (if x - x₀ ∈ aL κ a then (1:ℂ) else 0) := by
      intro x₀ _
      split_ifs with h
      · have := hper x₀ (x - x₀) h
        rw [show x₀ + (x - x₀) = x by abel] at this
        rw [this]
      · simp
    rw [Finset.sum_congr rfl e2, ← Finset.mul_sum]
    by_cases h0 : Φ x = 0
    · simp [h0]
    · obtain ⟨y, ⟨hyT, hy⟩, huniq⟩ := hT.2 x (hsupp x h0)
      rw [Finset.sum_eq_single y]
      · simp [hy]
      · intro x₀ hx₀ hne
        rw [if_neg]
        intro hm
        exact hne (huniq x₀ ⟨hx₀, hm⟩)
      · intro h
        exact absurd hyT h
  have hW : ∀ y, wT G k t a c T Φ y = ∑ x₀ ∈ T, Φ x₀ * wT G k t a c {x₀} (fun _ => 1) y := by
    intro y
    simp only [wT, Finset.sum_singleton, one_mul]
    split_ifs
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun x₀ _ => by ring)
    · simp
  have hsumL : ∀ x₀ ∈ T, ∀ z : Hn F, Summable fun x => (if x - x₀ ∈ aL κ a then (1:ℂ) else 0) * ez (QF G x) z := by
    intro x₀ hx₀ z
    refine (_root_.GlobalTheory.T.thetaSeries_holomorphic_qExpansion_of_bounded_coeff F κ G hG b _ 1 ?_ ?_).1 z
    · intro x hx
      have hm : x - x₀ ∈ aL κ a := by
        by_contra hm
        exact hx (if_neg hm)
      have := (aL κ b).add_mem (hab hm) (hT.1 x₀ hx₀)
      simpa using this
    · intro x
      split_ifs <;> simp
  have hsumR : ∀ (x₀ : κ → F) (z : Hn F), Summable fun y => wT G k t a c {x₀} (fun _ => (1:ℂ)) y * ez (QF G y) z := by
    intro x₀ z
    obtain ⟨-, ⟨N, hN, hN2⟩, -⟩ := _root_.GlobalTheory.T.dualLattice_index_eq_discr_pow_mul_det_pow F κ G hG
    have hc : (c : F) ≠ 0 := c.ne_zero
    have hNF : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
    refine (_root_.GlobalTheory.T.thetaSeries_holomorphic_qExpansion_of_bounded_coeff F κ G hG ((c:F) / ((N:F) * a)) _ ‖wC k t a (c:F)‖ ?_ ?_).1 z
    · intro y hy
      have hd : (a / c) • y ∈ dualL F G := by
        by_contra hd
        exact hy (by simp [wT, hd])
      have hw := (hN2 _ hd).1
      refine AddSubgroup.mem_map.2 ⟨_, hw, ?_⟩
      simp only [DistribSMul.toAddMonoidHom_apply]
      rw [smul_smul, smul_smul]
      rw [show (c:F) / ((N:F) * a) * (N:F) * (a / c) = 1 by field_simp, one_smul]
    · intro y
      simp only [wT, Finset.sum_singleton, one_mul]
      split_ifs
      · simp [et, Complex.norm_exp]
      · simp
  have thL : ∀ z, th G Φ z = ∑ x₀ ∈ T, Φ x₀ * th G (fun x => if x - x₀ ∈ aL κ a then (1:ℂ) else 0) z := by
    intro z
    simp only [th]
    have e : ∀ x, Φ x * ez (QF G x) z = ∑ x₀ ∈ T, Φ x₀ * ((if x - x₀ ∈ aL κ a then (1:ℂ) else 0) * ez (QF G x) z) := by
      intro x
      rw [hdec x, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    rw [tsum_congr e, Summable.tsum_finsetSum (fun x₀ hx₀ => (hsumL x₀ hx₀ z).mul_left (Φ x₀))]
    exact Finset.sum_congr rfl (fun x₀ _ => tsum_mul_left)
  have thR : ∀ z, th G (wT G k t a c T Φ) z = ∑ x₀ ∈ T, Φ x₀ * th G (wT G k t a c {x₀} (fun _ => (1:ℂ))) z := by
    intro z
    simp only [th]
    have e : ∀ y, wT G k t a c T Φ y * ez (QF G y) z = ∑ x₀ ∈ T, Φ x₀ * (wT G k t a c {x₀} (fun _ => (1:ℂ)) y * ez (QF G y) z) := by
      intro y
      rw [hW y, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    rw [tsum_congr e, Summable.tsum_finsetSum (fun x₀ _ => (hsumR x₀ z).mul_left (Φ x₀))]
    exact Finset.sum_congr rfl (fun x₀ _ => tsum_mul_left)
  funext z
  rw [thR z]
  simp only [sl0]
  rw [thL, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x₀ _ => ?_)
  have := congrFun (_root_.GlobalTheory.T.hilbertThetaSeries_coset_inversion_formula F κ G hG t ht k hk a c x₀ ha) z
  simp only [sl0] at this
  rw [← this]
  ring

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

theorem _root_.GlobalTheory.T.hilbertThetaSeries_periodic_inversion_formula : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → ∀ t : ℕ, G.det = (t : ℤ) ^ 2 → ∀ k : ℕ, Fintype.card κ = 2 * k → ∀ (a b : F) (c : Fˣ) (T : Finset (κ → F)) (Φ : (κ → F) → ℂ), a ≠ 0 → b ≠ 0 → aL κ a ≤ aL κ b → IsReps (aL κ a) (aL κ b) T → (∀ x, Φ x ≠ 0 → x ∈ aL κ b) → (∀ x, ∀ l ∈ aL κ a, Φ (x + l) = Φ x) → sl0 k (toInf (wm c)) (th G Φ) = th G (wT G k t a c T Φ) := by
  first | exact @GlobalTheory.HilbertThetaSeries.thetaSeries_periodic_slash_frickeMatrix | exact GlobalTheory.HilbertThetaSeries.thetaSeries_periodic_slash_frickeMatrix | (intros; apply GlobalTheory.HilbertThetaSeries.thetaSeries_periodic_slash_frickeMatrix <;> assumption)
end
end
