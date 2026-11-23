module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldFiniteSupportSumOrderEqZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceOrderCalculusStatement
public import Mathlib.RingTheory.PowerSeries.Trunc
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
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRatOfHankelEventuallyZeroStatement
import Mathlib.Algebra.Order.Star.Int
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HankelDeterminantIntegralOfQuotient

section

@[expose] public section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

open PowerSeries Finset

theorem hankelInt_sumLemma {F : Type} [Field F] (E Q : PowerSeries F) (n : ℕ) (i : Fin (n + 1)) (s : ℕ) :
    ∑ l : Fin (n + 1), (if (l : ℕ) ≤ i then coeff ((i : ℕ) - l) E else 0) * coeff ((l : ℕ) + s) Q =
      coeff ((i : ℕ) + s) ((trunc ((i : ℕ) + 1) E : PowerSeries F) * Q) := by
  have hi : (i : ℕ) + 1 ≤ n + 1 := by omega
  rw [Fin.sum_univ_eq_sum_range (fun l => (if l ≤ (i : ℕ) then coeff ((i : ℕ) - l) E else 0) * coeff (l + s) Q) (n + 1)]
  simp only [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  have hf : (range (n + 1)).filter (fun l => l ≤ (i : ℕ)) = range ((i : ℕ) + 1) := by
    ext l; simp only [mem_filter, mem_range]; omega
  rw [hf, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => coeff a (trunc ((i : ℕ) + 1) E : PowerSeries F) * coeff b Q)]
  simp only [Polynomial.coeff_coe, coeff_trunc, ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  have hg : (range ((i : ℕ) + s).succ).filter (fun a => a < (i : ℕ) + 1) = range ((i : ℕ) + 1) := by
    ext l; simp only [mem_filter, mem_range, Nat.succ_eq_add_one]; omega
  rw [hg, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [mem_range] at hl
  rw [show (i : ℕ) - ((i : ℕ) + 1 - 1 - l) = l by omega, show (i : ℕ) + 1 - 1 - l + s = (i : ℕ) + s - l by omega]

theorem hankel_integral : ∀ (O F : Type) [CommRing O] [Field F] (ι : O →+* F) (e ψ : PowerSeries O) (φ : PowerSeries F) (n : ℕ), PowerSeries.map ι e * φ = PowerSeries.map ι ψ → ∃ z : O, ι z = ι (PowerSeries.constantCoeff e) ^ (2 * (n + 1)) * hankel (fun i => PowerSeries.coeff i φ) n := by
  intro O F _ _ ι e ψ φ n h
  set E := PowerSeries.map ι e with hE
  set P : ℕ → PowerSeries F := fun i => (trunc (i + 1) E : PowerSeries F) with hP
  let N : Matrix (Fin (n + 1)) (Fin (n + 1)) O := Matrix.of fun i j =>
    coeff ((i : ℕ) + j) ((trunc ((i : ℕ) + 1) e : PowerSeries O) * ψ - (e - (trunc ((j : ℕ) + 1) e : PowerSeries O)) * ψ)
  let T : Matrix (Fin (n + 1)) (Fin (n + 1)) F := Matrix.of fun i l =>
    if (l : ℕ) ≤ i then coeff ((i : ℕ) - l) E else 0
  let H : Matrix (Fin (n + 1)) (Fin (n + 1)) F := Matrix.of fun i j => coeff ((i : ℕ) + j) φ
  have hmapP : ∀ k, PowerSeries.map ι (trunc k e : PowerSeries O) = (trunc k E : PowerSeries F) := by
    intro k; ext m; simp only [hE, coeff_map, Polynomial.coeff_coe, coeff_trunc]; split_ifs <;> simp
  have hX : ∀ i : ℕ, X ^ (i + 1) ∣ E - P i := by
    intro i; rw [X_pow_dvd_iff]; intro m hm
    simp [hP, Polynomial.coeff_coe, coeff_trunc, hm]
  have hdiv : ∀ i j : ℕ, coeff (i + j) ((E - P i) * (E - P j) * φ) = 0 := by
    intro i j
    have h3 : X ^ (i + 1 + (j + 1)) ∣ (E - P i) * (E - P j) * φ := by
      rw [pow_add]; exact Dvd.dvd.mul_right (mul_dvd_mul (hX i) (hX j)) φ
    exact X_pow_dvd_iff.mp h3 _ (by omega)
  have hent : N.map ι = T * H * T.transpose := by
    ext i j
    have inner : ∀ l : Fin (n + 1), ∑ m, H l m * T.transpose m j = coeff ((l : ℕ) + j) (P j * φ) := by
      intro l
      rw [Nat.add_comm (l : ℕ) (j : ℕ)]
      refine Eq.trans ?_ (hankelInt_sumLemma E φ n j l)
      refine sum_congr rfl fun m _ => ?_
      simp only [H, T, Matrix.of_apply, Matrix.transpose_apply]; rw [mul_comm, add_comm (l : ℕ)]
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    simp only [Matrix.mul_apply, inner]
    rw [show (∑ x, T i x * coeff ((x : ℕ) + j) (P j * φ)) = coeff ((i : ℕ) + j) (P i * (P j * φ)) from hankelInt_sumLemma E (P j * φ) n i j]
    simp only [Matrix.map_apply, N, Matrix.of_apply]
    have key : PowerSeries.map ι ((trunc ((i : ℕ) + 1) e : PowerSeries O) * ψ - (e - (trunc ((j : ℕ) + 1) e : PowerSeries O)) * ψ)
        = P i * (P j * φ) - (E - P i) * (E - P j) * φ := by
      rw [map_sub, map_mul, map_mul, map_sub, hmapP, hmapP, ← h, ← hE]
      simp only [hP]; ring
    rw [← coeff_map, key, map_sub, hdiv, sub_zero]
  have hT : T.det = ι (constantCoeff e) ^ (n + 1) := by
    rw [Matrix.det_of_lowerTriangular T ?_]
    · simp [T, E, Finset.prod_const]
    · intro i j hij
      have hij' : i < j := hij
      have h1 : ¬ j ≤ i := not_le.mpr hij'
      have h2 : ¬ ((j : ℕ) ≤ i) := h1
      simp [T, h1, h2]
  refine ⟨N.det, ?_⟩
  rw [RingHom.map_det, RingHom.mapMatrix_apply, hent, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hT]
  show _ = _ * H.det
  ring

end GlobalTheory.Nef
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HankelDeterminantIntegralOfQuotientStatement

section

@[expose] public section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef


theorem _root_.GlobalTheory.T.hankelDeterminant_integral_of_quotient : ∀ (O F : Type) [CommRing O] [Field F] (ι : O →+* F) (e ψ : PowerSeries O) (φ : PowerSeries F) (n : ℕ), PowerSeries.map ι e * φ = PowerSeries.map ι ψ → ∃ z : O, ι z = ι (PowerSeries.constantCoeff e) ^ (2 * (n + 1)) * hankel (fun i => PowerSeries.coeff i φ) n := by
  first | exact @GlobalTheory.Nef.hankel_integral | exact GlobalTheory.Nef.hankel_integral | (intros; apply GlobalTheory.Nef.hankel_integral <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRationalPowerSeriesOfAdelicIntegralPositiveRad

section

@[expose] public section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RatCrit

variable {k F : Type} [Field k] [Field F] [Algebra k F]

theorem hankel_pow_mul (a : F) (c : ℕ → F) (n : ℕ) :
    hankel (fun i => a ^ i * c i) n = a ^ (n * (n + 1)) * hankel c n := by
  have hM : (Matrix.of fun i j : Fin (n + 1) => a ^ ((i : ℕ) + j) * c (i + j)) =
      Matrix.diagonal (fun i : Fin (n + 1) => a ^ (i : ℕ)) * (Matrix.of fun i j : Fin (n + 1) => c (i + j)) *
        Matrix.diagonal (fun i : Fin (n + 1) => a ^ (i : ℕ)) := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [Matrix.of_apply, pow_add]
    ring
  unfold hankel
  rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum]
  have hs : (∑ i : Fin (n + 1), (i : ℕ)) * 2 = n * (n + 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => i) (n + 1), Finset.sum_range_id_mul_two]
    simp [mul_comm]
  rw [← hs, pow_mul]
  ring

theorem ord_mul' (v : Place k F) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    ord v (x * y) = ord v x + ord v y := by
  unfold ord
  rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).2 hx) ((Valuation.ne_zero_iff _).2 hy)]
  ring

theorem ord_pow' (v : Place k F) (x : F) (m : ℕ) : ord v (x ^ m) = m * ord v x := by
  unfold ord
  rw [map_pow, WithZero.log_pow, nsmul_eq_mul]
  ring

theorem ord_of_eq_one (v : Place k F) {x : F} (h : v.1 x = 1) : ord v x = 0 := by
  simp [ord, h]

end GlobalTheory.RatCrit

namespace GlobalTheory.RatCrit

variable {k F : Type} [Field k] [Field F] [Algebra k F]

theorem ord_hankel_ge (v : Place k F) (φ : PowerSeries F) (u : F) (e ψ : PowerSeries v.O) (hu : u ≠ 0)
    (he0 : PowerSeries.constantCoeff e ≠ 0)
    (heq : sc v u e * φ = sc v u ψ) (n : ℕ) (hH : hankel (fun i => PowerSeries.coeff i φ) n ≠ 0) :
    ((n * (n + 1) : ℕ) : ℤ) * ord v u - ((2 * (n + 1) : ℕ) : ℤ) * ord v ((PowerSeries.constantCoeff e : v.O) : F) ≤
      ord v (hankel (fun i => PowerSeries.coeff i φ) n) := by
  have hr : ∀ f : PowerSeries F, PowerSeries.rescale u⁻¹ (PowerSeries.rescale u f) = f := by
    intro f; ext m
    simp only [PowerSeries.coeff_rescale, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hu, one_pow, one_mul]
  have h1 : PowerSeries.map v.O.subtype e * PowerSeries.rescale u⁻¹ φ = PowerSeries.map v.O.subtype ψ := by
    have := congrArg (PowerSeries.rescale u⁻¹) heq
    simpa only [sc, RingHom.comp_apply, map_mul, hr] using this
  obtain ⟨z, hz⟩ := GlobalTheory.T.hankelDeterminant_integral_of_quotient v.O F v.O.subtype e ψ (PowerSeries.rescale u⁻¹ φ) n h1
  have h2 : (fun i => PowerSeries.coeff i φ) = fun i => u ^ i * PowerSeries.coeff i (PowerSeries.rescale u⁻¹ φ) := by
    funext i
    rw [PowerSeries.coeff_rescale, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hu, one_pow, one_mul]
  set c : F := ((PowerSeries.constantCoeff e : v.O) : F) with hc
  set H := hankel (fun i => PowerSeries.coeff i φ) n with hHdef
  set H0 := hankel (fun i => PowerSeries.coeff i (PowerSeries.rescale u⁻¹ φ)) n with hH0
  have h3 : H = u ^ (n * (n + 1)) * H0 := by rw [hHdef, h2, hankel_pow_mul]
  have hz' : (z : F) = c ^ (2 * (n + 1)) * H0 := hz
  have h4 : c ^ (2 * (n + 1)) * H = u ^ (n * (n + 1)) * (z : F) := by rw [h3, hz']; ring
  have hH0 : H0 ≠ 0 := by
    intro h; exact hH (by rw [h3, h, mul_zero])
  have hcne : c ≠ 0 := by
    intro h; apply he0; ext; simpa [hc] using h
  have hzne : (z : F) ≠ 0 := by rw [hz']; exact mul_ne_zero (pow_ne_zero _ hcne) hH0
  have hz1 : 0 ≤ ord v (z : F) :=
    ((GlobalTheory.T.functionFieldPlaceOrder_calculus k F v).2.2.1 _ hzne).1 ((Valuation.mem_valuationSubring_iff _ _).1 z.2)
  have h5 := congrArg (ord v) h4
  rw [ord_mul' v (pow_ne_zero _ hcne) hH, ord_mul' v (pow_ne_zero _ hu) hzne, ord_pow', ord_pow'] at h5
  linarith

end GlobalTheory.RatCrit

namespace GlobalTheory.RatCrit

theorem isRat_of_adelic : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ (φ : PowerSeries F) (u : Place k F → F) (e ψ : ∀ v : Place k F, PowerSeries v.O), (∀ v, u v ≠ 0) → {v | ord v (u v) ≠ 0}.Finite → 0 < ∑ᶠ v, ord v (u v) → (∀ v, PowerSeries.constantCoeff (e v) ≠ 0) → {v | ¬ IsUnit (PowerSeries.constantCoeff (e v))}.Finite → (∀ v, sc v (u v) (e v) * φ = sc v (u v) (ψ v)) → IsRat φ := by
  intro k F _ _ _ _ _ hFF φ u e ψ hu0 hufin hdeg he0 hefin heq
  classical
  set c : Place k F → F := fun v => ((PowerSeries.constantCoeff (e v) : v.O) : F) with hc
  have hcunit : ∀ v, IsUnit (PowerSeries.constantCoeff (e v)) → v.1 (c v) = 1 := by
    intro v h
    obtain ⟨a, ha⟩ := h
    have h1 := ValuationSubring.valuation_unit v.O a
    rw [ha] at h1
    exact (Valuation.isEquiv_valuation_valuationSubring v.1).eq_one_iff_eq_one.2 h1
  set δ := ∑ᶠ v, ord v (c v) with hδ
  set D := ∑ᶠ v, ord v (u v) with hD
  apply GlobalTheory.T.isRat_of_hankel_eventually_eq_zero F φ ((2 * δ).toNat + 1)
  intro n hn
  by_contra hH
  obtain ⟨hHfin, hHsum⟩ := GlobalTheory.T.functionField_finite_support_sum_order_eq_zero k F hFF _ hH
  set H := hankel (fun i => PowerSeries.coeff i φ) n with hHdef
  let T : Finset (Place k F) := hufin.toFinset ∪ hefin.toFinset ∪ hHfin.toFinset
  have sU : Function.support (fun v => ord v (u v)) ⊆ (T : Set (Place k F)) := by
    intro v hv
    simp only [T, Finset.coe_union, Set.Finite.coe_toFinset]
    exact Or.inl (Or.inl hv)
  have sC : Function.support (fun v => ord v (c v)) ⊆ (T : Set (Place k F)) := by
    intro v hv
    simp only [T, Finset.coe_union, Set.Finite.coe_toFinset]
    refine Or.inl (Or.inr ?_)
    intro h
    exact hv (ord_of_eq_one v (hcunit v h))
  have sH : Function.support (fun v => ord v H) ⊆ (T : Set (Place k F)) := by
    intro v hv
    simp only [T, Finset.coe_union, Set.Finite.coe_toFinset]
    refine Or.inr ?_
    intro h
    exact hv (ord_of_eq_one v h)
  rw [finsum_eq_sum_of_support_subset _ sH] at hHsum
  rw [finsum_eq_sum_of_support_subset _ sC] at hδ
  rw [finsum_eq_sum_of_support_subset _ sU] at hD
  have hsum : ∑ v ∈ T, (((n * (n + 1) : ℕ) : ℤ) * ord v (u v) - ((2 * (n + 1) : ℕ) : ℤ) * ord v (c v)) ≤
      ∑ v ∈ T, ord v H :=
    Finset.sum_le_sum fun v _ => ord_hankel_ge v φ (u v) (e v) (ψ v) (hu0 v) (he0 v) (heq v) n hH
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← hD, ← hδ, hHsum] at hsum
  have hn' : 2 * δ + 1 ≤ (n : ℤ) := by
    have := Int.self_le_toNat (2 * δ)
    omega
  have hD1 : 1 ≤ D := hdeg
  push_cast at hsum
  have h6 : (n + 1 : ℤ) * (n * D - 2 * δ) ≤ 0 := by linarith [hsum]
  have h7 : (n : ℤ) * D - 2 * δ ≤ 0 := by
    by_contra h8
    push_neg at h8
    have : (0 : ℤ) < (n + 1 : ℤ) * (n * D - 2 * δ) := mul_pos (by positivity) h8
    linarith
  have h9 : (n : ℤ) ≤ n * D := by nlinarith [(Nat.cast_nonneg n : (0 : ℤ) ≤ n)]
  linarith

end GlobalTheory.RatCrit
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRationalPowerSeriesOfAdelicIntegralPositiveRadStatement

section

@[expose] public section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef


theorem _root_.GlobalTheory.T.isRational_powerSeries_of_adelicIntegral_positiveRadius : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ (φ : PowerSeries F) (u : Place k F → F) (e ψ : ∀ v : Place k F, PowerSeries v.O), (∀ v, u v ≠ 0) → {v | ord v (u v) ≠ 0}.Finite → 0 < ∑ᶠ v, ord v (u v) → (∀ v, PowerSeries.constantCoeff (e v) ≠ 0) → {v | ¬ IsUnit (PowerSeries.constantCoeff (e v))}.Finite → (∀ v, sc v (u v) (e v) * φ = sc v (u v) (ψ v)) → IsRat φ := by
  first | exact @GlobalTheory.RatCrit.isRat_of_adelic | exact GlobalTheory.RatCrit.isRat_of_adelic | (intros; apply GlobalTheory.RatCrit.isRat_of_adelic <;> assumption)
end
end
