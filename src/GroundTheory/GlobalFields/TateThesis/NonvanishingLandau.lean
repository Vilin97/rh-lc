module

public import GroundTheory.GlobalFields.TateThesis.DedekindZetaContinuation
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import GroundTheory.GlobalFields.TateThesis.HeckeLFunction
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.UniformSpace.Uniformizable
import Std.Tactic.BVDecide.Normalize.Prop
public import GroundTheory.GlobalFields.TateThesis.NonvanishingPrimes
public import Mathlib.NumberTheory.LSeries.Positivity
import Mathlib.Tactic.ENatToNat

-- Source module: GroundTheory.GlobalFields.TateThesis.NonvanishingDivisorSum

section

@[expose] public section

open NumberField Ideal Complex Filter Topology

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

theorem finite_setOf_le_of_ne_bot {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    {J : Ideal (𝓞 K) | I ≤ J}.Finite := by
  have hN : absNorm I ≠ 0 := fun h ↦ hI (absNorm_eq_zero_iff.1 h)
  refine (Set.Finite.biUnion (Finset.finite_toSet (Finset.range (absNorm I + 1)))
    fun k _ ↦ Ring.HasFiniteQuotients.finite_absNorm_eq (S := 𝓞 K) k).subset fun J hJ ↦ ?_
  simp only [Set.mem_iUnion, Finset.coe_range, Set.mem_Iio]
  exact ⟨absNorm J, Nat.lt_succ_of_le (Nat.le_of_dvd (Nat.pos_of_ne_zero hN)
    (absNorm_dvd_absNorm_of_le hJ)), rfl⟩

def idealDivisors (I : Ideal (𝓞 K)) : Finset (Ideal (𝓞 K)) :=
  if hI : I = ⊥ then ∅ else (finite_setOf_le_of_ne_bot hI).toFinset

theorem mem_idealDivisors {I J : Ideal (𝓞 K)} (hI : I ≠ ⊥) : J ∈ idealDivisors I ↔ I ≤ J := by
  rw [idealDivisors, dite_eq_right hI, Set.Finite.mem_toFinset]
  rfl

@[simp]
theorem idealDivisors_bot : idealDivisors (⊥ : Ideal (𝓞 K)) = ∅ :=
  dite_eq_left rfl

def divisorSum (ψ : Ideal (𝓞 K) → ℝ) (I : Ideal (𝓞 K)) : ℝ :=
  ∑ J ∈ idealDivisors I, ψ J

@[simp]
theorem divisorSum_bot (ψ : Ideal (𝓞 K) → ℝ) : divisorSum ψ ⊥ = 0 := by
  rw [divisorSum, idealDivisors_bot, Finset.sum_empty]

theorem divisorSum_top (ψ : Ideal (𝓞 K) → ℝ) : divisorSum ψ ⊤ = ψ ⊤ := by
  have h : idealDivisors (⊤ : Ideal (𝓞 K)) = {⊤} := by
    ext J
    rw [mem_idealDivisors top_ne_bot, Finset.mem_singleton, top_le_iff]
  rw [divisorSum, h, Finset.sum_singleton]

theorem mul_sup_eq_of_le {R : Type*} [CommRing R] {I J B₁ B₂ : Ideal R} (hIJ : I ⊔ J = ⊤)
    (h₁ : I ≤ B₁) (h₂ : J ≤ B₂) : B₁ * B₂ ⊔ I = B₁ := by
  have hB₂ : B₂ ⊔ I = ⊤ := top_le_iff.1 (hIJ ▸ sup_le (le_sup_of_le_right le_rfl)
    (le_sup_of_le_left h₂))
  refine le_antisymm (sup_le Ideal.mul_le_left h₁) ?_
  calc B₁ = B₁ * (B₂ ⊔ I) := by rw [hB₂, Ideal.mul_top]
    _ = B₁ * B₂ ⊔ B₁ * I := Ideal.mul_sup _ _ _
    _ ≤ B₁ * B₂ ⊔ I := sup_le_sup_left Ideal.mul_le_right _

theorem sup_mul_sup_eq_of_le {R : Type*} [CommRing R] {I J D : Ideal R} (hIJ : I ⊔ J = ⊤)
    (hD : I * J ≤ D) : (D ⊔ I) * (D ⊔ J) = D := by
  refine le_antisymm ?_ ?_
  · rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
    exact sup_le (sup_le Ideal.mul_le_left Ideal.mul_le_left) (sup_le Ideal.mul_le_right hD)
  · calc D = D * (I ⊔ J) := by rw [hIJ, Ideal.mul_top]
      _ = D * I ⊔ D * J := Ideal.mul_sup _ _ _
      _ ≤ (D ⊔ I) * (D ⊔ J) := sup_le (by
          rw [mul_comm]
          exact Ideal.mul_mono le_sup_right le_sup_left)
          (Ideal.mul_mono le_sup_left le_sup_right)

theorem divisorSum_mul {ψ : Ideal (𝓞 K) → ℝ} (hψ : ∀ A B, ψ (A * B) = ψ A * ψ B)
    {I J : Ideal (𝓞 K)} (hIJ : I ⊔ J = ⊤) : divisorSum ψ (I * J) = divisorSum ψ I * divisorSum ψ J := by
  by_cases hI : I = ⊥
  · simp [hI]
  by_cases hJ : J = ⊥
  · simp [hJ]
  have hIJ0 : I * J ≠ ⊥ := mul_ne_zero hI hJ
  rw [divisorSum, divisorSum, divisorSum, Finset.sum_mul_sum, ← Finset.sum_product']
  symm
  refine Finset.sum_bij' (fun p _ ↦ p.1 * p.2) (fun D _ ↦ (D ⊔ I, D ⊔ J)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_product, mem_idealDivisors hI, mem_idealDivisors hJ] at hp
    rw [mem_idealDivisors hIJ0]
    exact Ideal.mul_mono hp.1 hp.2
  · intro D hD
    rw [mem_idealDivisors hIJ0] at hD
    rw [Finset.mem_product, mem_idealDivisors hI, mem_idealDivisors hJ]
    exact ⟨le_sup_right, le_sup_right⟩
  · intro p hp
    rw [Finset.mem_product, mem_idealDivisors hI, mem_idealDivisors hJ] at hp
    have h2 : p.1 * p.2 ⊔ J = p.2 := by
      rw [mul_comm]
      exact mul_sup_eq_of_le (by rwa [sup_comm]) hp.2 hp.1
    exact Prod.ext (mul_sup_eq_of_le hIJ hp.1 hp.2) h2
  · intro D hD
    rw [mem_idealDivisors hIJ0] at hD
    exact sup_mul_sup_eq_of_le hIJ hD
  · intro p _
    exact (hψ p.1 p.2).symm

theorem divisorSum_prime_pow {ψ : Ideal (𝓞 K) → ℝ} (hψ : ∀ A B, ψ (A * B) = ψ A * ψ B)
    (hψ1 : ψ ⊤ = 1) {P : Ideal (𝓞 K)} (hP : Prime P) (k : ℕ) :
    divisorSum ψ (P ^ k) = ∑ j ∈ Finset.range (k + 1), ψ P ^ j := by
  have hP0 : P ≠ ⊥ := hP.ne_zero
  have hPk : P ^ k ≠ ⊥ := pow_ne_zero k hP0
  have hψpow : ∀ j : ℕ, ψ (P ^ j) = ψ P ^ j := fun j ↦ by
    induction j with
    | zero => rw [pow_zero, pow_zero, Ideal.one_eq_top, hψ1]
    | succ j ih => rw [pow_succ, pow_succ, hψ, ih]
  have hinj : Function.Injective fun j : ℕ ↦ P ^ j :=
    pow_injective_of_not_isUnit hP.not_isUnit hP0
  have hset : idealDivisors (P ^ k) = (Finset.range (k + 1)).image fun j ↦ P ^ j := by
    ext D
    rw [mem_idealDivisors hPk, Finset.mem_image, ← Ideal.dvd_iff_le, dvd_prime_pow hP]
    simp only [associated_iff_eq, Finset.mem_range, Nat.lt_succ_iff]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, rfl⟩
  rw [divisorSum, hset, Finset.sum_image fun i _ j _ h ↦ hinj h]
  exact Finset.sum_congr rfl fun j _ ↦ hψpow j

theorem geom_sum_nonneg_of_abs_le_one {x : ℝ} (hx : |x| ≤ 1) (n : ℕ) :
    0 ≤ ∑ j ∈ Finset.range n, x ^ j := by
  rcases eq_or_ne x 1 with rfl | h1
  · simp
  have hlt : x < 1 := lt_of_le_of_ne (le_of_abs_le hx) h1
  rw [geom_sum_eq h1]
  refine div_nonneg_of_nonpos ?_ (by linarith)
  have : x ^ n ≤ 1 := (le_abs_self _).trans (by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg x) hx)
  linarith

theorem divisorSum_nonneg {ψ : Ideal (𝓞 K) → ℝ} (hψ : ∀ A B, ψ (A * B) = ψ A * ψ B)
    (hψ1 : ψ ⊤ = 1) (hψb : ∀ A, |ψ A| ≤ 1) (I : Ideal (𝓞 K)) : 0 ≤ divisorSum ψ I := by
  induction I using UniqueFactorizationMonoid.induction_on_coprime with
  | h0 => rw [Ideal.zero_eq_bot, divisorSum_bot]
  | h1 hu =>
    rw [Ideal.isUnit_iff.1 hu, divisorSum_top, hψ1]
    exact zero_le_one
  | hpr i hp =>
    rw [divisorSum_prime_pow hψ hψ1 hp]
    exact geom_sum_nonneg_of_abs_le_one (hψb _) _
  | hcp hxy hx hy =>
    rename_i x y
    have hsup : x ⊔ y = ⊤ := by
      refine Ideal.isUnit_iff.1 (hxy ?_ ?_)
      · exact Ideal.dvd_iff_le.2 le_sup_left
      · exact Ideal.dvd_iff_le.2 le_sup_right
    rw [divisorSum_mul hψ hsup]
    exact mul_nonneg hx hy

theorem neg_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : -s ≠ 0 :=
  neg_ne_zero.2 fun h ↦ by
    rw [h, zero_re] at hs
    linarith

theorem summable_norm_mul_cpow {ψ : Ideal (𝓞 K) → ℝ} (hψb : ∀ A, |ψ A| ≤ 1) {s : ℂ}
    (hs : 1 < s.re) : Summable fun J : Ideal (𝓞 K) ↦ ‖(ψ J : ℂ) * (absNorm J : ℂ) ^ (-s)‖ := by
  refine (summable_absNorm_rpow_inv (K := K) hs).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _) fun J ↦ ?_
  by_cases hJ : J = ⊥
  · simp [hJ, zero_cpow (neg_ne_zero_of_one_lt_re hs),
      Real.zero_rpow (zero_lt_one.trans hs).ne']
  · have hpos : 0 < absNorm J := Nat.pos_of_ne_zero (absNorm_eq_zero_iff.not.2 hJ)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, cpow_neg, norm_inv,
      norm_natCast_cpow_of_pos hpos]
    exact mul_le_of_le_one_left (inv_nonneg.2 (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (hψb J)

theorem hasSum_divisorSum {ψ : Ideal (𝓞 K) → ℝ} (hψb : ∀ A, |ψ A| ≤ 1) {s : ℂ}
    (hs : 1 < s.re) :
    HasSum (fun I : Ideal (𝓞 K) ↦ (divisorSum ψ I : ℂ) * (absNorm I : ℂ) ^ (-s))
      ((∑' J, (ψ J : ℂ) * (absNorm J : ℂ) ^ (-s)) * dedekindZeta K s) := by
  have hs0 := neg_ne_zero_of_one_lt_re hs
  set f : Ideal (𝓞 K) → ℂ := fun J ↦ (ψ J : ℂ) * (absNorm J : ℂ) ^ (-s) with hf_def
  set g : Ideal (𝓞 K) → ℂ := fun J ↦ (absNorm J : ℂ) ^ (-s) with hg_def
  have hf := summable_norm_mul_cpow hψb hs
  have hg : Summable fun J ↦ ‖g J‖ := by
    simpa [hg_def] using
      (summable_norm_mul_cpow (K := K) (ψ := fun _ ↦ 1) (by simp) hs)
  have hζ : dedekindZeta K s = ∑' J, g J := by
    let e := Equiv.sigmaFiberEquiv (fun J : Ideal (𝓞 K) ↦ absNorm J)
    have hsum := e.summable_iff.2 hg.of_norm
    have hgroup := (e.hasSum_iff.2 hg.of_norm.hasSum).sigma fun n ↦ (hsum.sigma_factor n).hasSum
    unfold dedekindZeta LSeries
    rw [← hgroup.tsum_eq]
    refine tsum_congr fun n ↦ ?_
    have hterm (J : {J : Ideal (𝓞 K) // absNorm J = n}) :
        (g ∘ e) ⟨n, J⟩ = (n : ℂ) ^ (-s) := by
      simp [e, hg_def, J.2]
    rw [LSeries.term_def, tsum_congr hterm, tsum_const, nsmul_eq_mul]
    split_ifs with hn
    · subst hn
      simp [zero_cpow hs0]
    · rw [cpow_neg, div_eq_mul_inv]
  rw [hζ, tsum_mul_tsum_of_summable_norm hf hg]
  set F : Ideal (𝓞 K) × Ideal (𝓞 K) → ℂ := fun p ↦ f p.1 * g p.2 with hF_def
  have hF : Summable F := summable_mul_of_summable_norm hf hg
  let e := Equiv.sigmaFiberEquiv (fun p : Ideal (𝓞 K) × Ideal (𝓞 K) ↦ p.1 * p.2)
  have h1 : HasSum (F ∘ e) (∑' p, F p) := e.hasSum_iff.2 hF.hasSum
  have h2 := h1.sigma fun I ↦ ((e.summable_iff.2 hF).sigma_factor I).hasSum
  convert h2 using 1
  funext I
  by_cases hI : I = ⊥
  · subst hI
    rw [divisorSum_bot, ofReal_zero, zero_mul]
    symm
    refine (tsum_congr fun q ↦ ?_).trans tsum_zero
    have hq : q.1.1 * q.1.2 = ⊥ := q.2
    change f q.1.1 * g q.1.2 = 0
    rcases Ideal.mul_eq_bot.1 hq with h | h
    · simp [hf_def, h, zero_cpow hs0]
    · simp [hg_def, h, zero_cpow hs0]

  have hdvd : ∀ J : {J // J ∈ idealDivisors I}, J.1 ∣ I := fun J ↦
    Ideal.dvd_iff_le.2 ((mem_idealDivisors hI).1 J.2)
  have hfib : ∀ q : {p : Ideal (𝓞 K) × Ideal (𝓞 K) // p.1 * p.2 = I},
      q.1.1 ∈ idealDivisors I := fun q ↦ by
    rw [mem_idealDivisors hI]
    calc I = q.1.1 * q.1.2 := q.2.symm
      _ ≤ q.1.1 := Ideal.mul_le_left
  have hne : ∀ q : {p : Ideal (𝓞 K) × Ideal (𝓞 K) // p.1 * p.2 = I},
      q.1.1 ≠ ⊥ := fun q h0 ↦ hI (by rw [← q.2, h0, Ideal.bot_mul])
  let eqv : {p : Ideal (𝓞 K) × Ideal (𝓞 K) // p.1 * p.2 = I} ≃ {J // J ∈ idealDivisors I} :=
    { toFun := fun q ↦ ⟨q.1.1, hfib q⟩
      invFun := fun J ↦ ⟨(J.1, (hdvd J).choose), (hdvd J).choose_spec.symm⟩
      left_inv := fun q ↦ by
        refine Subtype.ext (Prod.ext rfl ?_)
        have h1 : I = q.1.1 * (hdvd ⟨q.1.1, hfib q⟩).choose := (hdvd ⟨q.1.1, hfib q⟩).choose_spec
        exact mul_left_cancel₀ (hne q) (h1.symm.trans q.2.symm)
      right_inv := fun J ↦ rfl }
  have hterm : ∀ q : {p : Ideal (𝓞 K) × Ideal (𝓞 K) // p.1 * p.2 = I},
      (F ∘ e) ⟨I, q⟩ = (ψ (eqv q).1 : ℂ) * (absNorm I : ℂ) ^ (-s) := fun q ↦ by
    change f q.1.1 * g q.1.2 = (ψ q.1.1 : ℂ) * (absNorm I : ℂ) ^ (-s)
    rw [hf_def, hg_def, mul_assoc, ← natCast_mul_natCast_cpow,
      ← Nat.cast_mul, ← map_mul, q.2]
  rw [tsum_congr hterm, tsum_mul_right, Equiv.tsum_eq eqv (fun J ↦ (ψ J.1 : ℂ)),
    Finset.tsum_subtype (idealDivisors I) (fun J ↦ (ψ J : ℂ)), divisorSum, ofReal_sum]

def divisorSumCoeff (ψ : Ideal (𝓞 K) → ℝ) (n : ℕ) : ℂ :=
  ∑' I : {I : Ideal (𝓞 K) // absNorm I = n}, (divisorSum ψ I : ℂ)

theorem hasSum_LSeries_term_divisorSum {ψ : Ideal (𝓞 K) → ℝ} (hψb : ∀ A, |ψ A| ≤ 1) {s : ℂ}
    (hs : 1 < s.re) :
    HasSum (LSeries.term (divisorSumCoeff ψ) s)
      ((∑' J, (ψ J : ℂ) * (absNorm J : ℂ) ^ (-s)) * dedekindZeta K s) := by
  have hs0 := neg_ne_zero_of_one_lt_re hs
  have hsum := hasSum_divisorSum hψb hs
  set h : Ideal (𝓞 K) → ℂ := fun I ↦ (divisorSum ψ I : ℂ) * (absNorm I : ℂ) ^ (-s) with hh
  let e := Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) ↦ absNorm I)
  have h1 : HasSum (h ∘ e) _ := e.hasSum_iff.2 hsum
  have h2 := h1.sigma fun n ↦ ((e.summable_iff.2 hsum.summable).sigma_factor n).hasSum
  convert h2 using 1
  funext n
  rw [LSeries.term_def]
  split_ifs with hn
  · subst hn
    symm
    refine (tsum_congr fun y ↦ ?_).trans tsum_zero
    have hy : (y : Ideal (𝓞 K)) = ⊥ := absNorm_eq_zero_iff.1 y.2
    simp [e, hh, hy]
  · rw [divisorSumCoeff, ← tsum_div_const]
    refine tsum_congr fun y ↦ ?_
    simp [e, hh, y.2, cpow_neg, div_eq_mul_inv]


open scoped ComplexOrder in
theorem divisorSumCoeff_nonneg {ψ : Ideal (𝓞 K) → ℝ} (hψ : ∀ A B, ψ (A * B) = ψ A * ψ B)
    (hψ1 : ψ ⊤ = 1) (hψb : ∀ A, |ψ A| ≤ 1) (n : ℕ) : 0 ≤ divisorSumCoeff ψ n := by
  rw [divisorSumCoeff, ← Complex.ofReal_tsum]
  exact Complex.zero_le_real.2 (tsum_nonneg fun I ↦ divisorSum_nonneg hψ hψ1 hψb I)

theorem divisorSumCoeff_one (ψ : Ideal (𝓞 K) → ℝ) : divisorSumCoeff ψ 1 = ψ ⊤ := by
  rw [divisorSumCoeff, tsum_eq_single ⟨⊤, absNorm_top⟩]
  · rw [divisorSum_top]
  · intro I hI
    exact absurd (Subtype.ext (absNorm_eq_one_iff.1 I.2)) hI

end

end GroundTheory.Global
end
end

-- Source module: GroundTheory.GlobalFields.TateThesis.NonvanishingLandau

section

@[expose] public section

open NumberField InfinitePlace IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Complex Topology
  Filter Ideal
open scoped ComplexOrder

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup


variable (K) in
theorem continuedDedekindZeta_neg_two : continuedDedekindZeta K (-2) = 0 := by
  rw [continuedDedekindZeta_of_ne_zero K (by norm_num), normalizedDedekindZeta]
  have hR : Gammaℝ (-2) = 0 := Gammaℝ_eq_zero_iff.2 ⟨1, by norm_num⟩
  have hC : Gammaℂ (-2) = 0 := by
    rw [Gammaℂ_def, show (-2 : ℂ) = -((2 : ℕ) : ℂ) by norm_num, Complex.Gamma_neg_nat_eq_zero,
      mul_zero]
  have hcard : 0 < nrRealPlaces K + nrComplexPlaces K := by
    rw [← card_eq_nrRealPlaces_add_nrComplexPlaces]
    exact Fintype.card_pos
  have h0 : Gammaℝ (-2) ^ nrRealPlaces K * Gammaℂ (-2) ^ nrComplexPlaces K = 0 := by
    rcases Nat.eq_zero_or_pos (nrRealPlaces K) with h | h
    · rw [hC, zero_pow (by omega), mul_zero]
    · rw [hR, zero_pow h.ne', zero_mul]
  rw [h0, inv_zero, mul_zero, zero_mul]

namespace HeckeCharacter

variable (χ : HeckeCharacter K)

def twistCoeff (t : ℝ) (J : Ideal (𝓞 K)) : ℂ :=
  χ.coeff J * (absNorm J : ℂ) ^ (-((t : ℂ) * I))

theorem twistCoeff_mul (t : ℝ) (A B : Ideal (𝓞 K)) :
    χ.twistCoeff t (A * B) = χ.twistCoeff t A * χ.twistCoeff t B := by
  rw [twistCoeff, twistCoeff, twistCoeff, coeff_mul, map_mul, Nat.cast_mul,
    natCast_mul_natCast_cpow]
  ring

theorem twistCoeff_top (t : ℝ) : χ.twistCoeff t ⊤ = 1 := by
  rw [twistCoeff, coeff_top, absNorm_top, Nat.cast_one, one_cpow, one_mul]

theorem twistCoeff_bot (t : ℝ) : χ.twistCoeff t ⊥ = 0 := by
  rw [twistCoeff, coeff_bot, zero_mul]

theorem norm_twistCoeff_le (t : ℝ) (J : Ideal (𝓞 K)) : ‖χ.twistCoeff t J‖ ≤ 1 := by
  by_cases hJ : J = ⊥
  · rw [hJ, twistCoeff_bot, norm_zero]
    exact zero_le_one
  have hN : 0 < absNorm J := Nat.pos_of_ne_zero fun h ↦ hJ (absNorm_eq_zero_iff.1 h)
  rw [twistCoeff, norm_mul, norm_natCast_cpow_neg_mul_I hN, mul_one]
  exact χ.norm_coeff_le J

theorem hasSum_twistCoeff (t : ℝ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun J ↦ χ.twistCoeff t J * (absNorm J : ℂ) ^ (-s)) (χ.LFunction (s + t * I)) := by
  have hs' : 1 < (s + t * I).re := by simpa using hs
  refine (χ.hasSum_LFunction hs').congr_fun fun J ↦ ?_
  by_cases hJ : J = ⊥
  · rw [hJ, twistCoeff_bot, coeff_bot, zero_mul, zero_mul]
  have hN : (absNorm J : ℂ) ≠ 0 := Nat.cast_ne_zero.2 fun h ↦ hJ (absNorm_eq_zero_iff.1 h)
  rw [twistCoeff, neg_add, cpow_add _ _ hN]
  ring

theorem twistCoeff_asIdeal_of_not_dvd (t : ℝ) {v : HeightOneSpectrum (𝓞 K)}
    (hv : ¬ v.asIdeal ∣ χ.conductor) {π : (v.adicCompletion K)ˣ}
    (hπ : Valued.v (π : v.adicCompletion K) = WithZero.exp (-1 : ℤ)) :
    χ.twistCoeff t v.asIdeal = χ.toIdele (finiteEmbedding v π) *
      ((ideleModule K (finiteEmbedding v π) : ℝ) : ℂ) ^ ((t : ℂ) * I) :=
  χ.coeff_mul_cpow_eq hv hπ t

theorem exists_real_twistCoeff (t : ℝ)
    (hsq : ∀ x : IdeleGroup K,
      ((χ.toIdele x : ℂ) * ((ideleModule K x : ℝ) : ℂ) ^ ((t : ℂ) * I)) ^ 2 = 1)
    (J : Ideal (𝓞 K)) : ∃ r : ℝ, χ.twistCoeff t J = r := by
  induction J using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact ⟨0, by rw [Ideal.zero_eq_bot, twistCoeff_bot, ofReal_zero]⟩
  | h₂ x hx => exact ⟨1, by rw [Ideal.isUnit_iff.1 hx, twistCoeff_top, ofReal_one]⟩
  | h₃ a p _ hp ih =>
    obtain ⟨r, hr⟩ := ih
    rw [twistCoeff_mul, hr]
    let v : HeightOneSpectrum (𝓞 K) := ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩
    have hvp : v.asIdeal = p := rfl
    by_cases hv : v.asIdeal ∣ χ.conductor
    · refine ⟨0, ?_⟩
      rw [← hvp, twistCoeff, χ.coeff_asIdeal_of_dvd hv, zero_mul, zero_mul, ofReal_zero]
    · obtain ⟨π, hπ⟩ := exists_uniformizer v
      have h := hsq (finiteEmbedding v π)
      rw [← χ.twistCoeff_asIdeal_of_not_dvd t hv hπ, hvp, sq, mul_self_eq_one_iff] at h
      rcases h with h | h
      · exact ⟨r, by rw [h, one_mul]⟩
      · exact ⟨-r, by rw [h, ofReal_neg, neg_one_mul]⟩

def twistCoeffRe (t : ℝ) (J : Ideal (𝓞 K)) : ℝ :=
  (χ.twistCoeff t J).re

theorem ofReal_twistCoeffRe (t : ℝ)
    (hsq : ∀ x : IdeleGroup K,
      ((χ.toIdele x : ℂ) * ((ideleModule K x : ℝ) : ℂ) ^ ((t : ℂ) * I)) ^ 2 = 1)
    (J : Ideal (𝓞 K)) : (χ.twistCoeffRe t J : ℂ) = χ.twistCoeff t J := by
  obtain ⟨r, hr⟩ := χ.exists_real_twistCoeff t hsq J
  rw [twistCoeffRe, hr, ofReal_re]

theorem continuation_ne_zero_of_sq_eq_one (t : ℝ)
    (hsq : ∀ x : IdeleGroup K,
      ((χ.toIdele x : ℂ) * ((ideleModule K x : ℝ) : ℂ) ^ ((t : ℂ) * I)) ^ 2 = 1)
    {G : ℂ → ℂ} (hG : Differentiable ℂ G) (hGL : ∀ s : ℂ, 1 < s.re → G s = χ.LFunction s) :
    G (1 + t * I) ≠ 0 := by
  intro hG0
  classical
  set ψ : Ideal (𝓞 K) → ℝ := χ.twistCoeffRe t with hψ_def
  have hψc : ∀ J, (ψ J : ℂ) = χ.twistCoeff t J := χ.ofReal_twistCoeffRe t hsq
  have hψmul : ∀ A B, ψ (A * B) = ψ A * ψ B := fun A B ↦ by
    apply ofReal_injective
    rw [ofReal_mul, hψc, hψc, hψc, twistCoeff_mul]
  have hψ1 : ψ ⊤ = 1 := by
    apply ofReal_injective
    rw [hψc, twistCoeff_top, ofReal_one]
  have hψb : ∀ A, |ψ A| ≤ 1 := fun A ↦ by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, hψc]
    exact χ.norm_twistCoeff_le t A

  have hψL : ∀ s : ℂ, 1 < s.re →
      ∑' J, (ψ J : ℂ) * (absNorm J : ℂ) ^ (-s) = χ.LFunction (s + t * I) := fun s hs ↦ by
    simp only [hψc]
    exact (χ.hasSum_twistCoeff t hs).tsum_eq

  set g₁ : ℂ → ℂ := fun s ↦ G (s + t * I) with hg₁_def
  have hg₁ : Differentiable ℂ g₁ := hG.comp (differentiable_id.add_const _)
  have hg₁1 : g₁ 1 = 0 := hG0
  set ρ : ℂ := (dedekindZeta_residue K : ℂ) with hρ
  set F : ℂ → ℂ := Function.update (fun s ↦ continuedDedekindZeta K s * g₁ s) 1
    (ρ * deriv g₁ 1) with hF_def
  have hFne : ∀ s, s ≠ 1 → DifferentiableAt ℂ F s := fun s hs ↦ by
    refine ((differentiableAt_continuedDedekindZeta K hs).mul (hg₁ s)).congr_of_eventuallyEq ?_
    filter_upwards [eventually_ne_nhds hs] with z hz using Function.update_of_ne hz ..
  have hFdiff : Differentiable ℂ F := by
    intro s
    rcases ne_or_eq s 1 with hs | rfl
    · exact hFne s hs
    refine (analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
    · filter_upwards [self_mem_nhdsWithin] with z hz using hFne z hz
    set Gz : ℂ → ℂ := Function.update (fun s ↦ (s - 1) * continuedDedekindZeta K s) 1 ρ with hGz
    set H : ℂ → ℂ := Function.update (fun s ↦ (g₁ s - g₁ 1) / (s - 1)) 1 (deriv g₁ 1) with hH
    have hFGH : F = Gz * H := by
      ext z
      rcases eq_or_ne z 1 with rfl | hz
      · simp only [hF_def, hGz, hH, Pi.mul_apply, Function.update_self]
      · simp only [hF_def, hGz, hH, Pi.mul_apply, Function.update_of_ne hz, hg₁1, sub_zero]
        field_simp [sub_ne_zero.2 hz]
    rw [hFGH]
    refine ContinuousAt.mul ?_ (hg₁ 1).hasDerivAt.continuousAt_div
    rw [hGz, continuousAt_update_same]
    exact tendsto_sub_one_mul_continuedDedekindZeta K

  have hF2 : F ((-2 : ℝ) : ℂ) = 0 := by
    have h : ((-2 : ℝ) : ℂ) = -2 := by push_cast; ring
    rw [h, hF_def, Function.update_of_ne (by norm_num), continuedDedekindZeta_neg_two, zero_mul]

  have hFL : {s : ℂ | (1 : ℝ) < s.re}.EqOn F (LSeries (divisorSumCoeff ψ)) := by
    intro s hs
    have hs1 : s ≠ 1 := fun h ↦ by
      rw [Set.mem_ofPred_eq, h, one_re] at hs
      exact lt_irrefl _ hs
    have hs' : 1 < (s + t * I).re := by simpa using hs
    rw [hF_def, Function.update_of_ne hs1, LSeries,
      (hasSum_LSeries_term_divisorSum hψb hs).tsum_eq, hψL s hs, continuedDedekindZeta_eq K hs]
    simp only [hg₁_def]
    rw [hGL _ hs']
    ring
  have habs : LSeries.abscissaOfAbsConv (divisorSumCoeff ψ) ≤ ((1 : ℝ) : EReal) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy ↦
      (hasSum_LSeries_term_divisorSum hψb (by simpa using hy)).summable
  have hpos := LSeries.positive_of_differentiable_of_eqOn
    (fun n ↦ divisorSumCoeff_nonneg hψmul hψ1 hψb n)
    (by rw [divisorSumCoeff_one, hψ1, ofReal_one]; exact zero_lt_one) hFdiff habs hFL (-2)
  rw [hF2] at hpos
  exact lt_irrefl _ hpos

end HeckeCharacter

end

end GroundTheory.Global
end
end
