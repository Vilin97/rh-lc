module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
public import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ClassNumberLeAbsDiscrOfFinrankEqTwo
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ConvRealChar
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayCountThetaFibreCount
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SumLamIdealLe
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RingOfIntegersSqrtNegThreeModFour
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.DedekindZetaEqSumRealEisenstein
import Mathlib.Algebra.Order.Star.Rat
public import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassNumberBounds
import Mathlib.Algebra.Order.Star.Real
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegralOfMemRayI

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteIdealsIn

section

@[expose] public section

open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

namespace GlobalTheory.Hk.RayConv

variable {K : Type} [Field K] [NumberField K]

theorem lamIdeal_pow {P : Ideal (𝓞 K)} (hP : Prime P) (k : ℕ) :
    lamIdeal (P ^ (k + 1)) = Real.log (Ideal.absNorm P) := by
  have h1 : P.IsPrime := Ideal.isPrime_of_prime hP
  unfold lamIdeal
  rw [if_pos ⟨P, k + 1, h1, hP.ne_zero, by omega, rfl⟩, Ideal.radical_pow _ (by omega), h1.radical]

theorem finite_dvd {I : Ideal (𝓞 K)} (hI : I ≠ 0) : {J : Ideal (𝓞 K) | J ∣ I}.Finite := by
  refine (Ideal.finite_setOf_absNorm_le (S := 𝓞 K) (Ideal.absNorm I)).subset fun J hJ => ?_
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero fun h => hI (Ideal.absNorm_eq_zero_iff.1 h)) (map_dvd _ hJ)

theorem sum_lamIdeal (I : Ideal (𝓞 K)) : I ≠ 0 → ∀ T : Finset (Ideal (𝓞 K)), (∀ J, J ∈ T ↔ J ∣ I) →
    ∑ J ∈ T, lamIdeal J = Real.log (Ideal.absNorm I) := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => intro h; exact (h rfl).elim
  | h₂ I hu =>
    intro _ T hT
    have h1 : I = 1 := isUnit_iff_eq_one.1 hu
    subst h1
    rw [map_one, Nat.cast_one, Real.log_one]
    refine Finset.sum_eq_zero fun J hJ => ?_
    unfold lamIdeal
    rw [if_neg]
    rintro ⟨P, k, hP, hP0, hk, rfl⟩
    have := isUnit_of_dvd_one ((hT _).1 hJ)
    rw [isUnit_pow_iff (by omega), Ideal.isUnit_iff] at this
    exact hP.ne_top this
  | h₃ I P hI hP ih =>
    intro _ T hT
    set S := (finite_dvd hI).toFinset with hS
    have hSm : ∀ J, J ∈ S ↔ J ∣ I := fun J => by simp [hS]
    have hsub : S ⊆ T := fun J hJ => (hT J).2 (((hSm J).1 hJ).mul_left P)
    have hfin : FiniteMultiplicity P I := FiniteMultiplicity.of_prime_left hP hI
    have hN : ∀ J : Ideal (𝓞 K), J ≠ 0 → ((Ideal.absNorm J : ℕ) : ℝ) ≠ 0 := fun J hJ =>
      Nat.cast_ne_zero.2 fun h => hJ (Ideal.absNorm_eq_zero_iff.1 h)
    rw [← Finset.sum_sdiff hsub, ih hI S hSm, map_mul, Nat.cast_mul, Real.log_mul (hN _ hP.ne_zero) (hN _ hI)]
    congr 1
    rw [Finset.sum_eq_single_of_mem (P ^ (multiplicity P I + 1)), lamIdeal_pow hP]
    · rw [Finset.mem_sdiff, hT, hSm]
      refine ⟨?_, hfin.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self _)⟩
      rw [pow_succ']
      exact mul_dvd_mul_left _ (pow_multiplicity_dvd _ _)
    · intro J hJ hne
      rw [Finset.mem_sdiff, hT, hSm] at hJ
      unfold lamIdeal
      rw [if_neg]
      rintro ⟨Q, k, hQ, hQ0, hk, rfl⟩
      have hQp : Prime Q := Ideal.prime_of_isPrime hQ0 hQ
      by_cases hQP : Q = P
      · subst hQP
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        have h1 : Q ^ j ∣ I := by
          have := hJ.1
          rw [pow_succ'] at this
          exact (mul_dvd_mul_iff_left hP.ne_zero).1 this
        have h2 : j ≤ multiplicity Q I := hfin.le_multiplicity_of_pow_dvd h1
        have h3 : ¬ j + 1 ≤ multiplicity Q I := fun h => hJ.2 (pow_dvd_of_le_multiplicity h)
        exact hne (by rw [show j = multiplicity Q I by omega])
      · refine hJ.2 (hQp.pow_dvd_of_dvd_mul_left k ?_ hJ.1)
        intro hd
        exact hQP (associated_iff_eq.1 ((hQp.dvd_prime_iff_associated hP).1 hd))

variable {M : ℕ} (D : RayData K M)

theorem finite_idealsIn (g : D.G) (n : ℕ) : (idealsIn D g n).Finite :=
  (Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).subset fun _ h => h.2.2.1

end GlobalTheory.Hk.RayConv

namespace GlobalTheory.Hk


open RayConv in
theorem aRay_mul_log : ∀ (K : Type) [Field K] [NumberField K] (M : ℕ), 2 ≤ M → ∀ (D : RayData K M) (g : D.G) (n : ℕ), aRay D g n * Real.log n = ∑ h : D.G, ∑ p ∈ n.divisorsAntidiagonal, lamRay D h p.1 * aRay D (g / h) p.2 := by
  intro K _ _ M _ D g n
  let F : D.G → ℕ → Finset (Ideal (𝓞 K)) := fun g n => (finite_idealsIn D g n).toFinset
  have hF : ∀ g n I, I ∈ F g n ↔ I ≠ ⊥ ∧ IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ Ideal.absNorm I = n ∧ D.cls I = g :=
    fun g n I => by simp [F, idealsIn]
  have ha : ∀ g n, aRay D g n = (F g n).card := fun g n => by
    unfold aRay; rw [Set.ncard_eq_toFinset_card _ (finite_idealsIn D g n)]
  have hl : ∀ g n, lamRay D g n = ∑ I ∈ F g n, lamIdeal I := fun g n => by
    unfold lamRay; rw [finsum_mem_eq_finite_toFinset_sum _ (finite_idealsIn D g n)]
  let T : Ideal (𝓞 K) → Finset (Ideal (𝓞 K)) := fun I => if h : I = 0 then ∅ else (finite_dvd h).toFinset
  have hT : ∀ I, I ≠ 0 → ∀ J, J ∈ T I ↔ J ∣ I := fun I hI J => by
    simp only [T]; rw [dite_eq_right hI]; simp
  have L : aRay D g n * Real.log n = ∑ I ∈ F g n, ∑ J ∈ T I, lamIdeal J := by
    rw [ha, ← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun I hI => ?_
    have := (hF _ _ _).1 hI
    rw [sum_lamIdeal I this.1 _ (hT I this.1), this.2.2.1]
  have R : ∀ h (p : ℕ × ℕ), lamRay D h p.1 * aRay D (g / h) p.2 =
      ∑ q ∈ F h p.1 ×ˢ F (g / h) p.2, lamIdeal q.1 := fun h p => by
    rw [hl, ha, Finset.sum_product, Finset.sum_mul]
    refine Finset.sum_congr rfl fun I _ => ?_
    simp [mul_comm]
  simp only [R]
  rw [L, Finset.sum_sigma', Finset.sum_sigma', Finset.sum_sigma']
  symm
  refine Finset.sum_bij (fun x _ => ⟨x.2.1 * x.2.2, x.2.1⟩) ?_ ?_ ?_ ?_
  · rintro ⟨⟨h, p⟩, I, J⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_product, hF, Nat.mem_divisorsAntidiagonal] at hx ⊢
    obtain ⟨⟨-, hp, -⟩, ⟨a1, a2, a3, a4⟩, b1, b2, b3, b4⟩ := hx
    refine ⟨⟨mul_ne_zero a1 b1, a2.mul_left b2, by rw [map_mul, a3, b3, hp], ?_⟩,
      (hT _ (mul_ne_zero a1 b1) _).2 (dvd_mul_right _ _)⟩
    rw [D.cls_mul I J a2 b2 a1 b1, a4, b4, mul_div_cancel]
  · rintro ⟨⟨h, p, p'⟩, I, J⟩ hx ⟨⟨h', q, q'⟩, I', J'⟩ hy hxy
    simp only [Finset.mem_sigma, Finset.mem_product, hF, Nat.mem_divisorsAntidiagonal] at hx hy
    obtain ⟨⟨-, hp, -⟩, ⟨a1, a2, a3, a4⟩, b1, b2, b3, b4⟩ := hx
    obtain ⟨⟨-, hq, -⟩, ⟨c1, c2, c3, c4⟩, d1, d2, d3, d4⟩ := hy
    simp only [Sigma.mk.injEq, heq_eq_eq] at hxy
    obtain ⟨e1, rfl⟩ := hxy
    obtain rfl : J = J' := mul_left_cancel₀ a1 e1
    subst a3 b3 a4 c3 d3 c4
    rfl
  · rintro ⟨I, J⟩ hx
    simp only [Finset.mem_sigma, hF] at hx
    obtain ⟨⟨a1, a2, a3, a4⟩, hJ⟩ := hx
    obtain ⟨J', rfl⟩ := (hT _ a1 _).1 hJ
    have j1 : J ≠ ⊥ := left_ne_zero_of_mul a1
    have j2 : J' ≠ ⊥ := right_ne_zero_of_mul a1
    refine ⟨⟨⟨D.cls J, Ideal.absNorm J, Ideal.absNorm J'⟩, J, J'⟩, ?_, rfl⟩
    simp only [Finset.mem_sigma, Finset.mem_product, hF, Nat.mem_divisorsAntidiagonal, Finset.mem_univ, true_and, and_true]
    refine ⟨⟨by rw [← map_mul, a3], ?_⟩, ⟨j1, a2.of_mul_left_left⟩, j2, a2.of_mul_left_right, ?_⟩
    · rw [← a3]; exact fun h => a1 (Ideal.absNorm_eq_zero_iff.1 h)
    · rw [← a4, D.cls_mul J J' a2.of_mul_left_left a2.of_mul_left_right j1 j2, mul_div_cancel_left]
  · intro x _; rfl

end GlobalTheory.Hk
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsImagQuadIntegers

section

@[expose] public section

open NumberField Module

namespace GlobalTheory.Mem.ImagQuad

open QuadraticZeta

theorem exists_field_sq_eq_neg (d : ℕ) (hd : 0 < d) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (r : K),
      finrank ℚ K = 2 ∧ r ^ 2 = -(d : K) := by
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  set p : Polynomial ℚ := Polynomial.X ^ 2 + Polynomial.C (d : ℚ) with hp
  have hpdeg : p.natDegree = 2 := by
    rw [hp]; compute_degree!
  have hpmon : p.Monic := by
    rw [hp]; monicity!
  have hroot : ∀ x : ℚ, ¬ p.IsRoot x := by
    intro x hx
    simp only [hp, Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C] at hx
    nlinarith [sq_nonneg x]
  have hirr : Irreducible p :=
    Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by rw [hpdeg]; decide) hroot
  have : Fact (Irreducible p) := ⟨hirr⟩
  let pb := AdjoinRoot.powerBasis hirr.ne_zero
  have : FiniteDimensional ℚ (AdjoinRoot p) := pb.finite
  have : NumberField (AdjoinRoot p) := ⟨⟩
  refine ⟨AdjoinRoot p, inferInstance, inferInstance, AdjoinRoot.root p, ?_, ?_⟩
  · rw [pb.finrank, AdjoinRoot.powerBasis_dim, hpdeg]
  · have h := AdjoinRoot.eval₂_root p
    simp only [hp, Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C] at h
    rw [eq_neg_iff_add_eq_zero, ← h]
    simp

theorem exists_imagQuad_integers : ∀ d : ℕ, d.Prime → d % 4 = 3 →
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (ω : 𝓞 K), IsTotallyComplex K ∧
      Module.finrank ℚ K = 2 ∧ discr K = -(d : ℤ) ∧ (2 * ω - 1) ^ 2 = -(d : 𝓞 K) ∧
      (∀ z : 𝓞 K, ∃ a b : ℤ, z = a + b * ω) ∧
      ∀ a b : ℤ, Algebra.norm ℤ ((a : 𝓞 K) + b * ω) * 4 = (2 * a + b) ^ 2 + d * b ^ 2 := by
  intro d hdp hd4
  obtain ⟨K, _, _, r, h2, hr⟩ := exists_field_sq_eq_neg d hdp.pos
  have hsq : Squarefree d := hdp.squarefree
  obtain ⟨w, bar, hw, -, hspan, hemb, -⟩ :=
    GlobalTheory.ringOfIntegers_sqrt_neg_three_mod_four d hsq hd4 K h2 r hr
  have hwr : 2 * (w : K) - 1 = r := by rw [hw]; ring
  have hcoe : algebraMap (𝓞 K) K (2 * w - 1) = r := by
    rw [← hwr]
    simp only [map_sub, map_mul, map_one, map_ofNat]
  have hw2 : (2 * w - 1) ^ 2 = -(d : 𝓞 K) := by
    apply RingOfIntegers.coe_injective
    rw [map_pow, hcoe, hr, map_neg, map_natCast]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, d + 1 = 4 * k := ⟨(d + 1) / 4, by omega⟩
  have hwsq : w * w = w - (k : 𝓞 K) := by
    have h4 : (4 : 𝓞 K) * (w * w - w + k) = 0 := by
      have : ((d : ℕ) : 𝓞 K) + 1 = 4 * (k : 𝓞 K) := by exact_mod_cast hk
      linear_combination hw2 - this
    have h4ne : (4 : 𝓞 K) ≠ 0 := by
      intro h
      have : ((4 : 𝓞 K) : K) = 0 := by rw [h]; simp
      norm_num at this
    have := (mul_eq_zero.mp h4).resolve_left h4ne
    linear_combination this
  have hli : LinearIndependent ℤ ![(1 : 𝓞 K), w] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hK : (s : K) + t * (w : K) = 0 := by
      have := congrArg (fun z : 𝓞 K => (z : K)) hst
      simpa [zsmul_eq_mul] using this
    have ht : t = 0 := by
      by_contra ht
      have htK : (t : K) ≠ 0 := by exact_mod_cast ht
      set q : ℚ := -(2 * s + t) / t with hqdef
      have hrq : r = algebraMap ℚ K q := by
        simp only [hqdef, map_div₀, map_neg, map_add (f := _), map_mul, map_ofNat, map_intCast]
        field_simp
        linear_combination (2 : K) * hK + (-(t : K)) * hwr
      have hq : q ^ 2 = -(d : ℚ) := by
        apply (algebraMap ℚ K).injective
        rw [map_pow, ← hrq, hr]
        simp
      have hdpos : (0 : ℚ) < d := by exact_mod_cast hdp.pos
      nlinarith [sq_nonneg q]
    subst ht
    refine ⟨?_, rfl⟩
    have : (s : K) = 0 := by simpa using hK
    exact_mod_cast this
  have hsp : ⊤ ≤ Submodule.span ℤ (Set.range ![(1 : 𝓞 K), w]) := by
    intro z _
    obtain ⟨a, b, rfl⟩ := hspan z
    have hr' : Set.range ![(1 : 𝓞 K), w] = {1, w} := by
      rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty]; rfl
    rw [hr', Submodule.mem_span_pair]
    exact ⟨a, b, by simp [zsmul_eq_mul]⟩
  let B := Basis.mk hli hsp
  have hB0 : B 0 = 1 := by simp [B]
  have hB1 : B 1 = w := by simp [B]
  have hrepr : ∀ s t : ℤ, B.repr ((s : 𝓞 K) + t * w) = Finsupp.single 0 s + Finsupp.single 1 t := by
    intro s t
    have : (s : 𝓞 K) + t * w = s • B 0 + t • B 1 := by
      rw [hB0, hB1]; simp [zsmul_eq_mul]
    rw [this, map_add (f := _), map_zsmul, map_zsmul, B.repr_self, B.repr_self]
    simp
  refine ⟨K, inferInstance, inferInstance, w, ?_, h2, ?_, hw2, hspan, ?_⟩
  · refine ⟨fun v => ?_⟩
    rw [InfinitePlace.isComplex_iff]
    exact (hemb v.embedding).1
  · exact GlobalTheory.discr_eq_neg_of_sq_eq h2 hsq hd4 hr
  · intro a b
    rw [Algebra.norm_eq_matrix_det B, Matrix.det_fin_two]
    have e00 : Algebra.leftMulMatrix B ((a : 𝓞 K) + b * w) 0 0 = a := by
      rw [Algebra.leftMulMatrix_eq_repr_mul, hB0, mul_one, hrepr]; simp
    have e10 : Algebra.leftMulMatrix B ((a : 𝓞 K) + b * w) 1 0 = b := by
      rw [Algebra.leftMulMatrix_eq_repr_mul, hB0, mul_one, hrepr]; simp
    have hx1 : ((a : 𝓞 K) + b * w) * w = ((-(b * k) : ℤ) : 𝓞 K) + ((a + b : ℤ) : 𝓞 K) * w := by
      push_cast
      linear_combination (b : 𝓞 K) * hwsq
    have e01 : Algebra.leftMulMatrix B ((a : 𝓞 K) + b * w) 0 1 = -(b * k) := by
      rw [Algebra.leftMulMatrix_eq_repr_mul, hB1, hx1, hrepr]; simp
    have e11 : Algebra.leftMulMatrix B ((a : 𝓞 K) + b * w) 1 1 = a + b := by
      rw [Algebra.leftMulMatrix_eq_repr_mul, hB1, hx1, hrepr]; simp
    rw [e00, e10, e01, e11]
    have hk' : (d : ℤ) + 1 = 4 * k := by exact_mod_cast hk
    linear_combination (-(b ^ 2) : ℤ) * hk'

end GlobalTheory.Mem.ImagQuad
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLFamRay

section

@[expose] public section

open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

namespace GlobalTheory.Hk

section

variable {K : Type} [Field K] [NumberField K] {M : ℕ} (D : RayData K M)

theorem aRay_norm_zero (g : D.G) : aRay D g 0 = 0 := by
  have : idealsIn D g 0 = ∅ := by
    ext I
    simp only [idealsIn, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨h1, -, h2, -⟩
    exact h1 (Ideal.absNorm_eq_zero_iff.1 h2)
  simp [aRay, this]

theorem aRay_one_norm_one : aRay D 1 1 = 1 := by
  have : idealsIn D 1 1 = {⊤} := by
    ext I
    simp only [idealsIn, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨-, -, h2, -⟩
      exact Ideal.absNorm_eq_one_iff.1 h2
    · rintro rfl
      refine ⟨top_ne_bot, ?_, Ideal.absNorm_eq_one_iff.2 rfl, D.cls_top⟩
      rw [← Ideal.one_eq_top]; exact isCoprime_one_left
  simp [aRay, this]

theorem aRay_norm_one_of_ne {g : D.G} (hg : g ≠ 1) : aRay D g 1 = 0 := by
  have : idealsIn D g 1 = ∅ := by
    ext I
    simp only [idealsIn, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨-, -, h2, h3⟩
    rw [Ideal.absNorm_eq_one_iff.1 h2, D.cls_top] at h3
    exact hg h3.symm
  simp [aRay, this]

theorem card_ray_le (hK : Module.finrank ℚ K = 2) (hM : M ≠ 0) :
    (Fintype.card D.G : ℝ) ≤ 4 * |(discr K : ℝ)| * (M : ℝ) ^ 2 := by
  have h1 := RayData.card_eq_rayNo K M hM D
  have h2 := (RayNo.rayNo_bounds K (Ideal.span {(M : 𝓞 K)})
    (by simpa [Ideal.span_singleton_eq_bot] using hM)).2.1
  have h3 : Ideal.absNorm (Ideal.span {(M : 𝓞 K)}) = M ^ 2 := by
    rw [Ideal.absNorm_span_singleton, show (M : 𝓞 K) = algebraMap ℤ (𝓞 K) M by simp, Algebra.norm_algebraMap,
      RingOfIntegers.rank, hK]
    simp [Int.natAbs_pow]
  have h4 : (classNumber K : ℝ) ≤ 4 * |(discr K : ℝ)| := by
    exact_mod_cast GlobalTheory.classNumber_le_four_mul_abs_discr K hK
  rw [h3, ← h1] at h2
  have h5 : (Fintype.card D.G : ℝ) ≤ (classNumber K : ℝ) * (M : ℝ) ^ 2 := by exact_mod_cast h2
  exact h5.trans (mul_le_mul_of_nonneg_right h4 (by positivity))

end

theorem addChar_eq_one_or_neg_one {G : Type} [AddCommGroup G] (χ : AddChar G ℂ) (h : χ * χ = 1) (g : G) :
    χ g = 1 ∨ χ g = -1 := by
  have : χ g * χ g = 1 := by
    rw [← AddChar.mul_apply, h, AddChar.one_apply]
  exact mul_self_eq_one_iff.1 this

theorem exists_lFam_ray : ∀ d M : ℕ, d.Prime → d % 4 = 3 → 100 ≤ d → 3 ≤ M → ∃ 𝓕 : LFam, 𝓕.B = (4 * (d : ℝ) * (M : ℝ) ^ 2) ∧
    ∀ p : ℕ, p.Prime → 𝓕.lam 0 p ≠ 0 → GlobalTheory.Mem.An.NormOne d M p := by
  intro d M hd hd4 hd100 hM
  obtain ⟨K, _, _, ω, -, hK, hdisc, hω, -, -⟩ := GlobalTheory.Mem.ImagQuad.exists_imagQuad_integers d hd hd4
  have hx : (((2 * ω - 1 : 𝓞 K) : K)) ^ 2 = -(d : K) := by
    have := congrArg (algebraMap (𝓞 K) K) hω
    simpa using this
  have hM0 : M ≠ 0 := by omega
  let D : RayData K M := rayData K M hM0
  have hc := GlobalTheory.Hk.rayCountTheta K d M _ hd hd4 hd100 hx hK hM D
  have hl := GlobalTheory.Hk.LamRay.lamRay_props K d M _ hd hd4 hd100 hx hK hM D
  have hcard := card_ray_le D hK hM0
  have hdR : (100 : ℝ) ≤ d := by exact_mod_cast hd100
  have hMR : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hM2 : (9 : ℝ) ≤ (M : ℝ) ^ 2 := by nlinarith
  have hs : (10 : ℝ) ≤ Real.sqrt d := Real.le_sqrt_of_sq_le (by linarith)
  have hss : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt (by linarith)
  have hsd : Real.sqrt d ≤ d := by nlinarith
  have hpi := Real.pi_gt_three
  have hpi4 := Real.pi_le_four
  rw [hdisc] at hcard
  have habs : |(((-(d : ℤ) : ℤ)) : ℝ)| = d := by
    rw [Int.cast_neg, abs_neg, Int.cast_natCast, Nat.abs_cast]
  rw [habs] at hcard
  refine ⟨{
    G := Additive D.G
    ft := D.fin
    B := 4 * (d : ℝ) * (M : ℝ) ^ 2
    κ := 2 * Real.pi / (Real.sqrt d * (M : ℝ) ^ 2)
    a := fun g n => aRay D g.toMul n
    lam := fun g n => lamRay D g.toMul n
    B_ge := by nlinarith
    card_le := hcard
    κ_ge := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : Real.sqrt d * (M : ℝ) ^ 2 ≤ d * (M : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hsd (by positivity)
      have h2 : (0 : ℝ) ≤ d * (M : ℝ) ^ 2 := by positivity
      nlinarith
    κ_le := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    a_nonneg := fun g n => Nat.cast_nonneg _
    a_zero := fun g => aRay_norm_zero D _
    a_one := aRay_one_norm_one D
    a_one_ne := fun g hg => aRay_norm_one_of_ne D hg
    count := fun g => (hc g.toMul).1
    theta := fun g => (hc g.toMul).2
    lam_nonneg := fun g n => hl.1 _ n
    lam_le := hl.2.1
    conv := fun g n => GlobalTheory.Hk.aRay_mul_log K M (by omega) D g.toMul n
    sq := fun χ hχ n => GlobalTheory.Hk.RaySq.conv_real_char K M (by omega) D (fun g => (χ (Additive.ofMul g)).re) (by simp) ?_ ?_ n }, rfl, hl.2.2⟩
  · intro g h
    rw [ofMul_mul, AddChar.map_add_eq_mul]
    rcases addChar_eq_one_or_neg_one χ hχ (Additive.ofMul g) with h1 | h1 <;> simp [h1]
  · intro g
    rcases addChar_eq_one_or_neg_one χ hχ (Additive.ofMul g) with h1 | h1 <;> simp [h1]

end GlobalTheory.Hk
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLFamRayStatement

section

@[expose] public section

open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

theorem _root_.GlobalTheory.T.exists_lFam_normOne_of_mod_four_eq_three : ∀ d M : ℕ, d.Prime → d % 4 = 3 → 100 ≤ d → 3 ≤ M → ∃ 𝓕 : LFam, 𝓕.B = (4 * (d : ℝ) * (M : ℝ) ^ 2) ∧ ∀ p : ℕ, p.Prime → 𝓕.lam 0 p ≠ 0 → GlobalTheory.Mem.An.NormOne d M p := by
  first | exact @GlobalTheory.Hk.exists_lFam_ray | exact GlobalTheory.Hk.exists_lFam_ray | (intros; apply GlobalTheory.Hk.exists_lFam_ray <;> assumption)
end
end
