module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CmCurveGoodOutsidePrimePremises
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ComplexMultiplicationJPremises
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.SemiChar
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HcfjHolds
public import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Mathlib.NumberTheory.RamificationInertia.Ramification

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeNatCastMemPowOfRingHom

section

@[expose] public section

open NumberField IsDedekindDomain

namespace GlobalTheory.CMModel

theorem exists_prime_natCast_mem_pow_of_ringHom :
    ∀ (F H : Type) [Field F] [NumberField F] [Field H] [NumberField H] (f : F →+* H) (w : HeightOneSpectrum (𝓞 F)) (p n : ℕ), (p : 𝓞 F) ∈ w.asIdeal ^ n → ∃ P : Ideal (𝓞 H), P.IsPrime ∧ P ≠ ⊥ ∧ (p : 𝓞 H) ∈ P ^ n := by
  intro F H _ _ _ _ f w p n hp
  letI : Algebra F H := f.toAlgebra
  haveI := w.isMaximal
  obtain ⟨P, hPm, hP⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 H) w.asIdeal
  refine ⟨P, hPm.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot w.ne_bot P, ?_⟩
  have hle : w.asIdeal.map (algebraMap (𝓞 F) (𝓞 H)) ≤ P := by
    rw [Ideal.map_le_iff_le_comap]
    exact le_of_eq hP.over
  have h1 := Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 H)) hp
  rw [Ideal.map_pow, map_natCast] at h1
  exact Ideal.pow_right_mono hle n h1

end GlobalTheory.CMModel
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeNatCastMemPowOfRingHomStatement

section

@[expose] public section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.exists_prime_natCast_mem_pow_of_ringHom' : ∀ (F H : Type) [Field F] [NumberField F] [Field H] [NumberField H] (f : F →+* H) (w : HeightOneSpectrum (𝓞 F)) (p n : ℕ), (p : 𝓞 F) ∈ w.asIdeal ^ n → ∃ P : Ideal (𝓞 H), P.IsPrime ∧ P ≠ ⊥ ∧ (p : 𝓞 H) ∈ P ^ n := by
  first | exact @GlobalTheory.CMModel.exists_prime_natCast_mem_pow_of_ringHom | exact GlobalTheory.CMModel.exists_prime_natCast_mem_pow_of_ringHom | (intros; apply GlobalTheory.CMModel.exists_prime_natCast_mem_pow_of_ringHom <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimeSpanOfSqEqNegPrime

section

@[expose] public section

open NumberField

namespace GlobalTheory.CMModel

theorem isPrime_span_of_sq_eq_neg_prime :
    ∀ (p : ℕ) (K : Type) [Field K] [NumberField K] (y : 𝓞 K), p.Prime → Module.finrank ℚ K = 2 →
      y ^ 2 = -(p : 𝓞 K) → (Ideal.span {y}).IsPrime := by
  intro p K _ _ y hp hK hy
  have hr : Module.finrank ℤ (𝓞 K) = 2 := by rw [RingOfIntegers.rank, hK]
  have h1 : Ideal.absNorm (Ideal.span {y}) ^ 2 = p ^ 2 := by
    rw [← map_pow, Ideal.span_singleton_pow, hy, Ideal.span_singleton_neg,
      Ideal.absNorm_span_singleton]
    have : (p : 𝓞 K) = algebraMap ℤ (𝓞 K) (p : ℤ) := by simp
    rw [this, Algebra.norm_algebraMap, hr]
    simp [Int.natAbs_pow]
  have h2 : Ideal.absNorm (Ideal.span {y}) = p :=
    Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) h1
  apply Ideal.isPrime_of_irreducible_absNorm
  rw [h2]
  exact (Nat.irreducible_iff_nat_prime p).2 hp

end GlobalTheory.CMModel
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimeSpanOfSqEqNegPrimeStatement

section

@[expose] public section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.isPrime_span_of_sq_eq_neg_prime_quadratic : ∀ (p : ℕ) (K : Type) [Field K] [NumberField K] (y : 𝓞 K), p.Prime → Module.finrank ℚ K = 2 → y ^ 2 = -(p : 𝓞 K) → (Ideal.span {y}).IsPrime := by
  first | exact @GlobalTheory.CMModel.isPrime_span_of_sq_eq_neg_prime | exact GlobalTheory.CMModel.isPrime_span_of_sq_eq_neg_prime | (intros; apply GlobalTheory.CMModel.isPrime_span_of_sq_eq_neg_prime <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatPrimeNotMemPrimeCubeOfIsUnramifiedAt

section

@[expose] public section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory

theorem mem_prime_sq_of_sq_mem_prime_cube {A : Type} [CommRing A] [IsDedekindDomain A]
    (P : Ideal A) [hP : P.IsPrime] (hP0 : P ≠ ⊥) (Y : A) (h : Y ^ 2 ∈ P ^ 3) : Y ∈ P ^ 2 := by
  have hY : Y ∈ P := hP.mem_of_pow_mem 2 (Ideal.pow_le_self (by norm_num) h)
  have hprime : Prime P := Ideal.prime_of_isPrime hP0 hP
  have hdvd : P ∣ Ideal.span {Y} := Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hY)
  obtain ⟨J, hJ⟩ := hdvd
  have h2 : P ^ 3 ∣ Ideal.span {Y} ^ 2 := by
    rw [Ideal.span_singleton_pow]
    exact Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr h)
  rw [hJ, mul_pow, show P ^ 3 = P ^ 2 * P by ring] at h2
  have hP2 : P ^ 2 ≠ 0 := pow_ne_zero _ hP0
  have h3 : P ∣ J ^ 2 := (mul_dvd_mul_iff_left hP2).mp h2
  have h4 : P ∣ J := hprime.dvd_of_dvd_pow h3
  have h5 : P ^ 2 ∣ Ideal.span {Y} := by
    rw [hJ, sq]; exact mul_dvd_mul_left P h4
  exact (Ideal.span_singleton_le_iff_mem _).mp (Ideal.le_of_dvd h5)

theorem natPrime_not_mem_cube_of_isUnramifiedAt :
    ∀ (p : ℕ) (K H : Type) [Field K] [NumberField K] [Field H] [NumberField H] [Algebra K H] (x : K) (P : Ideal (𝓞 H)) [P.IsPrime], p.Prime → Module.finrank ℚ K = 2 → x ^ 2 = -(p : K) → P ≠ ⊥ → Algebra.IsUnramifiedAt (𝓞 K) P → (p : 𝓞 H) ∉ P ^ 3 := by
  intro p K H _ _ _ _ _ x P _ hp hK hx hP hunr hpP
  have hint : IsIntegral ℤ x := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C (p : ℤ), ?_, ?_⟩
    · exact Polynomial.monic_X_pow_add_C _ (by norm_num)
    · simp [hx]
  set y : 𝓞 K := ⟨x, hint⟩ with hydef
  have hy : y ^ 2 = -(p : 𝓞 K) := by
    apply RingOfIntegers.coe_injective
    rw [map_pow, map_neg, map_natCast]
    exact hx
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0] at hy
    have : ((p : 𝓞 K)) = 0 := by simpa using hy.symm
    exact hp.ne_zero (by exact_mod_cast this)
  have hprime : (Ideal.span {y}).IsPrime := GlobalTheory.T.isPrime_span_of_sq_eq_neg_prime_quadratic p K y hp hK hy
  set Y : 𝓞 H := algebraMap (𝓞 K) (𝓞 H) y with hYdef
  have hpY : (p : 𝓞 H) = -(Y ^ 2) := by
    rw [hYdef, ← map_pow, hy, map_neg, map_natCast, neg_neg]
  have hY2 : Y ^ 2 ∈ P ^ 3 := by
    have := (P ^ 3).neg_mem_iff.mpr hpP
    rwa [hpY, neg_neg] at this
  have hYP2 : Y ∈ P ^ 2 := mem_prime_sq_of_sq_mem_prime_cube P hP Y hY2
  have hYP : Y ∈ P := Ideal.pow_le_self (by norm_num) hYP2
  have hyU : y ∈ P.under (𝓞 K) := by
    rw [Ideal.under_def, Ideal.mem_comap]; exact hYP
  have hU0 : P.under (𝓞 K) ≠ ⊥ := by
    intro h; rw [h, Ideal.mem_bot] at hyU; exact hy0 hyU
  have hspan : Ideal.span {y} = P.under (𝓞 K) := by
    have hmax : (Ideal.span {y}).IsMaximal :=
      hprime.isMaximal (by simpa [Ideal.span_singleton_eq_bot] using hy0)
    exact hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance)
      ((Ideal.span_singleton_le_iff_mem _).mpr hyU)
  have he : P.ramificationIdx (𝓞 K) = 1 := Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (P.under (𝓞 K)) P hU0] at he
  have hle : Ideal.map (algebraMap (𝓞 K) (𝓞 H)) (P.under (𝓞 K)) ≤ P := Ideal.map_comap_le
  have hne := (Ideal.ramificationIdx'_ne_one_iff hle).not
  apply hne.mp (not_not.mpr he)
  rw [← hspan, Ideal.map_span, Set.image_singleton]
  exact (Ideal.span_singleton_le_iff_mem _).mpr hYP2

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatPrimeNotMemPrimeCubeOfIsUnramifiedAtStatement

section

@[expose] public section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.natPrime_not_mem_prime_cube_of_isUnramifiedAt : ∀ (p : ℕ) (K H : Type) [Field K] [NumberField K] [Field H] [NumberField H] [Algebra K H] (x : K) (P : Ideal (𝓞 H)) [P.IsPrime], p.Prime → Module.finrank ℚ K = 2 → x ^ 2 = -(p : K) → P ≠ ⊥ → Algebra.IsUnramifiedAt (𝓞 K) P → (p : 𝓞 H) ∉ P ^ 3 := by
  first | exact @GlobalTheory.natPrime_not_mem_cube_of_isUnramifiedAt | exact GlobalTheory.natPrime_not_mem_cube_of_isUnramifiedAt | (intros; apply GlobalTheory.natPrime_not_mem_cube_of_isUnramifiedAt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCastNotMemCubePrimeAdjoinJInvariantSqrtNeg

section

@[expose] public section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem natCast_notMem_pow_three_of_quadratic (p : ℕ) (K : Type) [Field K] [NumberField K]
    [Algebra K ℂ] (h2 : Module.finrank ℚ K = 2) (x : K) (hx : x ^ 2 = -(p : K))
    (L₀ : PeriodPair) [NumberField ℚ⟮(latticeCurve L₀).j⟯]
    (w : HeightOneSpectrum (𝓞 ℚ⟮(latticeCurve L₀).j⟯)) (hp : p.Prime)
    (hL : IsIntegersLattice p L₀) : (p : 𝓞 ℚ⟮(latticeCurve L₀).j⟯) ∉ w.asIdeal ^ 3 := by
  intro hw
  have := isTotallyComplex_of_sq_eq_neg hp.pos hx
  obtain ⟨⟨⟨hfin, -, hun⟩, -⟩, -⟩ :=
    GlobalTheory.Laid.hcfj_holds K h2 L₀ ((isIntegersLattice_iff hp.pos h2 hx L₀).mp hL)
  have : NumberField K⟮(latticeCurve L₀).j⟯ := NumberField.of_module_finite K _
  have hle : ℚ⟮(latticeCurve L₀).j⟯ ≤
      (K⟮(latticeCurve L₀).j⟯.toSubfield.toIntermediateField fun q =>
        SubfieldClass.ratCast_mem _ q) :=
    IntermediateField.adjoin_simple_le_iff.mpr (IntermediateField.mem_adjoin_simple_self K _)
  let f : ℚ⟮(latticeCurve L₀).j⟯ →+* K⟮(latticeCurve L₀).j⟯ :=
    RingHom.codRestrict (algebraMap ℚ⟮(latticeCurve L₀).j⟯ ℂ) K⟮(latticeCurve L₀).j⟯
      fun z => hle z.2
  obtain ⟨P, hP, hP0, hPp⟩ := GlobalTheory.T.exists_prime_natCast_mem_pow_of_ringHom' _ _ f w p 3 hw
  exact GlobalTheory.T.natPrime_not_mem_prime_cube_of_isUnramifiedAt p K K⟮(latticeCurve L₀).j⟯ x P hp h2 hx hP0 (hun P hP0) hPp

theorem natCast_notMem_pow_three_adjoin_j : ∀ (p : ℕ) (L₀ : PeriodPair)
    [NumberField ℚ⟮(latticeCurve L₀).j⟯] (w : HeightOneSpectrum (𝓞 ℚ⟮(latticeCurve L₀).j⟯)),
    p.Prime → IsIntegersLattice p L₀ → (p : 𝓞 ℚ⟮(latticeCurve L₀).j⟯) ∉ w.asIdeal ^ 3 := by
  intro p L₀ _ w hp hL
  have hint : IsIntegral ℚ (sqrtNegNat p) :=
    IsIntegral.of_pow two_pos (by rw [sqrtNegNat_sq]; exact (isIntegral_natCast p).neg)
  have : FiniteDimensional ℚ ℚ⟮sqrtNegNat p⟯ := IntermediateField.adjoin.finiteDimensional hint
  have : NumberField ℚ⟮sqrtNegNat p⟯ := NumberField.of_module_finite ℚ _
  have hx : (IntermediateField.AdjoinSimple.gen ℚ (sqrtNegNat p)) ^ 2 =
      -(p : ℚ⟮sqrtNegNat p⟯) := Subtype.ext (by simpa using sqrtNegNat_sq p)
  have := isTotallyComplex_of_sq_eq_neg hp.pos hx
  have h2 : Module.finrank ℚ ℚ⟮sqrtNegNat p⟯ = 2 := by
    have hle : Module.finrank ℚ ℚ⟮sqrtNegNat p⟯ ≤ 2 := by
      rw [IntermediateField.adjoin.finrank hint]
      have hm : (Polynomial.X ^ 2 + Polynomial.C (p : ℚ)).Monic :=
        Polynomial.monic_X_pow_add_C _ two_ne_zero
      have := Polynomial.natDegree_le_of_dvd (minpoly.dvd ℚ (sqrtNegNat p)
        (p := Polynomial.X ^ 2 + Polynomial.C (p : ℚ)) (by simp [sqrtNegNat_sq])) hm.ne_zero
      rwa [Polynomial.natDegree_X_pow_add_C] at this
    have h1 := IsTotallyComplex.finrank ℚ⟮sqrtNegNat p⟯
    have h3 : 0 < Module.finrank ℚ ℚ⟮sqrtNegNat p⟯ := Module.finrank_pos
    omega
  exact natCast_notMem_pow_three_of_quadratic p _ h2 _ hx L₀ w hp hL

end GlobalTheory.CMModel
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCastNotMemCubePrimeAdjoinJInvariantSqrtNegStatement

section

@[expose] public section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.natCast_notMem_cube_prime_adjoin_jInvariant_sqrtNeg : ∀ (p : ℕ) (L₀ : PeriodPair) [NumberField ℚ⟮(latticeCurve L₀).j⟯] (w : HeightOneSpectrum (𝓞 ℚ⟮(latticeCurve L₀).j⟯)), p.Prime → IsIntegersLattice p L₀ → (p : 𝓞 ℚ⟮(latticeCurve L₀).j⟯) ∉ w.asIdeal ^ 3 := by
  first | exact @GlobalTheory.CMModel.natCast_notMem_pow_three_adjoin_j | exact GlobalTheory.CMModel.natCast_notMem_pow_three_adjoin_j | (intros; apply GlobalTheory.CMModel.natCast_notMem_pow_three_adjoin_j <;> assumption)
end
end
