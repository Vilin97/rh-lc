module

public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Unramified.Locus
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
public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.NumberTheory.NumberField.Discriminant.Different

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NotSqMulUnit

section

@[expose] public section

open NumberField IsDedekindDomain
open scoped nonZeroDivisors Pointwise

namespace GlobalTheory.UnramSquare

theorem not_sq_mul_unit (K : Type) [Field K] [NumberField K] (Q : Ideal (𝓞 K)) [Q.IsMaximal] :
    Algebra.IsUnramifiedAt ℤ Q → ∀ p : ℕ, p.Prime → (p : 𝓞 K) ∈ Q → ∀ y u : 𝓞 K, u ∉ Q →
      y ^ 2 = (p : 𝓞 K) * u → False := by
  intro h p hp hpQ y u hu hyu
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  haveI hPr : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).mpr hpZ
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    hPr.isMaximal (by simpa using hpZ.ne_zero)
  haveI hQp : Q.IsPrime := inferInstance
  haveI : Q.LiesOver (Ideal.span {(p : ℤ)}) := by
    refine ⟨hmax.eq_of_le (Ideal.IsPrime.under ℤ Q).ne_top ?_⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
    simpa using hpQ
  letI := Localization.AtPrime.algebraOfLiesOver (Ideal.span {(p : ℤ)}) Q
  have h2 := ((Algebra.isUnramifiedAt_iff_map_eq ℤ (Ideal.span {(p : ℤ)}) Q).1 h).2
  have hyQ : y ∈ Q := hQp.mem_of_pow_mem 2 (by rw [hyu]; exact Q.mul_mem_right _ hpQ)
  have h3 : algebraMap (𝓞 K) (Localization.AtPrime Q) y ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime Q) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff _ Q y).2 hyQ
  rw [← h2, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at h3
  obtain ⟨w, hw⟩ := h3
  obtain ⟨⟨z, t⟩, hzt⟩ := IsLocalization.surj Q.primeCompl w
  have htz : (t : 𝓞 K) * y = p * z := by
    apply IsLocalization.injective (Localization.AtPrime Q) Q.primeCompl_le_nonZeroDivisors
    simp only at hzt
    rw [map_mul, map_mul, ← hw, ← hzt]
    simp only [map_natCast, eq_intCast, Int.cast_natCast]
    ring
  have hp0 : (p : 𝓞 K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h4 : (t : 𝓞 K) ^ 2 * u = p * z ^ 2 := by
    apply mul_left_cancel₀ hp0
    calc (p : 𝓞 K) * ((t : 𝓞 K) ^ 2 * u) = (t : 𝓞 K) ^ 2 * y ^ 2 := by rw [hyu]; ring
      _ = ((t : 𝓞 K) * y) ^ 2 := by ring
      _ = p * (p * z ^ 2) := by rw [htz]; ring
  have h5 : (t : 𝓞 K) ^ 2 * u ∈ Q := by rw [h4]; exact Q.mul_mem_right _ hpQ
  rcases hQp.mem_or_mem h5 with h6 | h6
  · exact t.2 (hQp.mem_of_pow_mem 2 h6)
  · exact hu h6

end GlobalTheory.UnramSquare
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotIsUnramifiedAtOfSqEqNegPrime

section

@[expose] public section

open NumberField IsDedekindDomain

namespace GlobalTheory.SqrtNegRam

theorem not_isUnramifiedAt_of_sq_eq_neg :
    ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] (p : ℕ), p.Prime →
      ¬ (p : ℤ) ∣ discr E → ∀ δ : K, δ ^ 2 = -(p : K) → ∀ w : HeightOneSpectrum (𝓞 K),
        (p : 𝓞 K) ∈ w.asIdeal → ¬ Algebra.IsUnramifiedAt (𝓞 E) w.asIdeal := by
  intro E K _ _ _ _ _ p hp hd δ hδ w hpw hunr
  have hmax := w.isMaximal
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hv : Algebra.IsUnramifiedAt ℤ (w.asIdeal.under (𝓞 E)) := by
    refine (not_dvd_discr_iff_forall_mem E (𝓞 E) hpz).1 hd _ inferInstance ?_
    rw [Ideal.under, Ideal.mem_comap]
    simpa using hpw
  have h1 : w.asIdeal.ramificationIdx (𝓞 E) = 1 := Ideal.ramificationIdx_eq_one_iff.2 hunr
  have h2 : (w.asIdeal.under (𝓞 E)).ramificationIdx ℤ = 1 := Ideal.ramificationIdx_eq_one_iff.2 hv
  have h3 : w.asIdeal.ramificationIdx ℤ = 1 := by
    rw [Ideal.ramificationIdx_tower (R := ℤ) (w.asIdeal.under (𝓞 E)) w.asIdeal, h1, h2]
  have hZ : Algebra.IsUnramifiedAt ℤ w.asIdeal := Ideal.ramificationIdx_eq_one_iff.1 h3
  have hint : IsIntegral ℤ δ := by
    refine IsIntegral.of_pow two_pos ?_
    rw [hδ]
    have : (-(p : K)) = algebraMap ℤ K (-(p : ℤ)) := by simp
    rw [this]
    exact isIntegral_algebraMap
  set y : 𝓞 K := ⟨δ, hint⟩ with hy
  have hy2 : y ^ 2 = (p : 𝓞 K) * (-1) := by
    apply RingOfIntegers.ext
    change algebraMap (𝓞 K) K (y ^ 2) = algebraMap (𝓞 K) K ((p : 𝓞 K) * (-1))
    rw [map_pow, map_mul, map_neg, map_one, map_natCast]
    change δ ^ 2 = _
    rw [hδ]; ring
  have hu : (-1 : 𝓞 K) ∉ w.asIdeal := by
    intro h
    exact hmax.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using w.asIdeal.neg_mem h))
  exact GlobalTheory.UnramSquare.not_sq_mul_unit K w.asIdeal hZ p hp hpw y (-1) hu hy2

end GlobalTheory.SqrtNegRam
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotIsUnramifiedAtOfSqEqNegPrimeStatement

section

@[expose] public section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.not_isUnramifiedAt_of_sq_eq_neg_prime : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] (p : ℕ), p.Prime → ¬ (p : ℤ) ∣ discr E → ∀ δ : K, δ ^ 2 = -(p : K) → ∀ w : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ w.asIdeal → ¬ Algebra.IsUnramifiedAt (𝓞 E) w.asIdeal := by
  first | exact @GlobalTheory.SqrtNegRam.not_isUnramifiedAt_of_sq_eq_neg | exact GlobalTheory.SqrtNegRam.not_isUnramifiedAt_of_sq_eq_neg | (intros; apply GlobalTheory.SqrtNegRam.not_isUnramifiedAt_of_sq_eq_neg <;> assumption)
end
end
