module

public import GroundTheory.ProfiniteCohomology.RestrictedRamification.MaxUnramifiedOutside
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DifferentDvdRamifiedPrimePowerStatement
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
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
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Formalism.ConjugateSelfDual.Statement
import ReciprocityTheory.GaloisValuations.GlobalA

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.RamifiedPrimeContainsDiscriminant

section

@[expose] public section

open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.GlobalFiniteness

theorem natAbs_discr_mul_prod_absNorm_mem_of_dvd_differentIdeal
    (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ v ∉ S, Algebra.IsUnramifiedIn (𝓞 E) v.asIdeal)
    (P : Ideal (𝓞 E)) [hP : P.IsPrime] (hP0 : P ≠ ⊥) (hdvd : P ∣ differentIdeal ℤ (𝓞 E)) :
    (((discr F).natAbs * ∏ v ∈ S, v.asIdeal.absNorm : ℕ) : 𝓞 E) ∈ P := by
  by_contra ht
  have hv0 : P.under (𝓞 F) ≠ ⊥ := Ideal.under_ne_bot (𝓞 F) hP0
  have hvp : (P.under (𝓞 F)).IsPrime := inferInstance
  let v : HeightOneSpectrum (𝓞 F) := ⟨P.under (𝓞 F), hvp, hv0⟩
  have hcast : ∀ (n : ℕ), (n : 𝓞 F) ∈ v.asIdeal → (n : 𝓞 E) ∈ P := fun n hn => by
    have : algebraMap (𝓞 F) (𝓞 E) (n : 𝓞 F) ∈ P := hn
    simpa [map_natCast] using this
  have hvS : v ∉ S := by
    intro hvS
    apply ht
    rw [Nat.cast_mul]
    apply Ideal.mul_mem_left
    have hd : v.asIdeal.absNorm ∣ ∏ w ∈ S, w.asIdeal.absNorm := Finset.dvd_prod_of_mem _ hvS
    obtain ⟨c, hc⟩ := hd
    rw [hc, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (hcast _ (Ideal.absNorm_mem _))
  have hlies : P.LiesOver v.asIdeal := ⟨rfl⟩
  have hun : Algebra.IsUnramifiedAt (𝓞 F) P := hS v hvS P hP hlies
  rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 F) (𝓞 E)] at hdvd
  rcases (Ideal.prime_of_isPrime hP0 hP).dvd_or_dvd hdvd with h | h
  · exact not_dvd_differentIdeal_iff.2 hun h
  · apply ht
    rw [Nat.cast_mul]
    apply Ideal.mul_mem_right
    apply hcast
    have hmap : differentIdeal ℤ (𝓞 F) ≤ v.asIdeal := Ideal.map_le_iff_le_comap.1 (Ideal.le_of_dvd h)
    apply hmap
    rw [← absNorm_differentIdeal F (𝓞 F)]
    exact Ideal.absNorm_mem _

end GlobalTheory.CompanionTheory.GlobalFiniteness
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.RamifiedPrimeContainsDiscriminantStatement

section

@[expose] public section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.ramified_prime_contains_discriminant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (S : Finset (HeightOneSpectrum (𝓞 F))), (∀ v ∉ S, Algebra.IsUnramifiedIn (𝓞 E) v.asIdeal) → ∀ (P : Ideal (𝓞 E)) [P.IsPrime], P ≠ ⊥ → P ∣ differentIdeal ℤ (𝓞 E) → (((discr F).natAbs * ∏ v ∈ S, v.asIdeal.absNorm : ℕ) : 𝓞 E) ∈ P := by
  first | exact @GlobalTheory.CompanionTheory.GlobalFiniteness.natAbs_discr_mul_prod_absNorm_mem_of_dvd_differentIdeal | exact GlobalTheory.CompanionTheory.GlobalFiniteness.natAbs_discr_mul_prod_absNorm_mem_of_dvd_differentIdeal | (intros; apply GlobalTheory.CompanionTheory.GlobalFiniteness.natAbs_discr_mul_prod_absNorm_mem_of_dvd_differentIdeal <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.HermiteFinitelyManyUnramifiedExtensions

section

@[expose] public section

@[expose] public section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace GlobalTheory.CompanionTheory.HermiteMinkowski

noncomputable def bound {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) : ℕ :=
  (discr F).natAbs * ∏ v ∈ S, v.asIdeal.absNorm

theorem bound_ne_zero {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) : bound S ≠ 0 := by
  refine mul_ne_zero (Int.natAbs_ne_zero.mpr (discr_ne_zero F)) ?_
  refine Finset.prod_ne_zero_iff.mpr fun v _ => ?_
  rw [Ne, Ideal.absNorm_eq_zero_iff]
  exact v.ne_bot

theorem natAbs_discr_dvd {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hE : ∀ v ∉ S, Algebra.IsUnramifiedIn (𝓞 E) v.asIdeal) :
    (discr E).natAbs ∣ bound S ^ (Module.finrank ℚ E * Module.finrank ℚ E) := by
  have hdvd := GlobalTheory.T.different_dvd_ramified_prime_power E (bound S) (bound_ne_zero S) fun P hP hP0 hPd => by
    haveI := hP
    exact GlobalTheory.T.ramified_prime_contains_discriminant F E S hE P hP0 hPd
  have h := map_dvd Ideal.absNorm hdvd
  rw [absNorm_differentIdeal E (𝓞 E)] at h
  have hr : ((bound S : 𝓞 E)) ^ (Module.finrank ℚ E) =
      algebraMap ℤ (𝓞 E) (((bound S : ℕ) : ℤ) ^ (Module.finrank ℚ E)) := by
    simp
  rw [Ideal.absNorm_span_singleton, hr, Algebra.norm_algebraMap, RingOfIntegers.rank,
    Int.natAbs_pow, Int.natAbs_pow, Int.natAbs_natCast, ← pow_mul] at h
  exact h

end GlobalTheory.CompanionTheory.HermiteMinkowski

open GlobalTheory.CompanionTheory.HermiteMinkowski in
theorem GlobalTheory.CompanionTheory.HermiteMinkowski.finite_unramified_bounded_degree :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
      (S : Finset (HeightOneSpectrum (𝓞 F))) (N : ℕ),
      {E : IntermediateField F Ω | FiniteDimensional F E ∧
        IsUnramifiedOutside (S : Set (HeightOneSpectrum (𝓞 F))) E ∧
        Module.finrank F E ≤ N}.Finite := by
  intro F Ω _ _ _ _ _ S N
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  set n := Module.finrank ℚ F * N with hn
  set M : ℕ := bound S ^ (n * n) with hM
  have hfin := (NumberField.finite_of_discr_bdd Ω M).image Subtype.val
  have hinj : Function.Injective (fun E : IntermediateField F Ω => E.restrictScalars ℚ) :=
    IntermediateField.restrictScalars_injective ℚ
  refine (hfin.preimage hinj.injOn).subset ?_
  rintro E ⟨hfd, hun, hdeg⟩
  haveI := hfd
  haveI : NumberField E := NumberField.of_module_finite F E
  let e : (E.restrictScalars ℚ) ≃ₐ[ℚ] E := (RingEquiv.refl E : E ≃+* E).toRatAlgEquiv
  haveI hfd' : FiniteDimensional ℚ (E.restrictScalars ℚ) :=
    e.toLinearEquiv.symm.finiteDimensional
  refine ⟨⟨E.restrictScalars ℚ, hfd'⟩, ?_, rfl⟩
  haveI : NumberField (E.restrictScalars ℚ) := @NumberField.mk _ _ inferInstance hfd'
  show |discr (E.restrictScalars ℚ)| ≤ (M : ℤ)
  rw [discr_eq_discr_of_algEquiv _ e]
  have hdvd := natAbs_discr_dvd (E := E) S fun v hv => hun v (by simpa using hv)
  have hd : Module.finrank ℚ E ≤ n := by
    rw [← Module.finrank_mul_finrank ℚ F E]
    exact Nat.mul_le_mul_left _ hdeg
  have hb : 0 < bound S := Nat.pos_of_ne_zero (bound_ne_zero S)
  have hle := Nat.le_of_dvd (pow_pos hb _) hdvd
  have hle2 : bound S ^ (Module.finrank ℚ E * Module.finrank ℚ E) ≤ bound S ^ (n * n) :=
    Nat.pow_le_pow_right hb (Nat.mul_le_mul hd hd)
  rw [hM, Int.abs_eq_natAbs]
  exact_mod_cast hle.trans hle2
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.HermiteFinitelyManyUnramifiedExtensionsStatement

section

@[expose] public section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual

theorem _root_.GlobalTheory.T.hermite_finitely_many_unramified_extensions : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (S : Finset (HeightOneSpectrum (𝓞 F))) (N : ℕ), {E : IntermediateField F Ω | FiniteDimensional F E ∧ IsUnramifiedOutside (S : Set (HeightOneSpectrum (𝓞 F))) E ∧ Module.finrank F E ≤ N}.Finite := by
  first | exact @GlobalTheory.CompanionTheory.HermiteMinkowski.finite_unramified_bounded_degree | exact GlobalTheory.CompanionTheory.HermiteMinkowski.finite_unramified_bounded_degree | (intros; apply GlobalTheory.CompanionTheory.HermiteMinkowski.finite_unramified_bounded_degree <;> assumption)
end
end
