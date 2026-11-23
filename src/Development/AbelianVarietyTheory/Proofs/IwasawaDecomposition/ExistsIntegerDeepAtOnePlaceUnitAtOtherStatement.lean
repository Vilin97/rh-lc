module

public import Formalism.ConjugateSelfDual.Statement
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import ReciprocityTheory.GaloisValuations.GlobalB
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Objects
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import ReciprocityTheory.Automorphisms.PlaceA
import ReciprocityTheory.GaloisValuations.GlobalB
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowValuationLtOfIntegralAlgClosurePlace

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.MaxIdealPow

variable {Ω : Type} [Field Ω]

theorem aeval_eq_coeff_zero_add (A : ValuationSubring Ω) (g : ℤ[X]) {y : Ω} (hy : y ∈ A) :
    ∃ w ∈ A, aeval y g = ((g.coeff 0 : ℤ) : Ω) + y * w := by
  obtain ⟨r, hr⟩ := X_dvd_sub_C (p := g)
  have hg : g = C (g.coeff 0) + X * r := by rw [← hr]; ring
  refine ⟨((aeval (⟨y, hy⟩ : A) r : A) : Ω), SetLike.coe_mem _, ?_⟩
  have h1 : aeval y r = ((aeval (⟨y, hy⟩ : A) r : A) : Ω) :=
    aeval_algebraMap_apply Ω (⟨y, hy⟩ : A) r
  conv_lhs => rw [hg]
  rw [map_add (f := _), map_mul, aeval_C, aeval_X, h1]
  simp

theorem exists_nat_of_isPlaceOver (E : Type) [Field E] [NumberField E] [Algebra E Ω]
    (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)) (hP : IsPlaceOver (F := E) A P) :
    ∃ p : ℕ, p ≠ 0 ∧ p ≠ 1 ∧ ∀ n : ℤ, A.valuation (n : Ω) < 1 ↔ (p : ℤ) ∣ n := by
  let I : Ideal ℤ := P.asIdeal.comap (Int.castRingHom (𝓞 E))
  obtain ⟨a, ha⟩ := Submodule.IsPrincipal.principal I
  have hmem : ∀ n : ℤ, A.valuation (n : Ω) < 1 ↔ a ∣ n := by
    intro n
    have h1 := hP (n : 𝓞 E)
    have h2 : (algebraMap E Ω) (((n : 𝓞 E)) : E) = (n : Ω) := by simp
    rw [h2] at h1
    rw [h1]
    have h3 : (n : 𝓞 E) ∈ P.asIdeal ↔ n ∈ I := by simp [I]
    rw [h3, ha, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨k, rfl⟩; exact Dvd.intro_left k rfl
    · rintro ⟨k, rfl⟩; exact ⟨k, by rw [smul_eq_mul, mul_comm]⟩
  refine ⟨a.natAbs, ?_, ?_, fun n => by rw [hmem n, Int.natAbs_dvd]⟩
  · intro h0
    have ha0 : a = 0 := Int.natAbs_eq_zero.mp h0
    have hN := Ideal.absNorm_mem P.asIdeal
    have hNv : A.valuation (((Ideal.absNorm P.asIdeal : ℕ) : ℤ) : Ω) < 1 := by
      have h1 := (hP ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E)).mpr hN
      simpa using h1
    rw [hmem, ha0, zero_dvd_iff] at hNv
    have : Ideal.absNorm P.asIdeal = 0 := by exact_mod_cast hNv
    exact P.ne_bot (Ideal.absNorm_eq_zero_iff.mp this)
  · intro h1
    have : A.valuation ((1 : ℤ) : Ω) < 1 := by
      rw [hmem, ← Int.natAbs_dvd, h1]; simp
    simp at this

end GlobalTheory.MaxIdealPow

namespace GlobalTheory.MaxIdealPow

theorem exists_pow_lt_valuation : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A P → ∀ x c : Ω, IsIntegral ℤ x → IsIntegral ℤ c → c ≠ 0 → A.valuation x < 1 → ∃ k : ℕ, A.valuation x ^ k < A.valuation c := by
  intro E Ω _ _ _ _ _ A P hP x c hx hc hc0 hvx
  obtain ⟨p, hp0, hp1, hpv⟩ := exists_nat_of_isPlaceOver E A P hP
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have hvp : A.valuation (p : Ω) < 1 := by
    have := (hpv p).2 dvd_rfl
    simpa using this
  have hvp0 : A.valuation (p : Ω) ≠ 0 := by
    rw [Valuation.ne_zero_iff]; exact_mod_cast hp0
  have hunit : ∀ n : ℤ, ¬ (p : ℤ) ∣ n → A.valuation (n : Ω) = 1 := fun n hn =>
    le_antisymm ((A.valuation_le_one_iff _).2 (intCast_mem A n))
      (not_lt.1 (fun h => hn ((hpv n).1 h)))
  have hxA : x ∈ A := ReciprocityTheory.Gal.mem_of_isIntegral_int A hx
  have hcA : c ∈ A := ReciprocityTheory.Gal.mem_of_isIntegral_int A hc

  have hstep2 : ∃ s : ℕ, A.valuation x ^ s ≤ A.valuation (p : Ω) := by
    haveI : Fact (1 < p) := ⟨by omega⟩
    let f := minpoly ℤ x
    have hfm : f.Monic := minpoly.monic hx
    let fb := f.map (Int.castRingHom (ZMod p))
    have hfb0 : fb ≠ 0 := (hfm.map _).ne_zero
    obtain ⟨q, hq, hqX⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd fb hfb0 0
    simp only [map_zero, sub_zero] at hq hqX
    set s := rootMultiplicity 0 fb
    have hq0 : q.coeff 0 ≠ 0 := fun h => hqX (X_dvd_iff.mpr h)
    obtain ⟨g, hg⟩ := map_surjective (Int.castRingHom (ZMod p)) ZMod.intCast_surjective q
    have hker : f - X ^ s * g ∈ RingHom.ker (mapRingHom (Int.castRingHom (ZMod p))) := by
      rw [RingHom.mem_ker, coe_mapRingHom, Polynomial.map_sub, Polynomial.map_mul,
        Polynomial.map_pow, map_X, hg]
      exact sub_eq_zero.mpr hq
    rw [ker_mapRingHom, ZMod.ker_intCastRingHom, Ideal.map_span, Set.image_singleton,
      Ideal.mem_span_singleton] at hker
    obtain ⟨h, hh⟩ := hker
    have hev := congrArg (aeval x) hh
    rw [map_sub, map_mul, map_pow, aeval_X, minpoly.aeval, map_mul, aeval_C] at hev
    have hg0 : ¬ (p : ℤ) ∣ g.coeff 0 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      intro h0; apply hq0; rw [← hg, coeff_map]; simpa using h0
    obtain ⟨w, hwA, hw⟩ := aeval_eq_coeff_zero_add A g hxA
    have hvg : A.valuation (aeval x g) = 1 := by
      rw [hw, Valuation.map_add_eq_of_lt_left, hunit _ hg0]
      rw [hunit _ hg0, Valuation.map_mul]
      calc A.valuation x * A.valuation w ≤ A.valuation x * 1 :=
            mul_le_of_le_one_right' ((A.valuation_le_one_iff _).2 hwA) |>.trans_eq (mul_one _).symm
        _ = A.valuation x := mul_one _
        _ < 1 := hvx
    have hhA : aeval x h ∈ A := by
      obtain ⟨w', hw'A, hw'⟩ := aeval_eq_coeff_zero_add A h hxA
      rw [hw']; exact add_mem (intCast_mem A _) (mul_mem hxA hw'A)
    refine ⟨s, ?_⟩
    have hev2 : x ^ s * aeval x g = -((algebraMap ℤ Ω p) * aeval x h) := by
      rw [← hev]; ring
    have := congrArg A.valuation hev2
    rw [Valuation.map_neg, Valuation.map_mul, Valuation.map_mul, Valuation.map_pow, hvg,
      mul_one] at this
    rw [this]
    have hp' : (algebraMap ℤ Ω (p : ℤ)) = (p : Ω) := by simp
    rw [hp']
    calc A.valuation (p : Ω) * A.valuation (aeval x h) ≤ A.valuation (p : Ω) * 1 :=
          mul_le_of_le_one_right' ((A.valuation_le_one_iff _).2 hhA) |>.trans_eq (mul_one _).symm
      _ = A.valuation (p : Ω) := mul_one _

  have hstep3 : ∃ t : ℕ, A.valuation (p : Ω) ^ t ≤ A.valuation c := by
    let f := minpoly ℤ c
    have hf0 : f ≠ 0 := (minpoly.monic hc).ne_zero
    obtain ⟨f₁, hf, hfX⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd f hf0 0
    simp only [map_zero, sub_zero] at hf hfX
    have ha0 : f₁.coeff 0 ≠ 0 := fun h => hfX (X_dvd_iff.mpr h)
    have hev : aeval c f₁ = 0 := by
      have h1 := minpoly.aeval ℤ c
      change aeval c f = 0 at h1
      rw [hf, map_mul, map_pow, aeval_X] at h1
      exact (mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ hc0)
    obtain ⟨w, hwA, hw⟩ := aeval_eq_coeff_zero_add A f₁ hcA
    rw [hev] at hw
    have hle : A.valuation ((f₁.coeff 0 : ℤ) : Ω) ≤ A.valuation c := by
      have he : ((f₁.coeff 0 : ℤ) : Ω) = -(c * w) := by linear_combination -hw
      rw [he, Valuation.map_neg, Valuation.map_mul]
      calc A.valuation c * A.valuation w ≤ A.valuation c * 1 :=
            mul_le_of_le_one_right' ((A.valuation_le_one_iff _).2 hwA) |>.trans_eq (mul_one _).symm
        _ = A.valuation c := mul_one _
    have hn0 : (f₁.coeff 0).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr ha0
    obtain ⟨t, u, hu, hfac⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 p hp1
    refine ⟨t, le_trans (le_of_eq ?_) hle⟩
    have habs : A.valuation ((f₁.coeff 0 : ℤ) : Ω) = A.valuation (((f₁.coeff 0).natAbs : ℤ) : Ω) := by
      rcases Int.natAbs_eq (f₁.coeff 0) with h | h
      · rw [← h]
      · conv_lhs => rw [h]
        rw [Int.cast_neg, Valuation.map_neg]
    rw [habs, hfac]
    have hu1 : A.valuation ((u : ℤ) : Ω) = 1 := hunit u (by exact_mod_cast hu)
    push_cast
    rw [Valuation.map_mul, Valuation.map_pow]
    push_cast at hu1
    rw [hu1, mul_one]
  obtain ⟨s, hs⟩ := hstep2
  obtain ⟨t, ht⟩ := hstep3
  refine ⟨s * (t + 1), ?_⟩
  calc A.valuation x ^ (s * (t + 1)) = (A.valuation x ^ s) ^ (t + 1) := pow_mul _ _ _
    _ ≤ A.valuation (p : Ω) ^ (t + 1) := pow_le_pow_left₀ zero_le' hs _
    _ = A.valuation (p : Ω) ^ t * A.valuation (p : Ω) := pow_succ _ _
    _ < A.valuation (p : Ω) ^ t * 1 :=
        mul_lt_mul_of_pos_left hvp (zero_lt_iff.mpr (pow_ne_zero _ hvp0))
    _ = A.valuation (p : Ω) ^ t := mul_one _
    _ ≤ A.valuation c := ht

end GlobalTheory.MaxIdealPow
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowValuationLtOfIntegralAlgClosurePlaceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.exists_pow_valuation_lt_of_integral_algClosure_place : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A P → ∀ x c : Ω, IsIntegral ℤ x → IsIntegral ℤ c → c ≠ 0 → A.valuation x < 1 → ∃ k : ℕ, A.valuation x ^ k < A.valuation c := by
  first | exact @GlobalTheory.MaxIdealPow.exists_pow_lt_valuation | exact GlobalTheory.MaxIdealPow.exists_pow_lt_valuation | (intros; apply GlobalTheory.MaxIdealPow.exists_pow_lt_valuation <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegerDeepAtOnePlaceUnitAtOther

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.TwoPlaces

theorem exists_deep_one_sub :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A A' : ValuationSubring Ω)
      (P : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A P → IsPlaceOver (F := E) A' P → A ≠ A' →
      ∀ c : Ω, IsIntegral ℤ c → c ≠ 0 →
        ∃ e : Ω, IsIntegral ℤ e ∧ A.valuation e < A.valuation c ∧ A'.valuation (1 - e) < 1 := by
  intro E Ω _ _ _ _ _ A A' P hA hA' hne c hc hc0
  have hQ : (primeBelow (F := E) A).under (𝓞 E) = P.asIdeal := under_primeBelow hA
  have hQ' : (primeBelow (F := E) A').under (𝓞 E) = P.asIdeal := under_primeBelow hA'
  haveI : (primeBelow (F := E) A).IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := 𝓞 E) _
      (by change (Ideal.under (𝓞 E) (primeBelow (F := E) A)).IsMaximal; rw [hQ]; exact P.isMaximal)
  haveI : (primeBelow (F := E) A').IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := 𝓞 E) _
      (by change (Ideal.under (𝓞 E) (primeBelow (F := E) A')).IsMaximal; rw [hQ']; exact P.isMaximal)
  have hQne : primeBelow (F := E) A ≠ primeBelow (F := E) A' := by
    intro h
    apply hne
    refine eq_of_valuation_lt_one_iff E fun b hb => ?_
    have hb' : IsIntegral (𝓞 E) b := hb.tower_top
    have := congrArg (fun I : Ideal (IntCl E Ω) => (⟨b, hb'⟩ : IntCl E Ω) ∈ I) h
    simpa [mem_primeBelow] using this
  have hnle : ¬ primeBelow (F := E) A ≤ primeBelow (F := E) A' := fun h =>
    hQne (Ideal.IsMaximal.eq_of_le inferInstance (Ideal.IsPrime.ne_top inferInstance) h)
  obtain ⟨x, hxQ, hxQ'⟩ := SetLike.not_le_iff_exists.mp hnle
  rw [mem_primeBelow] at hxQ
  obtain ⟨k, hk⟩ := GlobalTheory.T.exists_pow_valuation_lt_of_integral_algClosure_place E Ω A P hA (x : Ω) c (isIntegral_int_of_isIntegral x.2) hc hc0 hxQ
  have hxk : x ^ k ∉ primeBelow (F := E) A' := fun h => hxQ' (Ideal.IsPrime.mem_of_pow_mem inferInstance k h)
  obtain ⟨y, i, hi, hyi⟩ := Ideal.IsMaximal.exists_inv inferInstance hxk
  refine ⟨((y * x ^ k : IntCl E Ω) : Ω), isIntegral_int_of_isIntegral (y * x ^ k).2, ?_, ?_⟩
  · rw [MulMemClass.coe_mul, Valuation.map_mul, SubmonoidClass.coe_pow, Valuation.map_pow]
    calc A.valuation (y : Ω) * A.valuation (x : Ω) ^ k ≤ 1 * A.valuation (x : Ω) ^ k :=
          mul_le_mul_left (valuation_le_one_intCl A y) _
      _ < A.valuation c := by rw [one_mul]; exact hk
  · have e1 : (1 : Ω) - ((y * x ^ k : IntCl E Ω) : Ω) = (i : Ω) := by
      have := congrArg (fun z : IntCl E Ω => (z : Ω)) hyi
      simp only [AddMemClass.coe_add, OneMemClass.coe_one] at this
      rw [← this]; ring
    rw [e1]
    exact hi

end GlobalTheory.TwoPlaces
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegerDeepAtOnePlaceUnitAtOtherStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.exists_integer_deep_at_one_place_unit_at_other : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A A' : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A P → IsPlaceOver (F := E) A' P → A ≠ A' → ∀ c : Ω, IsIntegral ℤ c → c ≠ 0 → ∃ e : Ω, IsIntegral ℤ e ∧ A.valuation e < A.valuation c ∧ A'.valuation (1 - e) < 1 := by
  first | exact @GlobalTheory.TwoPlaces.exists_deep_one_sub | exact GlobalTheory.TwoPlaces.exists_deep_one_sub | (intros; apply GlobalTheory.TwoPlaces.exists_deep_one_sub <;> assumption)
end
end
