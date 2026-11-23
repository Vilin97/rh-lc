module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PrimeProj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.AuxiliaryInertOddPrime
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PArithK
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PAuxPrime
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.AuxiliaryInertOddPrime
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagHermitianTrivialOfSumFourSquares
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ApartAllEmpty
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PadicUnitNorm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.CodiffUnit
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.SetupBasicHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.MemIffDvd
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.DatExOf
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PCjMem
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DiscriminantMulIntegralMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.SetupBasicHolds

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PRootAt

section

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1 UpperTheory.Gal.Int.Geo GlobalTheory.CongL
open scoped TensorProduct

theorem UpperTheory.Gal.G1.pRootAt :
    RootAt := by
  intro E _ _ _ A q _ hs w hw
  obtain ⟨_, r, k, hk⟩ := hs
  have hkE : (r : 𝓞 E) ^ 2 - (A.tr : 𝓞 E) * (r : 𝓞 E) + (A.nm : 𝓞 E) = (q : 𝓞 E) * (k : 𝓞 E) := by
    exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) hk
  have hprod : (A.ω - (r : 𝓞 E)) * (A.ω - ((A.tr - r : ℤ) : 𝓞 E)) = (q : 𝓞 E) * (-(k : 𝓞 E)) := by
    have htr := A.tr_eq
    have hnm := A.nm_eq
    have h0 : A.ω ^ 2 - (A.tr : 𝓞 E) * A.ω + (A.nm : 𝓞 E) = 0 := by
      rw [← htr, ← hnm]; ring
    push_cast
    linear_combination h0 - hkE
  have hmem : (A.ω - (r : 𝓞 E)) * (A.ω - ((A.tr - r : ℤ) : 𝓞 E)) ∈ w.asIdeal := by
    rw [hprod]; exact w.asIdeal.mul_mem_right _ hw
  rcases w.isPrime.mem_or_mem hmem with h | h
  · exact ⟨r, ⟨k, hk⟩, h⟩
  · refine ⟨A.tr - r, ⟨k, ?_⟩, h⟩
    rw [← hk]; ring
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PScOf

section

@[expose] public section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1 UpperTheory.Gal.Int.Geo GlobalTheory.CongL
open scoped TensorProduct

theorem UpperTheory.Gal.G1.pScOf :
    SetupBasic → ScOf := by
  intro hB E _ _ _ hev A n p _ S hn
  obtain ⟨hga, -, hc⟩ := hB E A n p S
  have hmul : Module.finrank ℚ (maximalRealSubfield E) * Module.finrank (maximalRealSubfield E) E =
      Module.finrank ℚ E := (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E)
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hpos : 0 < Module.finrank ℚ (maximalRealSubfield E) := Module.finrank_pos
  have hlt : 2 < Module.finrank ℚ E := by
    obtain ⟨k, hk⟩ := hev
    rw [← hmul, h2]
    omega
  exact ⟨rfl, rfl, hga, hn, (hc hlt).2⟩
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.ExistsAuxiliaryPrime

section

@[expose] public section

open UpperTheory.Gal.W2.Seed

namespace UpperTheory.Gal.G1

theorem exists_auxiliary_prime : AuxiliaryInertOddPrime := exists_auxiliary_prime_cmDatum
theorem ArithK_holds : ArithK := pArithK BarEx_holds QuadEx_holds CEx_holds UnitMod_holds CodiffGen_holds CodiffUnit_holds IdemEx_holds RealGen_holds PosGen_holds DeltaEx_holds PerfOf_holds
theorem ScOf_holds : ScOf := pScOf SetupBasic_holds
theorem RootAt_holds : RootAt := pRootAt

end UpperTheory.Gal.G1
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PBarAdj

section

@[expose] public section

open NumberField IsDedekindDomain UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1 UpperTheory.Gal.Int.Geo GlobalTheory.CongL GlobalTheory.UnitaryBC

theorem UpperTheory.Gal.G1.pBarAdj :
    DiscInt → BarAdj := by
  intro h E _ _ _ A y hy
  obtain ⟨a, b, hab⟩ := h E A y hy
  have hD : (((A.tr ^ 2 - 4 * A.nm : ℤ)) : E) ≠ 0 := by
    exact_mod_cast ne_of_lt A.disc_neg
  have hb : A.bar A.ω = (A.tr : 𝓞 E) - A.ω := by
    rw [← A.tr_eq]; ring
  have h1 := congrArg A.bar hab
  simp only [map_mul, map_add (f := _), map_intCast] at h1
  rw [hb] at h1
  have h2 : (((A.tr ^ 2 - 4 * A.nm : ℤ)) : E) * ((A.bar y : 𝓞 E) : E)
      = (a : E) + (b : E) * ((A.tr : E) - (A.ω : E)) := by
    have h3 := congrArg (algebraMap (𝓞 E) E) h1
    simpa only [map_mul, map_add (f := _), map_sub, map_intCast] using h3
  have e : ((A.bar y : 𝓞 E) : E)
      = ((a : E) + (b : E) * ((A.tr : E) - (A.ω : E))) / (((A.tr ^ 2 - 4 * A.nm : ℤ)) : E) := by
    rw [← h2, mul_div_cancel_left₀ _ hD]
  rw [e]
  exact div_mem (add_mem (intCast_mem _ _) (mul_mem (intCast_mem _ _)
    (sub_mem (intCast_mem _ _) (IntermediateField.mem_adjoin_simple_self ℚ _)))) (intCast_mem _ _)
end
end

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PDiscInt

section

@[expose] public section

theorem UpperTheory.Reformulated.B.Qk39.pDiscInt :
    UpperTheory.Gal.G1.DiscInt := by
  intro E _ _ _ A y hy
  have h1 := congrArg (fun x : NumberField.RingOfIntegers E => (x : E)) A.tr_eq
  have h2 := congrArg (fun x : NumberField.RingOfIntegers E => (x : E)) A.nm_eq
  simp only [map_add (f := _), map_mul, map_intCast] at h1 h2
  obtain ⟨a, b, h⟩ := UpperTheory.discriminant_mul_integral_mem E (UpperTheory.Gal.W2.Seed.cj E) (A.ω : E) (y : E) A.tr A.nm
    (by rw [← h1]; exact congrArg _ (A.bar_eq _).symm) (by rw [← h2]; exact congrArg _ (A.bar_eq _).symm)
    (NumberField.RingOfIntegers.isIntegral_coe y) hy
  refine ⟨a, b, NumberField.RingOfIntegers.coe_injective ?_⟩
  simp only [map_add (f := _), map_mul, map_intCast]
  exact h
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PDiscInt

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain UpperTheory.Gal.W2.Seed

namespace UpperTheory.Gal.G1

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem pDiscInt : DiscInt :=
  _root_.UpperTheory.Reformulated.B.Qk39.pDiscInt

end UpperTheory.Gal.G1
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PSides

section

@[expose] public section

open NumberField IsDedekindDomain UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1 UpperTheory.Gal.Int.Geo GlobalTheory.CongL GlobalTheory.UnitaryBC

theorem UpperTheory.Gal.G1.pSides :
    CjMem → BarAdj → KeyK → RootAt → Pl.Sides := by
  intro hCj hBar hKey hRoot E _ _ _ A x hG q hq hs w hw
  have hadj : IntermediateField.adjoin ℚ {x} = IntermediateField.adjoin ℚ {(A.ω : E)} :=
    le_antisymm (IntermediateField.adjoin_simple_le_iff.2 hG.2) (IntermediateField.adjoin_simple_le_iff.2 hG.1)
  have hS : ∀ u u' : HeightOneSpectrum (𝓞 E), CertificateRingHomMap.SameK x u u' ↔
      ∀ y : 𝓞 E, (y : E) ∈ IntermediateField.adjoin ℚ {(A.ω : E)} → (y ∈ u.asIdeal ↔ y ∈ u'.asIdeal) := fun u u' => by
    unfold CertificateRingHomMap.SameK
    rw [hadj]
  have hnd := hs.1
  have hmemω : ∀ s : ℤ, ((A.ω - (s : 𝓞 E) : 𝓞 E) : E) ∈ IntermediateField.adjoin ℚ {(A.ω : E)} := fun s => by
    have e : ((A.ω - (s : 𝓞 E) : 𝓞 E) : E) = (A.ω : E) - (s : E) := by
      change algebraMap (𝓞 E) E _ = algebraMap (𝓞 E) E _ - _
      simp
    rw [e]
    exact sub_mem (IntermediateField.mem_adjoin_simple_self ℚ _) (intCast_mem _ s)
  have hmemq : ((q : 𝓞 E) : E) ∈ IntermediateField.adjoin ℚ {(A.ω : E)} := by
    have e : ((q : 𝓞 E) : E) = (q : E) := by
      change algebraMap (𝓞 E) E _ = _
      simp
    rw [e]
    exact natCast_mem _ q
  have hbarI : ∀ s : ℤ, A.bar (s : 𝓞 E) = (s : 𝓞 E) := fun s => map_intCast A.bar s
  have hbarN : A.bar (q : 𝓞 E) = (q : 𝓞 E) := map_natCast A.bar q
  have hbarω : A.bar A.ω = (A.tr : 𝓞 E) - A.ω := by
    rw [← A.tr_eq]; ring
  have hbarsub : ∀ s : ℤ, A.bar (A.ω - (s : 𝓞 E)) = (A.tr : 𝓞 E) - A.ω - (s : 𝓞 E) := fun s => by
    rw [map_sub, hbarω, hbarI]
  have hquad : A.ω ^ 2 - (A.tr : 𝓞 E) * A.ω + (A.nm : 𝓞 E) = 0 := by
    rw [← A.tr_eq, ← A.nm_eq]; ring
  obtain ⟨r, hr, hrw⟩ := hRoot E A q hq hs w hw
  have hne1 : ¬ CertificateRingHomMap.SameK x (CertificateRingHomMap.cj w) w := by
    intro h
    have h1 : A.ω - (r : 𝓞 E) ∈ (CertificateRingHomMap.cj w).asIdeal := ((hS _ _).1 h _ (hmemω r)).2 hrw
    have h2 : (A.tr : 𝓞 E) - A.ω - (r : 𝓞 E) ∈ w.asIdeal := by
      rw [← hbarsub]; exact (hCj E A w _).1 h1
    have h3 : ((2 : 𝓞 E) * A.ω - (A.tr : 𝓞 E)) ∈ w.asIdeal := by
      have := w.asIdeal.sub_mem hrw h2
      have e : A.ω - (r : 𝓞 E) - ((A.tr : 𝓞 E) - A.ω - (r : 𝓞 E)) = (2 : 𝓞 E) * A.ω - (A.tr : 𝓞 E) := by ring
      rwa [e] at this
    have h4 : ((A.tr ^ 2 - 4 * A.nm : ℤ) : 𝓞 E) ∈ w.asIdeal := by
      have := w.asIdeal.mul_mem_left ((2 : 𝓞 E) * A.ω - (A.tr : 𝓞 E)) h3
      have e : ((A.tr ^ 2 - 4 * A.nm : ℤ) : 𝓞 E) = ((2 : 𝓞 E) * A.ω - (A.tr : 𝓞 E)) * ((2 : 𝓞 E) * A.ω - (A.tr : 𝓞 E)) - 4 * (A.ω ^ 2 - (A.tr : 𝓞 E) * A.ω + (A.nm : 𝓞 E)) * (-1) - 8 * (A.ω ^ 2 - (A.tr : 𝓞 E) * A.ω + (A.nm : 𝓞 E)) := by
        push_cast; ring
      rw [e, hquad]
      simpa using this
    obtain ⟨a, b, hab⟩ := ((Nat.prime_iff_prime_int.1 hq).irreducible.coprime_iff_not_dvd).2 hnd
    have h5 : (1 : 𝓞 E) ∈ w.asIdeal := by
      have e : (1 : 𝓞 E) = (a : 𝓞 E) * (q : 𝓞 E) + (b : 𝓞 E) * ((A.tr ^ 2 - 4 * A.nm : ℤ) : 𝓞 E) := by
        exact_mod_cast (congrArg (Int.cast : ℤ → 𝓞 E) hab).symm
      rw [e]
      exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ hw) (w.asIdeal.mul_mem_left _ h4)
    exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h5)
  refine ⟨hne1, ?_, ?_, ?_, ?_, ⟨r, hr, hrw⟩, ?_⟩
  · refine ⟨CertificateRingHomMap.cj w, fun h => hne1 (by rw [h]; exact fun _ _ => Iff.rfl), ?_⟩
    exact GlobalTheory.DefU.ClassFin.under_conjSrc _ (fun y => (IsCMField.complexConj E).commutes y) w
  · intro u hu
    obtain ⟨k, hk⟩ := hr
    have hkE : (r : 𝓞 E) ^ 2 - (A.tr : 𝓞 E) * (r : 𝓞 E) + (A.nm : 𝓞 E) = (q : 𝓞 E) * (k : 𝓞 E) := by
      exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) hk
    have hprod : (A.ω - (r : 𝓞 E)) * (A.ω - ((A.tr - r : ℤ) : 𝓞 E)) = (q : 𝓞 E) * (-(k : 𝓞 E)) := by
      push_cast
      linear_combination hquad - hkE
    have hmem : (A.ω - (r : 𝓞 E)) * (A.ω - ((A.tr - r : ℤ) : 𝓞 E)) ∈ u.asIdeal := by
      rw [hprod]; exact u.asIdeal.mul_mem_right _ hu
    rcases u.isPrime.mem_or_mem hmem with h | h
    · exact Or.inl ((hS _ _).2 (hKey E A q hq hnd r u w hu hw h hrw))
    · refine Or.inr ((hS _ _).2 (hKey E A q hq hnd r (CertificateRingHomMap.cj u) w ?_ hw ?_ hrw))
      · rw [hCj E A u, hbarN]; exact hu
      · rw [hCj E A u, hbarsub]
        have e : (A.tr : 𝓞 E) - A.ω - (r : 𝓞 E) = -(A.ω - ((A.tr - r : ℤ) : 𝓞 E)) := by
          push_cast; ring
        rw [e]
        exact u.asIdeal.neg_mem h
  · intro u h
    exact ((hS _ _).1 h _ hmemq).2 hw
  · intro u u' h y hy
    rw [hadj] at hy
    rw [hCj E A u, hCj E A u']
    exact (hS _ _).1 h _ (hBar E A y hy)
  · intro s hsw u
    constructor
    · intro h
      exact ⟨((hS _ _).1 h _ hmemq).2 hw, ((hS _ _).1 h _ (hmemω s)).2 hsw⟩
    · rintro ⟨h1, h2⟩
      exact (hS _ _).2 (hKey E A q hq hnd s u w h1 hw h2 hsw)
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PDatEx

section

@[expose] public section

open UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1

namespace UpperTheory.Gal.Int.Geo.Pl

theorem datEx_holds : DatEx := datEx_of exists_auxiliary_prime ArithK_holds SetupEx_holds ScOf_holds PerfCof_holds

theorem sides_holds : Sides := pSides pCjMem (pBarAdj pDiscInt) (pKeyK pDiscInt) RootAt_holds

end UpperTheory.Gal.Int.Geo.Pl
end
end
