module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.IneFixRoots
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.DecGen
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
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocallyConstantOfKernel
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.DecZhat
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Connected.Separation
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnitaryThreeReflectionRight

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DfExistsPrime

section

@[expose] public section

theorem UpperTheory.Reformulated.B.Qj5.df_exists_prime :
    ∀
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (n : ℕ),
    n ≠ (0 : ℕ) →
      (↑n : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal →
        ∃ (p : ℕ), Nat.Prime p ∧ p ∣ n ∧ (↑p : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal := by
  intro v n
  induction n using induction_on_primes with
  | zero => intro h; exact absurd rfl h
  | one =>
    intro _ h
    rw [Nat.cast_one] at h
    exact absurd ((Ideal.eq_top_iff_one _).2 h) v.isPrime.ne_top
  | prime_mul p a hp ih =>
    intro h0 h
    rw [Nat.cast_mul] at h
    rcases v.isPrime.mem_or_mem h with h | h
    · exact ⟨p, hp, Dvd.intro _ rfl, h⟩
    · obtain ⟨q, hq, hqa, hqv⟩ := ih (right_ne_zero_of_mul h0) h
      exact ⟨q, hq, Dvd.dvd.mul_left hqa p, hqv⟩
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsDecompositionFieldFrobeniusData

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

open Formalism.GaloisCohomology in
theorem UpperTheory.exists_decompositionField_frobenius_data :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 ℚ)), IsPlaceOver A v →
          CompactSpace (Dec (F := ℚ) A) ∧ ((Ine (F := ℚ) A).subgroupOf (Dec (F := ℚ) A)).Normal ∧ IsClosed (Ine (F := ℚ) A : Set (G ℚ Ω)) ∧
          (∃ fr : Dec (F := ℚ) A, ((Ine (F := ℚ) A).subgroupOf (Dec (F := ℚ) A) ⊔ Subgroup.zpowers fr).topologicalClosure = ⊤) ∧
          ∀ n : ℕ, 0 < n → ∃ U : Subgroup (Dec (F := ℚ) A), IsOpen (U : Set (Dec (F := ℚ) A)) ∧ (Ine (F := ℚ) A).subgroupOf (Dec (F := ℚ) A) ≤ U ∧ U.index = n := by
  intro Ω _ _ _ A v hv
  haveI : IsGalois ℚ Ω := {}
  obtain ⟨φ, -, h1, h2⟩ := UpperTheory.V.GC.decZhat ℚ Ω v A hv
  refine ⟨isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact, inferInstance, isClosed_Ine A, ⟨φ, h1⟩,
    fun n hn => ?_⟩
  obtain ⟨d, hd, hI, hφ⟩ := h2 n hn
  haveI : NeZero n := ⟨hn.ne'⟩
  refine ⟨d.ker, hd {1}, fun s hs => hI s hs, ?_⟩
  have hs : d.range = ⊤ := by
    rw [eq_top_iff]
    intro x _
    refine ⟨φ ^ (Multiplicative.toAdd x).val, ?_⟩
    rw [map_pow, hφ, ← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]
  rw [Subgroup.index_ker, hs, Subgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
end
end
