module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RbUVal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.OrbIndex
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.SupIndex
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.DecCyc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DecInf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.ClosedInf
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
import Mathlib.FieldTheory.Galois.Profinite
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.NcardPlacesDividingLeOfOrbitBound
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.DecIdx

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

theorem UpperTheory.V.Ws.index_cyclotomicKer_sup_decompositionGroup_ne_zero :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (p : ℕ) (A : ValuationSubring Ω), p.Prime → A.valuation (p : Ω) < 1 → ((cycZ ℚ Ω l).ker ⊔ Dec (F := ℚ) A).index ≠ 0 := by
  intro Ω _ _ _ l _ p A hp hA
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have hg : ∃ g ∈ Dec (F := ℚ) A, ¬ IsOfFinOrder (cycZ ℚ Ω l g) := by
    by_cases hlp : l = p
    · subst hlp
      obtain ⟨g, hg, hf⟩ := UpperTheory.V.Base.decInf ℚ Ω l ⊤ isOpen_univ A hA
      exact ⟨g, hg.2, hf⟩
    · obtain ⟨-, -, γ, hγ, -, hc⟩ := UpperTheory.V.Chr.decCyc Ω p A hp hA
      refine ⟨γ, hγ, fun hf => ?_⟩
      obtain ⟨n, hn, e⟩ := isOfFinOrder_iff_pow_eq_one.1 hf
      have h3 := congrArg (Units.val : ℤ_[l]ˣ → ℤ_[l]) e
      rw [Units.val_pow_eq_pow_val, hc l hlp, Units.val_one] at h3
      have h4 : p ^ n = 1 := by exact_mod_cast h3
      exact (Nat.one_lt_pow hn.ne' hp.one_lt).ne' h4
  obtain ⟨g, hg, hf⟩ := hg
  have hcl : IsClosed (((Dec (F := ℚ) A).map (cycZ ℚ Ω l) : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) :=
    ((isClosed_Dec (F := ℚ) A).isCompact.image (continuous_cycZ ℚ Ω l)).isClosed
  have h0 := UpperTheory.V.Ws.index_ne_zero_of_isClosed_of_not_isOfFinOrder l _ hcl ⟨_, ⟨g, hg, rfl⟩, hf⟩
  have e : (cycZ ℚ Ω l).ker ⊔ Dec (F := ℚ) A = ((Dec (F := ℚ) A).map (cycZ ℚ Ω l)).comap (cycZ ℚ Ω l) := by
    rw [Subgroup.comap_map_eq, sup_comm]
  rw [e, Subgroup.index_comap]
  have hrel0 : ((Dec (F := ℚ) A).map (cycZ ℚ Ω l)).relIndex ⊤ ≠ 0 := by rwa [Subgroup.relIndex_top_right]
  exact fun h => hrel0 (Subgroup.relIndex_eq_zero_of_le_right le_top h)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.PlacesBd

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private theorem plDvd_eq (F : Type) [Field F] (N : ℕ) (hN : N ≠ 0) :
    plDvd F N = ⋃ p ∈ N.primeFactors, plDvd F p := by
  ext v
  simp only [plDvd, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  constructor
  · have key : ∀ M : ℕ, M ≠ 0 → ((M : 𝓞 F) ∈ v.asIdeal) →
        ∃ p ∈ M.primeFactors, (p : 𝓞 F) ∈ v.asIdeal := by
      intro M
      induction M using Nat.strong_induction_on with
      | _ M ih =>
        intro hM hv
        by_cases h1 : M = 1
        · subst h1
          rw [Nat.cast_one] at hv
          exact (v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 hv)).elim
        · obtain ⟨p, hp, m, rfl⟩ := Nat.exists_prime_and_dvd h1
          rw [Nat.cast_mul] at hv
          rcases v.isPrime.mem_or_mem hv with h | h
          · exact ⟨p, Nat.mem_primeFactors.2 ⟨hp, dvd_mul_right p m, hM⟩, h⟩
          · have hm0 : m ≠ 0 := by
              rintro rfl
              simp at hM
            have hlt : m < p * m := by
              have := hp.two_le
              have := Nat.pos_of_ne_zero hm0
              nlinarith
            obtain ⟨q, hq, hqv⟩ := ih m hlt hm0 h
            have hq' := Nat.mem_primeFactors.1 hq
            exact ⟨q, Nat.mem_primeFactors.2 ⟨hq'.1, hq'.2.1.mul_left p, hM⟩, hqv⟩
    exact key N hN
  · rintro ⟨p, hp, hpv⟩
    obtain ⟨m, hm⟩ := (Nat.mem_primeFactors.1 hp).2.1
    rw [hm, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hpv

theorem UpperTheory.V.Ws.exists_uniform_bound_ncard_placesDividing :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (U : Subgroup (G ℚ Ω)) (N : ℕ), U.Normal → IsOpen (U : Set (G ℚ Ω)) → N ≠ 0 → ∃ g : ℕ, ∀ (F : IntermediateField ℚ Ω) [NumberField F], cycU l U ≤ F.fixingSubgroup → (plDvd F N).ncard ≤ g := by
  intro Ω _ _ _ l _ U N hUn hUo hN
  haveI := hUn
  haveI : (cycU l U).Normal := by
    unfold cycU
    infer_instance
  have hUi : U.index ≠ 0 := by
    haveI := Subgroup.quotient_finite_of_isOpen U hUo
    exact Subgroup.index_ne_zero_of_finite
  have hUle : ∀ {X : Type} (s : Finset ℕ) (f : ℕ → Set X),
      (⋃ p ∈ s, f p).ncard ≤ ∑ p ∈ s, (f p).ncard := by
    intro X s f
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro a s ha ih
      rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
      exact (Set.ncard_union_le _ _).trans (Nat.add_le_add_left ih _)
  have hb : ∀ p : ℕ, ∃ n, p.Prime → OrbLe (cycU l U) p n := by
    intro p
    by_cases hA : ∃ A₀ : ValuationSubring Ω, A₀.valuation (p : Ω) < 1
    · obtain ⟨A₀, hA₀⟩ := hA
      refine ⟨(cycU l U ⊔ Dec A₀).index, fun hp => ?_⟩
      have hK := index_cyclotomicKer_sup_decompositionGroup_ne_zero Ω l p A₀ hp hA₀
      have hs := supIndex (G ℚ Ω) (cycZ ℚ Ω l).ker U (Dec A₀) hUi hK
      exact orbIndex Ω p (cycU l U) A₀ hp hA₀ hs.1
    · exact ⟨0, fun _ => ⟨∅, by simp, by simp, fun A hA' => (hA ⟨A, hA'⟩).elim⟩⟩
  choose nf hnf using hb
  refine ⟨∑ p ∈ N.primeFactors, nf p, fun F _ hF => ?_⟩
  rw [plDvd_eq F N hN]
  refine (hUle _ _).trans (Finset.sum_le_sum fun p hp => ?_)
  have hpp := (Nat.mem_primeFactors.1 hp).1
  exact ncard_placesDividing_le_of_orbitBound Ω F (cycU l U) p (nf p) hpp.ne_zero hF (hnf p hpp)
end
end
