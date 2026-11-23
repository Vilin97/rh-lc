module

public import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularQuotientNearPrimeFiniteTypeIntStatement
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalFibreIsRegularRingEssFiniteTypeInt
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
import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularNearOfRegularQuotientPrime
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalFibreIsRegularRingEssFiniteTypeIntStatement

section

@[expose] public section

open IsLocalRing TensorProduct

theorem _root_.GlobalTheory.T.formalFibre_isRegularRing_essFiniteType_int : ∀ (R K : Type) [CommRing R] [IsLocalRing R] [Algebra.EssFiniteType ℤ R] [Field K] [Algebra R K] [Algebra.EssFiniteType R K], IsRegularRing (AdicCompletion (maximalIdeal R) R ⊗[R] K) := by
  first | exact @GlobalTheory.formalFibre_isRegularRing_of_essFiniteType_int | exact GlobalTheory.formalFibre_isRegularRing_of_essFiniteType_int | (intros; apply GlobalTheory.formalFibre_isRegularRing_of_essFiniteType_int <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeomRegFibOfIsRegularRingTensorEssFiniteType

section

@[expose] public section

open IsLocalRing TensorProduct ReciprocityTheory.AnForm.R

namespace GlobalTheory

theorem geomRegFib_of_isRegularRing_essFiniteType :
    ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B],
      (∀ (K : Type) [Field K] [Algebra R K] [Algebra.EssFiniteType R K], IsRegularRing (B ⊗[R] K)) →
        FinalTheorems.GeomRegFib R B := by
  intro R B _ _ _ h P _ K _ _ _ _ hfg
  haveI : Algebra.EssFiniteType P.ResidueField K := IntermediateField.fg_top_iff.mp hfg
  haveI : Algebra.EssFiniteType R K := Algebra.EssFiniteType.comp R P.ResidueField K
  haveI hr : IsRegularRing (B ⊗[R] K) := h K
  exact ⟨inferInstance, fun Q _ => hr.isRegularLocalRing_localization Q⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeomRegFibOfIsRegularRingTensorEssFiniteTypeStatement

section

@[expose] public section

open IsLocalRing TensorProduct ReciprocityTheory.AnForm.R

theorem _root_.GlobalTheory.T.geomRegFib_of_isRegularRing_tensor_essFiniteType : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B], (∀ (K : Type) [Field K] [Algebra R K] [Algebra.EssFiniteType R K], IsRegularRing (B ⊗[R] K)) → FinalTheorems.GeomRegFib R B := by
  first | exact @GlobalTheory.geomRegFib_of_isRegularRing_essFiniteType | exact GlobalTheory.geomRegFib_of_isRegularRing_essFiniteType | (intros; apply GlobalTheory.geomRegFib_of_isRegularRing_essFiniteType <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularNearOfRegularQuotientPrimeStatement

section

@[expose] public section

open IsLocalRing TensorProduct

theorem _root_.GlobalTheory.T.exists_regular_near_of_regular_quotient_prime : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (p : Ideal B) [p.IsPrime], IsRegularLocalRing (Localization.AtPrime p) → ∃ g, g ∉ p ∧ ∀ (q : Ideal B) [q.IsPrime], p ≤ q → g ∉ q → IsRegularLocalRing (Localization.AtPrime q ⧸ p.map (algebraMap B (Localization.AtPrime q))) → IsRegularLocalRing (Localization.AtPrime q) := by
  first | exact @GlobalTheory.RegularAscent.exists_regular_near_of_regular_quotient | exact GlobalTheory.RegularAscent.exists_regular_near_of_regular_quotient | (intros; apply GlobalTheory.RegularAscent.exists_regular_near_of_regular_quotient <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenOfStableUnderGeneralizationOfLocallyOpen

section

@[expose] public section

open IsLocalRing TensorProduct

namespace GlobalTheory

theorem isOpen_of_stableUnderGeneralization_of_locally_open_in_closure :
    ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (U : Set (PrimeSpectrum B)),
      (∀ p q : PrimeSpectrum B, p ≤ q → q ∈ U → p ∈ U) →
      (∀ p ∈ U, ∃ g, g ∉ p.asIdeal ∧ ∀ q : PrimeSpectrum B, p ≤ q → g ∉ q.asIdeal → q ∈ U) →
      IsOpen U := by
  intro B _ _ U hgen hloc
  classical
  set I := PrimeSpectrum.vanishingIdeal (Uᶜ) with hI
  have hIle : ∀ q : PrimeSpectrum B, q ∈ Uᶜ → I ≤ q.asIdeal := by
    intro q hq f hf
    exact (PrimeSpectrum.mem_vanishingIdeal _ f).1 hf q hq
  have key : ∀ x : PrimeSpectrum B, x.asIdeal ∈ I.minimalPrimes → x ∉ U := by
    intro x hx hxU
    obtain ⟨g, hg, hgU⟩ := hloc x hxU
    have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing B I
    set S := hfin.toFinset.erase x.asIdeal with hS
    have hJ : ¬ S.inf id ≤ x.asIdeal := by
      intro h
      obtain ⟨P, hPS, hPx⟩ := (Ideal.IsPrime.inf_le' x.isPrime).1 h
      have hPm : P ∈ I.minimalPrimes := (Set.Finite.mem_toFinset hfin).1 (Finset.mem_of_mem_erase hPS)
      have hne : P ≠ x.asIdeal := Finset.ne_of_mem_erase hPS
      exact hne (le_antisymm hPx (hx.2 hPm.1 hPx))
    obtain ⟨c, hcJ, hcx⟩ := Set.not_subset.1 hJ
    have hgc : g * c ∈ I := by
      rw [hI, PrimeSpectrum.mem_vanishingIdeal]
      intro q hq
      obtain ⟨P, hPm, hPq⟩ := Ideal.exists_minimalPrimes_le (hIle q hq)
      by_cases hPx : P = x.asIdeal
      · by_cases hgq : g ∈ q.asIdeal
        · exact q.asIdeal.mul_mem_right c hgq
        · exact absurd (hgU q (show x.asIdeal ≤ q.asIdeal by rw [← hPx]; exact hPq) hgq) hq
      · have hPS : P ∈ S := Finset.mem_erase.2 ⟨hPx, (Set.Finite.mem_toFinset hfin).2 hPm⟩
        have : S.inf id ≤ P := Finset.inf_le (f := id) hPS
        exact q.asIdeal.mul_mem_left g (hPq (this hcJ))
    rcases x.isPrime.mem_or_mem (hx.1.2 hgc) with h | h
    · exact hg h
    · exact hcx h
  have hcl : IsClosed (Uᶜ) := by
    rw [← closure_subset_iff_isClosed, ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
    intro q hq
    have hIq : I ≤ q.asIdeal := (PrimeSpectrum.mem_zeroLocus _ _).1 hq
    obtain ⟨P, hPm, hPq⟩ := Ideal.exists_minimalPrimes_le hIq
    intro hqU
    exact key ⟨P, hPm.1.1⟩ hPm (hgen _ _ hPq hqU)
  exact isClosed_compl_iff.1 hcl

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenOfStableUnderGeneralizationOfLocallyOpenStatement

section

@[expose] public section

open IsLocalRing TensorProduct

theorem _root_.GlobalTheory.T.isOpen_of_stableUnderGeneralization_of_locally_open : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (U : Set (PrimeSpectrum B)), (∀ p q : PrimeSpectrum B, p ≤ q → q ∈ U → p ∈ U) → (∀ p ∈ U, ∃ g, g ∉ p.asIdeal ∧ ∀ q : PrimeSpectrum B, p ≤ q → g ∉ q.asIdeal → q ∈ U) → IsOpen U := by
  first | exact @GlobalTheory.isOpen_of_stableUnderGeneralization_of_locally_open_in_closure | exact GlobalTheory.isOpen_of_stableUnderGeneralization_of_locally_open_in_closure | (intros; apply GlobalTheory.isOpen_of_stableUnderGeneralization_of_locally_open_in_closure <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenRegularLocusOfNagata

section

@[expose] public section

open IsLocalRing TensorProduct

namespace GlobalTheory

theorem isRegularLocalRing_atPrime_of_le {B : Type} [CommRing B] (p q : Ideal B) [p.IsPrime]
    [q.IsPrime] (hpq : p ≤ q) (hq : IsRegularLocalRing (Localization.AtPrime q)) :
    IsRegularLocalRing (Localization.AtPrime p) := by
  have hd : Disjoint (q.primeCompl : Set B) (p : Set B) := by
    rw [Set.disjoint_left]
    intro x hx hxp
    exact hx (hpq hxp)
  let P' : Ideal (Localization.AtPrime q) := p.map (algebraMap B _)
  haveI hP' : P'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl _ p ‹_› hd
  have hc : P'.comap (algebraMap B (Localization.AtPrime q)) = p :=
    IsLocalization.under_map_of_isPrime_disjoint q.primeCompl _ ‹p.IsPrime› hd
  have hsub : (P'.comap (algebraMap B (Localization.AtPrime q))).primeCompl = p.primeCompl := by
    ext x
    rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, hc]
  haveI : IsRegularRing (Localization.AtPrime q) := isRegularRing_of_isRegularLocalRing _
  have hreg : IsRegularLocalRing (Localization.AtPrime P') :=
    IsRegularRing.isRegularLocalRing_localization P'
  haveI : IsLocalization p.primeCompl (Localization.AtPrime P') := by
    rw [← hsub]
    exact IsLocalization.isLocalization_atPrime_localization_atPrime q.primeCompl P'
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime P')
      (Localization.AtPrime p)).toRingEquiv

theorem isOpen_regularLocus_of_nagata : ∀ (B : Type) [CommRing B] [IsNoetherianRing B], (∀ (p : Ideal B) [p.IsPrime], ∃ g, g ∉ p ∧ ∀ (q : Ideal B) [q.IsPrime], p ≤ q → g ∉ q → IsRegularLocalRing (Localization.AtPrime q ⧸ p.map (algebraMap B (Localization.AtPrime q)))) → IsOpen {Q : PrimeSpectrum B | IsRegularLocalRing (Localization.AtPrime Q.asIdeal)} := by
  intro B _ _ hyp
  apply GlobalTheory.T.isOpen_of_stableUnderGeneralization_of_locally_open B
  · intro p q hpq hq
    exact isRegularLocalRing_atPrime_of_le p.asIdeal q.asIdeal hpq hq
  · intro p hp
    obtain ⟨g₁, hg₁p, hg₁⟩ := hyp p.asIdeal
    obtain ⟨g₂, hg₂p, hg₂⟩ := GlobalTheory.T.exists_regular_near_of_regular_quotient_prime B p.asIdeal hp
    refine ⟨g₁ * g₂, fun h => (p.isPrime.mem_or_mem h).elim hg₁p hg₂p, ?_⟩
    intro q hpq hq
    have hq₁ : g₁ ∉ q.asIdeal := fun h => hq (q.asIdeal.mul_mem_right _ h)
    have hq₂ : g₂ ∉ q.asIdeal := fun h => hq (q.asIdeal.mul_mem_left _ h)
    exact hg₂ q.asIdeal hpq hq₂ (hg₁ q.asIdeal hpq hq₁)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenRegularLocusOfNagataStatement

section

@[expose] public section

open IsLocalRing TensorProduct

theorem _root_.GlobalTheory.T.isOpen_regularLocus_of_nagata' : ∀ (B : Type) [CommRing B] [IsNoetherianRing B], (∀ (p : Ideal B) [p.IsPrime], ∃ g, g ∉ p ∧ ∀ (q : Ideal B) [q.IsPrime], p ≤ q → g ∉ q → IsRegularLocalRing (Localization.AtPrime q ⧸ p.map (algebraMap B (Localization.AtPrime q)))) → IsOpen {Q : PrimeSpectrum B | IsRegularLocalRing (Localization.AtPrime Q.asIdeal)} := by
  first | exact @GlobalTheory.isOpen_regularLocus_of_nagata | exact GlobalTheory.isOpen_regularLocus_of_nagata | (intros; apply GlobalTheory.isOpen_regularLocus_of_nagata <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.QeRingOfFiniteTypeInt

section

@[expose] public section

open IsLocalRing TensorProduct ReciprocityTheory.AnForm.R

namespace GlobalTheory

theorem qeRing_of_finiteType_int : ∀ (A : Type) [CommRing A] [Algebra.FiniteType ℤ A], FinalTheorems.QERing A := by
  intro A _ _
  have hN : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℤ A
  refine ⟨hN, fun P _ => ⟨?_, ?_⟩, fun B _ _ _ => ?_⟩
  · exact AdicCompletion.flat_of_isNoetherian _
  · apply GlobalTheory.T.geomRegFib_of_isRegularRing_tensor_essFiniteType
    intro K _ _ _
    haveI : Algebra.EssFiniteType A (Localization.AtPrime P) :=
      Algebra.EssFiniteType.of_isLocalization _ P.primeCompl
    haveI : Algebra.EssFiniteType ℤ (Localization.AtPrime P) :=
      Algebra.EssFiniteType.comp ℤ A (Localization.AtPrime P)
    have hZ : @Algebra.EssFiniteType ℤ (Localization.AtPrime P) _ _ (Ring.toIntAlgebra _) := by
      convert this
      exact Subsingleton.elim _ _
    exact @GlobalTheory.T.formalFibre_isRegularRing_essFiniteType_int (Localization.AtPrime P) K _ _ hZ _ _ _
  · haveI : Algebra.FiniteType ℤ B := Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType ℤ A) ‹_›
    haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing ℤ B
    exact GlobalTheory.T.isOpen_regularLocus_of_nagata' B (fun p _ => GlobalTheory.T.exists_regular_quotient_near_prime_finiteType_int B p)

end GlobalTheory
end
end
