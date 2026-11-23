module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SplitPlaceTypes
public import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.SplitRowIffOfIsEmpty
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CmHalfTypePlacesMeetConjugatePairsAndCount
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPrimePlaceCmTypeConjugateStatement
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalFieldUnramified
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SplitPlaceTypes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPrimeImpliesPlacesSplit
import Formalism.LocalRingCardinality.HostCls

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CmHalfTypePlacesMeetConjugatePairsAndCountStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.FrobeniusOrbits GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes
open GlobalTheory.SplitCount in

theorem _root_.GlobalTheory.T.cmHalfTypePlaces_meet_conjugatePairs_and_count : ∀ (D : D7) (i : D.nd.Loc), SplitRowPrime D.host (D.nd.l i) → ∀ s : Bool, (∀ w ∈ placesOver D.host.E (D.nd.l i), ∀ w', IsConjPl D.host w w' → Xor (w ∈ columns (N := D.nd) D.nbr i s) (w' ∈ columns (N := D.nd) D.nbr i s)) ∧ (columns (N := D.nd) D.nbr i s).Finite ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), locDeg D.host.E w * (columns (N := D.nd) D.nbr i s).ncard = D.R.f := by
  intro D i hl s
  have hx : ∀ w ∈ placesOver D.host.E (D.nd.l i), ∀ w', IsConjPl D.host w w' →
      Xor (w ∈ columns (N := D.nd) D.nbr i s) (w' ∈ columns (N := D.nd) D.nbr i s) := by
    intro w hw w' h
    have hw' := mem_placesOver_of_conj D.host hw h
    have n1 := GlobalTheory.SplitRowProbe.not_both_columns D i w hw
    have n2 := GlobalTheory.SplitRowProbe.not_both_columns D i w' hw'
    rcases GlobalTheory.T.splitPrime_place_cmType_conjugate D i hl w w' hw hw' h with
      ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> cases s
    · exact Or.inr ⟨⟨hw', h2⟩, fun ⟨_, h3⟩ => n1 ⟨h1, h3⟩⟩
    · exact Or.inl ⟨⟨hw, h1⟩, fun ⟨_, h3⟩ => n2 ⟨h3, h2⟩⟩
    · exact Or.inl ⟨⟨hw, h1⟩, fun ⟨_, h3⟩ => n2 ⟨h2, h3⟩⟩
    · exact Or.inr ⟨⟨hw', h2⟩, fun ⟨_, h3⟩ => n1 ⟨h3, h1⟩⟩
  have := D.host.hostE_isGalois
  obtain ⟨hfin, hdeg⟩ := locDeg_mul_ncard D.host.E hl.1
  let C := columns (N := D.nd) D.nbr i s
  have hsub : C ⊆ placesOver D.host.E (D.nd.l i) := fun _ ⟨hw, _⟩ => hw
  have hCf : C.Finite := hfin.subset hsub
  refine ⟨hx, hCf, fun w hw => ?_⟩
  have hinj : Function.Injective (cPl D.host) := Function.LeftInverse.injective (cPl_cPl D.host)
  have hun : placesOver D.host.E (D.nd.l i) = C ∪ cPl D.host '' C := by
    ext v
    constructor
    · intro hv
      rcases hx v hv _ (isConjPl_cPl D.host v) with h | h
      · exact Or.inl h.1
      · exact Or.inr ⟨_, h.1, cPl_cPl D.host v⟩
    · rintro (hv | ⟨u, hu, rfl⟩)
      · exact hsub hv
      · exact mem_placesOver_of_conj D.host (hsub hu) (isConjPl_cPl D.host u)
  have hdis : Disjoint C (cPl D.host '' C) := by
    rw [Set.disjoint_left]
    rintro _ hv ⟨u, hu, rfl⟩
    rcases hx u (hsub hu) _ (isConjPl_cPl D.host u) with h | h
    · exact h.2 hv
    · exact h.2 hu
  have hfr : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    ring
  have h := hdeg w hw
  rw [hun, Set.ncard_union_eq hdis hCf (hCf.image _), Set.ncard_image_of_injective _ hinj, hfr] at h
  rw [Nat.mul_add] at h
  change locDeg D.host.E w * C.ncard = D.R.f
  omega
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalFieldUnramifiedStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.FrobeniusOrbits GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes

theorem _root_.GlobalTheory.T.K0_eq_and_good_of_ne : ∀ (D : D7) (i : D.nd.Loc), D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), Loc.K0 (D.nbr i w hw).Kw = (D.nbr i w hw).Kw.1 ∧ (D.nbr i w hw).Kw.1 ≤ Loc.Ks (D.nbr i w hw).Kw 1 ∧ Loc.Good (D.nbr i w hw).Kw 1 (D.nbr i w hw).LL := by
  exact GlobalTheory.HubLoc.localField_unramified
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPrimeImpliesPlacesSplitStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.FrobeniusOrbits GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes

theorem _root_.GlobalTheory.T.split_prime_implies_places_split : ∀ {R : Ranks} (H : Host R) (l : ℕ), SplitRowPrime H l → PlacesSplit H l := by
  first | exact @GlobalTheory.SplitPlaces.placesSplit | exact GlobalTheory.SplitPlaces.placesSplit | (intros; apply GlobalTheory.SplitPlaces.placesSplit <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitRowAt

section

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.FrobeniusOrbits GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes

namespace GlobalTheory.SplitRowAll

theorem splitRow_at : ∀ D : D7, SplitRow_at D := by
  intro D
  refine ⟨fun l hl => GlobalTheory.T.split_prime_implies_places_split D.host l hl, fun i hi => ⟨?_, ?_, ?_, ?_⟩⟩
  · intro w hw
    have h2 : D.nd.l i ∉ D.host.small := ((primeClass_eq_splitK_iff _).1 hi.2.2.2.2.2).1
    exact (GlobalTheory.T.K0_eq_and_good_of_ne D i h2 hi.2.2.1 hi.2.2.2.1 w hw).1
  · rintro w hw τ ⟨h1, h2⟩
    rcases GlobalTheory.SplitRowProbe.embIn_xor D i w hw τ with h | h
    · exact h.2 h2
    · exact h.2 h1
  · exact GlobalTheory.T.splitPrime_place_cmType_conjugate D i hi
  · exact GlobalTheory.T.cmHalfTypePlaces_meet_conjugatePairs_and_count D i hi

end GlobalTheory.SplitRowAll
end
end
