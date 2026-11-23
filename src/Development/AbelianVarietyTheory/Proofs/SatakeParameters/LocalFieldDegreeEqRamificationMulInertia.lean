module

public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Mathlib.Algebra.AffineMonoid.Basic
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.KrullDimension.PID
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
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlaceOverPrimeOfPadicAlgClEmbeddingStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankLocalFieldEqCardDecompositionGroupStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicAlgClFiniteDenseEqAdjoinStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardDecompositionGroupEqLocalDegree

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

namespace GlobalTheory.DecompCard

theorem card_stabilizer_eq_locDeg : ∀ (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E] [IsGalois ℚ E]
    (v w : HeightOneSpectrum (𝓞 E)), v ∈ placesOver E l → w ∈ placesOver E l →
    Nat.card (MulAction.stabilizer (E ≃ₐ[ℚ] E) v.asIdeal) = locDeg E w := by
  intro l _ E _ _ _ v w hv hw
  have hpz : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  have : IsGaloisGroup (E ≃ₐ[ℚ] E) ℤ (𝓞 E) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ E
  have : (Ideal.span {(l : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpz.ne_zero).2 hpz
  have := v.isPrime
  have := w.isPrime
  have hover : ∀ R : HeightOneSpectrum (𝓞 E), R ∈ placesOver E l →
      R.asIdeal.LiesOver (Ideal.span {(l : ℤ)}) := fun R hR =>
    (Ideal.liesOver_span_iff R.isPrime.ne_top hpz).mpr (by simpa [placesOver] using hR)
  have := hover v hv
  have := hover w hw
  rw [Ideal.card_stabilizer_eq (G := E ≃ₐ[ℚ] E) (Ideal.span {(l : ℤ)}) v.asIdeal,
    Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(l : ℤ)}) w.asIdeal (E ≃ₐ[ℚ] E),
    Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(l : ℤ)}) w.asIdeal (E ≃ₐ[ℚ] E), locDeg]

end GlobalTheory.DecompCard
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardDecompositionGroupEqLocalDegreeStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

theorem _root_.GlobalTheory.T.card_decomposition_group_eq_local_degree : ∀ (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (v w : HeightOneSpectrum (𝓞 E)), v ∈ placesOver E l → w ∈ placesOver E l → Nat.card (MulAction.stabilizer (E ≃ₐ[ℚ] E) v.asIdeal) = locDeg E w := by
  first | exact @GlobalTheory.DecompCard.card_stabilizer_eq_locDeg | exact GlobalTheory.DecompCard.card_stabilizer_eq_locDeg | (intros; apply GlobalTheory.DecompCard.card_stabilizer_eq_locDeg <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalFieldDegreeEqRamificationMulInertia

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

namespace GlobalTheory

theorem bridge_degW {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} (nbr : Br.NBr N)
    (i : N.Loc) (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E (N.l i)) :
    Br.DegW nbr i w hw := by
  have hG : IsGalois ℚ H.E := H.hostE_isGalois
  let c : H.E →+* PadicAlgCl (N.l i) := (nbr i w hw).j.comp (algebraMap H.E N.Om)
  have hK : (nbr i w hw).Kw.1 = IntermediateField.adjoin ℚ_[N.l i] (Set.range c) :=
    GlobalTheory.T.padicAlgCl_finite_dense_eq_adjoin' (N.l i) H.E c (nbr i w hw).Kw.1 (nbr i w hw).j_E (nbr i w hw).Kw.2
      (nbr i w hw).j_dense
  obtain ⟨v, hv, hc⟩ := GlobalTheory.T.exists_place_over_prime_of_padicAlgCl_embedding (N.l i) H.E c
  have h1 := GlobalTheory.T.finrank_local_field_eq_card_decomposition_group (N.l i) H.E c v hc
  have h2 := GlobalTheory.T.card_decomposition_group_eq_local_degree (N.l i) H.E v w hv hw
  have h3 : Module.finrank ℚ_[N.l i] (nbr i w hw).Kw.1 = locDeg H.E w := by
    rw [hK, h1, h2]
  exact h3

end GlobalTheory
end
end
