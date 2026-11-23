module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
public import Development.AutomorphicArithmetic.CyclotomicBounds.PlaceOfLetterInjective
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
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
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AtMostTwoThickInWindowLongOrbitStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComplexConjugationOrbitOneRealPlaceStatement
import Mathlib.Tactic.ReduceModChar
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Development.AutomorphicArithmetic.CyclotomicBounds.PlaceOfLetterInjective

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.AtMostOneThickShortOrbit

section

@[expose] public section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem short_orbit_one_thick : ∀ {R : Ranks} (H : Host R) (τ φ : R.GG),
    orderOf φ.2 ≤ 4 * H.Lw → ∀ a b : ZMod (orderOf φ), Thick H (letter τ φ a) →
      Thick H (letter τ φ b) → plc (letter τ φ a) = plc (letter τ φ b) := by
  intro R H τ φ hord a b ha hb
  have key : ∀ g : R.GG, Thick H g → ∃ s ∈ H.T2, R.tau2 (R.dig s + H.u0) = plc g := by
    intro g hg
    unfold Thick Host.thickPlaces at hg
    simpa [Finset.mem_image] using hg
  exact UpperTheory.KStar.Words.thick_one_place H.T2 H.second_set_range H.u0 τ φ
    ((Nat.le_of_dvd (orderOf_pos _) (R.toFrame.orderOf_hH_dvd φ.2)).trans hord) a.val b.val (key _ ha) (key _ hb)

end GlobalTheory.HTW
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.AtMostOneThickShortOrbitStatement

section

@[expose] public section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.atMostOneThick_short_orbit : ∀ {R : Ranks} (H : Host R) (τ φ : R.GG), orderOf φ.2 ≤ 4 * H.Lw → ∀ a b : ZMod (orderOf φ), Thick H (letter τ φ a) → Thick H (letter τ φ b) → plc (letter τ φ a) = plc (letter τ φ b) := by
  first | exact @GlobalTheory.HTW.short_orbit_one_thick | exact GlobalTheory.HTW.short_orbit_one_thick | (intros; apply GlobalTheory.HTW.short_orbit_one_thick <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.CyclicWordNoThreeMarkedOfAtMostOne

section

@[expose] public section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory

theorem noThree_of_atMostOne : ∀ {n : ℕ} (th : ZMod n → Prop), 2 ≤ n → (∀ a b, th a → th b → a = b) → NoThree th ∧ ∃ i, ¬ th i := by
  intro n th hn hone
  have h10 : (1 : ZMod n) ≠ 0 := by
    have : Fact (1 < n) := ⟨by omega⟩
    exact one_ne_zero
  have key : ∀ i : ZMod n, ¬ (th i ∧ th (i + 1)) := by
    rintro i ⟨ha, hb⟩
    exact h10 (by linear_combination (hone _ _ ha hb).symm)
  refine ⟨fun i h => key i ⟨h.1, h.2.1⟩, ?_⟩
  by_cases h0 : th 0
  · exact ⟨0 + 1, fun h1 => key 0 ⟨h0, h1⟩⟩
  · exact ⟨0, h0⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.CyclicWordNoThreeMarkedOfAtMostOneStatement

section

@[expose] public section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.cyclicWord_noThreeMarked_of_atMostOne : ∀ {n : ℕ} (th : ZMod n → Prop), 2 ≤ n → (∀ a b, th a → th b → a = b) → NoThree th ∧ ∃ i, ¬ th i := by
  first | exact @GlobalTheory.noThree_of_atMostOne | exact GlobalTheory.noThree_of_atMostOne | (intros; apply GlobalTheory.noThree_of_atMostOne <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.CyclicWordNoThreeMarkedOfAtMostTwoInWindow

section

@[expose] public section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory

theorem _root_.GlobalTheory.noThree_of_windowTwo : ∀ {n : ℕ} (th : ZMod n → Prop) (L : ℕ),
    3 ≤ L → _root_.GlobalTheory.HTW.WindowTwo th L →
    _root_.GlobalTheory.HTW.NoThree th ∧ ∃ i, ¬ th i := by
  intro n th L hL hw
  have key : ∀ i, ¬(th i ∧ th (i + 1) ∧ th (i + 2)) := by
    intro i h
    have := hw i 0 1 2 (by norm_num) (by norm_num) (by omega)
    simp only [Nat.cast_zero, add_zero, Nat.cast_one, Nat.cast_ofNat] at this
    exact this h
  refine ⟨key, ?_⟩
  by_contra hall
  push_neg at hall
  exact key 0 ⟨hall _, hall _, hall _⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.CyclicWordNoThreeMarkedOfAtMostTwoInWindowStatement

section

@[expose] public section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.cyclicWord_noThreeMarked_of_atMostTwoInWindow : ∀ {n : ℕ} (th : ZMod n → Prop) (L : ℕ), 3 ≤ L → WindowTwo th L → NoThree th ∧ ∃ i, ¬ th i := by
  first | exact @GlobalTheory.noThree_of_windowTwo | exact GlobalTheory.noThree_of_windowTwo | (intros; apply GlobalTheory.noThree_of_windowTwo <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrderOfEqMaxTwoOfSignNegImplicit

section

@[expose] public section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory

theorem orderOf_moving (fr : Formalism.HC.Frame) (φ : fr.GG) (h : φ.1.2 = -1) : orderOf φ = Nat.lcm 2 (orderOf φ.2) :=
  UpperTheory.KStar.Words.orderOf_moving φ h

theorem orderOf_moving_stmt : ∀ {fr : Formalism.HC.Frame} (φ : fr.GG), φ.1.2 = -1 → orderOf φ = Nat.lcm 2 (orderOf φ.2) :=
  fun {fr} φ h => orderOf_moving fr φ h

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrderOfEqMaxTwoOfSignNegImplicitStatement

section

@[expose] public section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.orderOf_eq_max_two_of_sign_neg_implicit : ∀ {fr : Formalism.HC.Frame} (φ : fr.GG), φ.1.2 = -1 → orderOf φ = Nat.lcm 2 (orderOf φ.2) := by
  first | exact @GlobalTheory.orderOf_moving_stmt | exact GlobalTheory.orderOf_moving_stmt | (intros; apply GlobalTheory.orderOf_moving_stmt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPrimeNonthickLetterNoThreeThick

section

@[expose] public section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.InertWord

theorem inert_nothree_nonthick : ∀ {R : Ranks} (H : Host R) (τ φ : R.GG), 3 ≤ H.Lw → φ.1.2 = -1 →
    ¬ (φ = R.cc ∧ Thick H τ) →
    NoThree (fun i : ZMod (orderOf φ) => Thick H (letter τ φ i)) ∧
      ∃ i : ZMod (orderOf φ), ¬ Thick H (letter τ φ i) := by
  intro R H τ φ hL hφ hnot
  have h2 : 2 ≤ orderOf φ := by
    rw [GlobalTheory.T.orderOf_eq_max_two_of_sign_neg_implicit φ hφ]
    exact Nat.le_of_dvd (Nat.lcm_pos two_pos (orderOf_pos _)) (Nat.dvd_lcm_left _ _)
  by_cases hc : φ = R.cc
  · have hτ : ¬ Thick H τ := fun h => hnot ⟨hc, h⟩
    subst hc
    have hno : ∀ i : ZMod (orderOf (R.cc)), ¬ Thick H (letter τ (R.cc) i) := by
      intro i h
      apply hτ
      have := (GlobalTheory.T.complexConjugation_orbit_one_realPlace τ).2 i
      unfold Thick at h ⊢
      rw [this] at h
      exact h
    exact GlobalTheory.T.cyclicWord_noThreeMarked_of_atMostOne _ h2 (fun a b ha _ => absurd ha (hno a))
  · by_cases hlen : 4 * H.Lw < orderOf φ.2
    · exact GlobalTheory.T.cyclicWord_noThreeMarked_of_atMostTwoInWindow _ H.Lw hL (GlobalTheory.T.atMostTwoThick_in_window_long_orbit H τ φ hlen)
    · have h1 : φ ≠ 1 := by
        rintro rfl
        exact absurd (show (1 : ℤˣ) = -1 from hφ) (by decide)
      have adj : ∀ i : ZMod (orderOf φ), ¬ (Thick H (letter τ φ i) ∧ Thick H (letter τ φ (i + 1))) := fun i h =>
        UpperTheory.KStar.Words.placeOf_letter_succ_ne τ φ h1 hc i
          (GlobalTheory.T.atMostOneThick_short_orbit H τ φ (not_lt.mp hlen) (i + 1) i h.2 h.1)
      refine ⟨fun i h => adj i ⟨h.1, h.2.1⟩, ?_⟩
      by_contra hall
      have hall' : ∀ i, Thick H (letter τ φ i) := fun i => by_contra fun hi => hall ⟨i, hi⟩
      exact adj 0 ⟨hall' 0, hall' (0 + 1)⟩

end GlobalTheory.HTW.InertWord
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPrimeNonthickLetterNoThreeThickStatement

section

@[expose] public section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.inertPrime_nonthick_letter_no_three_thick : ∀ {R : Ranks} (H : Host R) (τ φ : R.GG), 3 ≤ H.Lw → φ.1.2 = -1 → ¬ (φ = R.cc ∧ Thick H τ) → NoThree (fun i : ZMod (orderOf φ) => Thick H (letter τ φ i)) ∧ ∃ i : ZMod (orderOf φ), ¬ Thick H (letter τ φ i) := by
  first | exact @GlobalTheory.HTW.InertWord.inert_nothree_nonthick | exact GlobalTheory.HTW.InertWord.inert_nothree_nonthick | (intros; apply GlobalTheory.HTW.InertWord.inert_nothree_nonthick <;> assumption)
end
end
