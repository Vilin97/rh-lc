module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.PositiveOfDimensionChange
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BejjSmulLeft
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.MemLevelsIff
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestSumSpan
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.SumFinrankLeOfIndep
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.FinrankEqSpanGen
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestBCdimOfYbc
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BePhiAddLeft
import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.KappaZeroNonneg

-- Source module: Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestrictedBoundsWeakenFromSevenToSix

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

def RestOpen7 (C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM : ℝ) (X : flipOneThree.Inst) : Prop :=
  flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X →
    RestBCdim C0 CE1 CE2 X ∧ RestOrth C0 CE1 CE2 X CM ∧ RestWin C0 CE1 CE2 X CM ∧ RestDirQ C0 CE1 CE2 X

def RestOpen7E (D : Formalism.BasicNotions.D7) : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc => ∀ Ckap Cs CM : ℝ, 1 ≤ CM →
    ∀ X : flipOneThree.Inst, AdmNoK D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs X → RestOpen7 C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM X

theorem restricted_bounds_weaken_from_seven_to_six (D : Formalism.BasicNotions.D7) (h : RestOpen7E D) : RestOpen6E D :=
  thr_mono (fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc hP Ckap Cs CM hCM X hA hH => by
    obtain ⟨a, b, c, d⟩ := hP Ckap Cs CM hCM X hA hH
    have hY0 : (0 : ℝ) < X.L.Y := by linarith [hH.1.1]
    exact ⟨a, restPlusB_of CM hY0 b c, d⟩) h

theorem closed_of_open_base_dims (D : Formalism.BasicNotions.D7) (h : RestOpen7E D) : IntegralityFromMetricForLargeConstants D :=
  closed_of_open_dimensions D (restricted_bounds_weaken_from_seven_to_six D h)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestrictedBoundsWeakenFromEightToSeven

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

def RestOpen8 (C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM : ℝ) (X : flipOneThree.Inst) : Prop :=
  flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X →
    RestBClvl C0 CE1 CE2 X ∧ RestOrth C0 CE1 CE2 X CM ∧ RestWin C0 CE1 CE2 X CM ∧ RestDirQ C0 CE1 CE2 X

def RestOpen8E (D : Formalism.BasicNotions.D7) : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc => ∀ Ckap Cs CM : ℝ, 1 ≤ CM →
    ∀ X : flipOneThree.Inst, AdmNoK D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs X → RestOpen8 C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM X

theorem restricted_bounds_weaken_from_eight_to_seven (D : Formalism.BasicNotions.D7) (h : RestOpen8E D) : RestOpen7E D :=
  thr_mono (fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc hP Ckap Cs CM hCM X hA hH => by
    obtain ⟨a, b, c, d⟩ := hP Ckap Cs CM hCM X hA hH
    exact ⟨restBCdim_of C0 CE1 CE2 X a, b, c, d⟩) h

theorem theorem_A_closed_of_eight_open_bounds (D : Formalism.BasicNotions.D7) (h : RestOpen8E D) : IntegralityFromMetricForLargeConstants D :=
  closed_of_open_base_dims D (restricted_bounds_weaken_from_eight_to_seven D h)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestrictedBoundsWeakenFromNineToEight

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

def RestOpen9 (C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM : ℝ) (X : flipOneThree.Inst) : Prop :=
  flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X →
    RestBClvl C0 CE1 CE2 X ∧ RestOrth C0 CE1 CE2 X CM ∧ RestWin C0 CE1 CE2 X CM ∧ RestLvlDim C0 CE1 CE2 X

def RestOpen9E (D : Formalism.BasicNotions.D7) : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc => ∀ Ckap Cs CM : ℝ, 1 ≤ CM →
    ∀ X : flipOneThree.Inst, AdmNoK D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs X → RestOpen9 C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM X

theorem restricted_bounds_weaken_from_nine_to_eight (D : Formalism.BasicNotions.D7) (h : RestOpen9E D) : RestOpen8E D :=
  thr_mono (fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc hP Ckap Cs CM hCM X hA hH => by
    obtain ⟨a, b, c, d⟩ := hP Ckap Cs CM hCM X hA hH
    exact ⟨a, b, c, restDirQ_of d (restSumSpan_proved C0 CE1 CE2 X)⟩) h

theorem theorem_A_closed_of_nine_open_bounds (D : Formalism.BasicNotions.D7) (h : RestOpen9E D) : IntegralityFromMetricForLargeConstants D :=
  theorem_A_closed_of_eight_open_bounds D (restricted_bounds_weaken_from_nine_to_eight D h)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.IntegralityFromMetricOfOrthogonalityWindow

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

def OpenConditionsOrthogonal (C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM : ℝ) (X : flipOneThree.Inst) : Prop :=
  flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X →
    RestOrth C0 CE1 CE2 X CM ∧ RestWin C0 CE1 CE2 X CM ∧ RestLvlDim C0 CE1 CE2 X

def OrthogonalityWindowLevelDimOnAdmissible (D : Formalism.BasicNotions.D7) : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc => ∀ Ckap Cs CM : ℝ, 1 ≤ CM →
    ∀ X : flipOneThree.Inst, AdmNoK D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs X → OpenConditionsOrthogonal C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM X

theorem open_conditions_base_change (D : Formalism.BasicNotions.D7) (hY : RestYbc) (h : OrthogonalityWindowLevelDimOnAdmissible D) : RestOpen9E D :=
  thr_mono (fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc hP Ckap Cs CM hCM X hA hH => by
    obtain ⟨a, b, c⟩ := hP Ckap Cs CM hCM X hA hH
    exact ⟨restBClvl_of C0 CE1 CE2 X hY, a, b, c⟩) h

theorem integrality_from_metric_of_orthogonality_window (D : Formalism.BasicNotions.D7) (hY : RestYbc) (h : OrthogonalityWindowLevelDimOnAdmissible D) : IntegralityFromMetricForLargeConstants D :=
  theorem_A_closed_of_nine_open_bounds D (open_conditions_base_change D hY h)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.SymmetryFinitenessWindowLevelDimOnAdmissible

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

def SymmetryFinitenessWindowLevelDimConditions (C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM : ℝ) (X : flipOneThree.Inst) : Prop :=
  flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X →
    RestSymm C0 CE1 CE2 X ∧ RestLjjFin C0 CE1 CE2 X ∧ RestWin C0 CE1 CE2 X CM ∧ RestLvlDim C0 CE1 CE2 X

def SymmetryFinitenessWindowLevelDimOnAdmissible (D : Formalism.BasicNotions.D7) : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc => ∀ Ckap Cs CM : ℝ, 1 ≤ CM →
    ∀ X : flipOneThree.Inst, AdmNoK D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs X → SymmetryFinitenessWindowLevelDimConditions C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM X

theorem orthogonal_of_symmetric_finite (D : Formalism.BasicNotions.D7) (hO : OrthLat) (h : SymmetryFinitenessWindowLevelDimOnAdmissible D) : OrthogonalityWindowLevelDimOnAdmissible D :=
  thr_mono_ge (fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc hCYb hP Ckap Cs CM hCM X hA hH => by
    obtain ⟨a, b, c, d⟩ := hP Ckap Cs CM hCM X hA hH
    have hF := hiFacts C0 CYb Cde Ck CD Cb Cc X hCYb hH
    have hp2 : X.p ≠ 2 := by
      intro h2
      have := p25 hF
      have h3 : (X.L.p : ℝ) = 2 := by exact_mod_cast h2
      linarith
    exact ⟨restOrth_of CM hp2 hO a b, c, d⟩) h

theorem closed_of_symmetric_finite (D : Formalism.BasicNotions.D7) (hY : RestYbc) (hO : OrthLat) (h : SymmetryFinitenessWindowLevelDimOnAdmissible D) : IntegralityFromMetricForLargeConstants D :=
  integrality_from_metric_of_orthogonality_window D hY (orthogonal_of_symmetric_finite D hO h)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end
end
