module

public import Formalism.AdmissibleDesigns.RestrictedSevenEightOfFull
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoLocalAllPrimesOfBlochKato
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicIntegersFiniteExtGoodCoefficientRingStatement
public import Formalism.SharpRestriction.LevelLetterCocycles.LargeLevelLemmas
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.GaloisConditionFiveExtraOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BlochKatoAnnihilatorAboveL

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions

theorem bloch_kato_annihilator_above_l (D : D7) (i : D.nd.Loc) (h55 : Formalism.MainNotions.LocalSituation.Conclusion5 D) (hO : LitGoodO) :
    Formalism.MainNotions.LargeLevelLemmas.BlochKatoAnnihilators (D := D) i := by
  intro w hw C _
  exact Formalism.MainNotions.LargeLevelLemmas.bkAAt_of_core (h := (h55 _ _).1) (hO := hO _ C.LL)

end Formalism.MainNotions.N
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoAnnihilatorAllOfTateDualityEulerChar

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.BKaRows

theorem bkaAll_of_hypotheses : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK →
    Formalism.GaloisCohomology.LocalEulerCharK → ∀ D : D7, Formalism.MainNotions.N.K.Rows.BKaAll D := by
  intro hBK hTD hEC D i
  exact bloch_kato_annihilator_above_l D i (GlobalTheory.BlochKatoLocalOfHyp.blochKatoLocal_allPrimes_of_blochKato hBK hTD hEC D) GlobalTheory.T.padicIntegers_finiteExt_goodCoefficientRing

end GlobalTheory.BKaRows
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoAnnihilatorAllOfTateDualityEulerCharStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

theorem _root_.GlobalTheory.T.blochKatoAnnihilator_all_of_tateDuality_eulerChar : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ D : D7, Formalism.MainNotions.N.K.Rows.BKaAll D := by
  first | exact @GlobalTheory.BKaRows.bkaAll_of_hypotheses | exact GlobalTheory.BKaRows.bkaAll_of_hypotheses | (intros; apply GlobalTheory.BKaRows.bkaAll_of_hypotheses <;> assumption)
end
end
