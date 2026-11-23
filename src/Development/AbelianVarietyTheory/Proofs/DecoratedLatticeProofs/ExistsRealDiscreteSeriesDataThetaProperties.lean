module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChosenSeries
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypesJointShapeBlockInUnitarySStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypesJointShapeBlockUnitaryStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestTypeNotJointShapeSmallerPairsStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoIntertwinerSmallerFockToDiscreteSeries
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoThetaTensorIntertwinerLowerTowerMembers
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealPlaceThetaObjectsTheoremARParts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockStructure
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LineMatrixKroneckerLeftFactorEqZeroOfIsPC
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.NoThetaLiftDiscreteSeriesSmallerTowerMember

section

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory.TowerDrop

theorem archimedeanRallisFourth_of_discreteSeriesBlattner : ∀ X : ProvA, admH1 X → admH2 X → DiscreteSeriesBlattner X → admQ5 X → ArchimedeanRallisFourth X := by
  intro X _ _ hD h5
  refine ⟨fun t al be ga de hd i hi hr hs MM f hf => ?_,
    fun t al be ga de hd i hi hr hs MM f hf => ?_⟩
  · exact ((GlobalTheory.LowerTower.no_map_lower X hD h5 t al be ga de hd.1 i hi).1 hr hs) MM f hf
  · have hA := hd.1
    have ht : 1 ≤ t := hA.1
    have hn : 1 ≤ al.length + be.length + ga.length + de.length := hA.2.1
    have ht0 : (0 : ℚ) ≤ t := Nat.cast_nonneg t
    obtain ⟨-, hpar, -⟩ := GlobalTheory.T.lowest_kTypes_jointShape_block_unitary t al be ga de hA
    obtain ⟨-, -, hsign, -⟩ := GlobalTheory.T.lowestKTypes_jointShape_block_in_unitaryS t al be ga de hA
    have hno := (GlobalTheory.T.lowestType_not_jointShape_smaller_pairs t al be ga de hA i hi).2.1 hr hs
    refine GlobalTheory.LowerTower.tensNo_first X hD h5 (by omega) _ hpar 0 ?_ hno MM f hf
    rw [GlobalTheory.SmallerSource.cPair_sub hr hs]
    refine fun a => ⟨(hsign a).1, fun h => (hsign a).2 (lt_of_le_of_ne h fun h0 => ?_)⟩
    have := hA.2.2.2.2.2.2.2.2.2.2 _ (GlobalTheory.LowerTower.lamA_mem al be ga de a)
    rw [h0, abs_zero] at this
    linarith

end GlobalTheory.TowerDrop
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.NoThetaLiftDiscreteSeriesSmallerTowerMemberStatement

section

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

theorem _root_.GlobalTheory.T.no_thetaLift_discreteSeries_smaller_tower_member : ∀ X : ProvA, admH1 X → admH2 X → DiscreteSeriesBlattner X → admQ5 X → ArchimedeanRallisFourth X := by
  first | exact @GlobalTheory.TowerDrop.archimedeanRallisFourth_of_discreteSeriesBlattner | exact GlobalTheory.TowerDrop.archimedeanRallisFourth_of_discreteSeriesBlattner | (intros; apply GlobalTheory.TowerDrop.archimedeanRallisFourth_of_discreteSeriesBlattner <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRealDiscreteSeriesDataThetaProperties

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealPlaceTheta

theorem exists_record_theta_all :
    GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∃ X : ProvA, ChosenSeries X ∧ Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFirst X ∧ Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisSecond X ∧ Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X ∧ Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFourth X ∧ Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFifth X := by
  intro hD hH
  obtain ⟨X, hX, d1, q5, a1, a2, a3, a5⟩ := GlobalTheory.RealPlaceTheta.exists_record_theta hD hH
  exact ⟨X, hX, a1, a2, a3,
    GlobalTheory.T.no_thetaLift_discreteSeries_smaller_tower_member X (GlobalTheory.FockDeg.degrees_and_adjoints X) (GlobalTheory.FockAlg.fock_structure X) d1 q5, a5⟩

end GlobalTheory.RealPlaceTheta
end
end
