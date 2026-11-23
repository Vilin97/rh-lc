module

public import Formalism.PeriodIntegrals.SplitRow
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.CoreStepOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.AdjointActionReduction
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.FrameReduction
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.SecondDualReduction
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.CoreStep
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
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.MeasureIsomorphismAtInfinity

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.SplitRowOf

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace PI.SRW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem splitRow_of (hc : CoreStep) (ha : AaStep) (ht : TrStep) : PI.SplitRow.SplitRow := by
  intro D u F0 Λ hΛ
  obtain ⟨hg, hF, hX⟩ := hΛ
  exact hc _ _ _ _ _ F0 Λ ⟨hg.1.toIsLattice, hF.2.1, hF.2.2.1.1, hF.2.2.2.2,
    hX.trans (Formalism.L2.SG.Saturated.latSpan_aaS D F0).symm,
    fun a => (ha D a).1, fun a => (ha D a).2, ht D⟩

end PI.SRW
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.Assemble

section

@[expose] public section

namespace PI.SRW

theorem splitRow_of_iso (hi : IsoStep) : PI.SplitRow.SplitRow :=
  splitRow_of (coreStep_of frame_reduction hi assembly_reduction) adjoint_action_reduction trace_reduction

end PI.SRW
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SplitRow

section

@[expose] public section

theorem split_row_iso : PI.SplitRow.SplitRow := PI.SRW.splitRow_of_iso PI.SRW.measure_isomorphism_at_infinity
end
end
