module

public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
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
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WfRing
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WfSubst
public import Formalism.PeriodIntegrals.InvSerSub
public import Formalism.PeriodIntegrals.W2pair
public import Formalism.PeriodIntegrals.WfRing
public import Formalism.PeriodIntegrals.WfSubst
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WittLogarithm
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittEndomorphism.FlogConstantCoeff
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.EndIntWOf

section

@[expose] public section

open Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric Formalism.BasicNotions

namespace Formalism.MainNotions.Ext

def CoefWfRing : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (f g : MvPowerSeries σ ℂ_[p]), CoefWf f → CoefWf g →
    CoefWf (f + g) ∧ CoefWf (f - g) ∧ CoefWf (f * g) ∧ ∀ c : ℂ_[p], InWf c → CoefWf (MvPowerSeries.C c * f)

def SubstWf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (f : PowerSeries ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]),
    CoefWf f → IntegralW a → MvPowerSeries.constantCoeff a = 0 → CoefWf (PowerSeries.subst a f)

def EndIntWG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok → ModelOverW g.lam g.abelian₂ g.C → ∀ α ∈ W2pair p,
    IntegralMv (g.mulBy α.1 (Xv ()) : MvPowerSeries Unit ℂ_[p]) →
    IntegralW (g.mulBy α.1 (Xv ()) : MvPowerSeries Unit ℂ_[p])

end Formalism.MainNotions.Ext
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittEndomorphism.WfEndOfLog

section

@[expose] public section

namespace PI.WfEndProof

theorem wfEnd_of_log (hL : WfLog) : WfEnd := wfEnd_of witt_ring_structure witt_substitution hL

end PI.WfEndProof
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WittFrobeniusEnd

section

@[expose] public section

theorem witt_pairing : PI.PairW := PI.WfEndProof.pairW

theorem witt_frobenius_end : PI.WfEnd := PI.WfEndProof.wfEnd_of_log witt_logarithm

theorem wfEnd_of : PI.WfRing → PI.WfSubst → PI.WfLog → PI.WfEnd := PI.WfEndProof.wfEnd_of
end
end

-- Source module: Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.StmtEndIntWOfOkp

section

@[expose] public section

namespace Formalism.MainNotions.Ext

theorem substWf_holds : SubstWf :=
  fun p _ σ f a hf ha h0 => witt_substitution p σ f a hf (fun n => ⟨0, by rw [pow_zero, one_mul]; exact ha n⟩) h0

theorem coefWfRing_holds : CoefWfRing := witt_ring_structure

theorem endIntWG_holds : EndIntWG :=
  fun p _ g hOk hW α hα hI =>
    witt_frobenius_end p g.W g.wq g.ex hW.1 hW.2.1 hW.2.2.1 hW.2.2.2.1 hW.2.2.2.2 hOk.2.1 hOk.2.2.1 hOk.2.2.2 α.1
      ⟨0, by simpa using witt_pairing p α hα⟩ hI

end Formalism.MainNotions.Ext
end
end
