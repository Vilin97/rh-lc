module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
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
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import GroundTheory.LocalFields.PadicLogSeries

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsSideMore

section

@[expose] public section

theorem GlobalTheory.FourClauses.adm : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.IrreducibleAdmissibleGL :=
  fun h k _ _ _ _ n V _ _ π hs hi => (h k).1 (Fin n) V π hs hi
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleAdmissibleGL

section

@[expose] public section

theorem GlobalTheory.FourClauses.irreducibleAdmissibleGL : GlobalTheory.Published.IrreducibleAdmissibleGL :=
  GlobalTheory.FourClauses.adm GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFixedOpenSubgroupGLw

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.BCT

theorem finiteDimensional_fixed_openSubgroup_GLw : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    ∀ (n : ℕ) (w : Pl E) (σ : SmIrr (GLw n w)) (U : Subgroup (GLw n w)), IsOpen (U : Set (GLw n w)) →
      FiniteDimensional ℂ (fixed σ.ρ U) := by
  intro E _ _ _ n w σ U hU
  letI := GlobalTheory.LocalData.complRel w
  haveI := GlobalTheory.LocalData.isLocalField w
  have hadm : IsAdmissible σ.ρ :=
    GlobalTheory.FourClauses.irreducibleAdmissibleGL (w.adicCompletion E) n σ.V σ.ρ σ.smooth σ.irred
  obtain ⟨ho, hc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n
  have hK : FiniteDimensional ℂ (fixed σ.ρ (U ⊓ GlobalTheory.LFun.KGL w (n := n))) :=
    hadm.2 _ (hU.inter ho) (hc.inter_left (U.isClosed_of_isOpen hU))
  have hle : fixed σ.ρ U ≤ fixed σ.ρ (U ⊓ GlobalTheory.LFun.KGL w (n := n)) := fun v hv h => hv ⟨h.1, h.2.1⟩
  exact Submodule.finiteDimensional_of_le hle

end GlobalTheory.BCT
end
end
