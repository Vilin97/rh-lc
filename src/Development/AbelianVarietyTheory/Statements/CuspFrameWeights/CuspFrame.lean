module

public import Mathlib.Analysis.Complex.Exponential
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne

-- Source module: Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.PointwiseKernelBound

section

@[expose] public section

open NumberField Finset

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PointwiseKernelBound

open Formalism.MainNotions.S GlobalTheory.Count

def decHS (q : ℕ) (h t : ℝ) : ℝ := Real.exp (-(h / 8) * min (t ^ 2) (t / Real.sqrt (2 * (q : ℝ))))

end GlobalTheory.IndefiniteRowSideFullHecke.PointwiseKernelBound
end
end
end

-- Source module: Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.FarTermsLatticeBound

section

@[expose] public section

open NumberField

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound

open Formalism.MainNotions.S GlobalTheory.Count

def farSet (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (ep : ℝ) (x : B.I.GA) : Set B.I.GA :=
  {γ | γ ∈ B.I.GFset ∧ ¬ IsNear B d ep x γ}

def latFactor (I : AutInst) (x : I.GA) : ℝ :=
  (3 * Real.sqrt (I.n : ℝ) / tau1 I x ^ 2) ^ (2 * (I.n ^ 2 * I.f))

end GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound
end
end
end

-- Source module: Development.AbelianVarietyTheory.Statements.CuspFrameWeights.CuspFrame

section

@[expose] public section

open MeasureTheory NumberField Finset

noncomputable section

namespace GlobalTheory.Deep

open Formalism.MainNotions.S GlobalTheory.Count

def PtBound : Prop :=
  ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (h : ℝ),
    IsDSData B d → SigIs B p q → GapGe B h →
    120 * (B.I.n : ℝ) * ((min p q : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h →
      (1 ≤ min p q → ∀ y : B.I.GA,
          ‖phe B d y‖ ≤ (∏ v, d v) * (B.e 1).re *
            ∏ v, GlobalTheory.IndefiniteRowSideFullHecke.PointwiseKernelBound.decHS (min p q) h (dHS (uMat (y.1 v)))) ∧
      (∀ y : B.I.GA, ‖phe B d y‖ ≤ (∏ v, d v) * (B.e 1).re) ∧
      phe B d 1 = ((∏ v, d v : ℝ) : ℂ) * B.e 1 ∧
      (B.e 1).im = 0 ∧ 0 ≤ (B.e 1).re ∧
      (∀ y : B.I.GA, phe B d y ≠ 0 → y.2 ∈ B.I.Kset) ∧ GlobalTheory.Dec.LocDec B h

def FarBound : Prop :=
  ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (h ep : ℝ),
    IsDSData B d → SigIs B p q → q = min p q → 1 ≤ q → GapGe B h →
    0 < ep → ep ≤ 1 / Real.sqrt (2 * (q : ℝ)) → 2 * (B.I.n : ℝ) ^ 2 * ep ≤ Real.log 2 →
    64 * (B.I.n : ℝ) ^ 2 ≤ h * ep → 1 ≤ h * ep ^ 2 / 16 →
    120 * (B.I.n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) ≤ h →
    ∀ x : B.I.GA,
      Summable (fun γ : GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x => ‖phe B d (x⁻¹ * γ.1 * x)‖) ∧
      ∑' γ : GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x, ‖phe B d (x⁻¹ * γ.1 * x)‖ ≤
        (∏ v, d v) * (B.e 1).re * GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.latFactor B.I x *
          (2 * (B.I.f : ℝ) * 3 ^ B.I.f * Real.exp (-(h * ep ^ 2 / 16)))

end GlobalTheory.Deep
end
end
end
