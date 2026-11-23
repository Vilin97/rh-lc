module

public import Formalism.PeriodIntegrals.JointBlockShapes.JointShape
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

-- Source module: ReciprocityTheory.ThetaSummability.RealCoinvariants.CoinvSubLeComap

section

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ThetaSummability.Real

variable {M : Type*} [AddCommGroup M] [Module ℂ M] {ι : Type*}

def coinvSub (Y : ι → Module.End ℂ M) (μ : ι → ℂ) : Submodule ℂ M :=
  ⨆ i, LinearMap.range (Y i - μ i • 1)

def jointEig (Y : ι → Module.End ℂ M) (μ : ι → ℂ) : Submodule ℂ M :=
  ⨅ i, LinearMap.ker (Y i - μ i • 1)

abbrev Coinv (Y : ι → Module.End ℂ M) (μ : ι → ℂ) := M ⧸ coinvSub Y μ

theorem coinvSub_le_comap {Y : ι → Module.End ℂ M} (μ : ι → ℂ) {T : Module.End ℂ M}
    (hT : ∀ i, Commute T (Y i)) : coinvSub Y μ ≤ (coinvSub Y μ).comap T := by
  unfold coinvSub
  apply iSup_le
  intro i
  rintro x ⟨y, rfl⟩
  rw [Submodule.mem_comap]
  apply Submodule.mem_iSup_of_mem i
  refine ⟨T y, ?_⟩
  have hc : T (Y i y) = Y i (T y) := by
    rw [← Module.End.mul_apply, (hT i).eq, Module.End.mul_apply]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul, hc]

def coinvOp {Y : ι → Module.End ℂ M} (μ : ι → ℂ) (T : Module.End ℂ M)
    (hT : ∀ i, Commute T (Y i)) : Module.End ℂ (Coinv Y μ) :=
  (coinvSub Y μ).mapQ (coinvSub Y μ) T (coinvSub_le_comap μ hT)

end ReciprocityTheory.ThetaSummability.Real
end
end
end

-- Source module: Formalism.LocalToGlobal.ThetaOperatorCommutation.RealTh

section

@[expose] public section

noncomputable section

open MvPolynomial FockH1Action ReciprocityTheory.ThetaSummability.Real

namespace ReciprocityTheory.ChartRestriction.G.ThK.Real

variable {p q r s : ℕ}

def chiTr (c : ℂ) (Z : Mat p q) : ℂ := c * Z.trace

def KCMat (p q : ℕ) : Type := {Z : Mat p q // IsKC Z}

def act1 (p q r s : ℕ) (Z : Mat p q) : Module.End ℂ (Pol p q r s) := fockAct1 p q r s Z

def polChi (p q r s : ℕ) (c : ℂ) : Submodule ℂ (Pol p q r s) :=
  jointEig (fun Z : KCMat p q => fockAct1 p q r s Z.1) (fun Z => chiTr c Z.1)

def jHarm (p q r s : ℕ) : Submodule ℂ (Pol p q r s) := Submodule.span ℂ (Jset p q r s)

abbrev ThC (p q r s : ℕ) (c : ℂ) := Coinv (act1 p q r s) (chiTr c)

def thMkC (p q r s : ℕ) (c : ℂ) : Pol p q r s →ₗ[ℂ] ThC p q r s c :=
  (coinvSub (act1 p q r s) (chiTr c)).mkQ

end ReciprocityTheory.ChartRestriction.G.ThK.Real
end
end
end
