module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ClassCountBoundAtConstructedPoints
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassNumberAll
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
public import Formalism.SharpRestriction.ParConsts

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ClassNumberClosed

section

@[expose] public section

namespace GlobalTheory.ColClassNumber

open Formalism.MainNotions

theorem classNumber_closed (𝒞 : FamClass) :
    Closed 𝒞 fun Fm _ => ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), StandardLattice.ClassNumberFormula₂ (Fm.D x i) (Fm.ex x hx i).lev :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩,
    fun Fm _ _ _ x hx i => classNumber_all (Fm.D x i) (Fm.ex x hx i).lev⟩⟩

end GlobalTheory.ColClassNumber
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ScaleOneLeA

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField IsDedekindDomain

namespace GlobalTheory

theorem scale_one_le_a (s : Scale) : 1 ≤ s.a := by
  have hx : 1 < s.x := s.one_lt_alt
  have hL : 0 ≤ s.L := by
    unfold Scale.L
    exact Real.rpow_nonneg (by linarith) _
  have hb : 1 ≤ s.b := by
    unfold Scale.b
    exact Real.one_le_exp hL
  unfold Scale.a
  exact one_le_mul_of_one_le_of_one_le hx.le hb

theorem famP_La_nonneg : ∀ (eps : ℝ) (Fm : FamP eps), ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x,
    0 ≤ (Fm.L x i).La := by
  intro eps Fm x hx i
  obtain ⟨-, -, -, -, -, -, hQD, -⟩ := Fm.sizes x hx i
  obtain ⟨-, -, -, -, -, -, hrd, -⟩ := hQD
  unfold SizeData₂.La
  exact Real.log_nonneg (one_le_mul_of_one_le_of_one_le (scale_one_le_a _) hrd)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ClassCountBoundParamsLambdaConstructedPoints

section

@[expose] public section

namespace GlobalTheory.Fc.R0

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mem.Top GlobalTheory.Fc

theorem h_la_all (𝒜 : FamClass) : H_la 𝒜 :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩,
    fun Fm _ _ _ => ⟨Fm.x1 + 1, fun x hx i => GlobalTheory.famP_La_nonneg _ Fm x (by linarith) i⟩⟩⟩

theorem classCountBound_all_classes (𝒜 : FamClass) : ClassCountBoundAllPoints 𝒜 :=
  GlobalTheory.ColClassNumber.classNumber_closed (W1 𝒜)

theorem classCountBound_paramsLambda_constructedPoints : ∀ (Bd : BdT) (Q : V4.Slot) (Lk : LkT Bd), R0.ClassCountBoundAtConstructedPoints Q Lk ∧ R0.LambdaConditionAtConstructedPoints Q Lk := by
  intro Bd Q Lk
  refine ⟨?_, ?_⟩
  · apply Row.of_sel
    intros
    exact classCountBound_all_classes _
  · apply Row.of_sel
    intros
    exact h_la_all _

end GlobalTheory.Fc.R0
end
end
