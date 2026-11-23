module

public import Formalism.LatticeSlopes.CovolAntiSameRank
import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolEqCovolume
public import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolEqGram
public import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolPos
public import Formalism.LatticeSlopes.LatticeSlopesProofs.DegQuot
import Formalism.LatticeSlopes.LatticeSlopesProofs.FiniteSaturated
public import Formalism.LatticeSlopes.LatticeSlopesProofs.GramDetLe
public import Formalism.LatticeSlopes.LatticeSlopesProofs.DiscreteTopologyOfLe
public import Formalism.LatticeSlopes.LatticeSlopesProofs.MuMaxAttained
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import Formalism.LatticeSlopes.LatticeSlopesProofs.OrthSum
public import Formalism.LatticeSlopes.LatticeSlopesProofs.SaturationProperties
import Formalism.LatticeSlopes.LatticeSlopesProofs.ShortVector
import Formalism.LatticeSlopes.LatticeSlopesProofs.SlopeLeMuMaxOf
import Formalism.LatticeSlopes.LatticeSlopesProofs.SlopesBdd
import Mathlib.Tactic.TypeStar

-- Source module: Formalism.LatticeSlopes.LatticeSlopesProofs.MuMaxLeMin

section

@[expose] public section

open Module

namespace Formalism.F

universe u

theorem muMaxLeMin_of (hP : CovolPos.{u}) (hS : ShortVector.{u}) : MuMaxLeMin.{u} := by
  intro E _ _ _ L hL hL0 r hr hmin
  haveI := hL
  have hne : (slopes L).Nonempty := ⟨slope L, L, le_rfl, hL0, rfl⟩
  unfold muMax
  apply csSup_le hne
  rintro t ⟨N, hNL, hN0, rfl⟩
  haveI : DiscreteTopology N := discreteTopology_of_le hNL
  have hk : 0 < rk N := att_rk_pos hN0
  have hkL : rk N ≤ rk L := att_rk_le hNL
  have hc : 0 < covol N := hP E N inferInstance
  obtain ⟨v, hvN, hv0, hvle⟩ := hS E N inferInstance hN0
  have hrv : r ≤ ‖v‖ := hmin v (hNL hvN) hv0
  have hk' : (0 : ℝ) < (rk N : ℝ) := by exact_mod_cast hk

  have h1 : Real.log r ≤ Real.log (rk N : ℝ) / 2 + Real.log (covol N) / (rk N : ℝ) := by
    have hpow : 0 < covol N ^ ((1 : ℝ) / (rk N : ℝ)) := Real.rpow_pos_of_pos hc _
    have hsq : 0 < Real.sqrt (rk N : ℝ) := Real.sqrt_pos.mpr hk'
    have h := Real.log_le_log hr (hrv.trans hvle)
    rw [Real.log_mul hsq.ne' hpow.ne', Real.log_sqrt hk'.le, Real.log_rpow hc] at h
    have e : (1 : ℝ) / (rk N : ℝ) * Real.log (covol N) = Real.log (covol N) / (rk N : ℝ) := by ring
    linarith
  have h2 : Real.log (rk N : ℝ) ≤ Real.log (rk L : ℝ) :=
    Real.log_le_log hk' (by exact_mod_cast hkL)
  have h3 : slope N = -(Real.log (covol N) / (rk N : ℝ)) := by
    unfold slope deg; ring
  rw [h3]
  linarith

end Formalism.F
end
end

-- Source module: Formalism.LatticeSlopes.ExistsSaturatedSlopeEqMuMax

section

@[expose] public section

namespace Formalism.F

theorem covolEqGram : CovolEqGram := covol_eq_gram
theorem covolPos : CovolPos := covol_pos'
theorem covolBasic : CovolBasic := covol_basic_properties
theorem covolEqCovolume : CovolEqCovolume := covol_eq_covolume'
theorem gramDetLe : GramDetLe := gram_det_le
theorem slopesBdd : SlopesBdd := slopesBdd_of gramDetLe
theorem slopeLeMuMax : SlopeLeMuMax := slopeLeMuMax_of slopesBdd
theorem degQuot : DegQuot := degree_quotient
theorem covolAntiSameRank : CovolAntiSameRank := covol_anti_same_rank
theorem saturProps : SaturProps := saturation_properties
theorem shortVector : ShortVector := shortVector_of covolEqCovolume
theorem finiteSaturated : FiniteSaturated := finiteSaturated_of shortVector
theorem muMaxLeMin : MuMaxLeMin := muMaxLeMin_of covolPos shortVector
theorem orthSum : OrthSum := orthogonal_sum_slope

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem covol_pos (L : Submodule ℤ E) [DiscreteTopology L] : 0 < covol L :=
  covolPos E L ‹_›

theorem deg_eq_deg_add_deg_quot {L N : Submodule ℤ E} [DiscreteTopology L] (hN : IsSaturated L N) :
    deg L = deg N + deg (quot L N) :=
  (degQuot E L N ‹_› hN).2.2

end

end Formalism.F
end
end
