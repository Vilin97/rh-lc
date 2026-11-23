module

public import Formalism.SharpRestriction.GlobalSchurBounds.MainSup
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.LocalRingCardinality.IntCastDvdOfDvdIntegers
public import Formalism.LocalRingCardinality.SpanPowerMembership.PlacesOverNcardOfSplitInj
public import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLt
public import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLu
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
import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLu

-- Source module: Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLz

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions NumberField

theorem level_prime_splits_totally_real (D : D7) (u : D.what₂.Word) : StandardLattice.SplitsF D (D.mem u).A.T := by
  have : Fact (D.mem u).A.T.Prime := ⟨(D.mem u).A.T_prime⟩
  have h := Formalism.BasicNotions.Examples₂.placesOver_ncard_of_split D.host (D.mem u).A.T (D.T_mod_cond u)
  have h' := splits_sub D.host.F (D.mem u).A.T D.host.E (D.mem u).A.T_prime h
  rw [finrank_F_eq] at h'
  exact h'

end Formalism.MainNotions.J

end
end
end

-- Source module: Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.LwRankTies

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.Ext.Lw

open Formalism.BasicNotions Formalism.MainNotions

theorem splitsF_g_all (D : D7) : ∀ j, StandardLattice.SplitsF D (D.host.g j) := fun j => J.splitsF_g D j

theorem splitsF_T_all (D : D7) (u : D.what₂.Word) : StandardLattice.SplitsF D (D.mem u).A.T := J.level_prime_splits_totally_real D u

theorem rank_conditions_iff_lowest_space {eps : ℝ} (Fm : FamP eps) :
    RankTiesF Fm ↔ ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word), StandardLattice.Mu0Tie (Fm.D x i) u := by
  unfold RankTiesF
  constructor
  · rintro ⟨x0, hx0⟩
    exact ⟨x0, fun x hx i u => ((hx0 x hx i).2 u).2⟩
  · rintro ⟨x0, hx0⟩
    exact ⟨x0, fun x hx i => ⟨splitsF_g_all (Fm.D x i), fun u => ⟨splitsF_T_all (Fm.D x i) u, hx0 x hx i u⟩⟩⟩

theorem rank_conditions_of_lowest_space {eps : ℝ} (Fm : FamP eps)
    (h : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word), StandardLattice.Mu0Tie (Fm.D x i) u) : RankTiesF Fm :=
  (rank_conditions_iff_lowest_space Fm).2 h

end Formalism.MainNotions.Ext.Lw

end
end
end
