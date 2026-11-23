module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleOrbitalFourierRankOneTransferStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisFourierMatchOfWeilRepresentation
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilConstantStandardHermitianEqOneStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRepresentationEtaleOfQuadraticFieldStatement
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisUnitMatchSuccStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilConstantStandardHermitianEqOneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRepresentationEtaleOfQuadraticFieldStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRepresentationQuadraticFieldExists

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisFourierMatchOfWeilRepresentationStatement

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.jacquetRallisFourierMatch_of_weilRepresentation : WeilEt → RankOne → GammaOne → ∀ r, FourierMatch r := by
  first | exact @GlobalTheory.JR.fourierMatch_of_weil | exact GlobalTheory.JR.fourierMatch_of_weil | (intros; apply GlobalTheory.JR.fourierMatch_of_weil <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisFourierMatchingOfWeilField

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem fourierMatch_of_weilField : WeilField → ∀ r, FourierMatch r := fun h =>
  GlobalTheory.T.jacquetRallisFourierMatch_of_weilRepresentation (GlobalTheory.T.weilRepresentationEtale_of_quadraticField h) GlobalTheory.T.etaleOrbitalFourier_rankOne_transfer GlobalTheory.T.weilConstantStandardHermitian_eq_one

end GlobalTheory.JR
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisFourierMatchingOfWeilFieldStatement

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.jacquetRallis_fourier_matching_of_weil_field : WeilField → ∀ r, FourierMatch r := by
  first | exact @GlobalTheory.JR.fourierMatch_of_weilField | exact GlobalTheory.JR.fourierMatch_of_weilField | (intros; apply GlobalTheory.JR.fourierMatch_of_weilField <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisUnitMatchSizeOne

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.SizeOne

theorem eta_one' {F : Type} [NormedField F] : eta (1 : F) = 1 := by
  unfold eta
  rw [if_pos ⟨1, by simp⟩]

theorem unitMatch_zero : UnitMatch 0 := by
  intro F E _ _ _ _ _ M a _
  letI := M.mG; letI := M.mU
  have hG : M.μG Set.univ = 1 := by
    rw [← M.volG]; congr 1; ext g; simp [glO]
  have hU : M.μU Set.univ = 1 := by
    rw [← M.volU]; congr 1; ext g; simp [uO]
  have hw : ∀ Y : Gl 0 F, omega Y = 1 := by
    intro Y
    have : lastDet Y = 1 := by simp [lastDet, Fin.last]
    rw [omega, this, eta_one']
  refine ⟨fun X hX => ?_, fun hn => (hn ⟨(0, 0, a.2.2), ?_⟩).elim⟩
  · have hl : X.2.2 = a.2.2 := (algebraMap F E).injective (congrArg (fun t => t.2.2) hX)
    by_cases hb : ‖a.2.2‖ ≤ 1 <;>
      simp [orbG, orbU, hw, unitG, unitU, act, actU, sec, Set.indicator, hl, hb, Measure.real, hG, hU]
  · exact Prod.ext (Subsingleton.elim _ _) (Prod.ext (Subsingleton.elim _ _) rfl)

end GlobalTheory.JR.SizeOne
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisUnitMatchSizeOneStatement

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.jacquetRallisUnitMatch_sizeOne : UnitMatch 0 := by
  first | exact @GlobalTheory.JR.SizeOne.unitMatch_zero | exact GlobalTheory.JR.SizeOne.unitMatch_zero | (intros; apply GlobalTheory.JR.SizeOne.unitMatch_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisUnitMatchOfWeilRepQuadratic

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem unitMatch_of_weilField : WeilField → ∀ r, UnitMatch r := by
  intro hW r
  induction r with
  | zero => exact GlobalTheory.T.jacquetRallisUnitMatch_sizeOne
  | succ r ih => exact GlobalTheory.T.jacquetRallisUnitMatch_succ (GlobalTheory.T.weilRepresentationEtale_of_quadraticField hW) GlobalTheory.T.weilConstantStandardHermitian_eq_one r (GlobalTheory.T.jacquetRallis_fourier_matching_of_weil_field hW (r + 1)) ih

end GlobalTheory.JR
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisUnitMatchOfWeilRepQuadraticStatement

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.jacquetRallisUnitMatch_of_weilRep_quadratic : WeilField → ∀ r, UnitMatch r := by
  first | exact @GlobalTheory.JR.unitMatch_of_weilField | exact GlobalTheory.JR.unitMatch_of_weilField | (intros; apply GlobalTheory.JR.unitMatch_of_weilField <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRepresentationQuadraticFieldExistsStatement

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.weilRepresentation_quadraticField_exists : WeilField := by
  first | exact @GlobalTheory.JR.WeilQuad.weilField_main | exact GlobalTheory.JR.WeilQuad.weilField_main | (intros; apply GlobalTheory.JR.WeilQuad.weilField_main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisUnitMatchAllRanks

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem unitMatch_all : ∀ r, UnitMatch r :=
  GlobalTheory.T.jacquetRallisUnitMatch_of_weilRep_quadratic GlobalTheory.T.weilRepresentation_quadraticField_exists

end GlobalTheory.JR
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisUnitMatchAllRanksStatement

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.jacquetRallisUnitMatch_all_ranks : ∀ r, UnitMatch r := by
  first | exact @GlobalTheory.JR.unitMatch_all | exact GlobalTheory.JR.unitMatch_all | (intros; apply GlobalTheory.JR.unitMatch_all <;> assumption)
end
end
