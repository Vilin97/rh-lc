module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowGood
public import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CountsIrreducibilityConstants
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountConstantsOfSiegelWeil
public import Formalism.LocalToGlobal.GlobalTheory.IrreducibleOfCountSizes
public import Formalism.LocalToGlobal.HilbertRowConditions.AllJoin
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AllRowsAtRecord
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountClausesClosed
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.GapClosed
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsFinDimLink
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsWt

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.IrreducibilityRowOfConcreteAutomorphicData

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.GlobalTheoryTheory.ConcN Formalism.L2.GlobalTheoryTheory.AllJoin Formalism.L2.SG.HidaSetting Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PackageTie2

namespace GlobalTheory.IrrRowConcrete

theorem irr_row_closed : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → Formalism.L2.SG.RowsDef.RowsFinDim → ∃ cIc : ℝ, 0 < cIc ∧ ∀ 𝒞 : FamClass, (∀ {eps : ℝ} (Fm : FamP eps), 𝒞 Fm → TuSize Fm) → (Closed 𝒞 fun Fm _ => 𝒞 Fm → ∃ x0 : ℝ, ∀ x, Fm.x1 < x → x0 ≤ x → ∀ i : Fm.Ix x, ∃ (X : HidaSetting (Fm.D x i)) (G : GoodOp X) (ι : (Fm.D x i).s.HH ≃ₗᵢ[ℂ] HHX X), AutTie (Fm.D x i) X.B X.pl ∧ RowDictTie X G ι ∧ GlobalTheory.LabPin.LabTie X ι) → Closed 𝒞 fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ A : AllRows (Fm.D x i), LabelCountGoodInjective A ∧ AllJoinA A ∧ CountAllRows A (epsC cIc (Fm.D x i).R.r (Fm.D x i).R.f) := by
  intro hSW hRF
  obtain ⟨c30, cIc, hc30, hcI, hcle, hP⟩ := GlobalTheory.CountConstants.count_constants_of_siegelWeil hSW
  refine ⟨cIc, hcI, fun 𝒞 hT hX => ?_⟩
  have hcb : ∀ {eps : ℝ} (Fm : FamP eps), 0 < (c30 Fm.cOut).cb := fun Fm =>
    (hP (fun _ _ _ _ => True) Fm).2.1
  have hEv := GlobalTheory.IrrCountEv.countClauses_closed 𝒞 c30 hc30 hcb hT
  have hGap := Formalism.L2.SG.GapClosed.gapEv_closed_of 𝒞 hT
  obtain ⟨a1, ha1, H1⟩ := (hX.and hEv).and hGap
  refine ⟨a1, ha1, fun e he hle => ?_⟩
  obtain ⟨K, hK⟩ := H1 e he hle
  refine ⟨K, fun Fm CH hc hL => ?_⟩
  obtain ⟨⟨hx, hev⟩, hg⟩ := hK Fm CH hc hL
  obtain ⟨x1, hx1⟩ := hx hc
  obtain ⟨x2, hx2⟩ := hev
  obtain ⟨y, hy⟩ := hg hc
  refine ⟨max (max x1 x2) (max y (Fm.x1 + 1)), fun x hxge i => ?_⟩
  obtain ⟨⟨b1, b2⟩, b3, b4⟩ := (max_le_iff.mp hxge).imp max_le_iff.mp max_le_iff.mp
  have hxlt : Fm.x1 < x := (lt_add_of_pos_right _ zero_lt_one).trans_le b4
  obtain ⟨X, G, ι, hA, hR, hLab⟩ := hx1 x hxlt b1 i
  obtain ⟨hpar, h4⟩ := hx2 x b2 i
  exact GlobalTheory.AllRowsAtRecord.allRows_at_record hRF (Fm.D x i) (Fm.L x i) X G ι (c30 Fm.cOut).n0 (c30 Fm.cOut).A (c30 Fm.cOut).C
    (c30 Fm.cOut).c (c30 Fm.cOut).cb cIc hcI (hcle Fm) (hy x b3 i) hA hR hLab (fun P => (hP P Fm).2.2 x i) hpar h4

end GlobalTheory.IrrRowConcrete
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.IrreducibilityRowOfConcreteAutomorphicDataStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.GlobalTheoryTheory.ConcN Formalism.L2.GlobalTheoryTheory.AllJoin Formalism.L2.SG.HidaSetting Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PackageTie2

theorem _root_.GlobalTheory.T.irreducibilityRow_of_concreteAutomorphicData : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → Formalism.L2.SG.RowsDef.RowsFinDim → ∃ cIc : ℝ, 0 < cIc ∧ ∀ 𝒞 : FamClass, (∀ {eps : ℝ} (Fm : FamP eps), 𝒞 Fm → TuSize Fm) → (Closed 𝒞 fun Fm _ => 𝒞 Fm → ∃ x0 : ℝ, ∀ x, Fm.x1 < x → x0 ≤ x → ∀ i : Fm.Ix x, ∃ (X : HidaSetting (Fm.D x i)) (G : GoodOp X) (ι : (Fm.D x i).s.HH ≃ₗᵢ[ℂ] HHX X), AutTie (Fm.D x i) X.B X.pl ∧ RowDictTie X G ι ∧ GlobalTheory.LabPin.LabTie X ι) → Closed 𝒞 fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ A : AllRows (Fm.D x i), LabelCountGoodInjective A ∧ AllJoinA A ∧ CountAllRows A (epsC cIc (Fm.D x i).R.r (Fm.D x i).R.f) := by
  exact GlobalTheory.IrrRowConcrete.irr_row_closed
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowCountsOfTies

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PackageTie2
  GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.Cp
namespace GlobalTheory.CountRow
theorem row_counts_of_ties_alt : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∀ (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition),
    Row Q Lk (AtAll fun D _ _ _ => ∃ (X : HidaSetting D) (G : GoodOp X) (ι : D.s.HH ≃ₗᵢ[ℂ] HHX X),
      AutTie D X.B X.pl ∧ RowDictTie X G ι ∧ GlobalTheory.LabPin.LabTie X ι) → _root_.GlobalTheory.Fc.R1.CountsIrreducibilityConstants' Q Lk := by
  intro hSW Q Lk hrow
  obtain ⟨c30, -, h1, -, -, h4⟩ := GlobalTheory.CountConstants.count_constants_of_siegelWeil hSW
  obtain ⟨cIc, hc, H⟩ := GlobalTheory.T.irreducibilityRow_of_concreteAutomorphicData hSW GlobalTheory.rowsFinDim_link
  refine ⟨c30, cIc, h1, hc, hrow.imp fun 𝒜 σ _ hA => ⟨?_, ?_⟩⟩
  · exact Formalism.MainNotions.Pk.Closed.of_class fun Fm _ _ => h4 _ Fm
  · exact H (D3 3 𝒜) (fun Fm hw => hw.2.2.1)
      (Formalism.MainNotions.Pk.Closed.of_class fun Fm _ hw _ => ⟨0, fun x hx _ i => hA Fm (d3_a hw) x hx i⟩)
end GlobalTheory.CountRow
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowCountsOfLabels

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc
namespace GlobalTheory.CountRowByName
theorem row_counts_of_labels_alt : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∀ (KP : ∀ B : GlobalTheory.Mem.Base, Fr B.toPre → Prop) (Q Q' : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition), (Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.RL.RowLabelCondition S Lk) → Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.CountsIrreducibilityConstants' S Lk :=
  fun hSW _ _ _ Lk ⟨R, hR, h⟩ => ⟨R, hR, _root_.GlobalTheory.CountRow.row_counts_of_ties_alt hSW _ Lk h⟩
end GlobalTheory.CountRowByName
end
end
end
