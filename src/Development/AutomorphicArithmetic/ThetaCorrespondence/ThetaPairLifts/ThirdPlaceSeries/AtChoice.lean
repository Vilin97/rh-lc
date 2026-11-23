module

public import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AllRows
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CountsIrreducibilityConstants
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OffK0Closed
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowPositivityOfSiegelWeil
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsFinDimLink
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SwxsOfSiegelWeil
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryHyperplaneVolumeRatioSiegelWeil
public import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TSelF
public import Formalism.SharpRestriction.GlobalSchurBounds.MassRatioUnfoldedOfTheoremTwo
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
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RanksAndFrameOfTiedClass
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LoopRowsOfRowsFinDim

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryHyperplaneVolumeRatioSiegelWeilStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.unitary_hyperplane_volumeRatio_siegelWeil : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∀ D : Formalism.BasicNotions.D7, Formalism.MainNotions.RT.MassRatioUnderVolume D := by
  first | exact @GlobalTheory.VolRatioFromSiegelWeil.volumeRatio | exact GlobalTheory.VolRatioFromSiegelWeil.volumeRatio | (intros; apply GlobalTheory.VolRatioFromSiegelWeil.volumeRatio <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RanksAndFrameOfTiedClassStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions

theorem _root_.GlobalTheory.T.ranksF_tFrame_closed_of_mass_ratio : (∀ D : D7, RT.MassRatioUnderVolume D) → ∀ (𝒞 : FamClass), _root_.Formalism.L2.TwistSelection 𝒞 → (Closed 𝒞 fun Fm _ => PX.RanksF Fm 3 (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu) ∧ Closed 𝒞 fun Fm _ => PX.TFrame Fm (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu 3 := by
  first | exact @_root_.GlobalTheory.ranks_and_frame_of_tied_class_alt | exact _root_.GlobalTheory.ranks_and_frame_of_tied_class_alt | (intros; apply _root_.GlobalTheory.ranks_and_frame_of_tied_class_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BothRowsFromSiegelWeil

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions
namespace GlobalTheory
theorem bothRowsFromSiegelWeil_alt :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∀ (𝒞 : FamClass), _root_.Formalism.L2.TwistSelection 𝒞 →
      (Closed 𝒞 fun Fm _ => PX.RanksF Fm 3 (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu) ∧
        Closed 𝒞 fun Fm _ => PX.TFrame Fm (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu 3 :=
  fun hSW => _root_.GlobalTheory.T.ranksF_tFrame_closed_of_mass_ratio (GlobalTheory.T.unitary_hyperplane_volumeRatio_siegelWeil hSW)
end GlobalTheory
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtChoice

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.Cp
namespace GlobalTheory.LocalRows
theorem at_choice_alt (hSW : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent) (𝒜 : FamClass) (σ : RawSel _root_.GlobalTheory.Fc.BundleCondition 𝒜) :
    _root_.GlobalTheory.Fc.R1.SelectionLpBound 𝒜 σ ∧ _root_.GlobalTheory.Fc.R1.SelectionOrderBound 𝒜 σ ∧ R1.H_hTF 𝒜 := by
  let T : _root_.Formalism.L2.TwistSelection (D3 3 𝒜) := fun Fm hc => (_root_.GlobalTheory.Fc.familySelection σ) Fm (d3_a hc)
  have hB := _root_.GlobalTheory.bothRowsFromSiegelWeil_alt hSW (D3 3 𝒜) T
  have hL : _root_.GlobalTheory.Fc.R1.SelectionLpBound 𝒜 σ :=
    _root_.GlobalTheory.LoopRowsByName.loopRows_of_rowsFinDim_alt GlobalTheory.rowsFinDim_link (GlobalTheory.VolRatioFromSiegelWeil.volumeRatio hSW) (D3 3 𝒜) T _ (fun Fm hw => hw.2.2.1)
  exact ⟨hL, GlobalTheory.CarrierGap.offDiag (GlobalTheory.St.swxs_of_siegelWeil hSW) (GlobalTheory.rowNGP_of_siegelWeil hSW) GlobalTheory.rowsFinDim_link (D3 3 𝒜) _
    (fun Fm hc x hx h i => ((_root_.GlobalTheory.Fc.spectralConditionOfRawSelection σ) Fm (d3_a hc) x hx h i).locTied) hB.1 hL, hB.2⟩
theorem sLp_sO_hTF_of_siegelWeil : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∀ (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition), _root_.GlobalTheory.Fc.R1.SlotLpCondition Q Lk ∧ _root_.GlobalTheory.Fc.R1.SlotOrderCondition Q Lk ∧ _root_.GlobalTheory.Fc.R1.SlotTorsionFreeCondition Q Lk := fun hSW Q Lk =>
  ⟨Row.of_sel fun 𝒜 σ _ => (_root_.GlobalTheory.LocalRows.at_choice_alt hSW 𝒜 σ).1, Row.of_sel fun 𝒜 σ _ => (_root_.GlobalTheory.LocalRows.at_choice_alt hSW 𝒜 σ).2.1,
    Row.of_sel fun 𝒜 σ _ => (_root_.GlobalTheory.LocalRows.at_choice_alt hSW 𝒜 σ).2.2⟩
theorem lg1_sLp_sO_hTF : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∀ (KP : ∀ B : GlobalTheory.Mem.Base, Fr B.toPre → Prop) (Q Q' : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition), (Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotLpCondition S Lk) ∧ (Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotOrderCondition S Lk) ∧ Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotTorsionFreeCondition S Lk := fun hSW KP Q Q' Lk =>
  ⟨⟨_, largeBaseProperty_true, (_root_.GlobalTheory.LocalRows.sLp_sO_hTF_of_siegelWeil hSW _ Lk).1⟩, ⟨_, largeBaseProperty_true, (_root_.GlobalTheory.LocalRows.sLp_sO_hTF_of_siegelWeil hSW _ Lk).2.1⟩, ⟨_, largeBaseProperty_true, (_root_.GlobalTheory.LocalRows.sLp_sO_hTF_of_siegelWeil hSW _ Lk).2.2⟩⟩
end GlobalTheory.LocalRows
end
end
end
