module

public import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameDegreeZeroFormsSelf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
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
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InstExists
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocalAdditiveCharContinuous
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataConc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ColDict
public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.MultiplicityOneUnitaryBranchingOfGapHyp
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColDictCoreHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHGamUnipKu
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHLatOfLattice
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHFinOrd
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGlobalSetting
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrablePhLocOfIntegrablePh
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFdegFdegOfLowest
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.IotaKerHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.NeatTies
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.FinLevi
import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TypedFinal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.FullExistsTiedHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictFinal

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowDictGoodOpNonempty

section

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace GlobalTheory

theorem rowDict_goodOp_nonempty :
    ∀ (D : D7) (X : HidaSetting D), Nonempty (Formalism.L2.SG.RowDict.GoodOp X) :=
  fun _ X => Formalism.L2.SG.Pf.rowDictGoodOp_exists X

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnLevelStabTriv

section

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PackageTie2

namespace GlobalTheory

theorem columnLevel_stabTriv :
    ∀ (D : D7) (X : HidaSetting D) (hK : X.LevelSubgroupCharacter) (u : D.what₂.Word),
      Formalism.L2.SG.ColsDim.StabTriv (iotaF X u) (Ku X u hK) := by
  intro D X hK u h γ hγ

  have hfin : IsOfFinOrder γ :=
    Formalism.L2.SG.PoincareInHH.Cut.gamFinKu_of X u hK
      (Formalism.L2.SG.PoincareInHH.Cut.latOfLattice_holds X u) h γ hγ
  exact Formalism.L2.SG.PoincareInHH.Cut.gamUnipKu_holds X u hK h γ hγ hfin

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteDimensionalHHX

section

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace GlobalTheory.RowsFiniteDim

theorem finiteDimensional_HHX : Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (X : HidaSetting D),
    Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) → FiniteDimensional ℂ (HHX X) := by
  intro hHC D X h
  exact hHC X.B.I X.B.μf X.B.fund X.B.fund_spec X.B.R X.B.R_spec X.B.e X.B.Re X.B.e_adm.1
    X.B.e_adm.2.2.2.2.1 X.B.Re_spec
    X.B.H X.B.σ (fun v => fdegOf (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.B.w v)) X.B.w
    (fun v => (X.ds v).2.2.1) (fun v => (X.ds v).2.2.2.1)
    (fun v => GlobalTheory.LowestVectorDegree.isFdeg_fdegOf_lowest D X v) (fun v => (X.low v).1)
    (GlobalTheory.ProdFactor.integrable_phLoc_of_integrable_ph D X h) X.Rph X.Rph_spec

end GlobalTheory.RowsFiniteDim
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.FinXOfDecay

section

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PackageTie2

namespace GlobalTheory.FinitenessBundle

open Formalism.MainNotions.S.Lat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem star_Gflag {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} (n m : ℕ)
    (F : FlagG S r (n : E)) (F' : FlagG S r (m : E)) : star (Gflag F F') = Gflag F F' := by
  simp only [Gflag, star_sub, star_mul', star_star, star_natCast]
  ring

theorem finX_of_decay : Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X),
    Formalism.L2.SG.WuDecay.WuDecay X → Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) → FinX Y := by
  intro hR D X Y hW hI
  refine Formalism.L2.SG.Pf.finX_of_neat Y (fun u => Formalism.L2.SG.Closed.NeatKu_holds X u Y.hK) (fun u => ?_)
    (GlobalTheory.RowsFiniteDim.finiteDimensional_HHX hR D X hI) (fun u u' t => Formalism.L2.SG.Pf.FinXP.fibFin_holds D X Y u u' t)
    (fun u u' s₁ s₂ s₁' s₂' => Formalism.L2.SG.Pf.FinXP.pairIndep_of Formalism.L2.SG.Pf.KernelOfEmbedding.IotaKer_holds D X Y u u' s₁ s₂ s₁' s₂')
    (fun u u' t => ?_) Formalism.L2.SG.Closed.VolPosC_holds
  · have hL : X.LevelSubgroupNormalized := Formalism.L2.SG.Closed.level_subgroup_properties X
    exact Formalism.L2.SG.Closed.InHHC_holds D X Y u hI (Formalism.L2.SG.Closed.FoldOKC_holds Formalism.L2.SG.Pf.FinLeviPf.finLeviC_holds D X Y u hL hW)
  · rw [← NumberField.IsCMField.complexConj_eq_self_iff]
    exact star_Gflag _ _ _ _

end GlobalTheory.FinitenessBundle
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.FullExistsOfLocTied

section

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace GlobalTheory

theorem fullExists_of_locTied : ∀ (D : D7) (X : HidaSetting D), Formalism.L2.SG.Pf.LocCP.LocTied D → Nonempty (Formalism.L2.SG.Full.Full X) := by

  intro D X hT
  exact Formalism.L2.SG.Pf.fullExists_tied Formalism.L2.SG.Pf.trExistsC_holds Formalism.L2.SG.Pf.lattice_steps_hold
    Formalism.L2.SG.Closed.LocCTied_holds D X (Formalism.L2.SG.Closed.level_subgroup_is_group X) hT

end GlobalTheory
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BesselSpectral

section

@[expose] public section

section
noncomputable section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PackageTie2 Formalism.L2.SG.ColDict
open GlobalTheory.St.SpectralData
namespace UpperTheory.Lit
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem exists_spectralData_gap_alt : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (F : ∀ u, Formalism.L2.Forms.Forms0 D u), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → Formalism.L2.SG.Pf.LocCP.LocTied D → ∃ (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (Y : Formalism.L2.SG.Full.Full X) (hF : FinX Y) (tr : ∀ u, Transport X u (F u)), X.B.I = Formalism.L2.SG.InstExistsPf.instOf D ∧ (∀ x : X.B.I.E, HEq (X.ιE x) x) ∧ X.MeasTie hb ∧ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ ∧ Formalism.L2.SG.LocVol.IsStdChar ψ ∧ Formalism.L2.SG.MassDataConc.MeasCompatψ X ψ ∧ (∀ w, Formalism.L2.SG.LocVol.LocCompatX X ψ w) ∧ Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) ∧ ∀ u, LevelMatch X (tr u) Y.hK ∧ ColDictInto X (tr u) Y.hK ∧ ColDictBij X (tr u) Y.hK ∧ ColDictIsom X (tr u) Y.hK (Y.cs u) (hF.shInj u) := by
  intro hSW hRF D F hG hLT
  obtain ⟨X, hb, ψ, hI, hι, hM, hψ, hstd, hCm, hL, hT⟩ := exists_setting hSW D F hG
  obtain ⟨Y⟩ := GlobalTheory.fullExists_of_locTied D X hLT
  obtain ⟨hWD, hph⟩ := CompanionTheory.Lime.BM.wuDecayOfGap_holds' D hG X
  have hF : FinX Y := GlobalTheory.FinitenessBundle.finX_of_decay hRF D X Y hWD hph
  choose tr htr using hT Y.hK
  refine ⟨X, hb, ψ, Y, hF, tr, hI, hι, hM, hψ, hstd, hCm, hL, hph, fun u => ?_⟩
  obtain ⟨-, h1, h2, h3⟩ := GlobalTheory.St.colDictCore_holds D X u (F u) (tr u) Y.hK (htr u)
    (GlobalTheory.columnLevel_stabTriv D X Y.hK u)
  exact ⟨htr u, h1, h2, h3 _ (Y.cs u) (hF.shInj u) (Y.colReps u)⟩
end UpperTheory.Lit
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.LocalBesselUniquenessHolds

section

@[expose] public section

section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PackageTie2 Formalism.L2.SG.ColDict

theorem _root_.GlobalTheory.T.local_bessel_uniqueness_holds : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (F : ∀ u, Formalism.L2.Forms.Forms0 D u), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → Formalism.L2.SG.Pf.LocCP.LocTied D → ∃ (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (Y : Formalism.L2.SG.Full.Full X) (hF : FinX Y) (tr : ∀ u, Transport X u (F u)), X.B.I = Formalism.L2.SG.InstExistsPf.instOf D ∧ (∀ x : X.B.I.E, HEq (X.ιE x) x) ∧ X.MeasTie hb ∧ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ ∧ Formalism.L2.SG.LocVol.IsStdChar ψ ∧ Formalism.L2.SG.MassDataConc.MeasCompatψ X ψ ∧ (∀ w, Formalism.L2.SG.LocVol.LocCompatX X ψ w) ∧ Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) ∧ ∀ u, LevelMatch X (tr u) Y.hK ∧ ColDictInto X (tr u) Y.hK ∧ ColDictBij X (tr u) Y.hK ∧ ColDictIsom X (tr u) Y.hK (Y.cs u) (hF.shInj u) := by
  first | exact @_root_.UpperTheory.Lit.exists_spectralData_gap_alt | exact _root_.UpperTheory.Lit.exists_spectralData_gap_alt | (intros; apply _root_.UpperTheory.Lit.exists_spectralData_gap_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsSPackIntegrable

section

@[expose] public section

section
open scoped Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2 Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.SG.RowDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.ConcreteSettingExists GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.SRe
theorem exists_sPack_integrable_alt :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → Formalism.L2.SG.RowsDef.RowsFinDim →
      ∀ (D : D7) (F : ∀ u, Forms0 D u), GapHyp D → Formalism.L2.SG.Pf.LocCP.LocTied D →
        ∃ P : SPack D F, Integrable P.X.ph (Formalism.L2.SG.ProjRows.muInf P.X.B.I) := by
  intro hSW hRF D F hG hL
  obtain ⟨X, hb, ψ, Y, hF, tr, hinst, hpin, hmt, hch, hstd, hmc, hlc, hint, hu⟩ :=
    _root_.GlobalTheory.T.local_bessel_uniqueness_holds hSW hRF D F hG hL
  obtain ⟨G⟩ := GlobalTheory.rowDict_goodOp_nonempty D X
  exact ⟨⟨X, hb, Y, hF, ψ, hmt, hch, hstd, hmc, hlc, tr, fun u => (hu u).2.1, fun u => (hu u).2.2.1,
    fun u => (hu u).1, fun u => (hu u).2.2.2, hinst, G, hpin⟩, hint⟩
end GlobalTheory.Mem.SRe
end
end
end
