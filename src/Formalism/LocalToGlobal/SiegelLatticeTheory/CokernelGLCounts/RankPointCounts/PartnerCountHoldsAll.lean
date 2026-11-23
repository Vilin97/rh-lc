module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCount
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GlobalCountOfSplitMode
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.LocalCountConclusions.LocCntUG
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.LocCnt0G
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.Common
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.ModularBoundZeroHolds
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumA
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.GSteps
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.CoordGHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.DetAddCor
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.SelfDualLatticesOneOrbit
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.ThetaMbe0GOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.SecondProjConjApply
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.SplitIsoCountOfComponents
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.HatZSecondProjTranspose
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.StepLiftG
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.StepSplitHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PcBridgeB
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PcIntGen
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCountOfIso

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.ThetaLocalCount.LocCnt0GOfTheta

section

@[expose] public section

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.LocCnt0GWork

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem headDet_zzplus_G {M : Model F E} (g : SplitG M.L) (hs : M.split = some g) {r : ℕ}
    (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (hD : (Zh.submatrix Fin.castSucc Fin.castSucc).det = 0)
    (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R)
    (hZ : Z.map M.R.subtype = HermSp.ZZplusOf M Zh T T') : headDet M Z = 0 := by
  set Zh' := Zh.submatrix Fin.castSucc Fin.castSucc with hZh'
  set N : Matrix (Fin r) (Fin r) E := Matrix.of fun a b =>
    g.e.symm ((g.e (Zh' a b)).1 / (g.q : F), -((g.e (Zh' b a)).2 / (g.q : F))) with hN
  have hsub : (Z.map M.R.subtype).submatrix Fin.castSucc Fin.castSucc = N := by
    rw [hZ]
    ext a b
    simp [HermSp.ZZplusOf, hs, hN, hZh', (Fin.castSucc_lt_last a).ne]
  let φ₁ : E →+* F := (RingHom.fst F F).comp g.e.toRingEquiv.toRingHom
  let φ₂ : E →+* F := (RingHom.snd F F).comp g.e.toRingEquiv.toRingHom
  have h1 : (φ₁.mapMatrix Zh').det = 0 := by rw [← RingHom.map_det, hD, map_zero]
  have h2 : (φ₂.mapMatrix Zh').det = 0 := by rw [← RingHom.map_det, hD, map_zero]
  have hN1 : φ₁.mapMatrix N = (g.q : F)⁻¹ • φ₁.mapMatrix Zh' := by
    ext a b
    simp [φ₁, hN, div_eq_inv_mul]
  have hN2 : φ₂.mapMatrix N = (-(g.q : F)⁻¹) • (φ₂.mapMatrix Zh').transpose := by
    ext a b
    simp [φ₂, hN, div_eq_inv_mul]
  have c1 : φ₁ N.det = 0 := by
    rw [RingHom.map_det, hN1, Matrix.det_smul, h1, mul_zero]
  have c2 : φ₂ N.det = 0 := by
    rw [RingHom.map_det, hN2, Matrix.det_smul, Matrix.det_transpose, h2, mul_zero]
  show ((Z.map M.R.subtype).submatrix Fin.castSucc Fin.castSucc).det = 0
  rw [hsub]
  apply g.e.injective
  rw [map_zero]
  exact Prod.ext c1 c2

theorem locCnt0G_of_theta
    (h1 : Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r n, ThetaMbe0 M r n true)) :
    Formalism.L2.SG.LocalCountModules.LocCnt0G.LocCnt0G := by
  intro F _ _ _ E _ _ _ _ M hM r n hmode V _ _ H hn t₁ f₂ f₂' φ φ' hyp hD Z₁ Z₂ hZ₁ hZ₂
  have hθ := h1 F E M hM r n hmode V H hn t₁ f₂ f₂' φ φ' hyp hD Z₁ Z₂ hZ₁ hZ₂
  obtain ⟨g, hg⟩ := Option.isSome_iff_exists.mp hmode
  have hd₁ : headDet M Z₁.Z = 0 :=
    headDet_zzplus_G g hg _ t₁.T t₁.T' (by rw [← dl_eq_det]; exact hD) Z₁.Z hZ₁
  have hd₂ : headDet M Z₂.Z = 0 :=
    headDet_zzplus_G g hg _ t₁.T t₁.T' (by rw [← dl_eq_det]; exact dl_zero_two hyp hD) Z₂.Z hZ₂
  rw [hθ]
  exact modularBoundZero_holds M r Z₁ Z₂ hd₁ hd₂

end Formalism.L2.SG.LocalCountModules.LocCnt0GWork
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.ThetaMbe0GOfSplitDu

section

@[expose] public section

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

theorem thetaMbe0G_of_split_du (hS : StepSplit) (hD : StepDu) {F : Type} [Field F] [ValuativeRel F]
    [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (r n : ℕ) : ThetaMbe0 M r n true :=
  thetaMbe0_of_detG_coordG_splitIsoCount detG_holds coordG_holds
    (splitIsoCount_of_components stepZsig0 hS firstIso_forward_holds firstIso_backward_holds firstIso_uniqueness_holds hD stepDuU) M r n

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.ThetaMbe0GOfSplit

section

@[expose] public section

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

theorem thetaMbe0G_of_split (hS : StepSplit) {F : Type} [Field F] [ValuativeRel F]
    [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (r n : ℕ) : ThetaMbe0 M r n true :=
  thetaMbe0G_of_split_du hS (stepDu_of_lift stepLiftG) M r n

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.LocalCountConclusions.ThetaMbe0True

section

@[expose] public section

namespace Formalism.L2.SG.LocalCountModules

open ValuativeRel in
theorem thetaMbe0_true {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Formalism.MainNotions.S.Loc.Model F E) (r n : ℕ) : Formalism.L2.SG.LocalCountModules.LocCntCommon.ThetaMbe0 M r n true :=
  Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork.thetaMbe0G_of_split Formalism.L2.SG.LocalCountModules.AlgGSplit.stepSplit_holds M r n

end Formalism.L2.SG.LocalCountModules
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.LocalCountConclusions.LocalCountZeroGlobalHolds

section

@[expose] public section

namespace Formalism.L2.SG.LocalCountModules

theorem localCountZeroGlobal_holds : Formalism.L2.SG.LocalCountModules.LocCnt0G.LocCnt0G :=
  Formalism.L2.SG.LocalCountModules.LocCnt0GWork.locCnt0G_of_theta (by intro F _ _ _ E _ _ _ _ M _ r n; exact thetaMbe0_true M r n)

end Formalism.L2.SG.LocalCountModules
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IntegralClosureRankAndResidueTrdegLe

section

@[expose] public section

namespace Formalism.L2.SG.LsDatumA

theorem modSide0G : ModSide0G := Formalism.L2.SG.LocalCountModules.localCountZeroGlobal_holds

theorem modSideUG : ModSideUG := Formalism.L2.SG.LocalCountModules.localCountUnitGlobal_holds

theorem integralClosureRank_and_residueTrdegLe (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.ThinScalesBound.T2 D := globalCount_of_split_mode D modSide0G modSideUG

end Formalism.L2.SG.LsDatumA
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCountHoldsAll

section

@[expose] public section

namespace Formalism.L2.SG.Pf.PCount

theorem partnerCount_holds_all {D : Formalism.BasicNotions.D7} (Zd : Formalism.L2.SG.TermLoc.LocDat D) : PartnerIsomorphismCount Zd :=
  partnerCount_of_iso Zd (Formalism.L2.SG.LsDatumA.integralClosureRank_and_residueTrdegLe D) (intGenP_holds Zd) BI.integralIsomorphism_holds

end Formalism.L2.SG.Pf.PCount
end
end
