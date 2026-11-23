module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealPf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.LamCut
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GinfTestHolds
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
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ConstFin
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ConstSm
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ContinuousThetaInf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.DKForm
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.DetTHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.AinfValueOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ExistsOrthonormalPerp
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.FibNear
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.JacOneCOfCharts
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.LamDer
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.MuBridgeB
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.OrbAll
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PerpPosV
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PolarLocalOfAction
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PushInv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.SplitG
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PushSupp
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.DetNZHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PushLF
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.SdTestC
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.RowsZP
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.UniInf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.LintegralMulRightOfMem
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.T2SpaceTensorProductFiniteExtension
import Mathlib.Tactic.Linter.HaveILetI
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.JacOneOfCharts
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.LocalSum
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.RmulFactsHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.WittInfHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.OrbPol

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.AprimeInfOfLeaves

section

@[expose] public section

namespace PI.AprimeInfW

theorem aprimeInf_iff : Formalism.L2.SG.Pf.NcReal.AprimeInf ↔ AprimeInfS := Iff.rfl

theorem aprimeInf_of (hV : AinfValue) (hG : GinfTest) : Formalism.L2.SG.Pf.NcReal.AprimeInf :=
  aprimeInf_iff.2 (aprimeInfS_of hV hG)

theorem aprimeInf_of_steps (hE : ExInf) (hP : PushInf) (hW : WeilInf) (hH : HtotInf) (hG : GinfTest) :
    Formalism.L2.SG.Pf.NcReal.AprimeInf :=
  aprimeInf_of (ainfValue_of hE hP hW hH) hG

theorem aprimeInf_of_open (hE : ExInf) (hP : PushInf) (hW : WeilInf) (hF : HinfFin) :
    Formalism.L2.SG.Pf.NcReal.AprimeInf :=
  aprimeInf_of_steps hE hP hW (htotInf_of hF) ginfTest_holds

theorem aprimeInf_of_leaves (hE : ExInf) (hP : PushInf) (hW : WeilInf) (hC : MassDataMassesW.HinfCompact) :
    Formalism.L2.SG.Pf.NcReal.AprimeInf :=
  aprimeInf_of_open hE hP hW (hinfFin_of hC)

end PI.AprimeInfW
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ExInfHolds

section

@[expose] public section

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem exInf_holds : ExInf := by
  intro D X hb FdN FdN' u u' ψ _hX hM _hS
  obtain ⟨⟨_hT1, _νH, hOm, _⟩, _⟩ := hM.1 u'
  obtain ⟨_, h1⟩ := hOm
  refine ⟨h1.1, fun μ hμ => ⟨(h1.2 μ hμ).1, fun ν hν => ?_⟩⟩
  have h2 := (h1.2 μ hμ).2 ν hν
  obtain ⟨μv, hμv⟩ := h2.1
  have h3 := h2.2 μv hμv
  obtain ⟨νv, hνv⟩ := h3.1
  exact ((h3.2 νv hνv).1)

end PI.AprimeInfW
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PolarLocalOfFibres

section

@[expose] public section

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem act_continuous {D : D7} (X : HidaSetting D) (y : TupI X) :
    Continuous (fun g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J => g • y) := by
  have : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  refine continuous_pi fun a => ?_
  change Continuous fun h : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J =>
    ((HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J h : GL (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)).mulVec (y a)
  exact (MassDataMassesW.SplitW.continuous_matHA X.B.I.cm.sig X.B.I.J (Ainf X.B.I.F)).matrix_mulVec continuous_const

theorem actMeas_holds : ActMeas := by
  intro D X Z
  have : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have : BorelSpace (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
  exact (act_continuous X Z).measurable

theorem polar_local_of_fibres (hK : KPos) (hG : GramMeas) (h1 : FibOrbAt) (h2 : PushCont) (h4 : JacOneC) : PolarLoc :=
  polar_local_of_action hK hG actMeas_holds h1 h2 h4

end PI.AprimeInfW
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PushTop

section

@[expose] public section

noncomputable section

namespace PI.AprimeInfW

theorem pushInf_of_pushLFin_of_orbUniq_of_constTest (hL : PushLFin) (hU : OrbUniq) (hC : ConstTest) : PushInf :=
  pushInf_of invPush_holds invFib_holds (lfPush_of detNZ_holds hL) lfFib_holds hU hC

end PI.AprimeInfW
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.WeilInfOf

section

@[expose] public section

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem weilInf_of (hH : HtotInf) : WeilInf := by
  intro D X hb FdN FdN' u u' hX f hf s hs
  obtain ⟨e1, e2, e3⟩ := hH X hb FdN FdN' u u' hX
  haveI : FiniteDimensional X.B.I.F X.B.I.E :=
    Module.finite_of_finrank_pos (by rw [X.B.I.cm.deg2]; norm_num)
  haveI : SecondCountableTopology (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) :=
    PI.AprimeInfT.secondCountable_HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J
  haveI : BorelSpace (Fin (D.R.rS + 1 + D.R.rS) → Fin X.B.I.n → Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) :=
    PI.AprimeInfT.borelSpace_tup (F := X.B.I.F) (E := X.B.I.E) (Ainf X.B.I.F) (D.R.rS + 1 + D.R.rS)
  haveI : X.measG.μGinf.IsHaarMeasure := X.measG_norm.2.1
  have hL : Measure.IsMulLeftInvariant ((X.measW u').μHinf : Measure (MulAction.stabilizer
      (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (ratTup (F := X.B.I.F) (Ainf X.B.I.F) (tupH (frameOf X u'))))) :=
    (X.measW_norm u').2.1.toIsMulLeftInvariant
  have h0 : (X.measW u').μHinf Set.univ ≠ 0 := by rw [e1]; exact e2.ne'
  have hfin : (X.measW u').μHinf Set.univ ≠ ⊤ := by rw [e1]; exact e3.ne
  exact PI.AprimeInfA.unfold_stab (G := HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)
    (ratTup (F := X.B.I.F) (Ainf X.B.I.F) (tupH (frameOf X u')))
    (PI.AprimeInfT.continuous_orbit (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J _)
    X.measG.μGinf (X.measW u').μHinf hL h0 hfin f hf s hs

end PI.AprimeInfW
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.WittNearP

section

@[expose] public section

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem wittNear_holds : WittNear := by
  intro D X u' ψ hT μinf νinf fibInf hP Ω a Ω' a₂ hC hC₂ T hTm hU
  obtain ⟨-, hmul, hsm, hgr, hcT, hc1, -, -⟩ := rmulFacts_holds X
  obtain ⟨u, hu⟩ := hU
  set w : TupI X := rmulT X (↑u⁻¹ : MfI X) (rmulT X (a T) (Y0 X u')) with hw
  have hgT : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (rmulT X (a T) (Y0 X u')) = (T : Matrix _ _ _) :=
    hC.2.2.2 T hTm.1
  have hgT₂ : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (rmulT X (a₂ T) (Y0 X u')) = (T : Matrix _ _ _) :=
    hC₂.2.2.2 T hTm.2
  have hY0 : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (Y0 X u') =
      (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Ainf X.B.I.F)) :=
    gramR_ratTup (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))
  have hinv1 : cTI X (↑u⁻¹ : MfI X) * cTI X (↑u : MfI X) = 1 := by
    rw [← hcT, Units.mul_inv, hc1]
  have hgw : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J w =
      (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Ainf X.B.I.F)) := by
    rw [hw, hgr, hgT, ← hgT₂, ← hu, hgr, hY0]
    rw [show cTI X (↑u⁻¹ : MfI X) * (cTI X (↑u : MfI X) *
        (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Ainf X.B.I.F)) * (↑u : MfI X)) *
        (↑u⁻¹ : MfI X) = (cTI X (↑u⁻¹ : MfI X) * cTI X (↑u : MfI X)) *
        (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Ainf X.B.I.F)) *
        ((↑u : MfI X) * (↑u⁻¹ : MfI X)) by simp only [Matrix.mul_assoc],
      hinv1, Units.mul_inv, Matrix.one_mul, Matrix.mul_one]
  have h2 : Module.finrank X.B.I.F X.B.I.E = 2 := X.B.I.cm.deg2
  have hfix : ∀ b : X.B.I.E, X.B.I.cm.sig b = b ↔ b ∈ (algebraMap X.B.I.F X.B.I.E).range :=
    fun b => X.B.I.cm.fixed b
  have hinv : ∀ x, X.B.I.cm.sig (X.B.I.cm.sig x) = x := fun x => star_star x
  have hJ : IsHermND X.B.I.cm.sig X.B.I.J := by
    refine ⟨fun i j => ?_, X.B.I.J_det⟩
    have := congrFun (congrFun X.B.I.J_herm i) j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at this
    exact this
  have hdet := detNZ_holds X u' ψ hT μinf νinf fibInf hP
  have hUC : PIW.AdelicOrbitU.UnitChoice (Ainf X.B.I.F) :=
    PIW.AdelicOrbitU.uc_pi (fun v : NumberField.InfinitePlace X.B.I.F => v.Completion)
  obtain ⟨g, hg⟩ := PI.AprimeInfWitt.witt_R X.B.I.cm.sig h2 hfix hinv X.B.I.J hJ (tupH (frameOf X u')) hT hdet
    (Ainf X.B.I.F) hUC w hgw
  refine ⟨g, ?_⟩
  have hback : rmulT X (↑u : MfI X) w = rmulT X (a T) (Y0 X u') := by
    rw [hw, hmul, Units.inv_mul, rmulT_one]
  rw [← hback, ← hu, hsm]
  congr 1
  exact hg.symm

end PI.AprimeInfW
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Assembly

section

@[expose] public section

namespace PI.AprimeInfAsm

open PI.AprimeInfW

theorem aprimeInf_of_good (hC : MassDataMassesW.HinfCompact) (hG : GoodChartEx) :
    Formalism.L2.SG.Pf.NcReal.AprimeInf :=
  have hJ : JacOneC := jacOneC_of_charts kPos_holds unimodInf_holds wittNear_holds hG
  aprimeInf_of_leaves exInf_holds
    (pushInf_of_pushLFin_of_orbUniq_of_constTest (pushLFin_of_compact hC) (orbUniq_of_compact hC)
      (constTest_of_polar_compact
        (polar_local_of_fibres kPos_holds gramMeas_holds (fibOrbAt_of_compact hC) (pushCont_of_compact hC) hJ) hC))
    (weilInf_of (htotInf_of (hinfFin_of hC))) hC

theorem aprimeInf_of_std (hC : MassDataMassesW.HinfCompact) (hG : GrpStd) (hT : TupStd) :
    Formalism.L2.SG.Pf.NcReal.AprimeInf :=
  aprimeInf_of_good hC (goodChartEx_of_witt linIndW_holds perpPosV wittLin_holds hG hT)

theorem lamDet_of_open (hN : NuBridge) (hP : PlaceJacAll) : LamDet :=
  lamDet_of betaIso_holds muBridge_holds hN dKForm_holds rowsZ_holds detT_holds hP

theorem aprimeInf_of_grp (hC : MassDataMassesW.HinfCompact) (hG : GrpStd) (hN : NuBridge) (hP : PlaceJacAll) :
    Formalism.L2.SG.Pf.NcReal.AprimeInf :=
  aprimeInf_of_std hC hG (tupStd_of_sm kapSm_holds (lamDet_of_open hN hP))

end PI.AprimeInfAsm
end
end
