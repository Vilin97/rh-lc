module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
public import Formalism.LocalToGlobal.HilbertRowConditions.AllJoin
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCountE
public import Formalism.LocalToGlobal.GlobalTheory.IrreducibleOfCountSizes
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsEtOne
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JCount
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsCountBase
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowsGoodRed
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsAdd
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.AllRowsOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTRph
import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsDS
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
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsClosed
import Mathlib.Tactic.Linter.Style
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsPCount
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsRedKer
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsAddFin

section

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf.AllRowsAddFin

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.AllRowsOf

variable {D : D7} (X : HidaSetting D)

theorem eHom_fin (hHC : Formalism.L2.SG.RowsDef.RowsFinDim) (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) :
    FiniteDimensional ℂ (X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re) := by
  have hint := Formalism.L2.SG.Pf.RowDictPf.hint_of_gap X hG
  have hB := Formalism.L2.SG.Closed.RowsBij_holds X.B.I X.B.μf X.B.fund X.B.fund_spec X.B.R X.B.R_spec X.B.e X.B.Re
    X.B.Re_spec X.B.H X.B.σ X.dv X.B.w (fun v => (X.ds v).2.2.1) (fun v => (X.ds v).2.2.2.1)
    (Formalism.L2.SG.EvalTRph.isFdeg_dv X) (fun v => (X.low v).1) hint X.Rph X.Rph_spec X.B.Hs X.B.σs X.B.tens
    X.B.tens_spec
  have : FiniteDimensional ℂ (Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X) :=
    Formalism.L2.SG.Pf.RowDictPf.finiteDimensional_HHX_of_gap X hHC hG
  exact Formalism.L2.SG.RowsDef.finiteDimensional_eHom hB.1 hB.2

theorem rowsAdd_holds (hHC : Formalism.L2.SG.RowsDef.RowsFinDim) (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) : RowsAdd X :=
  Formalism.L2.SG.Pf.AllRowsAdd.rowsAdd_of X (eHom_fin X hHC hG)

end Formalism.L2.SG.Pf.AllRowsAddFin
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsDcount

section

@[expose] public section

noncomputable section

open scoped InnerProductSpace

namespace Formalism.L2.SG.Pf.AllRowsDcount

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.SG.HidaSetting Formalism.L2.SG.AllRowsOf Formalism.L2.SG.Pf.AllRowsAdd

variable {D : D7} (X : HidaSetting D)

theorem reT_rph (S : Set (Tup2 D)) : (ReT X S).comp X.Rph = X.Rph.comp (ReT X S) := by
  refine ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun x => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_inner_left,
    X.Rph_spec, X.Rph_spec]
  congr 1
  funext g
  rw [ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply,
    reT_comm]

theorem HH_eq_VT (t : Tup2 D) :
    Formalism.L2.SG.RowsDef.HH X.B.I X.B.μf X.B.fund (ReT X {t}) X.Rph = Formalism.L2.SG.Pf.RowsGoodRed.VT X t := by
  have hPE : (ReT X {t}).comp X.B.Re = ReT X {t} := by
    rw [← reT_univ' X, reT_inter, Set.inter_univ]
  have hEP : X.B.Re.comp (ReT X {t}) = ReT X {t} := by
    rw [← reT_univ' X, reT_inter, Set.univ_inter]
  have hPP : (ReT X {t}).comp (ReT X {t}) = ReT X {t} := by
    rw [reT_inter, Set.inter_self]
  have hR := reT_rph X {t}
  apply le_antisymm
  · rintro v ⟨y, rfl⟩
    refine ⟨⟨ReT X {t} y, ?_⟩, ?_⟩
    · show X.B.Re (X.Rph (ReT X {t} y)) = ReT X {t} (X.Rph y)
      have := congrArg (fun L => L y) hR
      simp only [ContinuousLinearMap.comp_apply] at this
      rw [← this]
      have := congrArg (fun L => L (X.Rph y)) hEP
      simpa only [ContinuousLinearMap.comp_apply] using this
    · show ReT X {t} (ReT X {t} (X.Rph y)) - ReT X {t} (X.Rph y) = 0
      have := congrArg (fun L => L (X.Rph y)) hPP
      simp only [ContinuousLinearMap.comp_apply] at this
      rw [this, sub_self]
  · rintro v ⟨⟨y, hy⟩, hv⟩
    have hv' : ReT X {t} v = v := by
      have : ReT X {t} v - v = 0 := hv
      exact sub_eq_zero.1 this
    refine ⟨y, ?_⟩
    show ReT X {t} (X.Rph y) = v
    have hy' : X.B.Re (X.Rph y) = v := hy
    rw [← hv', ← hy']
    have := congrArg (fun L => L (X.Rph y)) hPE
    simp only [ContinuousLinearMap.comp_apply] at this
    exact this.symm

theorem dcountEq_holds (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) : Formalism.L2.SG.Pf.RowsGoodRed.DcountEq X := by
  intro t _ _
  have hint := Formalism.L2.SG.Pf.RowDictPf.hint_of_gap X hG
  have hB := Formalism.L2.SG.Closed.RowsBij_holds X.B.I X.B.μf X.B.fund X.B.fund_spec X.B.R X.B.R_spec (eT X {t})
    (ReT X {t}) (reT_spec X (etInt_holds X) {t}) X.B.H X.B.σ X.dv X.B.w (fun v => (X.ds v).2.2.1)
    (fun v => (X.ds v).2.2.2.1) (Formalism.L2.SG.EvalTRph.isFdeg_dv X) (fun v => (X.low v).1) hint X.Rph X.Rph_spec
    X.B.Hs X.B.σs X.B.tens X.B.tens_spec
  delta dimX
  rw [← Formalism.L2.SG.RowsDef.finrank_HH_eq_Dcount hB.1 hB.2, HH_eq_VT]

end Formalism.L2.SG.Pf.AllRowsDcount
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsLab

section

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf.AllRowsLab

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.SG.HidaSetting Formalism.L2.SG.AllRowsOf

variable {D : D7} (X : HidaSetting D)

theorem rowsGood_holds (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) (G : Formalism.L2.SG.RowDict.GoodOp X)
    (ι : D.s.HH ≃ₗᵢ[ℂ] Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X) (hT : Formalism.L2.SG.RowDict.RowDictTie X G ι)
    (hL : Formalism.L2.SG.Pf.RowsGoodRed.LabTie X ι) : RowsGood X :=
  Formalism.L2.SG.Pf.RowsGoodRed.rowsGood_of X G ι hT hL (Formalism.L2.SG.Pf.AllRowsAdd.projT_holds X G)
    (Formalism.L2.SG.Pf.AllRowsDcount.dcountEq_holds X hG)

theorem rowsLab_holds (hHC : Formalism.L2.SG.RowsDef.RowsFinDim) (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D)
    (G : Formalism.L2.SG.RowDict.GoodOp X) (ι : D.s.HH ≃ₗᵢ[ℂ] Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X)
    (hT : Formalism.L2.SG.RowDict.RowDictTie X G ι) (hL : Formalism.L2.SG.Pf.RowsGoodRed.LabTie X ι)
    (hAT : AutTie D X.B X.pl) : RowsLab X :=
  rowsLab_of X (Formalism.L2.SG.Pf.AllRowsAddFin.rowsAdd_holds X hHC hG) (rowsGood_holds X hG G ι hT hL)
    (Formalism.L2.SG.Pf.AllRowsClosed.etUniv_holds X) hAT

end Formalism.L2.SG.Pf.AllRowsLab
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.AllRowsAtRecord

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.GlobalTheoryTheory.ConcN Formalism.L2.GlobalTheoryTheory.AllJoin Formalism.L2.SG.HidaSetting Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PackageTie2

noncomputable section

namespace GlobalTheory.AllRowsAtRecord

open Formalism.L2.SG.AllRowsOf

def stdChar (D : D7) (k : Fin 2) : AddChar (ZMod (D.host.g k)) ℂ :=
  haveI : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩
  ZMod.stdAddChar

theorem stdChar_ne (D : D7) (k : Fin 2) : stdChar D k ≠ 1 := by
  intro hk
  haveI : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩
  haveI : Fact (1 < D.host.g k) := ⟨(D.host.g_prime k).one_lt⟩
  change (ZMod.stdAddChar : AddChar (ZMod (D.host.g k)) ℂ) = 1 at hk
  have h1 : (ZMod.stdAddChar : AddChar (ZMod (D.host.g k)) ℂ) 1 = (ZMod.stdAddChar : AddChar (ZMod (D.host.g k)) ℂ) 0 := by
    rw [hk, AddChar.one_apply, AddChar.map_zero_eq_one]
  exact one_ne_zero (ZMod.injective_stdAddChar h1)

theorem countAllRows_of {D : D7} (A : AllRows D) {c c₃ : ℝ} (hc : 0 < c) (hcc : c ≤ c₃) (hN : 2 ≤ D.R.r)
    (hf : 1 ≤ D.R.f) (hC : Formalism.MainNotions.N.CylinderCountFamily.CountCylAt D A.toAt c₃) (hpos : 0 < DstarE A A.B.e) :
    CountAllRows A (epsC c D.R.r D.R.f) := by
  have hL : 0 < Real.log (D.R.r : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hN0 : (0 : ℝ) < D.R.r := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hN)
  have hf0 : (0 : ℝ) < D.R.f := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hf)
  have hP : 0 < (D.R.r : ℝ) * D.R.f * Real.log D.R.r := by positivity
  refine ⟨(Real.exp_pos _).le, ?_, hpos, fun k S => ?_⟩
  · unfold epsC
    have h0 : 0 < c * (D.R.r : ℝ) * D.R.f * Real.log D.R.r := by
      have := mul_pos hc hP
      linarith [this, show c * ((D.R.r : ℝ) * D.R.f * Real.log D.R.r) = c * (D.R.r : ℝ) * D.R.f * Real.log D.R.r by ring]
    have h1 := Real.exp_lt_exp.mpr (show -(c * (D.R.r : ℝ) * D.R.f * Real.log D.R.r) < 0 by linarith)
    rwa [Real.exp_zero] at h1
  · have h := hC k S
    change |((A.dimT (cyl D k S) : ℕ) : ℝ) - DstarE A (A.eT (cyl D k S))| ≤
      Real.exp (-c₃ * (A.B.I.n : ℝ) * (A.B.I.f : ℝ) * Real.log (A.B.I.n : ℝ)) * DstarE A (A.eT (cyl D k S)) at h
    rw [A.n_eq, A.f_eq] at h
    have hDs : 0 ≤ DstarE A (A.eT (cyl D k S)) :=
      (mul_nonneg_iff_of_pos_left (Real.exp_pos _)).mp (le_trans (abs_nonneg _) h)
    have hexp : Real.exp (-c₃ * (D.R.r : ℝ) * (D.R.f : ℝ) * Real.log (D.R.r : ℝ)) ≤ epsC c D.R.r D.R.f := by
      unfold epsC
      apply Real.exp_le_exp.mpr
      have e1 : -c₃ * (D.R.r : ℝ) * (D.R.f : ℝ) * Real.log (D.R.r : ℝ) = -(c₃ * ((D.R.r : ℝ) * D.R.f * Real.log D.R.r)) := by ring
      have e2 : -(c * (D.R.r : ℝ) * (D.R.f : ℝ) * Real.log (D.R.r : ℝ)) = -(c * ((D.R.r : ℝ) * D.R.f * Real.log D.R.r)) := by ring
      rw [e1, e2]
      have := mul_le_mul_of_nonneg_right hcc hP.le
      linarith
    exact le_trans h (mul_le_mul_of_nonneg_right hexp hDs)

theorem allRows_at_record : Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (G : GoodOp X)
    (ι : D.s.HH ≃ₗᵢ[ℂ] HHX X) (n₀ : ℕ) (Alev C₃ c₃ cb c : ℝ), 0 < c → c ≤ c₃ → Formalism.L2.SG.ConcreteSettingExists.GapHyp D →
    AutTie D X.B X.pl → RowDictTie X G ι → GlobalTheory.LabPin.LabTie X ι → (∀ P, CountE.CountIdempotentsClass P D n₀ Alev C₃ c₃ cb) →
    AdmissibleBoundsFromSource.CountTheoremHypotheses D large₂ n₀ Alev C₃ cb → 4 * D.R.r < D.host.g 1 →
    ∃ A : AllRows D, LabelCountGoodInjective A ∧ AllJoinA A ∧ CountAllRows A (epsC c D.R.r D.R.f) := by
  intro hRF D large₂ X G ι n₀ Alev C₃ c₃ cb c hc hcc hG hAut hT hLab hCnt hp hg1
  have hL : RowsLab X := Formalism.L2.SG.Pf.AllRowsLab.rowsLab_holds X hRF hG G ι hT hLab hAut
  have hψ : ∀ k, stdChar D k ≠ 1 := stdChar_ne D
  have hB : CountBase X n₀ Alev C₃ cb := Formalism.L2.SG.Pf.AllRowsCountBase.countBase_of X hAut hp hg1
  refine ⟨Formalism.L2.SG.Pf.AllRowsClosed.allRowsOfL X (stdChar D) hψ hL, ?_, ⟨?_, ?_⟩, ?_⟩
  · exact thirdTie_allRows (hI := etInt_holds X)
  · refine ⟨⟨X.pl, hAut⟩, fun v => Formalism.L2.SG.Pf.AllRowsCountBase.hc_X X hAut v, fun _ => ?_⟩
    change Formalism.MainNotions.S.SplitsCompl X.B.I.E X.B.g₀
    rw [X.g0_eq]
    exact Formalism.L2.SG.Pf.AllRowsCountBase.splits_X X 0
  · exact ⟨stdChar D, hψ, fun _ _ => rfl⟩
  · have hN : 2 ≤ D.R.r := le_trans (by norm_num) hG.1
    have hf : 1 ≤ D.R.f := by exact_mod_cast Formalism.MainNotions.S.one_le_f (D := D)
    have hTC := tieCountAt_allRowsOf (X := X) (ψ₀ := stdChar D) (hJ := ejIdem_holds D (stdChar D))
      (hU := etUniv_of X (redKer_of X (redKerOne_of X (Formalism.L2.SG.Pf.AllRowsRedKer.redKerP_holds X 0)
        (Formalism.L2.SG.Pf.AllRowsRedKer.redKerP_holds X 1))))
      (hO := Formalism.L2.SG.Pf.AllRowsClosed.etOne_holds X (stdChar D) hψ) (hI := etInt_holds X) (hL := hL) hB
      (fun _ _ => Formalism.L2.SG.Pf.AllRowsClosed.etAlg_holds X _)
      (fun k S => Formalism.L2.SG.Pf.AllRowsClosed.etUnip_holds X k S)
    have hC : Formalism.MainNotions.N.CylinderCountFamily.CountCylAt D (Formalism.L2.SG.Pf.AllRowsClosed.allRowsOfL X (stdChar D) hψ hL).toAt c₃ :=
      Formalism.MainNotions.N.CylinderCountFamily.countCylAt_of D _ (hCnt Formalism.MainNotions.S.CountE.PCount) hTC
        (Formalism.L2.SG.Pf.AllRowsPCount.pCountTie_holds X (stdChar D) hψ hL)
    obtain ⟨-, -, -, -, -, -, -, hpos⟩ := hB
    exact countAllRows_of _ hc hcc hN hf hC hpos

end GlobalTheory.AllRowsAtRecord
end
end
end
