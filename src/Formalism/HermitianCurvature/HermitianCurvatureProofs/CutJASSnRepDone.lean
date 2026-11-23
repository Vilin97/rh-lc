module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepThConstS
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutRegFF
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRhoExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepThtFacts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJATCDatumTransit
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepThConst
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreKLExistsOf
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreKLIsoAlg
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreKLLieGrp
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGaugeLinesLeft
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepDatumUnit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DifferentialOperatorBracket
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedA
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ParametersUPrimeForULower
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.HermitianCurvature.FrameExists2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJATCModConst
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GaugeConstructionHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepTop
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJATCModConstCut
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LineScalingNorm.CrossSectionAtPoint
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LineScalingNorm.ConstantOneMemNonvanishing
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LieBracketMultiplication
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedS

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJATCLineNonzero

section

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC

noncomputable section

theorem line_nonvanishing_holds : LineNonzero := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl hk Pr hPr π ζ hζ
  have hζT : P.TT < Complex.normSq ζ := hζ
  obtain ⟨hOK, hz, hz', hTz, hTz', -, -⟩ := id hpl
  have hζ' : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ := by
    rw [hTz, hTz']; exact hζT
  have hT := Bs.T_pos
  obtain ⟨hνfix, hνν, -, -⟩ := DU.base hz hz' Bs.T_pos Bs.T'_pos Bs.sec hζ'
  set ν := SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ with hνdef

  set μ := NF.muZ P.k P.r Bs.μsec ζ with hμ
  have hm := NFRadRedA.muZ_uwb Bs.sec hζ'
  have hG := NFRadRedA.uwb_glev hm
  have hy : inWb P.k P.r (μ *ᵥ Bs.z') := Qx8.inWb_mulVec hG hz'
  have hνW : inWb P.k P.r ν := by
    show inWb P.k P.r (SSn.unitH P.k P.r (SSn.prWv P.k P.r Bs.z (μ *ᵥ Bs.z')))
    unfold SSn.unitH
    exact Qx8.inWb_smul (DU.prWv_inWb hz hy) _
  have hνz : herm (Hpk P.k P.r) ν Bs.z = 0 := by
    rw [← hνfix]; exact DU.prWv_perp hT hνW
  obtain ⟨Fr, hFr⟩ := Topx1.typ_frame_exists P.k P.r (by omega) Bs.z ν hz hT hνW hνz hνν
  obtain ⟨hFr', hpass⟩ := PRho.GL.gauge_left_line_holds Wp Wq P Bs hpl hk ζ hζT Fr hFr
  have hq : ((fun _ => (1 : ℂ)), ζ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨fun _ => one_ne_zero, hζ'⟩
  obtain ⟨-, hg, hGG⟩ := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' Bs.sec hq
  have hEx := Gauge.GC.lie_existence_of_iso_group Gauge.GC.KLIso.lie_algebra_isomorphism_holds Gauge.GC.lie_group_realization
  obtain ⟨E, hEfib, hEeig, hE0⟩ := hEx Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl hk _ hg hGG.ne' _ hFr' π
  have hEF : E ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ :=
    fun p hp => hEfib p.1 hp.1 p.2 hp.2.1 hp.2.2
  have hgl' := (Formalism.FourierDecayAlt.P.frame_general_linear Wq P.k P.r (P.k - 1) Bs.z' Bs.π'
    (fun a => μ⁻¹ *ᵥ Fr a) ⟨Bs.π'_rep, Bs.π'_cont⟩
    (Formalism.FourierDecayAlt.P.Qx8.frame_sub hFr' (by simp))).2
  have hπrep : Qr.IsRepW P.k P.r Bs.z Bs.π := ⟨Bs.π_rep, Bs.π_cont⟩
  refine ⟨E, hEF, ?_, hE0⟩
  have hpos : 0 < PRho.nrmW P.k P.r Bs.z ν := by
    unfold PRho.nrmW
    rw [hνfix, hνν]; simp
  have hrange := ((hPr.2.2 ν hpos).2.2.2 π)
  ext v
  rw [ContinuousLinearMap.comp_apply]
  refine (hrange (E v)).2 ?_
  intro Fr2 hFr2 w
  rw [hνfix] at hFr2
  rw [Topx1.typ_frame_change P.k P.r (by omega) Bs.z ν Bs.π Fr2 Fr hz hT hνW hνz hνν hπrep hFr2 hFr w (E v),
    hpass E hEF w v, hgl']
  have hw : w = (w - ((P.k : ℂ) - 2) / 2) + ((P.k : ℂ) - 2) / 2 := by ring
  conv_lhs => rw [hw]
  exact hEeig _ v

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.SsnRepOfOpen2

section

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep

theorem ssnRep_of_open2 (hPE : PRho.PRhoExists) (hMC : Core.TC.ModConst) (hLN : Core.TC.LineNonzero)
    (hPoly : Core.TC.PolyRadial ∨ Core.TC.PolyRadialS) : SSnRep :=
  ssnRep_of_open hPE theta_facts_hold hMC hLN hPoly

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LineScalingNorm.LineMove

section

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.SR

noncomputable section

theorem line_move_formula : LineMove := by
  intro Wp Wq _ _ _ _ _ _ P Bs μ' hμ' _hpl ζ _hζ h hh h' hh' he Pr hPr σ Y hY
  obtain ⟨hYF, hYP⟩ := hY
  have hhi := Formalism.FourierDecayAlt.P.LieBracketMultiplication.uw_inv hh
  have hh'i := Formalism.FourierDecayAlt.P.LieBracketMultiplication.uw_inv hh'
  refine ⟨?_, ?_⟩
  · intro p hp
    obtain ⟨hp1, hp2, hpe⟩ := hp
    have hq1 : h⁻¹ * p.1 * h ∈ UWset P.k P.r Bs.z :=
      Formalism.FourierDecayAlt.P.LieBracketMultiplication.uw_mul (Formalism.FourierDecayAlt.P.LieBracketMultiplication.uw_mul hhi hp1) hh
    have hq2 : h' * p.2 * h'⁻¹ ∈ UWset P.k P.r Bs.z' :=
      Formalism.FourierDecayAlt.P.LieBracketMultiplication.uw_mul (Formalism.FourierDecayAlt.P.LieBracketMultiplication.uw_mul hh' hp2) hh'i
    have hback : NF.muZ P.k P.r μ' ζ = h⁻¹ * NF.muZ P.k P.r Bs.μsec ζ * h'⁻¹ := by
      rw [he, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Formalism.FourierDecayAlt.P.NFRadRedS.uw_inv_mul hh, Matrix.one_mul,
        Matrix.mul_assoc, Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul_inv hh', Matrix.mul_one]
    have hq : ((h⁻¹ * p.1 * h, h' * p.2 * h'⁻¹) : Q.Mx P.k P.r × Q.Mx P.k P.r) ∈
        NF.Stab P.k P.r Bs.z Bs.z' μ' ζ := by
      refine ⟨hq1, hq2, ?_⟩
      change h⁻¹ * p.1 * h * NF.muZ P.k P.r μ' ζ * (h' * p.2 * h'⁻¹) = NF.muZ P.k P.r μ' ζ
      have e : h⁻¹ * p.1 * h * NF.muZ P.k P.r μ' ζ * (h' * p.2 * h'⁻¹) =
          h⁻¹ * (p.1 * (h * NF.muZ P.k P.r μ' ζ * h') * p.2) * h'⁻¹ := by
        simp only [Matrix.mul_assoc]
      rw [e, ← he, hpe, ← hback]
    have key : (Bs.π (h⁻¹ * p.1 * h)).comp (Y.comp (Bs.π' (h' * p.2 * h'⁻¹))) = Y := hYF _ hq
    have e1 : (Bs.π p.1).comp (Bs.π h) = (Bs.π h).comp (Bs.π (h⁻¹ * p.1 * h)) := by
      rw [← Bs.π_rep.2 _ hp1 _ hh, ← Bs.π_rep.2 _ hh _ hq1]
      congr 1
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul_inv hh, Matrix.one_mul]
    have e2 : (Bs.π' h').comp (Bs.π' p.2) = (Bs.π' (h' * p.2 * h'⁻¹)).comp (Bs.π' h') := by
      rw [← Bs.π'_rep.2 _ hh' _ hp2, ← Bs.π'_rep.2 _ hq2 _ hh']
      congr 1
      rw [Matrix.mul_assoc, Formalism.FourierDecayAlt.P.NFRadRedS.uw_inv_mul hh', Matrix.mul_one]
    change (Bs.π p.1).comp (((Bs.π h).comp (Y.comp (Bs.π' h'))).comp (Bs.π' p.2)) = (Bs.π h).comp (Y.comp (Bs.π' h'))
    calc (Bs.π p.1).comp (((Bs.π h).comp (Y.comp (Bs.π' h'))).comp (Bs.π' p.2))
        = ((Bs.π p.1).comp (Bs.π h)).comp (Y.comp ((Bs.π' h').comp (Bs.π' p.2))) := by
          simp only [ContinuousLinearMap.comp_assoc]
      _ = ((Bs.π h).comp (Bs.π (h⁻¹ * p.1 * h))).comp (Y.comp ((Bs.π' (h' * p.2 * h'⁻¹)).comp (Bs.π' h'))) := by
          rw [e1, e2]
      _ = (Bs.π h).comp (((Bs.π (h⁻¹ * p.1 * h)).comp (Y.comp (Bs.π' (h' * p.2 * h'⁻¹)))).comp (Bs.π' h')) := by
          simp only [ContinuousLinearMap.comp_assoc]
      _ = (Bs.π h).comp (Y.comp (Bs.π' h')) := by rw [key]
  · set a := SSn.nu0 P.k P.r Bs.z Bs.z' μ' ζ with ha
    have hYP' : (Pr σ a).comp Y = Y := hYP
    have hν : SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ = h *ᵥ a := by
      rw [ha]
      unfold SSn.nu0 SSn.unitH
      rw [he, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hh'.2.2,
        Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.TF.prWv_uw Bs.z_mem Bs.T_pos hh, Formalism.FourierDecayAlt.P.Qx2.herm_uh hh.1,
        Matrix.mulVec_smul]
    have e0 : (Bs.π h⁻¹).comp (Bs.π h) = 1 := by
      rw [← Bs.π_rep.2 _ hhi _ hh, Formalism.FourierDecayAlt.P.NFRadRedS.uw_inv_mul hh, Bs.π_rep.1]
    have e0' : ∀ T : Wq →L[ℂ] Wp, (Bs.π h⁻¹).comp ((Bs.π h).comp T) = T := by
      intro T
      ext v
      have k1 := DFunLike.congr_fun e0 (T v)
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at k1 ⊢
      exact k1
    change (Pr σ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp ((Bs.π h).comp (Y.comp (Bs.π' h'))) =
      (Bs.π h).comp (Y.comp (Bs.π' h'))
    rw [hν, hPr.2.1 h hh σ a]
    calc ((Bs.π h).comp ((Pr σ a).comp (Bs.π h⁻¹))).comp ((Bs.π h).comp (Y.comp (Bs.π' h')))
        = (Bs.π h).comp ((Pr σ a).comp ((Bs.π h⁻¹).comp ((Bs.π h).comp (Y.comp (Bs.π' h'))))) := by
          simp only [ContinuousLinearMap.comp_assoc]
      _ = (Bs.π h).comp (((Pr σ a).comp Y).comp (Bs.π' h')) := by
          rw [e0' (Y.comp (Bs.π' h'))]; simp only [ContinuousLinearMap.comp_assoc]
      _ = (Bs.π h).comp (Y.comp (Bs.π' h')) := by rw [hYP']

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.SR
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SRaiseSNorm

section

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC

theorem s_raise_section : SRaise := SR.sRaise_of SR.cross_section_at_point SR.line_move_formula

theorem s_norm_section : SNorm := SR.sNorm_of SR.cross_section_at_point SR.line_move_formula

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepDone

section

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC

theorem modular_constancy_holds : ModConst :=
  modConst_of_cut line_nonvanishing_holds line_at_most_one_holds datum_transitivity_holds s_raise_section s_norm_section
    Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.theta_facts_hold

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep

theorem ssnRep_of_polyS (h : Core.TC.PolyRadialS) : SSnRep :=
  ssnRep_of_open2 rho_projection_existence Core.TC.MC.modular_constancy_holds Core.TC.line_nonvanishing_holds (Or.inr h)

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep

namespace Formalism.FourierDecayAlt.P.CutMP

theorem modelPlaceBuilt2_of_polyS (hJ : JfSmoothDS) (h : JA.SSn.Rep.Core.TC.PolyRadialS) :
    Formalism.FourierDecayAlt.JCT.ModelPlaceBuilt2 :=
  modelPlaceBuilt2_of_SSnRep hJ (JA.SSn.Rep.ssnRep_of_polyS h)

end Formalism.FourierDecayAlt.P.CutMP
end
end
