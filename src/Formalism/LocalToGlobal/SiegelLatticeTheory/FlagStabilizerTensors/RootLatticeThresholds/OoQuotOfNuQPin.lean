module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SubOneMulVec
public import Formalism.RealPlaceAnalysis.Complexify
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
import Formalism.LocalRingCardinality.SpanPowerMembership.HasStrictFDerivAtExpZero
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.UnitaryIsometries
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuot
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.DetUpMatSub
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.MonoZhMulVec
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.PtParAnti
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuotStVGeo
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuotStRel
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuotStVFix
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ContinuousAdjugate

section

@[expose] public section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Matrix Topology

namespace Formalism.L2.S.L6.UnitaryStandardVectors

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.Carrier.JointQuot

section Pack

variable {n : ℕ} (ε : Fin n → Bool)

def mkUJ (y : Matrix (Fin n) (Fin n) ℂ) (hy : yᴴ * Formalism.REAL.Jm ε * y = Formalism.REAL.Jm ε) : Formalism.REAL.UJ ε :=
  ⟨⟨y, Formalism.REAL.Jm ε * yᴴ * Formalism.REAL.Jm ε,
    mul_eq_one_comm.1 (by
      calc Formalism.REAL.Jm ε * yᴴ * Formalism.REAL.Jm ε * y = Formalism.REAL.Jm ε * (yᴴ * Formalism.REAL.Jm ε * y) := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hy, Formalism.REAL.Jm_mul_self]),
    by
      calc Formalism.REAL.Jm ε * yᴴ * Formalism.REAL.Jm ε * y = Formalism.REAL.Jm ε * (yᴴ * Formalism.REAL.Jm ε * y) := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hy, Formalism.REAL.Jm_mul_self]⟩, hy⟩

end Pack

section Adj

variable {m : ℕ}

end Adj

end Formalism.L2.S.L6.UnitaryStandardVectors
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.UMatMulInv

section

@[expose] public section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Matrix Topology

namespace Formalism.L2.S.L6.UnitaryStandardVectors

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.Carrier.JointQuot

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))
  (v : InfinitePlace X.B.I.F)

theorem map_span_G (g : Formalism.REAL.UJ (X.B.I.ε v)) (Fp : Fin (D.R.rS + 1) → Fin X.B.I.n → ℂ)
    (S : Set (Fin (D.R.rS + 1))) (y : Fin X.B.I.n → ℂ)
    (hy : y ∈ Submodule.span ℂ ((fun b => uMat g *ᵥ Fp b) '' S)) :
    uMat g⁻¹ *ᵥ y ∈ Submodule.span ℂ (Fp '' S) := by
  have e : Submodule.span ℂ ((fun b => uMat g *ᵥ Fp b) '' S) =
      (Submodule.span ℂ (Fp '' S)).map (Matrix.mulVecLin (uMat g)) := by
    rw [Submodule.map_span, Set.image_image]
    rfl
  rw [e] at hy
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hy
  have h1 : uMat g⁻¹ * uMat g = 1 := by simp [uMat]
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  exact hz

section Main

variable (hw : OkPt X u u' w)

def yU (c : FreeE w → ℂ) (hw : OkPt X u u' w) : Formalism.REAL.UJ (X.B.I.ε v) :=
  mkUJ _ (Yc (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Cw w c)) (yM_unit X u u' w v hw c)

theorem T_sub (c : FreeE w → ℂ) (x : Fin X.B.I.n → ℂ) :
    (uMat ((gamW X u u' w v)⁻¹ * yU X u u' w v c hw * gamW X u u' w v) - 1) *ᵥ x =
      uMat (gamW X u u' w v)⁻¹ *ᵥ (Yc (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Cw w c) *ᵥ
        (uMat (gamW X u u' w v) *ᵥ x) - uMat (gamW X u u' w v) *ᵥ x) := by
  have hc : uMat ((gamW X u u' w v)⁻¹ * yU X u u' w v c hw * gamW X u u' w v) =
      uMat (gamW X u u' w v)⁻¹ * uMat (yU X u u' w v c hw) * uMat (gamW X u u' w v) := rfl
  have hy : uMat (yU X u u' w v c hw) = Yc (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Cw w c) := rfl
  have h1 : uMat (gamW X u u' w v)⁻¹ * uMat (gamW X u u' w v) = 1 := by simp [uMat]
  rw [hc, hy, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]

theorem G_eq (b : Fin (D.R.rS + 1)) : Gw X u u' w v b = uMat (gamW X u u' w v) *ᵥ frm X u' D.host.rdE v b := rfl

include hw in
theorem TG_comb (c : FreeE w → ℂ) (b : Fin (D.R.rS + 1)) :
    uMat (gamW X u u' w v)⁻¹ *ᵥ (Yc (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Cw w c) *ᵥ Gw X u u' w v b -
      Gw X u u' w v b) = ∑ b', (Cw w c - 1) b' b • frm X u' D.host.rdE v b' := by
  have h1 : uMat (gamW X u u' w v)⁻¹ * uMat (gamW X u u' w v) = 1 := by simp [uMat]
  have hA : ∀ x, uMat (gamW X u u' w v)⁻¹ *ᵥ (uMat (gamW X u u' w v) *ᵥ x) = x := fun x => by
    rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  rw [yM_G X u u' w v hw c b]
  simp only [G_eq, Matrix.mulVec_sub, Matrix.mulVec_sum, Matrix.mulVec_smul, hA, Matrix.sub_apply, sub_smul,
    Finset.sum_sub_distrib, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

include hw in
theorem inN_u' (c : FreeE w → ℂ) :
    InN (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))
      (uMat ((gamW X u u' w v)⁻¹ * yU X u u' w v c hw * gamW X u u' w v)) := by
  have hC := isUB_Cw w c
  refine ⟨⟨fun a => ?_, ?_⟩, fun x hx => ?_⟩
  · show (uMat ((gamW X u u' w v)⁻¹ * yU X u u' w v c hw * gamW X u u' w v) - 1) *ᵥ rv X.B.I v (X.eR a) ∈ _
    rw [T_sub, e_eq X u' v a, Matrix.mulVec_smul, Matrix.mulVec_smul, ← smul_sub, Matrix.mulVec_smul,
      ← G_eq, TG_comb X u u' w v hw c]
    exact Submodule.smul_mem _ _ (span_frm_le X u' v a.1 a.2.le (comb_mem X u' v hC a.castSucc))
  · rw [T_sub, ← frm_last X u' v, ← G_eq, TG_comb X u u' w v hw c]
    exact span_frm_le X u' v D.R.rS le_rfl (comb_mem X u' v hC (Fin.last D.R.rS))
  · rw [T_sub]
    have hperp := Yc_perpG _ _ _ (Tw u) (Tw u') (piW w) (blkW w) (gram_frm X v u _) (hGG_w X u u' w v) (piW_invol w)
      (piW_blk w) (piW_anti w) (hZ_w X u u' w hw v) (hgap_w X u u' w v hw) hC (uMat (gamW X u u' w v) *ᵥ x)
      (fun b hb => by
        obtain ⟨b0, rfl⟩ : ∃ b0 : Fin D.R.rS, b = b0.castSucc := ⟨⟨b.1, Fin.val_lt_last hb⟩, Fin.ext rfl⟩
        rw [G_eq, Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.hJ_adj (gamW X u u' w v), Matrix.mulVec_mulVec,
          Formalism.L2.SG.RealObj.InfCut.uMat_inv_mul', Matrix.one_mulVec, frm_castSucc, hJs_l, hx b0, mul_zero])
    have h2 := map_span_G X v (gamW X u u' w v) (frm X u' D.host.rdE v) _ _ hperp
    rw [lt_last_set] at h2
    exact span_frm_le X u' v D.R.rS le_rfl h2

end Main

end Formalism.L2.S.L6.UnitaryStandardVectors
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.OoQuotOfNuQPin

section

@[expose] public section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Matrix Topology

namespace Formalism.L2.S.L6.UnitaryStandardVectors

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.Carrier.JointQuot

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))
  (v : InfinitePlace X.B.I.F)

theorem hfF (w' : D.what₂.Word) (a : Fin D.R.rS) (b : Fin (D.R.rS + 1)) :
    hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (frm X w' D.host.rdE v b) =
      if b = a.castSucc then ((D.host.rdE : ℂ) ^ (D.R.rS - a.1))⁻¹ else 0 := by
  induction b using Fin.lastCases with
  | last =>
    rw [frm_last, hfz_v, if_neg (Fin.castSucc_ne_last a).symm]
  | cast b =>
    rw [frm_castSucc, hJs_r, hfe_v]
    by_cases h : b = a
    · subst h; simp
    · rw [if_neg h, if_neg (fun e => h (Fin.castSucc_injective _ e)), mul_zero]

theorem coord_eq (hw : OkPt X u u' w) (c : FreeE w → ℂ) (p : FreeE w) :
    stCoordV X u' w (gamW X u u' w) v (yU X u u' w v c hw) p = c p := by
  unfold stCoordV
  set a' : Fin D.R.rS := ⟨p.1.1.1, by have := p.2.1; omega⟩ with ha'
  have hcs : a'.castSucc = p.1.1 := Fin.ext rfl
  have hT : uMat ((gamW X u u' w v)⁻¹ * yU X u u' w v c hw * gamW X u u' w v) *ᵥ frm X u' D.host.rdE v p.1.2 =
      frm X u' D.host.rdE v p.1.2 + ∑ b', (Cw w c - 1) b' p.1.2 • frm X u' D.host.rdE v b' := by
    have h1 := T_sub X u u' w v hw c (frm X u' D.host.rdE v p.1.2)
    rw [sub_one_mulVec, ← G_eq, TG_comb X u u' w v hw c] at h1
    rw [← h1]; abel
  rw [hT, hJ_add_r', hJ_sum_r', hfF, if_neg (fun e => (ne_of_lt p.2.1) (by rw [← hcs, e]))]
  rw [Finset.sum_eq_single a'.castSucc]
  · rw [hfF, if_pos rfl, zero_add, hcs, Matrix.sub_apply, Matrix.one_apply, if_neg (ne_of_lt p.2.1), sub_zero,
      Cw_apply_free]
    have hrd : (D.host.rdE : ℂ) ^ (D.R.rS - a'.1) ≠ 0 :=
      pow_ne_zero _ (Complex.ofReal_ne_zero.2 (rdE_pos_c (D := D)).ne')
    rw [show p.1.1.1 = a'.1 from rfl]
    field_simp
  · intro b _ hb
    rw [hfF, if_neg hb, mul_zero]
  · simp

theorem continuous_yM (hw : OkPt X u u' w) :
    Continuous fun c : FreeE w → ℂ => Yc (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Cw w c) := by

  have hC : Continuous fun c : FreeE w → ℂ => Cw w c := by
    refine continuous_matrix fun i j => ?_
    simp only [Cw, Matrix.of_apply]
    split_ifs
    · exact continuous_const
    · exact continuous_apply _
    · exact continuous_const

  have hdet : ∀ c : FreeE w → ℂ, (Cw w c).det = 1 := by
    intro c
    rw [Matrix.det_of_upperTriangular]
    · simp [Cw]
    · intro i j hij
      simp only [Cw, Matrix.of_apply]
      have hji : j < i := hij
      rw [if_neg (ne_of_gt hji), dite_eq_right (fun h => absurd h.1 (lt_asymm hji))]

  have hinv : Continuous fun c : FreeE w → ℂ => (Cw w c)⁻¹ := by
    have h : (fun c : FreeE w → ℂ => (Cw w c)⁻¹) = fun c => (Cw w c).adjugate := by
      funext c
      rw [Matrix.inv_def, hdet c, Ring.inverse_one, one_smul]
    rw [h]
    exact hC.matrix_adjugate
  unfold Yc Ymat Mm Am
  exact continuous_const.add ((((continuous_const.matrix_mul (Continuous.matrix_fromBlocks
    (((continuous_const.matrix_mul hinv).matrix_mul continuous_const).matrix_conjTranspose.sub continuous_const)
    continuous_const continuous_const (hC.sub continuous_const))).matrix_mul continuous_const).matrix_mul
    continuous_const).matrix_mul continuous_const)

theorem stVSec_holds : StVSec X u u' := by
  intro w hw v
  refine ⟨fun c => yU X u u' w v c hw, ?_, fun c => ⟨inN_u X u u' w v hw c, inN_u' X u u' w v hw c⟩,
    fun c => funext fun p => coord_eq X u u' w v hw c p⟩
  have hY := continuous_yM X u u' w v hw
  unfold yU mkUJ
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨hY, ?_⟩) _
  exact (continuous_const.matrix_mul hY.matrix_conjTranspose).matrix_mul continuous_const

theorem ooQuot_of_nuQPin (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (hN : NuQPin X u u' νq) :
    ∃ νl, (∀ w, OkPt X u u' w → LocPin X u u' w νl) ∧ Formalism.L2.SG.Pf.Carrier.JointPf.OOQuot X u u' νq νl :=
  ooQuot_geo X u u' νq hN (stRel_holds X u u') (stVGeo_of_sec X u u' (stVSec_holds X u u'))

end Formalism.L2.S.L6.UnitaryStandardVectors
end
end
end
