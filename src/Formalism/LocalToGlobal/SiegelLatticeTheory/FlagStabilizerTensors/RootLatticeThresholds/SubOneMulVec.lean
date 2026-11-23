module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuot
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuotRel
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.YcUnitary
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.DetUpMatSub
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuotStVKer
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.PtParAnti
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
import Mathlib.Tactic.ENatToNat
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
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuotStVGeo
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ProductExactness
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuot
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.MonoZhMulVec
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.PtParAnti
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowLast
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalModelPeriodLattices
import Mathlib.Algebra.Order.Star.Real

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.PiWInvol

section

@[expose] public section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Matrix

namespace Formalism.L2.S.L6.UnitaryStandardVectors

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.Carrier.JointQuot

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))

def piW : Fin (D.R.rS + 1) → Fin (D.R.rS + 1) := fun b =>
  ⟨ptPar w.1 b.val, lt_of_lt_of_eq (ptPar_lt w.1 b.val (by rw [w.2.2]; exact b.2)) w.2.2⟩

def blkW : Fin (D.R.rS + 1) → ℕ := fun i => blkOf w.1 i.val

theorem piW_invol (a : Fin (D.R.rS + 1)) : piW w (piW w a) = a := by
  apply Fin.ext
  show ptPar w.1 (ptPar w.1 a.val) = a.val
  exact ptPar_invol w.1 a.val (by rw [w.2.2]; exact a.2)

theorem piW_blk (a : Fin (D.R.rS + 1)) : blkW w (piW w a) = blkW w a := by
  show blkOf w.1 (ptPar w.1 a.val) = blkOf w.1 a.val
  exact blkOf_ptPar w.1 a.val (by rw [w.2.2]; exact a.2)

theorem piW_anti (a b : Fin (D.R.rS + 1)) (h : blkW w a = blkW w b) (hab : a < b) : piW w b < piW w a := by
  show ptPar w.1 b.val < ptPar w.1 a.val
  exact ptPar_anti w.1 a.val b.val (by rw [w.2.2]; exact b.2) hab h

def Fw (v : InfinitePlace X.B.I.F) : Fin (D.R.rS + 1) → Fin X.B.I.n → ℂ := frm X u D.host.rdE v

def Gw (v : InfinitePlace X.B.I.F) : Fin (D.R.rS + 1) → Fin X.B.I.n → ℂ :=
  fun b => uMat (gamW X u u' w v) *ᵥ frm X u' D.host.rdE v b

theorem hGG_w (v : InfinitePlace X.B.I.F) (a b : Fin (D.R.rS + 1)) :
    hJ (X.B.I.ε v) (Gw X u u' w v a) (Gw X u u' w v b) = lastDiag (-((Tw u' : ℝ) : ℂ)) a b := by
  show hJ (X.B.I.ε v) (uMat (gamW X u u' w v) *ᵥ frm X u' D.host.rdE v a)
    (uMat (gamW X u u' w v) *ᵥ frm X u' D.host.rdE v b) = _
  rw [Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.hJ_adj, Matrix.mulVec_mulVec]
  have h1 : uMat (gamW X u u' w v)⁻¹ * uMat (gamW X u u' w v) = 1 := by
    simp [uMat]
  rw [h1, Matrix.one_mulVec]
  exact gram_frm X v u' D.host.rdE a b

theorem hZ_w (hw : OkPt X u u' w) (v : InfinitePlace X.B.I.F) (c b : Fin (D.R.rS + 1)) :
    Zm (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) c b ≠ 0 ↔ c = piW w b := by
  have hrep : IsPtRep X u u' w (gamW X u u' w) := by
    unfold gamW
    rw [dite_eq_left hw.1]
    exact hw.1.choose_spec
  have hk : ∀ a : Fin (D.R.rS + 1), (((D.host.rdE : ℝ) : ℂ) ^ (D.R.rS - a.1))⁻¹ ≠ 0 := fun a =>
    inv_ne_zero (pow_ne_zero _ (by exact_mod_cast rdE_pos_c.ne'))
  have hZ : Zm (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) c b =
      (star ((((D.host.rdE : ℝ) : ℂ) ^ (D.R.rS - c.1))⁻¹) * (((D.host.rdE : ℝ) : ℂ) ^ (D.R.rS - b.1))⁻¹) *
        ZX X u u' 1 (gamW X u u' w) v c b := by
    simp only [Zm, Matrix.of_apply, Fw, Gw, ZX, Formalism.L2.SG.RealObj.Zhat, frm, famSc, hJ, Matrix.mulVec_smul, star_smul,
      Complex.ofReal_one, one_pow, inv_one, one_smul]
    simp [dotProduct_smul, smul_dotProduct]
    ring
  have h2 := congrFun (congrFun (hrep v) c) b
  simp only [Formalism.L2.SG.RealObj.ZhatO] at h2
  have h3 : ZX X u u' 1 (gamW X u u' w) v c b ≠ 0 ↔ Formalism.L2.SG.RealObj.ptC X v w c b ≠ 0 := by
    rw [← h2]
    simp
  have hb : b.val < (w.1.map Prod.snd).sum := by rw [w.2.2]; exact b.2
  rw [hZ, mul_ne_zero_iff, h3]
  simp only [Formalism.L2.SG.RealObj.ptC, Matrix.map_apply, Formalism.MainNotions.S.ptMat]
  rw [ptEntry_eq w.1 c.val b.val hb]
  simp only [ne_eq, map_eq_zero_iff _ (X.B.I.φ v).injective, EmbeddingLike.map_eq_zero_iff, ite_eq_right_iff,
    not_forall, exists_prop]
  constructor
  · rintro ⟨_, h, _⟩
    exact Fin.ext h
  · intro h
    exact ⟨mul_ne_zero (star_ne_zero.mpr (hk c)) (hk b), congrArg Fin.val h, ptSc_ne w.1 w.2.1 b.val hb⟩

end Formalism.L2.S.L6.UnitaryStandardVectors
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ContinuousCw

section

@[expose] public section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Matrix Topology

namespace Formalism.L2.S.L6.UnitaryStandardVectors

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.Carrier.JointQuot

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def Cw (w : Point D.host.E (D.R.rS + 1)) (c : FreeE w → ℂ) : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ :=
  Matrix.of fun i j => if i = j then 1 else if h : i < j ∧ blkOf w.1 i.1 = blkOf w.1 j.1 then c ⟨(i, j), h⟩ else 0

theorem isUB_Cw (w : Point D.host.E (D.R.rS + 1)) (c : FreeE w → ℂ) : IsUB (blkW w) (Cw w c) := by
  refine ⟨fun i => by simp [Cw], fun i j hij => ?_⟩
  simp only [Cw, Matrix.of_apply] at hij
  split_ifs at hij with h1 h2
  · subst h1; exact ⟨le_rfl, rfl⟩
  · exact ⟨h2.1.le, h2.2⟩
  · exact absurd rfl hij

theorem Cw_apply_free (w : Point D.host.E (D.R.rS + 1)) (c : FreeE w → ℂ) (p : FreeE w) :
    Cw w c p.1.1 p.1.2 = c p := by
  simp only [Cw, Matrix.of_apply]
  rw [if_neg (ne_of_lt p.2.1), dite_eq_left p.2]
  rfl

theorem span_frm_le (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (w : D.what₂.Word) (v : InfinitePlace X.B.I.F) (k : ℕ)
    (hk : k ≤ D.R.rS) :
    Submodule.span ℂ (frm X w D.host.rdE v '' {a | a.1 < k}) ≤
      spanLt (fun a => rv X.B.I v (X.eR a)) k := by
  rw [Submodule.span_le]
  rintro _ ⟨a, ha, rfl⟩
  have ha' : a.1 < D.R.rS := lt_of_lt_of_le ha hk
  obtain ⟨b, rfl⟩ : ∃ b : Fin D.R.rS, a = b.castSucc := ⟨⟨a.1, ha'⟩, Fin.ext rfl⟩
  simp only [frm, famSc, fam_castSucc, SetLike.mem_coe]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, ?_, rfl⟩)
  simpa using ha

theorem frm_castSucc (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (w : D.what₂.Word) (v : InfinitePlace X.B.I.F) (b : Fin D.R.rS) :
    frm X w D.host.rdE v b.castSucc = (((D.host.rdE : ℂ) ^ (D.R.rS - b.1))⁻¹) • rv X.B.I v (X.eR b) := by
  simp only [frm, famSc, fam_castSucc, Fin.val_castSucc]

theorem frm_last (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (w : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    frm X w D.host.rdE v (Fin.last D.R.rS) = rv X.B.I v (X.zR w) := by
  simp only [frm, famSc, fam_last, Fin.val_last, Nat.sub_self, pow_zero, inv_one, one_smul]

theorem comb_mem (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (w : D.what₂.Word) (v : InfinitePlace X.B.I.F)
    {blk : Fin (D.R.rS + 1) → ℕ} {A : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ} (hA : IsUB blk A)
    (a' : Fin (D.R.rS + 1)) :
    ∑ a'', (A - 1) a'' a' • frm X w D.host.rdE v a'' ∈ Submodule.span ℂ (frm X w D.host.rdE v '' {a | a.1 < a'.1}) := by
  refine Submodule.sum_mem _ fun a'' _ => ?_
  by_cases h : (A - 1) a'' a' = 0
  · rw [h, zero_smul]; exact Submodule.zero_mem _
  · have hne : a'' ≠ a' := by intro he; subst he; apply h; simp [hA.1]
    have hA0 : A a'' a' ≠ 0 := by intro h0; apply h; simp [h0, Matrix.one_apply, hne]
    have hlt : a'' < a' := lt_of_le_of_ne (hA.2 _ _ hA0).1 hne
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a'', hlt, rfl⟩)

end Formalism.L2.S.L6.UnitaryStandardVectors
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.InvLast

section

@[expose] public section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Matrix

namespace Formalism.L2.S.L6.UnitaryStandardVectors

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.Carrier.JointQuot

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem inv_last {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) :
    Z⁻¹ (Fin.last r) (Fin.last r) = Ring.inverse (Formalism.L2.SG.RealObj.Dl Z (r + 1)) * Formalism.L2.SG.RealObj.Dl Z r := by
  have hfull : Formalism.L2.SG.RealObj.Dl Z (r + 1) = Z.det := by
    unfold Formalism.L2.SG.RealObj.Dl; rw [dite_eq_left le_rfl]
    congr 1
  have hr : Formalism.L2.SG.RealObj.Dl Z r = (Z.submatrix (Fin.last r).succAbove (Fin.last r).succAbove).det := by
    unfold Formalism.L2.SG.RealObj.Dl; rw [dite_eq_left (Nat.le_succ r)]
    congr 1; ext i j; simp only [Matrix.submatrix_apply, Fin.succAbove_last]; rfl
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Matrix.adjugate_fin_succ_eq_det_submatrix, hfull, hr]
  have : ((-1 : ℂ) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ))) = 1 := by
    rw [← two_mul, pow_mul]; simp
  rw [this, one_mul]

theorem gap_of_G {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (hZ : IsUnit Z.det) (T T' : ℝ)
    (hG : 0 < Gv T T' Z) :
    1 - (T : ℂ) * T' * (Z⁻¹ (Fin.last r) (Fin.last r) * starRingEnd ℂ (Z⁻¹ (Fin.last r) (Fin.last r))) ≠ 0 := by
  have hfull : Formalism.L2.SG.RealObj.Dl Z (r + 1) = Z.det := by
    unfold Formalism.L2.SG.RealObj.Dl; rw [dite_eq_left le_rfl]
    congr 1
  have hd : Formalism.L2.SG.RealObj.Dl Z (r + 1) ≠ 0 := by rw [hfull]; exact hZ.ne_zero
  rw [inv_last, Ring.inverse_eq_inv']
  set d := Formalism.L2.SG.RealObj.Dl Z (r + 1)
  set e := Formalism.L2.SG.RealObj.Dl Z r
  have hdd : d * starRingEnd ℂ d ≠ 0 := mul_ne_zero hd ((map_ne_zero _).2 hd)
  intro h0
  have h1 : d * starRingEnd ℂ d - (T : ℂ) * T' * (e * starRingEnd ℂ e) = 0 := by
    have e1 : d * starRingEnd ℂ d - (T : ℂ) * T' * (e * starRingEnd ℂ e) =
        (d * starRingEnd ℂ d) * (1 - (T : ℂ) * T' * (d⁻¹ * e * starRingEnd ℂ (d⁻¹ * e))) := by
      have hcd : starRingEnd ℂ d ≠ 0 := (map_ne_zero _).2 hd
      rw [map_mul, map_inv₀]; field_simp
    rw [e1, h0, mul_zero]
  have h2 : ((Complex.normSq d - T * T' * Complex.normSq e : ℝ) : ℂ) = 0 := by
    rw [← h1]; push_cast; rw [Complex.mul_conj, Complex.mul_conj]
  have h3 : Complex.normSq d - T * T' * Complex.normSq e = 0 := by exact_mod_cast h2
  unfold Gv at hG
  rw [Complex.sq_norm, Complex.sq_norm] at hG
  linarith

end Formalism.L2.S.L6.UnitaryStandardVectors
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SubOneMulVec

section

@[expose] public section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Matrix Topology

namespace Formalism.L2.S.L6.UnitaryStandardVectors

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.Carrier.JointQuot

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))
  (v : InfinitePlace X.B.I.F)

theorem gv_eq : GX X u u' D.host.rdE (gamW X u u' w) v =
    Gv (Tw u) (Tw u') (Zm (X.B.I.ε v) (Fw X u v) (Gw X u u' w v)) := rfl

theorem sub_one_mulVec (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) (x : Fin X.B.I.n → ℂ) :
    (M - 1) *ᵥ x = M *ᵥ x - x := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]

theorem frame_diff {m : ℕ} {N : ℕ} (V : Fin (m + 1) → Fin N → ℂ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (a' : Fin (m + 1)) : ∑ a'', A a'' a' • V a'' - V a' = ∑ a'', (A - 1) a'' a' • V a'' := by
  simp [Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib, Matrix.one_apply]

section Main

variable (hw : OkPt X u u' w)

include hw in
theorem hgap_w : 1 - ((Tw u : ℝ) : ℂ) * (Tw u' : ℝ) *
    ((Zm (X.B.I.ε v) (Fw X u v) (Gw X u u' w v))⁻¹ (Fin.last D.R.rS) (Fin.last D.R.rS) *
      starRingEnd ℂ ((Zm (X.B.I.ε v) (Fw X u v) (Gw X u u' w v))⁻¹ (Fin.last D.R.rS) (Fin.last D.R.rS))) ≠ 0 := by
  set Z := Zm (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) with hZd
  have hG : 0 < Gv (Tw u) (Tw u') Z := by
    rw [← gv_eq X u u' w v]
    exact hw.2 v
  have hdet : IsUnit Z.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have hD : Dl Z (D.R.rS + 1) = Z.det := by
      unfold Formalism.L2.SG.RealObj.Dl
      rw [dite_eq_left le_rfl]
      congr 1
    have hnn : (0 : ℝ) ≤ (Tw u : ℝ) * (Tw u' : ℝ) * ‖Dl Z D.R.rS‖ ^ 2 :=
      mul_nonneg (mul_nonneg (Formalism.L2.SG.RealObj.InfCut.ProductExactness.Tw_pos (D := D) u).le
        (Formalism.L2.SG.RealObj.InfCut.ProductExactness.Tw_pos (D := D) u').le) (sq_nonneg _)
    unfold Gv at hG
    rw [hD, h0, norm_zero, zero_pow two_ne_zero, zero_sub] at hG
    linarith
  exact gap_of_G Z hdet _ _ hG

include hw in
theorem yM_unit (c : FreeE w → ℂ) :
    (Yc (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Cw w c))ᴴ * Formalism.REAL.Jm (X.B.I.ε v) *
      Yc (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Cw w c) = Formalism.REAL.Jm (X.B.I.ε v) :=
  by
  have hC : IsUB (blkW w) (Cw w c) := by
      refine ⟨fun i => by simp [Cw], fun i j h => ?_⟩
      simp only [Cw, Matrix.of_apply] at h
      split_ifs at h with h1 h2
      · exact ⟨le_of_eq h1, by rw [h1]⟩
      · exact ⟨le_of_lt h2.1, h2.2⟩
      · exact absurd rfl h
  exact Yc_unitary (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Tw u : ℝ) (Tw u' : ℝ) (piW w) (blkW w) (fun a b => gram_frm (X := X) v u D.host.rdE a b)
    (fun a b => hGG_w (X := X) (u := u) (u' := u') (w := w) v a b)
    (fun a => piW_invol (w := w) a)
    (fun a => piW_blk (w := w) a) (fun a b h hab => piW_anti (w := w) a b h hab)
    (fun c b => hZ_w (X := X) (u := u) (u' := u') (w := w) hw v c b) (hgap_w X u u' w v hw) hC

include hw in
theorem yM_F (c : FreeE w → ℂ) (a : Fin (D.R.rS + 1)) :
    Yc (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Cw w c) *ᵥ Fw X u v a =
      ∑ a', Am (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Cw w c) a' a • Fw X u v a' :=
  Yc_F (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Tw u : ℝ) (Tw u' : ℝ) (piW w) (fun a b => gram_frm (X := X) v u D.host.rdE a b)
    (fun a b => hGG_w (X := X) (u := u) (u' := u') (w := w) v a b)
    (fun a => piW_invol (w := w) a)
    (fun c b => hZ_w (X := X) (u := u) (u' := u') (w := w) hw v c b) (hgap_w X u u' w v hw) a

include hw in
theorem yM_G (c : FreeE w → ℂ) (b : Fin (D.R.rS + 1)) :
    Yc (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Cw w c) *ᵥ Gw X u u' w v b =
      ∑ b', Cw w c b' b • Gw X u u' w v b' :=
  Yc_G (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Tw u : ℝ) (Tw u' : ℝ) (piW w) (fun a b => gram_frm (X := X) v u D.host.rdE a b)
    (fun a b => hGG_w (X := X) (u := u) (u' := u') (w := w) v a b)
    (fun a => piW_invol (w := w) a)
    (fun c b => hZ_w (X := X) (u := u) (u' := u') (w := w) hw v c b) (hgap_w X u u' w v hw) b

include hw in
theorem yM_isUB_A (c : FreeE w → ℂ) : IsUB (blkW w) (Am (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Cw w c)) := by
  unfold Am
  exact isUB_A (piW w) (fun a => piW_invol (w := w) a) (fun a => piW_blk (w := w) a)
    (fun a b h hab => piW_anti (w := w) a b h hab) (Zm (X.B.I.ε v) (Fw X u v) (Gw X u u' w v))
    (fun c b => hZ_w (X := X) (u := u) (u' := u') (w := w) hw v c b) (isUB_Cw w c)

theorem lt_last_set : {a : Fin (D.R.rS + 1) | a ≠ Fin.last D.R.rS} = {a | a.1 < D.R.rS} := by
  ext a
  simp only [Set.mem_setOf_eq]
  rw [← Fin.lt_last_iff_ne_last]
  exact Iff.rfl

theorem e_eq (b : Fin D.R.rS) : rv X.B.I v (X.eR b) =
    ((D.host.rdE : ℂ) ^ (D.R.rS - b.1)) • frm X u D.host.rdE v b.castSucc := by
  have hr : (D.host.rdE : ℂ) ≠ 0 := by exact_mod_cast (Formalism.MainNotions.LocalModelPeriodLattices.rdE_pos D).ne'
  simp only [frm, famSc, fam, Fin.coe_castSucc, Fin.snoc_castSucc, smul_smul]
  rw [mul_inv_cancel₀ (pow_ne_zero _ hr), one_smul]

include hw in
theorem inN_u (c : FreeE w → ℂ) :
    InN (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))
      (Yc (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Cw w c)) := by
  have hr : (D.host.rdE : ℂ) ≠ 0 := by exact_mod_cast (Formalism.MainNotions.LocalModelPeriodLattices.rdE_pos D).ne'
  have hF : ∀ b : Fin D.R.rS, Fw X u v b.castSucc =
      ((D.host.rdE : ℂ) ^ (D.R.rS - b.1))⁻¹ • rv X.B.I v (X.eR b) := by
    intro b
    show frm X u D.host.rdE v b.castSucc = _
    rw [e_eq X u v b, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hr), one_smul]
  have hspan : ∀ k, k ≤ D.R.rS → Submodule.span ℂ (Fw X u v '' {a | a.1 < k}) ≤
      spanLt (fun a => rv X.B.I v (X.eR a)) k := by
    intro k hk
    rw [Submodule.span_le]
    rintro _ ⟨a, ha, rfl⟩
    have ha' : a.1 < k := ha
    obtain ⟨b, rfl⟩ : ∃ b : Fin D.R.rS, a = b.castSucc := ⟨⟨a.1, by omega⟩, Fin.ext rfl⟩
    rw [hF b]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, ha', rfl⟩)
  have hA := yM_isUB_A X u u' w v hw c
  have hcol : ∀ a' : Fin (D.R.rS + 1),
      Yc (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Cw w c) *ᵥ Fw X u v a' - Fw X u v a' ∈
        spanLt (fun a => rv X.B.I v (X.eR a)) a'.1 := by
    intro a'
    rw [yM_F X u u' w v hw c a', frame_diff]
    exact hspan a'.1 (Nat.lt_succ_iff.mp a'.2) (comb_mem X u v hA a')
  refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩
  · show (Yc (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Cw w c) - 1) *ᵥ rv X.B.I v (X.eR a) ∈ _
    have he : rv X.B.I v (X.eR a) = ((D.host.rdE : ℂ) ^ (D.R.rS - a.1)) • Fw X u v a.castSucc := by
      rw [hF a, smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hr), one_smul]
    rw [sub_one_mulVec X, he, Matrix.mulVec_smul, ← smul_sub]
    exact Submodule.smul_mem _ _ (hcol a.castSucc)
  · have hz : Fw X u v (Fin.last D.R.rS) = rv X.B.I v (X.zR u) := by
      simp [Fw, frm, famSc, fam]
    rw [sub_one_mulVec X, ← hz]
    exact hcol (Fin.last D.R.rS)
  · have hx : ∀ a, a ≠ Fin.last D.R.rS → hJ (X.B.I.ε v) (Fw X u v a) y = 0 := by
      intro a ha
      obtain ⟨b, rfl⟩ : ∃ b : Fin D.R.rS, a = b.castSucc :=
        ⟨⟨a.1, Fin.val_lt_last ha⟩, Fin.ext rfl⟩
      rw [hF b, hJs_l, hy b, mul_zero]
    have hp := Yc_perpF (ε := X.B.I.ε v) (F := Fw X u v) (G := Gw X u u' w v) (T := (Tw u : ℝ))
      (T' := (Tw u' : ℝ)) (π := piW w) (blk := blkW w)
      (hFF := fun a b => gram_frm (X := X) v u D.host.rdE a b)
      (hGG := fun a b => hGG_w (X := X) (u := u) (u' := u') (w := w) v a b)
      (hπ := fun a => piW_invol (w := w) a) (hblk := fun a => piW_blk (w := w) a)
      (hanti := fun a b h hab => piW_anti (w := w) a b h hab)
      (hZ := fun c b => hZ_w (X := X) (u := u) (u' := u') (w := w) hw v c b)
      (hgap := hgap_w X u u' w v hw) (hC := isUB_Cw w c) y hx
    rw [lt_last_set] at hp
    rw [sub_one_mulVec X]
    exact hspan D.R.rS le_rfl hp

end Main

end Formalism.L2.S.L6.UnitaryStandardVectors
end
end
end
