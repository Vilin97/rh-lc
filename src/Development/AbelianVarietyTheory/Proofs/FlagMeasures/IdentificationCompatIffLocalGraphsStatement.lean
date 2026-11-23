module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IdentificationCompatPassesToLocalCongruenceStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalThetaGraphRationalIsometryMovedLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PulledLocalGraphsEqIffIdentificationsCompatibleStatement
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalIsometryExtendsLocalIsometry
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.EmbeddingIntegerAlgebraMap
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBetaIIota
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBetaIIotaA
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdNF
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
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalIsometryExtendsLocalIsometryStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnipotentGroupsLatticesGlobalCoordinatesStatement
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ActFrame
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalCompatibilityOfLocalIdentifications

section

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IotaLocConv

open Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

variable {D : D7}

theorem locH_add_right (Z : LocDat D) (p : PlF D) (x y y' : Vp D p) :
    (locH Z p).h x (y + y') = (locH Z p).h x y + (locH Z p).h x y' := by
  rw [(locH Z p).h_herm (y + y') x, (locH Z p).h_add_left, map_add (f := _), ← (locH Z p).h_herm,
    ← (locH Z p).h_herm]

theorem locH_smul_right (Z : LocDat D) (p : PlF D) (c : (D.s.atP p).Ep) (x y : Vp D p) :
    (locH Z p).h x (c • y) = (Z.M p).L.cj c * (locH Z p).h x y := by
  rw [(locH Z p).h_herm (c • y) x, (locH Z p).h_smul_left, map_mul, ← (locH Z p).h_herm]

theorem baseChange_mem_perp_sup (Z : LocDat D) (p : PlF D) {T : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T) {m : (VS D).V}
    (hm : m ∈ orth (VS D) (Xsp G)) :
    baseChange₂ D p m ∈ (locH Z p).perp ((locH Z p).X (scaled Z p (frame G))) := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hm
  show ∀ y ∈ (locH Z p).X (scaled Z p (frame G)), (locH Z p).h (baseChange₂ D p m) y = 0
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    show (locH Z p).h (baseChange₂ D p m) (frFac Z.δ p a.castSucc • baseChange₂ D p (frame G a.castSucc)) = 0
    rw [locH_smul_right, BwdNP.localForm_baseChange, GlobalTheory.LocExt.frame_castSucc,
      hm (G.fl.e a) (Submodule.subset_span ⟨a, rfl⟩), map_zero, mul_zero]
  | zero =>
    have h2 := locH_add_right Z p (baseChange₂ D p m) 0 0
    rw [add_zero] at h2
    linear_combination -h2
  | add y y' _ _ hy hy' => rw [locH_add_right, hy, hy', add_zero]
  | smul c y _ hy => rw [locH_smul_right, hy, mul_zero]

theorem theta_of_split (Z : LocDat D) (p : PlF D) (g : Formalism.MainNotions.S.Loc.SplitG (Z.M p).L)
    (hs : (Z.M p).split = some g) : Formalism.MainNotions.S.LocNG.theta (Z.M p) = (g.q : (D.s.atP p).Fp) := by
  unfold Formalism.MainNotions.S.LocNG.theta
  rw [hs]

theorem cong_of_mem (Z : LocDat D) (p : PlF D) (g : Formalism.MainNotions.S.Loc.SplitG (Z.M p).L) (hs : (Z.M p).split = some g)
    {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T)
    (F' : LFlag (D.sp.Y 0) D.R.rS T') {v : (VS D).V} (hv : v ∈ NgX Λ (gS D) F F') :
    Cong (locH Z p) (lattice₂ D Z.M p Λ) (scaled Z p (frame F)) (scaled Z p (frame F')) (baseChange₂ D p v) := by
  obtain ⟨l, hl, ξ, hξ, ξ', hξ', rfl⟩ := IotaBP.NgX_dec hv
  obtain ⟨w, hw, -, -, he, -⟩ := IotaBP.gS_typed Z p g hs
  have hξX : ξ ∈ Xsp F := (Submodule.mem_inf.1 hξ).2
  have hξ'X : ξ' ∈ Xsp F' := (Submodule.mem_inf.1 hξ').2
  refine ⟨algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) • (w • baseChange₂ D p l), ?_,
    baseChange₂ D p ξ, BwdNP.baseChange_mem_localLattice Z (Submodule.mem_inf.1 hξ).1 p, baseChange₂ D p ξ', BwdNP.baseChange_mem_localLattice Z (Submodule.mem_inf.1 hξ').1 p,
    GlobalTheory.LocExt.bcP_Xsp_mem Z p F hξX, GlobalTheory.LocExt.bcP_Xsp_mem Z p F' hξ'X, ?_⟩
  · rw [theta_of_split Z p g hs]
    exact Submodule.subset_span ⟨_, Formalism.L2.SG.Pf.LocalDenominators.smul_mem_localLattice Z p hw (BwdNP.baseChange_mem_localLattice Z hl p), rfl⟩
  · rw [map_add (f := _), map_add (f := _), baseChange_smul₂, he, mul_smul]

theorem mem_localLattice_of_cong (Z : LocDat D) (p : PlF D) (g : Formalism.MainNotions.S.Loc.SplitG (Z.M p).L)
    (hs : (Z.M p).split = some g) {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Λ.FG) {T T' : D.host.E}
    (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') {w : Vp D p}
    (hw : Cong (locH Z p) (lattice₂ D Z.M p Λ) (scaled Z p (frame F)) (scaled Z p (frame F')) w) :
    w ∈ lattice₂ D Z.M p (NgX Λ (gS D) F F') := by
  obtain ⟨a, ha, b, hb, c, hc, hbX, hcX, rfl⟩ := hw
  have hX : ∀ {T₁ : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T₁) {y : Vp D p}, y ∈ lattice₂ D Z.M p Λ →
      y ∈ (locH Z p).X (scaled Z p (frame G)) → y ∈ lattice₂ D Z.M p (XLam Λ G) := by
    intro T₁ G y hy hyX
    have hsp : y ∈ Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (Xsp G : Set (VS D).V)) := by
      refine Submodule.span_le.2 ?_ hyX
      rintro _ ⟨i, rfl⟩
      show frFac Z.δ p i.castSucc • baseChange₂ D p (frame G i.castSucc) ∈ _
      rw [GlobalTheory.LocExt.frame_castSucc]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨G.fl.e i, Submodule.subset_span ⟨i, rfl⟩, rfl⟩)
    have h := Formalism.L2.SG.Pf.locSatC_holds D Z p Λ (Xsp G) hΛ
    have h2 : y ∈ (lattice₂ D Z.M p (Λ ⊓ toO (VS D) (Xsp G)) : Set (Vp D p)) := by
      rw [h]; exact ⟨hy, hsp⟩
    exact h2
  refine add_mem (add_mem ?_ ?_) ?_
  · rw [theta_of_split Z p g hs] at ha
    unfold Formalism.MainNotions.S.Loc.HermSp.smulLat at ha
    refine (Submodule.span_le.2 ?_) ha
    rintro _ ⟨y, hy, rfl⟩
    exact IotaBP.typed_q_mem Z p g hs F F' hy
  · exact IotaBP.localLattice_mono Z p (le_sup_right.trans le_sup_left) (hX F hb hbX)
  · exact IotaBP.localLattice_mono Z p le_sup_right (hX F' hc hcX)

theorem mem_NgX_of_local (Z : LocDat D) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hΛ : Submodule.IsFullLattice D.host.E Λ) {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T)
    (F' : LFlag (D.sp.Y 0) D.R.rS T') {v : (VS D).V} (hv : v ∈ Λ)
    (h : ∀ p : PlF D, (Z.M p).split ≠ none →
      Cong (locH Z p) (lattice₂ D Z.M p Λ) (scaled Z p (frame F)) (scaled Z p (frame F')) (baseChange₂ D p v)) :
    v ∈ NgX Λ (gS D) F F' := by
  refine BwdNP.mem_of_bcP Z (IotaBP.isLattice_NgX hΛ F F') fun p => ?_
  match hs : (Z.M p).split with
  | none => exact IotaBP.untyped_mem Z p hs F F' (BwdNP.baseChange_mem_localLattice Z hv p)
  | some g => exact mem_localLattice_of_cong Z p g hs hΛ.toIsLattice.fg F F' (h p (by rw [hs]; exact Option.some_ne_none g))

theorem iotaCompat_of_local : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (t₀ t : TauC Y u u'),
    t.lam = t₀.lam → t.lam' = t₀.lam' →
    (∀ p : PlF D, (Y.M p).split ≠ none → ∀ gβ, Ext p (t.lin * t₀.lin⁻¹) gβ →
      ∀ x' ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam,
      ∀ x ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam,
      x' ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).perp ((locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X
        (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame t₀.frame))) →
      x ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).perp ((locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X
        (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u))))) →
      (Cong (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) (lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam)
          (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u))))
          (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame t₀.frame)) (x - x') ↔
        Cong (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) (lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam)
          (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u))))
          (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame t.frame)) (x - gβ x'))) →
    IotaCompat t₀.lam (lf D (X.Fu u)) t₀.frame t.frame (t.lin * t₀.lin⁻¹) (gS D) := by
  intro D X Y u u' t₀ t hl hl' hloc
  set Z : LocDat D := ⟨Y.δ, Y.M, Y.agree⟩ with hZ
  have hγ0 : t₀.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t₀.rep.2.2.1
  have hγ1 : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  have hβ : t.lin * t₀.lin⁻¹ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := mul_mem hγ1 (inv_mem hγ0)
  have hg0 : Formalism.HermitianLatticesTheory.gmap t₀.lin t₀.lam' = t₀.lam := t₀.rep.2.2.2.1
  have hg1 : Formalism.HermitianLatticesTheory.gmap t.lin t₀.lam' = t₀.lam := by
    have h : Formalism.HermitianLatticesTheory.gmap t.lin t.lam' = t.lam := t.rep.2.2.2.1
    rw [hl, hl'] at h
    exact h
  have hβΛ : ∀ y ∈ t₀.lam, (t.lin * t₀.lin⁻¹) y ∈ t₀.lam := by
    intro y hy
    rw [← hg0] at hy
    obtain ⟨y', hy', rfl⟩ := Submodule.mem_map.1 hy
    rw [← hg1]
    refine Submodule.mem_map.2 ⟨y', hy', ?_⟩
    show t.lin y' = t.lin (t₀.lin.symm (t₀.lin y'))
    rw [LinearEquiv.symm_apply_apply]
  have hLat : Submodule.IsFullLattice D.host.E t₀.lam := ((Y.rowsOK u).1 t₀.lam t₀.mem).1.1
  unfold Formalism.MainNotions.S.Lat.IotaCompat
  intro x' hx' l hlr
  have hx'Λ : x' ∈ t₀.lam := (Submodule.mem_inf.1 hx').1
  have hx'o : x' ∈ orth (VS D) (Xsp t₀.frame) := (Submodule.mem_inf.1 hx').2
  have hlΛ : l ∈ t₀.lam := (Submodule.mem_inf.1 hlr).1
  have hlo : l ∈ orth (VS D) (Xsp (lf D (X.Fu u))) := (Submodule.mem_inf.1 hlr).2
  have hβx' : (t.lin * t₀.lin⁻¹) x' ∈ t₀.lam := hβΛ x' hx'Λ
  have key : ∀ p : PlF D, (Z.M p).split ≠ none →
      (Cong (locH Z p) (lattice₂ D Z.M p t₀.lam) (scaled Z p (frame (lf D (X.Fu u)))) (scaled Z p (frame t₀.frame))
          (baseChange₂ D p (l - x')) ↔
        Cong (locH Z p) (lattice₂ D Z.M p t₀.lam) (scaled Z p (frame (lf D (X.Fu u)))) (scaled Z p (frame t.frame))
          (baseChange₂ D p (l - (t.lin * t₀.lin⁻¹) x'))) := by
    intro p hp
    obtain ⟨gβ, hext, -⟩ := GlobalTheory.LocExt.ext_isometry D Z p _ hβ
    have h := hloc p hp gβ hext (baseChange₂ D p x') (BwdNP.baseChange_mem_localLattice Z hx'Λ p) (baseChange₂ D p l) (BwdNP.baseChange_mem_localLattice Z hlΛ p)
      (baseChange_mem_perp_sup Z p _ hx'o) (baseChange_mem_perp_sup Z p _ hlo)
    rw [map_sub, map_sub, ← hext x']
    exact h
  constructor
  · intro h1
    refine mem_NgX_of_local Z hLat _ _ (sub_mem hlΛ hβx') fun p hp => ?_
    obtain ⟨g, hg⟩ := Option.ne_none_iff_exists'.1 hp
    exact (key p hp).1 (cong_of_mem Z p g hg _ _ h1)
  · intro h2
    refine mem_NgX_of_local Z hLat _ _ (sub_mem hlΛ hx'Λ) fun p hp => ?_
    obtain ⟨g, hg⟩ := Option.ne_none_iff_exists'.1 hp
    exact (key p hp).2 (cong_of_mem Z p g hg _ _ h2)

end GlobalTheory.IotaLocConv
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalCompatibilityOfLocalIdentificationsStatement

section

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rationalCompatibility_of_local_identifications : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (t₀ t : TauC Y u u'), t.lam = t₀.lam → t.lam' = t₀.lam' → (∀ p : PlF D, (Y.M p).split ≠ none → ∀ gβ, Ext p (t.lin * t₀.lin⁻¹) gβ → ∀ x' ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam, ∀ x ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam, x' ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).perp ((locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame t₀.frame))) → x ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).perp ((locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u))))) → (Cong (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) (lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam) (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u)))) (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame t₀.frame)) (x - x') ↔ Cong (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) (lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam) (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u)))) (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame t.frame)) (x - gβ x'))) → IotaCompat t₀.lam (lf D (X.Fu u)) t₀.frame t.frame (t.lin * t₀.lin⁻¹) (gS D) := by
  first | exact @GlobalTheory.IotaLocConv.iotaCompat_of_local | exact GlobalTheory.IotaLocConv.iotaCompat_of_local | (intros; apply GlobalTheory.IotaLocConv.iotaCompat_of_local <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.IdentificationCompatIffLocalGraphs

section

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IotaGraph

open Formalism.L2.SG.Pf Formalism.L2.SG.Saturated



theorem graph_eq_iff_local : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ (t : TauC Y u u') n m, t.lam = t₀.lam → t.lam' = t₀.lam' → n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → ∀ p : PlF D, ((G.datOf (c.lat (ρ * n) t.lam) p).2.2 = (G.datOf (c.lat ρ t₀.lam) p).2.2 ↔ ∀ gβ, Ext p (t.lin * t₀.lin⁻¹) gβ → ∀ x' ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam, ∀ x ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam, x' ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).perp ((locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame t₀.frame))) → x ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).perp ((locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u))))) → (Cong (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) (lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam) (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u)))) (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame t₀.frame)) (x - x') ↔ Cong (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) (lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam) (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u)))) (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame t.frame)) (x - gβ x'))) := by
  intro D X Y u u' hSt hk w F00 F'0 FP hZ hG hFP G c t₀ ρ U U' hMv t n m hl hl' hnm p
  obtain ⟨hn, hm, ht⟩ := hnm
  obtain ⟨gρ, hgρ, -⟩ := GlobalTheory.T.rational_isometry_extends_local_isometry D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p ρ hMv.1
  obtain ⟨gn, hgn, -⟩ := GlobalTheory.T.rational_isometry_extends_local_isometry D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p n hn.1
  have hgρn : Ext p (ρ * n) (gρ * gn) := by
    intro x
    show gρ (gn (baseChange₂ D p x)) = baseChange₂ D p (ρ (n x))
    rw [hgn x, hgρ (n x)]
  have hmv := (GlobalTheory.T.rational_unipotent_groups_lattices_global_coordinates D X Y u u' hSt hk w F00 F'0 FP hZ hG hFP G c t₀ ρ U U' hMv).2.2.2.2.2
  obtain ⟨A, A', -, -, -, -, hMv1⟩ := hmv t n m ⟨hn, hm, ht⟩
  have h1 := GlobalTheory.T.localThetaGraph_rationalIsometry_moved_lattice D X Y u u' hSt hk w F00 F'0 FP hZ hG hFP G c p (ρ * n) (gρ * gn) t.frame
    (U * A) (U' * A') hMv1 hgρn t₀.lam
  have h0 := GlobalTheory.T.localThetaGraph_rationalIsometry_moved_lattice D X Y u u' hSt hk w F00 F'0 FP hZ hG hFP G c p ρ gρ t₀.frame U U' hMv hgρ t₀.lam
  have hs : ∀ x, (gρ * gn).symm x = gn.symm (gρ.symm x) := fun x => rfl
  have hlat : G.datOf (c.lat (ρ * n) t.lam) p = G.datOf (c.lat (ρ * n) t₀.lam) p :=
    congrArg (fun Λ => G.datOf (c.lat (ρ * n) Λ) p) hl
  refine Iff.trans ?_ (GlobalTheory.T.pulledLocalGraphs_eq_iff_identificationsCompatible D X Y u u' t₀ t n m hl hl' ⟨hn, hm, ht⟩ p gn hgn)
  constructor
  · intro h a b
    rw [hlat] at h
    have hq := (h1 ((c.c p).e (gρ a), (c.c p).e (gρ b))).symm.trans
      ((iff_of_eq (congrArg (fun S => ((c.c p).e (gρ a), (c.c p).e (gρ b)) ∈ S) h)).trans
        (h0 ((c.c p).e (gρ a), (c.c p).e (gρ b))))
    have e1 : ∀ x, (gρ * gn).symm ((c.c p).e.symm ((c.c p).e (gρ x))) = gn.symm x := fun x => by
      rw [hs, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    have e2 : ∀ x, gρ.symm ((c.c p).e.symm ((c.c p).e (gρ x))) = x := fun x => by
      rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    dsimp only at hq
    simp only [e1, e2] at hq
    exact hq
  · intro h
    rw [hlat]
    apply Set.ext
    intro q
    have hq := h (gρ.symm ((c.c p).e.symm q.1)) (gρ.symm ((c.c p).e.symm q.2))
    refine (h1 q).trans (Iff.trans ?_ (h0 q).symm)
    rw [hs, hs]
    exact hq



theorem iotaCompat_iff_graph : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ (t : TauC Y u u') n m, t.lam = t₀.lam → t.lam' = t₀.lam' → n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → (IotaCompat t₀.lam (lf D (X.Fu u)) t₀.frame t.frame (t.lin * t₀.lin⁻¹) (gS D) ↔ ∀ p, (G.datOf (c.lat (ρ * n) t.lam) p).2.2 = (G.datOf (c.lat ρ t₀.lam) p).2.2) := by
  intro D X Y u u' hSt hk w F00 F'0 FP hZ hG hFP G c t₀ ρ U U' hMv t n m hl hl' hnm
  have hloc := graph_eq_iff_local D X Y u u' hSt hk w F00 F'0 FP hZ hG hFP G c t₀ ρ U U' hMv t n m hl hl' hnm
  have hγ0 : t₀.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t₀.rep.2.2.1
  have hγ1 : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  have hβ : t.lin * t₀.lin⁻¹ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT :=
    (Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem hγ1 ((Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem hγ0)
  have hg0 : Formalism.HermitianLatticesTheory.gmap t₀.lin t₀.lam' = t₀.lam := t₀.rep.2.2.2.1
  have hg1 : Formalism.HermitianLatticesTheory.gmap t.lin t₀.lam' = t₀.lam := by
    have h : Formalism.HermitianLatticesTheory.gmap t.lin t.lam' = t.lam := t.rep.2.2.2.1
    rw [hl, hl'] at h
    exact h
  have hβΛ : Formalism.HermitianLatticesTheory.gmap (t.lin * t₀.lin⁻¹) t₀.lam = t₀.lam := by
    rw [gmap_mul_sat, ← hg0, gmap_inv_gmap, hg1, hg0]
  constructor
  · intro hI p
    rw [hloc p]
    intro gβ hgβ x' hx' x hx hx'p hxp
    by_cases hs : (Y.M p).split = none
    · obtain ⟨g0, -, -, huniq, himg, -⟩ := GlobalTheory.T.rational_isometry_extends_local_isometry D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p _ hβ
      have hg : gβ = g0 := huniq gβ hgβ
      have hgx : gβ x' ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam := by
        have h := himg t₀.lam
        rw [hβΛ] at h
        rw [← h, hg]
        exact ⟨x', hx', rfl⟩
      have hth : LocNG.theta ((⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p) = 1 := by
        show LocNG.theta (Y.M p) = 1
        unfold LocNG.theta; rw [hs]
      have key : ∀ (f f' : Fin (D.R.rS + 1) → Vp D p) (v : Vp D p), v ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam →
          Cong (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) (lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam) f f' v := by
        intro f f' v hv
        refine ⟨v, ?_, 0, Submodule.zero_mem _, 0, Submodule.zero_mem _, Submodule.zero_mem _,
          Submodule.zero_mem _, by simp⟩
        rw [hth]
        exact Submodule.subset_span ⟨v, hv, by simp⟩
      exact ⟨fun _ => key _ _ _ (Submodule.sub_mem _ hx hgx), fun _ => key _ _ _ (Submodule.sub_mem _ hx hx')⟩
    · have hrow : IsRowLat D (X.Fu u) t₀.lam := (Y.rowsOK u).1 _ t₀.mem
      have hPD0 := t₀.rep.2.2.2.2
      have hPD1 : Formalism.L2.SG.TermDef.PD D t₀.lam (lf D (X.Fu u)) u' t.frame := by
        have h : Formalism.L2.SG.TermDef.PD D t.lam (lf D (X.Fu u)) u' t.frame := t.rep.2.2.2.2
        rw [hl] at h
        exact h
      have hfr : ∀ a, frame t.frame a = (t.lin * t₀.lin⁻¹) (frame t₀.frame a) := by
        intro a
        show frame (mapLF t.lin (lf D (X.Fu u'))) a = (t.lin * t₀.lin⁻¹) (frame (mapLF t₀.lin (lf D (X.Fu u'))) a)
        rw [Formalism.L2.SG.Pf.Act.frame_mapLF hγ1, Formalism.L2.SG.Pf.Act.frame_mapLF hγ0]
        show t.lin _ = t.lin (t₀.lin.symm (t₀.lin _))
        rw [LinearEquiv.symm_apply_apply]
      exact GlobalTheory.T.identificationCompat_passes_to_local_congruence D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) u u' (X.Fu u) t₀.lam hrow t₀.frame t.frame hPD0 hPD1 _ hβ hβΛ hfr hI p gβ hgβ hs
        x' hx' x hx hx'p hxp
  · intro h
    exact GlobalTheory.T.rationalCompatibility_of_local_identifications D X Y u u' t₀ t hl hl' (fun p _ => (hloc p).1 (h p))

end GlobalTheory.IotaGraph
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.IdentificationCompatIffLocalGraphsStatement

section

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.identificationCompat_iff_localGraphs : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ (t : TauC Y u u') n m, t.lam = t₀.lam → t.lam' = t₀.lam' → n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → (IotaCompat t₀.lam (lf D (X.Fu u)) t₀.frame t.frame (t.lin * t₀.lin⁻¹) (gS D) ↔ ∀ p, (G.datOf (c.lat (ρ * n) t.lam) p).2.2 = (G.datOf (c.lat ρ t₀.lam) p).2.2) := by
  first | exact @GlobalTheory.IotaGraph.iotaCompat_iff_graph | exact GlobalTheory.IotaGraph.iotaCompat_iff_graph | (intros; apply GlobalTheory.IotaGraph.iotaCompat_iff_graph <;> assumption)
end
end
