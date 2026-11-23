module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDatumOfTwoCongruentFramesStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramInvariantIsometryUnitriangularMovesStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeDatumEquivariantFlagIsometries
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitriangularFrameChangeLocalScalings
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalTermDefectNeIffMoveLinearEquivStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsTermLocalTermMoveOfIsometry
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermOp
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalIsometryExtendsLocalIsometryStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnipotentGroupsLatticesGlobalCoordinatesStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsGenericTermIffNoLocalDefectBaseFrames
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsOrbitsHeightsAmplitudesInCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnsignedLocalTermRowLatticeIsTerm
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalFramesMovedTermUnitriangularChange

section

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LocOver

theorem isUpperUnitriangularFinMatrix_mul_of_both {K : Type} [CommRing K] {n : ℕ} (A B : Matrix (Fin n) (Fin n) K) (hA : Uni A) (hB : Uni B) :
    Uni (A * B) := by
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases lt_or_ge c a with h | h
    · rw [hA.1 a c h, zero_mul]
    · rw [hB.1 c b (lt_of_lt_of_le hab h), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [hA.2 a, hB.2 a, mul_one]
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with h | h
      · rw [hA.1 a c h, zero_mul]
      · rw [hB.1 c a h, mul_zero]
    · intro h; exact absurd (Finset.mem_univ a) h

theorem triMove_main : ∀ {D : D7} (Z : LocDat D) (p : PlF D) {T T' : D.host.E} (F0 : LFlag (D.sp.Y 0) D.R.rS T) (F0' : LFlag (D.sp.Y 0) D.R.rS T') (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (U U' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) (g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (f' : Fin (D.R.rS + 1) → Vp D p), MovesTo F0 F0' F F' ρ U U' → Ext p ρ g → Tri (D.s.atP p).Ep (scaled Z p (frame F')) f' → Tri (D.s.atP p).Ep (scaled Z p (frame F0)) (fun a => g (scaled Z p (frame F) a)) ∧ Tri (D.s.atP p).Ep (scaled Z p (frame F0')) (fun b => g (f' b)) := by
  intro D Z p T T' F0 F0' F F' ρ U U' g f' hM hE hf'
  obtain ⟨_, hU, hU', hρ, hρ'⟩ := hM
  have hs : ∀ (h : Fin (D.R.rS + 1) → (VS D).V) a, g (scaled Z p h a) = scaled Z p (fun b => ρ (h b)) a := by
    intro h a
    simp only [scaled, map_smul]
    rw [hE]
  have uniOf : ∀ W : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, IsUpUni W → Uni W :=
    fun W hW => ⟨fun a b hab => (hW a b).1 hab, fun a => (hW a a).2 rfl⟩
  obtain ⟨A1, hA1, -⟩ := tri_scaled D Z (frame F0) (fun b => ρ (frame F b)) U (uniOf U hU) (fun b => hρ b)
  obtain ⟨A2, hA2, -⟩ := tri_scaled D Z (frame F0') (fun b => ρ (frame F' b)) U' (uniOf U' hU') (fun b => hρ' b)
  refine ⟨⟨A1 p, (hA1 p).1, fun b => ?_⟩, ?_⟩
  · show g (scaled Z p (frame F) b) = _
    rw [hs]; exact (hA1 p).2 b
  · obtain ⟨A, hA, hc⟩ := hf'
    refine ⟨A2 p * A, isUpperUnitriangularFinMatrix_mul_of_both _ _ (hA2 p).1 hA, fun b => ?_⟩
    show g (f' b) = _

    rw [hc b, map_sum]
    have h2 : ∀ a, g (A a b • scaled Z p (frame F') a) =
        ∑ d, (A a b * A2 p d a) • scaled Z p (frame F0') d := by
      intro a
      rw [map_smul, hs, (hA2 p).2 a, Finset.smul_sum]
      exact Finset.sum_congr rfl fun d _ => smul_smul _ _ _
    rw [Finset.sum_congr rfl fun a _ => h2 a, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Matrix.mul_apply, Finset.sum_smul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_comm]

end GlobalTheory.LocOver
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalFramesMovedTermUnitriangularChangeStatement

section

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.localFrames_movedTerm_unitriangular_change : ∀ {D : D7} (Z : LocDat D) (p : PlF D) {T T' : D.host.E} (F0 : LFlag (D.sp.Y 0) D.R.rS T) (F0' : LFlag (D.sp.Y 0) D.R.rS T') (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (U U' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) (g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (f' : Fin (D.R.rS + 1) → Vp D p), MovesTo F0 F0' F F' ρ U U' → Ext p ρ g → Tri (D.s.atP p).Ep (scaled Z p (frame F')) f' → Tri (D.s.atP p).Ep (scaled Z p (frame F0)) (fun a => g (scaled Z p (frame F) a)) ∧ Tri (D.s.atP p).Ep (scaled Z p (frame F0')) (fun b => g (f' b)) := by
  first | exact @GlobalTheory.LocOver.triMove_main | exact GlobalTheory.LocOver.triMove_main | (intros; apply GlobalTheory.LocOver.triMove_main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalTermMoveUnitaryIsTerm

section

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.LocOver.isTerm_move_unitary : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Formalism.MainNotions.S.Loc.HermSp M V) {r : ℕ} (g : V ≃ₗ[E] V) (hg : LocNG.IsUnitary H g) (t : Formalism.MainNotions.S.Loc.Term V M r), H.IsTerm t → H.IsTerm (move g t) :=
  fun H _ g hg t ht => GlobalTheory.LocOver.isTerm_move_of_unitary H g t hg ht
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalTermMoveUnitaryIsTermStatement

section

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.localTerm_move_unitary_isTerm : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Formalism.MainNotions.S.Loc.HermSp M V) {r : ℕ} (g : V ≃ₗ[E] V) (hg : LocNG.IsUnitary H g) (t : Formalism.MainNotions.S.Loc.Term V M r), H.IsTerm t → H.IsTerm (move g t) := by
  first | exact @GlobalTheory.LocOver.isTerm_move_unitary | exact GlobalTheory.LocOver.isTerm_move_unitary | (intros; apply GlobalTheory.LocOver.isTerm_move_unitary <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.SignedLocalTermDefectIffUnsignedLocalTerm

section

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SignDefect

theorem locBBne_iff_locU : ∀ {D : D7} (Z : LocDat D) (p : PlF D) (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') (Tn T'n : ℕ), locBBne Z p Λ F F' Tn T'n ↔ LocNG.BBne (H := locH Z p) (locU Z p Λ F F' Tn T'n) := by
  intro D Z p Λ T T' F F' Tn T'n
  exact (GlobalTheory.Unfold.GenLoc.locBBne_iff Z p Λ F F' Tn T'n).symm

end GlobalTheory.SignDefect
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.SignedLocalTermDefectIffUnsignedLocalTermStatement

section

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.signedLocalTerm_defect_iff_unsignedLocalTerm : ∀ {D : D7} (Z : LocDat D) (p : PlF D) (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') (Tn T'n : ℕ), locBBne Z p Λ F F' Tn T'n ↔ LocNG.BBne (H := locH Z p) (locU Z p Λ F F' Tn T'n) := by
  first | exact @GlobalTheory.SignDefect.locBBne_iff_locU | exact GlobalTheory.SignDefect.locBBne_iff_locU | (intros; apply GlobalTheory.SignDefect.locBBne_iff_locU <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericIffZeroDefectGroupCoordinates

section

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL.GenCoord

theorem generic_iff_locU {D : D7} (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (Z : LocDat D)
    (t₀ : TauC Y u u') : t₀.generic ↔
      ∀ p, ¬ LocNG.BBne (H := locH Z p) (locU Z p t₀.lam (lf D (X.Fu u)) t₀.frame (Tu D u) (Tu D u')) := by
  have hrows := Y.rowsOK u
  have hBF := Formalism.L2.SG.Pf.big_block_function_holds D u u'
  have hT := Formalism.L2.SG.Pf.bbTie_holds D Z
  have hMI : ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
      (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)), Formalism.L2.SG.Saturated.MplusIndep Λ (lf D F0) (gS D) F' :=
    fun F0 Λ F' => Formalism.L2.SG.Pf.m_plus_independent _ _ _ _
  have hg := genIffLocBB_of Z hT u u' hBF hMI (X.Fu u) (Y.what₂ u) hrows t₀.toTerm
  show t₀.toTerm.generic ↔ _
  rw [hg]
  refine forall_congr' fun p => not_congr ?_
  have hL := hrows.1 t₀.lam t₀.mem
  refine ((termBBne_iff_loc Z hT hrows hBF (hMI (X.Fu u)) t₀.toTerm p).symm.trans ?_).trans
    (GlobalTheory.T.signedLocalTerm_defect_iff_unsignedLocalTerm Z p t₀.lam (lf D (X.Fu u)) t₀.frame (Tu D u) (Tu D u'))
  refine Iff.trans ?_ (hT u u' (X.Fu u) t₀.lam t₀.frame hL t₀.rep.2.2.2.2 (hMI _ _ _) p)
  constructor
  · rintro ⟨F', ⟨h, hm⟩, P, hP, hbb⟩
    refine ⟨P, hP, ?_⟩
    have e := Formalism.L2.SG.TermDef.const_of_mk
      (fun y : Formalism.L2.SG.TermDef.Carrier (Formalism.L2.SG.TermDef.PD D t₀.lam (lf D (X.Fu u)) u') =>
        Formalism.L2.SG.Saturated.BBneP t₀.lam (gS D) (lf D (X.Fu u)) y.1 P)
      (fun a b hab => propext (hBF (X.Fu u) t₀.lam hL P a b hab)) hm
    exact e ▸ hbb
  · intro h
    exact ⟨t₀.frame, ⟨t₀.rep.2.2.2.2, rfl⟩, h⟩

theorem generic_iff_gen : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → (t₀.generic ↔ G.Gen (G.datOf (c.lat ρ t₀.lam)) (c.lat ρ t₀.lam)) := by
  intro D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv
  have hρ : ρ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hMv.1
  rw [generic_iff_locU X Y u u' (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) t₀]
  refine forall_congr' fun p => ?_
  obtain ⟨g, hgExt, hgU, -, -, -⟩ := GlobalTheory.T.rational_isometry_extends_local_isometry D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p ρ hρ
  have hGv : Gval (lf D (X.Fu u)) t₀.frame ≠ 0 := fun h => hG ((GlobalTheory.T.gramInvariant_isometry_unitriangular_moves F00 F'0 _ _ ρ U U' hMv).symm.trans h)
  have hRL : IsRowLat D (X.Fu u) t₀.lam := (Y.rowsOK u).1 t₀.lam t₀.mem
  obtain ⟨hIT, hTri'⟩ := GlobalTheory.LocOver.locU_isTerm D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) u u' (X.Fu u) t₀.lam hRL
    t₀.frame t₀.rep.2.2.2.2 hGv p
  have hOK : (Y.M p).OK := (Y.agree p).1
  have htIT := GlobalTheory.T.localTerm_move_unitary_isTerm (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) g hgU _ hIT
  obtain ⟨hTA, hTB⟩ := GlobalTheory.T.localFrames_movedTerm_unitriangular_change (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 _ _ ρ U U' g _ hMv hgExt hTri'
  obtain ⟨hA1, hA2, hA3, hA4⟩ := (hAt p).1
  rw [← hA1] at hTA
  rw [← hA2] at hTB
  obtain ⟨d, hd⟩ := GlobalTheory.T.exists_datum_of_two_congruent_frames (Y.M p) hOK (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS (FP p)
    (move g (locU (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p t₀.lam (lf D (X.Fu u)) t₀.frame (Tu D u) (Tu D u')))
    htIT hA3.symm hA4.symm hTA hTB
  have hW := ((GlobalTheory.T.terms_orbits_heights_amplitudes_in_coordinates (Y.M p) hOK (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS D.R.k (FP p) (G.S p)
    (c.c p)).1 d _ hd)
  have hlat := (GlobalTheory.T.rational_unipotent_groups_lattices_global_coordinates D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv).2.2.2.2.1 ρ hρ p g t₀.lam hgExt
  haveI := ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).lf
  haveI := ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).char0
  have hlat' : (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat p (c.lat ρ t₀.lam) = (c.c p).lat
      (move g (locU (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p t₀.lam (lf D (X.Fu u)) t₀.frame (Tu D u) (Tu D u'))).abelian₂ := hlat
  have hdat := GlobalTheory.HL.DatumOf.datOf_term (G.S p) hW.1
  show _ ↔ (G.S p).BBzero ((G.S p).datOf ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat p (c.lat ρ t₀.lam)))
    ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat p (c.lat ρ t₀.lam))
  rw [hlat', ← hdat, ← GlobalTheory.T.localTermDefect_ne_iff_move_linearEquiv (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) g, hW.2.2]
  exact not_not

end GlobalTheory.HL.GenCoord
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericIffZeroDefectGroupCoordinatesStatement

section

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.generic_iff_zero_defectGroup_coordinates : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → (t₀.generic ↔ G.Gen (G.datOf (c.lat ρ t₀.lam)) (c.lat ρ t₀.lam)) := by
  first | exact @GlobalTheory.HL.GenCoord.generic_iff_gen | exact GlobalTheory.HL.GenCoord.generic_iff_gen | (intros; apply GlobalTheory.HL.GenCoord.generic_iff_gen <;> assumption)
end
end
