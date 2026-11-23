module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AnisotropicFrameVectorPrimitiveInInnerLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAddIsotropicSpanMemLocallyStandardLatticeStatement
public import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEnds
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermOp
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedConvOfIntegralFlagLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsUnimodularOfLocalStandardLatticeTranslates
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicPartEqSpanScaledFrameUnitriangularStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticePropertiesTransportByIsometryStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WittExistsHolds
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFlagOfUnitriangularIsotropicShift

section

@[expose] public section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MkFlag

variable {Ef : Type} [Field Ef] [NumberField Ef] [StarRing Ef] {H : HSpace Ef} {r : ℕ} {T : Ef}

theorem Xa_le_X (F : FlagG H r T) (a : ℕ) : F.Xa a ≤ F.X :=
  Submodule.span_mono (Set.image_subset_range _ _)

theorem orth_of_mem_X (F : FlagG H r T) {w : H.V} (hw : ∀ a, H.hT (F.e a) w = 0)
    {u : H.V} (hu : u ∈ F.X) : H.hT u w = 0 := by
  unfold FlagG.X at hu
  induction hu using Submodule.span_induction with
  | mem v hv => obtain ⟨a, rfl⟩ := hv; exact hw a
  | zero => simp
  | add u v _ _ hu hv => simp [hu, hv]
  | smul c u _ hu => simp [hu]

theorem iso_X (F : FlagG H r T) {x y : H.V} (hx : x ∈ F.X) (hy : y ∈ F.X) : H.hT x y = 0 := by
  refine orth_of_mem_X F (fun a => ?_) hx
  have hle : F.X ≤ LinearMap.ker (H.hT (F.e a)) := by
    rw [FlagG.X, Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    exact F.e_iso a b
  exact hle hy

theorem span_eq (F : FlagG H r T) (e' : Fin r → H.V) (h : ∀ a, e' a - F.e a ∈ F.Xa a.val) :
    Submodule.span Ef (Set.range e') = F.X := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    have hsplit : e' a = (e' a - F.e a) + F.e a := by abel
    rw [hsplit]
    exact Submodule.add_mem _ (Xa_le_X F a.val (h a)) (Submodule.subset_span ⟨a, rfl⟩)
  · have key : ∀ n : ℕ, ∀ a : Fin r, a.val < n → F.e a ∈ Submodule.span Ef (Set.range e') := by
      intro n
      induction n with
      | zero => intro a ha; exact absurd ha (Nat.not_lt_zero _)
      | succ n ih =>
        intro a ha
        have hXa : F.Xa a.val ≤ Submodule.span Ef (Set.range e') := by
          rw [FlagG.Xa, Submodule.span_le]
          rintro _ ⟨b, hb, rfl⟩
          have hb' : b.val < a.val := hb
          exact ih b (by omega)
        have hsplit : F.e a = e' a - (e' a - F.e a) := by abel
        rw [hsplit]
        exact Submodule.sub_mem _ (Submodule.subset_span ⟨a, rfl⟩) (hXa (h a))
    rw [FlagG.X, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact key (a.val + 1) a (Nat.lt_succ_self _)

theorem indep (F : FlagG H r T) (e' : Fin r → H.V) (h : ∀ a, e' a - F.e a ∈ F.Xa a.val) :
    LinearIndependent Ef e' := by
  rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, span_eq F e' h, FlagG.X,
    finrank_span_eq_card F.e_indep]

theorem herm_zero {u v : H.V} (h : H.hT u v = 0) : H.hT v u = 0 := by
  have h2 := H.herm.eq u v
  rw [← h2, h, map_zero]

def change (F : FlagG H r T) (e' : Fin r → H.V) (x : H.V) (h : ∀ a, e' a - F.e a ∈ F.Xa a.val)
    (hx : x ∈ F.X) : FlagG H r T where
  e := e'
  z := F.z + x
  e_indep := indep F e' h
  e_iso a b := by
    have hX : ∀ c, e' c ∈ F.X := fun c => span_eq F e' h ▸ Submodule.subset_span ⟨c, rfl⟩
    exact iso_X F (hX a) (hX b)
  z_orth a := by
    have hX : e' a ∈ F.X := span_eq F e' h ▸ Submodule.subset_span ⟨a, rfl⟩
    have h1 : H.hT (e' a) F.z = 0 := orth_of_mem_X F F.z_orth hX
    rw [map_add (f := _), h1, iso_X F hX hx, add_zero]
  z_norm := by
    have h1 : H.hT x F.z = 0 := orth_of_mem_X F F.z_orth hx
    have h2 : H.hT F.z x = 0 := herm_zero h1
    simp only [map_add (f := _), LinearMap.add_apply, h1, h2, iso_X F hx hx, F.z_norm]
    ring

theorem change_X (F : FlagG H r T) (e' : Fin r → H.V) (x : H.V) (h : ∀ a, e' a - F.e a ∈ F.Xa a.val)
    (hx : x ∈ F.X) : (change F e' x h hx).X = F.X :=
  span_eq F e' h

theorem mkflag : ∀ (D : D7) (T : D.host.E) (G : FlagG (VS D) D.R.rS T) (e' : Fin D.R.rS → (VS D).V) (x : (VS D).V), (∀ a, e' a - G.e a ∈ G.Xa a.val) → x ∈ G.X → ∃ G' : FlagG (VS D) D.R.rS T, G'.e = e' ∧ G'.z = G.z + x ∧ G'.X = G.X := by
  intro D T G e' x h hx
  exact ⟨change G e' x h hx, rfl, rfl, change_X G e' x h hx⟩

end GlobalTheory.MkFlag
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFlagOfUnitriangularIsotropicShiftStatement

section

@[expose] public section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_flag_of_unitriangular_isotropic_shift : ∀ (D : D7) (T : D.host.E) (G : FlagG (VS D) D.R.rS T) (e' : Fin D.R.rS → (VS D).V) (x : (VS D).V), (∀ a, e' a - G.e a ∈ G.Xa a.val) → x ∈ G.X → ∃ G' : FlagG (VS D) D.R.rS T, G'.e = e' ∧ G'.z = G.z + x ∧ G'.X = G.X := by
  first | exact @GlobalTheory.MkFlag.mkflag | exact GlobalTheory.MkFlag.mkflag | (intros; apply GlobalTheory.MkFlag.mkflag <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsUnimodularOfLocalStandardLatticeTranslatesStatement

section

@[expose] public section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isUnimodular_of_local_standardLattice_translates : ∀ (D : D7) (Z : LocDat D) (A : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS) (Λ : LV D), Submodule.IsLattice D.host.E Λ → (∀ p, ∃ n ∈ (A p).N, ∃ L, (A p).IsInner L ∧ lattice₂ D Z.M p Λ = LocNG.img n ((A p).LamStd L)) → Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ := by
  first | exact @GlobalTheory.Unfold.StdDual.unimodular_of_local | exact GlobalTheory.Unfold.StdDual.unimodular_of_local | (intros; apply GlobalTheory.Unfold.StdDual.unimodular_of_local <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticeOfLocallyStandardFrame

section

@[expose] public section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowLatAdapt

theorem witt_flag (D : D7) (T : D.host.E) (hT : T ≠ 0) (F F' : FlagG (VS D) D.R.rS T) :
    ∃ g : GV D, g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ ∀ a, g (F.fvec a) = F'.fvec a := by
  have hind : ∀ G : FlagG (VS D) D.R.rS T, LinearIndependent D.host.E G.fvec := by
    intro G
    unfold FlagG.fvec
    rw [linearIndependent_finSnoc]
    refine ⟨G.e_indep, fun hz => hT ?_⟩
    have h0 : ∀ x ∈ Submodule.span D.host.E (Set.range G.e), (VS D).hT x G.z = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem y hy => obtain ⟨a, rfl⟩ := hy; exact G.z_orth a
      | zero => simp
      | add x y _ _ hx hy => simp [hx, hy]
      | smul c x _ hx => simp [hx]
    have := h0 _ hz
    rw [G.z_norm] at this
    exact neg_eq_zero.1 this
  have hgram : ∀ G : FlagG (VS D) D.R.rS T, ∀ i j, (VS D).hT (G.fvec i) (G.fvec j) =
      if i = Fin.last _ ∧ j = Fin.last _ then -T else 0 := by
    intro G i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simp [FlagG.fvec, G.z_norm]
      | cast b =>
        simp only [FlagG.fvec, Fin.snoc_last, Fin.snoc_castSucc]
        rw [← (VS D).herm.eq (G.e b) G.z, G.z_orth b, map_zero]
        simp [Fin.castSucc_ne_last]
    | cast a =>
      induction j using Fin.lastCases with
      | last => simp [FlagG.fvec, G.z_orth, Fin.castSucc_ne_last]
      | cast b => simp [FlagG.fvec, G.e_iso, Fin.castSucc_ne_last]
  obtain ⟨g, hg, hgi⟩ := GlobalTheory.St.WittT.witt_family F.fvec F'.fvec (hind F) (hind F')
    (fun i j => by rw [hgram F, hgram F'])
  exact ⟨g, hg, hgi⟩

theorem iso_X {D : D7} {T : D.host.E} (G : FlagG (VS D) D.R.rS T) :
    ∀ y ∈ G.X, ∀ x ∈ G.X, (VS D).hT y x = 0 := by
  intro y hy x hx
  induction hx using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨b, rfl⟩ := hw
    induction hy using Submodule.span_induction with
    | mem v hv => obtain ⟨a, rfl⟩ := hv; exact G.e_iso a b
    | zero => simp
    | add u v _ _ hu hv => simp [hu, hv]
    | smul c u _ hu => simp [hu]
  | zero => simp
  | add u v _ _ hu hv => simp [hu, hv]
  | smul c u _ hu => simp [hu]

theorem xa_last {D : D7} {T : D.host.E} (G : FlagG (VS D) D.R.rS T) : G.Xa D.R.rS = G.X := by
  unfold FlagG.Xa FlagG.X
  congr 1
  ext v
  simp

theorem lsub_eq {D : D7} {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T')
    (h : F.fl.X = F'.fl.X) (Λ : LV D) : Lsub Λ F = Lsub Λ F' := by
  simp only [Lsub, Lrep, Xsp, h]

theorem xlam_eq {D : D7} {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T')
    (h : F.fl.X = F'.fl.X) (Λ : LV D) : XLam Λ F = XLam Λ F' := by
  simp only [XLam, Xsp, h]

theorem row_lattice_of_local_standard : ∀ (D : D7) (Tn : ℕ), Tn ≠ 0 → ∀ (F0 : FlagG (VS D) D.R.rS (Tn : D.host.E)) (G : LFlag (D.sp.Y 0) D.R.rS (Tn : D.host.E)) (Z : LocDat D) (A : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS), (∀ p, (A p).f = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) → ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → (∀ p, ∃ n ∈ (A p).N, ∃ L, (A p).IsInner L ∧ lattice₂ D Z.M p Λ = LocNG.img n ((A p).LamStd L)) → ∃ g, Adapt g (lf D F0) G ∧ IsRowLat D F0 (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) := by
  intro D Tn hTn F0 G Z A hA Λ hΛ hloc
  have hU := GlobalTheory.T.isUnimodular_of_local_standardLattice_translates
  have hX := GlobalTheory.T.isotropicPart_eq_span_scaledFrame_unitriangular
  have hZ := GlobalTheory.T.exists_add_isotropicSpan_mem_locallyStandardLattice
  have hP := GlobalTheory.T.anisotropicFrameVector_primitive_in_innerLattice
  have hM := GlobalTheory.T.exists_flag_of_unitriangular_isotropic_shift
  have hTr := GlobalTheory.T.rowLattice_properties_transport_by_isometry
  have hC := GlobalTheory.T.fixed_conv_of_integral_flag_lattice
  have hu := hU D Z A Λ hΛ hloc
  obtain ⟨e', he', hXe⟩ := hX D _ G Z A hA Λ hΛ hloc
  obtain ⟨x, hx, hzx⟩ := hZ D _ G Z A hA Λ hΛ hloc
  have hpr := hP D _ G Z A hA Λ hΛ hloc
  obtain ⟨G', hGe, hGz, hGX⟩ := hM D _ G.fl e' x he' hx
  have hT0 : ((Tn : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hTn
  obtain ⟨g, hg, hga⟩ := witt_flag D _ hT0 F0 G'
  have hX' : XLam Λ (lf D G') = XS D G' := by
    rw [xlam_eq (lf D G') G hGX, hXe, XS, hGe]
  have hpr' : ∀ c : D.host.E, c • G'.z ∈ Lsub Λ (lf D G') → ∃ o : 𝓞 D.host.E, (o : D.host.E) = c := by
    intro c hc
    rw [lsub_eq (lf D G') G hGX] at hc
    refine hpr c ?_
    have hcx : c • G.fl.z = c • G'.z - c • x := by rw [hGz, smul_add]; abel
    rw [hcx]
    refine Submodule.sub_mem _ hc ?_
    have hxX : c • x ∈ (Xsp G : Submodule D.host.E (VS D).V) := Submodule.smul_mem _ c hx
    refine ⟨Submodule.mem_sup_right hxX, ?_⟩
    show c • x ∈ orth (VS D) (Xsp G)
    simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
    intro y hy
    exact iso_X G.fl y hy _ hxX
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hTr D _ F0 G' g hg hga Λ hΛ hu (hGz ▸ hzx) hX' hpr'
  refine ⟨g, ⟨hg, fun a => ?_⟩, h1, ⟨h2, h3, ⟨h4, rfl⟩, hC D _ F0 _ h5 h6⟩, h5⟩
  show g (F0.fvec a) - G.fl.fvec a ∈ G.fl.Xa a.val
  rw [hga a]
  induction a using Fin.lastCases with
  | last =>
    simp only [FlagG.fvec, Fin.snoc_last, Fin.val_last, hGz, xa_last]
    simpa using hx
  | cast b =>
    simp only [FlagG.fvec, Fin.snoc_castSucc, Fin.val_castSucc, hGe]
    exact he' b

end GlobalTheory.RowLatAdapt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticeOfLocallyStandardFrameStatement

section

@[expose] public section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rowLattice_of_locally_standard_frame : ∀ (D : D7) (Tn : ℕ), Tn ≠ 0 → ∀ (F0 : FlagG (VS D) D.R.rS (Tn : D.host.E)) (G : LFlag (D.sp.Y 0) D.R.rS (Tn : D.host.E)) (Z : LocDat D) (A : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS), (∀ p, (A p).f = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) → ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → (∀ p, ∃ n ∈ (A p).N, ∃ L, (A p).IsInner L ∧ lattice₂ D Z.M p Λ = LocNG.img n ((A p).LamStd L)) → ∃ g, Adapt g (lf D F0) G ∧ IsRowLat D F0 (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) := by
  first | exact @GlobalTheory.RowLatAdapt.row_lattice_of_local_standard | exact GlobalTheory.RowLatAdapt.row_lattice_of_local_standard | (intros; apply GlobalTheory.RowLatAdapt.row_lattice_of_local_standard <;> assumption)
end
end
