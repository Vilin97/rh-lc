module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwArgs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeoHalfUpd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisionCompatibleAtReadIdentificationsStatement
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Formalism.LocalToGlobal.IndefiniteReal.WeakCharacterisationWithError
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FurtherFaceStatementsIndependentOfError
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PartAtUpdSReFace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReFacePrim
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.XEUpdSZeroLam
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.XEUpdSZeroLam
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FurtherRowsUpdatedScalars

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section
namespace GlobalTheory.Mem.R3
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]



theorem prim_updS (R : RealDat3 D A3 Ks) (F : Face3 D A3) (lam : type_of% R.lam3) (h : PrimRows3 R F)
    (h1 : ∀ i t p v, 0 < lam i t p v) (h2 : (R.updS R.kap lam).PThmB) (h3 : (R.updS R.kap lam).PThmA)
    (h4 : ((R.updS R.kap lam).toCx3 F).GalD F.cr false) : PrimRows3 (R.updS R.kap lam) F := by
  -- Reduce projections of the updated records before checking the row proofs.
  obtain ⟨R₂, _, _, _, _⟩ := R
  cases R₂
  dsimp only [RealDat3.updS, RealDat.upd6] at h2 h3 h4 ⊢
  obtain ⟨⟨hE, hR⟩, ⟨hW, hL⟩⟩ := h.hecke
  exact
  { heckeR := h.heckeR
    heckeL := h.heckeL
    hecke := ⟨⟨hE, ⟨hR.intw, hR.comm, hR.parts⟩⟩, ⟨hW, ⟨hL.intw, hL.comm, hL.parts⟩⟩⟩
    gUnit := h.gUnit
    gEquiv := h.gEquiv
    block := h.block
    rowTest := h.rowTest
    liftTest := h.liftTest
    liftTestB := h.liftTestB
    liftOnto := fun hW' hh => h.liftOnto hW' ⟨hh.intw, hh.comm, hh.parts⟩
    pos := h.pos
    posScal := ⟨h.posScal.1, h1⟩
    levE := h.levE
    h2P := h.h2P
    thmB := h2
    sumE := h.sumE
    unif := h.unif
    mLat := h.mLat
    levW := h.levW
    thmA := h3
    sumW := h.sumW
    scalConj := h4
    dimParts := h.dimParts }



theorem pins_updS (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (lam : type_of% R.lam3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (e : type_of% R.err0) (hP : Pins R F cG)
    (hs : (R.updS R.kap lam).IsScal (reFace F Dc Sp Zsc)) : Pins ((R.updS R.kap lam).withErr e) (reFace F Dc Sp Zsc) cG := by
  let R' := R.updS R.kap lam
  let F' := reFace F Dc Sp Zsc
  have h := hP.char
  have hC : R'.WeakCharacterisation F' :=
    ⟨h.base, ⟨h.inert.tie, h.inert.onto, h.inert.hR, h.inert.hL, h.inert.SF⟩, h.fullY, h.fullX, h.fullP, hs,
      ⟨h.tup.mu_off, h.tup.mu_used, h.tup.mu_ne, h.tup.mu_conj, h.tup.mu_on⟩, h.phase, h.allPl⟩
  exact ⟨RealDat3.weak_characterisation_with_error (R := R') (F := F') hC e,
    reFace_keep R' F cG Dc Sp Zsc e hP.keep, hP.phs, hP.trSem⟩



theorem furtherRows_updatedScalars (R : RealDat3 D A3 Ks) (F : Face3 D A3) (lam : type_of% R.lam3) (h : UnusedChoiceStatements R F) :
    UnusedChoiceStatements (R.updS R.kap lam) F := ⟨h.ex, h.conj, h.levelW, h.integral⟩

end GlobalTheory.Mem.R3

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadUpdSKeep

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section
namespace GlobalTheory.Mem.R3
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]



theorem read_updS_keep (R : RealDat3 D A3 Ks) (F : Face3 D A3) (lam : type_of% R.lam3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (err : type_of% R.err0)
    (hX : ∀ b, (((R.updS R.kap lam).toCx3 F).data F.cr b).XE = ((R.toCx3 F).data F.cr b).XE) (X0 : BaseLevelRowSide D)
    (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) :
    ∃ (Y' : Read (A3 := A3) ((R.updS R.kap lam).withErr err).toRealDat (reFace F Dc Sp Zsc).lv2 X0) (Z' : ReadL ((R.updS R.kap lam).withErr err) (reFace F Dc Sp Zsc) X0 Y'), Y'.tup = Y.tup ∧ Y'.tupT = Y.tupT ∧ HEq Y'.jA Y.jA ∧ HEq Y'.jA0 Y.jA0 ∧ HEq Y'.eMt Y.eMt ∧ HEq Y'.PY Y.PY ∧ HEq Y'.eFT Y.eFT ∧ HEq Y'.IL Y.IL ∧ HEq Y'.PW Y.PW ∧ HEq Y'.eE Y.eE ∧ HEq Y'.mj.eW Y.mj.eW ∧ HEq Z'.eRR Z.eRR ∧ HEq Z'.jW Z.jW := by
  refine ⟨reFaceRead (R.updS R.kap lam) F Dc Sp Zsc err X0 Y,
    reFaceReadL (R.updS R.kap lam) F Dc Sp Zsc err X0 Y (scalReadL R F lam hX X0 Y Z), ?_⟩
  have fields := And.intro (Eq.refl Y.tup) <| And.intro (Eq.refl Y.tupT) <|
    And.intro (HEq.refl Y.jA) <| And.intro (HEq.refl Y.jA0) <|
    And.intro (HEq.refl Y.eMt) <| And.intro (HEq.refl Y.PY) <|
    And.intro (HEq.refl Y.eFT) <| And.intro (HEq.refl Y.IL) <|
    And.intro (HEq.refl Y.PW) <| And.intro (HEq.refl Y.eE) <|
    And.intro (HEq.refl Y.mj.eW) <| And.intro (HEq.refl Z.eRR) (HEq.refl Z.jW)
  -- Compare the fully elaborated conjunction in the kernel, which reduces the copied fields.
  run_tac
    Lean.Elab.Tactic.closeMainGoalUsing `exact fun target _ => do
      let proof ← Lean.Elab.Tactic.elabTerm (Lean.mkIdent `fields) none
      let actual ← Lean.instantiateMVars (← Lean.Meta.inferType proof)
      let target ← Lean.instantiateMVars target
      let context ← Lean.instantiateLCtxMVars (← Lean.getLCtx)
      match Lean.Kernel.isDefEq (← Lean.getEnv) context actual target with
      | .ok true => pure proof
      | .ok false => throwError "The copied fields are not definitionally equal"
      | .error err => Lean.throwKernelException err

end GlobalTheory.Mem.R3

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReFaceZeroPartConventionsChosenAgain

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3



theorem reFace_zero_parts : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs)) (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3), Pins R F cG → Holds R F → (∀ p, R.EEp3 p ≠ ⊥ → ∀ i, R.Wp3 i p ≠ ⊥ ∧ ∀ v, v ≠ A3.A.v0 → R.PartAt F i p v) → ∃ kap lam err, Pins ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) cG ∧ Holds ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) ∧ ErrEq ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) ∧ kap = R.kap ∧ (∀ i t p v, R.EEp3 p ≠ ⊥ → lam i t p v = R.lam3 i t p v) ∧ ∃ (Y' : Read (A3 := A3) ((R.updS kap lam).withErr err).toRealDat (reFace F Dc Sp Zsc).lv2 X0) (Z' : ReadL ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) X0 Y'), Y'.tup = Y.tup ∧ Y'.tupT = Y.tupT ∧ HEq Y'.jA Y.jA ∧ HEq Y'.jA0 Y.jA0 ∧ HEq Y'.eMt Y.eMt ∧ HEq Y'.PY Y.PY ∧ HEq Y'.eFT Y.eFT ∧ HEq Y'.IL Y.IL ∧ HEq Y'.PW Y.PW ∧ HEq Y'.eE Y.eE ∧ HEq Y'.mj.eW Y.mj.eW ∧ HEq Z'.eRR Z.eRR ∧ HEq Z'.jW Z.jW := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z Dc Sp Zsc hP hH hZ
  have h1 := pins_updS R F cG (zeroLam R F (Zsc (R.toCx3 F).zs).l6m) Dc Sp Zsc (reFaceErr (R.updS R.kap (zeroLam R F (Zsc (R.toCx3 F).zs).l6m)) F Dc Sp Zsc) hP (scal_zeroLam R F Dc Sp Zsc hZ hP.char.scal)
  have h2 := prim_updS R F (zeroLam R F (Zsc (R.toCx3 F).zs).l6m) hH.prim (zeroLam_pos R F (Zsc (R.toCx3 F).zs).l6m hH.prim.posScal.2)
    (thmB_zeroLam R F (Zsc (R.toCx3 F).zs).l6m hZ hH.prim.thmB) (thmA_zeroLam R F (Zsc (R.toCx3 F).zs).l6m hH.prim.thmA) (galD_zeroLam R F (Zsc (R.toCx3 F).zs).l6m hH.prim.scalConj)
  have h3 := Holds.mk (reFace_prim (R.updS R.kap (zeroLam R F (Zsc (R.toCx3 F).zs).l6m)) F Dc Sp Zsc (reFaceErr (R.updS R.kap (zeroLam R F (Zsc (R.toCx3 F).zs).l6m)) F Dc Sp Zsc) h2)
    (further_face_statements_independent_of_error (R.updS R.kap (zeroLam R F (Zsc (R.toCx3 F).zs).l6m)) F Dc Sp Zsc (reFaceErr (R.updS R.kap (zeroLam R F (Zsc (R.toCx3 F).zs).l6m)) F Dc Sp Zsc) (furtherRows_updatedScalars R F (zeroLam R F (Zsc (R.toCx3 F).zs).l6m) hH.aux)) hH.ok hH.sep
  have h4 := reFace_errEq (R.updS R.kap (zeroLam R F (Zsc (R.toCx3 F).zs).l6m)) F Dc Sp Zsc
  have h5 : ∀ i t p v, R.EEp3 p ≠ ⊥ → zeroLam R F (Zsc (R.toCx3 F).zs).l6m i t p v = R.lam3 i t p v :=
    fun i t p v hp => zeroLam_of_ne R F _ (hZ p hp i).1 fun hv => (hZ p hp i).2 v hv
  have h6 := read_updS_keep R F (zeroLam R F (Zsc (R.toCx3 F).zs).l6m) Dc Sp Zsc (reFaceErr (R.updS R.kap (zeroLam R F (Zsc (R.toCx3 F).zs).l6m)) F Dc Sp Zsc)
    (XE_updS_zeroLam R F (Zsc (R.toCx3 F).zs).l6m hP.char hH.prim hH.ok hH.sep hZ) X0 Y Z
  refine ⟨R.kap, (zeroLam R F (Zsc (R.toCx3 F).zs).l6m), (reFaceErr (R.updS R.kap (zeroLam R F (Zsc (R.toCx3 F).zs).l6m)) F Dc Sp Zsc), ?_, ?_, ?_, rfl, ?_, ?_⟩
  · exact (by with_unfolding_all exact (h1 :))
  · exact (by with_unfolding_all exact (h3 :))
  · exact (by with_unfolding_all exact (h4 :))
  · exact (by with_unfolding_all exact (h5 :))
  · exact (by with_unfolding_all exact (h6 :))

end GlobalTheory.Mem.R3

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReFaceZeroPartConventionsChosenAgainStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.reFace_zero_part_conventions_chosen_again : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs)) (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3), Pins R F cG → Holds R F → (∀ p, R.EEp3 p ≠ ⊥ → ∀ i, R.Wp3 i p ≠ ⊥ ∧ ∀ v, v ≠ A3.A.v0 → R.PartAt F i p v) → ∃ kap lam err, Pins ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) cG ∧ Holds ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) ∧ ErrEq ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) ∧ kap = R.kap ∧ (∀ i t p v, R.EEp3 p ≠ ⊥ → lam i t p v = R.lam3 i t p v) ∧ ∃ (Y' : Read (A3 := A3) ((R.updS kap lam).withErr err).toRealDat (reFace F Dc Sp Zsc).lv2 X0) (Z' : ReadL ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) X0 Y'), Y'.tup = Y.tup ∧ Y'.tupT = Y.tupT ∧ HEq Y'.jA Y.jA ∧ HEq Y'.jA0 Y.jA0 ∧ HEq Y'.eMt Y.eMt ∧ HEq Y'.PY Y.PY ∧ HEq Y'.eFT Y.eFT ∧ HEq Y'.IL Y.IL ∧ HEq Y'.PW Y.PW ∧ HEq Y'.eE Y.eE ∧ HEq Y'.mj.eW Y.mj.eW ∧ HEq Z'.eRR Z.eRR ∧ HEq Z'.jW Z.jW := by
  first | exact @GlobalTheory.Mem.R3.reFace_zero_parts | exact GlobalTheory.Mem.R3.reFace_zero_parts | (intros; apply GlobalTheory.Mem.R3.reFace_zero_parts <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnParamsInstanceData

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.TwistedScalarIndependence

theorem dep_imp {α : Sort _} {β : α → Sort _} (P : ∀ a, β a → Prop) {a a' : α} {b : β a} {b' : β a'} (h : a' = a) (hb : HEq b' b)
    (H : P a b) : P a' b' := by
  subst h
  cases hb
  exact H

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}

section Field

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3)
  (lam : type_of% R.lam3) (err : type_of% R.err0)

abbrev newR : RealDat3 D A3 Ks := (R.updS R.kap lam).withErr err

variable {R F} {X0 : BaseLevelRowSide D} {Y : Read (A3 := A3) R.toRealDat F.lv2 X0}
  {Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)} {Sp₀ Sp : ∀ Zs, SPer (Dc Zs)}
  {Zsc₀ Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3}
  {Y' : Read (A3 := A3) (newR R lam err).toRealDat (reFace F Dc Sp Zsc).lv2 X0}



def newC (C₀ : ReadC R (reFace F Dc Sp₀ Zsc₀) X0 Y) (ht : Y'.tup = Y.tup) (hj : HEq Y'.jA Y.jA) :
    ReadC (newR R lam err) (reFace F Dc Sp Zsc) X0 Y' where
  wU := (by with_unfolding_all exact (C₀.wU :))
  bij := (by with_unfolding_all exact (C₀.bij :))
  eNu := (by with_unfolding_all exact (C₀.eNu :))
  NuC := (by with_unfolding_all exact (C₀.NuC :))
  nu := (by with_unfolding_all exact (C₀.nu :))
  pt := by
    have h := dep_imp (β := fun tup : T → D.what₂.Tup =>
        ∀ t, (Fin (rDim D A3.A F.P1 F.ψ1 t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Amb (tup t))
      (fun tup jA => ∀ (u : D.what₂.Word) (t : T) (x : Fin ((Dc (zsOf R F)).a (C₀.wU u)) → D.what₂.LL)
        (f : Fin ((A3.side3 F.P1 F.ψ1 (zsOf R F)).nV t) → D.what₂.LL),
        D.what₂.embLL ((Dc (zsOf R F)).Pt (C₀.wU u) t x f) =
          D.what₂.perCol u (tup t) (D.jN u (C₀.eNu u x)) (jA t ((rV0 D A3.A F.P1 F.ψ1 t).mulVec f)))
      (b := Y.jA) (b' := (by with_unfolding_all exact (Y'.jA :))) ht ((by with_unfolding_all exact (hj :))) ((by with_unfolding_all exact (C₀.pt :)))
    with_unfolding_all exact (h :)



theorem rationalFormsComparison_baseLevel_indep_scalars {a0 : AmbForm D X0.s} (h : ∃ J, AmbTie D A3.A X0.s a0 F.P0 F.ψ0 Y.tup Y.jA0 J) (ht : Y'.tup = Y.tup)
    (hj : HEq Y'.jA0 Y.jA0) :
    ∃ J, AmbTie D A3.A X0.s a0 (reFace F Dc Sp Zsc).P0 (reFace F Dc Sp Zsc).ψ0 Y'.tup Y'.jA0 J := by
  have h' := dep_imp (β := fun tup : T → D.what₂.Tup =>
      ∀ t, (Fin (rDim D A3.A F.P0 F.ψ0 t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] X0.s.Amb (tup t))
    (fun tup jA => ∃ J, AmbTie D A3.A X0.s a0 F.P0 F.ψ0 tup jA J) (b := Y.jA0) (b' := (by with_unfolding_all exact (Y'.jA0 :))) ht ((by with_unfolding_all exact (hj :))) h
  exact (by with_unfolding_all exact (h' :))



theorem mj_new {Z : ReadL R F X0 Y} {Z' : ReadL (newR R lam err) (reFace F Dc Sp Zsc) X0 Y'} {Xd : DivX D} (h : MjAre Z Xd)
    (hj : HEq Z'.jW Z.jW) : MjAre Z' Xd := by
  set_option backward.isDefEq.lazyWhnfCore false in
  set_option backward.isDefEq.lazyProjDelta false in
    obtain ⟨J, hJ⟩ := h
    have e : Z'.jW = (by with_unfolding_all exact (Z.jW :)) := eq_of_heq ((by with_unfolding_all exact (hj :)))
    refine ⟨⟨(by with_unfolding_all exact (J.eW :))⟩, ?_, (by with_unfolding_all exact (hJ.hlat :))⟩
    rewrite [e]
    exact (by with_unfolding_all exact (hJ.j_eq :))

end Field



def newGeo {C : Formalism.L2.Pj.CoreJ D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat3 D A3 C.Q.c.F} (lam : type_of% R.lam3)
    (err : type_of% R.err0) (g : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1) :
    GlobalTheory.RealGeo.GeoHalf C (GlobalTheory.RealGeo.Upd.upE C R.toRealDat R.kap R.lam err) fun _ => 1 :=
  ⟨g.κ, g.v₀, GlobalTheory.RealGeo.Upd.updFWT C R.toRealDat R.kap R.lam err g.fw, g.bar,
    fun i => GlobalTheory.RealGeo.Upd.updO C R.toRealDat R.kap R.lam err (g.O i),
    fun i => GlobalTheory.RealGeo.Upd.omPins_upE R.kap R.lam err g.O i (g.pins i), g.rhoGeo, g.equivAll, g.cTie, g.phase⟩



theorem inGeo_new {C : Formalism.L2.Pj.CoreJ D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat3 D A3 C.Q.c.F} (lam : type_of% R.lam3)
    (err : type_of% R.err0) {g : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1} (h : GlobalTheory.RealGeo.InGeo g) :
    GlobalTheory.RealGeo.InGeo (newGeo lam err g) := by
  set_option backward.isDefEq.lazyWhnfCore false in
  set_option backward.isDefEq.lazyProjDelta false in
    exact ⟨h.jEvExists, h.jEvBar, h.evInj, h.jUnif, h.geoAct, h.latFull, h.dimMatch⟩

section Tw

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {C : Formalism.L2.Pj.CoreJ D} [Algebra C.Q.c.F D.what₂.LL]
  {R : RealDat3 D A3 C.Q.c.F} {F : Face3 D A3} {cG : G0 R.Pg D.R.r ≃* G0g D.nd} (lam : type_of% R.lam3) (err : type_of% R.err0)
  {Y : Read (A3 := A3) R.toRealDat F.lv2 ex.p0} {Z : ReadL R F ex.p0 Y}
  {Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)} {Sp₀ Sp : ∀ Zs, SPer (Dc Zs)}
  {Zsc₀ Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3}
  {Y' : Read (A3 := A3) (newR R lam err).toRealDat (reFace F Dc Sp Zsc).lv2 ex.p0}



def newTw (hC : GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧
      GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay)
    (g : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1) (Z' : ReadL (newR R lam err) (reFace F Dc Sp Zsc) ex.p0 Y')
    (C₀ : ReadC R (reFace F Dc Sp₀ Zsc₀) ex.p0 Y) (sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (Sp (zsOf R F)).HH)
    (hP : Pins (newR R lam err) (reFace F Dc Sp Zsc) cG) (hH : Holds (newR R lam err) (reFace F Dc Sp Zsc))
    (hE : ErrEq (newR R lam err) (reFace F Dc Sp Zsc))
    (hG : GrpTie D A3.A F.P0 F.ψ0 F.P1 F.ψ1 (R.eG.trans cG))
    (hA : ∃ J, AmbTie D A3.A ex.p0.s ex.amb0 F.P0 F.ψ0 Y.tup Y.jA0 J) (hM : MjAre Z Yd)
    (ht : Y'.tup = Y.tup) (hj : HEq Y'.jA Y.jA) (hj0 : HEq Y'.jA0 Y.jA0) (hW : HEq Z'.jW Z.jW) : TwIn ex where
  G := G
  Pl0 := Pl0
  I0 := I0
  T := T
  A3 := A3
  core := C
  R := newR R lam err
  F := reFace F Dc Sp Zsc
  cG := cG
  geo := (by with_unfolding_all exact ((newGeo lam err g) :))
  pins := hP
  err := hE
  Y := Y'
  Z := Z'
  C := newC lam err C₀ ht hj
  sEE := (by with_unfolding_all exact (sEE :))
  div := (GlobalTheory.T.divisionCompatible_at_readIdentifications hC D G Pl0 I0 T A3 C.Q.c.F (newR R lam err) (reFace F Dc Sp Zsc) cG ex.p0 Y' Z' (newC lam err C₀ ht hj)
    (by with_unfolding_all exact (sEE :)) Yd (mj_new lam err hM hW).choose hP hH (fun _ _ => (by with_unfolding_all exact (hG :)))).1
  JA := (rationalFormsComparison_baseLevel_indep_scalars lam err hA ht hj0).choose
  amb0 := (rationalFormsComparison_baseLevel_indep_scalars lam err hA ht hj0).choose_spec
  JM := (mj_new lam err hM hW).choose
  mjH := (mj_new lam err hM hW).choose_spec

-- Check the dependent column projections before specializing the ambient data to a row.

private theorem newTw_preserves_columns
    (hC : GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧
      GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧
      GlobalTheory.Published.CuspRapidDecay)
    (g : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1)
    (Z' : ReadL (newR R lam err) (reFace F Dc Sp Zsc) ex.p0 Y')
    (C₀ : ReadC R (reFace F Dc Sp₀ Zsc₀) ex.p0 Y)
    (sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (Sp (zsOf R F)).HH)
    (hP : Pins (newR R lam err) (reFace F Dc Sp Zsc) cG)
    (hH : Holds (newR R lam err) (reFace F Dc Sp Zsc))
    (hE : ErrEq (newR R lam err) (reFace F Dc Sp Zsc))
    (hG : GrpTie D A3.A F.P0 F.ψ0 F.P1 F.ψ1 (R.eG.trans cG))
    (hA : ∃ J, AmbTie D A3.A ex.p0.s ex.amb0 F.P0 F.ψ0 Y.tup Y.jA0 J)
    (hM : MjAre Z Yd) (ht : Y'.tup = Y.tup) (hj : HEq Y'.jA Y.jA)
    (hj0 : HEq Y'.jA0 Y.jA0) (hW : HEq Z'.jW Z.jW) (hg : GlobalTheory.RealGeo.InGeo g) :
    let x := newTw (R := R) (F := F) (cG := cG) (Y := Y) (Z := Z) (Dc := Dc)
      (Sp₀ := Sp₀) (Sp := Sp) (Zsc₀ := Zsc₀) (Zsc := Zsc) (Y' := Y')
      lam err hC g Z' C₀ sEE hP hH hE hG hA hM ht hj hj0 hW
    HEq x.sEE sEE ∧ HEq x.C.wU C₀.wU ∧ HEq x.C.eNu C₀.eNu ∧ GlobalTheory.RealGeo.InGeo x.geo := by
  have hCols := And.intro (HEq.refl sEE)
    (And.intro (HEq.refl C₀.wU) (And.intro (HEq.refl C₀.eNu) (inGeo_new lam err hg)))
  -- Check the dependent projections together with the kernel's conversion checker.
  run_tac
    Lean.Elab.Tactic.closeMainGoalUsing `exact fun _ _ =>
      Lean.Elab.Tactic.elabTerm (Lean.mkIdent `hCols) none

end Tw

end GlobalTheory.Mem.R3.TwistedScalarIndependence

namespace GlobalTheory.Mem.R3

open TwistedScalarIndependence



theorem twArgs_exists : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (L : SizeData₂ (w.st Z).toD7) (hT : GatTies (w.st Z).toD7) (Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L) (Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX (w.st Z).toD7) (cX : ExtraC) (ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX) (t : RowsT K w Z Wt ex.p0), AmbAre t.r.Z ex.amb ex.amb0 → MjAre t.r.Z Yd → GrpTie (w.st Z).toD7 (famT t).A t.r.z.F.P0 t.r.z.F.ψ0 t.r.z.F.P1 t.r.z.F.ψ1 (t.r.z.R.eG.trans t.r.z.cG) → (∀ p, t.r.z.R.EEp3 p ≠ ⊥ → ∀ i, t.r.z.R.Wp3 i p ≠ ⊥ ∧ ∀ v, v ≠ (famT t).A.v0 → t.r.z.R.PartAt t.r.z.F i p v) → ∀ Dc Sp₀ Zsc₀ (C₀ : ReadC t.r.z.R (reFace t.r.z.F Dc Sp₀ Zsc₀) ex.p0 ((t.r.Y))) (Sp : ∀ Zs, SPer (Dc Zs)) Zsc (sEE : (t.r.z.R.toCx3 t.r.z.F).EE →ₗ⋆[ℂ] (Sp (zsOf t.r.z.R t.r.z.F)).HH), ∃ a : TwArgs ex t, a.Dc = Dc ∧ HEq a.Sp Sp ∧ a.Zsc = Zsc ∧ HEq a.x.sEE sEE ∧ HEq a.x.C.wU C₀.wU ∧ HEq a.x.C.eNu C₀.eNu ∧ GlobalTheory.RealGeo.InGeo a.x.geo := by
  intro hC K B f T w Z Wt L hT Gi Gl Kc Yd cX ex t hA hM hG hp Dc Sp₀ Zsc₀ C₀ Sp Zsc sEE
  obtain ⟨kap, lam, err, hP, hH, hE, rfl, hl, Y', Z', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ :=
    GlobalTheory.T.reFace_zero_part_conventions_chosen_again (w.st Z).toD7 _ _ _ _ (famT t) _ t.r.z.R t.r.z.F t.r.z.cG ex.p0 t.r.Y t.r.Z Dc Sp Zsc t.r.z.pins t.r.intersectionNumber_baseChange hp
  let x : TwIn ex := newTw (R := t.r.z.R) (F := t.r.z.F) (cG := t.r.z.cG) (Y := t.r.Y) (Z := t.r.Z) (Dc := Dc) (Sp₀ := Sp₀) (Sp := Sp)
    (Zsc₀ := Zsc₀) (Zsc := Zsc) (Y' := Y') lam err hC t.r.z.geo Z' C₀ sEE hP hH hE hG hA.2 hM h1 h3 h4 h13
  let a : TwArgs ex t :=
    { Dc := Dc, Sp := Sp, Zsc := Zsc, lam := lam, err := err, lam_eq := hl, x := x
      pack := rfl
      intersectionNumber_baseChange := (by with_unfolding_all exact (hH :))
      κ := (by with_unfolding_all exact ((HEq.refl t.r.z.geo.κ) :))
      v₀ := (by with_unfolding_all exact ((HEq.refl t.r.z.geo.v₀) :))
      fw := (by with_unfolding_all exact ((HEq.refl t.r.z.geo.fw.e) :))
      tup := (by with_unfolding_all exact ((heq_of_eq h1) :))
      tupT := (by with_unfolding_all exact ((heq_of_eq h2) :))
      jA := (by with_unfolding_all exact (h3 :))
      jA0 := (by with_unfolding_all exact (h4 :))
      eMt := (by with_unfolding_all exact (h5 :))
      PY := (by with_unfolding_all exact (h6 :))
      PW := (by with_unfolding_all exact (h9 :))
      eFT := (by with_unfolding_all exact (h7 :))
      IL := (by with_unfolding_all exact (h8 :))
      eE := (by with_unfolding_all exact (h10 :))
      eW := (by with_unfolding_all exact (h11 :))
      jW := (by with_unfolding_all exact (h13 :))
      eRR := (by with_unfolding_all exact (h12 :)) }
  have hCols := newTw_preserves_columns (R := t.r.z.R) (F := t.r.z.F) (cG := t.r.z.cG)
    (Y := t.r.Y) (Z := t.r.Z) (Dc := Dc) (Sp₀ := Sp₀) (Sp := Sp) (Zsc₀ := Zsc₀)
    (Zsc := Zsc) (Y' := Y') lam err hC t.r.z.geo Z' C₀ sEE hP hH hE hG hA.2 hM h1 h3 h4 h13 t.inGeo
  refine ⟨a, rfl, HEq.rfl, rfl, ?_⟩
  change HEq x.sEE sEE ∧ HEq x.C.wU C₀.wU ∧ HEq x.C.eNu C₀.eNu ∧ GlobalTheory.RealGeo.InGeo x.geo
  exact hCols

end GlobalTheory.Mem.R3

end
end
end
