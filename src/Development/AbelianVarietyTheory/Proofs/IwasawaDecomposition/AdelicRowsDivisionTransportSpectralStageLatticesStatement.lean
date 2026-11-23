module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OmPinsTr
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdxDefsUp
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BaseLevelRowSideTransport
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovedRowLiftDataToFittingStages
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicRowsDivisionOverReplacedLaterStages
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Wp3ApplyEqSqMulSubSqMul
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardReadingTransportAndExtensionTransStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicRowsDivisionOverReplacedLaterStagesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

theorem _root_.GlobalTheory.T.exists_adelicRowsDivision_over_replacedLaterStages : ∀ (B : Base) (C : Cols B) (a : Late B C) (c : Refill a) (px : PreX B.toPre) (I : ColIn B px) (hX : B.fields.Ok) (T : TwDat B) (Wt : Set B.places.Pl) (ix : C.Tup ≃ I.ι) (p0 : BaseLevelRowSide a.D) (r : RowsAre a.st I hX T Wt ix p0), ∃ r' : RowsAre c.to.st I hX T Wt ix (Tr.baseLevelRowSideTransport c p0), r'.z = GlobalTheory.Mem.R3.Rw.Mv.cpDat c.to c.same r.z ∧ HEq r'.Y.tup r.Y.tup ∧ HEq r'.Y.tupT r.Y.tupT ∧ HEq r'.Y.PY.ψ r.Y.PY.ψ ∧ HEq (fun i => (r'.Y.PW i).ψ) (fun i => (r.Y.PW i).ψ) ∧ HEq (fun π => principalLevelFrame.rowRepR r'.z.R.θ (r'.Y.eFT π)) (fun π => principalLevelFrame.rowRepR r.z.R.θ (r.Y.eFT π)) ∧ HEq (fun x => (r'.Y.Ish.jE x).1) (fun x => (r.Y.Ish.jE x).1) ∧ HEq (fun x => (r'.Y.Iz.jE x).1) (fun x => (r.Y.Iz.jE x).1) ∧ HEq r'.Y.eE r.Y.eE ∧ HEq r'.Y.jA r.Y.jA ∧ HEq r'.Y.jA0 r.Y.jA0 ∧ HEq r'.Y.eMt r.Y.eMt ∧ HEq r'.Y.mj.eW r.Y.mj.eW ∧ HEq r'.Z.jW r.Z.jW ∧ HEq r'.Z.eRR r.Z.eRR ∧ HEq r'.Z.eRR0 r.Z.eRR0 := by
  exact GlobalTheory.Mem.R3.Rw.Mv.rowsAre_refill
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftHermitianLatticesReplacedStagesEq

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.Up

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T₀ : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T₀ D.R.m}

theorem exists_mjHTie_of_eq (F : Face3 D A3) (Xd : DivX D) {X X' : Cx.CxData A3.fam3.amb3} (e : X' = X)
    (jW : ∀ i : Fin D.R.m, (Fin ((A3.indefDown (X'.data F.cr false)).dW i) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Mj ((i : ℕ) + 1))
    (jW0 : ∀ i : Fin D.R.m, (Fin ((A3.indefDown (X.data F.cr false)).dW i) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Mj ((i : ℕ) + 1))
    (hj : HEq jW jW0)
    (eW : ∀ i : Fin D.R.m, (Fin ((A3.indefDown (X'.data F.cr false)).dW i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Xd.MjH ((i : ℕ) + 1)).V)
    (h1 : ∀ (i : Fin D.R.m) x, Xd.jM ((i : ℕ) + 1) (eW i x) = jW i x)
    (h2 : ∀ i : Fin D.R.m, HLatTie (Xd.MjH ((i : ℕ) + 1)) ((A3.indefDown (X'.data F.cr false)).M i)
      ((A3.indefDown (X'.data F.cr false)).XW i) (eW i)) :
    ∃ J, MjHTie D A3.A Xd (A3.indefDown (X.data F.cr false)) jW0 J := by
  subst e
  cases hj
  exact ⟨⟨eW⟩, ⟨h1, h2⟩⟩

end GlobalTheory.Mem.R3.Rw.Up



theorem GlobalTheory.Mem.R3.Rw.Up.mjAre_back : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z)) (r : RowsAre (w.st Z) w.I hX T Wt (Equiv.refl _) p0) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) (r' : RowsAre (w.st (SRe.upL Z S' N h)) w.I hX T Wt (Equiv.refl _) (Tr.baseLevelRowSideTransport (Up.refUp Z S' N h) p0)), r'.z = Mv.cpDat (Up.refUp Z S' N h).to (Up.refUp Z S' N h).same r.z → HEq r'.Z.jW r.Z.jW → ∀ Y : DivX (w.D (SRe.upL Z S' N h)), MjAre r'.Z Y → MjAre r.Z (Up.divBack Y) := by
  intro K B f T w Z hX Wt p0 r S' N h r'
  obtain ⟨z', hold', Y', Z', tix⟩ := r'
  intro hz
  change z' = _ at hz
  subst z'
  intro hj Y hY
  letI : Algebra (Mv.cpDat (Up.refUp Z S' N h).to (Up.refUp Z S' N h).same r.z).core.Q.c.F
      (w.st (SRe.upL Z S' N h)).toD7.what₂.LL :=
    (Mv.cpDat (Up.refUp Z S' N h).to (Up.refUp Z S' N h).same r.z).alg
  change HEq Z'.jW r.Z.jW at hj
  change MjAre Z' Y at hY
  obtain ⟨J', t'⟩ := hY
  have e := toCx3_eq (Up.refUp Z S' N h).to (iK := r.z.alg) r.z.R r.z.F
  with_unfolding_all
    exact exists_mjHTie_of_eq r.z.F (divBack Y) e.symm Z'.jW r.Z.jW hj J'.eW t'.j_eq t'.hlat

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftHermitianLatticesReplacedStagesEqStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

theorem _root_.GlobalTheory.T.liftHermitianLattices_replacedStages_eq :
    ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T)
      (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z))
      (r : RowsAre (w.st Z) w.I hX T Wt (Equiv.refl _) p0) (S' : SStage B w.C Z.W)
      (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ)
      (r' : RowsAre (w.st (SRe.upL Z S' N h)) w.I hX T Wt (Equiv.refl _)
        (Tr.baseLevelRowSideTransport (Up.refUp Z S' N h) p0)),
      r'.z = GlobalTheory.Mem.R3.Rw.Mv.cpDat (Up.refUp Z S' N h).to (Up.refUp Z S' N h).same r.z →
        HEq r'.Z.jW r.Z.jW → ∀ Y : DivX (w.D (SRe.upL Z S' N h)),
          MjAre r'.Z Y → MjAre r.Z (Up.divBack Y) :=
  @GlobalTheory.Mem.R3.Rw.Up.mjAre_back
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowCompatibilitiesTransportReplacedStages

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section
namespace GlobalTheory.Mem.R3.Rw.Up



theorem rxs_up : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) (t' : RowsT K w (SRe.upL Z S' N h) Wt (Tr.baseLevelRowSideTransport (Up.refUp Z S' N h) p0)), RowsSame t t' → Nonempty (RXs t) → Nonempty (RXs t') := by
  intro K B f T w Z Wt p0 t S' N h t' hs ⟨x⟩
  have hstd : t'.r.z.Std := (GlobalTheory.T.standardReading_transport_and_extension_trans).1 B f T w Z (SRe.upL Z S' N h) t.hX Wt t.r.z t'.r.z hs.Xg hs.tr hs.R hs.core x.std
  obtain ⟨hX', r', exAt', inGeo', grpAt', grp', mu'', exact', untw', emt0', emt', etaF', rowInt', idx'⟩ := t'
  obtain ⟨z', holds', Y', Z'', tup_ix'⟩ := r'
  obtain @⟨Xg', tr', core', alg', alg_eq', R', cG', geo', pins', lev', idG', good', mu', le', Ks'⟩ := z'
  have hXg := hs.Xg
  have htr := hs.tr
  have hcore := hs.core
  have hR := hs.R
  have hcG := hs.cG
  have htup := hs.tup
  have hjA := hs.jA
  have hjA0 := hs.jA0
  have heMt := hs.eMt
  clear hs
  dsimp only at hXg htr hcore hR hcG htup hjA hjA0 heMt hstd
  subst hXg htr
  have hc := eq_of_heq hcore
  subst hc
  have ha : @Eq _ alg' t.r.z.alg :=
    Algebra.algebra_ext _ _ fun r => B.embLL.injective ((alg_eq' r).trans (t.r.z.alg_eq r).symm)
  subst ha
  have hr := eq_of_heq hR
  cases hr
  have hg := eq_of_heq hcG
  cases hg
  cases Y' with
  | mk tup' tupT' tupT_tup' tupTie' tup0' muAt' hm' hTop' hinj' Ish' Iz' IL' Kc' PY' PW' eFT' ιW' tied' prtE' prtE0' prtWE' xi'
      isomFin' frameMatch' hF' stdPsi' jA' jA0' eMt' => ?_
  dsimp only at htup hjA hjA0 heMt
  have e1 := eq_of_heq htup
  cases e1
  have e2 := eq_of_heq hjA
  cases e2
  have e3 := eq_of_heq hjA0
  cases e3
  have e4 := eq_of_heq heMt
  cases e4
  exact ⟨{
    all := {
      jA := (by with_unfolding_all exact (x.all.jA :))
      jA0 := (by with_unfolding_all exact (x.all.jA0 :))
      eMt := (by with_unfolding_all exact (x.all.eMt :))
      formsA := (by with_unfolding_all exact (x.all.formsA :))
      latA := (by with_unfolding_all exact (x.all.latA :))
      formsAtBottomLevel := (by with_unfolding_all exact (x.all.formsAtBottomLevel :))
      latA0 := (by with_unfolding_all exact (x.all.latA0 :))
      formsL := (by with_unfolding_all exact (x.all.formsL :))
      latL := (by with_unfolding_all exact (x.all.latL :))
      cen := (by with_unfolding_all exact (x.all.cen :)) }
    jA_use := (by with_unfolding_all exact (x.jA_use :))
    movedReadingSameMaps_baseReading_agrees := (by with_unfolding_all exact (x.movedReadingSameMaps_baseReading_agrees :))
    eMt_use := (by with_unfolding_all exact (x.eMt_use :))
    e := (by with_unfolding_all exact (x.e :))
    eMt0 := (by with_unfolding_all exact (x.eMt0 :))
    eMtTw := (by with_unfolding_all exact (x.eMtTw :))
    crd := (by with_unfolding_all exact (x.crd :))
    io := (by with_unfolding_all exact (x.io :))
    sha := (by with_unfolding_all exact (x.sha :))
    laws := (by with_unfolding_all exact ((Mv.lawsCore_tr (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩)
      ⟨(SRe.upL Z S' N h).W, (SRe.upL Z S' N h).V, (SRe.upL Z S' N h).S, (SRe.upL Z S' N h).N, (SRe.upL Z S' N h).G⟩ (K := t.r.z.core.toCore) x.laws) :))
    canon := (by with_unfolding_all exact (x.canon :))
    rank := (by with_unfolding_all exact (x.rank :))
    pb := (by with_unfolding_all exact (x.pb :))
    std := (by with_unfolding_all exact (hstd :)) }⟩

end GlobalTheory.Mem.R3.Rw.Up
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowCompatibilitiesTransportReplacedStagesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

theorem _root_.GlobalTheory.T.rowCompatibilities_transport_replacedStages : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) (t' : RowsT K w (SRe.upL Z S' N h) Wt (Tr.baseLevelRowSideTransport (Up.refUp Z S' N h) p0)), RowsSame t t' → Nonempty (RXs t) → Nonempty (RXs t') := by
  first | exact @GlobalTheory.Mem.R3.Rw.Up.rxs_up | exact GlobalTheory.Mem.R3.Rw.Up.rxs_up | (intros; apply GlobalTheory.Mem.R3.Rw.Up.rxs_up <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicRowsDivisionTransportSpectralStageLattices

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section
namespace GlobalTheory.Mem.R3.Rw.Up



theorem rows_up_at : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ), ∃ t' : RowsT K w (SRe.upL Z S' N h) Wt (Tr.baseLevelRowSideTransport (refUp Z S' N h) p0), RowsSame t t' ∧ HEq t'.r.z.geo (geoHalf (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (SRe.upL Z S' N h) (iK := t.r.z.alg) t.r.z.geo) ∧ SRe.pkOf t' = (SRe.pkOf t).up Z S' N h ∧ (Nonempty (RXs t) → Nonempty (RXs t')) := by
  intro K B f T w Z Wt p0 t S' N h
  let ix : w.C.Tup ≃ w.I.ι := by
    with_unfolding_all exact (Equiv.refl w.C.Tup :)
  have transported := GlobalTheory.T.exists_adelicRowsDivision_over_replacedLaterStages
    B w.C Z (refUp Z S' N h) w.px w.I t.hX T Wt ix p0
    (by with_unfolding_all exact (t.r :))
  rcases transported with
    ⟨⟨z', hold', Y', Z'', tup'⟩, hz, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
  subst hz
  let r' : RowsAre (w.st (SRe.upL Z S' N h)) w.I t.hX T Wt (Equiv.refl _) (Tr.baseLevelRowSideTransport (refUp Z S' N h) p0) :=
    ⟨Mv.cpDat (refUp Z S' N h).to (refUp Z S' N h).same t.r.z, hold', Y', Z'', tup'⟩
  have eW1 := Mv.forcedContentPlaces_eq_transport_sameFiniteGroup (refUp Z S' N h).to (refUp Z S' N h).same t.r.z (F0K K.s (w.D (SRe.upL Z S' N h)))
  let t' : RowsT K w (SRe.upL Z S' N h) Wt (Tr.baseLevelRowSideTransport (refUp Z S' N h) p0) :=
    { hX := t.hX
      r := r'
      exAt := Mv.cp_exAt _ _ _ t.exAt
      inGeo := Mv.cp_inGeo _ _ _ t.inGeo
      grpAt := grpAt_up S' N h t.grpAt
      grp := t.grp
      mu := muIsW_up S' N h t.mu
      exact := (@Eq.trans (Set (@Rows.Places.Pl B.LL B.instLL B.places)) Wt (@Dat.W1 (@ColW.st B f T w Z) (@ColW.px B f T w) (@ColW.I B f T w) (@RowsT.hX B f T K w Z Wt p0 t) T Wt (@RowsAre.z (@ColW.st B f T w Z) (@ColW.px B f T w) (@ColW.I B f T w) (@RowsT.hX B f T K w Z Wt p0 t) T Wt (Equiv.refl (@Cols0.Tup (@ColW.st B f T w Z).B.toPre (@Cols.toCols0 (@ColW.st B f T w Z).B (@ColW.st B f T w Z).C))) p0 (@RowsT.r B f T K w Z Wt p0 t)) (F0K K.s (@ColW.D B f T w Z))) (@Dat.W1 (@Late.st B (@ColW.C B f T w) (@Refill.to B (@ColW.C B f T w) Z (@refUp B f T w Z S' N h))) (@ColW.px B f T w) (@ColW.I B f T w) (@RowsT.hX B f T K w Z Wt p0 t) T Wt (@Mv.cpDat B (@ColW.C B f T w) Z (@Refill.to B (@ColW.C B f T w) Z (@refUp B f T w Z S' N h)) (@ColW.px B f T w) (@ColW.I B f T w) (@RowsT.hX B f T K w Z Wt p0 t) T Wt (@Refill.same B (@ColW.C B f T w) Z (@refUp B f T w Z S' N h)) (@RowsAre.z (@ColW.st B f T w Z) (@ColW.px B f T w) (@ColW.I B f T w) (@RowsT.hX B f T K w Z Wt p0 t) T Wt (Equiv.refl (@Cols0.Tup (@ColW.st B f T w Z).B.toPre (@Cols.toCols0 (@ColW.st B f T w Z).B (@ColW.st B f T w Z).C))) p0 (@RowsT.r B f T K w Z Wt p0 t))) (F0K K.s (@ColW.D B f T w (@SRe.upL B (@ColW.C B f T w) Z S' N h)))) (@RowsT.exact B f T K w Z Wt p0 t) (@Eq.symm (Set (@Rows.Places.Pl (@Late.st B (@ColW.C B f T w) (@Refill.to B (@ColW.C B f T w) Z (@refUp B f T w Z S' N h))).B.LL (@Late.st B (@ColW.C B f T w) (@Refill.to B (@ColW.C B f T w) Z (@refUp B f T w Z S' N h))).B.instLL (@Late.st B (@ColW.C B f T w) (@Refill.to B (@ColW.C B f T w) Z (@refUp B f T w Z S' N h))).B.places)) (@Dat.W1 (@Late.st B (@ColW.C B f T w) (@Refill.to B (@ColW.C B f T w) Z (@refUp B f T w Z S' N h))) (@ColW.px B f T w) (@ColW.I B f T w) (@RowsT.hX B f T K w Z Wt p0 t) T Wt (@Mv.cpDat B (@ColW.C B f T w) Z (@Refill.to B (@ColW.C B f T w) Z (@refUp B f T w Z S' N h)) (@ColW.px B f T w) (@ColW.I B f T w) (@RowsT.hX B f T K w Z Wt p0 t) T Wt (@Refill.same B (@ColW.C B f T w) Z (@refUp B f T w Z S' N h)) (@RowsAre.z (@ColW.st B f T w Z) (@ColW.px B f T w) (@ColW.I B f T w) (@RowsT.hX B f T K w Z Wt p0 t) T Wt (Equiv.refl (@Cols0.Tup (@ColW.st B f T w Z).B.toPre (@Cols.toCols0 (@ColW.st B f T w Z).B (@ColW.st B f T w Z).C))) p0 (@RowsT.r B f T K w Z Wt p0 t))) (F0K K.s (@ColW.D B f T w (@SRe.upL B (@ColW.C B f T w) Z S' N h)))) (@Dat.W1 (@Late.st B (@ColW.C B f T w) Z) (@ColW.px B f T w) (@ColW.I B f T w) (@RowsT.hX B f T K w Z Wt p0 t) T Wt (@RowsAre.z (@ColW.st B f T w Z) (@ColW.px B f T w) (@ColW.I B f T w) (@RowsT.hX B f T K w Z Wt p0 t) T Wt (Equiv.refl (@Cols0.Tup (@ColW.st B f T w Z).B.toPre (@Cols.toCols0 (@ColW.st B f T w Z).B (@ColW.st B f T w Z).C))) p0 (@RowsT.r B f T K w Z Wt p0 t)) (F0K K.s (@ColW.D B f T w (@SRe.upL B (@ColW.C B f T w) Z S' N h)))) eW1))
      untw := (t.untw)
      emt0 := (t.emt0)
      emt := (t.emt)
      etaF := t.etaF
      rowInt := rowInt_up S' N h t.rowInt
      idx := fun Y hY => idxDefs_up (Z := Z) (S' := S') (N := N) (h := h) Y
        (t.idx (divBack Y) (GlobalTheory.T.liftHermitianLattices_replacedStages_eq K B f T w Z t.hX Wt p0 t.r S' N h r' rfl h13 Y hY)) }
  have hs : RowsSame t t' :=
    ⟨rfl, rfl, HEq.rfl, HEq.rfl, (HEq.refl t.r.z.cG), h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
  refine ⟨t', hs, (by with_unfolding_all exact ((HEq.refl (geoHalf (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (SRe.upL Z S' N h) (iK := t.r.z.alg) t.r.z.geo)) :)), ?_, GlobalTheory.T.rowCompatibilities_transport_replacedStages K B f T w Z Wt p0 t S' N h t' hs⟩
  exact (by with_unfolding_all exact ((congrArg (fun e => ({ (SRe.pkOf t).up Z S' N h with eE := e } : SRe.RowPk (SRe.upL Z S' N h).D)) (eq_of_heq h8)) :))

theorem rows_up : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ), ∃ (p0' : BaseLevelRowSide (w.D (SRe.upL Z S' N h))) (t' : RowsT K w (SRe.upL Z S' N h) Wt p0'), RowsSame t t' ∧ HEq t'.r.z.geo (geoHalf (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (SRe.upL Z S' N h) (iK := t.r.z.alg) t.r.z.geo) ∧ SRe.pkOf t' = (SRe.pkOf t).up Z S' N h ∧ (Nonempty (RXs t) → Nonempty (RXs t')) := fun K B f T w Z Wt p0 t S' N h =>
  Exists.elim (rows_up_at K B f T w Z Wt p0 t S' N h) fun t' ht' =>
    ⟨Tr.baseLevelRowSideTransport (refUp Z S' N h) p0, t', ht'⟩

end GlobalTheory.Mem.R3.Rw.Up
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicRowsDivisionTransportSpectralStageLatticesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

theorem _root_.GlobalTheory.T.adelicRowsDivision_transport_spectralStage_lattices : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ), ∃ (p0' : BaseLevelRowSide (w.D (SRe.upL Z S' N h))) (t' : RowsT K w (SRe.upL Z S' N h) Wt p0'), RowsSame t t' ∧ HEq t'.r.z.geo (geoHalf (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (SRe.upL Z S' N h) (iK := t.r.z.alg) t.r.z.geo) ∧ SRe.pkOf t' = (SRe.pkOf t).up Z S' N h ∧ (Nonempty (RXs t) → Nonempty (RXs t')) := by
  intro K B f T w Z Wt p0 t S' N h
  exact GlobalTheory.Mem.R3.Rw.Up.rows_up K B f T w Z Wt p0 t S' N h
end
end
