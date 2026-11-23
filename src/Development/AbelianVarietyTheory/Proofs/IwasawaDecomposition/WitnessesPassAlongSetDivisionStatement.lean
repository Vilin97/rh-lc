module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnLocalDataTransportDivision
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColsReTo0S
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnLocalDataTransportDivision
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisionLocalDataPreservedDivisionLatticeChangeStatement
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DsigEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InstBack
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaAutomorphicWeilDataPreservedDivisionLatticeStatement
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConcreteSplitPrimeAutomorphicDataDivisionLattice

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Db GlobalTheory.Mem.Top.Bl.WitTr NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Top.Bl.WitTr
open Formalism.MainNotions.G Formalism.UG Formalism.L2.Forms Formalism.L2.G
attribute [local instance] Formalism.BasicNotions.factResChar

section Gen

variable {D : D7} (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ) {X : Formalism.L2.Herm.Herm0 D}



def cmpInS (I : Cmp.CmpIn D X) : Cmp.CmpIn (setDiv D N h) (DivTr.herm0S N h X) := { I with }



theorem cmpHyp0P_setDiv {T : ∀ u : D.what₂.Word, Forms0 D u} {Gt : GatTies D} {I : Cmp.CmpIn D X} (H : CmpHyp0P T Gt I) :
    CmpHyp0P (D := setDiv D N h) (fun u => DivTr.forms0S N h (T u)) (gatTr N h Gt) (cmpInS N h I) :=
  ⟨H.ex, H.evInj, H.ptEx, H.ptAll, H.chi, H.latM⟩

theorem stdB_setDiv {B : GL (Fin D.R.k) D.host.E} (hB : Cmp.StdB D B) : Cmp.StdB (setDiv D N h) B := hB



theorem cmpHyp_setDiv {T : ∀ u : D.what₂.Word, Forms0 D u} {Gt : GatTies D} {I : Cmp.CmpIn D X} (H : Cmp.CmpHyp T Gt I) :
    Cmp.CmpHyp (D := setDiv D N h) (fun u => DivTr.forms0S N h (T u)) (gatTr N h Gt) (cmpInS N h I) :=
  ⟨H.ex, H.uniq, H.pos, H.chi, H.li, H.latM⟩



theorem latCmpC_setDiv {T : ∀ u : D.what₂.Word, Forms0 D u} {Gt : GatTies D} {I : Cmp.CmpIn D X} (H : Cmp.CmpHyp T Gt I) :
    cmpTr N h (Cmp.latCmpC T Gt I H) =
      Cmp.latCmpC (D := setDiv D N h) (fun u => DivTr.forms0S N h (T u)) (gatTr N h Gt) (cmpInS N h I) (cmpHyp_setDiv N h H) := rfl



theorem sigma_setDiv {T : ∀ u : D.what₂.Word, Forms0 D u} {Gt : GatTies D} {I : Cmp.CmpIn D X} (H : Cmp.CmpHyp T Gt I)
    (H0 : Formalism.L2.Herm.Herm0 D) :
    (⟨setDiv D N h, gatTr N h Gt, cmpTr N h (Cmp.latCmpC T Gt I H), DivTr.herm0S N h H0, fun u => DivTr.forms0S N h (T u)⟩ :
      Σ D : D7, GatTies D × LatCmp D × Formalism.L2.Herm.Herm0 D × ∀ u, Forms0 D u) =
    ⟨setDiv D N h, gatTr N h Gt,
      Cmp.latCmpC (D := setDiv D N h) (fun u => DivTr.forms0S N h (T u)) (gatTr N h Gt) (cmpInS N h I) (cmpHyp_setDiv N h H),
      DivTr.herm0S N h H0, fun u => DivTr.forms0S N h (T u)⟩ := by
  rw [latCmpC_setDiv]

end Gen

attribute [local instance_reducible] tauRec hP frobSet lamRec packC locPackC recG gatTiesG extRec embRec cmpInC hermitianLevelZeroOfRecursion levTieG gatRecP_lev gatRec_lev gatRec_pos
  DivTr.herm0S DivTr.forms0S DivTr.atTTS cmpInS LocPack.posOK



theorem isRecG_setDiv : ∀ (sc : Scale) (D : D7) (Gt : GatTies D) (c : LatCmp D) (H : Formalism.L2.Herm.Herm0 D)
    (F : ∀ u, Formalism.L2.Forms.Forms0 D u) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ),
    IsRecG sc D Gt c H F → IsRecG sc (setDiv D N h) (gatTr N h Gt) (cmpTr N h c) (DivTr.herm0S N h H)
      (fun u => DivTr.forms0S N h (F u)) := by
  intro sc D Gt c H F N h hR
  obtain ⟨D0, Lc, I, ψ, hd, H0, hL, T, B, hBs, hB, iK, lam, hK, hPos, CH, eq⟩ := hR
  cases eq
  refine IsRecG.intro (setDiv D0 N h) Lc I ?a1 ?a2 ?a3 ?a4 ?a5 B ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 ?a13
  case a1 => with_reducible_and_instances exact ψ
  case a2 => with_reducible_and_instances exact hd
  case a3 => with_reducible_and_instances exact DivTr.herm0S N h H0
  case a4 => with_reducible_and_instances exact hL
  case a5 => with_reducible_and_instances exact fun u => DivTr.forms0S N h (T u)
  case a6 => with_reducible_and_instances exact stdB_setDiv N h hBs
  case a7 => with_reducible_and_instances exact hB
  case a8 => with_reducible_and_instances exact iK
  case a9 => with_reducible_and_instances exact lam
  case a10 => with_reducible_and_instances exact hK
  case a11 => with_reducible_and_instances exact hPos
  case a12 => with_reducible_and_instances exact cmpHyp0P_setDiv N h CH
  case a13 =>
    with_reducible_and_instances refine Eq.trans (sigma_setDiv N h _ H0) ?_
    with_reducible_and_instances exact Eq.refl _

end GlobalTheory.Mem.Top.Bl.WitTr
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConcreteSplitPrimeAutomorphicDataDivisionLatticeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Db GlobalTheory.Mem.Top.Bl.WitTr NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.concreteSplitPrimeAutomorphicData_divisionLatticeChange : ∀ (sc : Scale) (D : D7) (Gt : GatTies D) (c : LatCmp D) (H : Formalism.L2.Herm.Herm0 D) (F : ∀ u, Formalism.L2.Forms.Forms0 D u) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ), IsRecG sc D Gt c H F → IsRecG sc (setDiv D N h) (gatTr N h Gt) (cmpTr N h c) (DivTr.herm0S N h H) (fun u => DivTr.forms0S N h (F u)) := by
  first | exact @GlobalTheory.Mem.Top.Bl.WitTr.isRecG_setDiv | exact GlobalTheory.Mem.Top.Bl.WitTr.isRecG_setDiv | (intros; apply GlobalTheory.Mem.Top.Bl.WitTr.isRecG_setDiv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTwistsThetaLatticesPreservedDivisionChange

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Db GlobalTheory.Mem.Top.Bl.WitTr NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Top.Bl.WitTr



theorem goodO_setDiv : ∀ (D : D7) (nch : NChoice D) (xd : ThData D) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ), GoodO D nch xd → GoodO (setDiv D N h) (nchTr N h nch) (xdTr N h xd) := by
  intro D nch xd N h hg
  obtain ⟨⟨⟨E, N0, S⟩, hE, hA, hC⟩, hsep⟩ := hg
  subst hE
  exact ⟨⟨⟨{ (twEOf xd) with }, N0, S⟩, rfl, hA, hC⟩, hsep⟩

end GlobalTheory.Mem.Top.Bl.WitTr

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTwistsThetaLatticesPreservedDivisionChangeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Db GlobalTheory.Mem.Top.Bl.WitTr NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.goodTwistsThetaLattices_preserved_divisionChange : ∀ (D : D7) (nch : NChoice D) (xd : ThData D) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ), GoodO D nch xd → GoodO (setDiv D N h) (nchTr N h nch) (xdTr N h xd) := by
  first | exact @GlobalTheory.Mem.Top.Bl.WitTr.goodO_setDiv | exact GlobalTheory.Mem.Top.Bl.WitTr.goodO_setDiv | (intros; apply GlobalTheory.Mem.Top.Bl.WitTr.goodO_setDiv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelTaylorSeriesPreservedDivisionLatticeChange

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Db GlobalTheory.Mem.Top.Bl.WitTr NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl.WitTr



theorem kerT_entC_setDiv : ∀ {B : Base} {f : Fr B.toPre} {T : TwDat B}
    (w : ColW B f T) (Z : w.Lt) (t : ColT w Z) (Y : DivX (w.D Z)) (Gy : G.LatInst (w.D Z))
    (ker : KerFam (w.D Z) t.Gt t.cmp (w.tw Z) Gy) (k : KerT t Y Gy ker)
    (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ),
    EntC k → ∃ k' : KerT (DivTr.colTTr w Z N h t) (DivTr.divTrZ w Z N h Y)
      (DivTr.latTrZ w Z N h Gy) (DivTr.kerTr w Z N h ker), EntC k' := by
  intro B f T w Z t Y Gy ker k N h hE
  exact ⟨DivTr.ktTr w Z N h k, DivTr.entC_tr w Z N h k hE⟩

end GlobalTheory.Mem.Top.Bl.WitTr
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelTaylorSeriesPreservedDivisionLatticeChangeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Db GlobalTheory.Mem.Top.Bl.WitTr NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.kernelTaylorSeries_preserved_divisionLatticeChange :
    ∀ {B : Base} {f : Fr B.toPre} {T : TwDat B}
    (w : ColW B f T) (Z : w.Lt) (t : ColT w Z) (Y : DivX (w.D Z)) (Gy : G.LatInst (w.D Z))
    (ker : KerFam (w.D Z) t.Gt t.cmp (w.tw Z) Gy) (k : KerT t Y Gy ker)
    (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ),
    EntC k → ∃ k' : KerT (DivTr.colTTr w Z N h t) (DivTr.divTrZ w Z N h Y)
      (DivTr.latTrZ w Z N h Gy) (DivTr.kerTr w Z N h ker), EntC k' :=
  @GlobalTheory.Mem.Top.Bl.WitTr.kerT_entC_setDiv
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WitnessesPassAlongSetDivision

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Top.Bl

open GlobalTheory.Mem.Db GlobalTheory.Mem.Top.Bl.WitTr



theorem witMv_of_positionMv : ∀ 𝒮 : Slots, PositionMv 𝒮 → WitMv 𝒮 := by
  intro 𝒮 hS K B f T w Z O x N h hE
  have hR := GlobalTheory.T.concreteSplitPrimeAutomorphicData_divisionLatticeChange K.s (w.D Z) x.col.Gt x.col.cmp x.col.g.herm x.col.g.forms N h x.col.isRec
  let col := columnLocalDataTransportDivision w Z N h x.col hR
  obtain ⟨k, hk⟩ := GlobalTheory.T.kernelTaylorSeries_preserved_divisionLatticeChange w Z x.col.toColT O.X O.Gy x.ker0 x.ker N h hE
  let n := nchTTr w Z N h x.n
  obtain ⟨dv⟩ := GlobalTheory.T.divisionLocalData_preserved_divisionLatticeChange w Z x.n O.X N h x.div
  obtain ⟨th⟩ := GlobalTheory.T.thetaAutomorphicWeilData_preserved_divisionLatticeChange w Z x.n O.th N h x.th
  obtain ⟨t, hobj, ⟨rx⟩, ⟨nx⟩, ⟨sx⟩, ⟨ox⟩⟩ := hS K B f T w Z O x N h (O.tr N h) rfl col n
  have hker : (⟨(O.tr N h).gatT, (O.tr N h).cmp, (O.tr N h).tw, (O.tr N h).ker⟩ : Σ (Gt : GatTies (w.D (setDivZ Z N h)))
      (cmp : LatCmp (w.D (setDivZ Z N h))) (tw : TwForms (w.D (setDivZ Z N h))), KerFam (w.D (setDivZ Z N h)) Gt cmp tw (O.tr N h).Gy) =
      ⟨col.Gt, col.cmp, w.tw (setDivZ Z N h), kerTr w Z N h x.ker0⟩ := by
    have e := congrArg (fun s : Σ (Gt : GatTies (w.D Z)) (cmp : LatCmp (w.D Z)) (tw : TwForms (w.D Z)), KerFam (w.D Z) Gt cmp tw O.Gy =>
      (⟨gatTr (D := w.D Z) N h s.1, cmpTr (D := w.D Z) N h s.2.1, twTr (D := w.D Z) N h s.2.2.1,
        fun u v g => { s.2.2.2 u v g with }⟩ : Σ (Gt : GatTies (w.D (setDivZ Z N h))) (cmp : LatCmp (w.D (setDivZ Z N h)))
          (tw : TwForms (w.D (setDivZ Z N h))), KerFam (w.D (setDivZ Z N h)) Gt cmp tw (O.tr N h).Gy)) x.ker_eq
    exact e
  have herr : (O.tr N h).errX = Formalism.L2.Herm.toErrXS col.full.1 := by
    show errTr (D := w.D Z) N h O.errX = _
    rw [x.errX]; rfl
  refine ⟨{
      isOver := x.isOver
      forced := x.forced
      Wt := x.Wt
      pin := x.pin
      coh := x.coh
      vol := x.vol
      col := col
      what₂ := t
      rx := rx
      lev := x.lev
      errX := herr
      n := n
      nx := nx
      sx := sx
      ker0 := kerTr w Z N h x.ker0
      ker_eq := hker
      ker := k
      div := dv
      th := th
      obj := hobj
      ox := ox
      real := { x.real with }
      dsig_eq := x.dsig_eq
      gauge := x.gauge
      good := GlobalTheory.T.goodTwistsThetaLattices_preserved_divisionChange (w.D Z) O.nch O.xd N h x.good }, hk⟩

end GlobalTheory.Mem.Top.Bl

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WitnessesPassAlongSetDivisionStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.witnesses_pass_along_set_division : ∀ 𝒮 : Slots, PositionMv 𝒮 → WitMv 𝒮 := by
  first | exact @GlobalTheory.Mem.Top.Bl.witMv_of_positionMv | exact GlobalTheory.Mem.Top.Bl.witMv_of_positionMv | (intros; apply GlobalTheory.Mem.Top.Bl.witMv_of_positionMv <;> assumption)
end
end
