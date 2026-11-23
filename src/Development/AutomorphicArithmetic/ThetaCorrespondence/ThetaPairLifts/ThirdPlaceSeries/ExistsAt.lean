module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtSame
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SideAAlt
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChoiceSide
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LabConj
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.ExistsCgTrueCharSide
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChoiceSide
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyAllIff
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NdSpec

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr
noncomputable section
namespace GlobalTheory.LayerMove

variable {D : D7} (m : Mv D) {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
section
variable {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {M : Formalism.L2.MtFam D} {C : NChoice D} {tp : TupTied D cf C}
def Mv.ndSpec_alt {big} {L : LocAll (lay0 D)} (x : NdSpec A.pl M C big L.X L.T) : NdSpec (m.sideA_alt A).pl (m.mt M) (m.ch C) big (m.loc L).X (m.loc L).T := @_root_.GlobalTheory.HeightCounting.NdSpec.mk (_) (_) (_) (_) (_) (_) (_)
    (iq := (by with_unfolding_all exact (x.iq :)))
    (iq_alg := (by with_unfolding_all exact (x.iq_alg :)))
    (iq_LL := (by with_unfolding_all exact (x.iq_LL :)))
    (iq_big := (by with_unfolding_all exact (x.iq_big :)))
    (B := @_root_.Formalism.L2.NLocBase.mk (_) (_)
      (Oc := (by with_unfolding_all exact (x.B.Oc :)))
      (ringOc := (by with_unfolding_all exact (x.B.ringOc :)))
      (domOc := (by with_unfolding_all exact (x.B.domOc :)))
      (dvrOc := (by with_unfolding_all exact (x.B.dvrOc :)))
      (ec := (by with_unfolding_all exact (x.B.ec :)))
      (ec_w := (by with_unfolding_all exact (x.B.ec_w :)))
      (V := (by with_unfolding_all exact (x.B.V :)))
      (acgV := (by with_unfolding_all exact (x.B.acgV :)))
      (modV := (by with_unfolding_all exact (x.B.modV :)))
      (modVO := (by with_unfolding_all exact (x.B.modVO :)))
      (towV := (by with_unfolding_all exact (x.B.towV :)))
      (iV := (by with_unfolding_all exact (x.B.iV :)))
      (iV_basis := (by with_unfolding_all exact (x.B.iV_basis :)))
      (Qc := (by with_unfolding_all exact (x.B.Qc :)))
      (hL := (by with_unfolding_all exact (x.B.hL :)))
      (hL_def := (by with_unfolding_all exact (x.B.hL_def :)))
      (hK := (by with_unfolding_all exact (x.B.hK :)))
      (hK_def := (by with_unfolding_all exact (x.B.hK_def :)))
      (split := (by with_unfolding_all exact (x.B.split :)))
      (Qc_over := (by with_unfolding_all exact (x.B.Qc_over :)))
      (Qc_conj := (by with_unfolding_all exact (x.B.Qc_conj :))))
    (Q_eq := (by with_unfolding_all exact (x.Q_eq :)))
    (mx := (by with_unfolding_all exact (x.mx :)))
    (mx_max := (by with_unfolding_all exact (x.mx_max :)))
    (mx_inj := (by with_unfolding_all exact (x.mx_inj :)))
    (mx_all := (by with_unfolding_all exact (x.mx_all :)))
    (phO := (by with_unfolding_all exact (x.phO :)))
    (phK := (by with_unfolding_all exact (x.phK :)))
    (phK_alg := (by with_unfolding_all exact (x.phK_alg :)))
    (phK_emb := (by with_unfolding_all exact (x.phK_emb :)))
    (Psi := (by with_unfolding_all exact (x.Psi :)))
    (Psi_inj := (by with_unfolding_all exact (x.Psi_inj :)))
    (Psi_range := (by with_unfolding_all exact (x.Psi_range :)))
    (Psi_pr := (by with_unfolding_all exact (x.Psi_pr :)))
    (ptX := (by with_unfolding_all exact (x.ptX :)))
    (ptX_hT := (by with_unfolding_all exact (x.ptX_hT :)))
    (iotaC := (by with_unfolding_all exact (x.iotaC :)))
    (iotaC_coh := (by with_unfolding_all exact (x.iotaC_coh :)))
    (Qc_eq := (by with_unfolding_all exact (x.Qc_eq :)))
    (std := (by with_unfolding_all exact (x.std :)))
    (act_hK := (by with_unfolding_all exact (x.act_hK :)))
    (twOf_eq := (by with_unfolding_all exact (x.twOf_eq :)))
    (twSide_eq := (by with_unfolding_all exact (x.twSide_eq :)))
    (psi_eq := (by with_unfolding_all exact (x.psi_eq :)))
    (twO_alg := (by with_unfolding_all exact (x.twO_alg :)))
    (tw_reads := (by with_unfolding_all exact (x.tw_reads :)))
    (heckeLoc_gamma_places := (by with_unfolding_all exact (x.heckeLoc_gamma_places :)))
    (nbr := (by with_unfolding_all exact (x.nbr :)))
    (nbr_ind := (by with_unfolding_all exact (x.nbr_ind :)))
    (self_good := (by with_unfolding_all exact (x.self_good :)))
    (nbr_iq := (by with_unfolding_all exact (x.nbr_iq :)))
    (bj := (by with_unfolding_all exact (x.bj :)))
    (bj_span := (by with_unfolding_all exact (x.bj_span :)))
    (bj_rel := (by with_unfolding_all exact (x.bj_rel :)))
end
section
end
end GlobalTheory.LayerMove
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AutSpec

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr
noncomputable section
namespace GlobalTheory.LayerMove

variable {D : D7} (m : Mv D) {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
section
variable {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {M : Formalism.L2.MtFam D} {C : NChoice D} {tp : TupTied D cf C}
def Mv.autSpec_alt {big} {L : LocAll (lay0 D)} {Sp : NdSpec A.pl M C big L.X L.T} (x : _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tp.tup Sp.iq L.Y L.C) : _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation (m.sideA_alt A) (m.mt M) (m.tp tp).tup (m.ndSpec_alt Sp).iq (m.loc L).Y (m.loc L).C := @_root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
    (iotaQ := (by with_unfolding_all exact (x.iotaQ :)))
    (iotaQC := (by with_unfolding_all exact (x.iotaQC :)))
    (kFbar := (by with_unfolding_all exact (x.kFbar :)))
    (locW := (by with_unfolding_all exact (x.locW :)))
    (satW := (by with_unfolding_all exact (x.satW :)))
    (wdOf := (by with_unfolding_all exact (x.wdOf :)))
    (muC := (by with_unfolding_all exact (x.muC :)))
    (S := (by with_unfolding_all exact (x.S :)))
    (irr := (by with_unfolding_all exact (x.irr :)))
    (inj := (by with_unfolding_all exact (x.inj :)))
    (surj := (by with_unfolding_all exact (x.surj :)))
    (typeV := (by with_unfolding_all exact (x.typeV :)))
    (ptV := (by with_unfolding_all exact (x.ptV :)))
    (emb := (by with_unfolding_all exact (x.emb :)))
end
section
end
end GlobalTheory.LayerMove
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AutomorphyOfMove

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr
noncomputable section
namespace GlobalTheory.LayerMove

variable {D : D7} (m : Mv D) {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
theorem Mv.automorphy_of_move {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} (x : _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL D A.wdT A.au) : _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL m.D (m.sideA_alt A).wdT (m.sideA_alt A).au := (by with_unfolding_all exact (x :))
section
end
section
end
end GlobalTheory.LayerMove
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LabConj

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr
noncomputable section
namespace GlobalTheory.LayerMove

variable {D : D7} (m : Mv D) {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
section
variable {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {M : Formalism.L2.MtFam D} {C : NChoice D} {tp : TupTied D cf C}
theorem Mv.labConj_alt (x : LabConj D A.wdT) : LabConj m.D (m.sideA_alt A).wdT := (by with_unfolding_all exact (x :))
end
section
end
end GlobalTheory.LayerMove
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MMvDmvCg

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem.R3.Tr GlobalTheory.LayerMove
noncomputable section
namespace UpperTheory.One.M

def mvCg_alt (s : _root_.UpperTheory.One.M.TrivialCondition) {D : D7} (m : Mv D) {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE}
    (x : _root_.GlobalTheory.HeightCounting.CGTrueT hL D A.wdT) : _root_.GlobalTheory.HeightCounting.CGTrueT hL m.D (m.sideA_alt A).wdT :=
  @_root_.UpperTheory.One.M.New.cgMk _ _ _ s ((by with_unfolding_all exact (x.e :))) ((by with_unfolding_all exact ((_root_.UpperTheory.One.M.New.cgGood s x) :))) ((by with_unfolding_all exact ((_root_.UpperTheory.One.M.New.cgSurj x) :))) ((by with_unfolding_all exact (x.zero :))) ((by with_unfolding_all exact (x.loc :))) ((by with_unfolding_all exact (x.tw :))) ((by with_unfolding_all exact (x.inf :))) ((by with_unfolding_all exact (x.csd :)))
end UpperTheory.One.M
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PhtOn

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr
noncomputable section
namespace GlobalTheory.LayerMove

variable {D : D7} (m : Mv D) {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
section
variable {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {M : Formalism.L2.MtFam D} {C : NChoice D} {tp : TupTied D cf C}
end
section
variable {cf : CharFrame D} {C : NChoice D} {tp : TupTied D cf C}
theorem Mv.phtOn_alt {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {fr : Formalism.L2.OmFrame D} (x : PhtOn A.wd fr fun _ _ _ _ => True) : PhtOn (m.sideA_alt A).wd (m.omFrame fr) fun _ _ _ _ => True := @_root_.GlobalTheory.HeightCounting.PhtOn.mk (_) (_) (_) (_) (_)
    (card := (by with_unfolding_all exact (x.card :)))
end
end GlobalTheory.LayerMove
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PrimitiveAtLinkedAlt

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr
noncomputable section
namespace GlobalTheory.LayerMove

variable {D : D7} (m : Mv D) {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
theorem Mv.herm_wCell_last_mul_mulVec_eq_of_inWb {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {rep} (x : _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL D rep (fun σ w ↦ (A.wdT.e w) (A.row.locR σ w)) A.row.satR) : _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL m.D rep (fun σ w ↦ ((m.sideA_alt A).wdT.e w) ((m.sideA_alt A).row.locR σ w)) (m.sideA_alt A).row.satR := (by with_unfolding_all exact (x :))
section
end
section
end
end GlobalTheory.LayerMove
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsAt

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr
noncomputable section
namespace GlobalTheory.LayerMove

variable {D : D7} (m : Mv D) {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
section
variable {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {M : Formalism.L2.MtFam D} {C : NChoice D} {tp : TupTied D cf C}
end
section
variable {cf : CharFrame D} {C : NChoice D} {tp : TupTied D cf C}
end
theorem Mv.exists_at_alt {cf : CharFrame D} {C : NChoice D} {tp : TupTied D cf C} (a : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL D cf C tp) :
    ∃ a' : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL m.D (m.cf cf) (m.ch C) (m.tp tp), _root_.GlobalTheory.LayerMove.AtSameAltAlt m a a' := by
  obtain ⟨⟨nb, pack⟩, all, chr_eq, host, frameN, chrN, chrGal, Pq', Pq_over, pq, jE_eq, mt_eq, Pq_eq, hlow, split, ratIn,
    r1, r2, r3, depth⟩ := a
  obtain ⟨D0, cf0, jE, A, cg, au, rep, row, low, Pq, S, hk, eig, θ, Bs, M, C0, tp0, ch, mt, big, L, Sp, Au, ss, eq⟩ := nb
  subst eq
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at pack
  obtain ⟨rfl, rfl, rfl⟩ := pack
  have hmt : mtL L M = all.gal.mt := eq_of_heq mt_eq
  refine ⟨@_root_.GlobalTheory.Mem.Top.Bl.NAtData.mk hL m.D _ _ _
    (⟨@_root_.GlobalTheory.HeightCounting.NormChoiceConstructed.mk hL m.D m.pre.D (m.pre.cf cf0) jE (m.pre.sideA_alt A) ((_root_.UpperTheory.One.M.mvCg_alt trivial) m.pre cg) (m.pre.automorphy_of_move au) rep (m.pre.herm_wCell_last_mul_mulVec_eq_of_inWb row) low Pq S hk eig θ
      (m.pre.sideB_alt Bs) (m.pre.mt M) (m.pre.ch C0) (m.pre.tp tp0) (m.pre.choiceSide_alt ch) (m.pre.mtInput mt) big (m.pre.loc L)
      (m.pre.ndSpec_alt Sp) (m.pre.autSpec_alt Au) ((by with_unfolding_all exact (ss :))) m.withLoc_pre, m.pack_pre tp0⟩)
    ((_root_.UpperTheory.One.M.mvAll_alt trivial) m all)
    ((by with_unfolding_all exact ((congrArg (fun p : Σ c : CharFrame (withLoc L), TupTied (withLoc L) c (chL L C0) =>
      (⟨m.cf p.1, m.tp p.2⟩ : Σ c : CharFrame m.D, TupTied m.D c (m.ch (chL L C0)))) chr_eq) :)))
    (m.host host) ((by with_unfolding_all exact (frameN :))) (m.chrN chrN) (m.chrGal chrGal) ((by with_unfolding_all exact (Pq' :))) ((by with_unfolding_all exact (Pq_over :))) ((by with_unfolding_all exact (pq :))) ((by with_unfolding_all exact (jE_eq :)))
    ((by with_unfolding_all exact ((heq_of_eq (congrArg m.mt hmt)) :))) ((by with_unfolding_all exact (Pq_eq :))) ((by with_unfolding_all exact (hlow :))) (m.oSplit split) ((by with_unfolding_all exact ((m.pre.ratIn ratIn) :))) ((by with_unfolding_all exact (r1 :))) ((by with_unfolding_all exact (r2 :)))
    ((by with_unfolding_all exact (r3 :))) ((by with_unfolding_all exact ((m.pre.rowDepth depth) :))), ?_⟩
  refine ⟨HEq.rfl, (by with_unfolding_all exact ((HEq.refl Pq') :)), (by with_unfolding_all exact ((HEq.refl (ratL L S)) :)), (by with_unfolding_all exact ((HEq.refl hk) :)), (by with_unfolding_all exact ((HEq.refl rep) :)), (by with_unfolding_all exact ((HEq.refl eig) :)), ?_⟩
  rintro ⟨h1, h2, fr, h3, h4⟩
  exact ⟨(by with_unfolding_all exact ((m.pre.labConj_alt (A := A) h1) :)), (by with_unfolding_all exact (h2 :)), (by with_unfolding_all exact ((m.pre.omFrame fr) :)), (by with_unfolding_all exact (h3 :)), (by with_unfolding_all exact ((m.pre.phtOn_alt (A := A) h4) :))⟩
end GlobalTheory.LayerMove
end
end
end
end
