module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GKeyFin
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExtensionWithAtProperty
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartSel
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PtOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingsFormsExistList
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwArgs
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowRatW
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TwistedDataOffBaseLevel
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowNumAt
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EventuallyConstructedPointHostSizeNumerical
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SetAtOfSizeAt
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealPins
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
import Mathlib.Tactic.NormNum.Parity
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightOnePlacesFiniteOfWitness

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowEListPinPt

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.LiteralAutomorphy.PinPt

open Formalism.L2.Host Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev

theorem listPin_twArgs {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
    {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L} {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7}
    {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC} {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX}
    {t : RowsT K w Z Wt ex.p0} (a : GlobalTheory.Mem.R3.TwArgs ex t) {CF bb : ℝ}
    (h : GlobalTheory.HeightCounting.Up.ListPin (w.st Z).toD7 t.r.z.R.toRealDat.toLevCh CF bb) :
    GlobalTheory.HeightCounting.Up.ListPin (w.st Z).toD7 a.x.R.toRealDat.toLevCh CF bb := by
  have e := congrArg (fun s : Σ' (G : Type) (_ : Group G) (_ : Fintype G) (Pl0 I0 T0 : Type)
        (A3 : FamIn3 (w.st Z).toD7.what₂.LL G Pl0 I0 (List ℕ) T0 (w.st Z).toD7.R.m) (C : Formalism.L2.Pj.CoreJ (w.st Z).toD7)
        (_ : Algebra C.Q.c.F (w.st Z).toD7.what₂.LL) (R : RealDat3 (w.st Z).toD7 A3 C.Q.c.F) (_ : Face3 (w.st Z).toD7 A3),
        G0 R.Pg (w.st Z).toD7.R.r ≃* G0g (w.st Z).toD7.nd =>
      match s with
      | ⟨_, _, _, _, _, _, _, _, _, R, _, _⟩ => GlobalTheory.HeightCounting.Up.ListPin (w.st Z).toD7 R.toRealDat.toLevCh CF bb) a.pack
  exact cast e.symm h

end GlobalTheory.Mem.LiteralAutomorphy.PinPt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BwitFrameTwists

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowEx.FrmW

open GlobalTheory.Mem.R3 Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links GlobalTheory.Mem.Col2

variable {K : Ctx} {B : GlobalTheory.Mem.Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L} {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7}
  {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC} {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX}
  {t : RowsT K w Z Wt ex.p0}



theorem frame_of_args (a : TwArgs ex t) (x : TwIn ex) (hx : HEq a.x x) :
    x.R.toRealDat.C = Fr.at (w.st Z) f ∧ TwistPlacesOffPrimeQZero x.R.toRealDat.toLevCh ∧
      ∀ u, ∃ ξ ∈ T.set f, HEq (x.R.toRealDat.toLevCh.xiH u) ξ := by
  obtain rfl := eq_of_heq hx
  have hz := GlobalTheory.RowEx.twisted_data_off_base_level B f T w Z _ _ t.r.z
  have e := congrArg (fun s => match s with
    | ⟨_, _, _, _, _, _, _, _, _, R, _, _⟩ => R.toRealDat.C = Fr.at (w.st Z) f ∧ TwistPlacesOffPrimeQZero R.toRealDat.toLevCh ∧
        ∀ u, ∃ ξ ∈ T.set f, HEq (R.toRealDat.toLevCh.xiH u) ξ) a.pack
  exact e.mpr ⟨hz.2.1, hz.1, fun u => ⟨_, hz.2.2.2 u, HEq.rfl⟩⟩

end GlobalTheory.RowEx.FrmW
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BwitFrameTwists

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem GlobalTheory.RowEx.frame_eq_and_twistPlacesOffPrimeQZero_of_bWit : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (K : Ctx) (q : WPt p.s K) (c : ℝ) (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → b.B.Q.Rl.toRealDat.C = Fr.at (q.w.st q.Z) q.f ∧ TwistPlacesOffPrimeQZero b.B.Q.Rl.toRealDat.toLevCh ∧ ∀ u, ∃ ξ ∈ q.T.set q.f, HEq (b.B.Q.Rl.toRealDat.toLevCh.xiH u) ξ := by
  intro hL p K q c b w
  have h2 := GlobalTheory.RowEx.FrmW.frame_of_args w.a w.x w.ax
  have e := congrArg (fun r : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S => r.B.Q.Rl.toRealDat.C = Fr.at (q.w.st q.Z) q.f ∧ TwistPlacesOffPrimeQZero r.B.Q.Rl.toRealDat.toLevCh ∧
      ∀ u, ∃ ξ ∈ q.T.set q.f, HEq (r.B.Q.Rl.toRealDat.toLevCh.xiH u) ξ) w.y.eq
  exact e.mpr h2
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LeastSplitAuxiliaryPrimeLtScaleBound

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.AtSize

theorem leastSplitAuxiliaryPrime_lt_scaleBound {K : Ctx} {X : Stages} (hO : K.Over X.B.toPre) {C5 c6 Cb : ℝ} (hG : K.Good C5 c6 Cb) :
    ((GlobalTheory.ChiGrid.q0 X.toD7 : ℕ) : ℝ) < K.s.X' := by
  have hOk := hG.ok
  obtain ⟨sp, hT, hY, hA', hV, hz, hB, -⟩ := hO
  obtain ⟨B, Cc, W, V, S, N, Gj⟩ := X
  cases B
  dsimp only at hB
  subst hB
  have hmem := hOk.small.1
  rcases hOk.lev _ hmem with ⟨i, hi⟩ | hlt
  · exact absurd hi (hOk.small.2.2.2.1 i)
  · exact hlt


end GlobalTheory.Mem.AtSize

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EvPSizeRows

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Mem.AtSize

theorem eventually_sizeRows_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) :
    EvP fun _ K => ∀ β : BPt K, β.Is (IsGoodE p.s) → GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows β.O.L := by
  refine EvP.of_ev ⟨1, one_pos, fun eps C8 he _ he52 _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C hStd _ _ => ?_⟩⟩
  obtain ⟨c1, hN⟩ := szRow_numAt eps he he52 C hStd
  refine ⟨c1, fun cD hcD => ?_⟩
  obtain ⟨c2, hN⟩ := hN cD hcD
  refine ⟨c2, fun ch hch => ?_⟩
  obtain ⟨x0, hN⟩ := hN ch hch
  refine ⟨max x0 (max (44 ^ 4) ((8 : ℝ) ^ (4 / eps))), fun K h1 h2 h3 h4 hx β _ => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨hy0, hy44, hy8⟩ := hx
  have hsc : β.O.L.sc = K.s := β.sc
  have hsx : β.O.L.sc.x = K.s.x := by rw [hsc]
  have hse : β.O.L.sc.eps = eps := by rw [hsc, h4]
  have hv : Val C cD ch β.O.L := by
    rw [← h1, ← h2, ← h3]
    exact β.p.pt_val β.val
  obtain ⟨⟨N⟩, -, -⟩ := hN _ _ hse (hy0.trans hsx.ge) hv (GlobalTheory.Plug.hostArith_bpt β)
  obtain ⟨C5, c6, Cb, hG⟩ := β.good
  have hq : ((GlobalTheory.ChiGrid.q0 β.D : ℕ) : ℝ) < β.O.L.sc.X' := by
    rw [hsc]
    exact leastSplitAuxiliaryPrime_lt_scaleBound β.c.isOver hG
  refine GlobalTheory.BigTop.Fun.SetAtModel.sizeRows_of N.params N.parT (N.CnW_eq.trans hStd.1.2.2.2.2.2.2.2.1) N.sizes
    N.win.1.1 N.win.2.1.1 N.win.2.1.2 N.win.2.2.1 N.g_le hq N.ccK_top ?_ (by rw [hsx]; exact hy44)
  rw [hsx, hse]
  have e2 : (8 : ℝ) = ((8 : ℝ) ^ (4 / eps)) ^ (eps / 4) := by
    rw [← Real.rpow_mul (by norm_num), show 4 / eps * (eps / 4) = 1 by field_simp, Real.rpow_one]
  rw [e2]
  exact Real.rpow_le_rpow (by positivity) hy8 (by positivity)
end GlobalTheory.Mem.AtSize
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ListPinRpk

section

@[expose] public section



namespace GlobalTheory.Mem.LiteralAutomorphy.PinPt

open Formalism.BasicNotions GlobalTheory.EX.OB
open Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem listPin_rpk_alt {D : D7} {O : Obj D} {R : _root_.Formalism.L2.RecTAlt O.ex}
    {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R} {x : GlobalTheory.Mem.R3.TwIn O.ex}
    (y : _root_.GlobalTheory.Mem.R3.RealInAlt x R S)
    (r : _root_.GlobalTheory.Mem.Top.Bl.RealPackage R S)
    (hr : r = _root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y) {CF bb : ℝ}
    (h : GlobalTheory.HeightCounting.Up.ListPin D x.R.toRealDat.toLevCh CF bb) :
    GlobalTheory.HeightCounting.Up.ListPin D r.B.Q.Rl.toRealDat.toLevCh CF bb := by
  subst hr
  exact h

end GlobalTheory.Mem.LiteralAutomorphy.PinPt
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowTestSetting

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.PrimIn
theorem rowTest_setting_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (B : _root_.Formalism.IndefR.RealTBAlt Rc P Dcf Spf Zscf S), _root_.Formalism.IndefR.IndefiniteRealisationNormalisation B.Q → (∀ w, (B.Q.Rl.toCx3 B.Q.F).W1 B.Q.F.cr (B.Q.Rl.num B.Q.F 0 0) w → w ∈ B.Q.Rl.twPl) → B.Q.Rl.toRealDat.ExAt → GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows L → GlobalTheory.GLq.ESerTie D → Finite P.T → GlobalTheory.RowClaim.HidaSetting L B.Q.Rl.toRealDat B.Q.F.lv2 := by
  intro D L hT Gi Gl K Y cX ex Rc P Dcf Spf Zscf S B hp _hW hEx hsz hser hfin
  have hC := B.Q.charW
  have hcore := (GlobalTheory.CoreOfWeak.core_of_weak B.Q.Rl B.Q.F hC hEx).1
  exact
    { size := hsz
      eser := hser
      host := B.Q.host
      hF := hp.hF
      core := hcore
      mu_off := hC.tup.mu_off
      mu_used := hC.tup.mu_used
      mu_ne := hC.tup.mu_ne
      mu_conj := hC.tup.mu_conj
      mu_on := hC.tup.mu_on
      grp := hC.base.grp.record
      guard := hp.qGuard
      fin := hfin
      fullY := hC.fullY
      fullX := hC.fullX
      std := B.Q.stdChar
      stdX := B.Q.stdX
      betaX := hp.betaStd.2 }
end GlobalTheory.PrimIn
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EvPSizeRowsDlog

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Mem.LiteralAutomorphy.GridRow
theorem eventually_sizeRows_and_logDeriv_le_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) : EvP fun _ K => ∀ β : BPt K, β.Is (IsGoodE p.s) →
    GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows β.O.L ∧ |β.O.L.logDerivativeAtOne| ≤ K.s.x ^ K.s.eps := by
  refine (_root_.GlobalTheory.Mem.AtSize.eventually_sizeRows_alt hL p).mono fun κ K _ H β hq => ⟨H β hq, ?_⟩
  have h := β.val.dlog
  rw [β.sc] at h
  exact h

theorem rowE_full_grid_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (CF : ℝ) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP) : RowE (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N (GridA CF)) S Γ).s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N (GridA CF)) S Γ)) fun _ D O c b => ∀ t : b.Comparison₂, (b.part t).pt.CompatibilityConditions → ∀ G₀ : GlobalTheory.BigTop.Fun.Grid (b.part t).pt CF, ∃ G : GlobalTheory.BigTop.Fun.Grid (b.part t).pt CF, G.pl.v0 = G₀.pl.v0 ∧ G.pl.w G.pl.v0 = G₀.pl.w G₀.pl.v0 ∧ (∀ a : Fin D.R.m, G.ch.chiH (a.1 + 1) = G₀.ch.chiH (a.1 + 1)) ∧ Full (b.part t).pt.R.toRealDat G := by
  refine (_root_.GlobalTheory.Mem.LiteralAutomorphy.GridRow.eventually_sizeRows_and_logDeriv_le_alt hL (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N (GridA CF)) S Γ)).mono fun κ K hk H β hq c b hl => ?_
  obtain ⟨q, b', ⟨w⟩, he⟩ := hl
  have h2 : (⟨β.D, β.O⟩ : Σ D : D7, Obj D) = ⟨q.w.D q.Z, q.O⟩ :=
    congrArg (fun s : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c => (⟨s.1, s.2.1⟩ : Σ D : D7, Obj D)) he
  have hL' : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows q.O.L ∧ |q.O.L.logDerivativeAtOne| ≤ K.s.x ^ K.s.eps :=
    Eq.ndrec (motive := fun s : Σ D : D7, Obj D => GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows s.2.L ∧ |s.2.L.logDerivativeAtOne| ≤ K.s.x ^ K.s.eps) (H β hq) h2
  have hsc0 : β.O.L.sc = K.s := β.sc
  have hsc : q.O.L.sc = K.s := Eq.ndrec (motive := fun s : Σ D : D7, Obj D => s.2.L.sc = K.s) hsc0 h2
  have hA : GridA CF K q.B q.f q.T := q.x.nx.2.2.down
  have hG : GridAt K.s CF (q.w.st q.Z) q.f (q.T.set q.f) := hA _ _ _ _ _ _
  suffices key : ∀ t : b'.Comparison₂, (b'.part t).pt.CompatibilityConditions → ∀ G₀ : GlobalTheory.BigTop.Fun.Grid (b'.part t).pt CF,
      ∃ G : GlobalTheory.BigTop.Fun.Grid (b'.part t).pt CF, G.pl.v0 = G₀.pl.v0 ∧ G.pl.w G.pl.v0 = G₀.pl.w G₀.pl.v0 ∧
        (∀ a : Fin (q.w.D q.Z).R.m, G.ch.chiH (a.1 + 1) = G₀.ch.chiH (a.1 + 1)) ∧ Full (b'.part t).pt.R.toRealDat G by
    have h1 := congrArg (fun s : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c => ∀ t : s.2.2.Comparison₂, (s.2.2.part t).pt.CompatibilityConditions →
      ∀ G₀ : GlobalTheory.BigTop.Fun.Grid (s.2.2.part t).pt CF, ∃ G : GlobalTheory.BigTop.Fun.Grid (s.2.2.part t).pt CF, G.pl.v0 = G₀.pl.v0 ∧
        G.pl.w G.pl.v0 = G₀.pl.w G₀.pl.v0 ∧ (∀ a : Fin s.1.R.m, G.ch.chiH (a.1 + 1) = G₀.ch.chiH (a.1 + 1)) ∧
        Full (s.2.2.part t).pt.R.toRealDat G) he
    exact cast h1.symm key
  intro t ht G₀
  obtain ⟨hW1, hEx, hfin⟩ := _root_.GlobalTheory.Mem.Top.Bl.weight_one_places_finite_of_witness hL _ K q c b' w hsc
  obtain ⟨hC, hoff, hxi⟩ := _root_.GlobalTheory.RowEx.frame_eq_and_twistPlacesOffPrimeQZero_of_bWit hL _ K q c b' w
  have hset : GlobalTheory.RowClaim.HidaSetting q.O.L b'.B.Q.Rl.toRealDat b'.B.Q.F.lv2 :=
    _root_.GlobalTheory.PrimIn.rowTest_setting_alt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b'.B t.pins hW1 hEx hL'.1 ht.eSer hfin
  have hrec : GlobalTheory.SqTop.Rec q.O.L := ⟨hL'.1, hset.host, hset.hF, by rw [hsc]; exact hL'.2⟩
  have hb : (b'.part t).pt.Z.b = K.s.b := by
    have h0 : (b'.part t).pt.Z.b = q.O.L.sc.b := rfl
    rw [h0, hsc]
  have gen : ∀ z : ℝ, z = K.s.b → ∀ G₀ : GlobalTheory.ChiGrid.GridData b'.B.Q.Rl.toRealDat.toLevCh ⟨1, CF, z⟩,
      ∃ G : GlobalTheory.ChiGrid.GridData b'.B.Q.Rl.toRealDat.toLevCh ⟨1, CF, z⟩, G.pl.v0 = G₀.pl.v0 ∧ G.pl.w G.pl.v0 = G₀.pl.w G₀.pl.v0 ∧
        (∀ a : Fin (q.w.D q.Z).R.m, G.ch.chiH (a.1 + 1) = G₀.ch.chiH (a.1 + 1)) ∧ Full b'.B.Q.Rl.toRealDat G := by
    rintro z rfl G₀
    obtain ⟨G, hk, hF⟩ := @hG q.O.L hsc hrec _ _ _ _ _ _ _ _ _ b'.B.alg b'.B.Q.Rl.toRealDat b'.B.Q.F.lv2 hset hC hoff hxi G₀
    exact ⟨G, congrArg Prod.fst hk, congrArg (fun x => x.2.1) hk, fun a => congrFun (congrArg (fun x => x.2.2) hk) a, hF⟩
  exact gen _ hb G₀

theorem rowE_pinned_grid_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (CF : ℝ) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP) (hN : ∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL CF K B f T w Z Wt p0 t nch n xd c)) : RowE (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N (GridA CF)) S Γ).s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N (GridA CF)) S Γ)) fun _ D O c b => ∀ t : b.Comparison₂, (b.part t).pt.CompatibilityConditions → ∃ G₀ : GlobalTheory.BigTop.Fun.Grid (b.part t).pt CF, GlobalTheory.BigTop.Fun.FieldHas G₀ (Formalism.L2.Host.embLL0 D) ∧ GlobalTheory.LamTie.IsLamTieFull D.ntw (GlobalTheory.BigTop.Fun.lamOf G₀) := by
  refine RowE.of_all fun κ K β c b _ _ hl => ?_
  obtain ⟨q, b', ⟨w⟩, he⟩ := hl
  have hsc : β.O.L.sc = K.s := β.sc
  have hsc' : q.O.L.sc = K.s := by
    have := congrArg (fun s : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c => s.2.1.L.sc) he
    exact this.symm.trans hsc
  have e := congrArg (fun s : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c => ∀ t : s.2.2.Comparison₂, (s.2.2.part t).pt.CompatibilityConditions →
    ∃ G₀ : GlobalTheory.BigTop.Fun.Grid (s.2.2.part t).pt CF, GlobalTheory.BigTop.Fun.FieldHas G₀ (Formalism.L2.Host.embLL0 s.1) ∧
      GlobalTheory.LamTie.IsLamTieFull s.1.ntw (GlobalTheory.BigTop.Fun.lamOf G₀)) he
  refine cast e.symm ?_
  intro t _
  obtain ⟨nl⟩ := hN _ _ _ _ _ _ _ _ _ _ _ _ _ q.x.nx.2.1
  have hp : GlobalTheory.HeightCounting.Up.ListPin (q.w.st q.Z).toD7 q.x.what₂.r.z.R.toRealDat.toLevCh CF K.s.b := nl.2.down
  have h1 := GlobalTheory.Mem.LiteralAutomorphy.PinPt.listPin_twArgs w.a hp
  rw [eq_of_heq w.ax] at h1
  have h2 := _root_.GlobalTheory.Mem.LiteralAutomorphy.PinPt.listPin_rpk_alt w.y.y (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b') w.y.eq h1
  rw [← hsc'] at h2
  exact h2
end GlobalTheory.Mem.LiteralAutomorphy.GridRow
end
end
end
end
