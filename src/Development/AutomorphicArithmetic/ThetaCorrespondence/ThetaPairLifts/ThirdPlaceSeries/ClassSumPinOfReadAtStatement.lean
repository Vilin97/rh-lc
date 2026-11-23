module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartSel
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PtOf
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumPin
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
public import Formalism.LocalToGlobal.IndefiniteReal.WeakCharacterisationWithError
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.PtEquivApply
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeUnderScaleOfGeneral

-- Source module: Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumOfPin

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BigTop

namespace GlobalTheory.ExportPin.Model

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem theta_cast (j : ℕ) (μ ν : D.what₂.Tup) (h : μ = ν) (x : D.what₂.MtL μ j) :
    D.what₂.thetaP ν j (D.what₂.jMt ν j (h ▸ x)) = D.what₂.thetaP μ j (D.what₂.jMt μ j x) := by
  subst h; rfl



end GlobalTheory.ExportPin.Model
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassSumDivisibilityBundle

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BigTop

namespace GlobalTheory.ClassSumPinLink

open Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}




theorem classSumPin_of_read (p : PtAt ex Csz) (Yr : R3.Read (A3 := p.P.A3) p.R.toRealDat p.F.lv2 ex.p0)
    (hjW : ∀ (i : Fin D.R.m) (v : Fin ((p.P.A3.indefDown p.P.S0).dW i) → D.what₂.LL)
      (y : Fin (Module.finrank D.what₂.LL (p.R.toRealDat.WL p.F.lv2 false i)) → D.what₂.LL), HEq v y →
      Yr.mj.eW i (p.P.I.jW i v) = (p.R.FW i).j (sg0 D p.P.A3.A) (jDL p.R p.F.lv2 i y))
    (hth : GlobalTheory.HeightCounting.EMtTheta Yr p.nexp ex.nch)
    (hD : DivRows3 D p.P.A3 p.P.P0 p.P.ψ0 p.P.Ps p.P.ψs p.P.Zs p.P.S0 p.P.S1 ex.p0 p.P.C p.P.NuC p.P.I) :
    GlobalTheory.ExportPin.ClassSumPin p := by
  intro w i h1 h2 t ht hw c x hx hxT y hy n a f hsum
  subst hx
  apply hth w i hw _ hxT n a f
  rw [hsum, GlobalTheory.ExportPin.Model.theta_cast _ _ _ ht, hD.thTheta, hjW i _ y hy]

end GlobalTheory.ClassSumPinLink

namespace GlobalTheory.ClassSumPinLink

open Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX

section Pack

variable {D : D7} {O : Obj D}




end Pack

end GlobalTheory.ClassSumPinLink

namespace GlobalTheory.ClassSumPinLink

open Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX




theorem eMtTheta_of_pack {D : D7} {nch : NChoice D} {X0 : BaseLevelRowSide D} {G G' : Type} {g : Group G} {g' : Group G'} {fi : Fintype G}
    {fi' : Fintype G'} {Pl0 I0 T Pl0' I0' T' : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {A3' : FamIn3 D.what₂.LL G' Pl0' I0' (List ℕ) T' D.R.m}
    {C C' : CoreJ D} {al : Algebra C.Q.c.F D.what₂.LL} {al' : Algebra C'.Q.c.F D.what₂.LL} {R : RealDat3 D A3 C.Q.c.F}
    {R' : RealDat3 D A3' C'.Q.c.F} {F : Face3 D A3} {F' : Face3 D A3'} {kap : ℝ} {lam : type_of% R'.lam3} {err : type_of% R'.err0}
    {Dc : ∀ Zs : DefSub A3'.fam3.amb3, DefCols (A3'.side3 F'.P1 F'.ψ1 Zs)} {Sp : ∀ Zs, SPer (Dc Zs)}
    {Zsc : DefSub A3'.fam3.amb3 → IndefScale A3'.fam3.base3}
    {cG : G0 R.Pg D.R.r ≃* G0g D.nd} {cG' : G0 R'.Pg D.R.r ≃* G0g D.nd}
    {cG'' : G0 ((R'.updS kap lam).withErr err).Pg D.R.r ≃* G0g D.nd}
    (pack : (⟨G, g, fi, Pl0, I0, T, A3, C, al, R, F, cG⟩ :
      Σ' (G : Type) (_ : Group G) (_ : Fintype G) (Pl0 I0 T0 : Type)
        (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (C : CoreJ D)
        (_ : Algebra C.Q.c.F D.what₂.LL) (R : RealDat3 D A3 C.Q.c.F) (_ : Face3 D A3),
        G0 R.Pg D.R.r ≃* G0g D.nd) =
      ⟨G', g', fi', Pl0', I0', T', A3', C', al', (R'.updS kap lam).withErr err, R3.reFace F' Dc Sp Zsc, cG''⟩)
    (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (Y' : R3.Read (A3 := A3') R'.toRealDat F'.lv2 X0)
    (hW : HEq Y.mj.eW Y'.mj.eW) {S S' : RatDat D.ntw} (hS : S = S')
    (E : NExpRealS R cG S) (E' : NExpRealS R' cG' S') (hF : HEq E.eF E'.eF) (hi : HEq E.fi E'.fi)
    (h : GlobalTheory.HeightCounting.EMtTheta Y' E' nch) : GlobalTheory.HeightCounting.EMtTheta Y E nch := by
  cases pack
  cases hS
  intro w i hw x hx n a f hs
  have e1 : E.eF = E'.eF := eq_of_heq hF
  have e2 : E.fi = E'.fi := eq_of_heq hi
  have e3 : Y.mj.eW = Y'.mj.eW := eq_of_heq hW
  rw [e2, e3] at hs
  rw [e1]
  exact h w i hw x hx n a f hs


end GlobalTheory.ClassSumPinLink

namespace GlobalTheory.ClassSumPinLink


end GlobalTheory.ClassSumPinLink
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ClassSumPinOfReadAt

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BigTop
namespace GlobalTheory.ClassSumPinLink
open Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
end GlobalTheory.ClassSumPinLink
namespace GlobalTheory.ClassSumPinLink
open Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX
section Pack
variable {D : D7} {O : Obj D}


def ReadAtAlt {R : _root_.Formalism.L2.RecTAlt O.ex} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R} (k : _root_.GlobalTheory.Mem.Top.Bl.RealPackage R S) : Prop :=
  ∃ Yr : R3.Read (A3 := k.P.A3) k.B.Q.Rl.toRealDat
      (⟨k.P.P0, k.P.ψ0, k.P.Ps, k.P.ψs, k.Dc, k.Sp, k.Zsc⟩ : Face3 D k.P.A3).lv2 O.ex.p0,
    (∀ (i : Fin D.R.m) (v : Fin ((k.P.A3.indefDown k.P.S0).dW i) → D.what₂.LL)
      (y : Fin (Module.finrank D.what₂.LL (k.B.Q.Rl.toRealDat.WL
        (⟨k.P.P0, k.P.ψ0, k.P.Ps, k.P.ψs, k.Dc, k.Sp, k.Zsc⟩ : Face3 D k.P.A3).lv2 false i)) → D.what₂.LL),
      HEq v y → Yr.mj.eW i (k.P.I.jW i v) = (k.B.Q.Rl.FW i).j (sg0 D k.P.A3.A)
        (jDL k.B.Q.Rl (⟨k.P.P0, k.P.ψ0, k.P.Ps, k.P.ψs, k.Dc, k.Sp, k.Zsc⟩ : Face3 D k.P.A3).lv2 i y)) ∧
    GlobalTheory.HeightCounting.EMtTheta Yr k.B.Q.nexp O.ex.nch


theorem readAt_rpkX_of_eMtTheta {R : _root_.Formalism.L2.RecTAlt O.ex} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R} {x : R3.TwIn O.ex} (y : _root_.GlobalTheory.Mem.R3.RealInAlt x R S)
    (h : GlobalTheory.HeightCounting.EMtTheta x.Y y.nexp O.ex.nch) : _root_.GlobalTheory.ClassSumPinLink.ReadAtAlt (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y) := by
  refine ⟨x.Y, ?_, h⟩
  intro i v z hvz
  obtain rfl := eq_of_heq hvz
  exact x.Z.jW_read i v


theorem classSumPin_of_readAt_of_pDiv {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition D O c) (t : b.Comparison₂) (h : _root_.GlobalTheory.ClassSumPinLink.ReadAtAlt (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b)) (hD : _root_.GlobalTheory.Fc.Ind.DivisorPointSummands D O c (b.part t)) :
    GlobalTheory.ExportPin.ClassSumPin (b.part t).pt := by
  obtain ⟨Yr, h1, h2⟩ := h
  exact classSumPin_of_read (b.part t).pt Yr h1 h2 hD
end Pack
end GlobalTheory.ClassSumPinLink
namespace GlobalTheory.ClassSumPinLink
open Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX


theorem eMtTheta_of_args_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : GlobalTheory.Mem.Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
    {Z : w.Lt} {Wt : Set B.places.Pl} {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L}
    {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC}
    {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX} (t : RowsT K w Z Wt ex.p0) (n : NchT w Z Wt ex.nch) (c : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceCore hL t n)
    (a : R3.TwArgs ex t) (x : R3.TwIn ex) (ax : HEq a.x x) {Sx : RatDat (w.st Z).toD7.ntw} (E : NExpRealS x.R x.cG Sx)
    (hS : HEq Sx (ratDatR (D := (w.st Z).toD7) t.r.z.R t.r.z.cG c.row.kKs c.row.hk))
    (hF : HEq E.eF c.row.nexp.eF) (hi : HEq E.fi c.row.nexp.fi)
    (h : GlobalTheory.HeightCounting.EMtTheta (D := (w.st Z).toD7) t.r.Y c.row.nexp ex.nch) : GlobalTheory.HeightCounting.EMtTheta x.Y E ex.nch := by
  cases ax
  exact eMtTheta_of_pack a.pack a.x.Y t.r.Y a.eW (eq_of_heq hS) E c.row.nexp hF hi h
end GlobalTheory.ClassSumPinLink
namespace GlobalTheory.ClassSumPinLink

theorem pIota_classSumPin_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → ∀ (K : Ctx) (q : WPt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K) (c : ℝ) (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) (_ : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness (p := _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) q b) (t : b.Comparison₂), _root_.GlobalTheory.Fc.Ind.IotaPointSummands _ _ c (b.part t) ∧ (_root_.GlobalTheory.Fc.Ind.DivisorPointSummands _ _ c (b.part t) → GlobalTheory.ExportPin.ClassSumPin (b.part t).pt) := by
  intro hL N S Γ hN K q c b hb t
  refine ⟨?_, fun hD => ?_⟩
  · obtain ⟨sP, sS, -, -, hS⟩ := hb.s
    have key : ∀ S' : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt b.R, S' = sS.toRealSpectralMatching b.R → ∀ x : S'.X.B.I.E, HEq (S'.X.ιE x) x := by
      rintro S' rfl
      exact sP.pin
    exact key b.S hS
  · have hth : GlobalTheory.HeightCounting.EMtTheta hb.x.Y hb.y.y.nexp q.O.ex.nch := by
      obtain ⟨m⟩ := hN _ _ _ _ _ _ _ _ _ _ _ _ _ q.x.nx.2
      exact _root_.GlobalTheory.ClassSumPinLink.eMtTheta_of_args_alt q.x.what₂ q.x.n (_root_.GlobalTheory.Mem.Top.Bl.WPt.core_data_of_point (p := _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) q) hb.a hb.x hb.ax hb.y.y.nexp hb.sx hb.eF hb.fi m.1.th
    have hR : _root_.GlobalTheory.ClassSumPinLink.ReadAtAlt (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b) := by
      rw [hb.y.eq]
      exact _root_.GlobalTheory.ClassSumPinLink.readAt_rpkX_of_eMtTheta hb.y.y hth
    exact _root_.GlobalTheory.ClassSumPinLink.classSumPin_of_readAt_of_pDiv b t hR hD
end GlobalTheory.ClassSumPinLink
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ClassSumPinOfReadAtStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.class_sum_divisibility_of_extensionWithLaw : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → ∀ (K : Ctx) (q : WPt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K) (c : ℝ) (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) (_ : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness (p := _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) q b) (t : b.Comparison₂), _root_.GlobalTheory.Fc.Ind.IotaPointSummands _ _ c (b.part t) ∧ (_root_.GlobalTheory.Fc.Ind.DivisorPointSummands _ _ c (b.part t) → GlobalTheory.ExportPin.ClassSumPin (b.part t).pt) := by
  first | exact @_root_.GlobalTheory.ClassSumPinLink.pIota_classSumPin_alt | exact _root_.GlobalTheory.ClassSumPinLink.pIota_classSumPin_alt | (intros; apply _root_.GlobalTheory.ClassSumPinLink.pIota_classSumPin_alt <;> assumption)
end
end
end
