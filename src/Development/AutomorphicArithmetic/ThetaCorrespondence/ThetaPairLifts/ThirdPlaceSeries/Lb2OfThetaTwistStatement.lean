module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriedThTw
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DofOTw
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExpTh
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovedDataLaterStagesWithNewTwistStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalisedReadingTransportedNewTwistStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftOfMovedTwistStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SeriesAtThetaTwist
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideTw
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinTypRepCast
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodLEq
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
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StateB2OfRationalData

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.HeightCounting.Up
open GlobalTheory.Mem.R3.Tr


section Gen
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {C : Formalism.L2.Pj.CoreJ D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat3 D A3 C.Q.c.F}
  {F : Face3 D A3} {X0 : BaseLevelRowSide D} {Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0} {cG : G0 R.Pg D.R.r ≃* G0g D.nd} {cf : CharFrame D}
  {g : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1}
theorem state_b2_of_rational_data_alt {a : _root_.GlobalTheory.HeightCounting.HeightCountingBaseData hL D cf (repOf Y)} {n : InRat Y cG} {PV : ∀ i : Fin D.R.m, principalLevelFrame.RowPsi (Vc D i) D.R.nV}
    {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host}
    (row : RowSide D) (S : RatDat D.ntw) (hLS : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j))
    (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ)
    (Sb : Finset (PlE D.host)) (PV' : ∀ i : Fin D.R.m, principalLevelFrame.RowPsi (Vc D i) D.R.nV)
    (Pq' : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host)
    (hrow : HEq a.A.row row) (hS : HEq n.S S) (hhL : HEq n.In.hL hLS) (heig : HEq n.In.eig eig) (hθ : HEq n.In.θ θ)
    (hSb : HEq n.In.Sb Sb) (hPV : PV = PV') (hPq : HEq Pq Pq')
    (Bs : SideB D cf row (lowAll D) Pq' S hLS eig θ) (Sb_le : ∀ i, Sb ⊆ D.ntw.S0 i)
    (rootsOfUnityRing_le_wittIntegers : ∀ i, OverSet D (D.ntw.S0 i) (insert (D.ntw.l i) (lowAll D)))
    (lam : ∃ Z : GlobalTheory.LamTie.LamDat D, Z.Ok ∧ Z.Teich ∧ Z.C = cf ∧ Z.q0 = AbsolutelyIrreducibleSpan.q0 D ∧ GlobalTheory.LamTie.IsLamTieFull D.ntw Z)
    (YS : NExpRealS R cG S) (eF : YS.eF = Bs.eF) (fi : ∀ i x, HEq ((YS.fi i).e x) x)
    (ser : SerAt YS g.v₀ Bs.exp PV' cf Pq') (tau : TauTrue Bs.exp)
    (geo : Nonempty (GlobalTheory.GeoTie.ThetaTie YS g.fw D.nth)) : Nonempty (_root_.GlobalTheory.HeightCounting.ModuliPointsData g a n PV Pq) := by
  cases eq_of_heq hrow
  cases eq_of_heq hS
  cases eq_of_heq hhL
  cases eq_of_heq heig
  cases eq_of_heq hθ
  cases eq_of_heq hSb
  cases hPV
  cases eq_of_heq hPq
  exact ⟨⟨⟨⟨Bs, Sb_le, rootsOfUnityRing_le_wittIntegers, lam⟩, YS, eF, fi, ser, tau⟩, geo⟩⟩
end Gen
section Gen2
end Gen2
section MtCopy
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
theorem exists_in_mt_theta_twist_pv_eq (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x) (th : NTh (Dof x).R (Dof x).host (Dof x).what₂ (Dof x).LL0 (Dof x).nd (Dof x).ntw (Dof x).nexp)
    (m : Moved (oTw x (thTw (Dof x) th))) (hm : m.z = datTw x (thTw (Dof x) th)) (hc : m.Copy) (hh : m.Coh)
    (r : ReadPk m (sideTw x (thTw (Dof x) th))) (hp : r.Pin)
    (hj : ∀ μ h i y, HEq (r.Y.IL.jMt μ h i y).1 (x.r.Y.IL.jMt μ h i y).1) :
    ∃ mt : InMt r.Y (cfOf (stTw x _ m hc hh r hp)) w.I.xi (QOf P),
      mt.ad.PV = fun i => (by with_unfolding_all exact ((rowPsi (a := x.o.Z) (oTw x (thTw (Dof x) th)).Z (l.mt.ad.PV ((by with_unfolding_all exact (i :))))) :)) := by
  rcases m with ⟨z⟩
  dsimp only at hm
  subst hm
  refine ⟨{ M := (by with_unfolding_all exact (((thTw (Dof x) th).mt l.mt.M) :))
            ad :=
              { PV := fun i => (by with_unfolding_all exact ((rowPsi (a := x.o.Z) (oTw x (thTw (Dof x) th)).Z (l.mt.ad.PV ((i)))) : _))
                std := (by with_unfolding_all exact (l.mt.ad.std :))
                eW := (by with_unfolding_all exact (l.mt.ad.eW :))
                read := fun μ h i y g => by
                  have e := congrFun (eq_of_heq (hj μ h i y)) ((l.mt.ad.PV i).ψ g)
                  exact Eq.trans ((by with_unfolding_all exact ((l.mt.ad.read μ h i y g) :))) e.symm
                rat := (by with_unfolding_all exact (l.mt.ad.rat :))
                wt := (by with_unfolding_all exact (l.mt.ad.wt :))
                id := (by with_unfolding_all exact (l.mt.ad.id :)) }
            mt := by
              with_unfolding_all exact LiTw.mtIn (thTw (Dof x) th) l.mt.mt }, rfl⟩
end MtCopy
end GlobalTheory.HeightCounting.Up
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Lb2OfThetaTwist

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.HeightCounting.Up
open GlobalTheory.Mem.R3.Tr


variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
theorem lb2_of_theta_twist_alt (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevel hL x) (th : NTh (Dof x).R (Dof x).host (Dof x).what₂ (Dof x).LL0 (Dof x).nd (Dof x).ntw (Dof x).nexp)
    (hT : GlobalTheory.GeoTie.ThetaTie l.b.YS x.m.z.geo.fw th)
    (m : Moved (oTw x (thTw (Dof x) th))) (hm : m.z = datTw x (thTw (Dof x) th)) (hc : m.Copy) (hh : m.Coh)
    (r : ReadPk m (sideTw x (thTw (Dof x) th))) (hp : r.Pin) (l' : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL (stTw x _ m hc hh r hp))
    (h1 : HEq l'.a.A.row ((thTw (Dof x) th).row l.a.A.row)) (h2 : HEq l'.Pq l.Pq)
    (h3 : HEq l'.rat.S ((thTw (Dof x) th).rat l.rat.S)) (h4 : HEq l'.rat.In.Sb l.rat.In.Sb) (h5 : HEq l'.rat.In.hL l.rat.In.hL)
    (h6 : HEq l'.rat.In.eig l.rat.In.eig) (h7 : HEq l'.rat.In.θ l.rat.In.θ)
    (mt : InMt r.Y (cfOf (stTw x _ m hc hh r hp)) w.I.xi (QOf P))
    (hPV : mt.ad.PV = fun i => (by with_unfolding_all exact ((rowPsi (a := x.o.Z) (oTw x (thTw (Dof x) th)).Z (l.mt.ad.PV ((by with_unfolding_all exact (i :))))) :)))
    (hser : Nonempty (SerAt (_root_.GlobalTheory.HeightCounting.Up.ysTh_alt x l th) (datTw x (thTw (Dof x) th)).geo.v₀ (_root_.GlobalTheory.HeightCounting.Up.exponentOfTheta x l th) (_root_.GlobalTheory.HeightCounting.Up.rowPsiOfTheta x l.toLI th)
      (TC.cf w.I w.l (oTw x (thTw (Dof x) th)).Z) l.Pq)) :
    Nonempty (_root_.GlobalTheory.HeightCounting.ModuliPointsData (stTw x _ m hc hh r hp).m.z.geo l'.a l'.rat mt.ad.PV l'.Pq) := by
  rcases m with ⟨z⟩
  dsimp only at hm
  subst hm
  exact hser.elim fun s => _root_.GlobalTheory.HeightCounting.Up.state_b2_of_rational_data_alt ((by with_unfolding_all exact (((thTw (Dof x) th).row l.a.A.row) :))) ((by with_unfolding_all exact (((thTw (Dof x) th).rat l.rat.S) :))) ((by with_unfolding_all exact (l.rat.In.hL :)))
    ((by with_unfolding_all exact (l.rat.In.eig :))) ((by with_unfolding_all exact (l.rat.In.θ :))) ((by with_unfolding_all exact (l.rat.In.Sb :)))
    _ ((by with_unfolding_all exact (l.Pq :)))
    ((by with_unfolding_all exact (h1 :))) ((by with_unfolding_all exact (h3 :))) ((by with_unfolding_all exact (h5 :))) ((by with_unfolding_all exact (h6 :))) ((by with_unfolding_all exact (h7 :))) ((by with_unfolding_all exact (h4 :))) hPV ((by with_unfolding_all exact (h2 :)))
    ((by with_unfolding_all exact ((bsTw l.b.Bs th) :))) ((by with_unfolding_all exact (l.b.Sb_le :))) ((by with_unfolding_all exact (l.b.rootsOfUnityRing_le_wittIntegers :))) ((by with_unfolding_all exact ((lam_thTw th l.b.lam) :)))
    ((by with_unfolding_all exact ((_root_.GlobalTheory.HeightCounting.Up.ysTh_alt x l th) :)))
    ((by with_unfolding_all exact (l.b.eF :))) ((by with_unfolding_all exact (l.b.fi :)))
    ((by with_unfolding_all exact (s :)))
    ((by with_unfolding_all exact (l.b.tau :)))
    ⟨⟨fun i j b => ⟨(by with_unfolding_all exact ((hT.side ((i)) ((j)) b).pt : _)), (by with_unfolding_all exact ((hT.side ((i)) ((j)) b).cover : _)),
      (by with_unfolding_all exact ((hT.side ((i)) ((j)) b).ev_eq : _)), (by with_unfolding_all exact ((hT.side ((i)) ((j)) b).fmUr : _)), (by with_unfolding_all exact ((hT.side ((i)) ((j)) b).hk : _)),
      (by with_unfolding_all exact ((hT.side ((i)) ((j)) b).hk_none : _))⟩, (by with_unfolding_all exact (hT.isUnramified₂ :))⟩⟩
theorem exists_levelB2_twisted_state_of_thetaTie : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevel hL x) (th : NTh (Dof x).R (Dof x).host (Dof x).what₂ (Dof x).LL0 (Dof x).nd (Dof x).ntw (Dof x).nexp), GlobalTheory.GeoTie.ThetaTie l.b.YS x.m.z.geo.fw th → ∃ x' : St P, Nonempty (_root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x') ∧ x'.o = oTw x (thTw (Dof x) th) ∧ HEq x'.m.z.R.toRealDat.toLevCh (GlobalTheory.Mem.R3.Tr.levCh (a := x.o.Z) (oTw x (thTw (Dof x) th)).Z x.m.z.R.toRealDat.toLevCh) := by
  intro hL K B f T w P x l th hT
  let N := thTw (Dof x) th
  obtain ⟨m, hm, hc, hh⟩ := GlobalTheory.T.exists_movedData_laterStagesWithNewTwist x N
  obtain ⟨r, hp, hrep, hj, he⟩ :=
    GlobalTheory.T.exists_normalisedReading_transported_newTwist x N m hm hc hh
  obtain ⟨l', h1, h2, h3, h4, h5, h6, h7⟩ :=
    _root_.GlobalTheory.T.read_package_twist_heq_alt hL x l.toLI N m hm hc hh r hp hrep hj he
  obtain ⟨mt, hPV⟩ := _root_.GlobalTheory.HeightCounting.Up.exists_in_mt_theta_twist_pv_eq x l.toLI th m hm hc hh r hp hj
  refine ⟨stTw x N m hc hh r hp, ?_, rfl, ?_⟩
  · have hser := _root_.GlobalTheory.T.series_at_theta_twist_ys_exp hL x l th
    have hpoints := _root_.GlobalTheory.HeightCounting.Up.lb2_of_theta_twist_alt
      x l th hT m hm hc hh r hp l' h1 h2 h3 h4 h5 h6 h7 mt hPV hser
    exact hpoints.map fun b => { toLI := { l' with mt := mt }, b := b }
  · show HEq m.z.R.toRealDat.toLevCh _
    rw [hm]
    with_unfolding_all
      exact HEq.refl (datTw x N).R.toRealDat.toLevCh
end GlobalTheory.HeightCounting.Up
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Lb2OfThetaTwistStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_levelB2_twist_of_thetaTie : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevel hL x) (th : NTh (Dof x).R (Dof x).host (Dof x).what₂ (Dof x).LL0 (Dof x).nd (Dof x).ntw (Dof x).nexp), GlobalTheory.GeoTie.ThetaTie l.b.YS x.m.z.geo.fw th → ∃ x' : St P, Nonempty (_root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x') ∧ x'.o = oTw x (thTw (Dof x) th) ∧ HEq x'.m.z.R.toRealDat.toLevCh (GlobalTheory.Mem.R3.Tr.levCh (a := x.o.Z) (oTw x (thTw (Dof x) th)).Z x.m.z.R.toRealDat.toLevCh) := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.exists_levelB2_twisted_state_of_thetaTie | exact _root_.GlobalTheory.HeightCounting.Up.exists_levelB2_twisted_state_of_thetaTie | (intros; apply _root_.GlobalTheory.HeightCounting.Up.exists_levelB2_twisted_state_of_thetaTie <;> assumption)
end
end
end
