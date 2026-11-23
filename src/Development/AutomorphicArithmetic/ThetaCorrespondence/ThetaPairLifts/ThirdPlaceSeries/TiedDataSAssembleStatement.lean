module

public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DsigEq
public import Formalism.LocalToGlobal.HilbertRowConditions.TiedEMt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IpMtTie
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
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnChoiceExistsStandardChainDataStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DtTiedTrue
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NatCardCodeWordStagesFiniteGroupEq

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EMtTied

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.Mem.Col2.EMt

theorem eMtTied : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (nch : NChoice (I.rec7 l Z)) (tp : Formalism.L2.Host.TupTied (I.rec7 l Z) (I.cf l Z) nch) (C : ColsTiedSym (I.rec7 l Z)) (t : SymmetricTwistedColumnsAtPrimes tp C (I.tw l l0 Z)), (∀ u F G, inner ℂ ((I.rec7 l Z).eMt u F) ((I.rec7 l Z).eMt u G) = I.ipMt l u I.mu0 F G) → (∀ u (a : (I.rec7 l Z).what₂.Tup), a ≠ (I.rec7 l Z).what₂.mu0 → ∀ F G, inner ℂ ((I.rec7 l Z).eMtTw u a F) ((I.rec7 l Z).eMtTw u a G) = I.ipMt l u a F G) → Formalism.L2.Rows.EMtTied (I.rec7 l Z) C t := by
  intro B X I hOk hP l Z l0 nch tp C t h0 h1
  refine ⟨fun u F G => ?_, fun u a ha F G => ?_⟩
  · rw [h0 u F G]
    exact (GlobalTheory.Mem.Col2.IpMt.ipMt_tie I hOk hP l Z u I.mu0 (C.forms u).jM (C.forms u).per.2.1 (C.forms u).per.2.2).1 F G
  · rw [h1 u a ha F G]
    exact (GlobalTheory.Mem.Col2.IpMt.ipMt_tie I hOk hP l Z u a (t.ptE.jM u a) (t.ptE.per u a ha).2.1 (t.ptE.per u a ha).2.2).1 F G

end GlobalTheory.Mem.Col2.EMt

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColsTwTied

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Top.Bl

theorem WPt.colsTwTied : ∀ (𝒮 : Slots) (K : Ctx) (q : WPt 𝒮 K), q.O.ex.tw = q.w.tw q.Z ∧ ∃ tw : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes q.x.n.tp q.x.col.C (q.w.tw q.Z), TC.StdTw q.w.I q.w.l q.Z q.w.l0 tw ∧ Formalism.L2.Rows.EMtTied (q.w.D q.Z) q.x.col.C tw := by
  intro 𝒮 K q
  refine ⟨?_, ?_⟩
  · exact congrArg (fun s : Σ (Gt : GatTies (q.w.D q.Z)) (cmp : LatCmp (q.w.D q.Z)) (tw : TwForms (q.w.D q.Z)),
      KerFam (q.w.D q.Z) Gt cmp tw (ofObj q.O).Gy => s.2.2.1) q.x.ker_eq
  · obtain ⟨tw, htw⟩ := GlobalTheory.T.trueColumnChoice_exists_standardChainData q.w.I q.w.ok q.w.pins q.w.l q.Z q.w.l0 _ q.x.n.tp q.x.col.C q.x.n.xi q.x.col.std q.x.col.stdLv
    exact ⟨tw, htw, GlobalTheory.Mem.Col2.EMt.eMtTied q.w.I q.w.ok q.w.pins q.w.l q.Z q.w.l0 _ q.x.n.tp q.x.col.C tw q.x.what₂.emt0 q.x.what₂.emt⟩

end GlobalTheory.Mem.Top.Bl

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTiedDataReciprocity

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl


theorem ColW.cf_eq {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z : w.Lt) :
    Fr.at (w.st Z) f = TC.cf w.I w.l Z := by
  have h := w.C_eq
  have : Fr.at (w.st Z) w.I.C = TC.cf w.I w.l Z := rfl
  rw [← this, h]


end GlobalTheory.Mem.Top.Bl
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtraTiedCol

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Mem.Top.Bl.WPt.extraTied_col : ∀ (𝒮 : Slots) (K : Ctx) (q : WPt 𝒮 K), Formalism.L2.Forms.ColsExtraTiedS q.x.col.full q.O.ex ∧ ∃ g : Formalism.L2.G.GroupCompatibilityAll (q.w.D q.Z) q.O.gatT q.O.ex.cmp, HEq g q.x.col.g ∧ g.herm = q.x.col.full.1.to0 ∧ g.forms = fun u => (q.x.col.C.forms u).to0 := by
  intro 𝒮 K q
  obtain ⟨B, f, T, w, Z, O, x⟩ := q
  obtain ⟨L, gatT, Gx, Gy, K', X, cX, ex⟩ := O
  obtain ⟨lev, th, th_io, cmp, lat, tw, ker, ep_def, ep_tie, kapI_def, fills_all, nu_unserved, idx, kap_def, lam_def, kapR_def,
    errX, err, nch, nch_tie, xd, p0, rationalRoots_def, amb, amb0, fdef, duStar_def, Dstar_def, gauge, gauge_def⟩ := ex
  obtain ⟨isOver, forced, Wt, pin, coh, vol, col, what₂, rx, hlev, herrX, n, nx, sx, ker0, ker_eq, kt, div, thT, obj, ox, real,
    dsig_eq, hgauge, good⟩ := x
  obtain ⟨⟨C, std, stdLv, full, stdDt, Gt, cmp', g, herm_eq, forms_eq, gpl⟩, isRec, om⟩ := col
  dsimp only at hlev herrX ker_eq ⊢
  cases ker_eq
  exact ⟨⟨⟨hlev, herrX, gpl⟩, kt.iw, kt.iw_pos⟩, g, HEq.rfl, herm_eq, forms_eq⟩
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NTiedAllAtWit

section

@[expose] public section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.Top.Bl
theorem exists_core_parameters_agree : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (K : Ctx) (q : WPt p.s K), ∃ (I : TwIn (q.w.D q.Z)) (n : _root_.Formalism.L2.NTiedAllAlt (q.w.D q.Z) q.O.ex.nch I), I.E = twEOf q.O.ex.xd ∧ DQ.GoodAllAt (q.w.D q.Z) q.O.ex.nch I ∧ (⟨n.cf, n.tp⟩ : Σ c : CharFrame (q.w.D q.Z), TupTied (q.w.D q.Z) c q.O.ex.nch) = ⟨TC.cf q.w.I q.w.l q.Z, q.x.n.tp⟩ ∧ n.gal = q.core_data_of_point.a.all.gal ∧ n.n = q.core_data_of_point.a.all.n ∧ n.exp = q.core_data_of_point.a.all.exp ∧ n.chiD = q.core_data_of_point.a.all.chiD ∧ n.twF = q.core_data_of_point.a.all.twF ∧ HEq n.types q.core_data_of_point.a.all.types ∧ HEq n.cover q.core_data_of_point.a.all.cover ∧ n.plB = q.core_data_of_point.a.all.plB := by
  intro hL p K q
  obtain ⟨I, hE, hG, hC⟩ := q.x.good.tw
  have hch := q.core_data_of_point.a.chr_eq
  have hc : Formalism.L2.NChoiceTied (q.w.D q.Z) q.O.ex.nch I (Formalism.L2.avDesign (q.w.D q.Z)) := by
    have c := q.core_data_of_point.a.all.choice
    first
    | exact { twI_conj := c.twI_conj, sd_place := c.sd_place, emb_side := c.emb_side, sd_conj := c.sd_conj, one := c.one,
              good := fun w hw h => hC w hw h, conj := c.conj }
    | exact { twI_conj := c.twI_conj, sd_place := c.sd_place, emb_side := c.emb_side, sd_conj := c.sd_conj, one := c.one,
              conj := c.conj }
  refine ⟨I, { q.core_data_of_point.a.all with choice := hc }, hE, hG, hch, rfl, rfl, rfl, rfl, rfl, HEq.rfl, HEq.rfl, rfl⟩
end GlobalTheory.Mem.Top.Bl
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TiedDataSAssemble

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.Top.Bl
open Formalism.L2 in

theorem tiedDataS_assemble_alt {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {K : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} (ex : Extra D L hT Gi Gl K Y cX)
    (host : Formalism.L2.Host.HostTied D) (level : Formalism.L2.Host.LevelTied D) (cols : Formalism.L2.Forms.ColsTiedSym D) (full : Formalism.L2.Forms.ColsFullS cols)
    (extra : Formalism.L2.Forms.ColsExtraTiedS full ex) (provA : Formalism.BasicNotions.TH.ProvA) (theta : Formalism.L2.Theta.AllTied D ex.th provA) (twIn : Formalism.MainNotions.TwIn D)
    (n : _root_.Formalism.L2.NTiedAllAlt D ex.nch twIn) (frameN : ∀ x, n.gal.fr.jE x = host.fr.j x)
    (cf : Formalism.L2.Host.CharFrame D) (tp : Formalism.L2.Host.TupTied D cf ex.nch)
    (h : (⟨n.cf, n.tp⟩ : Σ c : Formalism.L2.Host.CharFrame D, Formalism.L2.Host.TupTied D c ex.nch) = ⟨cf, tp⟩)
    (thetaChr : Formalism.L2.Host.ThetaChrTied D cf ex.nch tp ex.th) (chrVal : Formalism.L2.Host.ValLL0 D cf) (chrDt : Formalism.L2.Host.DtTied D cf)
    (chrN : Formalism.L2.Host.NCharTied D cf ex.nch tp) (chrGal : Formalism.L2.Host.NGalChrTied D cf ex.nch tp)
    (chrPsi : Formalism.L2.Host.PsiChoiceCompatible D cf ex.nch tp) (sameChr : Formalism.L2.JoinChr.SameChr theta.T thetaChr)
    (what₂ : Formalism.L2.Rows.RowsCompatible D host cf tp) (inK : Y.Lev → ℕ → Prop) (geo : Formalism.L2.Geo.GeoTiedP Y inK)
    (tw0 : TwForms D) (he : ex.tw = tw0) (tw : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes tp cols tw0) (emt : Formalism.L2.Rows.EMtTied D cols tw)
    (g : Formalism.L2.G.GroupCompatibilityAll D hT ex.cmp) (herm_eq : g.herm = full.1.to0) (forms_eq : g.forms = fun u => (cols.forms u).to0)
    (P : ∀ (c : Formalism.L2.Host.CharFrame D) (t : Formalism.L2.Host.TupTied D c ex.nch) (C : Formalism.L2.Forms.ColsTiedSym D), Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes t C tw0 → Prop)
    (hP : P cf tp cols tw) :
    ∃ S : _root_.Formalism.L2.TiedDataSAlt ex, S.host = host ∧ S.cols = cols ∧ HEq S.full full ∧ S.g = g ∧
      (⟨S.provA, S.theta⟩ : Σ a, Formalism.L2.Theta.AllTied D ex.th a) = ⟨provA, theta⟩ ∧
      (⟨S.twIn, S.n⟩ : Σ I, _root_.Formalism.L2.NTiedAllAlt D ex.nch I) = ⟨twIn, n⟩ ∧ HEq S.thetaChr thetaChr ∧
      (∀ a, S.chrDt.eDt a = chrDt.eDt a) ∧
      (S.what₂.O.pieces.rcf = what₂.O.pieces.rcf ∧ S.what₂.O.pieces.MDel = what₂.O.pieces.MDel) ∧
      S.inK = inK ∧ HEq S.geo geo ∧ P _ _ _ (he ▸ S.tw) := by
  cases h
  subst he
  first
  | exact ⟨{ host := host, level := level, cols := cols, full := full, extra := extra, provA := provA, theta := theta,
               twIn := twIn, n := n, frameN := frameN, thetaChr := thetaChr, chrVal := chrVal, chrDt := chrDt, chrN := chrN,
               chrGal := chrGal, chrPsi := chrPsi, sameChr := sameChr, what₂ := what₂, inK := inK, geo := geo, tw := tw, emt := emt,
               g := g, herm_eq := herm_eq, forms_eq := forms_eq },
        rfl, rfl, HEq.rfl, rfl, rfl, rfl, HEq.rfl, fun _ => rfl, ⟨rfl, rfl⟩, rfl, HEq.rfl, hP⟩
  | exact ⟨{ host := host, level := level, cols := cols, full := full, extra := extra, provA := provA, theta := theta,
               twIn := twIn, n := n, thetaChr := thetaChr, chrVal := chrVal, chrDt := chrDt, chrN := chrN,
               chrGal := chrGal, chrPsi := chrPsi, sameChr := sameChr, what₂ := what₂, inK := inK, geo := geo, tw := tw, emt := emt,
               g := g, herm_eq := herm_eq, forms_eq := forms_eq },
        rfl, rfl, HEq.rfl, rfl, rfl, rfl, HEq.rfl, fun _ => rfl, ⟨rfl, rfl⟩, rfl, HEq.rfl, hP⟩

theorem WPt.exists_pinned_spectral_data_compatible : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.WeberRayFieldSt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (K : Ctx) (q : WPt p.s K), Formalism.L2.Host.LevelTied (q.w.D q.Z) → Formalism.L2.Rows.ZetaCompatible (q.w.D q.Z) → ∃ S : _root_.Formalism.L2.TiedDataSAlt q.O.ex, _root_.GlobalTheory.Mem.Top.Bl.SpectralDataCompatible q S := by
  intro hA hW hL p K q hlev hze
  obtain ⟨extra, g, hg, hherm, hforms⟩ := WPt.extraTied_col p.s K q
  obtain ⟨I, n, hE, hgood, hchr, h1, h2, h3, h4, h5, h6, h7, h8⟩ := _root_.GlobalTheory.Mem.Top.Bl.exists_core_parameters_agree hL p K q
  obtain ⟨he, tw, hstd, emt⟩ := GlobalTheory.Mem.Top.Bl.WPt.colsTwTied p.s K q
  obtain ⟨dt, hdt⟩ := TC.dtTied_true q.w.I q.w.ok q.w.pins q.w.l q.Z
  have hO : ∃ O : Formalism.L2.Rows.OTied (q.w.D q.Z) q.core_data_of_point.a.host (TC.cf q.w.I q.w.l q.Z),
      O.pieces.rcf = GlobalTheory.Mem.HD.qb q.core_data_of_point.a.host.fr.ι q.w.δ.ray ∧ O.pieces.MDel = GlobalTheory.Mem.HD.qb q.core_data_of_point.a.host.fr.ι q.w.δ.M' := by
    generalize q.core_data_of_point.a.host = H
    rw [← ColW.cf_eq]
    exact GlobalTheory.Mem.CyclotomicFieldContainment.oTied_of_ksExact hA hW (q.w.st q.Z) q.f q.w.δ q.w.exact H
  obtain ⟨O, hO1, hO2⟩ := hO
  have hval : Formalism.L2.Host.ValLL0 (q.w.D q.Z) (TC.cf q.w.I q.w.l q.Z) := by
    rw [← ColW.cf_eq]
    exact q.w.val _ _ _ _ _ _
  have hfr : ∀ x, n.gal.fr.jE x = q.core_data_of_point.a.host.fr.j x := by
    rw [h1]
    exact q.core_data_of_point.a.frameN
  obtain ⟨S, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12⟩ :=
    _root_.GlobalTheory.Mem.Top.Bl.tiedDataS_assemble_alt q.O.ex q.core_data_of_point.a.host hlev q.x.col.C q.x.col.full extra q.x.th.provA q.x.th.all I n hfr
      (TC.cf q.w.I q.w.l q.Z) q.x.n.tp hchr q.x.th.chr hval dt q.core_data_of_point.a.chrN q.core_data_of_point.a.chrGal q.x.n.chrPsi q.x.th.same
      ⟨O, q.O.ex.kap_def, hze⟩ q.x.div.inK q.x.div.geo (q.w.tw q.Z) he tw emt g hherm hforms
      (fun _ _ _ t => TC.StdTw q.w.I q.w.l q.Z q.w.l0 t) hstd
  have key : ∀ Q : (Σ I, _root_.Formalism.L2.NTiedAllAlt (q.w.D q.Z) q.O.ex.nch I) → Prop, Q ⟨I, n⟩ → Q ⟨S.twIn, S.n⟩ :=
    fun Q hQ => s6 ▸ hQ
  refine ⟨S, s1, s2, s3, s4 ▸ hg, s5, key (fun z => z.1.E = _) hE, key (fun z => DQ.GoodAllAt _ _ z.1) hgood,
    key (fun z => (⟨z.2.cf, z.2.tp⟩ : Σ c : CharFrame (q.w.D q.Z), TupTied (q.w.D q.Z) c q.O.ex.nch) = _) hchr,
    key (fun z => z.2.gal = _) h1, key (fun z => z.2.n = _) h2, key (fun z => z.2.exp = _) h3,
    key (fun z => z.2.chiD = _) h4, key (fun z => z.2.twF = _) h5, key (fun z => HEq z.2.types _) h6,
    key (fun z => HEq z.2.cover _) h7, key (fun z => z.2.plB = _) h8, s7, fun a => (s8 a).trans (hdt a), ?_, s10, s11, he, s12⟩
  rw [s9.1, s9.2, s1]
  exact ⟨hO1, hO2⟩
end GlobalTheory.Mem.Top.Bl
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TiedDataSAssembleStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_spectral_data_compatible : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.WeberRayFieldSt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (K : Ctx) (q : WPt p.s K), Formalism.L2.Host.LevelTied (q.w.D q.Z) → Formalism.L2.Rows.ZetaCompatible (q.w.D q.Z) → ∃ S : _root_.Formalism.L2.TiedDataSAlt q.O.ex, _root_.GlobalTheory.Mem.Top.Bl.SpectralDataCompatible q S := by
  first | exact @_root_.GlobalTheory.Mem.Top.Bl.WPt.exists_pinned_spectral_data_compatible | exact _root_.GlobalTheory.Mem.Top.Bl.WPt.exists_pinned_spectral_data_compatible | (intros; apply _root_.GlobalTheory.Mem.Top.Bl.WPt.exists_pinned_spectral_data_compatible <;> assumption)
end
end
end
