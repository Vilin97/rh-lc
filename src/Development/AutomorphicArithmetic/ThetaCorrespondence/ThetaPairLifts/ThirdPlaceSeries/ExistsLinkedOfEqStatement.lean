module

public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.EventuallyAllScaleContextsAndOfBoth
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevExOfOver
public import Formalism.LocalToGlobal.UnitaryNorms.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
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
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ColNorm
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HasPartAnd
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsStdFStdLvC
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsDefiniteLaws
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelEntriesCompatibleTrueColumns
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Tactic.NormNum.Parity
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TrueColumnTupleTrivialEqOne
import Development.AutomorphicArithmetic.PrimeDiscriminants.Scales
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KerEntTiedTrueEnt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostPlacesRayField
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsHostDatum
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TiedDataSAssembleStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TiedSKAtWitnesses
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelTiedOfLevEx

section

@[expose] public section

open Formalism.BasicNotions GlobalTheory.Mem.HD

theorem GlobalTheory.Mem.HD.levelTied_of_levEx : ∀ D : D7, LevEx D → Formalism.L2.Host.LevelTied D :=
  fun D h => ⟨fun p => by
    have hq : Formalism.MainNotions.q0Av D = Formalism.MainNotions.AbsolutelyIrreducibleSpan.q0 D := rfl
    simpa [hq] using h p⟩
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsBdRecOfEq

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.Top.Bl
theorem exists_bdRec_of_eq_alt {D D' : D7} {O : Obj D} {O' : Obj D'} (h : (⟨D, O⟩ : Σ D : D7, Obj D) = ⟨D', O'⟩)
    (R : _root_.Formalism.L2.RecTAlt O'.ex) (c : ℝ) :
    ∃ b : _root_.GlobalTheory.Mem.Top.Bl.BoundaryReciprocity D O c, (⟨D, O, b⟩ : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Mem.Top.Bl.BoundaryReciprocity D O c) = ⟨D', O', R⟩ := by
  cases h
  exact ⟨R, rfl⟩
end GlobalTheory.Mem.Top.Bl
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsKerTie

section

@[expose] public section

section BaseLevels₂

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar



theorem GlobalTheory.Core.DefKer.stdRd_keep {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l))
    {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)} {K : G.Consts}
    {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX} (t : KerEntTied ex) (hS : I.StdKer l Z t) :
    ∃ t' : KerEntTied ex, I.StdKer l Z t' ∧ GlobalTheory.Pdv.StdRd I l Z t' ∧ t'.TopPinned ∧ t'.O = t.O ∧ t'.ent = t.ent := by
  rcases t with ⟨cc, cc_rec, cc_ok, δ, δ_ok, Bb, χ, χ_ok, idl, idl_ok, χ_rec, cD, Xf, seam, seam_ok, Pr, pr_ok, g_rec, Ch, sel, S, word, T_rec, tup, Q_rec, cst, idx, m2, glob, glob_σ, glob_xi, idx_ok, O, rd, rd_chain, O_dgen, O_S, O_lat, O_Th, unf, ent, ent_lam, kf, kf_un, served⟩
  obtain ⟨hX, hseam, hPr, hCh, hsel, hSS, hword, htup, hcst, hidx, hm2, hglob, hamb, hδ, hO⟩ := hS
  dsimp only at hX hseam hPr hCh hsel hSS hword htup hcst hidx hm2 hglob hamb hδ hO
  subst hX
  cases hseam
  cases hPr
  cases hCh
  cases hsel
  subst hSS
  cases htup
  cases hcst
  cases hidx
  subst hm2
  cases hglob
  cases hword
  have hA : ambOf (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) Bb χ cD = I.J.amb B χ := eq_of_heq hamb
  have hm := hOk.hm
  have hpi : ∀ (u : B.Word) (a : I.ι) (w : rowSG (B.primes X) I.sel (I.tup a)), (B.primes X).piT u ∉ w.1.asIdeal := fun u a =>
    (TopStep.tilOk_of_avoid l.pr hOk.sel_ok u ⟨hOk.T_mem u, hOk.g_mem⟩).2.1
  refine ⟨⟨cc, cc_rec, cc_ok, δ, δ_ok, Bb, χ, χ_ok, idl, idl_ok, χ_rec, cD, _, _, seam_ok, _, pr_ok, g_rec, _, _, _, _, T_rec, _, Q_rec, _, _, _, _, glob_σ, glob_xi, idx_ok, O, I.kerRd l Z, fun u a => topChain _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (FieldsLaws.fields_ok B) l.pr (hOk.idx_ok a).cst_ok hm (hpi u a) (I.kerRd_top l Z hm u a), O_dgen, O_S, ?_, ?_, unf, ent, ent_lam, kf, kf_un, served⟩, ?_, ?_, ?_, rfl, rfl⟩
  · exact fun u a i c => (hO.lat u a i c).trans (seamOf_lat B (I.cols l) Z.W Z.V Z.S Z.N Z.G _).symm
  · intro u a i c c'
    rw [hA, AmbIn.amb_eq_ambOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J χ, χ_rec]
    exact (hO.Th u a i c c').trans (I.kerRd_Th l Z hOk idl_ok hO u a i c c').symm
  · exact ⟨rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl, heq_of_eq hA, hδ, hO⟩
  · exact fun u a => ⟨I.kerRd l Z u a, HEq.rfl, fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩
  · exact fun u a => I.kerRd_top l Z hm u a


end BaseLevels₂

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Core GlobalTheory.Core.Cls NumberField IsDedekindDomain GlobalTheory.Mem.Db Formalism.L2 Formalism.L2.Ker Formalism.L2.Forms
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsKerTie

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem GlobalTheory.Mem.Top.Bl.WPt.exists_kerTie : ∀ (𝒮 : Slots) (K : Ctx) (q : WPt 𝒮 K), EntC q.x.ker → ∃ t : Formalism.L2.Ker.KerEntTied q.O.ex, KPin q t ∧ GlobalTheory.Svd.StdAt q.w.I q.w.l q.w.l0 q.Z q.O t ∧ GlobalTheory.Pdv.StdRd q.w.I q.w.l q.Z t := by
  intro 𝒮 K q hE
  obtain ⟨B, f, T, w, Z, O, x⟩ := q
  obtain ⟨L, gatT, Gx, Gy, Kc, X, cX, ex⟩ := O
  obtain ⟨lev, th, th_io, cmp, lat, tw, ker, ep_def, ep_tie, kapI_def, fills_all, nu_unserved, idx, kap_def, lam_def, kapR_def, errX, err, nch, nch_tie, xd, p0, rationalRoots_def, amb, amb0, fdef, duStar_def, Dstar_def, gauge, gauge_def⟩ := ex
  obtain ⟨isOver, forced, Wt, pin, coh, vol, col, what₂, rx, hlev, herrX, n, nx, sx, ker0, ker_eq, kT, div, thT, obj, ox, real, dsig_eq, gaugeG, good⟩ := x
  simp only [ofObj, extraObj] at ker_eq
  cases ker_eq
  obtain ⟨t1, s1, o1, e1, a1, p1⟩ := TC.kerEntTied_true_ent w.I w.ok w.pins w.l Z L col.Gt Gx Gy Kc X cX
    ⟨lev, th, th_io, col.cmp, lat, w.tw Z, ker, ep_def, ep_tie, kapI_def, fills_all, nu_unserved, idx, kap_def, lam_def, kapR_def, errX, err, nch,
      nch_tie, xd, p0, rationalRoots_def, amb, amb0, fdef, duStar_def, Dstar_def, gauge, gauge_def⟩ kT.O kT.E div.Qp kT.std
    kT.unf kT.ok kT.served
  obtain ⟨t, s, r, p, o, e⟩ := GlobalTheory.Core.DefKer.stdRd_keep w.I w.ok w.l Z t1 ((StdModel.stdKer_iff w.I w.l Z t1).2 s1)
  have ha : t.Adapted := by
    unfold Formalism.L2.Ker.KerEntTied.Adapted at a1 ⊢
    rw [o, e]
    exact a1
  have hc : GlobalTheory.Pdv.IsEntC t := by
    unfold GlobalTheory.Pdv.IsEntC
    rw [o, e, o1, e1]
    exact hE
  exact ⟨t, ⟨s, o.trans o1, heq_of_eq (e.trans e1), ha, p⟩, ⟨w.ok, w.pins, pin.isTw, pin.jets, rfl, s, hc, ha, p⟩, r⟩
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsRecPinE

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.Top.Bl
theorem WPt.exists_recPinE_alt : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.WeberRayFieldSt → GlobalTheory.NT.RayField →
    ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (K : Ctx) (q : WPt p.s K), Formalism.L2.Host.LevelTied (q.w.D q.Z) →
      Formalism.L2.Rows.ZetaCompatible (q.w.D q.Z) → EntC q.x.ker → ∃ R : _root_.Formalism.L2.RecTAlt q.O.ex, _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended q R := by
  intro hA hW hR hL p K q hLT hZe hE
  obtain ⟨S, hS⟩ := _root_.GlobalTheory.T.exists_spectral_data_compatible hA hW hL p K q hLT hZe
  obtain ⟨t, hK, hstd, hrd⟩ := GlobalTheory.Mem.Top.Bl.WPt.exists_kerTie p.s K q hE
  obtain ⟨T, hTS, hTk, hcrd, hpin, hj, ⟨⟨hw⟩⟩⟩ := _root_.GlobalTheory.Mem.Top.Bl.exists_kernel_spectral_data_at_witnesses hL p K q S t hS hK
  have hp := GlobalTheory.Mem.Top.Bl.hostPins_wpt hR p.s K q
  subst hTS hTk
  obtain ⟨hd, -⟩ := _root_.GlobalTheory.HostDatumExists.exists_hostDatum_alt hA _ _ _ _ _ _ _ _ q.O.ex T.toTiedDataS hp q.x.pin.d3b
  exact ⟨⟨T, hpin, hj, ⟨hd⟩, hw⟩, ⟨⟨hS, hK, hcrd⟩, hE, hstd, hrd⟩⟩
end GlobalTheory.Mem.Top.Bl
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsRecPinEStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_reciprocity_record_compatible : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.WeberRayFieldSt → GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (K : Ctx) (q : WPt p.s K), Formalism.L2.Host.LevelTied (q.w.D q.Z) → Formalism.L2.Rows.ZetaCompatible (q.w.D q.Z) → EntC q.x.ker → ∃ R : _root_.Formalism.L2.RecTAlt q.O.ex, _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended q R := by
  first | exact @_root_.GlobalTheory.Mem.Top.Bl.WPt.exists_recPinE_alt | exact _root_.GlobalTheory.Mem.Top.Bl.WPt.exists_recPinE_alt | (intros; apply _root_.GlobalTheory.Mem.Top.Bl.WPt.exists_recPinE_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsLinkedOfEq

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
namespace GlobalTheory.Mem.Top.Bl
theorem exists_linked_of_eq_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx}
    (hB : ∀ (q : WPt p.s K) (R : _root_.Formalism.L2.RecTAlt q.O.ex), _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended q R → ∀ (c : ℝ)
      (_ : {n : ℕ × ℕ // (q.w.D q.Z).s.Del = (n.1 : ℚ) ∧ q.O.L.etaSz = ((q.w.D q.Z).R.m : ℝ) * (n.2 : ℝ)}),
      q.O.L.sc = K.s → Val K.C K.cD K.ch q.O.L → ∃ b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c, b.R = R ∧ Nonempty (_root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b))
    (q : WPt p.s K) (R' : _root_.Formalism.L2.RecTAlt q.O.ex) (hR' : _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended q R') (c : ℝ) {D : D7} {O : Obj D} (R : _root_.GlobalTheory.Mem.Top.Bl.BoundaryReciprocity D O c)
    (he : (⟨D, O, R⟩ : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Mem.Top.Bl.BoundaryReciprocity D O c) = ⟨q.w.D q.Z, q.O, R'⟩) (hsc : O.L.sc = K.s)
    (hv : Val K.C K.cD K.ch O.L) (n : {n : ℕ × ℕ // D.s.Del = (n.1 : ℚ) ∧ O.L.etaSz = (D.R.m : ℝ) * (n.2 : ℝ)}) :
    ∃ b : _root_.GlobalTheory.Fc.BundleCondition D O c, ∃ (q' : WPt p.s K) (b' : _root_.GlobalTheory.Fc.BundleCondition (q'.w.D q'.Z) q'.O c), Nonempty (_root_.GlobalTheory.Mem.Top.Bl.BundleWitness q' b') ∧
      (⟨D, O, b⟩ : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c) = ⟨q'.w.D q'.Z, q'.O, b'⟩ := by
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.mp he
  obtain ⟨rfl, -⟩ := Sigma.mk.inj_iff.mp (eq_of_heq h2)
  obtain ⟨b, -, hW⟩ := hB q R' hR' c n hsc hv
  exact ⟨b, q, b, hW, rfl⟩
theorem exBL_isLinked_alt : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.WeberRayFieldSt → GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), WitExE p.s → (GlobalTheory.Fc.EvP fun _ K => ∀ q : WPt p.s K, Formalism.L2.Rows.ZetaCompatible (q.w.D q.Z)) → (GlobalTheory.Fc.EvP fun _ K => ∀ (q : WPt p.s K) (R : _root_.Formalism.L2.RecTAlt q.O.ex), _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended q R → ∀ (c : ℝ) (_ : {n : ℕ × ℕ // (q.w.D q.Z).s.Del = (n.1 : ℚ) ∧ q.O.L.etaSz = ((q.w.D q.Z).R.m : ℝ) * (n.2 : ℝ)}), q.O.L.sc = K.s → Val K.C K.cD K.ch q.O.L → ∃ b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c, b.R = R ∧ Nonempty (_root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b)) → GlobalTheory.Fc.ExBL KPx (IsBuiltE p.s) (IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) := by
  intro hA hW hRay hL p hWit hZe hB
  refine ⟨fun _ _ _ _ _ => True, GlobalTheory.Fc.largeBaseProperty_true, ?_⟩
  unfold GlobalTheory.Fc.ExB
  refine GlobalTheory.Fc.EvP.mono (fun κ K _ H => ?_) (GlobalTheory.Fc.EvP.and hZe hB)
  intro β hβ c
  obtain ⟨q, hq, hE⟩ := hWit K β hβ.1
  obtain ⟨C5, c6, Cb, hG⟩ := β.good
  have hO : Over β.X.toD7 K.P K.Lv := by
    obtain ⟨sp, hT, hY, hA', hV, hz, e, -⟩ := β.c.isOver
    exact ⟨sp, hT, hY, hA', hV, hz, β.X, e, rfl⟩
  have hP : K.P.H.levelPrimes = {K.P.H.g 0, K.P.H.g 1, K.P.H.pde, K.P.H.pde', DC.q0H K.P.H} :=
    hG.host.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hLT : Formalism.L2.Host.LevelTied β.D :=
    GlobalTheory.Mem.HD.levelTied_of_levEx _ ((GlobalTheory.Mem.HD.levEx_of_over _ _ _ hO hP).2 _ _)
  have hD : β.D = q.w.D q.Z := congrArg Sigma.fst hq
  have hLT' : Formalism.L2.Host.LevelTied (q.w.D q.Z) := hD ▸ hLT
  obtain ⟨R', hR'⟩ := _root_.GlobalTheory.T.exists_reciprocity_record_compatible hA hW hRay hL p K q hLT' (H.1 q) hE
  obtain ⟨R, he⟩ := _root_.GlobalTheory.Mem.Top.Bl.exists_bdRec_of_eq_alt hq R' c
  have hv : Val K.C K.cD K.ch β.O.L := β.p.pt_val β.val
  exact _root_.GlobalTheory.Mem.Top.Bl.exists_linked_of_eq_alt H.2 q R' hR' c R he β.sc hv ⟨(_, _), hv.Del_eq, hv.eta_eq⟩
end GlobalTheory.Mem.Top.Bl
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsLinkedOfEqStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw

theorem _root_.GlobalTheory.T.eta_size_recursion_alt : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.WeberRayFieldSt → GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), WitExE p.s → (GlobalTheory.Fc.EvP fun _ K => ∀ q : WPt p.s K, Formalism.L2.Rows.ZetaCompatible (q.w.D q.Z)) → (GlobalTheory.Fc.EvP fun _ K => ∀ (q : WPt p.s K) (R : _root_.Formalism.L2.RecTAlt q.O.ex), _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended q R → ∀ (c : ℝ) (_ : {n : ℕ × ℕ // (q.w.D q.Z).s.Del = (n.1 : ℚ) ∧ q.O.L.etaSz = ((q.w.D q.Z).R.m : ℝ) * (n.2 : ℝ)}), q.O.L.sc = K.s → Val K.C K.cD K.ch q.O.L → ∃ b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c, b.R = R ∧ Nonempty (_root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b)) → GlobalTheory.Fc.ExBL KPx (IsBuiltE p.s) (IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) := by
  first | exact @_root_.GlobalTheory.Mem.Top.Bl.exBL_isLinked_alt | exact _root_.GlobalTheory.Mem.Top.Bl.exBL_isLinked_alt | (intros; apply _root_.GlobalTheory.Mem.Top.Bl.exBL_isLinked_alt <;> assumption)
end
end
end
