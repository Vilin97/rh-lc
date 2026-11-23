module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PackB
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevTruePackB
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelCharacterMatchesWitnessAltBisStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QplacesOfBWitStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealPins
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealDataOfWitness
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiagSpacesOfOver
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeqIotaIffEqTransCastAdelicGroup
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedArgsColumnHeq
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPinsRealTOf
import Mathlib.Tactic.Linter.Style
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IdELevelMatchOfBwitStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.idE_and_levelMatch_of_bWit : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → GlobalTheory.Core.Mi.IdE b.S.X ∧ ∀ u, Formalism.L2.SG.ColDict.LevelMatch b.S.X (b.S.tr u) b.S.Y.hK := by
  intro hL p K q c b hw
  obtain ⟨sP, sS, -, -, e⟩ := hw.s
  rw [e]
  exact ⟨sP.pin, sP.lev⟩
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevTruePackBStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fam_levTrue_of_bWit : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → _root_.GlobalTheory.Fam.LevelCondition' (_root_.GlobalTheory.Fam.packB_alt b) := by
  first | exact @_root_.GlobalTheory.Fam.BundleLev.levTrue_packB_of_bWit | exact _root_.GlobalTheory.Fam.BundleLev.levTrue_packB_of_bWit | (intros; apply _root_.GlobalTheory.Fam.BundleLev.levTrue_packB_of_bWit <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPinsOfSeeAt

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev Formalism.L2.SG.RowsJoinPinned
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.SRe GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam.LinkedPins

theorem realPins_of_seeAt_alt {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {K : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl K Yd cX} {x : TwIn ex} {Rc : _root_.Formalism.L2.RecTAlt ex}
    {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} (y : _root_.GlobalTheory.Mem.R3.RealInAlt x Rc S) {P : SPack D fun u => (Rc.T.cols.forms u).to0} (sS : SRest P)
    (e : S = sS.toRealSpectralMatching Rc) (hC : x.R.C = Rc.T.n.cf) (hD : ∀ i, IsFDiag (Wc D i) ∧ IsFDiag (Vc D i))
    (hPg : open Classical in x.R.Pg = Rc.T.ker.Pr.vGs.image (Formalism.L2.Host.CT.plMap Rc.T.ker.seam.iE))
    (hs : SeeAt x.R.toRealDat x.F.lv2 P.X P.inst y.tS) : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation (_root_.GlobalTheory.Mem.R3.realisationOfInput y) := by
  subst e
  have hι : y.ιS = (iotaX P.X P.inst).toMulEquiv := (by with_unfolding_all exact ((GlobalTheory.Mem.JIota.heq_iota_iff D P.X P.inst ((y.ιS))).1 ((y.ιS_eq)) : _))
  refine _root_.GlobalTheory.Mem.R3.realPins_realTOf_alt _ _ _ _ _ _ _ _ ex x Rc _ y hC hD hPg hs.fin ?_ ?_
  · rw [hι]
    exact (by with_unfolding_all exact (hs.conj :))
  · exact (by with_unfolding_all exact (hs.mat :))
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx}

theorem realisation_normalisation_of_bundle_witness (q : WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation (_root_.GlobalTheory.Mem.R3.realisationOfInput w.y.y) := by
  obtain ⟨x, a, ax, y, recPin, ⟨sP, sS, hP, -, e⟩, ⟨pt, -⟩, _⟩ := w
  cases ax
  obtain ⟨h1, h2, -⟩ := twArgs_lev _ _ _ _ _ _ _ _ _ _ _ _ _ _ q.O.ex q.x.what₂ a
  have hk := recPin.k.std
  have fd : ∀ V : Formalism.BasicNotions.TH.HSp (q.w.D q.Z), GlobalTheory.Mem.HostFrames.SignFrame V → IsFDiag V := fun V hV => by
    obtain ⟨d, -, h⟩ := hV.gram_eq (q.w.D q.Z).host.F
    exact ⟨d, h⟩
  have hWV := (GlobalTheory.Mem.HostFrames.frames_of_over K (q.w.st q.Z) q.x.isOver).2.1
  refine _root_.GlobalTheory.Fam.LinkedPins.realPins_of_seeAt_alt y.y sS e ?_ (fun i => ⟨fd _ (hWV i).1, fd _ (hWV i).2⟩) ?_ ?_
  · have hc : b.R.T.n.cf = TC.cf q.w.I q.w.l q.Z := congrArg Sigma.fst recPin.s.chr
    have hC : Top.Fr.at (q.w.st q.Z) q.w.I.C = Top.Fr.at (q.w.st q.Z) q.f := congrArg (Top.Fr.at (q.w.st q.Z)) q.w.C_eq
    exact (eq_of_heq h1).trans (hC.symm.trans hc.symm)
  · rw [image_congr hk.X_eq hk.seam hk.Pr]
    exact (eq_of_heq h2).trans (image_refl _ rfl _).symm
  · have ht : y.y.tS = q.saturationAtWeightedPoint.t := eq_of_heq pt
    have hcols : b.R.T.cols = q.x.col.C := recPin.s.cols
    rw [ht]
    exact seeAt_twArgs a sP.X sP.inst q.saturationAtWeightedPoint.t (setting_congr (D := (q.w.st q.Z).toD7)
      (fun X h => SeeAt (D := (q.w.st q.Z).toD7) q.x.what₂.r.z.R.toRealDat q.x.what₂.r.z.F.lv2 X h q.saturationAtWeightedPoint.t)
      (congrArg (fun C u => (C.forms u).to0) hcols) hP q.saturationAtWeightedPoint.see)
end GlobalTheory.Fam.LinkedPins
open GlobalTheory.MiS GlobalTheory.Fam in

theorem GlobalTheory.Fam.realPins_bundle_of_bWit : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ}
    (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → _root_.Formalism.IndefR.IndefiniteRealisationNormalisation b.B.Q := by
  intro hL p K q c b w
  show (fun k : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S => _root_.Formalism.IndefR.IndefiniteRealisationNormalisation k.B.Q) (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b)
  rw [w.y.eq]
  exact _root_.GlobalTheory.Fam.LinkedPins.realisation_normalisation_of_bundle_witness q b w
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPinsOfSeeAtStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.realPins_of_bWit_third_place_series : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → _root_.Formalism.IndefR.IndefiniteRealisationNormalisation b.B.Q := by
  first | exact @_root_.GlobalTheory.Fam.realPins_bundle_of_bWit | exact _root_.GlobalTheory.Fam.realPins_bundle_of_bWit | (intros; apply _root_.GlobalTheory.Fam.realPins_bundle_of_bWit <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.XiChrEqCols

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 Formalism.IndefR Formalism.IndefR.Links
namespace GlobalTheory.Fam

theorem xi_chrEq_cols_alt : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → ∀ t, Formalism.IndefR.Links.ChrEq ((_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).xi t) (q.w.I.xi (b.P.I.tup t)) := by
  intro hL p K q c b hw
  obtain ⟨x, a, ax, y, recPin, s, pt, sx, eF, cW, d3b, side, colPins⟩ := hw
  have key : ∀ t : x.T, Formalism.IndefR.Links.ChrEq (x.R.toRealDat.xi t) (q.w.I.xi (x.Y.tup t)) := by
    have hxi : ∀ μ, Formalism.IndefR.RecTie.Used0 (q.w.D q.Z) μ → HEq (x.R.toLevCh.xiH (x.Y.tupT μ)) (q.w.I.xi μ) := by
      have h := eq_of_heq ax
      rw [← h]
      exact fun μ hμ => ((GlobalTheory.Mem.R3.twArgs_lev K q.B q.f q.T q.w q.Z _ _ _ _ _ _ _ _ _ _ a).2.2.1 μ hμ).2
    intro t
    have hu : Formalism.IndefR.RecTie.Used0 (q.w.D q.Z) (x.Y.tup t) := by
      rcases x.pins.char.tup.mu_used t with h | ⟨w, h⟩
      · rw [h]; exact Or.inl x.Y.tup0
      · rw [← h]
        obtain ⟨w', rfl⟩ := (q.w.D q.Z).plEq.surjective w
        exact Or.inr ⟨w', (x.Y.muAt w').symm⟩
    have h1 := hxi _ hu
    rw [x.Y.tupT_tup] at h1
    have h2 := x.pins.char.base.lev.xi t
    rw [eq_of_heq h1] at h2
    exact h2
  show (fun k : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S => ∀ t : k.P.T, Formalism.IndefR.Links.ChrEq (k.B.Q.Rl.toRealDat.xi t) (q.w.I.xi (k.P.I.tup t))) (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b)
  rw [y.eq]
  exact key
end GlobalTheory.Fam
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.XiChrEqColsStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.twist_character_matches_witness' : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → ∀ t, Formalism.IndefR.Links.ChrEq ((_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).xi t) (q.w.I.xi (b.P.I.tup t)) := by
  first | exact @_root_.GlobalTheory.Fam.xi_chrEq_cols_alt | exact _root_.GlobalTheory.Fam.xi_chrEq_cols_alt | (intros; apply _root_.GlobalTheory.Fam.xi_chrEq_cols_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealAtCols

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem GlobalTheory.Fam.realAt_cols_alt : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → (∀ j : Fin q.B.R.m, Formalism.IndefR.Links.ChrEq ((_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).mu0 ((j : ℕ) + 1)) (q.w.I.C.mu0 j)) ∧ (∀ t, Formalism.IndefR.Links.ChrEq ((_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).xi t) (q.w.I.xi (b.P.I.tup t))) ∧ (∀ t PP, PP ∈ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).Q t ↔ PP ∈ Formalism.L2.Col.QE q.w.I.sel (q.w.I.tup (b.P.I.tup t) : Formalism.L2.DIV.Chr q.B.fields.F q.B.fields.E q.B.fields.K)) ∧ _root_.GlobalTheory.Fam.LevelCondition' (_root_.GlobalTheory.Fam.packB_alt b) ∧ Nonempty (_root_.Formalism.IndefR.IndefiniteRealisationRecursion b.B.Q) ∧ _root_.Formalism.IndefR.IndefiniteRealisationNormalisation b.B.Q ∧ (∃ s, b.P.A3.fam3.Ok3 s) ∧ GlobalTheory.Core.Mi.IdE b.S.X ∧ ∀ u, Formalism.L2.SG.ColDict.LevelMatch b.S.X (b.S.tr u) b.S.Y.hK := by
  intro hL p K q c b hw
  refine ⟨_root_.GlobalTheory.T.chrEq_packB_mu0_succ_of_bWit q b hw, _root_.GlobalTheory.T.twist_character_matches_witness' q b hw, _root_.GlobalTheory.T.twist_places_match_witness' q b hw, _root_.GlobalTheory.T.fam_levTrue_of_bWit q b hw, ?_,
    _root_.GlobalTheory.T.realPins_of_bWit_third_place_series q b hw, ⟨1, b.C.ok1⟩, (_root_.GlobalTheory.T.idE_and_levelMatch_of_bWit q b hw).1, (_root_.GlobalTheory.T.idE_and_levelMatch_of_bWit q b hw).2⟩
  obtain ⟨x, a, ax, y, recPin, s, pt, sx, eF, cW, d3b, side, colPins⟩ := hw
  show (fun k : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S => Nonempty (_root_.Formalism.IndefR.IndefiniteRealisationRecursion k.B.Q)) (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b)
  rw [y.eq]
  exact ⟨_root_.GlobalTheory.Mem.R3.realisationRecursionOfInput y.r⟩
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealAtColsStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.characters_match_bundle_alt : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → (∀ j : Fin q.B.R.m, Formalism.IndefR.Links.ChrEq ((_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).mu0 ((j : ℕ) + 1)) (q.w.I.C.mu0 j)) ∧ (∀ t, Formalism.IndefR.Links.ChrEq ((_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).xi t) (q.w.I.xi (b.P.I.tup t))) ∧ (∀ t PP, PP ∈ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).Q t ↔ PP ∈ Formalism.L2.Col.QE q.w.I.sel (q.w.I.tup (b.P.I.tup t) : Formalism.L2.DIV.Chr q.B.fields.F q.B.fields.E q.B.fields.K)) ∧ _root_.GlobalTheory.Fam.LevelCondition' (_root_.GlobalTheory.Fam.packB_alt b) ∧ Nonempty (_root_.Formalism.IndefR.IndefiniteRealisationRecursion b.B.Q) ∧ _root_.Formalism.IndefR.IndefiniteRealisationNormalisation b.B.Q ∧ (∃ s, b.P.A3.fam3.Ok3 s) ∧ GlobalTheory.Core.Mi.IdE b.S.X ∧ ∀ u, Formalism.L2.SG.ColDict.LevelMatch b.S.X (b.S.tr u) b.S.Y.hK := by
  exact @_root_.GlobalTheory.Fam.realAt_cols_alt
end
end
end
