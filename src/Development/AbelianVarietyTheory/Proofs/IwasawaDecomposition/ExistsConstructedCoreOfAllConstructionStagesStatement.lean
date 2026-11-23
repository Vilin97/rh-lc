module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnLayerConditionsTrueColumnsLaterStages
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
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsGaugeOfIsCMExt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnChoiceCloudBoundLeExplicitParametersStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeLayerTrueColumnsParametersFreeStatement
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelsKernelDataAtServedPlace
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyLiftObj
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeTransportPreservesSelfDual
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TilLatticesOfLevel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MkDetPtEqRelDetQ
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnChoicesKernelDatumAdaptedBasesStatement
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ForcedContentEqScaleAtResidueChar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResCharConj

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnLayerConditionsTrueColumnsLaterStagesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.columnLayerConditions_trueColumns_laterStages : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (t : ColT w Z), ColLay (w.D Z) t.full.1.base.lev0 (Formalism.L2.Herm.toErrXS t.full.1) := by
  first | exact @GlobalTheory.Mem.Top.ColOwe.colLay_colT | exact GlobalTheory.Mem.Top.ColOwe.colLay_colT | (intros; apply GlobalTheory.Mem.Top.ColOwe.colLay_colT <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelsKernelDataAtServedPlaceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.levels_kernelData_at_served_place : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ (Fl : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.Fills ((w.D Z).gat u v hg)),
      (∀ u v hg, (Fl u v hg).t = (w.D Z).R.t ∧ (Fl u v hg).mm = (w.D Z).R.m) →
      (∀ u v hg (x : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts (w.D Z),
        ((Fl u v hg).w x j s : ℝ) = wj (w.D Z) j (t.Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ (w.D Z) j) →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∃ (Lv : G.Levels (Fl u v hg)) (KD : Formalism.L2.G.Cmp.KerData (w.D Z) t.cmp (w.tw Z) u v hg Lv),
        KD.lam = E.lam v ∧
        ThAtServed (Formalism.L2.G.Cmp.kerAtP_of t.Gt KD) E ∧
        Formalism.L2.Herm.SymmetricKernelCompatibleAtPlace t.full.1.base.toHermColsCh t.full.1.g u v hg (Formalism.L2.G.Cmp.kerAtP_of t.Gt KD) ∧
        Formalism.L2.Herm.GIwPos u v hg (Formalism.L2.G.Cmp.kerAtP_of t.Gt KD) := by
  first | exact @GlobalTheory.Mem.Top.KerOne.kerData_at_served | exact GlobalTheory.Mem.Top.KerOne.kerData_at_served | (intros; apply GlobalTheory.Mem.Top.KerOne.kerData_at_served <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MtOfFactors

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.Mem.Col2.TC

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : Later B (I.cols l))

def latSD (u : B.Word) (a : I.ι) (i : ℕ) (c : (I.stp u a i).Cl) : (letI := B.host.cmStar; SDLat B.host.E (B.R.N i)) :=
  letI := B.host.cmStar
  ⟨((I.stp u a i).rep c).1.1.deco.1.N, GlobalTheory.SeamSelfDual.isSDLat_of_isSdLat _
    ⟨((I.stp u a i).rep c).1.1.deco.2.lat, ((I.stp u a i).rep c).1.1.deco.2.uni⟩⟩

def mtOf (a : I.ι) (j : ℕ) : (I.rec7 l Z).Dt →* ℂˣ :=
  if 1 ≤ j ∧ j ≤ B.R.m then
    (I.rec7 l Z).muTil j * (show (I.rec7 l Z).Dt →* ℂˣ from tildeQ B.host I.SQ (I.xi a)) else (I.rec7 l Z).muTil j

theorem mtOf_factors (u : B.Word) (a : I.ι) : GL3Theta.CarriesTupleCharacters (I.rec7 l Z) ((I.rec7 l Z).chTw u a) (I.mtOf l Z a)
    (fun i c => detPt B.host I.SQ ((I.stp u a i).rep c).1.1) := by
  intro i hi
  have hm : 1 ≤ i + 1 ∧ i + 1 ≤ B.R.m := ⟨by omega, hi⟩
  refine ⟨fun c => ?_, fun c => ?_⟩
  · show ((rhoAt I.SQ I.C (I.xi a) i _ : ℂˣ) : ℂ) = _
    rw [rhoAt_eq]
    simp only [GL3Theta.rhoOf, mtOf, if_pos hm]
    rfl
  · show ((rhoAt' I.SQ I.C (I.xi a) i _ : ℂˣ) : ℂ) = _
    rw [rhoAt'_eq]
    simp only [GL3Theta.rhoOf', mtOf, if_pos hm]
    rfl

def objOf (hok : I.Ok) (Qp : I.ι → Finset ℕ) (u : B.Word) (a : I.ι) : GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a) :=
  letI := B.host.cmStar
  { mt := I.mtOf l Z a
    L0 := fun i => ⟨GlobalTheory.Glob.IntegralWittCoefficients.Model.stdLat _ _, GlobalTheory.Glob.IntegralWittCoefficients.Model.isSDLat_std _ _⟩
    lattice_integral_coordinates := fun i x => GlobalTheory.Glob.IntegralWittCoefficients.Model.mem_stdLat x
    lat := fun i c => I.latSD u a i c
    dt := fun i c => detPt B.host I.SQ ((I.stp u a i).rep c).1.1
    dt_lat := fun i c => GlobalTheory.Mem.Col2.mk_detPt_eq_relDetQ B.R B.host _ _ _ _ I.SQ _ (GlobalTheory.Mem.LevTwist.levOk_twists B X I hok).1
    c13 := I.mtOf_factors l Z u a
    frm := fun i y => y.1
    frm_inj := fun i _ => Subtype.val_injective
    frm_range := fun i _ f => ⟨by
        rintro ⟨y, rfl⟩ τ
        exact (y.2 τ).ne_zero, fun h => ⟨⟨f, fun τ => isUnit_iff_ne_zero.2 (h τ)⟩, rfl⟩⟩
    frm_de := fun _ _ _ _ => rfl
    dgen := I.J.cD
    dgen_gen := hok.amb_ok.dgen
    S := insert (B.T u) ({B.host.g 0, B.host.g 1} ∪ Qp a)
    Th := fun i c c' => I.th u a i c.1 c'.1 ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c') }

theorem objOf_unf (hok : I.Ok) (Qp : I.ι → Finset ℕ) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) :
    UnfIsAll (I.objOf l Z hok Qp u a) i := by
  intro c c' Q
  have e0 : ∀ (n : ℕ) (P : MvPolynomial (GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N n)) ℂ),
      frPoly (I.objOf l Z hok Qp u a) n P = fnOf (Gr B.fields.emb B.embLL (B.R.N n)) 0 1 P := by
    intro n P
    funext y
    simp [frPoly, GL3Theta.evFr, fnOf, objOf]
    rfl
  have e1 : frInv (I.objOf l Z hok Qp u a) i (frPoly (I.objOf l Z hok Qp u a) i Q) = Q :=
    LinearMap.congr_fun (frInv_spec (I.objOf l Z hok Qp u a) hi) Q
  show fnOf _ 0 1 (jetMap (jetC I.J.cD (I.th u a i c.1 c'.1 _ _)) 0 (polOf _ 0 (fr0 _ _ _) (frPoly (I.objOf l Z hok Qp u a) i Q))) =
    frPoly (I.objOf l Z hok Qp u a) (i + 1) (jetMap _ _ (frInv (I.objOf l Z hok Qp u a) i (frPoly (I.objOf l Z hok Qp u a) i Q)))
  have e2 : polOf (Gr B.fields.emb B.embLL (B.R.N i)) 0 (fr0 B.fields.emb B.embLL (B.R.N i))
      (frPoly (I.objOf l Z hok Qp u a) i Q) = Q :=
    (congrArg _ (e0 i Q)).trans (GlobalTheory.TilClass.polOf_fnOf_one B.fields.emb B.embLL 0 Q)
  refine (congrArg (fun P => fnOf (Gr B.fields.emb B.embLL (B.R.N (i + 1))) 0 1
    (jetMap (jetC I.J.cD (I.th u a i c.1 c'.1 ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c'))) 0 P)) e2).trans ?_
  rw [e1, e0 (i + 1)]
  rfl

theorem lift_objects : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ Qp : I.ι → Finset ℕ, ∃ O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a), I.StdO l Z Qp O ∧ ∀ u a i, i < B.R.m → UnfIsAll (O u a) i := by
  intro B X I hok _ l Z Qp
  refine ⟨I.objOf l Z hok Qp, ⟨fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩, fun u a i hi => I.objOf_unf l Z hok Qp u a i hi.le⟩

end GlobalTheory.Mem.Col2.TC

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeLayerKernelDatumTrueColumns

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Df NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl

theorem gyLay_kerT_entC : StepW Pinned fun K B f T w => ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)), V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp → ∃ (Gy : G.LatInst (w.D Z)) (ker : KerFam (w.D Z) t.Gt t.cmp (w.tw Z) Gy), GyLay K (w.D Z) t.Gt t.cmp Gy ∧ ∃ kt : KerT t.toColT Y Gy ker, ∃ (Pl : Examples₂.EntPl (w.D Z)) (Bs : Formalism.L2.Ker.PlaceMatrixFamily (w.D Z)) (h : Formalism.L2.Ker.KerEntHyp Pl kt.O Bs Y (w.tw Z)), kt.E = Formalism.L2.Ker.kerEntC Pl kt.O Bs h := by
  have hcl : StepW Pinned fun K B f T w => ∀ Z : w.Lt, ∃ c : ℕ, (∀ u, Formalism.L2.G.CloudBound (w.D Z) u c) ∧ ∀ L : SizeData₂ (w.D Z), L.sc = K.s → Val K.C K.cD K.ch L → (c : ℝ) ≤ G.cG L := GlobalTheory.T.columnChoice_cloudBound_le_cG
  refine (StepW.and hcl (StepW.of_all (q := fun K B f T w => (∀ Z : w.Lt, ∃ c : ℕ, (∀ u, Formalism.L2.G.CloudBound (w.D Z) u c) ∧
      ∀ L : SizeData₂ (w.D Z), L.sc = K.s → Val K.C K.cD K.ch L → (c : ℝ) ≤ G.cG L) → _) ?_)).trans
    (StepW.of_all fun _ _ _ _ _ _ _ h => h.2 h.1)
  intro K B f T w hO hF hP hC Z t Wt nch n Y hMu hQp
  obtain ⟨cp⟩ := hP
  obtain ⟨O, hstd, hunf⟩ := TC.lift_objects w.I w.ok w.pins w.l Z Y.Qp
  let Pl : Examples₂.EntPl (w.D Z) := Classical.choice (Formalism.BasicNotions.Examples₂.entPl_nonempty _)
  obtain ⟨Bs, hB, hok⟩ := GlobalTheory.T.trueColumnChoices_kernelDatum_adaptedBases w.I w.ok w.pins w.l Z w.l0 Y O Pl hQp hstd hunf cp.jets
  obtain ⟨vOf, Fl, htm, hw, hled⟩ := GlobalTheory.T.latticeLayer_trueColumns_intrinsic w hO hF ⟨cp⟩ Z t Wt nch n Y hMu hQp (hC Z)
  choose Lv KD hK using GlobalTheory.T.levels_kernelData_at_served_place w hO hF ⟨cp⟩ Z t Wt nch n Y hMu hQp O hstd hunf _ hok Fl htm hw
  let Y0 : G.LatInst (w.D Z) := ⟨vOf, Fl, Lv, fun _ _ _ => ⟨fun _ => 0⟩, fun _ _ _ => ⊥⟩
  exact ⟨Formalism.L2.G.Cmp.withFirst t.cmp (w.tw Z) Y0 fun u v hg =>
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      (KD u v hg).up.maps,
    Formalism.L2.G.Cmp.kerAll t.Gt t.cmp (w.tw Z) Y0 KD, ⟨Formalism.L2.G.Cmp.withFirst_vram _ _ _ _, hw,
      fun L a b c X d e g h => hled Lv _ _ L a b c X d e g h⟩, ⟨O, hstd, hunf, _, hok, fun u v hg => (hK u v hg).1,
      fun u v hg => (hK u v hg).2.1, fun u v hg => (hK u v hg).2.2.1, fun u v hg => (hK u v hg).2.2.2⟩, Pl, Bs, hB, rfl⟩

end GlobalTheory.Mem.Top.Bl
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeLayerKernelDatumTrueColumnsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Df NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_latticeLayer_kernelDatum_trueColumns : StepW Pinned fun K B f T w => ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)), V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp → ∃ (Gy : G.LatInst (w.D Z)) (ker : KerFam (w.D Z) t.Gt t.cmp (w.tw Z) Gy), GyLay K (w.D Z) t.Gt t.cmp Gy ∧ ∃ kt : KerT t.toColT Y Gy ker, ∃ (Pl : Examples₂.EntPl (w.D Z)) (Bs : Formalism.L2.Ker.PlaceMatrixFamily (w.D Z)) (h : Formalism.L2.Ker.KerEntHyp Pl kt.O Bs Y (w.tw Z)), kt.E = Formalism.L2.Ker.kerEntC Pl kt.O Bs h := by
  first | exact @GlobalTheory.Mem.Top.Bl.gyLay_kerT_entC | exact GlobalTheory.Mem.Top.Bl.gyLay_kerT_entC | (intros; apply GlobalTheory.Mem.Top.Bl.gyLay_kerT_entC <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ParametersForcedContentEqScaleAtResidueCharStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.forcedContent_eq_scale_at_residueChar : ∀ (D : D7) (L : SizeData₂ D) (j : ℕ) (v : D.what₂.places.Pl), Fval L j v = FK L.sc D j (D.what₂.places.resChar v) := by
  first | exact @GlobalTheory.Mem.Top.Bl.Fval_eq_FK | exact GlobalTheory.Mem.Top.Bl.Fval_eq_FK | (intros; apply GlobalTheory.Mem.Top.Bl.Fval_eq_FK <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstructedCoreOfAllConstructionStages

section

@[expose] public section

noncomputable section

namespace GlobalTheory.Mem.Top.Bl.CoreAsm

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl
  NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {𝒮 : Slots} {w : ColW B f T} {Z : w.Lt}

theorem fval_off (l : Lv4 𝒮 K w Z) (L : SizeData₂ (w.D Z)) (hL : L.sc = K.s) (v : B.places.Pl) (hv : v ∉ l.Wt)
    (j : ℕ) (hj : j ∈ SizeData₂.lifts (w.D Z)) : Fval L j v = 0 := by
  refine (GlobalTheory.T.forcedContent_eq_scale_at_residueChar (w.D Z) L j v).trans ?_
  rw [hL]
  rw [l.what₂.exact] at hv
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
  have hv' := fun (i : Fin (w.D Z).R.m) h => hv ⟨i, (w.D Z).plEq v, Or.inl rfl, Or.inr (Or.inr h)⟩
  have key : F0K K.s (w.D Z) ((w.D Z).plEq v) ⟨j - 1, by omega⟩ = 0 := by
    by_contra h
    exact hv' _ h
  unfold F0K at key
  simp only [Equiv.symm_apply_apply] at key
  have e : j - 1 + 1 = j := by omega
  rw [e] at key
  exact key

theorem not_mem_of_untw (l : Lv4 𝒮 K w Z) (v : B.places.Pl) (hv : (w.D Z).what₂.muAt v = (w.D Z).what₂.mu0) : v ∉ l.Wt := by
  intro hvW
  have h1 := l.what₂.mu.on v hvW
  have h2 := l.what₂.mu.tw v
  have h3 := l.what₂.mu.mu0
  have hne := (GlobalTheory.Mem.Top.TwFin.tw_fin B f T).2.1 v
  apply hne
  rw [← h2, ← h1]
  change w.I.xi ((w.D Z).what₂.muAt v) = 1
  rw [hv]
  exact h3

theorem rowLay_of (l : Lv4 𝒮 K w Z) (Y : DivX (w.D Z)) (hMj : MjAre l.what₂.r.Z Y)
    (hk : ∀ σ, Y.kapR σ = kapSharp (w.D Z)) : V4.RowLay (w.D Z) l.p0 Y :=
  { rrDef := (Formalism.MainNotions.AbsolutelyIrreducibleSpan.sharp_RRDef _).1 l.what₂.r.Z.rr
    rationalRoots_def := l.what₂.r.Z.rr0
    kap_def := l.what₂.r.Y.kap
    lam_def := l.what₂.r.Y.lam
    bu_def := l.what₂.r.Y.bu
    ft_occ := l.what₂.r.Y.occ
    untw := fun v hv j h1 h2 => l.what₂.untw v (not_mem_of_untw l v hv) j h1 h2
    idx := l.what₂.idx Y hMj
    kapR_def := hk _ }

theorem stepW_core (_h2b : StandardLattice.SiegelMassRatioCM) : ∀ 𝒮 : Slots, AmbEx 𝒮 → DivEx 𝒮 → ThEx 𝒮 →
    StepW (pinAnd (Has4 𝒮)) (HasC (BuiltE 𝒮)) := by
  intro 𝒮 hA hD hT
  have hp : StepW (pinAnd (Has4 𝒮)) Pinned := StepW.of_all fun _ _ _ _ _ _ _ h => h.1
  have hAll := hp.trans (((hA.and hD).and hT).and GlobalTheory.T.exists_latticeLayer_kernelDatum_trueColumns)
  refine (StepW.and (StepW.of_all fun _ _ _ _ _ _ _ h => h) hAll).trans (StepW.of_all ?_)
  rintro K B f T w hO hF ⟨⟨⟨pin⟩, Z, ⟨l⟩⟩, ⟨⟨hAm, hDv⟩, hTh⟩, hGy⟩
  obtain ⟨a, a0, ha⟩ := hAm Z l
  obtain ⟨Y, ⟨dv⟩, hMj, hk, hox⟩ := hDv Z l
  obtain ⟨th, ⟨tt⟩⟩ := hTh Z l
  obtain ⟨Gy, ker, hgy, kt, Pl, Bs, hh, he⟩ := hGy Z l.col l.Wt l.nch l.n Y l.what₂.mu dv.Qp
  obtain ⟨G, hG⟩ := GlobalTheory.GaugeEx.exists_isGauge (w.D Z).host.F (w.D Z).host.E (w.D Z).sp.cm
  let O : Obj2 (w.D Z) :=
    { gatT := l.col.Gt, th := th, cmp := l.col.cmp, tw := w.tw Z, Gy := Gy, errX := Formalism.L2.Herm.toErrXS l.col.full.1,
      nch := l.nch, xd := l.xd, lev := l.col.full.1.base.lev0, X := Y, p0 := l.p0, ker := ker, amb := a, amb0 := a0,
      gauge := G }
  obtain ⟨ox⟩ := hox O l.what₂ rfl rfl HEq.rfl
  let c : V4.Core K (w.st Z) f T :=
    { isOver := hO
      xi := w.I.xi
      Wt := l.Wt
      mu := l.what₂.mu
      forced := hF
      fval := fun L hL _ _ v hv j hj => fval_off l L hL v hv j hj
      O := O
      col := GlobalTheory.T.columnLayerConditions_trueColumns_laterStages B f T w Z l.col.toColT
      gatNum := (l.g Z.W Z.V Z.S Z.N).2.1
      gy := hgy
      row := rowLay_of l Y hMj hk
      mtStable := l.what₂.r.Y.stable
      th_io := tt.io
      gauge_def := hG
      real := l.real
      dsig_eq := l.dsig_eq
      del := l.del
      etaF := l.what₂.etaF
      chiT := l.chiT
      nch_tie := l.n.tie
      nch_Q := l.n.Q }
  let bt : Built 𝒮 K w Z c :=
    { pin := pin
      coh := l.coh
      g := l.g
      col := l.col
      what₂ := l.what₂
      rx := l.rx
      xi := rfl
      lev := rfl
      errX := rfl
      n := l.n
      nx := l.nx
      sx := l.sx
      ker0 := ker
      ker_eq := rfl
      ker := kt
      div := dv
      th := tt
      obj := ⟨ha, hMj, hk⟩
      ox := ox }
  exact ⟨Z, c, bt, Pl, Bs, hh, he⟩

end GlobalTheory.Mem.Top.Bl.CoreAsm

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstructedCoreOfAllConstructionStagesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_constructedCore_of_all_construction_stages : StandardLattice.SiegelMassRatioCM → ∀ 𝒮 : Slots, AmbEx 𝒮 → DivEx 𝒮 → ThEx 𝒮 → StepW (pinAnd (Has4 𝒮)) (HasC (BuiltE 𝒮)) := by
  first | exact @GlobalTheory.Mem.Top.Bl.CoreAsm.stepW_core | exact GlobalTheory.Mem.Top.Bl.CoreAsm.stepW_core | (intros; apply GlobalTheory.Mem.Top.Bl.CoreAsm.stepW_core <;> assumption)
end
end
