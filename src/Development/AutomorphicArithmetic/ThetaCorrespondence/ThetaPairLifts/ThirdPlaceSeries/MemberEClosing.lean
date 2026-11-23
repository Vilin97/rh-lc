module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotGeoClFalse
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AmbExOfRx
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberOfConstructionStepsSecondPass
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
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaDataTrueRowsColumnsAllCompatibleStatement
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MovedReadingSameMapsBaseReadingAgrees
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupPinsOfMuIsW
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CdScaleEqCdScaleOf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SecondChernDegreeVanishesTrueSurfaces
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryHyperplaneVolumeRatioSiegelWeil
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VolumesEqMassesOfUnfold
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsSPackIntegrable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelThreeToFour
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSStageTrue
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GapHypOfNodes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SizesEqCount
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSStageUnconditional

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberOfConstructionStepsSecondPassStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl


theorem _root_.GlobalTheory.T.exists_member_of_construction_steps_secondPass : GlobalTheory.NT.RayField → GlobalTheory.Published.PrincipalIdealSt → GlobalTheory.Published.CMCurveGoodOutsidePrimeSt → StandardLattice.SiegelMassRatioCM →
    ∀ 𝒮 𝒮' : Slots, StepW Start (Has3 𝒮) → StepW (pinAnd (Has3 𝒮)) (Has4 𝒮) → AmbEx 𝒮 → DivEx 𝒮 → ThEx 𝒮 →
      ExportF KPx (IsBuiltE 𝒮) →
      Pass KPx (IsBuiltE 𝒮) (fun K B f T => ∃ w : ColW B f T, Start K B f T w ∧ Has3 𝒮' K B f T w) →
      StepW (pinAnd (Has3 𝒮')) (Has4 𝒮') → AmbEx 𝒮' → DivEx 𝒮' → ThEx 𝒮' →
      (∀ K B f T w Z c, BuiltE 𝒮' K B f T w Z c → GoodE 𝒮 K B f T w Z c ∧ DQ.TwAllAt (w.D Z) c.O.nch c.O.xd) → MemberE 𝒮 := by
  first | exact @GlobalTheory.Mem.Top.Bl.memberE_of_steps2 | exact GlobalTheory.Mem.Top.Bl.memberE_of_steps2 | (intros; apply GlobalTheory.Mem.Top.Bl.memberE_of_steps2 <;> assumption)

end GlobalTheory.Mem.Top.Bl
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PublishedInputsImplyConclusion

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw GlobalTheory.ShFam
open Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.Mem.Th

namespace GlobalTheory.Mem.Top.Closing

theorem divEx_geoCl (h1 : GlobalTheory.NT.RayField) (h2 : GlobalTheory.Published.PrincipalIdealSt) (h3 : GlobalTheory.Published.CMCurveGoodOutsidePrimeSt)
    (R : RPosition) (N : NCondition) (S : SPosition) : DivEx ⟨R, N, S, OX (geoCl anyGeometry)⟩ := by
  have h := GlobalTheory.Mem.Top.DivRec.divEx_of_ox h1 h2 h3 ⟨R, N, S, OX anyGeometry⟩ rfl
  refine GlobalTheory.Mem.Top.Bl.StepW.trans h (GlobalTheory.Mem.Top.Bl.StepW.of_all ?_)
  intro K B f T w _ _ hw Z l
  obtain ⟨Y, hY1, hY2, hY3, hY4⟩ := hw Z
    { g := l.g, coh := l.coh, Wt := l.Wt, p0 := l.p0, what₂ := l.what₂, rx := l.rx, nch := l.nch, n := l.n, xd := l.xd,
      chiT := l.chiT, nx := l.nx, col := l.col, real := l.real, dsig_eq := l.dsig_eq, del := l.del, sx := l.sx }
  refine ⟨Y, hY1, hY2, hY3, fun O t e1 e2 e3 => ?_⟩
  obtain ⟨o⟩ := hY4 O t e1 e2 e3
  exact ⟨⟨geoCl_of o.geo, o.lam⟩⟩

theorem io_zero (𝒮 : Slots) (h : 𝒮.Rx = RX) : ∀ K B f T (w : ColW B f T) (Z : w.Lt) Wt p0 (t : RowsT K w Z Wt p0),
    𝒮.Rx K B f T w Z Wt p0 t → ∀ μ, ¬ Formalism.IndefR.RecTie.Used0 (w.D Z) μ → ∀ j, j < (w.D Z).R.m → (w.D Z).what₂.io μ j = 0 := by
  intro K B f T w Z Wt p0 t r μ hμ j _
  rw [h] at r
  exact (RXs.io r μ j hμ).1

end GlobalTheory.Mem.Top.Closing
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GoodEOfBuiltE

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw GlobalTheory.ShFam
open Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.Mem.Th
namespace GlobalTheory.Mem.Top.Closing
theorem goodE_of_builtE_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N Ng : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP)
    (hN : ∀ K B f T w Z Wt p0 t nch n xd c, Ng K B f T w Z Wt p0 t nch n xd c →
      Nonempty (N K B f T w Z Wt p0 t nch n xd c) ∧ GoodO (w.D Z) nch xd) :
    ∀ K B f T w Z c, BuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension Ng S Γ).s K B f T w Z c →
      GoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K B f T w Z c ∧ DQ.TwAllAt (w.D Z) c.O.nch c.O.xd := by
  intro K B f T w Z c hc
  obtain ⟨b, hb⟩ := hc
  obtain ⟨⟨nx⟩, hg⟩ := hN _ _ _ _ _ _ _ _ _ _ _ _ _ b.nx.2
  have ch : GlobalTheory.HeightCounting.ChoiceC (w.D Z) c.O.nch := b.nx.1.a.all.choice
  refine ⟨⟨⟨{ b with nx := ⟨b.nx.1, nx⟩ }, hb⟩, hg⟩, fun v hv => ⟨ch.conj v hv, ch.sd_conj v hv⟩, ?_⟩
  obtain ⟨I, hI, hI1, -⟩ := hg.tw
  refine ⟨I.N0, I.S, ?_⟩
  rcases I with ⟨E, N0, S'⟩
  dsimp only at hI
  subst hI
  exact hI1
end GlobalTheory.Mem.Top.Closing
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StepOf

section

@[expose] public section



section
noncomputable section
namespace GlobalTheory.Mem.SRe.UpS
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.L2.DIV
  Formalism.L2.SG.RowDict Formalism.L2.SG.ConcreteSettingExists Formalism.MainNotions Formalism.L2.Forms MeasureTheory NumberField IsDedekindDomain
  GlobalTheory.EX GlobalTheory.Mem GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}

theorem exists_late_level_of_gap {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (hS : p.S = SExt.none) (hM : LevelThreeCondition p.s) (hN : SatNew) (hR : RealOf)
    (hP : PackEx) (hV : ∀ D : D7, VolTieG D → StandardLattice.VolumeEqMass₂ D) (hE : ∀ D : D7, GlobalTheory.GLq.ESerTie D → IdempotentRealFixed D) (hO : K.Over B.toPre)
    (a : w.Lt) (l : Lv3 p.s K w a) (gap : GapHyp (Late.D a)) (hdel : a.S.s.Del = (Delv K.s K.cD : ℚ))
    (hs : a.S.s.cdScale = Vol.trueScale a.G.cd) (hd : ∀ τ, a.S.dsig τ = Vol.trueDsig B.R (B.hc τ))
    (loc : Formalism.L2.SG.Pf.LocCP.LocTied (Late.D a)) : ∃ b : w.Lt, Nonempty (Lv4 p.s K w b) := by
  obtain ⟨vt, -, ⟨col⟩⟩ := l.g a.W a.V a.S a.N
  have col₀ : ColT w a := col.toColT
  obtain ⟨P, hI⟩ := hP (Late.D a) (fun u => (col₀.C.forms u).to0) gap loc
  have real₀ : RealTied (Late.D a) := (by with_unfolding_all exact ((real_of hR a l.g hs hd) :))
  have dstar : (Late.D a).what₂.Dstar = StandardLattice.DstarD (Late.D a) := (sizes_eq_count K (Late.st a) hO (hV _ real₀.vol) hd).2
  have e0 : IdempotentRealFixed (Late.D a) := hE _ (l.what₂.grp.eSerTie a.V a.S a.G)
  obtain ⟨Zs, H⟩ := hN B w.C a (pkOf l.what₂) _ P gap hI loc real₀ dstar e0 (rowHyp_pkOf l.what₂)
  let b : w.Lt := upL a (reSt a Zs) (fun u => (a.V.div.Nu u).L) a.V.div.h
  obtain ⟨l', e⟩ := hM K B f T w a l (reSt a Zs) (fun u => (a.V.div.Nu u).L) a.V.div.h
  obtain ⟨-, -, ⟨col'⟩⟩ := l'.g b.W b.V b.S b.N
  have col₁ : ColumnDataSplitPrimes K w b := col'
  obtain ⟨s⟩ := sat_col a col₀ (pkOf l.what₂) Zs H _ _ col₁.toColT
  have s' : SX K B f T w b l'.Wt l'.p0 l'.what₂ col₁.toColT := by
    rw [sx_eq l'.what₂ col₁.toColT, e]
    exact s
  have x : p.S K B f T w b l'.Wt l'.p0 l'.what₂ col₁.toColT s' := by
    rw [hS]
    exact PUnit.unit
  exact ⟨b, ⟨⟨l', col₁, real_of hR b l'.g ((by with_unfolding_all exact (hs :))) ((by with_unfolding_all exact (hd :))), (by with_unfolding_all exact (hd :)), (by with_unfolding_all exact (hdel :)), ⟨s', x⟩⟩⟩⟩

theorem pin_has3_to_has4_of_sat_new {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (hS : p.S = SExt.none) (hM : LevelThreeCondition p.s) (hN : SatNew) (hR : RealOf)
    (hP : PackEx) (hV : ∀ D : D7, VolTieG D → StandardLattice.VolumeEqMass₂ D) (hE : ∀ D : D7, GlobalTheory.GLq.ESerTie D → IdempotentRealFixed D) :
    StepW (pinAnd (Has3 p.s)) (Has4 p.s) := by
  refine Step.of_evG ((evG_of_ev GlobalTheory.Mem.Top.NodeGap.ev_gapHyp).imp fun K _ _ _ _ gap B f T hO _ _ _ w => ?_)
  rintro ⟨-, Z, ⟨l⟩⟩
  obtain ⟨S, hdel, hs, hd, loc⟩ := GlobalTheory.Mem.SProv.exists_sStage_true K B w.C Z.W Z.G.cd hO (SpectralModel.colsPos_of Z.S) (SpectralModel.rows_le_of Z.S)
  obtain ⟨l₀, -⟩ := hM K B f T w Z l S (fun u => (Z.V.div.Nu u).L) Z.V.div.h
  exact _root_.GlobalTheory.Mem.SRe.UpS.exists_late_level_of_gap p hS hM hN hR hP hV hE hO _ l₀ (gap _ hO) hdel hs hd ((by with_unfolding_all exact ((loc (upL Z S (fun u => (Z.V.div.Nu u).L) Z.V.div.h).V Z.N Z.G) :)))
end GlobalTheory.Mem.SRe.UpS
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelThreeToFour

section

@[expose] public section



section
section
noncomputable section
namespace GlobalTheory.Mem.SRe.UpS
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.L2.DIV
  Formalism.L2.SG.RowDict Formalism.L2.SG.ConcreteSettingExists Formalism.MainNotions Formalism.L2.Forms MeasureTheory NumberField IsDedekindDomain
  GlobalTheory.EX GlobalTheory.Mem GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
theorem has4_of_has3_of_sExt_none : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → Vol.DiscreteSeriesExist → Vol.FormalDegreeFormula₂ → StandardLattice.SiegelMassRatioCM → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), p.S = SExt.none → LevelThreeCondition p.s → StepW (pinAnd (Has3 p.s)) (Has4 p.s) :=
  fun h1 h2 h3 h4 h5 hW hD hF _ _ p hS hM =>
    pin_has3_to_has4_of_sat_new p hS hM
      (satOfDiscreteSeries h1 h2 h3 h4 h5) (realOf hD hF)
      (_root_.GlobalTheory.Mem.SRe.exists_sPack_integrable_alt hW h5)
      (GlobalTheory.Mem.VolMass.volumes_eq_masses_of_unfold
        (GlobalTheory.VolRatioFromSiegelWeil.volumeRatio hW))
      goodIdempotent_real_of_harishChandra_series
end GlobalTheory.Mem.SRe.UpS
end
end
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.SRe

theorem _root_.GlobalTheory.T.has4_of_has3_of_lv3Mv : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → Vol.DiscreteSeriesExist → Vol.FormalDegreeFormula₂ → StandardLattice.SiegelMassRatioCM → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), p.S = SExt.none → LevelThreeCondition p.s → StepW (pinAnd (Has3 p.s)) (Has4 p.s) :=
  _root_.GlobalTheory.Mem.SRe.UpS.has4_of_has3_of_sExt_none
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemberEClosing

section

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw GlobalTheory.ShFam
open Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.Mem.Th
namespace GlobalTheory.Mem.Top.Closing
theorem memberE_closing_alt_alt : GlobalTheory.NT.RayField → GlobalTheory.Published.PrincipalIdealSt → GlobalTheory.Published.CMCurveGoodOutsidePrimeSt → GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → Vol.DiscreteSeriesExist → Vol.FormalDegreeFormula₂ → StandardLattice.SiegelMassRatioCM → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → (∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε lam σ) → (∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), Formalism.MainNotions.S.IsDS ε lam σ → Formalism.MainNotions.S.IsDS ε lam σ' → ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ v, U (σ g v) = σ' g (U v)) → (∀ (p q : ℕ) (T : GrpData p q) (lam : Ix p q → ℚ), IsParam lam → ∃ R : DSRep T, HasParam R lam) → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N Ng : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL), StepW Start (Has3 (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry)).s) → LevelThreeCondition (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry)).s → LevelThreeCondition (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension Ng SExt.none (geoCl anyGeometry)).s → ExportF KPx (IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry)).s) → Pass KPx (IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry)).s) (fun K B f T => ∃ w : ColW B f T, Start K B f T w ∧ Has3 (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension Ng SExt.none (geoCl anyGeometry)).s K B f T w) → (∀ K B f T w Z Wt p0 t nch n xd c, Ng K B f T w Z Wt p0 t nch n xd c → Nonempty (N K B f T w Z Wt p0 t nch n xd c) ∧ GoodO (w.D Z) nch xd) → MemberE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry)).s := by
  intro p1 p2 p3 s1 s2 s3 s4 s5 s6 s8 s9 pv t1 t2 t3 t4 t5 t6 t7 hL N Ng h3 mv mv' ex ps hN
  exact GlobalTheory.T.exists_member_of_construction_steps_secondPass p1 p2 p3 pv (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry)).s (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension Ng SExt.none (geoCl anyGeometry)).s h3
    (_root_.GlobalTheory.T.has4_of_has3_of_lv3Mv s1 s2 s3 s4 s5 s6 s8 s9 pv hL (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry)) rfl mv)
    (GlobalTheory.AmbCrd.ambEx_of_rx _ rfl) (divEx_geoCl p1 p2 p3 _ _ _)
    (GlobalTheory.T.exists_thetaData_trueRowsColumns_allCompatible t1 t2 t3 t4 t5 t6 t7 _ (io_zero _ rfl)) ex ps
    (_root_.GlobalTheory.T.has4_of_has3_of_lv3Mv s1 s2 s3 s4 s5 s6 s8 s9 pv hL (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension Ng SExt.none (geoCl anyGeometry)) rfl mv')
    (GlobalTheory.AmbCrd.ambEx_of_rx _ rfl) (divEx_geoCl p1 p2 p3 _ _ _)
    (GlobalTheory.T.exists_thetaData_trueRowsColumns_allCompatible t1 t2 t3 t4 t5 t6 t7 _ (io_zero _ rfl))
    (_root_.GlobalTheory.Mem.Top.Closing.goodE_of_builtE_alt hL N Ng SExt.none (geoCl anyGeometry) hN)
end GlobalTheory.Mem.Top.Closing
end
end
end
end
