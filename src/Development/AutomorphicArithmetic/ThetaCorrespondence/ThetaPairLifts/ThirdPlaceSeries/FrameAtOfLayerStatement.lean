module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CenterEqSum
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjParahoricBlockLiftStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCompOfOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockDiagonalWithIdentity
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.G0LiftUnitaryCentralFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JumpsCardOfBuilt
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
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtMemberImp
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BlockTriAtStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePlacesNotPairwiseConjugate
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSplitReductionStandardFrameConj
import Mathlib.Tactic.NormNum.Parity
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPlaceEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DatumLevelHyperspecialOffFinitePlaces
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtMem

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
noncomputable section
namespace GlobalTheory.BlockLiftFrame
open ReciprocityTheory.Aut GlobalTheory.CenFrame
section Local
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
end Local
end GlobalTheory.BlockLiftFrame
end
theorem GlobalTheory.BlockLiftFrame.atMem_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t _ _ _ =>
  ∀ s, ∃ L : G0g (w.st Z).toD7.nd → Formalism.AUTREP.GAf (w.st Z).toD7.host.E (w.st Z).toD7.R.nV,
    GlobalTheory.PendOf.IsTypeGroupBlockLift (w.st Z).toD7 (w.st Z).toD7.R.nV L ∧ (∀ g, L g ∈ ReciprocityTheory.Aut.Umax (w.st Z).toD7.host.E (w.st Z).toD7.R.nV) ∧
    ∀ g (s' : ReciprocityTheory.Aut.SplitPlace (w.st Z).toD7.host.E) (φ : GlobalTheory.CenFrame.Os s' →+* Formalism.L2.DIV.kP s'.w), GlobalTheory.CenFrame.IsResidue s' φ →
      (s'.w ∈ t.r.z.R.Q s → ∃ y, GlobalTheory.CenFrame.IsCompOf s' (L g) y ∧ Matrix.GeneralLinearGroup.map φ y = 1) ∧
      ∀ hP : s'.w ∈ t.r.z.R.Pg, ∃ y, GlobalTheory.CenFrame.IsCompOf s' (L g) y ∧
        GlobalTheory.FrameBlockDiagonal.IsBlockDiagonalWithIdentity (t.r.z.R.eG ((t.r.z.R.eG.trans t.r.z.cG).symm g) ⟨s'.w, hP⟩) (Matrix.GeneralLinearGroup.map φ y) := by
  intro hL
  refine GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun K B f T _ w Z Wt p0 t nch n xd c hE hR hP => ?_
  intro s
  obtain ⟨plg, iso, h1, -, -, h4⟩ := t.r.z.pins.keep.grp
  exact GlobalTheory.BlockLiftFrame.exists_blockLift (w.st Z).toD7 (t.r.z.lev.is.Q_pl s) t.r.z.R.eG t.r.z.cG ⟨plg, iso, h1, h4⟩
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtMemStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev

theorem _root_.GlobalTheory.T.g0_lift_unitary_central_frame_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t _ _ _ =>
  ∀ s, ∃ L : G0g (w.st Z).toD7.nd → Formalism.AUTREP.GAf (w.st Z).toD7.host.E (w.st Z).toD7.R.nV,
    GlobalTheory.PendOf.IsTypeGroupBlockLift (w.st Z).toD7 (w.st Z).toD7.R.nV L ∧ (∀ g, L g ∈ ReciprocityTheory.Aut.Umax (w.st Z).toD7.host.E (w.st Z).toD7.R.nV) ∧
    ∀ g (s' : ReciprocityTheory.Aut.SplitPlace (w.st Z).toD7.host.E) (φ : GlobalTheory.CenFrame.Os s' →+* Formalism.L2.DIV.kP s'.w), GlobalTheory.CenFrame.IsResidue s' φ →
      (s'.w ∈ t.r.z.R.Q s → ∃ y, GlobalTheory.CenFrame.IsCompOf s' (L g) y ∧ Matrix.GeneralLinearGroup.map φ y = 1) ∧
      ∀ hP : s'.w ∈ t.r.z.R.Pg, ∃ y, GlobalTheory.CenFrame.IsCompOf s' (L g) y ∧
        GlobalTheory.FrameBlockDiagonal.IsBlockDiagonalWithIdentity (t.r.z.R.eG ((t.r.z.R.eG.trans t.r.z.cG).symm g) ⟨s'.w, hP⟩) (Matrix.GeneralLinearGroup.map φ y) := by
  first | exact @_root_.GlobalTheory.BlockLiftFrame.atMem_alt | exact _root_.GlobalTheory.BlockLiftFrame.atMem_alt | (intros; apply _root_.GlobalTheory.BlockLiftFrame.atMem_alt <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSplitReductionStandardFrameConjStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.HeightCounting GlobalTheory.CenFrame
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_split_reduction_standard_frame_conj : ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), R3.StdFrame hF P → IsBaseFrame V β Λ 1 → ∀ s : ReciprocityTheory.Aut.SplitPlace D.host.E, ∃ (φ : Os s →+* kP s.w) (b : GL (Fin n) (kP s.w)), IsResidue s φ ∧ FrameRed hn P β s φ b := by
  first | exact @GlobalTheory.FrameRedSplit.frameRed_exists | exact GlobalTheory.FrameRedSplit.frameRed_exists | (intros; apply GlobalTheory.FrameRedSplit.frameRed_exists <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFinEMemDivisorStandard

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev

noncomputable section

namespace GlobalTheory.FrameInt

theorem exists_split (D : D7) (PP : HeightOneSpectrum (𝓞 D.host.E)) (h : ¬ Formalism.IndefR.Lev.IsConjPl (D := D) PP PP) :
    ∃ s : ReciprocityTheory.Aut.SplitPlace D.host.E, s.w = PP := by
  refine GlobalTheory.RowUnitProof.exists_splitPlace_eq D PP ?_
  by_contra hs
  refine h fun c hc => ?_
  by_contra hn
  exact hs ⟨c, hc, fun y hy hm => hn ⟨y, hm, hy.trans (GlobalTheory.TypePlaces.star_eq_conj D _).symm⟩⟩

theorem frame_of {D : D7} {T : Type} (L : LevCh D T) {μ0 : T} (hL : L.Is μ0)
    (hF : D.host.F = maximalRealSubfield D.host.E) (k : Fin D.R.m) (P : principalLevelFrame.RowPsi (Vc D k) D.R.nV)
    (hP : R3.StdFrame hF P) (s : T) :
    (∀ κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV, Formalism.IndefR.Lev.finE (Vc D k) (P.ψ κ) ∈ Formalism.L2.DIV.St (L.βV k)) ∧
    ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q s → ∃ (s' : ReciprocityTheory.Aut.SplitPlace D.host.E) (φ : GlobalTheory.CenFrame.Os s' →+* Formalism.L2.DIV.kP s'.w)
      (b : GL (Fin D.R.nV) (Formalism.L2.DIV.kP s'.w)), s'.w = PP ∧ GlobalTheory.CenFrame.IsResidue s' φ ∧
        GlobalTheory.CenFrame.FrameRed (GlobalTheory.FrameBlockDiagonal.rankV D k) P (L.βV k) s' φ b := by
  have hβ : IsBaseFrame (Vc D k) (L.βV k) (L.ΛV k) 1 := by
    obtain ⟨c, hc⟩ := hL.βV k
    rwa [one_pow] at hc
  refine ⟨fun κ hκ => ?_, fun PP h => ?_⟩
  · have h1 := (hP.2 κ).1 hκ
    exact (GlobalTheory.FinZeta.LevelOff.finE_mem_St_iff hβ h1.1).2 h1
  · have hn : ¬ Formalism.IndefR.Lev.IsConjPl (D := D) PP PP :=
      h.elim (fun h => GlobalTheory.TypePlaces.not_isConjPl L.C.P L.Pg hL.Pg PP h PP h) fun h => (hL.Q_pl s PP h).2 PP h
    obtain ⟨s', hs'⟩ := exists_split D PP hn
    obtain ⟨φ, b, h1, h2⟩ := GlobalTheory.T.exists_split_reduction_standard_frame_conj D (Vc D k) D.R.nV (GlobalTheory.FrameBlockDiagonal.rankV D k) hF P (L.βV k) (L.ΛV k) hP hβ s'
    exact ⟨s', φ, b, hs', h1, h2⟩

end GlobalTheory.FrameInt

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsMoreAlt

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
noncomputable section
namespace GlobalTheory.FrameInt
theorem main_alt_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t _ _ c =>
  ∀ (ad : MtAd t.r.Y c.a.all.gal.mt) (k : Fin (w.st Z).toD7.R.m) s,
    (∀ κ ∈ ReciprocityTheory.Aut.Umax (w.st Z).toD7.host.E (w.st Z).toD7.R.nV,
      Formalism.IndefR.Lev.finE (Formalism.IndefR.Links.Vc (w.st Z).toD7 k) ((ad.PV k).ψ κ) ∈ Formalism.L2.DIV.St (t.r.z.R.βV k)) ∧
    ∀ PP, PP ∈ t.r.z.R.Pg ∨ PP ∈ t.r.z.R.Q s → ∃ (s' : ReciprocityTheory.Aut.SplitPlace (w.st Z).toD7.host.E) (φ : GlobalTheory.CenFrame.Os s' →+* Formalism.L2.DIV.kP s'.w)
      (b : GL (Fin (w.st Z).toD7.R.nV) (Formalism.L2.DIV.kP s'.w)), s'.w = PP ∧ GlobalTheory.CenFrame.IsResidue s' φ ∧
        GlobalTheory.CenFrame.FrameRed (GlobalTheory.FrameBlockDiagonal.rankV (w.st Z).toD7 k) (ad.PV k) (t.r.z.R.βV k) s' φ b :=
  fun hL => GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun K B f T _ w Z Wt p0 t nch n xd c _ _ _ ad k s =>
    frame_of (D := (w.st Z).toD7) t.r.z.R.toLevCh t.r.z.pins.char.base.lev t.r.Y.hF k (ad.PV k) (ad.std k) s
end GlobalTheory.FrameInt
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelFinEMemDivisorStandard

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev

theorem _root_.GlobalTheory.T.level_finE_mem_divisor_standard_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t _ _ c =>
  ∀ (ad : MtAd t.r.Y c.a.all.gal.mt) (k : Fin (w.st Z).toD7.R.m) s,
    (∀ κ ∈ ReciprocityTheory.Aut.Umax (w.st Z).toD7.host.E (w.st Z).toD7.R.nV,
      Formalism.IndefR.Lev.finE (Formalism.IndefR.Links.Vc (w.st Z).toD7 k) ((ad.PV k).ψ κ) ∈ Formalism.L2.DIV.St (t.r.z.R.βV k)) ∧
    ∀ PP, PP ∈ t.r.z.R.Pg ∨ PP ∈ t.r.z.R.Q s → ∃ (s' : ReciprocityTheory.Aut.SplitPlace (w.st Z).toD7.host.E) (φ : GlobalTheory.CenFrame.Os s' →+* Formalism.L2.DIV.kP s'.w)
      (b : GL (Fin (w.st Z).toD7.R.nV) (Formalism.L2.DIV.kP s'.w)), s'.w = PP ∧ GlobalTheory.CenFrame.IsResidue s' φ ∧
        GlobalTheory.CenFrame.FrameRed (GlobalTheory.FrameBlockDiagonal.rankV (w.st Z).toD7 k) (ad.PV k) (t.r.z.R.βV k) s' φ b := by
  first | exact @_root_.GlobalTheory.FrameInt.main_alt_alt | exact _root_.GlobalTheory.FrameInt.main_alt_alt | (intros; apply _root_.GlobalTheory.FrameInt.main_alt_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FrameAtOfLayer

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
namespace GlobalTheory.CenLocAt

theorem frameAt_of_layer_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t _ _ c => ∀ (ad : MtAd t.r.Y c.a.all.gal.mt) (i : (w.st Z).toD7.nd.Loc) s k, t.r.Y.tup s = (w.st Z).toD7.nd.mu i → GlobalTheory.CenLocAt.FrameAt t.r.Y t.r.z.cG k (ad.PV k) s := by
  intro hL
  refine _root_.GlobalTheory.HeightCounting.Up.Model.AtMem.at_member_imp
    (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.level_finE_mem_divisor_standard_alt hL) (_root_.GlobalTheory.T.central_frame_split_place_nontrivial_alt hL)) (_root_.GlobalTheory.T.g0_lift_unitary_central_frame_alt hL)) ?_
  intro K B f T w Z Wt p0 t nch n c h ad i s k hs
  obtain ⟨⟨hA, hB⟩, hC⟩ := h
  obtain ⟨L, hL1, hU, hLc⟩ := hC s
  obtain ⟨hSt, hFR⟩ := hA ad k s
  refine ⟨L, hL1, fun hN => ?_⟩
  refine GlobalTheory.T.exists_conj_parahoric_block_lift t.r.z.R t.r.z.cG k s (ad.PV k) L hU hSt (fun PP hPP => ?_) hLc
  obtain ⟨s', φ, b, hw, hres, hfr⟩ := hFR PP hPP
  exact ⟨s', φ, b, hw, hres, hfr, fun hP => hB ad i s k hs hN s' φ b (hw ▸ hP) hres hfr⟩
end GlobalTheory.CenLocAt
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FrameAtOfLayerStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

theorem _root_.GlobalTheory.T.frameAt_of_tup_eq_mu_at_members : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t _ _ c => ∀ (ad : MtAd t.r.Y c.a.all.gal.mt) (i : (w.st Z).toD7.nd.Loc) s k, t.r.Y.tup s = (w.st Z).toD7.nd.mu i → GlobalTheory.CenLocAt.FrameAt t.r.Y t.r.z.cG k (ad.PV k) s := by
  first | exact @_root_.GlobalTheory.CenLocAt.frameAt_of_layer_alt | exact _root_.GlobalTheory.CenLocAt.frameAt_of_layer_alt | (intros; apply _root_.GlobalTheory.CenLocAt.frameAt_of_layer_alt <;> assumption)
end
end
end
