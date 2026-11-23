module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
public import Formalism.SharpRestriction.GrowthBounds.TwistedLevelAgreement.StepInTwK
public import Formalism.SharpRestriction.GrowthBounds.ChartComparison
public import Formalism.SharpRestriction.GrowthBounds.ChartComparison.WtTieOf
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ExistsIsCGBases
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsChainChartLocalUnitCharacterCompatibleLeve
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
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOrthonormalStepBasisBaseLatticeChartsStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ServedPlaceNoChainPlaceOrTypePrimeOverStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnChoiceExistsStandardChainDataStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelsTwG
public import Formalism.SharpRestriction.GrowthBounds.ChartComparison.PStabEq
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StabilisesColumnBaseLatticeIffFirstFactor
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DetIntOfLevel
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUnifPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChiDValuesAndCcTop
public import Formalism.SharpRestriction.GrowthBounds.ChartRank.SiteGoodPrimeTorsion
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ValIntN
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsChainChartLocalUnitCharacterCompatibleLeveStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.G Formalism.L2.G Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.UG

theorem _root_.GlobalTheory.T.exists_chainChart_localUnitCharacter_compatible_level : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (n : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ (Fl : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.Fills ((w.D Z).gat u v hg)),
      ∀ (hfl : ∀ u v hg, (Fl u v hg).t = (w.D Z).R.t ∧ (Fl u v hg).mm = (w.D Z).R.m),
      (∀ u v hg (x : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts (w.D Z),
        ((Fl u v hg).w x j s : ℝ) = wj (w.D Z) j (t.Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ (w.D Z) j) →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∀ (hμ : (w.D Z).what₂.muAt v ≠ (w.D Z).what₂.mu0),
      ∀ (tt : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes n.tp t.C (w.tw Z)), TC.StdTw w.I w.l Z w.l0 tt →
      ∀ j (hj : j + 1 ≤ (w.D Z).R.m) (β : tt.ch.Ch u ((w.D Z).what₂.muAt v) (j + 1)),
        ∃ ψ : Formalism.L2.G.awayG (w.D Z).sp.cm.sig ((w.D Z).sp.X (j + 1)).gram
            (tt.ch.lev u ((w.D Z).what₂.muAt v) (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β).Uloc ((w.D Z).what₂.places.resChar v) →* ((w.D Z).gat u v hg).Oˣ,
          Formalism.MainNotions.G.CmpJ.UnitCharacterChartCompatibility hj (tt.forms.ch u ((w.D Z).what₂.muAt v) hμ (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β).lev (t.cmp.embW u v hg) ψ := by
  first | exact @GlobalTheory.Mem.Top.KerTwPsi.psi_tied | exact GlobalTheory.Mem.Top.KerTwPsi.psi_tied | (intros; apply GlobalTheory.Mem.Top.KerTwPsi.psi_tied <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedChainChartsHyperspecialStabiliseLattice

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.G Formalism.L2.G Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.UG

namespace GlobalTheory.Mem.Top.KerTwLv



theorem hyp_charts_tw : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (n : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ (Fl : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.Fills ((w.D Z).gat u v hg)),
      ∀ (hfl : ∀ u v hg, (Fl u v hg).t = (w.D Z).R.t ∧ (Fl u v hg).mm = (w.D Z).R.m),
      (∀ u v hg (x : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts (w.D Z),
        ((Fl u v hg).w x j s : ℝ) = wj (w.D Z) j (t.Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ (w.D Z) j) →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∀ (hμ : (w.D Z).what₂.muAt v ≠ (w.D Z).what₂.mu0),
      ∀ (tt : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes n.tp t.C (w.tw Z)), TC.StdTw w.I w.l Z w.l0 tt →
      (Formalism.L2.Forms.okQ (w.D Z) (tt.ch.Q ((w.D Z).what₂.muAt v)) v ∧
        (∀ w' ∈ Formalism.L2.Forms.badQ (w.D Z) (tt.ch.Q ((w.D Z).what₂.muAt v)), (((w.D Z).what₂.places.resChar v : ℕ) : 𝓞 (w.D Z).host.F) ∉ w'.asIdeal) ∧
        ¬ (w.D Z).what₂.places.resChar v ∣ ((w.D Z).mem u).A.T) →
      ∀ (Cd : GlobalTheory.Mem.Top.KerTwLv.ChData tt.ch t.g.herm u ((w.D Z).what₂.muAt v) v hg) j (hj : j + 1 ≤ (w.D Z).R.m) (β : tt.ch.Ch u ((w.D Z).what₂.muAt v) (j + 1)),
        Formalism.MainNotions.G.CmpJ.HypTJ ((Cd.Lc t.Gt (Fl u v hg) (hfl u v hg).1 j hj).t β) ∧
        Formalism.MainNotions.G.CmpJ.PStabEq.HypTJC ((Cd.Lc t.Gt (Fl u v hg) (hfl u v hg).1 j hj).t β) := by
  intro K B f T w _ _ _ Z t Wt nch n Y _ _ O _ _ E _ Fl hfl _ u v hg hμ tt _ hok Cd j hj β
  exact ⟨GlobalTheory.Port.hypTJ_stepLevelQ ((Cd.Lc t.Gt (Fl u v hg) (hfl u v hg).1 j hj).t β)
      (tt.ch.lev u ((w.D Z).what₂.muAt v) (j + 1) _ hj β) rfl rfl (GlobalTheory.Port.not_dvd_g hg) hok.1,
    GlobalTheory.Port.hypTJC_stepLevelQ ((Cd.Lc t.Gt (Fl u v hg) (hfl u v hg).1 j hj).t β)
      (tt.ch.lev u ((w.D Z).what₂.muAt v) (j + 1) _ hj β) rfl rfl⟩

end GlobalTheory.Mem.Top.KerTwLv
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedChainChartsHyperspecialStabiliseLatticeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.G Formalism.L2.G Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.UG

theorem _root_.GlobalTheory.T.twisted_chain_charts_hyperspecial_stabilise_lattice : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (n : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ (Fl : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.Fills ((w.D Z).gat u v hg)),
      ∀ (hfl : ∀ u v hg, (Fl u v hg).t = (w.D Z).R.t ∧ (Fl u v hg).mm = (w.D Z).R.m),
      (∀ u v hg (x : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts (w.D Z),
        ((Fl u v hg).w x j s : ℝ) = wj (w.D Z) j (t.Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ (w.D Z) j) →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∀ (hμ : (w.D Z).what₂.muAt v ≠ (w.D Z).what₂.mu0),
      ∀ (tt : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes n.tp t.C (w.tw Z)), TC.StdTw w.I w.l Z w.l0 tt →
      (Formalism.L2.Forms.okQ (w.D Z) (tt.ch.Q ((w.D Z).what₂.muAt v)) v ∧
        (∀ w' ∈ Formalism.L2.Forms.badQ (w.D Z) (tt.ch.Q ((w.D Z).what₂.muAt v)), (((w.D Z).what₂.places.resChar v : ℕ) : 𝓞 (w.D Z).host.F) ∉ w'.asIdeal) ∧
        ¬ (w.D Z).what₂.places.resChar v ∣ ((w.D Z).mem u).A.T) →
      ∀ (Cd : GlobalTheory.Mem.Top.KerTwLv.ChData tt.ch t.g.herm u ((w.D Z).what₂.muAt v) v hg) j (hj : j + 1 ≤ (w.D Z).R.m) (β : tt.ch.Ch u ((w.D Z).what₂.muAt v) (j + 1)),
        Formalism.MainNotions.G.CmpJ.HypTJ ((Cd.Lc t.Gt (Fl u v hg) (hfl u v hg).1 j hj).t β) ∧
        Formalism.MainNotions.G.CmpJ.PStabEq.HypTJC ((Cd.Lc t.Gt (Fl u v hg) (hfl u v hg).1 j hj).t β) := by
  first | exact @GlobalTheory.Mem.Top.KerTwLv.hyp_charts_tw | exact GlobalTheory.Mem.Top.KerTwLv.hyp_charts_tw | (intros; apply GlobalTheory.Mem.Top.KerTwLv.hyp_charts_tw <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedChartLevelsDeterminantMapsValues

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.G Formalism.L2.G Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.UG

noncomputable section

namespace GlobalTheory.Mem.Top.KerTwDet

theorem detTie_vals : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (n : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ (Fl : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.Fills ((w.D Z).gat u v hg)),
      ∀ (hfl : ∀ u v hg, (Fl u v hg).t = (w.D Z).R.t ∧ (Fl u v hg).mm = (w.D Z).R.m),
      (∀ u v hg (x : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts (w.D Z),
        ((Fl u v hg).w x j s : ℝ) = wj (w.D Z) j (t.Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ (w.D Z) j) →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∀ (hμ : (w.D Z).what₂.muAt v ≠ (w.D Z).what₂.mu0),
      ∀ (tt : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes n.tp t.C (w.tw Z)), TC.StdTw w.I w.l Z w.l0 tt →
      ∃ dt : ∀ j (hj : j + 1 ≤ (w.D Z).R.m) (β : tt.ch.Ch u ((w.D Z).what₂.muAt v) (j + 1)),
        Formalism.MainNotions.G.CmpJ.DetTie (tt.forms.ch u ((w.D Z).what₂.muAt v) hμ (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β).lev,
      ∀ j (hj : j + 1 ≤ (w.D Z).R.m) β cl, ∃ r : (w.D Z).what₂.LL, (w.D Z).what₂.embLL r =
        (((Formalism.MainNotions.G.CmpJ.AgreeLv.formsInTw tt.forms u ((w.D Z).what₂.muAt v) hμ j hj (dt j hj)).tw β).ch
          (((Formalism.MainNotions.G.CmpJ.AgreeLv.formsInTw tt.forms u ((w.D Z).what₂.muAt v) hμ j hj (dt j hj)).K β).y cl) : ℂ) := by
  intro K B f T w _ _ _ Z t Wt nch n Y _ _ O _ _ E _ Fl _ _ u v hg
  refine fun hμ tt _ => ⟨fun j hj β => GlobalTheory.Port.detTieOf t.full.1.base _, ?_⟩
  intro j hj β cl
  exact GlobalTheory.Port.chRat_ofChiD (GlobalTheory.Mem.ChiDVal.chiD_values_and_cc_top B f T w Z).1 _ _ _

end GlobalTheory.Mem.Top.KerTwDet
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedChartLevelsDeterminantMapsValuesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.G Formalism.L2.G Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.UG

theorem _root_.GlobalTheory.T.twisted_chart_levels_determinant_maps_values : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (n : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ (Fl : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.Fills ((w.D Z).gat u v hg)),
      ∀ (hfl : ∀ u v hg, (Fl u v hg).t = (w.D Z).R.t ∧ (Fl u v hg).mm = (w.D Z).R.m),
      (∀ u v hg (x : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts (w.D Z),
        ((Fl u v hg).w x j s : ℝ) = wj (w.D Z) j (t.Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ (w.D Z) j) →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∀ (hμ : (w.D Z).what₂.muAt v ≠ (w.D Z).what₂.mu0),
      ∀ (tt : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes n.tp t.C (w.tw Z)), TC.StdTw w.I w.l Z w.l0 tt →
      ∃ dt : ∀ j (hj : j + 1 ≤ (w.D Z).R.m) (β : tt.ch.Ch u ((w.D Z).what₂.muAt v) (j + 1)),
        Formalism.MainNotions.G.CmpJ.DetTie (tt.forms.ch u ((w.D Z).what₂.muAt v) hμ (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β).lev,
      ∀ j (hj : j + 1 ≤ (w.D Z).R.m) β cl, ∃ r : (w.D Z).what₂.LL, (w.D Z).what₂.embLL r =
        (((Formalism.MainNotions.G.CmpJ.AgreeLv.formsInTw tt.forms u ((w.D Z).what₂.muAt v) hμ j hj (dt j hj)).tw β).ch
          (((Formalism.MainNotions.G.CmpJ.AgreeLv.formsInTw tt.forms u ((w.D Z).what₂.muAt v) hμ j hj (dt j hj)).K β).y cl) : ℂ) := by
  first | exact @GlobalTheory.Mem.Top.KerTwDet.detTie_vals | exact GlobalTheory.Mem.Top.KerTwDet.detTie_vals | (intros; apply GlobalTheory.Mem.Top.KerTwDet.detTie_vals <;> assumption)
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ClsCharted1AtInTw

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.G.KAat

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ
  Formalism.MainNotions.G.CmpJ.AgreeLv
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Tw : TwForms D} {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop}
  {T : Formalism.L2.Herm.TwChTied D inQ} {Hc : Formalism.L2.Herm.HermColsCh D} {J : Formalism.L2.Herm.TwChJointS T Hc}
  {F : ∀ u, FormsTiedSym D u (Hc.Ch u) (Hc.chOf u)}
  {X0 : Formalism.L2.Herm.Herm0 D} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}

def atInTw (W : TwFormsTiedS D Tw T J F) (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0) {w : D.what₂.places.Pl}
    {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}
    (dt : ∀ j (hj : j + 1 ≤ D.R.m) β, DetTie (W.ch u μ hμ (j + 1) (one_le j) hj β).lev)
    (Lc : ∀ j (_ : j + 1 ≤ D.R.m), LocIn X0 u w h Lv j (T.Ch u μ (j + 1))) : AtIn X0 Tw u μ w h Lv where
  Fo := fun j hj => formsInTw W u μ hμ j hj (dt j hj)
  Lc := Lc

variable (W : TwFormsTiedS D Tw T J F) (hμ : μ ≠ D.what₂.mu0)
  (dt : ∀ j (hj : j + 1 ≤ D.R.m) β, DetTie (W.ch u μ hμ (j + 1) (one_le j) hj β).lev)
  (Lc : ∀ j (_ : j + 1 ≤ D.R.m), LocIn X0 u w h Lv j (T.Ch u μ (j + 1)))

variable {W hμ dt Lc}

end Formalism.MainNotions.G.KAat

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComparisonDataStepsNonReferenceTuple

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.G Formalism.L2.G Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.UG

namespace GlobalTheory.Mem.Top.KerTwLv

theorem fill_of : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (n : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ (Fl : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.Fills ((w.D Z).gat u v hg)),
      ∀ (hfl : ∀ u v hg, (Fl u v hg).t = (w.D Z).R.t ∧ (Fl u v hg).mm = (w.D Z).R.m),
      (∀ u v hg (x : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts (w.D Z),
        ((Fl u v hg).w x j s : ℝ) = wj (w.D Z) j (t.Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ (w.D Z) j) →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      Formalism.MainNotions.G.CmpJ.FillTie t.Gt u v hg (Fl u v hg) := by
  intro K B f T w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg
  intro x s b hb
  have h1 := hw u v hg x s (b + 1) (by simp [SizeData₂.lifts]; omega)
  apply (Rat.cast_injective (α := ℝ))
  rw [Formalism.BasicNotions.D7.hcW_e]
  have e : (((((Fl u v hg).w x (b + 1) s : ℤ) : ℚ)) : ℝ) = (((Fl u v hg).w x (b + 1) s : ℤ) : ℝ) := by push_cast; rfl
  rw [e, h1]
  unfold wj G.kaJ wG
  rw [dite_eq_left (by omega)]
  push_cast
  ring

theorem fin_of : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (n : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ (Fl : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.Fills ((w.D Z).gat u v hg)),
      ∀ (hfl : ∀ u v hg, (Fl u v hg).t = (w.D Z).R.t ∧ (Fl u v hg).mm = (w.D Z).R.m),
      (∀ u v hg (x : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts (w.D Z),
        ((Fl u v hg).w x j s : ℝ) = wj (w.D Z) j (t.Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ (w.D Z) j) →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∀ (hμ : (w.D Z).what₂.muAt v ≠ (w.D Z).what₂.mu0),
      ∀ (tt : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes n.tp t.C (w.tw Z)), TC.StdTw w.I w.l Z w.l0 tt →
      ∀ j (hj : j + 1 ≤ (w.D Z).R.m) (β : tt.ch.Ch u ((w.D Z).what₂.muAt v) (j + 1)),
        Finite (Formalism.L2.G.compG (w.D Z).sp.cm.sig ((w.D Z).sp.X (j + 1)).gram
          (tt.ch.lev u ((w.D Z).what₂.muAt v) (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β).Uloc ((w.D Z).what₂.places.resChar v)) := by
  intro K B f T w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg hμ tt _ j hj β
  exact finite_compG (w.D Z).sp.cm.sig ((w.D Z).sp.X (j + 1)).gram _ _ _
    (fun x hx => ((tt.ch.lev u _ (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β).U_eq x).1 hx)
    (tt.ch.finite_cls u _ hμ (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β)



theorem cmpJ_data_ne : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
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
      (w.D Z).what₂.muAt v ≠ (w.D Z).what₂.mu0 →
      ∃ (Lv : G.Levels (Fl u v hg)) (I : Formalism.MainNotions.G.CmpJ.CmpJIn (w.tw Z) u ((w.D Z).what₂.muAt v) v hg Lv),
        Formalism.MainNotions.G.CmpJ.CmpJHyp t.cmp I ∧
        (∀ j hj, (I.at' j hj).C = (w.D Z).chTw u ((w.D Z).what₂.muAt v)) ∧
        (∀ j hj, Formalism.MainNotions.G.KAat.ChX (I.at' j hj).st) ∧
        (∀ j, (w.D Z).R.m ≤ j → IsEmpty (Lv.compS j)) := by
  intro K B f T w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg
  haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
  intro hμ
  obtain ⟨tt, htt⟩ := GlobalTheory.T.trueColumnChoice_exists_standardChainData w.I w.ok w.pins w.l Z w.l0 nch n.tp t.C n.xi t.std t.stdLv
  have hpl := GlobalTheory.T.served_place_no_chain_place_or_type_prime_over w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg hμ tt htt
  obtain ⟨dt, hdt⟩ := GlobalTheory.T.twisted_chart_levels_determinant_maps_values w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg hμ tt htt
  have hB := GlobalTheory.T.exists_orthonormal_step_basis_base_lattice_charts w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg hμ tt htt
  have hψ := GlobalTheory.T.exists_chainChart_localUnitCharacter_compatible_level w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg hμ tt htt
  have hfin := fin_of w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg hμ tt htt
  have hfill := fill_of w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg
  let Cd : GlobalTheory.Mem.Top.KerTwLv.ChData tt.ch t.g.herm u ((w.D Z).what₂.muAt v) v hg :=
    { B := fun j hj => (hB j hj).choose
      fr_lat := fun j hj β => (hB j hj).choose_spec.2 β
      ψ := fun j hj β => (hψ j hj β).choose
      fin := hfin }
  have hhyp := GlobalTheory.T.twisted_chain_charts_hyperspecial_stabilise_lattice w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg hμ tt htt hpl Cd
  let Zt := Formalism.MainNotions.G.KAat.atInTw (X0 := t.g.herm) tt.forms u ((w.D Z).what₂.muAt v) hμ dt (Cd.Lc t.Gt (Fl u v hg) (hfl u v hg).1)
  have A : Formalism.MainNotions.G.ChF.HypTies Zt t.Gt t.cmp :=
    { fl_t := (hfl u v hg).1
      fill := hfill
      step := fun j hj =>
        { frRat := fun β => Cd.frRat t.Gt (Fl u v hg) (hfl u v hg).1 j hj β
          sameU := fun β => Cd.sameU tt.forms hμ t.Gt (Fl u v hg) (hfl u v hg).1 dt j hj β
          hypT := fun β => (hhyp j hj β).1
          bad_p := hpl.2.1
          std := (hB j hj).choose_spec.1
          psi := fun β => (hψ j hj β).choose_spec
          chRat := hdt j hj
          hypC := fun β => (hhyp j hj β).2
          ok := hpl.1
          siteGood_prime_torsion := hpl.2.2
          Lb_eq := fun β => Cd.Lb_eq tt.forms hμ t.Gt (Fl u v hg) (hfl u v hg).1 dt j hj β } }
  exact ⟨Cd.Lv t.Gt (Fl u v hg) (hfl u v hg).1, Zt.I t.Gt, A.hyp t.g.cmp, fun j hj => rfl,
    fun j hj => (A.atHyp t.g.cmp).chX j hj, fun j hj => Cd.empty t.Gt (Fl u v hg) (hfl u v hg).1 j hj⟩

end GlobalTheory.Mem.Top.KerTwLv
end
end
