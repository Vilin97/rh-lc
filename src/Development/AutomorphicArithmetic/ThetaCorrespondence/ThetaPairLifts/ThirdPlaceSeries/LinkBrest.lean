module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TieTwRecOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FiniteTOf
public import Formalism.LocalToGlobal.Divisibility.TupUsed
public import Formalism.SharpRestriction.GlobalSchurBounds.LinkTied
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BaseRankEqOfRealisation
public import Formalism.LocalToGlobal.Divisibility.DivisibilityRemainder.RationalColumns.ColFacts
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
import Formalism.LocalToGlobal.IndefiniteReal.EvTieP
import Formalism.LocalToGlobal.IndefiniteReal.LiftCoordinatesInGoodPartFamily
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Formalism.LocalToGlobal.Divisibility.DivisibilityRemainder.RationalColumns.BuRationalOf
import Formalism.SharpRestriction.GlobalSchurBounds.QuadraticLogDerivCongr
import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeUnderScaleOfGeneral
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HbmuSlopeMaxB
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HefunFunTop
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TSelF
public import Formalism.LocalToGlobal.ClassOfRecordOfChoice
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ClassOfRecordOfChoice
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GTiedFOfC2S
public import Formalism.SharpRestriction.SmoothDesignExistence.AdmissibleTopsMertens
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.GroupLattices.LinkGConcreteNoKer
public import Formalism.SharpRestriction.AdmissibleParameterJoins.SumLogPrimeFactorsLe
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Formalism.LocalToGlobal.Divisibility.RecBridgeWire
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Formalism.LocalToGlobal.GlobalTheory.GL6.CoordMapInjective
import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
public import Formalism.LocalToGlobal.Divisibility.DivisibilityRemainder.NoColumnCase.LvlWire
import Formalism.LocalToGlobal.Divisibility.RecBridgeWire

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BurrbColFacts

section

@[expose] public section



section
noncomputable section
open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
namespace Formalism.L2.DIV.RatFullPt
section CSD
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) {G : Type} [Group G] [Fintype G]
  (r : Representation K G S.Forms) (X : Finset (G → K)) (P : Subgroup G) (ψ : P →* Kˣ)
end CSD
section Forms
variable {K : Type} [Field K] [NumberField K] [StarRing K]
end Forms
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
theorem indefinite_realisation_column_facts (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) {s : ℕ} (hOk : P.A3.fam3.Ok3 s) (hsep : P.A3.fam3.TypesSep3)
    (hP : PrimRows3 Q.Rl Q.F) (hS : (Q.Rl.toCx3 Q.F).SEEIso Q.sEE)
    (hM : (Q.Rl.toCx3 Q.F).MIstar2 (Q.F.eV (Q.Rl.toCx3 Q.F).zs) Q.sEE) : ColFacts P.S1 P.C := by
  have hC := complex_data_conditions_base_level_of_primitive_links hOk hsep Q.charW hP
  have hcols := (Q.Rl.toCx3 Q.F).exists_zeta_pairing_factors_through_periods Q.F.cr Q.F.cv (Q.F.eV (Q.Rl.toCx3 Q.F).zs) Q.sEE (hC.wf true) hC.h4pos (hC.what₂ true).1
    (hC.ratMu true) hC.jIsoR (hC.levs true).1 (hC.levs true).2.1 (hC.levs true).2.2 (definite_coordinates_in_good_part _ true)
    (EvTie.evTie_of_ok hOk Q.F _) hS hM
  have hDc : HEq (Dcf (Q.Rl.toCx3 Q.F).zs) P.Dc :=
    (congr_arg_heq Dcf Q.zs).trans (heq_of_eq Q.dc)
  have hSp : HEq (Spf (Q.Rl.toCx3 Q.F).zs) P.Sp := (congr_arg_heq Spf Q.zs).trans Q.sp
  exact colFacts_transport Q.zs hDc hSp Q.s1 Q.col
    ⟨hC.wf true, hC.h0, fun t => (Q.Rl.toCx3 Q.F).rowMat_bij Q.F.cr true (hC.what₂ true).1 (hC.ratMu true) t,
      (Classical.epsilon_spec hcols).1⟩
end Formalism.L2.DIV.RatFullPt
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BurrbPlug

section

@[expose] public section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT
namespace Formalism.L2.DIV.RatFullFam
open Formalism.L2.Top3 Formalism.L2.Top4
theorem buRat_rrFull_closed_alt (𝒜 : FamClass)
    (sel : _root_.Formalism.L2.TwistSelection 𝒜)
    (selS : _root_.Formalism.L2.Top4.SelectionSpectralCondition 𝒜 sel)
    (selP : _root_.Formalism.L2.Top4.BaseLevelTiedChoiceAlt 𝒜 sel)
    (selDH : _root_.Formalism.L2.Top3.SelectionDefiniteHeightCondition 𝒜 sel)
    (selC : _root_.Formalism.L2.Top4.ColumnChoiceCompatibleSelection 𝒜 sel selP)
    (selB : _root_.Formalism.L2.Top4.SelectionBundle 𝒜 sel selS selP selDH selC)
    (hPA : _root_.Formalism.L2.Top4.AllRealisationsPrimitive sel (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB))
    (hDivG : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.DIV.DivRows3G (selP Fm hc x hx h i).1)
    (hDcPtG : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.DIV.DcPtG (selP Fm hc x hx h i).1)
    (rRows : Closed (D3 3 𝒜) fun Fm CH => ∀ hc : D3 3 𝒜 Fm, _root_.Formalism.L2.Top4.RowsAtSelAlt sel (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) (fun Fm hc x hx h i C CH => _root_.Formalism.L2.Top4Wire2.DefRowsFAlt (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) Fm hc x hx h i C CH) (_root_.Formalism.L2.Top4.SingleMapCondition selB)
        Fm (d3_a hc) CH) :
    Closed (D3 3 𝒜) fun Fm _ => ∀ _ : D3 3 𝒜 Fm, TuSize Fm → Formalism.MainNotions.DGamSize Fm →
      (∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, (Fm.D x i).BuRational) ∧
        (∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, (Fm.D x i).RRFull) :=
  rRows.imp fun Fm CH _ h hc _ _ => by
    obtain ⟨C, _, x0, H⟩ := h hc
    have key : ∀ x ≥ max (max x0 (sel Fm (d3_a hc)).1) (Fm.x1 + 1), ∀ i : Fm.Ix x,
        (Fm.D x i).BuRational ∧ (Fm.D x i).RRFull := by
      intro x hx0 i
      have h0 : x0 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx0
      have hs : (sel Fm (d3_a hc)).1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx0
      have hx : Fm.x1 < x := lt_of_lt_of_le (by linarith) (le_trans (le_max_right _ _) hx0)
      obtain ⟨ra, _⟩ := H x hx hs h0 i
      obtain ⟨prows, hsep⟩ := hPA Fm (d3_a hc) x hx hs i
      have hok1 := (selC Fm (d3_a hc) x hx hs i).ok1
      have hU := _root_.Formalism.IndefR.LevelRealisationRankEquality.tup_all_used_of_realisation (selB Fm (d3_a hc) x hx hs i).Q
      have hR := (hDivG Fm (d3_a hc) x hx hs i).toRows hU
      have hPt := Formalism.L2.DIV.dcPt_of_G hU (hDcPtG Fm (d3_a hc) x hx hs i)
      have hF := _root_.Formalism.L2.DIV.RatFullPt.indefinite_realisation_column_facts ((_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) Fm (d3_a hc) x hx hs i) hok1 hsep prows ra.seeIso ra.miStar
      exact ⟨Formalism.L2.DIV.RatFullPt.buRational_of _ hok1 hF hR hPt (Fm.ties x i).bu_def,
        Formalism.L2.DIV.RatFullPt.rrFull_of _ hok1 hF hR⟩
    exact ⟨⟨_, fun x hx i => (key x hx i).1⟩, ⟨_, fun x hx i => (key x hx i).2⟩⟩
end Formalism.L2.DIV.RatFullFam
end
end
end
end

-- Source module: Formalism.LocalToGlobal.Divisibility.DivisibilityRemainder.AdmissibleClasses.LinkGCl

section

@[expose] public section

noncomputable section

namespace Formalism.L2.DIV.LinkGCl

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.L2.Top3

variable {eps : ℝ}

theorem admissible_tops_of_class {𝒜 : FamClass} {C0 : ℝ} (Fm : FamP eps) (hc : D3 C0 𝒜 Fm) : Formalism.MainNotions.G.Adm2F Fm :=
  admissible_tops_mertens Fm (topsF_of_chosenE Fm hc.2.1.choose_spec)

end Formalism.L2.DIV.LinkGCl

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkgLinkGCl

section

@[expose] public section



section
noncomputable section
namespace Formalism.L2.DIV.LinkGCl
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.L2.Top3
variable {eps : ℝ}
theorem gTiedF_of_sel_alt (Fm : FamP eps) (s : _root_.Formalism.L2.TwistSelectionFunctions Fm) : Formalism.L2.G.GroupCompatibilityFamily Fm :=
  _root_.Formalism.L2.gTiedF_of_C2S_alt Fm (_root_.Formalism.L2.Top3.tied_families_of_choice_alt s)
theorem closed_linkG (𝒜 : FamClass) (sel : _root_.Formalism.L2.TwistSelection 𝒜) : Closed (D3 3 𝒜) fun Fm _ => LinkG Fm :=
  Formalism.L2.G.linkG_concrete5 (D3 3 𝒜)
    (Closed.of_class fun Fm _ hc => _root_.Formalism.L2.DIV.LinkGCl.gTiedF_of_sel_alt Fm (sel Fm (d3_a hc)))
    (Closed.of_class fun Fm _ hc => admissible_tops_of_class Fm hc)
theorem closed_linkG_of_tuSize_dGamSize (𝒜 : FamClass) (sel : _root_.Formalism.L2.TwistSelection 𝒜) :
    Closed (D3 3 𝒜) fun Fm _ => ∀ _ : D3 3 𝒜 Fm, Formalism.MainNotions.TuSize Fm → Formalism.MainNotions.DGamSize Fm → LinkG Fm :=
  (_root_.Formalism.L2.DIV.LinkGCl.closed_linkG 𝒜 sel).imp fun _ _ _ h _ _ _ => h
end Formalism.L2.DIV.LinkGCl
end
end
end
end

-- Source module: Formalism.LocalToGlobal.Divisibility.DivisibilityRemainder.LinkedMeasures.SlopeId

section

@[expose] public section

noncomputable section

namespace Formalism.SlopeId

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory

theorem muZero_free {eps : ℝ} (Fm : FamP eps) : J.MuZero Fm := Formalism.L2.DIV.Wire.za_of Fm

theorem muTu_of_size {eps : ℝ} (Fm : FamP eps) (h : Formalism.MainNotions.TuSize Fm) : J.MuTu Fm := by
  obtain ⟨x0, h⟩ := h
  refine ⟨2 * |Fm.CTu|, x0, fun x hx i u => ?_⟩
  refine ((h x hx i).2 u).trans ?_
  have hb := J.th_bounds (Fm.L x i)
  have hL1 : (Fm.L x i).sc.L ≤ (Fm.L x i).sc.x := by
    unfold Scale.L
    exact J.scale_rpow_le_self_of_le_one _ (by linarith [hb.1, hb.2.1])
  have hL0 : 0 ≤ (Fm.L x i).sc.L := Real.rpow_nonneg (zero_lt_one.trans (Fm.L x i).sc.one_lt_alt).le _
  have hm : ((Fm.D x i).R.m : ℝ) ≤ 2 * (Fm.D x i).R.n := by
    have := (Fm.D x i).R.m_le_f
    unfold Ranks.n
    exact_mod_cast this
  have hm0 : (0 : ℝ) ≤ (Fm.D x i).R.m := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ (Fm.D x i).R.n := Nat.cast_nonneg _
  have hX := J.xn_le_Xpp (Fm.L x i).sc (Fm.D x i).R
  have hmL : ((Fm.D x i).R.m : ℝ) * (Fm.L x i).sc.L ≤ 2 * (Fm.L x i).sc.X'' (Fm.D x i).R.n := by
    calc ((Fm.D x i).R.m : ℝ) * (Fm.L x i).sc.L ≤ (2 * (Fm.D x i).R.n) * (Fm.L x i).sc.x :=
          mul_le_mul hm hL1 hL0 (by positivity)
      _ = 2 * ((Fm.L x i).sc.x * (Fm.D x i).R.n) := by ring
      _ ≤ 2 * (Fm.L x i).sc.X'' (Fm.D x i).R.n := by linarith
  calc Fm.CTu * (Fm.D x i).R.m * (Fm.L x i).sc.L = Fm.CTu * (((Fm.D x i).R.m : ℝ) * (Fm.L x i).sc.L) := by ring
    _ ≤ |Fm.CTu| * (((Fm.D x i).R.m : ℝ) * (Fm.L x i).sc.L) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (mul_nonneg hm0 hL0)
    _ ≤ |Fm.CTu| * (2 * (Fm.L x i).sc.X'' (Fm.D x i).R.n) := mul_le_mul_of_nonneg_left hmL (abs_nonneg _)
    _ = 2 * |Fm.CTu| * (Fm.L x i).sc.X'' (Fm.D x i).R.n := by ring

theorem muDGam_of_size {eps : ℝ} (Fm : FamP eps) (h : Formalism.MainNotions.DGamSize Fm) : J.MuDGam Fm := J.muDGam_of_fact Fm h

theorem muFG_of_full {eps : ℝ} (Fm : FamP eps) (h : NuFullF Fm) : J.MuFG Fm := by
  obtain ⟨x0, h⟩ := h
  exact ⟨x0, fun x hx i u => (h x hx i u).1⟩

theorem linkMu_of_sizes {eps : ℝ} (Fm : FamP eps) (hT : Formalism.MainNotions.TuSize Fm) (hG : Formalism.MainNotions.DGamSize Fm) (hF : J.MuFG Fm)
    (hR : J.MuRank Fm) : LinkMu Fm :=
  J.linkMu Fm (muZero_free Fm) hF hR (muTu_of_size Fm hT) (muDGam_of_size Fm hG)

theorem linkMu_of_full {eps : ℝ} (Fm : FamP eps) (hT : Formalism.MainNotions.TuSize Fm) (hG : Formalism.MainNotions.DGamSize Fm) (hNF : NuFullF Fm)
    (hR : J.MuRank Fm) : LinkMu Fm :=
  linkMu_of_sizes Fm hT hG (muFG_of_full Fm hNF) hR

end Formalism.SlopeId

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BrestFinalAll

section

@[expose] public section



section
noncomputable section
open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.Pk Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Cx Formalism.L2.Top3 Formalism.L2.Top4 Formalism.L2.RowDataTransport Formalism.L2.DIV.Arith4S
namespace Formalism.L2.DIV.RestAll
theorem bRest_all_alt (𝒜 : FamClass) (Cabs : ℝ)
    (sel : _root_.Formalism.L2.TwistSelection 𝒜)
    (selS : _root_.Formalism.L2.Top4.SelectionSpectralCondition 𝒜 sel)
    (selP : _root_.Formalism.L2.Top4.BaseLevelTiedChoiceAlt 𝒜 sel)
    (selDH : _root_.Formalism.L2.Top3.SelectionDefiniteHeightCondition 𝒜 sel)
    (selC : _root_.Formalism.L2.Top4.ColumnChoiceCompatibleSelection 𝒜 sel selP)
    (selB : _root_.Formalism.L2.Top4.SelectionBundle 𝒜 sel selS selP selDH selC)
    (hRB : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      _root_.Formalism.IndefR.IndefiniteRealisationBoundedRows (selB Fm hc x hx h i))
    (hPA : _root_.Formalism.L2.Top4.AllRealisationsPrimitive sel (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB))
    (hDivG : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.DIV.DivRows3G (selP Fm hc x hx h i).1)
    (hDcPtG : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.DIV.DcPtG (selP Fm hc x hx h i).1)
    (rRows : Closed (D3 3 𝒜) fun Fm CH => ∀ hc : D3 3 𝒜 Fm, _root_.Formalism.L2.Top4.RowsAtSelAlt sel (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) (fun Fm hc x hx h i C CH => _root_.Formalism.L2.Top4Wire2.DefRowsFAlt (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) Fm hc x hx h i C CH) (_root_.Formalism.L2.Top4.SingleMapCondition selB)
        Fm (d3_a hc) CH)
    (tie : Closed (D3 3 𝒜) fun Fm _ => RealPlaceSecondLayerConditions Fm) :
    Closed (D3 3 𝒜) fun Fm CH => ∀ hc : D3 3 𝒜 Fm, Formalism.MainNotions.TuSize Fm → Formalism.MainNotions.DGamSize Fm → RemainingDivisionBounds Fm Cabs CH := by
  have hf := _root_.Formalism.L2.DIV.FunSharpTop.closed_funSharp_thr_alt 𝒜 sel selS selP selDH selC selB hRB hPA hDivG rRows
    Formalism.L2.DIV.SlopeMaxB.EbMu Formalism.MainNotions.DIV.HookProducts.Row4C.EcHH
  have hh : Closed (D3 3 𝒜) fun Fm CH => ∀ _ : D3 3 𝒜 Fm, Formalism.MainNotions.TuSize Fm → Formalism.MainNotions.DGamSize Fm →
      LocalQuadraticParts.ComplementTwoFamily Fm → DIVinN Fm → LocalQuadraticParts.FrameNumberBoundFamily Fm Fm.Csz CH :=
    (tie.and ((_root_.Formalism.L2.DIV.LinkGCl.closed_linkG_of_tuSize_dGamSize 𝒜 sel).and hf)).imp fun Fm CH _ h hc hTu hDG c2 hN => by
      obtain ⟨CF0, hL, he⟩ := h.2.2 hc hTu hDG
      have hE := Formalism.L2.DIV.LvlWire.lvlF_of_ties Fm h.1 hTu
      have hrk := Formalism.L2.DIV.LvlWire.muRank_of_lvl Fm (by norm_num : (0 : ℝ) < 3)
        (Formalism.L2.DIV.LvlWire.proviso_of_working_class Fm hc) hE hTu
      have lMu := Formalism.SlopeId.linkMu_of_full Fm hTu hDG (Formalism.L2.DIV.LvlWire.nuFullF_of_lvl Fm hE) hrk
      exact Formalism.L2.DIV.LvlWire.hh_of_lvl Fm CH Formalism.L2.DIV.SlopeMaxB.EbMu CF0 hL hE hTu hrk (h.2.1 hc hTu hDG) lMu c2
        (_root_.Formalism.L2.DIV.SlopeMaxB.eventually_muMax_le_pow_ebMu_mul_of_tuSize (sel Fm (d3_a hc)) hTu) (he hN)
  have br := _root_.Formalism.L2.DIV.RatFullFam.buRat_rrFull_closed_alt 𝒜 sel selS selP selDH selC selB hPA hDivG hDcPtG rRows
  exact (hh.and br).imp fun Fm _ _ h hc hT hD =>
    show RemainingDivisionBounds Fm Cabs _ from
      { hh := h.1 hc hT hD, bu := (h.2 hc hT hD).1, rr := (h.2 hc hT hD).2, la := Formalism.L2.DIV.Wire.la_of Fm }
end Formalism.L2.DIV.RestAll
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkBrest

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT Formalism.L2.Top3 Formalism.L2.Top4
theorem GlobalTheory.Top.link_brest_alt : ∀ (𝒜 : FamClass)
    (sel : _root_.Formalism.L2.TwistSelection 𝒜)
    (selS : _root_.Formalism.L2.Top4.SelectionSpectralCondition 𝒜 sel)
    (selP : _root_.Formalism.L2.Top4.BaseLevelTiedChoiceAlt 𝒜 sel)
    (selDH : _root_.Formalism.L2.Top3.SelectionDefiniteHeightCondition 𝒜 sel)
    (selC : _root_.Formalism.L2.Top4.ColumnChoiceCompatibleSelection 𝒜 sel selP)
    (selB : _root_.Formalism.L2.Top4.SelectionBundle 𝒜 sel selS selP selDH selC)
    (hRB : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      _root_.Formalism.IndefR.IndefiniteRealisationBoundedRows (selB Fm hc x hx h i))
    (hPA : _root_.Formalism.L2.Top4.AllRealisationsPrimitive sel (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB))
    (hDivG : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.DIV.DivRows3G (selP Fm hc x hx h i).1)
    (hDcPtG : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.DIV.DcPtG (selP Fm hc x hx h i).1)
    (rRows : Closed (D3 3 𝒜) fun Fm CH => ∀ hc : D3 3 𝒜 Fm, _root_.Formalism.L2.Top4.RowsAtSelAlt sel (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) (fun Fm hc x hx h i C CH => _root_.Formalism.L2.Top4Wire2.DefRowsFAlt (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) Fm hc x hx h i C CH) (_root_.Formalism.L2.Top4.SingleMapCondition selB)
        Fm (d3_a hc) CH)
    (tie : Closed (D3 3 𝒜) fun Fm _ => RealPlaceSecondLayerConditions Fm), Closed (D3 3 𝒜) fun Fm CH => ∀ hc : D3 3 𝒜 Fm, TuSize Fm → DGamSize Fm → RemainingDivisionBounds Fm 2 CH :=
  fun 𝒜 sel selS selP selDH selC selB hRB hPA hDivG hDcPtG rRows tie =>
    _root_.Formalism.L2.DIV.RestAll.bRest_all_alt 𝒜 2 sel selS selP selDH selC selB hRB hPA hDivG hDcPtG rRows tie
end
end
end
