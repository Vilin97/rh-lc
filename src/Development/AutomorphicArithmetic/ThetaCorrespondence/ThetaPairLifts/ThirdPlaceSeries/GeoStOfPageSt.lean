module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCond
public import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
public import Development.AbelianVarietyTheory.Definitions.Jets.CmQuadraticFormEqAlternatingForm
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LiftWeightComplexPointEqTwist
import Development.AbelianVarietyTheory.Definitions.Divisors.RealisedChainTorusEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotOntoOfCharAlone
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasIndexBoundOfRuns
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeafDepthAllRecord
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeavesSupSpanData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunNumericalConditionsHoldAlongFamilyStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.NormComparisonConstants
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPageRunRecordSubFour
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsThresholdRunHolds
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSmallIffOpo
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ParametersOkOfLaws
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Links2OfRowsStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NumOfFjEqOfRecord

section

@[expose] public section

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn

theorem numOf_eq_ofRecord (D : D7) (L : SizeData₂ D) (Del h0 : ℕ) (h1 : D.s.Del = (Del : ℚ))
    (h2 : L.etaSz = (D.R.m : ℝ) * (h0 : ℝ)) : GlobalTheory.RunDepth.numOf D L = ofRecord D L Del h0 := by
  have hm : (D.R.m : ℝ) ≠ 0 := by
    intro h
    have := L.etaSz_pos
    rw [h2, h, zero_mul] at this
    exact lt_irrefl _ this
  have e1 : ⌊((D.s.Del : ℚ) : ℝ)⌋₊ = Del := by
    rw [h1, Rat.cast_natCast, Nat.floor_natCast]
  have e2 : ⌊LevelStarExponents.h0 L⌋₊ = h0 := by
    have : LevelStarExponents.h0 L = (h0 : ℝ) := by
      unfold LevelStarExponents.h0
      rw [h2, mul_div_cancel_left₀ _ hm]
    rw [this, Nat.floor_natCast]
  have e3 : (fun z => D.hc (GlobalTheory.RunDepth.plOf D z)) = fun z => D.hc (Formalism.BasicNotions.tauPl D z) := by
    funext z
    obtain ⟨b, t⟩ := z
    cases b <;> rfl
  unfold GlobalTheory.RunDepth.numOf ofRecord
  simp only [e1, e2, e3]

theorem numOf_Fj_eq_ofRecord :
    ∀ (D : D7) (L : SizeData₂ D) (Del h0 : ℕ), D.s.Del = (Del : ℚ) → L.etaSz = (D.R.m : ℝ) * (h0 : ℝ) → ∀ (j : ℕ) (w : HeightOneSpectrum (𝓞 D.what₂.LL)), (GlobalTheory.RunDepth.numOf D L).Fj j w = (ofRecord D L Del h0).Fj j w := by
  intro D L Del h0 h1 h2 j w
  rw [numOf_eq_ofRecord D L Del h0 h1 h2]

end GlobalTheory.BigOn
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricFromPageEstimate

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn

section Comparison₂

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem indefinitePoint_splitPartContent_eq_forcedContent (p : PtAt ex Csz) (C CH : ℝ) :
    Formalism.L2.Indef.Tree.DepthCond.ContentEqualsDatumContent ((R2 p).num (F2 p) C CH) (GlobalTheory.RunDepth.numOf D L) (fun j : Fin D.R.m => (j : ℕ) + 1) := by
  intro w j
  rw [numOf_Fj_eq_ofRecord D L p.Del p.h0 p.hDel p.hh0]
  rfl

end Comparison₂

end GlobalTheory.BigOn
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsConstantsIndexBoundHypothesesLiftWeights

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin GlobalTheory.FinalJoin2

namespace GlobalTheory.FinalJoin2

theorem hyp_concl_at_run : ∃ (CK : ℝ) (x₁ : ℝ), ∀ (D : D7) (T : Top D) (h : LawsP T) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ), (∀ j, InR D j → ParOK T EX p j) → ∀ (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D), SizesAt L → Pm.CnW = 10 → (∀ i, Real.log (D.host.g i) ≤ 9 * L.sc.L + 1) → 1000 ≤ Tp.CP → Tp.CP ^ 20 ≤ zBase L → x₁ ≤ L.sc.x → FieldSmall D L → (∀ (j : ℕ) (hj : InR D j), HypC L (recPJ h j hj) ⟨CK, 20, Tp.CP, Tp.eP, Tp.CP, Tp.eP, 7⟩ Tp.CP Tp.eP 7 0 L.Ct (scalOfP (recB (h).toLawsCore) hinj EX p (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO) (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO Tp.nP Tp.nWn (LevelStarExponents.h0 L - 4) (nusR h j (lR Tp hK j)) ∧ Concl (recPJ h j hj) (scalOfP (recB (h).toLawsCore) hinj EX p (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO) (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO (nusR h j (lR Tp hK j)) ((recPJ h j hj).rk (kaR Tp hK j) ((recB (h).toLawsCore).Mlat j (kaR Tp hK j)) * D.R.f * D.R.m * L.sc.b * L.de2)) := by
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.FinalJoin.runHolds_of_parOK
  obtain ⟨CK, hCK⟩ := GlobalTheory.FinalJoin.RecordRun.exists_pageRun_record_sub_four
  refine ⟨CK, max ((10 : ℝ) ^ 60) (x₀ 20 CK), ?_⟩
  intro D T h hinj EX p hpar L Pm Tp hK hS hC hg hCP hz hx hF j hj
  have hO : OPO L (recB h.toLawsCore) := (fieldSmall_iff_opo D T h L).1 hF
  have hP := hCK D L Pm Tp hK hS hC hg ((le_max_left _ _).trans hx) hCP hz _ _ j (recPJ h j hj) hj hO
  exact (hx₀ D T h hinj EX p hpar j hj L _ _ _ _ _ _ _ _ _ _ _ hP ((le_max_right _ _).trans hx)).2

end GlobalTheory.FinalJoin2
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsConstantsIndexBoundHypothesesLiftWeightsStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin GlobalTheory.FinalJoin2

theorem _root_.GlobalTheory.T.exists_constants_indexBound_hypotheses_liftWeights : ∃ (CK : ℝ) (x₁ : ℝ), ∀ (D : D7) (T : Top D) (h : LawsP T) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ), (∀ j, InR D j → ParOK T EX p j) → ∀ (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D), SizesAt L → Pm.CnW = 10 → (∀ i, Real.log (D.host.g i) ≤ 9 * L.sc.L + 1) → 1000 ≤ Tp.CP → Tp.CP ^ 20 ≤ zBase L → x₁ ≤ L.sc.x → FieldSmall D L → (∀ (j : ℕ) (hj : InR D j), HypC L (recPJ h j hj) ⟨CK, 20, Tp.CP, Tp.eP, Tp.CP, Tp.eP, 7⟩ Tp.CP Tp.eP 7 0 L.Ct (scalOfP (recB (h).toLawsCore) hinj EX p (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO) (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO Tp.nP Tp.nWn (LevelStarExponents.h0 L - 4) (nusR h j (lR Tp hK j)) ∧ Concl (recPJ h j hj) (scalOfP (recB (h).toLawsCore) hinj EX p (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO) (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO (nusR h j (lR Tp hK j)) ((recPJ h j hj).rk (kaR Tp hK j) ((recB (h).toLawsCore).Mlat j (kaR Tp hK j)) * D.R.f * D.R.m * L.sc.b * L.de2)) := by
  first | exact @GlobalTheory.FinalJoin2.hyp_concl_at_run | exact GlobalTheory.FinalJoin2.hyp_concl_at_run | (intros; apply GlobalTheory.FinalJoin2.hyp_concl_at_run <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunsHoldOfTies

section

@[expose] public section

set_option autoImplicit false

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn

theorem runsHold_of_ties : ∃ CK x₁ : ℝ, ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (EX : ErrX D) (r : TwoRuns J G), CoreTies L EX J R → RunsOk fw r → OwnPin r → PageNum Tp x₁ → RunsHold Tp hK EX CK r := by
  obtain ⟨CK, x₁, H⟩ := GlobalTheory.T.exists_constants_indexBound_hypotheses_liftWeights
  refine ⟨CK, x₁, ?_⟩
  intro D G _ _ Pl0 T0 A J _ R F κ v₀ fw L Pm Tp hK EX r hc ok hown hnum v h hinj
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hnum
  have hl := ok.laws v
  have hF : GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) := by
    unfold ownAt
    split_ifs
    · exact hc.field₂
    · exact hc.field₁
  refine H D _ h hinj EX (ownAt D v) ?_ L Pm Tp hK h1 h2 h3 h4 h5 h6 hc.small
  refine GlobalTheory.FinalJoin2.liftIndexParameterConditions_of_coreAndShortLaws D J _ EX _ hl.j h hl.sh rfl hc.canon hF hc.halfEX ?_
  intro j hj n
  exact ⟨hl.lvA j hj n, hown v j n hj⟩

end GlobalTheory.BigOn
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoStOfPageSt

section

@[expose] public section



section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn
section Comparison₂
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
end Comparison₂
theorem geoSt_of_pageSt_alt : _root_.GlobalTheory.BigOn.PageStatement → _root_.GlobalTheory.BigOn.GeometricStatement' := by
  intro hP
  obtain ⟨CK, xa, HR⟩ := runsHold_of_ties
  obtain ⟨xb, HL⟩ := leaves_sup_span_data CK
  obtain ⟨Cd, HD⟩ := leafDepth_all_record
  refine ((hP.and (GlobalTheory.T.runNumericalConditions_hold_along_family xa)).and (GlobalTheory.T.runNumericalConditions_hold_along_family xb)).imp fun Fm CH _ H => ?_
  obtain ⟨⟨⟨c0, hc0⟩, ⟨ya, hya⟩⟩, ⟨yb, hyb⟩⟩ := H
  refine ⟨max c0 Cd, fun c hc hbad => ?_⟩
  obtain ⟨x0, hx0⟩ := hc0 c ((le_max_left _ _).trans hc) hbad
  refine ⟨max x0 (max ya yb), fun x hx hle i p hrows hmore r O hrec => ?_⟩
  have h0 : x0 ≤ x := (le_max_left _ _).trans hle
  have ha : ya ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hle
  have hb : yb ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hle
  obtain ⟨hPg, hSz, -, -, -, -, hOb, -, -⟩ := hx0 x hx h0 i p hrows hmore r O hrec
  obtain ⟨pna, hx3, hkb, hxe, -⟩ := hya x hx ha i
  obtain ⟨pnb, -, -, -, -⟩ := hyb x hx hb i
  have hcore := hmore.2.1
  have hown := hrec.2
  have hch := (_root_.GlobalTheory.T.links2_of_single_index_twisted _ _ _ _ _ _ _ _ _ _ p hrows hmore.1).1
  have hRH := HR _ _ _ _ _ _ _ (F2 p) _ _ _ _ _ _ (Fm.ex x hx i).kap_def _ _ hcore hrec.1.ok hown pna
  obtain ⟨hSup, hSpan, hS, hData⟩ := HL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ O hrec.1 hcore hown pnb hRH hch.grp
    hch.tup.mu_conj hch.tup.mu_off hch.tup.mu_ne
  refine ⟨hSup, hSpan, hS, hData, hasIndexBound_of_runs CK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ O hrec.1 hcore hown hRH hSup hSpan
    hOb, fun C CH' => ?_⟩
  exact HD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ O hrec.1 _ hPg hSz hx3 hkb (indefinitePoint_splitPartContent_eq_forcedContent p C CH')
    ((le_max_right _ _).trans hc) (le_of_eq pna.2.1.symm) hxe
end GlobalTheory.BigOn
end
end
end
end
