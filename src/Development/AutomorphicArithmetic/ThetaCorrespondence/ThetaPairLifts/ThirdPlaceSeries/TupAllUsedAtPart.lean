module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeometricWeakTies
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TupAllUsedPart
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Definitions.Divisors.BaseRankDimension
public import Formalism.SharpRestriction.GlobalSchurBounds.MainSup
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeUnderScaleOfGeneral
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumPin
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PtOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EvWPRowsOfRows
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EventualL6OfLowerScalarStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EvWCOnPtOfGuardedStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacementOfRealisationStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CountsIrreducibilityConstants
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartSel
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WorkingClassesFrozen
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SmallAlongStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TupAllUsedAtPart

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fc.StageZeroRow

theorem evW_of_atAll' {Bd : BdT} {q : BdP Bd} {𝒜 : FamClass} {σ : RawSel Bd 𝒜} (h : AtAll q 𝒜 σ) : Ind.EvW q 𝒜 σ :=
  Closed.of_all fun Fm _ hc => Ind.ev_of_atAll h Fm (w3_a hc)

end GlobalTheory.Fc.StageZeroRow
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EvWPRowsOfRowsStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top GlobalTheory.Fc

theorem _root_.GlobalTheory.T.eventually_pDiv_ties_of_class_sum_pin : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ (𝒜 : FamClass) (τ : RawSel _root_.GlobalTheory.Fc.Ind.PointSummands 𝒜), AtAll _root_.GlobalTheory.Fc.Ind.summandPrimitive 𝒜 τ → AtAll _root_.GlobalTheory.Fc.Ind.DivisorPointSummands 𝒜 τ → Ind.EvW (fun D _ _ _ => Formalism.BasicNotions.GoodFTAll D) 𝒜 τ → AtAll (fun D O c (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c) => GlobalTheory.ExportPin.ClassSumPin b.pt ∧ b.pt.CompatibilityConditions) 𝒜 τ → Ind.EvW _root_.GlobalTheory.Fc.Ind.RowPointSummands 𝒜 τ := by
  first | exact @_root_.GlobalTheory.Fc.Ind.evW_pRows_of_rows_alt | exact _root_.GlobalTheory.Fc.Ind.evW_pRows_of_rows_alt | (intros; apply _root_.GlobalTheory.Fc.Ind.evW_pRows_of_rows_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OntoAtChosen

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind GlobalTheory.BigTop
namespace GlobalTheory.Fc.Ind
theorem onto_at_chosen_alt : _root_.GlobalTheory.BigOn.SurjectiveOntoX → ∀ (𝒜 : FamClass) (σ : RawSel _root_.GlobalTheory.Fc.Ind.PointSummands 𝒜),
    (∀ (eps : ℝ) (Fm : FamP eps), 𝒜 Fm → GlobalTheory.EX.DQ.Duty7 Fm) → EvW _root_.GlobalTheory.Fc.Ind.RowPointSummands 𝒜 σ →
    EvW (fun _ _ _ b => GlobalTheory.BigOn.More b.pt) 𝒜 σ → EvWC (fun Fm => DIVinN Fm) _root_.GlobalTheory.Fc.Ind.summandNormBound 𝒜 σ :=
  fun h 𝒜 σ hD hR hM =>
    _root_.GlobalTheory.T.eventually_onPt_of_pDiv_ties_and_onPt (fun Fm => DIVinN Fm) (fun _ _ _ p => GlobalTheory.BigOn.More p)
      (fun C CH _ _ _ p => (p.S false).ON (p.N C CH)) h 𝒜 σ hD hR hM
end GlobalTheory.Fc.Ind
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OntoAtChosenStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind GlobalTheory.BigTop

theorem _root_.GlobalTheory.T.eventually_norm_bound_of_more_points : _root_.GlobalTheory.BigOn.SurjectiveOntoX → ∀ (𝒜 : FamClass) (σ : RawSel _root_.GlobalTheory.Fc.Ind.PointSummands 𝒜), (∀ (eps : ℝ) (Fm : FamP eps), 𝒜 Fm → GlobalTheory.EX.DQ.Duty7 Fm) → EvW _root_.GlobalTheory.Fc.Ind.RowPointSummands 𝒜 σ → EvW (fun _ _ _ b => GlobalTheory.BigOn.More b.pt) 𝒜 σ → EvWC (fun Fm => DIVinN Fm) _root_.GlobalTheory.Fc.Ind.summandNormBound 𝒜 σ := by
  first | exact @_root_.GlobalTheory.Fc.Ind.onto_at_chosen_alt | exact _root_.GlobalTheory.Fc.Ind.onto_at_chosen_alt | (intros; apply _root_.GlobalTheory.Fc.Ind.onto_at_chosen_alt <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartitionSelectionEvaluation

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top GlobalTheory.Fc

namespace GlobalTheory.Fc.RowsParts

variable {Bd : BdT} {𝒜 : FamClass} {σ : RawSel Bd 𝒜} {eps : ℝ} {Fm : FamP eps} {hc : 𝒜 Fm}

theorem ev_prem {p : Prop} {q : ℝ → BdP Bd} (h : p → ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ C, C0 ≤ C → Ind.Ev σ Fm hc (q C)) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ C, C0 ≤ C → Ind.Ev σ Fm hc fun D O c b => p → q C D O c b := by
  by_cases hp : p
  · obtain ⟨C0, h0, h⟩ := h hp
    refine ⟨C0, h0, fun C hC => ?_⟩
    obtain ⟨x0, h⟩ := h C hC
    exact ⟨x0, fun x hx hle i _ => h x hx hle i⟩
  · exact ⟨0, le_rfl, fun _ _ => ⟨0, fun _ _ _ _ h => absurd h hp⟩⟩

end GlobalTheory.Fc.RowsParts

namespace GlobalTheory.Fc

open RowsParts

end GlobalTheory.Fc
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowRRowsOfParts

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top GlobalTheory.Fc
namespace GlobalTheory.Fc.RowsParts
variable {Bd : BdT} {𝒜 : FamClass} {σ : RawSel Bd 𝒜} {eps : ℝ} {Fm : FamP eps} {hc : 𝒜 Fm}
end GlobalTheory.Fc.RowsParts
namespace GlobalTheory.Fc
open RowsParts
theorem row_rRows_of_parts_alt : ∀ (DR : _root_.GlobalTheory.Fc.R1.DefiniteSideType) (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition), Row Q Lk (fun 𝒜 σ => ∃ τ : _root_.GlobalTheory.Fc.CompatibleSelection σ, Ind.EvWC (fun _ => True) _root_.GlobalTheory.Fc.Ind.SmallPointSummands 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ) ∧ Ind.EvWC (fun _ => True) _root_.GlobalTheory.Fc.Ind.summandL3Bound 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ) ∧ Ind.EvWC (fun Fm => DIVinN Fm) _root_.GlobalTheory.Fc.Ind.summandNormBound 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ) ∧ Ind.EvWC (fun _ => True) _root_.GlobalTheory.Fc.Ind.summandL6Bound 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ) ∧ Ind.EvWC (fun Fm => DIVinN Fm) _root_.GlobalTheory.Fc.Ind.summandFunctionalBound 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ)) → Row Q Lk (Ind.EvW (Bd := _root_.GlobalTheory.Fc.BundleCondition) fun _ _ _ b => (b.B.Q.Rl.toCx3 b.B.Q.F).MIstar2 (b.B.Q.F.eV (b.B.Q.Rl.toCx3 b.B.Q.F).zs) b.B.Q.sEE) → Row Q Lk (Ind.EvW (Bd := _root_.GlobalTheory.Fc.BundleCondition) fun _ _ _ b => Formalism.L2.Rows.RowsHoldKap3 b.P) → Row Q Lk (Ind.EvWC (Bd := _root_.GlobalTheory.Fc.BundleCondition) (fun _ => True) fun C CH D O c b => DR D O c b C CH) → _root_.GlobalTheory.Fc.R1.SlotDefiniteRowsCondition DR Q Lk := by
  intro DR Q Lk h1 h2 h3 h4
  refine (h1.and (h2.and (h3.and h4))).imp fun 𝒜 σ _ H => ?_
  obtain ⟨⟨τ, hS, hL3, hON, hL6, hFUN⟩, hM, hK, hD⟩ := H
  have hw : ∀ {eps : ℝ} (Fm : FamP eps), GlobalTheory.Cp.D3 3 𝒜 Fm → W3 𝒜 Fm :=
    fun Fm h => (working_classes_frozen.1 𝒜 _ Fm).2.1 h
  have hall := Closed.and hS (Closed.and hL3 (Closed.and hON (Closed.and hL6 (Closed.and hFUN
    (Closed.and hM (Closed.and hK hD))))))
  refine Closed.imp (Pk.Closed.sub hall hw) fun Fm CH _ H hc => ?_
  obtain ⟨hS, hL3, hON, hL6, hFUN, hM, hK, hD⟩ := H
  have hc' := hw Fm hc
  obtain ⟨C1, p1, hS⟩ := hS hc' trivial
  obtain ⟨C2, -, hL3⟩ := hL3 hc' trivial
  obtain ⟨C3, -, hON⟩ := ev_prem (hON hc')
  obtain ⟨C4, -, hL6⟩ := hL6 hc' trivial
  obtain ⟨C5, -, hFUN⟩ := ev_prem (hFUN hc')
  obtain ⟨C6, -, hD⟩ := hD hc' trivial
  obtain ⟨C, k1, k2, k3, k4, k5, k6⟩ : ∃ C : ℝ, C1 ≤ C ∧ C2 ≤ C ∧ C3 ≤ C ∧ C4 ≤ C ∧ C5 ≤ C ∧ C6 ≤ C :=
    ⟨max C1 (max C2 (max C3 (max C4 (max C5 C6)))), by simp, by simp, by simp, by simp, by simp, by simp⟩
  obtain ⟨x1, hS⟩ := hS C k1
  obtain ⟨x2, hL3⟩ := hL3 C k2
  obtain ⟨x3, hON⟩ := hON C k3
  obtain ⟨x4, hL6⟩ := hL6 C k4
  obtain ⟨x5, hFUN⟩ := hFUN C k5
  obtain ⟨x6, hD⟩ := hD C k6
  obtain ⟨x7, hM⟩ := hM hc'
  obtain ⟨x8, hK⟩ := hK hc'
  obtain ⟨x0, l1, l2, l3, l4, l5, l6, l7, l8⟩ :
      ∃ y : ℝ, x1 ≤ y ∧ x2 ≤ y ∧ x3 ≤ y ∧ x4 ≤ y ∧ x5 ≤ y ∧ x6 ≤ y ∧ x7 ≤ y ∧ x8 ≤ y :=
    ⟨max x1 (max x2 (max x3 (max x4 (max x5 (max x6 (max x7 x8)))))),
      by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩
  refine ⟨C, p1.trans k1, x0, fun x hx _ hle i => ⟨?_, hD x hx (l6.trans hle) i⟩⟩
  have s := hS x hx (l1.trans hle) i
  exact
    { w1 := s.1
      covol := hL3 x hx (l2.trans hle) i
      onto := hON x hx (l3.trans hle) i
      lamLow := fun _ => hL6 x hx (l4.trans hle) i
      seeIso := s.2.1
      miStar := hM x hx (l7.trans hle) i
      fun0 := hFUN x hx (l5.trans hle) i
      pass := s.2.2
      kap := hK x hx (l8.trans hle) i }
end GlobalTheory.Fc
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TupAllUsedAtPart

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fc.StageZeroRow
theorem tupAllUsed_at_part_alt {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c) : Formalism.L2.DIV.TupAllUsed b.P :=
  _root_.GlobalTheory.Fc.FourBoundsAtBundles.tupAllUsed_part_alt b
theorem p_div_at_piece_of_div3g {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c) (h : GlobalTheory.Cp.DivRows3G b.P) : _root_.GlobalTheory.Fc.Ind.DivisorPointSummands D O c b :=
  _root_.GlobalTheory.Fc.FourBoundsAtBundles.p_div_of_div3g b h
theorem row_rRows_stage0_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.DiscreteSeriesClassification → _root_.GlobalTheory.BigOn.SurjectiveOntoX → _root_.GlobalTheory.BigTop.LambdaLowerBound₂ → ∀ (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition), _root_.GlobalTheory.Fc.R1.SlotPrimitivityCondition Q Lk → _root_.GlobalTheory.Fc.R1.SlotDivisorCondition Q Lk → _root_.GlobalTheory.Fc.RL.RowGoodnessCondition Q Lk → _root_.GlobalTheory.Fc.S0.GeometricWeakCompatibility' Q Lk → _root_.GlobalTheory.Fc.S0.CovolumeBoundThirdPlaceSeries Q Lk → _root_.GlobalTheory.Fc.S0.FunctionalCondition Q Lk → _root_.GlobalTheory.Fc.RL.RowMultiplicityCondition Q Lk → _root_.GlobalTheory.Fc.RL.RowKappaCondition Q Lk → _root_.GlobalTheory.Fc.RL.RowDefectCondition Q Lk → _root_.GlobalTheory.Fc.R1.SlotDefiniteRowsCondition _root_.GlobalTheory.Fc.DefiniteSideCondition Q Lk := by
  intro hDS hHC hCR hCW hDC hOnto hLam Q Lk hPA hDiv hGood hGeo hL3 hFun hMi hKap hDf
  refine _root_.GlobalTheory.Fc.row_rRows_of_parts_alt _root_.GlobalTheory.Fc.DefiniteSideCondition Q Lk ?_ hMi hKap hDf
  refine (((((hPA.and hDiv).and hGood).and hGeo).and hL3).and hFun).imp fun 𝒜 σ hsel H => ?_
  obtain ⟨⟨⟨⟨⟨hpa, hdv⟩, hgd⟩, hall⟩, hl3⟩, hfun⟩ := H
  choose τ hτ using fun {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) x hx i => hall Fm hc x hx i
  let τ' : _root_.GlobalTheory.Fc.CompatibleSelection σ := fun Fm hc x hx i => τ Fm hc x hx i
  have hduty : ∀ (eps : ℝ) (Fm : FamP eps), 𝒜 Fm → GlobalTheory.EX.DQ.Duty7 Fm := fun _ Fm hc =>
    let ⟨_, _, h7, _⟩ := hsel Fm hc
    (DQ.familyClass_sevenDuties_and_stableLattices _ Fm h7).1
  have hiota : AtAll _root_.GlobalTheory.Fc.Ind.IotaPointSummands 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ') := fun Fm hc x hx i => (hτ Fm hc x hx i).1
  have hppa : AtAll _root_.GlobalTheory.Fc.Ind.summandPrimitive 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ') := fun Fm hc x hx i => hpa Fm hc x hx i
  have hpdiv : AtAll _root_.GlobalTheory.Fc.Ind.DivisorPointSummands 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ') := fun Fm hc x hx i => _root_.GlobalTheory.Fc.StageZeroRow.p_div_at_piece_of_div3g _ (hdv Fm hc x hx i)
  have hcs : AtAll (fun D O c (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c) => GlobalTheory.ExportPin.ClassSumPin b.pt ∧ b.pt.CompatibilityConditions) 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ') :=
    fun Fm hc x hx i => ⟨(hτ Fm hc x hx i).2.1, (hτ Fm hc x hx i).2.2.1⟩
  have hrows : Ind.EvW _root_.GlobalTheory.Fc.Ind.RowPointSummands 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ') := _root_.GlobalTheory.T.eventually_pDiv_ties_of_class_sum_pin hDS hHC hCR hCW 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ') hppa hpdiv hgd hcs
  have hmore : Ind.EvW (fun _ _ _ b => GlobalTheory.BigOn.More b.pt) 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ') :=
    evW_of_atAll' fun Fm hc x hx i => (hτ Fm hc x hx i).2.2.2
  refine ⟨τ', ?_, hl3, _root_.GlobalTheory.T.eventually_norm_bound_of_more_points hOnto 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ') hduty hrows hmore, _root_.GlobalTheory.T.eventually_L6_bound_of_lamLow hLam 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ') hduty hrows, hfun⟩
  exact _root_.GlobalTheory.T.eventually_small_of_seeEx_primitive 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ') (fun Fm hc x hx i =>
      _root_.GlobalTheory.T.indefinite_scale_theta_nonvanishing_alt hDC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_root_.GlobalTheory.Fc.summandSelection σ τ' Fm hc x hx i).B.Q (_root_.GlobalTheory.Fc.summandSelection σ τ' Fm hc x hx i).pins
        (hiota Fm hc x hx i)) hppa
end GlobalTheory.Fc.StageZeroRow
end
end
end
