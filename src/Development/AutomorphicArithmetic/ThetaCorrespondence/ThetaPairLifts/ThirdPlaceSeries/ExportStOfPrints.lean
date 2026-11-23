module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AdaptExStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BaseGeOfStepsStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CanExHoldsStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CanProjStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConjBaseOfSteps
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
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsSeriesStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LowAtHolds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemBlockTriangularTwoBlockSizesOfLe
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemLevelTypeFormsOfUniversalCoeffReading
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Links2OfRowsStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwAdm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistCharacterOfArtin
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwGeStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwLeStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwOneOfStepsStatement

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConjBaseOfStepsStatement

section

@[expose] public section



section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp

theorem _root_.GlobalTheory.T.conjBase_of_ray_class_field_and_seriesRat : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.ConjugateBase := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.conjBase_of_cusp_decay_and_reciprocity | exact _root_.GlobalTheory.BigOn.Exp.conjBase_of_cusp_decay_and_reciprocity | (intros; apply _root_.GlobalTheory.BigOn.Exp.conjBase_of_cusp_decay_and_reciprocity <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LowAtHoldsStatement

section

@[expose] public section



section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp

theorem _root_.GlobalTheory.T.lowAt : _root_.GlobalTheory.BigOn.Exp.LowerBoundAtPlace := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.lowAt_holds_alt | exact _root_.GlobalTheory.BigOn.Exp.lowAt_holds_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.lowAt_holds_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RecSideOfTwAdm

section

@[expose] public section



section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
set_option autoImplicit false
noncomputable section
open scoped TensorProduct


namespace GlobalTheory.BigOn.Exp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem recSide_of_twAdm_alt : _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.RecursiveSide := by
  intro hA
  refine Formalism.MainNotions.Closed.imp hA fun Fm CH _ ⟨x0, H⟩ => ⟨x0, fun x hx h0 i p hr hm w hw j Z hRat => ?_⟩
  obtain ⟨hOK, -, -⟩ := H x hx h0 i p hr hm w hw j
  have hL := _root_.GlobalTheory.T.links2_of_single_index_twisted _ _ _ _ _ _ _ _ _ _ p hr hm.1
  have hU : p.R.toRealDat.LUnif := hL.2.2.1
  have hW : p.R.toRealDat.models_HW := p.charW.base.models.HW
  have T := Z.tie ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)
  have hAR := GlobalTheory.SeriesTie.actRead_realRd _ _ _ _ _ _ _ p.R p.cG p.Sx p.nexp p.v₀ Z.ρ Z.good
    ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) (Z.ν ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) Z.pin hU hW
  have hS : Formalism.MainNotions.IntegralHeckeForms.SgJ (Fm.D x i).nexp (twE Fm x hx i) ((Fm.ex x hx i).nch.twI w) ((j : ℕ) + 1) ((Fm.ex x hx i).nch.sd w) =
      Set.univ := by
    refine Set.eq_univ_of_forall fun a => hr.ties.data _ j _ a fun u => ?_
    have hm0 := GlobalTheory.ExportType.thetaSeriesDatum_mem_levelTypeForms T hAR a
    exact sub_eq_zero.1 (LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 hm0 u))
  have hb : baseSet (rdAt p w j Z.good (Z.ν ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w))) =
      Set.range ((Fm.D x i).nexp.th ((Fm.ex x hx i).nch.twI w) ((j : ℕ) + 1) ((Fm.ex x hx i).nch.sd w)) :=
    (range_th T).symm
  have ht : (⋃ a ∈ Formalism.MainNotions.IntegralHeckeForms.SgJ (Fm.D x i).nexp (twE Fm x hx i) ((Fm.ex x hx i).nch.twI w) ((j : ℕ) + 1)
        ((Fm.ex x hx i).nch.sd w),
        (Fm.D x i).nexp.thPsi _ _ _ ((Fm.ex x hx i).nch.k' w) ((Fm.ex x hx i).nch.Q w)
          (GlobalTheory.TwistIndex.chosenChar (Fm.ex x hx i).nch w) a) =
      twSet Z.good (rdAt p w j Z.good (Z.ν ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w))) ((Fm.ex x hx i).nch.k' w)
        ((Fm.ex x hx i).nch.Q w) (GlobalTheory.TwistIndex.chosenChar (Fm.ex x hx i).nch w) := by
    rw [hS, Set.biUnion_univ, iUnion_thPsi T hOK]
    ext y
    exact ⟨fun ⟨s, h, P, hd, _, hy⟩ => ⟨s, h, P, hd, hy⟩, fun ⟨s, h, P, hd, hy⟩ => ⟨s, h, P, hd, hRat.1 s h P hd, hy⟩⟩
  refine ⟨?_, ?_⟩
  · unfold baseLat
    rw [hb, hS, Set.image_univ, ← Set.range_comp]
    rfl
  · unfold twLat
    rw [ht]
end GlobalTheory.BigOn.Exp
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RecSideOfTwAdmStatement

section

@[expose] public section



section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp

theorem _root_.GlobalTheory.T.reciprocity_side_of_twAdm : _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.RecursiveSide := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.recSide_of_twAdm_alt | exact _root_.GlobalTheory.BigOn.Exp.recSide_of_twAdm_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.recSide_of_twAdm_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TieRatOf

section

@[expose] public section



section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
namespace GlobalTheory.BigOn.Exp
theorem tieRat_of_alt (hA : _root_.GlobalTheory.BigOn.Exp.TwAdmAlt) (hR : _root_.GlobalTheory.BigOn.Exp.ConditionAtPlace) : _root_.GlobalTheory.BigOn.Exp.CompatibilityRational := by
  unfold _root_.GlobalTheory.BigOn.Exp.CompatibilityRational _root_.GlobalTheory.BigOn.Exp.TwistConditions _root_.GlobalTheory.BigOn.AtPtsAlt at *
  refine (Formalism.MainNotions.Closed.and hA hR).imp fun Fm CH _ h => ?_
  obtain ⟨x0, hx0⟩ := h.1.and h.2
  refine ⟨x0, fun x hx hle i p hp hm w hw j Z => ?_⟩
  obtain ⟨hA', hR'⟩ := hx0 x hx hle i p hp
  have hrow := hR' hm w hw j Z.ρ Z.good Z.pin (levelOf_exportTie Z)
  have hs := Z.scalar ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)
  have hrat := hs.rat hrow
  obtain ⟨ν, hn, -⟩ := hrow
  obtain ⟨hok, hcl, -⟩ := hA' hm w hw j
  exact ⟨hs.norm ⟨ν, hn⟩, hrat.1, fun s h P hd => hrat.2.1 _ _ _ hok hcl s h P hd⟩
end GlobalTheory.BigOn.Exp
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TieRatOfStatement

section

@[expose] public section



section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp

theorem _root_.GlobalTheory.T.tieRat_of_twAdm_and_at : _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.ConditionAtPlace → _root_.GlobalTheory.BigOn.Exp.CompatibilityRational := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.tieRat_of_alt | exact _root_.GlobalTheory.BigOn.Exp.tieRat_of_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.tieRat_of_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwAdmStatement

section

@[expose] public section



section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp

theorem _root_.GlobalTheory.T.twist_admissible' : _root_.GlobalTheory.BigOn.Exp.TwAdmAlt := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.twAdm_alt | exact _root_.GlobalTheory.BigOn.Exp.twAdm_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.twAdm_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwChrOfTwAdm

section

@[expose] public section



section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.SeriesTie
namespace GlobalTheory.TwistChr
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 10000] GlobalTheory.GalChar.isTorsionFree_field


section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz} {w : D.what₂.places.Pl}
end Point
theorem twChr_of_twAdm_alt : GlobalTheory.Published.GlobalArtinReciprocity → _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.TwistCharacter := fun _ h =>
  Closed.imp h fun _ _ _ ⟨x0, H⟩ => ⟨x0, fun x hx h0 i p r hm w hw j _ hρ hA =>
    have hw' := (p.tw_iff w).1 hw
    have h1 := chrEq_tw hm.2.2 hw' (H x hx h0 i p r hm w hw j).1 hρ hA
    ⟨h1, xi_eq hw' hA.1 j _ h1⟩⟩
end GlobalTheory.TwistChr
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwChrOfTwAdmStatement

section

@[expose] public section



section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp

theorem _root_.GlobalTheory.T.twist_character_of_artin' : GlobalTheory.Published.GlobalArtinReciprocity → _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.TwistCharacter := by
  first | exact @_root_.GlobalTheory.TwistChr.twChr_of_twAdm_alt | exact _root_.GlobalTheory.TwistChr.twChr_of_twAdm_alt | (intros; apply _root_.GlobalTheory.TwistChr.twChr_of_twAdm_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportStOfPrints

section

@[expose] public section



section
set_option autoImplicit false
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
namespace GlobalTheory.BigOn.Exp
theorem exportSt_of_hypotheses_alt (hC : GlobalTheory.Published.CuspRapidDecay) (hA : GlobalTheory.Published.GlobalArtinReciprocity)
    (hR : GlobalTheory.Published.RayClassFieldSt) (hD : GlobalTheory.Published.DiscreteSeriesCover) (hW : GlobalTheory.Published.CasselmanWallach)
    (hS : GlobalTheory.SerStd.SeriesRatS) : _root_.GlobalTheory.BigOn.ExportedStatement :=
  have tA := _root_.GlobalTheory.T.twist_admissible'
  have tC := _root_.GlobalTheory.T.twist_character_of_artin' hA tA
  have row := _root_.GlobalTheory.T.at_statement_of_low_weight_twAdm hC hA hR hS _root_.GlobalTheory.T.lowAt tA
  _root_.GlobalTheory.BigOn.Exp.InductionConditions.exportSt ⟨_root_.GlobalTheory.T.bigOn_canEx, _root_.GlobalTheory.T.bigOn_canProj, tA, row, _root_.GlobalTheory.T.tieRat_of_twAdm_and_at tA row, _root_.GlobalTheory.T.reciprocity_side_of_twAdm tA, _root_.GlobalTheory.T.adaptEx',
    _root_.GlobalTheory.T.conjBase_of_ray_class_field_and_seriesRat hC hA hR hS, _root_.GlobalTheory.T.conjTw_of_discrete_series_and_casselman_wallach hC hA hR hD hW hS tA tC, _root_.GlobalTheory.T.baseLe_of_cuspRapidDecay_artin_rayClassField hC hA hR, _root_.GlobalTheory.T.baseGe_of_cuspRapidDecay_artin_rayClassField_seriesRat hC hA hR hS,
    _root_.GlobalTheory.T.twist_upper_bound_of_prints hC hA hR tA tC, _root_.GlobalTheory.T.twist_lower_bound_of_prints hC hA hR hS tA tC⟩
end GlobalTheory.BigOn.Exp
end
end
end
