module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowGood
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFactorisationCuspidal
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowNumAt
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EventuallyConstructedPointHostSizeNumerical
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
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteTypesViaFullHeckeAlgebraEigensystemsStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowConditionsAtCompanionFromReadings
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DsigEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFixed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankIsotEqIsotL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodIdempotentCoeffInvEqCoeff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodTypesOfTypesTrue
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedMultiplicityOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RealGroupInputsCombined

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fc.RL.LamLinked

theorem evP_params : EvP fun _ K => ∀ β : BPt K, Nonempty (ParameterChoice' β.D β.O.L) := by
  refine EvP.of_ev ⟨1, one_pos, fun eps C8 he _ he52 _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C hStd _ _ => ?_⟩⟩
  obtain ⟨c1, hN⟩ := szRow_numAt eps he he52 C hStd
  refine ⟨c1, fun cD hcD => ?_⟩
  obtain ⟨c2, hN⟩ := hN cD hcD
  refine ⟨c2, fun ch hch => ?_⟩
  obtain ⟨x0, hN⟩ := hN ch hch
  refine ⟨x0, fun K h1 h2 h3 h4 hx β => ?_⟩
  have hsc : β.O.L.sc = K.s := β.sc
  have hv : Val C cD ch β.O.L := by
    rw [← h1, ← h2, ← h3]
    exact β.p.pt_val β.val
  obtain ⟨⟨N⟩, -, -⟩ := hN _ _ (by rw [hsc, h4]) (by rw [hsc]; exact hx) hv (GlobalTheory.Plug.hostArith_bpt β)
  exact ⟨N.params⟩


end GlobalTheory.Fc.RL.LamLinked

namespace GlobalTheory.Fc.RL


end GlobalTheory.Fc.RL
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RealGroupInputsCombined

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fc.RL.LamLinked

theorem isotRank_of_wit_alt (h1 : GlobalTheory.Published.WeilRepresentationUnitaryPair) (h2 : GlobalTheory.Published.DiscreteSeriesExists)
    (h3 : GlobalTheory.Published.HarishChandraFinite) (h4 : GlobalTheory.Published.CuspRapidDecay)
    (a1 : GlobalTheory.Published.HarishChandraAnalyticity) (a2 : GlobalTheory.Published.DiscreteSeriesClassification) (a5 : GlobalTheory.Published.CuspTraceClass)
    (a6 : GlobalTheory.Published.DixmierMalliavinFactorisation) (a7 : GlobalTheory.Published.FlathFactorisation)
    (a12 : GlobalTheory.Published.ZelevinskyPolynomialRing) (a13 : GlobalTheory.Published.GeometricLemma) (hG : GlobalTheory.Published.GreenCuspidal)
    {𝒮 : Slots} {K : Ctx} (q : WPt 𝒮 K) (hH : Formalism.IndefR.Links.HostHyp (q.w.st q.Z).toD7)
    (hp : ∃ L : SizeData₂ (q.w.st q.Z).toD7, Nonempty (ParameterChoice' (q.w.st q.Z).toD7 L)) :
    Formalism.BasicNotions.Rows.IsotRank (q.w.st q.Z).toD7.what₂ := by
  have hGS : Formalism.L2.DIV.GoodStable q.x.what₂.r.z.Xg := by
    have hI := GlobalTheory.DimPartsCompare.TameTie.idemTie hG
      (GlobalTheory.DimPartsCompare.tameTie_of_typesTrue (D := (q.w.st q.Z).toD7) q.x.what₂.grp).2.1
    refine GlobalTheory.Mem.R3.GoodDual.goodStable_of_coeff (q.w.st q.Z).B.embLL q.x.what₂.r.z.Xg q.x.what₂.r.z.good.irr fun g => ?_
    apply (q.w.st q.Z).B.embLL.injective
    rw [q.x.what₂.r.z.good.2, q.x.what₂.r.z.good.2, map_inv, GlobalTheory.Mem.R3.GoodDual.goodIdempotent_coeff_inv_eq_coeff hI]
  have hT : TypesTrue (q.w.st q.Z).toD7.ntypes q.x.what₂.r.z.R.C.P q.x.what₂.r.z.R.C.W := by
    rw [q.x.what₂.r.z.lev.C, q.w.C_eq]
    exact q.x.what₂.grp
  have hME := _root_.GlobalTheory.T.twisted_multiplicity_one a1 a2 h4 h3 a5 a6 a7 a12 a13 hG q.x.what₂.r.z.R q.x.what₂.r.z.F q.x.what₂.r.intersectionNumber_baseChange.ok
    q.x.what₂.r.z.pins.char q.x.what₂.exAt hH hp q.B.ccK_top q.x.what₂.r.z.pins.keep.guard
    (GlobalTheory.LiftRows.Inh.goodTypes_of_typesTrue q.x.what₂.r.z.pins.char.base.lev hT)
  exact GlobalTheory.Mem.R3.isotRank_of_multEq h1 h2 h3 h4 _ _ _ _ _ _ _ q.x.what₂.r.z.R q.x.what₂.r.z.F q.x.what₂.r.z.cG _ q.x.what₂.r.Y q.x.what₂.r.z.pins
    q.x.what₂.r.intersectionNumber_baseChange hH hGS (GlobalTheory.CuspDec.cuspDecomp h3 h4 _) hME
end GlobalTheory.Fc.RL.LamLinked
namespace GlobalTheory.Fc.RL
end GlobalTheory.Fc.RL
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealGroupInputsCombined

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fc.RL

theorem at_row_hLamP_alt_alt : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraAnalyticity → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspTraceClass → GlobalTheory.Published.DixmierMalliavinFactorisation → GlobalTheory.Published.FlathFactorisation → GlobalTheory.Published.ZelevinskyPolynomialRing → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.GreenCuspidal → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.R1.SlotLambdaPrimeCondition := by
  intro h1 h2 h3 h4 a1 a2 a5 a6 a7 a12 a13 hG hL N S Γ
  refine _root_.GlobalTheory.Fc.RL.LinkedAt.of_row (RowE.row (EvP.mono (fun κ K _ H β _ c b hl => ?_) LamLinked.evP_params))
  obtain ⟨q, b', ⟨w⟩, he⟩ := hl
  have e1 := congrArg (fun s : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c => Nonempty (ParameterChoice' s.1 s.2.1.L)) he
  have e2 := congrArg (fun s : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c => _root_.GlobalTheory.Fc.R1.LambdaPrimeBundleCondition s.1 s.2.1 c s.2.2) he
  refine cast e2.symm ?_
  have hIR := _root_.GlobalTheory.Fc.RL.LamLinked.isotRank_of_wit_alt h1 h2 h3 h4 a1 a2 a5 a6 a7 a12 a13 hG q w.y.y.host ⟨_, cast e1 (H β)⟩
  show Formalism.L2.Rows.RowsHoldLam3 b'.P
  rw [show b'.P = R3.divisionPairOfAdelicFormsFaceColumnsData w.x from congrArg _root_.GlobalTheory.Mem.Top.Bl.RealPackage.P w.y.eq]
  exact (GlobalTheory.Mem.R3.rowConditions_at_companion_from_readings _ _ _ _ _ _ _ _ _ w.x).1
    (GlobalTheory.T.finiteTypes_via_full_heckeAlgebra_eigensystems h1 h2 h3 h4 _ _ _ _ _ w.x.A3 _ w.x.R w.x.F w.x.cG q.O.ex.p0 w.x.Y w.x.Z w.x.pins w.y.intersectionNumber_baseChange w.y.y.host hIR)
end GlobalTheory.Fc.RL

theorem _root_.GlobalTheory.T.real_group_inputs_combined_alt_alt : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraAnalyticity → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspTraceClass → GlobalTheory.Published.DixmierMalliavinFactorisation → GlobalTheory.Published.FlathFactorisation → GlobalTheory.Published.ZelevinskyPolynomialRing → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.GreenCuspidal → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.R1.SlotLambdaPrimeCondition :=
  _root_.GlobalTheory.Fc.RL.at_row_hLamP_alt_alt
end
end
end
