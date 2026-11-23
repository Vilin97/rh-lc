module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFactorisationCuspidal
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowGood
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CommutingLevelOperators
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChiIdemMulLvlIdemBaseNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodIdempotentCoeffInvEqCoeff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotNeBotRead
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodTypesOfTypesTrue
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
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeUnderScaleOfGeneral
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisorEmbeddingKappaEqRowsKappaAtInfinitePlaceStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedMultiplicityOne

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HarishChandraInputsCombined

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fc.KapLinked

section Rows

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  {p0 : BaseLevelRowSide (w.D Z)}



theorem isot_ne_bot_of_rows (hF : GlobalTheory.Published.HarishChandraFinite) (hG : GlobalTheory.Published.GreenCuspidal) (t : RowsT K w Z Wt p0)
    (hM : GlobalTheory.CuspMult.MultEq t.r.z.R.toRealDat) (σ : Fin (w.D Z).what₂.Drows) (i : Fin (w.D Z).R.m) :
    (w.D Z).what₂.isot ((i : ℕ) + 1) ((w.D Z).what₂.ft σ) ≠ ⊥ := by
  have hI := GlobalTheory.DimPartsCompare.TameTie.idemTie hG
    (GlobalTheory.DimPartsCompare.tameTie_of_typesTrue (D := (w.st Z).toD7) t.grp).2.1
  have hGS : Formalism.L2.DIV.GoodStable t.r.z.Xg := by
    refine GlobalTheory.Mem.R3.GoodDual.goodStable_of_coeff (w.st Z).B.embLL t.r.z.Xg t.r.z.good.irr fun g => ?_
    apply (w.st Z).B.embLL.injective
    rw [t.r.z.good.2, t.r.z.good.2, map_inv, GlobalTheory.Mem.R3.GoodDual.goodIdempotent_coeff_inv_eq_coeff hI]
  have hC := (GlobalTheory.CoreOfWeak.core_of_weak t.r.z.R t.r.z.F t.r.z.pins.char t.exAt).1
  exact GlobalTheory.KapIsotRead.isot_ne_bot_read hF (w.st Z).toD7 _ _ _ _ _ _ t.r.z.R t.r.z.F t.r.z.cG p0 t.r.Y t.r.z.pins t.r.intersectionNumber_baseChange hM hGS
    (GlobalTheory.GoodTypeGeneric.chiIdem_mul_lvlIdem_base_ne_zero t.r.z.R.toRealDat t.r.z.F.lv2 t.r.intersectionNumber_baseChange.ok.ok2 hC.lev hC.grp _ hI) σ i



theorem goodTypes_of_rows (t : RowsT K w Z Wt p0) : GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators.GoodTypes t.r.z.R.toRealDat := by
  have hT : TypesTrue (w.st Z).toD7.ntypes t.r.z.R.C.P t.r.z.R.C.W := by
    rw [t.r.z.lev.C, w.C_eq]
    exact t.grp
  exact GlobalTheory.LiftRows.Inh.goodTypes_of_typesTrue t.r.z.pins.char.base.lev hT

end Rows


end GlobalTheory.Fc.KapLinked

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HarishChandraInputsCombined

section

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Fc.KapLinked
section Rows
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  {p0 : BaseLevelRowSide (w.D Z)}
end Rows

theorem row_kap_of_row_lam_alt_alt : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraAnalyticity → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspTraceClass → GlobalTheory.Published.DixmierMalliavinFactorisation → GlobalTheory.Published.FlathFactorisation → GlobalTheory.Published.ZelevinskyPolynomialRing → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.GreenCuspidal → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.R1.SlotLambdaPrimeCondition → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.RL.RowKappaCondition := by
  intro a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a15 a16 a17 hL N S Γ h
  obtain ⟨R, hR, h⟩ := h
  refine ⟨R, hR, Row.imp h fun 𝒜 σ s hl => ?_⟩
  have key : AtAll (Bd := _root_.GlobalTheory.Fc.BundleCondition) (fun _ _ _ b => Formalism.L2.Rows.RowsHoldKap3 b.P) 𝒜 σ := by
    intro eps Fm hc x hx i
    obtain ⟨κ, -, -, hb⟩ := s Fm hc
    refine Built.ind (Bd := _root_.GlobalTheory.Fc.BundleCondition) (R := fun D _ _ b => (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → Formalism.L2.Rows.RowsHoldLam3 b.P →
      Formalism.L2.Rows.RowsHoldKap3 b.P) ?_ (hb x hx i).1 ⟨_, ⟨Fm.params x hx i⟩⟩ (hl Fm hc x hx i)
    intro K β c b _ _ hk
    obtain ⟨q, b', ⟨w⟩, he⟩ := hk
    have e := congrArg (fun s : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c => (∃ L : SizeData₂ s.1, Nonempty (ParameterChoice' s.1 L)) →
      Formalism.L2.Rows.RowsHoldLam3 s.2.2.P → Formalism.L2.Rows.RowsHoldKap3 s.2.2.P) he
    refine cast e.symm fun hP hLam => ?_
    have hb' : b'.P = R3.divisionPairOfAdelicFormsFaceColumnsData w.x := congrArg _root_.GlobalTheory.Mem.Top.Bl.RealPackage.P w.y.eq
    change Formalism.L2.Rows.RowsHoldLam3 b'.P at hLam
    change Formalism.L2.Rows.RowsHoldKap3 b'.P
    rw [hb'] at hLam ⊢
    have hM : GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat :=
      _root_.GlobalTheory.T.twisted_multiplicity_one a6 a7 a2 a1 a8 a9 a10 a15 a16 a17 q.x.what₂.r.z.R q.x.what₂.r.z.F q.x.what₂.r.intersectionNumber_baseChange.ok
        q.x.what₂.r.z.pins.char q.x.what₂.exAt w.y.y.host hP q.B.ccK_top q.x.what₂.r.z.pins.keep.guard (goodTypes_of_rows q.x.what₂)
    exact GlobalTheory.T.divisorEmbedding_kappa_eq_rowsKappa_at_infinitePlace ⟨a3, a4, a5, a1, a2⟩ _ _ _ _ _ w.x.A3 _ w.x.R w.x.F w.x.cG _ w.x.Y w.x.Z _ w.x.pins w.y.intersectionNumber_baseChange hLam
      (isot_ne_bot_of_rows a1 a17 q.x.what₂ hM) q.x.obj.kapR
  exact ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ hc => Ind.ev_of_atAll key Fm (w3_a hc)⟩⟩
end GlobalTheory.Fc.KapLinked
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc

theorem _root_.GlobalTheory.T.harish_chandra_inputs_combined_alt_alt : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraAnalyticity → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspTraceClass → GlobalTheory.Published.DixmierMalliavinFactorisation → GlobalTheory.Published.FlathFactorisation → GlobalTheory.Published.ZelevinskyPolynomialRing → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.GreenCuspidal → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.R1.SlotLambdaPrimeCondition → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.RL.RowKappaCondition := by
  first | exact @_root_.GlobalTheory.Fc.KapLinked.row_kap_of_row_lam_alt_alt | exact _root_.GlobalTheory.Fc.KapLinked.row_kap_of_row_lam_alt_alt | (intros; apply _root_.GlobalTheory.Fc.KapLinked.row_kap_of_row_lam_alt_alt <;> assumption)
end
end
end
end
