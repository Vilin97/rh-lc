module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AndLeft
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ReferenceChainEvaluationAtBundlePoints
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PropertyAtConstructedPointsOfTrueColumnsViewStatement
public import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LowerTieTwAt
public import Formalism.SharpRestriction.Divisibility.HookProducts.AdmPtTw
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
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Formalism.LocalToGlobal.Divisibility.BrJoint
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InvTrKEmbGLApply
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsIntegralCoordinatesTwistedTrueChainStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LowerTwistedCompatibleOfEvaluationBranching

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms

namespace GlobalTheory.PerQ

theorem lowerTieTwAt_to_lib : ∀ (D : D7) (T : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup),
    GlobalTheory.PerQ.LowerTieTwAt D T u μ → Formalism.MainNotions.DIV.HookProducts.AdmPtTw.LowerTieTwAt D T u μ := by
  rintro D T u μ ⟨a, b, P, hP⟩
  exact ⟨a, b, ⟨P.br, P.coM, P.coP, P.Pt_eq, P.lat_co, P.pt_co⟩, hP⟩

end GlobalTheory.PerQ
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LowerTwistedCompatibleOfEvaluationBranchingStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms

theorem _root_.GlobalTheory.T.lowerTwistedCompatible_of_evaluationBranching : ∀ (D : D7) (T : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup), GlobalTheory.PerQ.LowerTieTwAt D T u μ → Formalism.MainNotions.DIV.HookProducts.AdmPtTw.LowerTieTwAt D T u μ := by
  first | exact @GlobalTheory.PerQ.lowerTieTwAt_to_lib | exact GlobalTheory.PerQ.lowerTieTwAt_to_lib | (intros; apply GlobalTheory.PerQ.lowerTieTwAt_to_lib <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BranchingOk

section

@[expose] public section

namespace GlobalTheory.LvT.BuiltChain

theorem branching_ok : Formalism.MainNotions.PrimeDegreeVariant.Conclusion6 := Formalism.L2.DIV.BrJ.branching_interlacing_pairs

end GlobalTheory.LvT.BuiltChain
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EvaluationMapTrueChainFormsToFormsStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.evaluationMap_trueChain_forms_to_forms :
    ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), ColIn.Ok I →
      ∀ (l : TC.Laws I) (Z : TC.Later B (TC.cols I l)) (l0 : TC.Law0 I l)
        (u : B.Word) (a : I.ι),
        (∀ φ ∈ ((TC.tw I l l0 Z).fm u a).Fi B.R.m,
          GlobalTheory.PerQ.PtT (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u a φ ∈
            ((TC.tw I l l0 Z).fm u a).ptC) ∧
        ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).fm u).SgInterlace := by
  intro B X I _ l Z l0 u a
  have hs : ∀ τ, (TC.perIn I u a).sg τ = (RowPar.of (B.hcW u τ)).sg := fun τ =>
    congrArg RowPar.sg (B.wts_isOk.hc_row u τ).symm
  have hW := GlobalTheory.LvT.BuiltChain.weights_ok (TC.perIn I u a) (B.hcW u) B.fields.emb hs
  refine ⟨?_, ?_⟩
  · intro φ hφ
    let M := TC.fm I l u a
    have latticeImage : ∀ x ∈ (M.lat B.R.m).L, ∃ y, M.ptEmb y =
        (TC.per I l u a).lowerMap ((TC.per I l u a).evz (M.emb B.R.m x)) := by
      intro x hx
      obtain ⟨y, -, hy⟩ := GlobalTheory.LvT.BuiltChain.exists_image (Q := TC.perIn I u a)
        B.fields.emb B.embLL (B.hcW u) GlobalTheory.LvT.BuiltChain.branching_ok
        (l.ch u a) (l.per u a) (fun τ => (hW τ).1) (fun τ => (hW τ).2)
        ((l.fmL u a).fam B.R.m) (l.fmL u a).famP x hx
      exact ⟨y, hy⟩
    have rationalImage : ∀ x, ∃ y, M.ptEmb y =
        (TC.per I l u a).lowerMap ((TC.per I l u a).evz (M.emb B.R.m x)) := by
      intro x
      have hx : x ∈ Submodule.span B.LL ((M.lat B.R.m).L : Set (M.lat B.R.m).V) := by
        rw [(M.lat_good B.R.m).2.2]
        trivial
      induction hx using Submodule.span_induction with
      | mem x hx => exact latticeImage x hx
      | zero => exact ⟨0, by simp⟩
      | add x x' _ _ hx hx' =>
        obtain ⟨y, hy⟩ := hx
        obtain ⟨y', hy'⟩ := hx'
        exact ⟨y + y', by rw [map_add, map_add, map_add, map_add, hy, hy']⟩
      | smul r x _ hx =>
        obtain ⟨y, hy⟩ := hx
        refine ⟨r • y, ?_⟩
        rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, hy, LinearMap.map_smul, LinearMap.map_smul]
    have ptMem : ∀ y, M.ptEmb y ∈ M.ptC := by
      intro y

      rw [← M.ptEmb_basis.2, ← M.ptLat.b.sum_repr y, map_sum]
      refine Submodule.sum_mem _ fun c _ => ?_
      rw [LinearMap.map_smulₛₗ]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)
    have hφ' : φ ∈ M.Fi B.R.m := hφ
    rw [← (M.emb_basis B.R.m).2] at hφ'
    have hle : Submodule.span ℂ (Set.range fun c => M.emb B.R.m ((M.lat B.R.m).b c)) ≤
        M.ptC.comap ((TC.per I l u a).lowerMap ∘ₗ (TC.per I l u a).evz) := by
      rw [Submodule.span_le]
      rintro _ ⟨c, rfl⟩
      obtain ⟨y, hy⟩ := rationalImage ((M.lat B.R.m).b c)
      show (TC.per I l u a).lowerMap ((TC.per I l u a).evz _) ∈ M.ptC
      rw [← hy]
      exact ptMem y
    exact hle hφ'
  · intro τ i
    obtain ⟨ha, hb⟩ := (hW τ).1 i
    simp only [Br.aBr, Br.bBr, Br.iS, Br.iC, PerIn.sgT, GlobalTheory.Mem.Col2.lamT,
      GlobalTheory.Mem.Col2.shW] at ha hb
    constructor
    · show (B.wts.sgW τ).w i ≤ (Examples₂.lamOf (B.hcW u τ) B.R.m).w ⟨i.1, _⟩
      change 0 ≤ (Examples₂.lamOf (B.hcW u τ) B.R.m).w ⟨i.1, _⟩ + _ - ((B.wts.sgW τ).w i + _) at hb
      linarith
    · show (Examples₂.lamOf (B.hcW u τ) B.R.m).w ⟨i.1 + 1, _⟩ ≤ (B.wts.sgW τ).w i
      change 0 ≤ (B.wts.sgW τ).w i + _ - ((Examples₂.lamOf (B.hcW u τ) B.R.m).w ⟨i.1 + 1, _⟩ + _) at ha
      linarith
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwistedEvaluationBranchingAllTuplesTrueColumns

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.PerQ.lowerTieTwAt_all : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word) (a : I.ι), GlobalTheory.PerQ.LowerTieTwAt (I.rec7 l Z) (I.tw l l0 Z) u a := by
  intro B X I hI l Z l0 u a
  exact ⟨(GlobalTheory.T.evaluationMap_trueChain_forms_to_forms I hI l Z l0 u a).1, (GlobalTheory.T.evaluationMap_trueChain_forms_to_forms I hI l Z l0 u a).2, GlobalTheory.T.exists_integralCoordinates_twistedTrueChain I hI l Z l0 u a⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwistedEvaluationBranchingAllTuplesTrueColumnsStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.twistedEvaluation_branching_all_tuples_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word) (a : I.ι), GlobalTheory.PerQ.LowerTieTwAt (I.rec7 l Z) (I.tw l l0 Z) u a := by
  first | exact @GlobalTheory.PerQ.lowerTieTwAt_all | exact GlobalTheory.PerQ.lowerTieTwAt_all | (intros; apply GlobalTheory.PerQ.lowerTieTwAt_all <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwistedPointRowAdmissibleTrueColumns

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PerQ

theorem twistedPointIntegral_of_TC_ok : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l), Formalism.L2.G.Adm2InU.TwistedPointIntegral (I.rec7 l Z) (I.tw l l0 Z) := by
  intro B X I hI l Z l0 u μ _ _
  exact Formalism.MainNotions.DIV.HookProducts.AdmPtTw.lowerTieTwAt_integral
    (GlobalTheory.T.lowerTwistedCompatible_of_evaluationBranching _ _ u μ (GlobalTheory.T.twistedEvaluation_branching_all_tuples_trueColumns I hI l Z l0 u μ))

end GlobalTheory.PerQ
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwistedPointRowAdmissibleTrueColumnsStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.twistedPointRow_admissible_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l), Formalism.L2.G.Adm2InU.TwistedPointIntegral (I.rec7 l Z) (I.tw l l0 Z) := by
  first | exact @GlobalTheory.PerQ.twistedPointIntegral_of_TC_ok | exact GlobalTheory.PerQ.twistedPointIntegral_of_TC_ok | (intros; apply GlobalTheory.PerQ.twistedPointIntegral_of_TC_ok <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwistedChainEvaluationRationalIntegralBundlePoin

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Fc.Cv NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fc.PeriodEntriesOverColumns

theorem row_aPtTw_of_overCols : ∀ (Q : V4.Slot), OverCols Q → ∀ (Bd : BdT) (Lk : LkT Bd), PeriodEntriesOverColumns.TwistedPointAtBundlePoints Q Lk := by
  intro Q hQ Bd Lk
  have h0 : Row0 Q (EvC fun D O => Formalism.L2.G.Adm2InU.TwistedPointIntegral D O.ex.tw) := by
    apply validForConstructedPointClasses_eventuallyWorkingClass
    refine EvP.of_all fun _ K _ β hβ => ?_
    have hc : β.Is HasCols := hQ K β.X β.f β.T β.c hβ
    refine GlobalTheory.T.property_at_constructedPoints_of_trueColumnsView (fun D O => Formalism.L2.G.Adm2InU.TwistedPointIntegral D O.ex.tw) ?_ K β hc
    intro B f T w Z O nch hv _ _
    rw [hv.tw_eq]
    exact GlobalTheory.T.twistedPointRow_admissible_trueColumns w.I w.ok w.l Z w.l0
  exact h0.row Lk

end GlobalTheory.Fc.PeriodEntriesOverColumns
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwistedChainEvaluationRationalIntegralBundlePoinStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Fc.Cv NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.twistedChainEvaluation_rational_integral_bundlePoints : ∀ (Q : V4.Slot), OverCols Q → ∀ (Bd : BdT) (Lk : LkT Bd), PeriodEntriesOverColumns.TwistedPointAtBundlePoints Q Lk := by
  first | exact @GlobalTheory.Fc.PeriodEntriesOverColumns.row_aPtTw_of_overCols | exact GlobalTheory.Fc.PeriodEntriesOverColumns.row_aPtTw_of_overCols | (intros; apply GlobalTheory.Fc.PeriodEntriesOverColumns.row_aPtTw_of_overCols <;> assumption)
end
end
