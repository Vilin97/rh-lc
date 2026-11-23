module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PackB
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedArgsColumnHeq
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealRecOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BaseRankEqOfRealisation
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PackOfTup

section

@[expose] public section



section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam.Inhab
open GlobalTheory.SymBridge
section Frames
variable {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y]
end Frames
section True
open GlobalTheory.Mem
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX}
end True
section Built
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr
def realPackageOfInput {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {x : TwIn ex} {Rc : _root_.Formalism.L2.RecTAlt ex}
    {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} (y : _root_.GlobalTheory.Mem.R3.RealInAlt x Rc S) : _root_.GlobalTheory.MiS.RealPackAlt ex where
  R := Rc
  S := S
  P := divisionPairOfAdelicFormsFaceColumnsData x
  Dcf := x.F.Dc
  Spf := x.F.Sp
  Zscf := x.F.Zsc
  Ks := x.core.Q.c.F
  Q := _root_.GlobalTheory.Mem.R3.realisationOfInput y
def tupleAtIndex {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (s : W.P.T) : D.what₂.Tup := W.P.I.tup s
theorem used0_tupP_packOf_and_tupT_eq {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {x : TwIn ex} {Rc : _root_.Formalism.L2.RecTAlt ex}
    {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} (y : _root_.GlobalTheory.Mem.R3.RealInAlt x Rc S) (s : x.T) :
    Formalism.IndefR.RecTie.Used0 D (_root_.GlobalTheory.Fam.Inhab.tupleAtIndex (_root_.GlobalTheory.Fam.Inhab.realPackageOfInput y) s) ∧ x.Y.tupT (_root_.GlobalTheory.Fam.Inhab.tupleAtIndex (_root_.GlobalTheory.Fam.Inhab.realPackageOfInput y) s) = s :=
  ⟨_root_.Formalism.IndefR.LevelRealisationRankEquality.tup_all_used_of_realisation (_root_.GlobalTheory.Mem.R3.realisationOfInput y) s, x.Y.tupT_tup s⟩
end Built
end GlobalTheory.Fam.Inhab
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QplacesOfBWit

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
noncomputable def packK_alt {D : D7} {O : Obj D} {R : _root_.Formalism.L2.RecTAlt O.ex} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R} (k : _root_.GlobalTheory.Mem.Top.Bl.RealPackage R S) :
    _root_.GlobalTheory.MiS.RealPackAlt O.ex :=
  letI := k.B.alg
  { R := R, S := S, P := k.P, Dcf := k.Dc, Spf := k.Sp, Zscf := k.Zsc, Ks := k.B.T.Q.c.F, Q := k.B.Q }

theorem mem_Q_packB_iff_mem_QE_of_bWit : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → ∀ t PP, PP ∈ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).Q t ↔ PP ∈ Formalism.L2.Col.QE q.w.I.sel (q.w.I.tup (b.P.I.tup t) : Formalism.L2.DIV.Chr q.B.fields.F q.B.fields.E q.B.fields.K) := by
  intro hL p K q c b hw
  obtain ⟨x, a, ax, y, -, -, -, -, -, -, -, -, -⟩ := hw
  have hx : a.x = x := eq_of_heq ax
  subst hx
  have main : ∀ t PP, PP ∈ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packK_alt (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y.y))).Q t ↔
      PP ∈ Formalism.L2.Col.QE q.w.I.sel (q.w.I.tup ((_root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y.y).P.I.tup t) : Formalism.L2.DIV.Chr q.B.fields.F q.B.fields.E q.B.fields.K) := by
    intro t PP
    obtain ⟨-, -, hl, -⟩ := GlobalTheory.Mem.R3.twArgs_lev K q.B q.f q.T q.w q.Z _ _ _ _ _ _ _ _ q.O.ex q.x.what₂ a
    have h1 := (hl _ (_root_.GlobalTheory.Fam.Inhab.used0_tupP_packOf_and_tupT_eq y.y t).1).1
    rw [(_root_.GlobalTheory.Fam.Inhab.used0_tupP_packOf_and_tupT_eq y.y t).2] at h1
    exact Iff.of_eq (congrArg (PP ∈ ·) (eq_of_heq h1))
  show (fun k : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S => ∀ t PP, PP ∈ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packK_alt k)).Q t ↔
      PP ∈ Formalism.L2.Col.QE q.w.I.sel (q.w.I.tup (k.P.I.tup t) : Formalism.L2.DIV.Chr q.B.fields.F q.B.fields.E q.B.fields.K)) (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b)
  rw [y.eq]
  exact main
end GlobalTheory.Fam
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QplacesOfBWitStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.twist_places_match_witness' : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → ∀ t PP, PP ∈ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).Q t ↔ PP ∈ Formalism.L2.Col.QE q.w.I.sel (q.w.I.tup (b.P.I.tup t) : Formalism.L2.DIV.Chr q.B.fields.F q.B.fields.E q.B.fields.K) := by
  first | exact @_root_.GlobalTheory.Fam.mem_Q_packB_iff_mem_QE_of_bWit | exact _root_.GlobalTheory.Fam.mem_Q_packB_iff_mem_QE_of_bWit | (intros; apply _root_.GlobalTheory.Fam.mem_Q_packB_iff_mem_QE_of_bWit <;> assumption)
end
end
end
