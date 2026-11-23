module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
public import Formalism.LocalToGlobal.IndefiniteReal.IsFDiagIffDiagonal
public import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.FramesExistOfDiagonalTypePlaces
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters
public import Formalism.LocalToGlobal.IndefiniteReal.PartsRow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PartsRowOfEigensystemIndexGoodCharacters
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
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedArgsColumnHeq
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GoodGenericRowsStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealRecOf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DivisionPairOfAdelicFormsFaceColumnsData
public import Formalism.LocalToGlobal.IndefiniteReal.RealRec
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwArgs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LamPOfPart
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ParameterOfDiscreteSeriesRay

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PartsRowOfEigensystemIndexGoodCharactersStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.partsRow_of_eigensystemIndex_goodCharacters : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) (Xd : DivX D), Pins R F cG → Holds R F → HostHyp D → (∀ χ ∈ A3.A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → (∀ (i : Fin D.R.m) π (c : A3.fam3.base3.Ix) (e : D.what₂.LL →+* ℂ), D.what₂.isot ((i : ℕ) + 1) π ≠ ⊥ → D.what₂.isot ((i : ℕ) + 1) π ≤ (R.Wp3 i c).comap (Y.mj.eW i) → Xd.logLam ((i : ℕ) + 1) π e = Real.log (R.lam3 i A3.A.μ0 c (InfinitePlace.mk e))) → ∃ (E : EigIdx D Xd) (labPi : E.Pi → A3.A.fam.base.Ix) (piOf : E.Pi → HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ), PartsRec R.toRealDat F.lv2 Y.tupT Y.hm Y.PY Y.PW Y.eFT E labPi piOf Y.Ish.prt Y.IL.prtW := by
  first | exact @GlobalTheory.Mem.R3.partsRec_of_eig | exact GlobalTheory.Mem.R3.partsRec_of_eig | (intros; apply GlobalTheory.Mem.R3.partsRec_of_eig <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftGroupFormsEqExtendedRationalFormsCompanion

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3.Reads

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts} {Yd : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Yd cX}



theorem liftGroupForms_eq_extended_rationalForms_companion (x : TwIn ex) : Formalism.IndefR.RecTie.MtRead x.R.toRealDat x.F.lv2 x.Y.tupT x.Y.hm x.Y.hTop x.Y.hinj x.Y.IL
    (twPOf (divisionPairOfAdelicFormsFaceColumnsData x) x.Y.tupT x.Y.tupTie) := by
  intro μ hμ i v
  have key : ∀ (t : x.T) (μ : D.what₂.Tup) (e : x.Y.tup t = μ) (hμ : Formalism.IndefR.RecTie.Used0 D μ) (e' : x.Y.tupT μ = t)
      (v : D.what₂.MtL μ ((i : ℕ) + 1)),
      HEq (x.Y.IL.jMt μ hμ i (D.what₂.jMt μ ((i : ℕ) + 1) v)).1
        (x.R.toRealDat.extV i t (x.R.toRealDat.jV i t (liftForm x.A3.A x.F.P0 x.F.ψ0 i t ((x.Y.eMt i t).symm (e.symm ▸ v))))) := by
    intro t μ e hμ e' v
    subst e
    have := x.Y.mtRead i t hμ ((x.Y.eMt i t).symm v)
    rw [LinearEquiv.apply_symm_apply] at this
    exact heq_of_eq this
  have := eq_of_heq (key _ μ (x.Y.tupTie μ hμ) hμ rfl v)
  rw [this]
  unfold twPOf
  rw [dite_eq_left hμ]
  rfl



end GlobalTheory.Mem.R3.Reads

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MjReadRealizationEqual

section

@[expose] public section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.R3
namespace GlobalTheory.Mem.R3.Reads
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts} {Yd : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Yd cX}

theorem mjRead_of_indefinite_down_join (x : TwIn ex) {Rc : _root_.Formalism.L2.RecTAlt ex} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} (y : _root_.GlobalTheory.Mem.R3.RealInAlt x Rc S) :
    Formalism.IndefR.RecTie.MjRead x.R.toRealDat x.F.lv2 x.Y.tupT x.Y.hm x.Y.hTop x.Y.hinj x.Y.IL
    (fun i => (x.A3.indefDown (s0Of x.R x.F)).dW i) (fun i v => x.Z.jW i v) ((indefiniteDownJoin (realisationOfInput y))) := by
  intro i v
  have h1 := x.Y.mjRead i (x.Z.jW i v)
  have h2 := x.Z.jW_read i v
  have h3 : x.Y.mj.eW i (x.Z.jW i v) ∈ LinearMap.range (x.Y.mj.eW i) := ⟨_, rfl⟩
  rw [x.Y.mj.eW_range i] at h3
  have h4 := h3.2
  have h5 : Mult.postOn _ (x.R.toRealDat.eWf i (sg0 D x.A3.A)) ((x.R.HW i (sg0 D x.A3.A)).e (x.Y.mj.eW i (x.Z.jW i v))) =
      (x.R.HW i (sg0 D x.A3.A)).e (x.Y.mj.eW i (x.Z.jW i v)) := sub_eq_zero.1 h4
  refine h1.trans (congrArg _ ?_)
  rw [← h5, h2]
  rfl

theorem mt_mj_read_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Yd cX) (x : TwIn ex) (Rc : _root_.Formalism.L2.RecTAlt ex) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (y : _root_.GlobalTheory.Mem.R3.RealInAlt x Rc S), Holds x.R x.F → Formalism.IndefR.RecTie.MtRead x.R.toRealDat x.F.lv2 x.Y.tupT x.Y.hm x.Y.hTop x.Y.hinj x.Y.IL (twPOf (divisionPairOfAdelicFormsFaceColumnsData x) x.Y.tupT x.Y.tupTie) ∧ Formalism.IndefR.RecTie.MjRead x.R.toRealDat x.F.lv2 x.Y.tupT x.Y.hm x.Y.hTop x.Y.hinj x.Y.IL (fun i => (x.A3.indefDown (s0Of x.R x.F)).dW i) (fun i v => x.Z.jW i v) ((indefiniteDownJoin (realisationOfInput y))) := by
  intro D L hT Gi Gl K Yd cX ex x Rc S y _
  exact ⟨liftGroupForms_eq_extended_rationalForms_companion x, _root_.GlobalTheory.Mem.R3.Reads.mjRead_of_indefinite_down_join x y⟩
end GlobalTheory.Mem.R3.Reads
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ScalRows

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3
noncomputable section
namespace GlobalTheory.Mem.R3.ScalarComponentUnique

theorem scal_rows_alt : GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (Γ : GeoP) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), p = _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none Γ → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → ∀ (K : Ctx) (q : WPt p.s K), (∀ X : GlobalTheory.Mem.Stages, K.Over X.B.toPre → HostHyp X.toD7 ∧ X.toD7.host.F = maximalRealSubfield X.toD7.host.E ∧ (∀ i, IsFDiag (Wc X.toD7 i) ∧ IsFDiag (Vc X.toD7 i)) ∧ (∀ i, (Vc X.toD7 i).IsPosDef) ∧ (∀ j, Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.Y j) ∧ Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.V j) ∧ (1 ≤ j → j ≤ X.toD7.R.m → Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.W j))) ∧ Formalism.IndefR.Seed.FrmC.StdLat X.toD7.sp.X' ∧ (∀ i, (∀ a b, (Vc X.toD7 i).hT ((Vc X.toD7 i).frame a) ((Vc X.toD7 i).frame b) = if a = b then 1 else 0) ∧ (Vc X.toD7 i).L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range (Vc X.toD7 i).frame)) ∧ ((∀ a b, X.toD7.sp.X'.hT (X.toD7.sp.X'.frame a) (X.toD7.sp.X'.frame b) = if a = b then 1 else 0) ∧ X.toD7.sp.X'.L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range X.toD7.sp.X'.frame))) → GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat → ∀ (a : TwArgs q.O.ex q.x.what₂), letI := a.x.grp; letI := a.x.fin; letI := a.x.alg; ∀ (i : Fin (q.w.D q.Z).R.m) π (c : a.x.A3.fam3.base3.Ix) (e : (q.w.D q.Z).what₂.LL →+* ℂ), (q.w.D q.Z).what₂.isot ((i : ℕ) + 1) π ≠ ⊥ → (q.w.D q.Z).what₂.isot ((i : ℕ) + 1) π ≤ (a.x.R.Wp3 i c).comap (a.x.Y.mj.eW i) → q.O.X.logLam ((i : ℕ) + 1) π e = Real.log (a.x.R.lam3 i a.x.A3.A.μ0 c (InfinitePlace.mk e)) := by
  intro hGC h1 h2 h3 h4 h5 h6 hCRD h8 h9 hL N Γ p hp hNE K q hHost hMult a
  letI := a.x.grp; letI := a.x.fin; letI := a.x.alg
  intro i π c e hne hle
  by_cases he : e = (q.w.D q.Z).what₂.embLL
  · subst he
    have h := eigenvalue_of_part hCRD a.x.R a.x.F a.x.cG _ a.x.Y a.x.pins a.intersectionNumber_baseChange i π c hne hle
    exact (q.O.X.logLam_base _ π).trans
      (congrArg Real.log (h.trans (congrArg (a.x.R.lam3 i a.x.A3.A.μ0 c) a.x.R.hv0)))
  · exact _root_.GlobalTheory.T.parameter_of_discrete_series_ray_alt hGC h1 h2 h3 h4 h5 h6 hCRD h8 h9 hL N Γ p hp hNE K q hHost hMult a i π c e he hne hle
end GlobalTheory.Mem.R3.ScalarComponentUnique
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ScalRowsStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.parameter_of_discrete_series_reciprocity_alt : GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (Γ : GeoP) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), p = _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none Γ → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → ∀ (K : Ctx) (q : WPt p.s K), (∀ X : GlobalTheory.Mem.Stages, K.Over X.B.toPre → HostHyp X.toD7 ∧ X.toD7.host.F = maximalRealSubfield X.toD7.host.E ∧ (∀ i, IsFDiag (Wc X.toD7 i) ∧ IsFDiag (Vc X.toD7 i)) ∧ (∀ i, (Vc X.toD7 i).IsPosDef) ∧ (∀ j, Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.Y j) ∧ Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.V j) ∧ (1 ≤ j → j ≤ X.toD7.R.m → Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.W j))) ∧ Formalism.IndefR.Seed.FrmC.StdLat X.toD7.sp.X' ∧ (∀ i, (∀ a b, (Vc X.toD7 i).hT ((Vc X.toD7 i).frame a) ((Vc X.toD7 i).frame b) = if a = b then 1 else 0) ∧ (Vc X.toD7 i).L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range (Vc X.toD7 i).frame)) ∧ ((∀ a b, X.toD7.sp.X'.hT (X.toD7.sp.X'.frame a) (X.toD7.sp.X'.frame b) = if a = b then 1 else 0) ∧ X.toD7.sp.X'.L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range X.toD7.sp.X'.frame))) → GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat → ∀ (a : TwArgs q.O.ex q.x.what₂), letI := a.x.grp; letI := a.x.fin; letI := a.x.alg; ∀ (i : Fin (q.w.D q.Z).R.m) π (c : a.x.A3.fam3.base3.Ix) (e : (q.w.D q.Z).what₂.LL →+* ℂ), (q.w.D q.Z).what₂.isot ((i : ℕ) + 1) π ≠ ⊥ → (q.w.D q.Z).what₂.isot ((i : ℕ) + 1) π ≤ (a.x.R.Wp3 i c).comap (a.x.Y.mj.eW i) → q.O.X.logLam ((i : ℕ) + 1) π e = Real.log (a.x.R.lam3 i a.x.A3.A.μ0 c (InfinitePlace.mk e)) := by
  first | exact @_root_.GlobalTheory.Mem.R3.ScalarComponentUnique.scal_rows_alt | exact _root_.GlobalTheory.Mem.R3.ScalarComponentUnique.scal_rows_alt | (intros; apply _root_.GlobalTheory.Mem.R3.ScalarComponentUnique.scal_rows_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RecInPartsExists

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3
noncomputable section
namespace GlobalTheory.Mem.R3.RecInAt

private theorem tupTied_xi_eq {D : D7} {nch : NChoice D} {c₁ c₂ : CharFrame D}
    {t₁ : TupTied D c₁ nch} {t₂ : TupTied D c₂ nch} (hc : c₁ = c₂) (ht : HEq t₁ t₂) :
    t₁.xi = t₂.xi := by
  cases hc
  exact congrArg (fun t : TupTied D c₁ nch => t.xi) (eq_of_heq ht)

theorem recIn_parts_exists_alt : GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (Γ : GeoP) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), p = _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none Γ → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → ∀ (K : Ctx) (q : WPt p.s K), (∀ X : GlobalTheory.Mem.Stages, K.Over X.B.toPre → HostHyp X.toD7 ∧ X.toD7.host.F = maximalRealSubfield X.toD7.host.E ∧ (∀ i, IsFDiag (Wc X.toD7 i) ∧ IsFDiag (Vc X.toD7 i)) ∧ (∀ i, (Vc X.toD7 i).IsPosDef) ∧ (∀ j, Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.Y j) ∧ Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.V j) ∧ (1 ≤ j → j ≤ X.toD7.R.m → Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.W j))) ∧ Formalism.IndefR.Seed.FrmC.StdLat X.toD7.sp.X' ∧ (∀ i, (∀ a b, (Vc X.toD7 i).hT ((Vc X.toD7 i).frame a) ((Vc X.toD7 i).frame b) = if a = b then 1 else 0) ∧ (Vc X.toD7 i).L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range (Vc X.toD7 i).frame)) ∧ ((∀ a b, X.toD7.sp.X'.hT (X.toD7.sp.X'.frame a) (X.toD7.sp.X'.frame b) = if a = b then 1 else 0) ∧ X.toD7.sp.X'.L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range X.toD7.sp.X'.frame))) → GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat → ∀ (R : _root_.Formalism.L2.RecTAlt q.O.ex), _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended q R → ∀ (sP : GlobalTheory.Mem.SRe.SPack (q.w.D q.Z) fun u => (R.T.cols.forms u).to0) (sS : GlobalTheory.Mem.SRe.SRest sP), HEq sP q.saturationAtWeightedPoint.P → HEq sS q.saturationAtWeightedPoint.S → ∀ (a : TwArgs q.O.ex q.x.what₂) (x : TwIn q.O.ex), HEq a.x x → ∀ (y : _root_.GlobalTheory.Mem.R3.RealInAlt x R (sS.toRealSpectralMatching R)), ∃ r : _root_.GlobalTheory.Mem.R3.RecursiveInput y, (_root_.GlobalTheory.Mem.R3.realisationRecursionOfInput r).PartsRow := by
  intro hGC hDC hHM hCW hW hDS hHC hCR hGAR hRF hL N Γ p hp hN K q hH hM R hR sP sS hP hS a x hax
  obtain rfl := eq_of_heq hax
  intro y
  have hlev := GlobalTheory.Mem.R3.twArgs_lev K q.B q.f q.T q.w q.Z q.x.Wt
    q.O.L q.O.gatT q.O.Gx q.O.Gy q.O.K q.O.X q.O.cX q.O.ex q.x.what₂ a
  have hmt := _root_.GlobalTheory.Mem.R3.Reads.mt_mj_read_alt
    (q.w.D q.Z) q.O.L q.O.gatT q.O.Gx q.O.Gy q.O.K q.O.X q.O.cX
    q.O.ex a.x R (sS.toRealSpectralMatching R) y a.intersectionNumber_baseChange
  have hFr : Top.Fr.at (q.w.st q.Z) q.f = GlobalTheory.Mem.Col2.TC.cf q.w.I q.w.l q.Z :=
    (congrArg (Top.Fr.at (q.w.st q.Z)) q.w.C_eq.symm).trans rfl
  have hchr := Sigma.mk.inj_iff.1 hR.s.chr
  have hC : R.T.n.cf = a.x.R.C := hchr.1.trans (hFr.symm.trans (eq_of_heq hlev.1).symm)
  let tp := cast (congrArg (fun c => TupTied (q.w.D q.Z) c q.O.ex.nch) hC) R.T.n.tp
  have htp : HEq tp R.T.n.tp := cast_heq _ _
  have hxi : tp.xi = q.w.I.xi :=
    (tupTied_xi_eq hC.symm htp).trans ((tupTied_xi_eq hchr.1 hchr.2).trans q.x.n.xi)
  have hgen := _root_.GlobalTheory.T.geometric_parameter_of_reciprocity_alt
    hDC hHM hCW hW hDS hHC hCR hGAR hRF hL N Γ p hp hN K q hH hM a
  have hlam := _root_.GlobalTheory.T.parameter_of_discrete_series_reciprocity_alt
    hGC hDC hHM hCW hW hDS hHC hCR hGAR hRF hL N Γ p hp hN K q hH hM a
  have heig := @GlobalTheory.T.partsRow_of_eigensystemIndex_goodCharacters
    hW hDS hHC hCR (q.w.D q.Z) a.x.G a.x.grp a.x.fin a.x.Pl0 a.x.I0 a.x.T a.x.A3
    a.x.core.Q.c.F inferInstance inferInstance a.x.alg
    a.x.R a.x.F a.x.cG q.O.ex.p0 a.x.Y a.x.Z q.O.X a.x.pins a.intersectionNumber_baseChange
    (hH (q.w.st q.Z) q.x.isOver).1 hgen hlam
  refine heig.elim fun E hE => hE.elim fun labPi hLab => hLab.elim fun piOf hparts => ?_
  let r : RecursiveInput y := {
    E := E
    labPi := labPi
    piOf := piOf
    Tp := tp
    tpEq := htp
    tupXi := fun μ hμ => (eq_of_heq (hlev.2.2.1 μ hμ).2).trans (congrFun hxi.symm μ)
    mtRead := hmt.1
    mjRead := hmt.2 }
  exact ⟨r, hparts⟩
end GlobalTheory.Mem.R3.RecInAt
end
end
end
end
