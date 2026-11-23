module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoCptOfIsAnisoOrPosDef
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfThetaAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaChainLastStepIntertwinesMatchedHecke
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IoTLiftStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsKFinOfMemKfin
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KFiniteSpanLeSpanRealIntertwinerValues
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftEqCIIoStatement

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ItSpansPkAlt

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Core.Mi.SpanY
theorem itSpans_pk_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ j, j + 1 < D.R.m → GlobalTheory.Core.Mi.ItSpans ((_root_.GlobalTheory.Fam.pk_z W).MY j) ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ItY j) := by
  intro hDS hHC D L hT Gi Gl Kc Yd cX ex W hP j hj
  have hC := hP.bot.hyp.2.2.2.1
  have hok := GlobalTheory.Chain.StepVac.stepsOK _ _ _ _ _ _ _ hC.lev hC.models.inf hC.chain.ωY hC.chain.ωX hC.chain.vY hC.chain.vX
  obtain ⟨hw, hv⟩ := hok.1 W.P.A3.A.μ0 ⟨j, by omega⟩ hj
  have hle := GlobalTheory.ItOnto.kfinSpan_le_span_it hDS hHC D _ _ _ _ ((_root_.GlobalTheory.Fam.pk_z W).MY j) ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).θ (_root_.GlobalTheory.Fam.pk_z W).ψ _ _
    ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j) ((_root_.GlobalTheory.Fam.pk_z W).vY W.P.A3.A.μ0 j) ((_root_.GlobalTheory.Fam.pk_z W).ItY j) hC.models.inf hw hv (hC.chain.ItY W.P.A3.A.μ0 j hj)
  intro v hv
  have hv' := hle (Submodule.subset_span ⟨v, fun τ => Submodule.subset_span (hv τ), rfl⟩)
  refine (Submodule.span_le.2 ?_) hv'
  rintro w ⟨P, u, hu, rfl⟩
  have hu' : u ∈ Submodule.comap ((_root_.GlobalTheory.Fam.pk_z W).ItY j P) (Submodule.span ℂ
      {x | ∃ (P : PolF D (Yc D (j + 1)).rank (Yc D j).rank) (y : ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)).Vec), KVecP ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) y ∧
        x = (_root_.GlobalTheory.Fam.pk_z W).ItY j P (PiTensorProduct.tprod ℂ y)}) := by
    refine (Submodule.span_le.2 ?_) hu
    rintro _ ⟨y, hy, rfl⟩
    exact Submodule.subset_span ⟨P, y, fun τ => GlobalTheory.Core.Mi.StepSpans.isKFin_of_mem_kfin _ _ (hy τ), rfl⟩
  exact hu'
end GlobalTheory.Core.Mi.SpanY
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ItSpansPkStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.itSpans_MY_succ : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ j, j + 1 < D.R.m → GlobalTheory.Core.Mi.ItSpans ((_root_.GlobalTheory.Fam.pk_z W).MY j) ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ItY j) := by
  first | exact @_root_.GlobalTheory.Core.Mi.SpanY.itSpans_pk_alt | exact _root_.GlobalTheory.Core.Mi.SpanY.itSpans_pk_alt | (intros; apply _root_.GlobalTheory.Core.Mi.SpanY.itSpans_pk_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ItSpansPkAltAlt

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Core.Mi.SpanX
theorem itSpans_pk_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → GlobalTheory.Core.Mi.ItSpans ((_root_.GlobalTheory.Fam.pk_z W).MY (D.R.m - 1)) (_root_.GlobalTheory.Fam.pk_z W).MX (_root_.GlobalTheory.Fam.pk_z W).ItX := by
  intro hDS hHC D L hT Gi Gl Kc Yd cX ex W hP
  have hC := hP.bot.hyp.2.2.2.1
  have hok := GlobalTheory.Chain.StepVac.stepsOK _ _ _ _ _ _ _ hC.lev hC.models.inf hC.chain.ωY hC.chain.ωX hC.chain.vY hC.chain.vX
  have hm : 0 < D.R.m := lt_of_lt_of_le two_pos D.R.two_le_m
  obtain ⟨hw, hv⟩ := hok.2 W.P.A3.A.μ0 ⟨D.R.m - 1, by omega⟩ rfl
  have hle := GlobalTheory.ItOnto.kfinSpan_le_span_it hDS hHC D _ _ _ _ ((_root_.GlobalTheory.Fam.pk_z W).MY (D.R.m - 1)) (_root_.GlobalTheory.Fam.pk_z W).MX (_root_.GlobalTheory.Fam.pk_z W).θ (_root_.GlobalTheory.Fam.pk_z W).ψ _ _
    ((_root_.GlobalTheory.Fam.pk_z W).ωX W.P.A3.A.μ0) ((_root_.GlobalTheory.Fam.pk_z W).vX W.P.A3.A.μ0) (_root_.GlobalTheory.Fam.pk_z W).ItX hC.models.inf hw hv (hC.chain.ItX W.P.A3.A.μ0)
  intro v hv
  have hv' := hle (Submodule.subset_span ⟨v, fun τ => Submodule.subset_span (hv τ), rfl⟩)
  refine (Submodule.span_le.2 ?_) hv'
  rintro w ⟨P, u, hu, rfl⟩
  have hu' : u ∈ Submodule.comap ((_root_.GlobalTheory.Fam.pk_z W).ItX P) (Submodule.span ℂ
      {x | ∃ (P : PolF D D.sp.X'.rank (Yc D (D.R.m - 1)).rank) (y : (_root_.GlobalTheory.Fam.pk_z W).MX.Vec), KVecP (_root_.GlobalTheory.Fam.pk_z W).MX y ∧
        x = (_root_.GlobalTheory.Fam.pk_z W).ItX P (PiTensorProduct.tprod ℂ y)}) := by
    refine (Submodule.span_le.2 ?_) hu
    rintro _ ⟨y, hy, rfl⟩
    exact Submodule.subset_span ⟨P, y, fun τ => GlobalTheory.Core.Mi.StepSpans.isKFin_of_mem_kfin _ _ (hy τ), rfl⟩
  exact hu'
end GlobalTheory.Core.Mi.SpanX
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IteratesSpanLastStep

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.itSpans_MY_last_MX : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → GlobalTheory.Core.Mi.ItSpans ((_root_.GlobalTheory.Fam.pk_z W).MY (D.R.m - 1)) (_root_.GlobalTheory.Fam.pk_z W).MX (_root_.GlobalTheory.Fam.pk_z W).ItX := by
  first | exact @_root_.GlobalTheory.Core.Mi.SpanX.itSpans_pk_alt | exact _root_.GlobalTheory.Core.Mi.SpanX.itSpans_pk_alt | (intros; apply _root_.GlobalTheory.Core.Mi.SpanX.itSpans_pk_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Imports

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam.IsFam
theorem main_alt_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ f : _root_.GlobalTheory.Fam.FamilyCharacter W u, f.RowOK → f.c.Is ∧ (f.ColOK → ∀ t, (f.t t).Is) := by
  intro hDS hHC D L hT Gi Gl Kc Yd cX ex W u hP f hR
  have hC := hP.bot.hyp.2.2.2.1
  have hstd : IsStdChar D (_root_.GlobalTheory.Fam.pk_z W).ψ (-1) := (hC.chain.ωX W.P.A3.A.μ0).std
  have hinf : IsInfFam (_root_.GlobalTheory.Fam.pk_z W).θ := hC.models.inf
  have spanT : ∀ n (e : D.R.m - 1 = n), GlobalTheory.Core.Mi.ItSpans ((_root_.GlobalTheory.Fam.pk_z W).MY n) (_root_.GlobalTheory.Fam.pk_z W).MX
      (Eq.rec (motive := fun n _ => PolF D D.sp.X'.rank (Yc D n).rank →ₗ[ℂ] SmT (_root_.GlobalTheory.Fam.pk_z W).MX →ₗ[ℂ] SmT ((_root_.GlobalTheory.Fam.pk_z W).MY n)) (_root_.GlobalTheory.Fam.pk_z W).ItX e) := by
    intro n e
    subst e
    exact _root_.GlobalTheory.T.itSpans_MY_last_MX hDS hHC W hP
  refine ⟨⟨hstd, hinf, hR.x, (GlobalTheory.Unf.CoCptOf.coCpt_of_isAniso_or_posDef D D.sp.X').2 GlobalTheory.Hk3.StepX.gram_posDef_X,
    hR.meas.μf, hR.meas.ρJ, hR.meas.ρB, fun j hj => _root_.GlobalTheory.T.itSpans_MY_succ hDS hHC W hP j hj, fun j h => spanT _ (idx_top h)⟩, fun hCol t => ?_⟩
  exact
    { sBF := fun j ρ h => ⟨((hR.row t).sBF j ρ h).1, ((hR.row t).sBF j ρ h).2.1⟩
      sFB := fun j σ h => ⟨((hR.row t).sFB j σ h).1, ((hR.row t).sFB j σ h).2.1⟩
      pt := fun j hj P => GlobalTheory.Chain.InnerSteps.theta_pureTensorO hstd hinf _ _ _ _
        (GlobalTheory.VecTheta.isThetaFunO_stepVec ((hR.row t).vP j hj)) P
      ptT := fun j h P => GlobalTheory.Chain.InnerSteps.theta_pureTensorO hstd hinf _ _ _ _
        (GlobalTheory.VecTheta.isThetaFunO_stepVec ((hR.row t).vT j h)) P
      CC := fun j _ => ⟨_, _, le_rfl⟩
      CT := ⟨_, _, le_rfl⟩
      io := _root_.GlobalTheory.T.lift_s_eq_ci_smul_io W u hP f hR t
      ioT := _root_.GlobalTheory.T.lift_s_last_eq_ci_succ_smul_io W u hP f hR t
      cI := fun j hj => hR.meas.cIOf_ne_zero (_root_.GlobalTheory.Fam.complexLevelStructure W) t j hj
      ker := hCol.ker t
      e := hCol.e t
      eT := hCol.eT t
      stabK := hCol.stabK t
      stabS := hCol.stabS t }
end GlobalTheory.Fam.IsFam
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.famCh_is_and_tuples_is_of_colOK : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ f : _root_.GlobalTheory.Fam.FamilyCharacter W u, f.RowOK → f.c.Is ∧ (f.ColOK → ∀ t, (f.t t).Is) := by
  exact @_root_.GlobalTheory.Fam.IsFam.main_alt_alt
end
end
end
