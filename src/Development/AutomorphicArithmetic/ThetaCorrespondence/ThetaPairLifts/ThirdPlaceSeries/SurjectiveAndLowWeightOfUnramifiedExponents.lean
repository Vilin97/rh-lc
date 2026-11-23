module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BernsteinUnitaryProductIrreducible
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LamLowOfPublished
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LlOf
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelCohomologicalModel
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsConj
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SeriesRationalIntegral
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BadStOfBadW
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BadWStOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CompareOffOwnAtRuns
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExponentBoundOfUnitaryThetaStandardTheorems
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportStOfPrints
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
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoStOfPageSt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MaxSt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ModelSt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OntoXOfTwistSharesExp
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PageSt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RankAtPlacesRec
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ShareStOfShareWSt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ShareWStOfModelSt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceLatticeLeThetaLatticeAtPlace
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportStOfPrintsStatement

section

@[expose] public section



section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp

theorem _root_.GlobalTheory.T.exportSt_of_discrete_series_cover : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.ExportedStatement := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.exportSt_of_hypotheses_alt | exact _root_.GlobalTheory.BigOn.Exp.exportSt_of_hypotheses_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.exportSt_of_hypotheses_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportStOfReading

section

@[expose] public section



section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
namespace GlobalTheory.BigOn
theorem exportSt_of_reading_alt :
    GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
      GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach →
      GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.ExportedStatement :=
  _root_.GlobalTheory.T.exportSt_of_discrete_series_cover
end GlobalTheory.BigOn
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportStOfReadingStatement

section

@[expose] public section



section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp

theorem _root_.GlobalTheory.T.exportSt_of_reciprocity_and_casselman_wallach : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.ExportedStatement := by
  first | exact @_root_.GlobalTheory.BigOn.exportSt_of_reading_alt | exact _root_.GlobalTheory.BigOn.exportSt_of_reading_alt | (intros; apply _root_.GlobalTheory.BigOn.exportSt_of_reading_alt <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TupleReadBaseTupleEqFamily

section

@[expose] public section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BigOn.TwistBoundAtPlace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)

theorem tupleRead_baseTuple_eq_family : p.tupT D.what₂.mu0 = p.P.A3.A.μ0 :=
  p.charW.base.lev.xi_inj (by rw [p.tupXi D.what₂.mu0 (Or.inl rfl), p.Tp.trueColumnChoices_heckeChar_reference_eq_one, p.charW.base.lev.xi_base])

theorem twistedAt_of_mem {v : HeightOneSpectrum (𝓞 D.what₂.LL)} (hv : v ∈ p.R.twPl) : TwistedAt D (D.plEq.symm v) := by
  intro he
  apply p.charW.tup.mu_ne v hv
  have := p.tupAt (D.plEq.symm v)
  rw [he, tupleRead_baseTuple_eq_family, Equiv.apply_symm_apply] at this
  exact this.symm

theorem conj_mem {v : HeightOneSpectrum (𝓞 D.what₂.LL)} (hv : v ∈ p.R.twPl) : Formalism.DivisionValues.conjPl v ∈ p.R.twPl := by
  by_contra h
  have := p.charW.tup.mu_off _ h
  rw [p.charW.tup.mu_conj] at this
  exact p.charW.tup.mu_ne v hv this

end Point



theorem hasTwistBound_at {eps : ℝ} {Fm : FamP eps} {x : ℝ} {hx : Fm.x1 < x} {i : Fm.Ix x} (p : Pt Fm x hx i)
    {r : TwoRuns p.T p.P.Gp} {c : OnConst} {O : Obj p c} (hR : RecAt p (Fm.parT x hx i) r O)
    (hE : ∀ v ∈ p.R.twPl, ∀ j, GlobalTheory.TwistIndex.ExportTie p.P.A3.A (Fm.ex x hx i).nch (twE Fm x hx i) (R2 p) j (F2 p).P0
      (F2 p).ψ0⁻¹ 1 v (ownAt (Fm.D x i) v))
    (hS : LeafSup O) (hK : GlobalTheory.TraceClassRank.RankAtPlaces O)
    {N0 : (Fm.D x i).ntw.Tw → ℕ} {S : ∀ (i' : (Fm.D x i).ntw.Tw) (j : ℕ) (b : Bool), Finset ((Fm.D x i).nexp.Dat i' j b)}
    (hG : Formalism.MainNotions.TwGoodAt (Fm.D x i) (Fm.ex x hx i).nch ⟨twE Fm x hx i, N0, S⟩) : HasTwistBound O := by
  obtain ⟨hc, hinj, z, act, y, ht⟩ := hR.1.tied
  have tied : ∀ v ∈ p.R.twPl, TwistedAt (Fm.D x i) ((Fm.D x i).plEq.symm v) ∧
      ∀ j, GlobalTheory.TwistIndex.TiedAt p.P.A3.A (Fm.ex x hx i).nch (twE Fm x hx i) O v j (id j) := fun v hv =>
    ⟨twistedAt_of_mem p hv, fun j => ⟨(r.used v).full, p.alg, R2 p, p.κ, p.v₀, (hR.1.ok.laws v).p, fw2 p, hinj,
      (Fm.ex x hx i).errX, ownAt (Fm.D x i) v, _, _, _, z j, act j, GlobalTheory.OntoChain.mirIncl (R2 p), r.lev j, (F2 p).P0, (F2 p).ψ0⁻¹, 1, y v j,
      (ht v j).1, hE v hv j⟩⟩
  exact GlobalTheory.TwistIndex.exists_leafTW1_of_twGoodAt p.P.A3.A (Fm.ex x hx i).nch ⟨twE Fm x hx i, N0, S⟩ hG O id
    Function.injective_id (GlobalTheory.TwistIndex.goodPartLattice_of_leafSup hS)
    (fun w hw => ⟨fun j => ((hK w hw).1 j).2.1, fun j => ((hK w hw).2 j).2.1⟩)
    (fun w hw => ⟨tied w hw, tied _ (conj_mem p hw)⟩)

end GlobalTheory.BigOn.TwistBoundAtPlace
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistStOf

section

@[expose] public section



section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BigOn.TwistBoundAtPlace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)
end Point
theorem twistSt_of_alt (hE : _root_.GlobalTheory.BigOn.ExportedStatement) (hG : _root_.GlobalTheory.BigOn.GeometricStatement')
    (hK : _root_.GlobalTheory.BigOn.ForallRecordObjects fun _ _ _ _ _ _ O => GlobalTheory.TraceClassRank.RankAtPlaces O) : _root_.GlobalTheory.BigOn.TwistStatement' := by
  obtain ⟨a, ha, H⟩ := (hE.and hG).and hK
  refine ⟨a, ha, fun e he hle => ?_⟩
  obtain ⟨K, hK'⟩ := H e he hle
  refine ⟨K, fun Fm CH hc hL => ?_⟩
  obtain ⟨⟨⟨x1, E1⟩, ⟨c1, G1⟩⟩, ⟨c2, K1⟩⟩ := hK' Fm CH hc hL
  obtain ⟨x0, T0⟩ := hc.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨max c1 c2, fun c hcC hb => ?_⟩
  obtain ⟨x2, G2⟩ := G1 c ((le_max_left _ _).trans hcC) hb
  obtain ⟨x3, K2⟩ := K1 c ((le_max_right _ _).trans hcC) hb
  refine ⟨max (max x0 x1) (max x2 x3), fun x hx hle i p hp hM r O hR => ?_⟩
  have h0 : x0 ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hle)
  have h1 : x1 ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hle)
  have h2 : x2 ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hle)
  have h3 : x3 ≤ x := (le_max_right _ _).trans ((le_max_right _ _).trans hle)
  obtain ⟨-, N0, S, hTG⟩ := T0 x h0 hx i
  exact hasTwistBound_at p hR (E1 x hx h1 i p hp hM) (G2 x hx h2 i p hp hM r O hR).1 (K2 x hx h3 i p hp hM r O hR) hTG
end GlobalTheory.BigOn.TwistBoundAtPlace
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OntoXOfPrints

section

@[expose] public section



section
section
open GlobalTheory.BigOn
namespace GlobalTheory.BigOn
theorem ontoX_of_hypotheses_alt_alt : GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.ClozelCohomological → GlobalTheory.Published.HeckeLAdicCharacter → GlobalTheory.Published.ChebotarevDegreeOne → _root_.UpperTheory.GalS.CuspUAlt → _root_.GlobalTheory.Published.BaseChangeDefiniteUnitaryGroup → GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.HeckeLAdicCharacterAbove → GlobalTheory.Published.CuspRapidDecay → _root_.UpperTheory.Zero.LLC.RecTExists → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → _root_.GlobalTheory.BigOn.SurjectiveOntoX := by
  intro hGreen hCoh hHecke hCheb hGal hBC hBS hAbove hDecay hLL hCover hCW
  have hArtin : GlobalTheory.Published.GlobalArtinReciprocity :=
    GlobalTheory.Published.HeckeLAdicCharacter.globalArtin hHecke
  have hRay : GlobalTheory.Published.RayClassFieldSt :=
    GlobalTheory.Published.GlobalArtinReciprocity.rayClassFieldSt hArtin
  have hSer : GlobalTheory.SerStd.SeriesRatS := (GlobalTheory.seriesRatS_and_serInt_of_globalArtin hArtin).1
  have hExport : _root_.GlobalTheory.BigOn.ExportedStatement := by
    apply _root_.GlobalTheory.T.exportSt_of_reciprocity_and_casselman_wallach <;> with_reducible assumption
  have hPage : _root_.GlobalTheory.BigOn.PageStatement := _root_.GlobalTheory.BigOn.pageSt_alt
  have hGeo : _root_.GlobalTheory.BigOn.GeometricStatement' := _root_.GlobalTheory.BigOn.geoSt_of_pageSt_alt hPage
  have hRank := _root_.GlobalTheory.BigOn.rankLocSt_of_max_geo_runs _root_.GlobalTheory.BigOn.maxSt_alt hGeo _root_.GlobalTheory.BigOn.compareOffOwn_atRuns_alt
  have hTwist : _root_.GlobalTheory.BigOn.TwistStatement' := _root_.GlobalTheory.BigOn.TwistBoundAtPlace.twistSt_of_alt hExport hGeo hRank
  have hModel := _root_.GlobalTheory.ShareOn.modelSt_alt
  have hShare : _root_.GlobalTheory.BigOn.ShareStatement := _root_.GlobalTheory.ShareOn.shareSt_of_shareWSt_alt (_root_.GlobalTheory.ShareOn.shareWSt_of_modelSt_alt hModel)
  have hBad : _root_.GlobalTheory.BigOn.BadPlacesStatement := _root_.GlobalTheory.BigOn.badSt_of_badW_alt (_root_.GlobalTheory.BadWOn.badWSt_of_greenCuspidal_of_modelSt hGreen hModel)
  have hExp : _root_.GlobalTheory.BigOn.ExponentStatement := _root_.GlobalTheory.T.expSt_of_base_change_and_crystalline_lattices hCoh hHecke hCheb hGal hBC hBS hAbove hLL
  exact _root_.GlobalTheory.BigOn.ontoX_of_twist_shares_exp_alt hExport hTwist hShare hBad hExp
end GlobalTheory.BigOn
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SurjectiveAndLowWeightOfUnramifiedExponents

section

@[expose] public section



section
section
namespace GlobalTheory.Fc.S0
theorem ontoX_and_lamLow_of_unitaryGroupHypotheses' :
    _root_.GlobalTheory.Fc.S0.UnitaryGroupThirdPlaceHypotheses → _root_.GlobalTheory.BigOn.SurjectiveOntoX ∧ _root_.GlobalTheory.BigTop.LambdaLowerBound₂ := by
  intro P
  exact ⟨_root_.GlobalTheory.BigOn.ontoX_of_hypotheses_alt_alt P.greenCuspidal P.clozelCohomological
      P.heckeLAdicCharacter P.chebotarevDegreeOne
      P.galoisRepOfPolarizedCuspidal P.baseChangeDefiniteUnitary
      P.bhattScholzeCrystallineLattices P.heckeLAdicCharacterAbove P.cuspRapidDecay
      (_root_.UpperTheory.One.M.New.llOf_alt P.litN.loc.llc P.litN.loc.conv
      P.litN.loc.dzi P.litN.loc.brauer P.litN.loc.chev P.globalArtinReciprocity P.litN.loc.exh
      P.litN.loc.multi P.litN.loc.cos P.litN.loc.zel P.litN.loc.geo P.litN.loc.bz)
      P.discreteSeriesCover P.casselmanWallach,
    _root_.GlobalTheory.BigTop.lamLow_of_hypotheses_alt_alt P.cuspRapidDecay P.weilSiegelFormulaUnitary
      P.siegelWeilUnitaryConvergent P.doublingMethod P.unramifiedDoublingGL
      P.bernsteinZelevinskyFiniteness P.formalDegreeCompactDual⟩
end GlobalTheory.Fc.S0
end
end
end
end
