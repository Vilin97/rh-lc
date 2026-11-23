module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BoundAtTwoThreeFamilyFon
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoLocalConditionAllLocalizations
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionComparisonAdmissibleEveryPlaceOver
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontainePropertiesAllPlacesAlt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralTateH2TopStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetPointGood
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameDescentConditionsEveryLocalisation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedHomsBoundedByClassNumberOfArtinStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisConditionFourOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisConditionThreeOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HoldsAll
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsMoreExtraStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainAltAltTer

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoLocalConditionAllLocalizationsStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

theorem _root_.GlobalTheory.T.blochKato_localCondition_all_localizations : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.admBK i := by
  first | exact @GlobalTheory.AdmBK.admBK_loc_of_blochKato_tateDuality_euler | exact GlobalTheory.AdmBK.admBK_loc_of_blochKato_tateDuality_euler | (intros; apply GlobalTheory.AdmBK.admBK_loc_of_blochKato_tateDuality_euler <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionComparisonAdmissibleEveryPlaceOverStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

theorem _root_.GlobalTheory.T.completion_comparison_admissible_every_place_over : ∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility i := by
  first | exact @GlobalTheory.BridgeTie.localCoefficientCompatibility | exact GlobalTheory.BridgeTie.localCoefficientCompatibility | (intros; apply GlobalTheory.BridgeTie.localCoefficientCompatibility <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsFurtherAlt

section

@[expose] public section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace GlobalTheory.SetPtOff
theorem main_alt_alt : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → ∀ i, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, SetPt i (X.r i) (X.ρ i) π := by
  intro hP D L P nch HW F Cm X C₂ hS i hi π hπ
  have fa := hS.facts
  have hHub := _root_.GlobalTheory.T.split_bound_of_params_alt hP.font hP.fin GlobalTheory.Published.cheb_holds D L HW F (rowC C₂) nch X 120 0 hS.canon P
    (by linarith [hS.big]) le_rfl (by exact_mod_cast (Real.exp_pos _).le) (fa.admJ L hS.par) hS.par67 fa.admA
    fa.Conclusion1.1 fa.Conclusion1.2.2 fa.Conclusion2.1 fa.Conclusion2.2.2 fa.rhoBar fa.large.2.1 fa.large.2.2 fa.nct fa.trip fa.same fa.block
    fa.muUnr fa.depthG
  have hR : RestPt i (X.r i) (X.ρ i) π := hHub.2.2.2.2.2.2.2.1 i hi π hπ
  have hHG : HG D.nd D.naut i := ⟨π, (D.Zgood_tie i π).1 hπ⟩
  have hZ : π ∈ D.nd.Z i := (D.Z_tie i π).2 ((D.Zgood_tie i π).1 hπ).1
  have hJ := _root_.GlobalTheory.JumpStatement.holds_all_alt D L (fa.admJ L hS.par)
  have hdec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i (X.r i) (X.ρ i) π :=
    semisimple_decomposition_of D i (X.r i) (X.ρ i) π fa.admA.2.2.2.2.2.2 hR.good hR.rho hR.ss
  exact ⟨_root_.Formalism.MainNotions.N.galois_condition_one_of_alt D i (X.r i) fa.Conclusion1.1 hR.good,
    _root_.GlobalTheory.GTwoTheta.main_alt_alt hP.font D L fa.g2.1 hJ.1 hJ.2.2.1 i (X.r i) (X.ρ i) π hR.good hR.ng0 hR.ng1 hZ hdec,
    _root_.Formalism.MainNotions.N.galois_condition_three_of_alt_alt D i (X.r i) (X.ρ i) π fa.Conclusion1.1 hR.good hdec hR.cont hHG fa.rhoBar (litBurnside_all D) hR.g3,
    _root_.Formalism.MainNotions.N.admG4_of_goodR D i (X.r i) fa.Conclusion1.1 hR.good,
    galois_condition_five_of D i (X.r i) fa.Conclusion2.1 hHG hR.good,
    (GlobalTheory.TameDesign.main D i).2,
    galois_condition_six_of D i (X.r i) fa.Conclusion2.2.1 hHG hR.good,
    GlobalTheory.T.blochKato_localCondition_all_localizations hP.bk hP.tate hP.euler D i,
    continuous_family_of D i (X.r i) hR.good,
    semisimple_family_of D i (X.r i) hR.good,
    hdec, hR.eps, GlobalTheory.T.completion_comparison_admissible_every_place_over D i, hR.shape, GlobalTheory.FontaineAdm.fontaineProperties_all_places D i,
    GlobalTheory.T.integral_tate_H2_top hP.tate D i, GlobalTheory.T.unramifiedClassFieldBound_of_artin hP.artin D i⟩
end GlobalTheory.SetPtOff
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SetPointGood

section

@[expose] public section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem _root_.GlobalTheory.T.set_pt_of_setup_not_twisted : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → ∀ i, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, SetPt i (X.r i) (X.ρ i) π := by
  first | exact @_root_.GlobalTheory.SetPtOff.main_alt_alt | exact _root_.GlobalTheory.SetPtOff.main_alt_alt | (intros; apply _root_.GlobalTheory.SetPtOff.main_alt_alt <;> assumption)
end
end
end
