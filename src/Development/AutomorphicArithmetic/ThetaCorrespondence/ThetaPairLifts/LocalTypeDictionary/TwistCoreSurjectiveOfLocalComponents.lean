module

public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoreChainCompositesExistLiftCombinationsStatement
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticeChangeOfLatticeLawsStatement
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteTopSpaceColumnValuesStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DependenceFixedStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TestGridCommonDataPropertiesHoldStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TestGridStageLatticesPropertiesProofStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SeparatingFamilyHasModels
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistEvenSurjectiveOfRepresentatives

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoreChainLiftsSurjectiveOfEvenRank

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CoreOnto

theorem coreOnto_of_chain (hO : ∀ D : D7, GlobalTheory.EvenOnto.OntoAll D) (hC : ComOK) (hS : StageOK) (hE : ChainEx) (hT : TopCols) :
    CoreOnto := by
  intro D hq hsz T L μ0 hL sc hgap G W M hM v MP _hcart y hy x hx
  have hRL := GlobalTheory.T.selfDualLattice_changeOfLattice_laws D
  obtain ⟨⟨r₀, hr₀⟩, hst₀⟩ := hS D hq T L μ0 hL sc G W M hM 0 (Nat.zero_le _)
  obtain ⟨r, Mm, _hr, Θ, hR, hB⟩ := hE D hq hsz T L μ0 hL sc hgap G W M hM v r₀ MP hr₀ D.R.m le_rfl
  have hcom : (gridCom W).Is := hC D hq hsz T L μ0 hL sc hgap G W M hM
  have hs0 : (gridStage G v 0 r₀ MP).Is (gridCom W) 0 := hst₀ r₀ hr₀ v MP
  have hsurj := hO D (gridCom W) hcom (gridStage G v 0 r₀ MP) hs0 D.R.m le_rfl _ Θ hR
  have hyCC : y ∈ (gridStage G v 0 r₀ MP).CC (gridCom W) := by
    have h := (hRL.2.1 (G.V (.core 0)) r₀ W.θ _ MP (lev G (.core 0) : Set _)).1
    exact (SetLike.ext_iff.mp h y).mpr hy
  obtain ⟨y', hy'⟩ := hsurj ⟨y, hyCC⟩
  have hx' : x ∈ (gridStage G v 0 r₀ MP).KF := by
    have h := (hRL.2.1 (G.V (.core 0)) r₀ W.θ _ MP (lev G (.core 0) : Set _)).2.1
    rw [← h] at hx
    exact hx
  have key := hB y' x hx'
  rw [hy'] at key
  refine Submodule.span_mono ?_ key
  rintro F₀ ⟨w, Ψ, hrap, hstep, h0, hm⟩
  refine ⟨Ψ, ⟨hrap, hstep⟩, h0, ?_⟩
  have htop : y'.1 ∈ CoreForms G W.θ D.R.m Mm := by
    have h := (hRL.2.1 (G.V (.core D.R.m)) r W.θ _ Mm (lev G (.core D.R.m) : Set _)).1
    exact (SetLike.ext_iff.mp h y'.1).mp y'.2
  obtain ⟨c, hc, ξ, hξ⟩ := hT D hq T L μ0 hL sc G W M hM Mm _ htop w
  exact ⟨c, hc, ξ, hm.trans hξ⟩

end GlobalTheory.CoreOnto

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoreChainLiftsSurjectiveOfEvenRankStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.coreChain_lifts_surjective_of_evenRank : (∀ D : D7, GlobalTheory.EvenOnto.OntoAll D) → ComOK → StageOK → ChainEx → TopCols → CoreOnto := by
  first | exact @GlobalTheory.CoreOnto.coreOnto_of_chain | exact GlobalTheory.CoreOnto.coreOnto_of_chain | (intros; apply GlobalTheory.CoreOnto.coreOnto_of_chain <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistCoreSurjectiveOfLocalComponents

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Twist.CoreOntoAssembly
theorem twist_core_surjective_of_local_components : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → CoreOnto := by
  intro hP hHCF hCRD hDSC hHCM hCW hHowe hWeil hWSF hSWC hDbl hUDG
  exact GlobalTheory.T.coreChain_lifts_surjective_of_evenRank
    (_root_.GlobalTheory.T.twist_even_surjective_of_representatives hHCF hCRD hDSC hHCM hCW hHowe hWeil hWSF hSWC hDbl hUDG)
    GlobalTheory.T.testGridCommonData_properties_hold GlobalTheory.T.testGridStageLatticesProperties_proof
    (GlobalTheory.T.core_chain_composites_exist_lift_combinations hDSC hHCM hCRD hCW GlobalTheory.T.dependence_fixed (_root_.GlobalTheory.T.exists_separating_models hP))
    GlobalTheory.T.definiteTopSpace_columnValues
end GlobalTheory.Twist.CoreOntoAssembly
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.twist_core_surjective : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → CoreOnto := by
  first | exact @_root_.GlobalTheory.Twist.CoreOntoAssembly.twist_core_surjective_of_local_components | exact _root_.GlobalTheory.Twist.CoreOntoAssembly.twist_core_surjective_of_local_components | (intros; apply _root_.GlobalTheory.Twist.CoreOntoAssembly.twist_core_surjective_of_local_components <;> assumption)
end
end
end
