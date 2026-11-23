module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.RealBranch
public import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.BranchDefs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodNonvanishingAscentOfDepthDataStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DependenceFixedStatement
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodRowsPrincipalLevelAreRowsStatement
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SizesOfSizeRows
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowSeparationByRealFunctionalsOfChainStepsStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.BranchPeriod
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BesselSeparate
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ConvergenceOfSeparatingFamily
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsSeesawPairOfThetaData
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultTApplyRapidDec
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SeparatingFamilyExtendsByTwistedRow
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SeparatingFamilyHasModels
public import Development.AbelianVarietyTheory.Definitions.Foundations.UnitarySixTwoHarishChandraParameter
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodParParBLast
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPermOfCardFalse
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridParameterRegularCardEqRankFormula
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelModelsOfFunctoriality
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistCoreSurjectiveOfLocalComponents

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstRowTowerMultiplicitySpacesOfArrow

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SepRows

theorem rowTower_of_step : RowModels → RowStep → RowTower := by
  intro hmod hstep D q hs T L μ0 hL sc hc G W M hM M₀ h₀ n
  induction n with
  | zero =>
    intro h
    refine ⟨parB (Ptw D) 0, M₀, (parRow_zero D sc.cGap).symm, h₀, fun _ w => w, fun t ht Φ => ⟨t, ht, fun ρ w => ⟨trivial, rfl⟩⟩⟩
  | succ n ih =>
    intro h
    obtain ⟨S, MA, hS, hA, vec, hvec⟩ := ih (Nat.le_of_succ_le h)
    obtain ⟨MB, hB⟩ := hmod D q hs T L μ0 hL sc hc G W M hM (n + 1) h
    obtain ⟨It, hIt⟩ := hstep D q hs T L μ0 hL sc hc G W M hM n h S _ MA MB hS rfl hA hB
    refine ⟨_, MB, rfl, hB, fun ρ w => It (ρ ⟨n, h⟩) (vec ρ w), fun t ht Φ => ?_⟩
    obtain ⟨F, hF, hF'⟩ := hvec t ht Φ
    obtain ⟨F', hF1, hF2⟩ := hIt F hF (Φ ⟨n, h⟩)
    refine ⟨F', hF1, fun ρ w => ?_⟩
    obtain ⟨h1, h2⟩ := hF' ρ w
    obtain ⟨h3, h4⟩ := hF2 (ρ ⟨n, h⟩) (vec ρ w)
    rw [← h2] at h3 h4
    exact ⟨⟨h1, h3⟩, h4⟩

end GlobalTheory.SepRows
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstRowTowerMultiplicitySpacesOfArrowStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.firstRowTower_multiplicitySpaces_of_arrow : RowModels → RowStep → RowTower := by
  first | exact @GlobalTheory.SepRows.rowTower_of_step | exact GlobalTheory.SepRows.rowTower_of_step | (intros; apply GlobalTheory.SepRows.rowTower_of_step <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.LargeScaleSizesImplyGapConditions

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows

namespace GlobalTheory.SepRows

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sizeGap_of_sizes : SizeGap :=
  fun _ => ⟨0, fun _ large₂ _ _ h => GlobalTheory.RowSizes.sizes_of_sizeRows large₂ h⟩

end GlobalTheory.SepRows

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.LargeScaleSizesImplyGapConditionsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.largeScaleSizes_imply_gapConditions : SizeGap := by
  first | exact @GlobalTheory.SepRows.sizeGap_of_sizes | exact GlobalTheory.SepRows.sizeGap_of_sizes | (intros; apply GlobalTheory.SepRows.sizeGap_of_sizes <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelTowerRapidDecay

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SepRows.RowRapidPf

theorem multT_le_empty {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) :
    MultT θ M J χ ≤ MultT θ M ∅ 1 :=
  Submodule.map_mono (Submodule.span_mono fun _ h =>
    ⟨h.aut, h.cusp, fun _ _ hk => absurd hk (Set.notMem_empty _), h.equiv, h.cont⟩)

end GlobalTheory.SepRows.RowRapidPf

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RapidDecayOfSeparatingFamily

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.SepRows.RowRapidPf
theorem separating_family_rapid_decay : _root_.GlobalTheory.FunPr.ThetaLocalInputs → RowTower → RowRapid := by
  intro hP hT D hq hs T L μ0 hL sc hc G W M hM M₀ hM₀ t ht w
  have ht' : t ∈ MultT W.θ M₀ ∅ 1 := multT_le_empty W.θ M₀ _ _ ht
  have key : ∀ ρ Φ n (h : n ≤ D.R.m),
      PathConv W M (rowPath T 0 n) (rowFam 0 n fun i => W.datum ρ Φ (Fin.castLE h i)) (t w) ∧
        RapidDec (G.V (.grid n 0)) (part W M ρ Φ (t w) n h) := by
    intro ρ Φ n h
    obtain ⟨S, MB, -, -, vec, hv⟩ := hT D hq hs T L μ0 hL sc hc G W M hM M₀ hM₀ n h
    obtain ⟨F', hF', hF⟩ := hv t ht' Φ
    obtain ⟨hcv, heq⟩ := hF ρ w
    refine ⟨hcv, ?_⟩
    rw [heq]
    exact (GlobalTheory.ChainOnto.MultRapid.multT_apply_rapidDec hP.cuspRapidDecay D _ S MB W.θ W.θ_is ∅ 1 F' hF' (vec ρ w)).2.2
  exact ⟨fun ρ Φ n h => (key ρ Φ n h).2, fun ρ Φ => (key ρ Φ D.R.m le_rfl).1⟩
end GlobalTheory.SepRows.RowRapidPf
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rapid_decay_of_separating_family : _root_.GlobalTheory.FunPr.ThetaLocalInputs → RowTower → RowRapid := by
  first | exact @_root_.GlobalTheory.SepRows.RowRapidPf.separating_family_rapid_decay | exact _root_.GlobalTheory.SepRows.RowRapidPf.separating_family_rapid_decay | (intros; apply _root_.GlobalTheory.SepRows.RowRapidPf.separating_family_rapid_decay <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SeparatingModelsOfSeparatingData

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.SepRows
open Matrix
theorem separating_models_of_separating_data : _root_.GlobalTheory.FunPr.ThetaLocalInputs → RowModels := by
  intro hP D _ _ T L μ0 _ sc hsc G W M _ i hi
  have hDS := hP.discreteSeriesUpqExists
  classical
  rcases Nat.eq_zero_or_pos i with rfl | hi1
  ·
    rw [parRow_zero]
    have hV : (G.V (.grid 0 0)).SigOK := D.sp.Y_sig (min 0 D.R.m)
    refine exists_model_of_enum hDS hV (W.onb (.grid 0 0)) (W.cart (.grid 0 0)) (fun τ => ?_)
      (W.onb_is (.grid 0 0) ⟨Nat.zero_le _, Nat.zero_le _⟩)
    obtain ⟨lam, ε, hE, hH, -, hq⟩ := GlobalTheory.ChainModels.goodPar_parB D (min 0 D.R.m) (min_le_right _ _) τ
    have e : parB (Ptw D) (min 0 D.R.m) τ = parB (Ptw D) 0 τ := by rw [Nat.zero_min]
    rw [e] at hE
    exact ⟨lam, ε, hE, hH, hq⟩
  · rw [hsc]
    have hX : (Node.grid i 0).InRange D.R.m := ⟨hi, Nat.zero_le _⟩
    have hv := G.isV hX (fun j e => by cases e; omega)
    refine exists_model_of_enum hDS hv.sigOK (W.onb (.grid i 0)) (W.cart (.grid i 0)) (fun τ => ?_) (W.onb_is _ hX)
    obtain ⟨hr, hc, hm⟩ := GlobalTheory.GridJoin.dualPar_shift_counts (if Odd (i + 0) then -(1 / 2) else 0)
      (GlobalTheory.GridParDCount.isRegular_parD D 1 τ hi (Nat.zero_le D.R.m))
    have hc' : (parRow D 1 i τ).card = (G.V (.grid i 0)).rank :=
      hc.trans ((GlobalTheory.GridParDCount.card_parD D 1 τ hi (Nat.zero_le _)).trans hv.rank.symm)
    obtain ⟨lam, ε, hE, hcount⟩ := GlobalTheory.GridJoin.exists_isEnum_of_regular hr hc'
    refine ⟨lam, ε, hE, isHCParam_dual_parV D i 0 τ lam ε hv.rank hE, ?_⟩
    rw [hcount, hv.sig]
    exact hm.trans (GlobalTheory.SignedHC.Model.nMinus_parD _ i 0)
end GlobalTheory.SepRows
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_models_of_separating_data : _root_.GlobalTheory.FunPr.ThetaLocalInputs → RowModels := by
  first | exact @_root_.GlobalTheory.SepRows.separating_models_of_separating_data | exact _root_.GlobalTheory.SepRows.separating_models_of_separating_data | (intros; apply _root_.GlobalTheory.SepRows.separating_models_of_separating_data <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RealFunctionalsSeparateOfHypothesis

section

@[expose] public section

section
namespace UpperTheory.Lit
theorem real_functionals_separate_of_hypothesis
    (P : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hHowe : GlobalTheory.Hk3.HoweUnram)
    (hSW : GlobalTheory.Published.SiegelWeilUnitaryConvergent)
    (realIn : Branch.RealInputE) :
    GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate := by
  have rowModels := _root_.GlobalTheory.T.exists_models_of_separating_data P
  have rowStep := _root_.GlobalTheory.T.separating_family_extend_by_twist P (_root_.GlobalTheory.T.exists_seesaw_pair_of_theta_data P) rowModels
  have rowTower := GlobalTheory.T.firstRowTower_multiplicitySpaces_of_arrow rowModels rowStep
  have conv := _root_.GlobalTheory.T.convergence_of_separating_family P rowTower
  have per := Branch.periodNe_of_eigen P.harishChandraModules P.casselmanWallach P.cuspRapidDecay realIn
  have onto := _root_.GlobalTheory.T.twist_core_surjective P P.harishChandraFinite P.cuspRapidDecay P.discreteSeriesCover
    P.harishChandraModules P.casselmanWallach hHowe P.weilRepresentationUnitaryPair
    P.weilSiegelFormulaUnitary hSW P.doublingMethod P.unramifiedDoublingGL
  have weak := GlobalTheory.T.rowSeparation_by_realFunctionals_of_chain_steps GlobalTheory.T.largeScaleSizes_imply_gapConditions (_root_.GlobalTheory.T.exists_separating_models P) (_root_.GlobalTheory.T.rapid_decay_of_separating_family P rowTower) per onto
    (GlobalTheory.T.bessel_period_nonvanishing_ascent_of_depth_data GlobalTheory.T.dependence_fixed)
  exact _root_.UpperTheory.Lit.bessel_separate_of_step_gap P rowTower GlobalTheory.T.largeScaleSizes_imply_gapConditions GlobalTheory.T.goodRows_principalLevel_are_rows conv weak
end UpperTheory.Lit
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FunctionalsSeparateOfHoweUnramOfSiegelWeil

section

@[expose] public section

section
noncomputable section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell GlobalTheory.SepReal
open scoped InnerProductSpace
namespace UpperTheory.Lit.Branch
variable {n : ℕ}
variable {e : Option (Fin n) ≃ Fin (n + 1)} {ε : Fin (n + 1) → Bool} {lam : Fin (n + 1) → ℝ} {ε' : Fin n → Bool}
  {mu : Fin n → ℝ} {B : ℝ}
end UpperTheory.Lit.Branch
end
namespace UpperTheory.Lit
theorem functionalsSeparate_of_howeUnram_of_siegelWeil (P : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hH : GlobalTheory.Hk3.HoweUnram)
    (hSW : GlobalTheory.Published.SiegelWeilUnitaryConvergent) : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate :=
  _root_.UpperTheory.Lit.real_functionals_separate_of_hypothesis P hH hSW realInputE_holds
end UpperTheory.Lit
end
end
end
