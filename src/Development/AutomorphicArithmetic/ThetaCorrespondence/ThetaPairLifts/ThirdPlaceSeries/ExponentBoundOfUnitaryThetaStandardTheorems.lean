module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelCohomologicalModel
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsConj
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Formalism.PieriBlockIdeals.StatementE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylLatticeExactExponentBlockCut
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ModelStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExpStOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FrameStOfSmallStStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisAtPlaceOfAutomorphicAtPlace
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SmallnessCondition
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ModelStOfFrames
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NumSt
public import Formalism.SharpRestriction.Divisibility.JumpSets
public import Development.AutomorphicArithmetic.PrimeDiscriminants.ExcSet
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.Definitions.Divisors.SumExpSt
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.LocalToGlobal.Divisibility.RowLatLemmas
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
import Formalism.PieriBlockIdeals.PieriColumnMinors.ParameterBounds
public import Formalism.SharpRestriction.GlobalSchurBounds.MainSup
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SumExpStStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylLatticeExactExponentBlockCutStatement

section

@[expose] public section

open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds

theorem _root_.GlobalTheory.T.weylLattice_exact_exponent_block_cut : Formalism.CohomologicalDescent.E.ExCut := by
  first | exact @GlobalTheory.LeviCut.exCut | exact GlobalTheory.LeviCut.exCut | (intros; apply GlobalTheory.LeviCut.exCut <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExpStOfStatement

section

@[expose] public section



section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds

theorem _root_.GlobalTheory.T.expSt_of_num_sumExp_model : Formalism.CohomologicalDescent.E.ExCut → _root_.GlobalTheory.ExpTie.NumStAlt → _root_.GlobalTheory.ExpTie.ExponentSumStatement → _root_.GlobalTheory.ExpTie.ModelStatement → _root_.GlobalTheory.BigOn.ExponentStatement := by
  first | exact @_root_.GlobalTheory.ExpTie.Asm.expSt_of_alt | exact _root_.GlobalTheory.ExpTie.Asm.expSt_of_alt | (intros; apply _root_.GlobalTheory.ExpTie.Asm.expSt_of_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ModelStOfFramesStatement

section

@[expose] public section



section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

theorem _root_.GlobalTheory.T.model_statement_of_crystalline_chebotarev_frame_gal : GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.ChebotarevDegreeOne → _root_.GlobalTheory.ExpTie.SmallnessCondition → _root_.GlobalTheory.ExpTie.FrameStatement' → _root_.GlobalTheory.ExpTie.GaloisStatement → _root_.GlobalTheory.ExpTie.ModelStatement := by
  first | exact @_root_.GlobalTheory.ExpModel.modelSt_of_small_frame_gal | exact _root_.GlobalTheory.ExpModel.modelSt_of_small_frame_gal | (intros; apply _root_.GlobalTheory.ExpModel.modelSt_of_small_frame_gal <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

namespace GlobalTheory.ExpTie

theorem not_dvd_discr_host (D : D7) {l : ℕ} (hl : l.Prime) (hS : l ∉ Formalism.MainNotions.JumpSetsAlt.excSet D) :
    ¬ ((l : ℕ) : ℤ) ∣ NumberField.discr D.host.E :=
  UpperTheory.ExcSet.not_dvd_discr D hl hS

end GlobalTheory.ExpTie
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SmallStAltAlt

section

@[expose] public section



section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
namespace GlobalTheory.ExpTie
theorem smallSt_alt : _root_.GlobalTheory.ExpTie.SmallnessCondition := by
  unfold _root_.GlobalTheory.ExpTie.SmallnessCondition _root_.GlobalTheory.ExpTie.InRangeAlt _root_.GlobalTheory.BigOn.AtPtsAlt
  refine Formalism.MainNotions.Closed.of_all fun Fm CH => ?_
  refine _root_.GlobalTheory.BigTop.EventuallyAtPoints.of_forall fun x hx i p hR _ => ?_
  intro j P W hD hN w _ hWR
  have hC := Formalism.IndefR.Links.complex_data_conditions_base_level_of_primitive_links hR.ok hR.sep p.charW hR.prim
  have hst := DefFam3.toSub2_stable hC.stable
  have hin := DefFam3.toSub2_inBlock hR.prim.block
  refine ⟨Formalism.EigenvalueLevelCeiling.plc_prime w, ?_, ?_, fun k => DefFam.stable_lifts hst j _ k, DefFam.inBlock_lifts hin j _⟩
  · exact (Formalism.CohomologicalDescent.LogSmallConstantBounds.paramsLargePrime_holds P hN.1 hN.2.1 _ hWR.1).2.2.2.2.2.1
  · refine not_dvd_discr_host _ (Formalism.EigenvalueLevelCeiling.plc_prime w) ?_
    rw [← hD.special]
    exact hWR.2.2.2
end GlobalTheory.ExpTie
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SmallStStatement

section

@[expose] public section



section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

theorem _root_.GlobalTheory.T.small_estimate : _root_.GlobalTheory.ExpTie.SmallnessCondition := by
  first | exact @_root_.GlobalTheory.ExpTie.smallSt_alt | exact _root_.GlobalTheory.ExpTie.smallSt_alt | (intros; apply _root_.GlobalTheory.ExpTie.smallSt_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExponentBoundOfUnitaryThetaStandardTheorems

section

@[expose] public section



section
section
set_option autoImplicit false
namespace GlobalTheory.BigOn
theorem exponent_bound_of_unitaryThetaStandardTheorems_alt :
    GlobalTheory.Published.ClozelCohomological →
      GlobalTheory.Published.HeckeLAdicCharacter →
      GlobalTheory.Published.ChebotarevDegreeOne →
      _root_.UpperTheory.GalS.CuspUAlt →
      _root_.GlobalTheory.Published.BaseChangeDefiniteUnitaryGroup →
      GlobalTheory.Published.BhattScholzeCrystallineLattices →
      GlobalTheory.Published.HeckeLAdicCharacterAbove →
      _root_.UpperTheory.Zero.LLC.RecTExists →
      _root_.GlobalTheory.BigOn.ExponentStatement :=
  fun hCoh hHecke hCheb hGal hBC hBS hAbove hLL =>
    _root_.GlobalTheory.T.expSt_of_num_sumExp_model GlobalTheory.T.weylLattice_exact_exponent_block_cut _root_.GlobalTheory.ExpTie.numSt_alt _root_.GlobalTheory.T.sum_expansion'
      (_root_.GlobalTheory.T.model_statement_of_crystalline_chebotarev_frame_gal hBS hCheb _root_.GlobalTheory.T.small_estimate (_root_.GlobalTheory.T.frame_statement_of_small_statement _root_.GlobalTheory.T.small_estimate)
        (_root_.GlobalTheory.T.galois_frame_compatibility_alt hCoh hHecke hCheb hGal hBC hBS hAbove hLL _root_.GlobalTheory.T.small_estimate))
end GlobalTheory.BigOn
end
section

theorem _root_.GlobalTheory.T.expSt_of_base_change_and_crystalline_lattices : GlobalTheory.Published.ClozelCohomological → GlobalTheory.Published.HeckeLAdicCharacter → GlobalTheory.Published.ChebotarevDegreeOne → _root_.UpperTheory.GalS.CuspUAlt → _root_.GlobalTheory.Published.BaseChangeDefiniteUnitaryGroup → GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.HeckeLAdicCharacterAbove → _root_.UpperTheory.Zero.LLC.RecTExists → _root_.GlobalTheory.BigOn.ExponentStatement := by
  first | exact @_root_.GlobalTheory.BigOn.exponent_bound_of_unitaryThetaStandardTheorems_alt | exact _root_.GlobalTheory.BigOn.exponent_bound_of_unitaryThetaStandardTheorems_alt | (intros; apply _root_.GlobalTheory.BigOn.exponent_bound_of_unitaryThetaStandardTheorems_alt <;> assumption)
end
end
end
end
