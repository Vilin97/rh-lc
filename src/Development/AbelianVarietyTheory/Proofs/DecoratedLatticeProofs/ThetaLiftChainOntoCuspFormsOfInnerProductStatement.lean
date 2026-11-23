module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ArchimedeanThetaCorrespondenceTowersRealDataStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeParametersOfElementFromOneNonzeroValueStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultiplicitySpaceSpannedBySatakeEigenElementsStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainCoefVanishesOffLevelStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainCuspSpaceFiniteDimOfHarishChandra
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainHeckeParametersLinearIndependentStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainInnerProductsExistOfRapidDecay
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ParBoundW
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainLValuesNonvanishing
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainLevelPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainLocalZetaNonvanishingOfReal
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainOccurringParamsNormHalfRankBoundStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainRealZetaNonvanishingStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainUpwardInductionFixedMetric
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainAdjointNonvanishingStep
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainFockVectorLevelLawsStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainSurjectiveOfAdjointNonvanishingStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftUpwardsAdjointOfRapidDecay
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftUpwardsInCuspSpan
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftUpwardsNeZeroOfLValue

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainCuspSpaceFiniteDimOfHarishChandraStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaChainCuspSpaceFiniteDim_of_harishChandra : GlobalTheory.Published.HarishChandraFinite → ∀ D : D7, LevFacts D → FinDim D := by
  first | exact @GlobalTheory.ChainOnto.finDim_of_levFacts | exact GlobalTheory.ChainOnto.finDim_of_levFacts | (intros; apply GlobalTheory.ChainOnto.finDim_of_levFacts <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainInnerProductsExistOfRapidDecayStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaChainInnerProductsExist_of_rapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, MetEx D := by
  first | exact @GlobalTheory.ChainMetric.metEx | exact GlobalTheory.ChainMetric.metEx | (intros; apply GlobalTheory.ChainMetric.metEx <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainLValuesNonvanishingStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaChain_LValues_nonvanishing : ∀ D : D7, ChainLW D := by
  first | exact @GlobalTheory.ChainOnto.chainLW_holds | exact GlobalTheory.ChainOnto.chainLW_holds | (intros; apply GlobalTheory.ChainOnto.chainLW_holds <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainLocalZetaNonvanishingOfRealStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaChainLocalZetaNonvanishing_of_real : ∀ D : D7, MetEx D → LevFacts D → LevelLaw D → CoefSupp D → RealZeta D → ZetaNe D := by
  first | exact @GlobalTheory.ChainOnto.ZetaNeProof.zetaNe_of_real | exact GlobalTheory.ChainOnto.ZetaNeProof.zetaNe_of_real | (intros; apply GlobalTheory.ChainOnto.ZetaNeProof.zetaNe_of_real <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainAdjointNonvanishingStepStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaLiftChain_adjoint_nonvanishing_step : ∀ D : D7, FinDim D → ParOfVal D → UpSpan D → UpAdj D → UpPar D → UpNe D → StepUp D := by
  first | exact @GlobalTheory.ChainOnto.stepUp | exact GlobalTheory.ChainOnto.stepUp | (intros; apply GlobalTheory.ChainOnto.stepUp <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftUpwardsAdjointOfRapidDecayStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaLiftUpwardsAdjoint_of_rapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, UpAdj D := by
  first | exact @GlobalTheory.ChainOnto.upAdj_of_cuspRapidDecay | exact GlobalTheory.ChainOnto.upAdj_of_cuspRapidDecay | (intros; apply GlobalTheory.ChainOnto.upAdj_of_cuspRapidDecay <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftUpwardsInCuspSpanStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaLiftUpwards_in_cuspSpan : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ D : D7, GlobalTheory.ChainOnto.LevFacts D → GlobalTheory.ChainOnto.LevelLaw D → GlobalTheory.ChainOnto.UpSpan D := by
  first | exact @GlobalTheory.ChainOnto.upSpan_of | exact GlobalTheory.ChainOnto.upSpan_of | (intros; apply GlobalTheory.ChainOnto.upSpan_of <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftUpwardsNeZeroOfLValueStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaLiftUpwards_ne_zero_of_lValue : ∀ D : D7, GlobalTheory.Core.Rk.IP.HeckeForm D → MetEx D → LevFacts D → ZetaNe D → UpNe D := by
  first | exact @GlobalTheory.ChainOnto.upNe_of_heckeForm | exact GlobalTheory.ChainOnto.upNe_of_heckeForm | (intros; apply GlobalTheory.ChainOnto.upNe_of_heckeForm <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainOntoCuspFormsOfInnerProduct

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem ontoAll_of_classicalTheorems : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → ∀ D : D7, GlobalTheory.Core.Rk.IP.HeckeForm D → UpPar D → OntoAll D := by
  intro hHCF hCRD hDSC hHCM hCW D hHF hUP
  have hLF : LevFacts D := GlobalTheory.T.thetaChain_level_properties D
  have hFD : FinDim D := GlobalTheory.T.thetaChainCuspSpaceFiniteDim_of_harishChandra hHCF D hLF
  have hMet : MetEx D := GlobalTheory.T.thetaChainInnerProductsExist_of_rapidDecay hCRD D
  have hES : EigSpan D := GlobalTheory.T.multiplicity_space_spanned_by_satake_eigen_elements hCRD D hFD hMet hLF
  have hPI : ParIndep D := GlobalTheory.T.thetaChain_heckeParameters_linearIndependent D
  have hPOV : ParOfVal D := GlobalTheory.T.hecke_parameters_of_element_from_one_nonzero_value hCRD D hMet hLF
  have hPB : ParBoundW D := GlobalTheory.T.theta_chain_occurring_params_norm_half_rank_bound hCRD D hLF
  have hLL : LevelLaw D := GlobalTheory.T.thetaLiftChain_fockVector_levelLaws D
  have hCS : CoefSupp D := GlobalTheory.T.thetaChainCoef_vanishes_off_level D
  have hArch : GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ArchOnRecord D := GlobalTheory.T.archimedeanThetaCorrespondence_towers_real_data hDSC hHCM D
  have hRZ : RealZeta D := GlobalTheory.T.thetaChain_realZeta_nonvanishing hHCM D hArch
  have hZN : ZetaNe D := GlobalTheory.T.thetaChainLocalZetaNonvanishing_of_real D hMet hLF hLL hCS hRZ
  have hUN : UpNe D := GlobalTheory.T.thetaLiftUpwards_ne_zero_of_lValue D hHF hMet hLF hZN
  have hUS : UpSpan D := GlobalTheory.T.thetaLiftUpwards_in_cuspSpan hDSC hHCM hCRD hCW D hLF hLL
  have hUA : UpAdj D := GlobalTheory.T.thetaLiftUpwardsAdjoint_of_rapidDecay hCRD D
  have hSU : StepUp D := GlobalTheory.T.thetaLiftChain_adjoint_nonvanishing_step D hFD hPOV hUS hUA hUP hUN
  have hCL : ChainLW D := GlobalTheory.T.thetaChain_LValues_nonvanishing D
  have hCU : ChainUp D := chainUp_of D hMet hPB hCL hSU
  exact GlobalTheory.T.thetaLiftChain_surjective_of_adjoint_nonvanishing D hFD hMet hES hPI hCU

end GlobalTheory.ChainOnto
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainOntoCuspFormsOfInnerProductStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaLiftChain_onto_cuspForms_of_innerProduct : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → ∀ D : D7, GlobalTheory.Core.Rk.IP.HeckeForm D → UpPar D → OntoAll D := by
  first | exact @GlobalTheory.ChainOnto.ontoAll_of_classicalTheorems | exact GlobalTheory.ChainOnto.ontoAll_of_classicalTheorems | (intros; apply GlobalTheory.ChainOnto.ontoAll_of_classicalTheorems <;> assumption)
end
end
