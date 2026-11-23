module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.IsAut4
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.FerreroWashington
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AdjointLiftingOfCohomology
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PotentialModularityTower
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsHilbertModularFormCongrOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CyclicLiftRankTwoOfCyclicBaseChange
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.WsIIOfPrintsH
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ExistsPrimeIndex
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.RankFourAutomorphyOfTensor
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BirthIndS
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.EGIndAutCs
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
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Hypotheses4Z
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.ContRes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BirthSeedII
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.MPropMHol
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.MixSeedOf
public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.HilbertEisensteinWeightOneHolds
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BirthTop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PromodularityCaseThree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.PromodularityCaseThree
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Tactic.NormNum.Parity
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.CuFinal

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.IndAutLOfSplit

section

@[expose] public section




section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Published UpperTheory.V.Sd UpperTheory.V.Ws UpperTheory.V.Z.Bc UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.indAutLP_of_printsH_upQuad_upSol_indCs (H : _root_.UpperTheory.V.Af.HypothesesH') (hQ : UpQuadI) (hS : UpSolI) (hI : IndCs) : _root_.UpperTheory.V.Z.Win.Birth.IndAutLP :=
  _root_.UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.indAutLP_of_upQuad_upSol_indAutCs H hQ hS (_root_.UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.indAutCs_of_alt H.toClassicalTheorems hI)
end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SeedIIZ

section

@[expose] public section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S2
namespace UpperTheory.V.Z.Bc
theorem seedII_Z_alt (h : _root_.UpperTheory.V.Z.Bc.Hypotheses4Z') (hI : _root_.UpperTheory.V.Z.Win.Birth.IndAutLP) : _root_.UpperTheory.V.Ws.SeedIIAlt :=
  _root_.UpperTheory.V.Z.Bc.seedII_of_p_alt (_root_.UpperTheory.V.Z.Win.Birth.mixOfP (_root_.UpperTheory.Esk.mixSeed_of_alt h.h (_root_.UpperTheory.V.Z.Bc.propMHolZ_alt h))) hI
end UpperTheory.V.Z.Bc
end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BcIndCs

section

@[expose] public section




section
namespace UpperTheory.V.Z.Bc
theorem seedIIs_alt (hH : _root_.UpperTheory.V.Af.HypothesesH') : _root_.UpperTheory.V.Ws.SeedIIAlt :=
  have hA := hH.toClassicalTheorems
  _root_.UpperTheory.V.Z.Bc.seedII_Z_alt ⟨hH, Published.hilbert_eisenstein_weight_one_holds, Lit.oneUse⟩
    (_root_.UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.indAutLP_of_printsH_upQuad_upSol_indCs hH (_root_.UpperTheory.V.Z.Bc.upQuadI_of_alt hA (quadLiftRealToComplex_of_base_change hH.bc)) (_root_.UpperTheory.V.Z.Bc.upSolI_of_alt hA (cyclicLiftRankTwo_of_cyclic_base_change hH.cyc)) indCs)
end UpperTheory.V.Z.Bc
end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.Sp4In

section

@[expose] public section

namespace UpperTheory.V.Cu

theorem hFit : HFit := fun _ _ h ok f => ⟨ok, Or.inr ⟨h, f.five, f.sb, f.psi⟩⟩

end UpperTheory.V.Cu
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Sp4In

section

@[expose] public section




section
namespace UpperTheory.V.Cu
theorem sp4In_alt (hC : GradeZeroInterpolatingElement.CohomologyHyp) (hF : Published.FerreroWashington) (s2 : _root_.UpperTheory.V.Ws.SeedIIAlt) (s4 : _root_.UpperTheory.V.Cu.SeedIVAlt) (hP : _root_.UpperTheory.V.Ws.PMExAlt) : _root_.UpperTheory.V.Aut.SymplecticFourImageDense :=
  _root_.UpperTheory.V.Cu.main4_alt hC hF hFit s2 s4 hP
end UpperTheory.V.Cu
end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Sp4In0

section

@[expose] public section




section
open UpperTheory.Top
namespace UpperTheory.V.HV.DescentVanishingReductions
theorem sp4In0_alt (hH : _root_.UpperTheory.V.Af.HypothesesH') :
    _root_.UpperTheory.V.Aut.SymplecticFourImageDense :=
  _root_.UpperTheory.V.Cu.sp4In_alt (adjoint_lift_of_prints hH).coh
    _root_.UpperTheory.V.FW.ferreroWashington
    (_root_.UpperTheory.V.Z.Bc.seedIIs_alt hH)
    (_root_.UpperTheory.V.Z.Win.Birth.fourth_initial_of_prints_h hH)
    (pmEx_of_printsH hH)
end UpperTheory.V.HV.DescentVanishingReductions
end
end
end
