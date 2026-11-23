module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoefficientDataExistsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinHolomorphyOfHeightsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierJacobiCoefficientOfBoundStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierJacobiEisensteinStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierJacobiUnfoldingStatement
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierZeroHolds
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
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCharacterEtaCondition
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightFunctionsExist
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacobiMapsExist
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantFourierCoefficient
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolarPartIdentity
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PoleRealityStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularSectionOfHeights
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueMeasureIdentityStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightIdentityStatementStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalBoundOfHeightsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaTotalOfHeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaTwistIdentityStatement

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierZeroHoldsStatement

section

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fourier_zero_holds : PositivityTheory.PfSWUS.FourierZero := by
  first | exact @GlobalTheory.CompanionTheory.FourierN.fourierZero | exact GlobalTheory.CompanionTheory.FourierN.fourierZero | (intros; apply GlobalTheory.CompanionTheory.FourierN.fourierZero <;> assumption)
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCharacterEtaConditionStatement

section

section

open PositivityTheory.Rg.Rsw

theorem _root_.GlobalTheory.T.hecke_character_eta_condition : HeckeEta := by
  first | exact @GlobalTheory.CompanionTheory.HeckeEtaExist.heckeEta | exact GlobalTheory.CompanionTheory.HeckeEtaExist.heckeEta | (intros; apply GlobalTheory.CompanionTheory.HeckeEtaExist.heckeEta <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightFunctionsExistStatement

section

@[expose] public section

open PositivityTheory.Rg.Rsw

theorem _root_.GlobalTheory.T.height_functions_exist : HtExist := by
  first | exact @GlobalTheory.CompanionTheory.HtEx.htExist | exact GlobalTheory.CompanionTheory.HtEx.htExist | (intros; apply GlobalTheory.CompanionTheory.HtEx.htExist <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacobiMapsExistStatement

section

@[expose] public section

open PositivityTheory.Rg.Rsw

theorem _root_.GlobalTheory.T.jacobi_maps_exist : MapsExist := by
  first | exact @GlobalTheory.CompanionTheory.JacobiMaps.mapsExist | exact GlobalTheory.CompanionTheory.JacobiMaps.mapsExist | (intros; apply GlobalTheory.CompanionTheory.JacobiMaps.mapsExist <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantFourierCoefficientStatement

section

section

open PositivityTheory.Rg.Rsw

theorem _root_.GlobalTheory.T.partial_constant_fourier_coefficient : MapsExist → PositivityTheory.PfSWUS.FourierZero → PcFc := by
  first | exact @GlobalTheory.CompanionTheory.PcFc.target | exact GlobalTheory.CompanionTheory.PcFc.target | (intros; apply GlobalTheory.CompanionTheory.PcFc.target <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBoundStatement

section

section

open PositivityTheory.Rg.Rsw

theorem _root_.GlobalTheory.T.partial_constant_term_bound : PcBound := by
  first | exact @GlobalTheory.CompanionTheory.PcB.pcBound | exact GlobalTheory.CompanionTheory.PcB.pcBound | (intros; apply GlobalTheory.CompanionTheory.PcB.pcBound <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolarPartIdentityStatement

section

@[expose] public section

open PositivityTheory.Rg.Rsw

theorem _root_.GlobalTheory.T.polar_part_identity : MapsExist → HtExist → HeckeEta → RightId → PoleReal → FJEis → PcBound → RSec → EisHol → ThTotal → CfFJ → PcFc → SphBound → Polar := by
  first | exact @GlobalTheory.CompanionTheory.RswPolar.polar | exact GlobalTheory.CompanionTheory.RswPolar.polar | (intros; apply GlobalTheory.CompanionTheory.RswPolar.polar <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularSectionOfHeightsStatement

section

@[expose] public section

open PositivityTheory.Rg.Rsw

theorem _root_.GlobalTheory.T.regular_section_of_heights : HtExist → RSec := by
  first | exact @GlobalTheory.CompanionTheory.RSecPf.rSec_of_htExist | exact GlobalTheory.CompanionTheory.RSecPf.rSec_of_htExist | (intros; apply GlobalTheory.CompanionTheory.RSecPf.rSec_of_htExist <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaTotalOfHeckeEtaStatement

section

section

open PositivityTheory.Rg.Rsw

theorem _root_.GlobalTheory.T.theta_total_of_hecke_eta : HeckeEta → ThTotal := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.thTotal | exact GlobalTheory.CompanionTheory.ThTot.thTotal | (intros; apply GlobalTheory.CompanionTheory.ThTot.thTotal <;> assumption)
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.SphBound

section

@[expose] public section

namespace PositivityTheory.Rg.Rsw

theorem mapsExist : MapsExist := GlobalTheory.T.jacobi_maps_exist
theorem htExist : HtExist := GlobalTheory.T.height_functions_exist
theorem heckeEta : HeckeEta := GlobalTheory.T.hecke_character_eta_condition
theorem fjEis : FJEis := GlobalTheory.T.fourier_jacobi_eisenstein GlobalTheory.T.fourier_jacobi_unfolding GlobalTheory.T.theta_twist_identity
theorem pcBound : PcBound := GlobalTheory.T.partial_constant_term_bound
theorem rSec : RSec := GlobalTheory.T.regular_section_of_heights htExist
theorem eisHol : EisHol := GlobalTheory.T.eisenstein_holomorphy_of_heights htExist
theorem thTotal : ThTotal := GlobalTheory.T.theta_total_of_hecke_eta heckeEta
theorem cfFJ : CfFJ := GlobalTheory.T.fourier_jacobi_coefficient_of_bound pcBound
theorem pcFc : PcFc := GlobalTheory.T.partial_constant_fourier_coefficient mapsExist GlobalTheory.T.fourier_zero_holds
theorem sphBound : SphBound := GlobalTheory.T.spherical_bound_of_heights htExist
theorem resMu : ResMu :=
  GlobalTheory.T.residue_measure_identity mapsExist htExist heckeEta fjEis pcBound rSec eisHol thTotal pcFc sphBound GlobalTheory.T.fourier_zero_holds GlobalTheory.T.coefficient_data_exists
theorem polar : Polar :=
  GlobalTheory.T.polar_part_identity mapsExist htExist heckeEta GlobalTheory.T.right_identity_statement GlobalTheory.T.pole_reality fjEis pcBound rSec eisHol thTotal cfFJ pcFc sphBound

end PositivityTheory.Rg.Rsw
end
end
