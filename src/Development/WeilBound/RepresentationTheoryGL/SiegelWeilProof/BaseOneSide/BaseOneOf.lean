module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelDensities.Pieces
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterSideEquidistributionStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CountingFormulaOfComponentsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EquidistributionStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistenceTestFunctionsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HassePrincipleHermitianStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianExistencePrincipleStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LFunctionSideEquidistributionStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthFormulaOfTotalMassOneStatement
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyReal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanBinaryGramDensity
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalBinaryGramIntegral
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalDensityOfMassOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalDensityRatioFormula
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarFibrationFormulaStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilRankOneBaseCase
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimilitudeOfScalarFormulaStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TateIntegralFormulaStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIdentityOfLocalDensities
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.MassOneBase.MassOne
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelDensities.DensEqOfPieces
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.LowRankSiegelDensities.MassTop
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.OneVecBinary
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.UnramifiedSchwartzDensity.SchTop

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalDensityFormula

section

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open PositivityTheory.Rg.Base1 PositivityTheory.SiegelWeilFormula.Densx
open scoped TensorProduct ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.RankOne

theorem dens : Dens := by
  intro F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hσ hJ hli hlam hμ hF hmi hm S φ A hT
  obtain ⟨hφ, hφc, hφ0, hφU, hA, -⟩ := hT
  have : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨c1, c2, -, c4⟩ := GlobalTheory.CompanionTheory.SW.ArchFibre.fibre_integral (Ainf F)
    (GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hσ.1) hσ hJ b li hli.1 mi hmi φ hφ hφc hφ0 hφU
  have hv : ∀ v ∈ S, Continuous (fun s : Fv F v => (m v (hermScal (Fv F v) σ s) (A v)).toReal) ∧
      HasCompactSupport (fun s : Fv F v => (m v (hermScal (Fv F v) σ s) (A v)).toReal) ∧
      ENNReal.ofReal (∫ s, (m v (hermScal (Fv F v) σ s) (A v)).toReal ∂(lam v)) =
        coordW (Fv F v) b (lam v) 1 1 (A v) := fun v hvS => by
    have : BorelSpace (Fv F v) := ⟨rfl⟩
    exact GlobalTheory.CompanionTheory.SW.FibreCpt.masses_field (Fv F v) (GlobalTheory.T.completion_is_local_ring F v) hσ hJ b (lam v) (hlam v).1
      (m v) (hm v) (A v) (hA v hvS).1 (hA v hvS).2.1 (hA v hvS).2.2
  refine ⟨c1, c2, fun v hvS => ⟨continuous_const.mul (hv v hvS).1, (hv v hvS).2.1.mul_left⟩, ?_⟩
  have hI0 : 0 ≤ ∫ y, Gi mi φ y ∂li :=
    integral_nonneg fun s => integral_nonneg fun X => hφ0 X
  have hJ0 : ∀ v ∈ S, 0 ≤ ∫ s, gv m A v s ∂(lam v) := fun v _ =>
    integral_nonneg fun s => mul_nonneg (NNReal.coe_nonneg _) ENNReal.toReal_nonneg
  have hloc : ∀ v ∈ S, ENNReal.ofReal (∫ s, gv m A v s ∂(lam v)) =
      (cfac E v : ℝ≥0∞) * coordW (Fv F v) b (lam v) 1 1 (A v) := fun v hvS => by
    have e : ∫ s, gv m A v s ∂(lam v) =
        (cfac E v : ℝ) * ∫ s, (m v (hermScal (Fv F v) σ s) (A v)).toReal ∂(lam v) :=
      integral_const_mul _ _
    rw [e, ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal, (hv v hvS).2.2]
  rw [ENNReal.ofReal_mul hI0, ENNReal.ofReal_prod_of_nonneg hJ0, Finset.prod_congr rfl hloc,
    Finset.prod_mul_distrib]
  have e0 : ENNReal.ofReal (∫ y, Gi mi φ y ∂li) = ∫⁻ X, ENNReal.ofReal (φ X) ∂(coordW (Ainf F) b li 1 1) := c4
  rw [e0, vol]
  ring

end GlobalTheory.CompanionTheory.SW.RankOne

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalDensityFormulaStatement

section

@[expose] public section

open PositivityTheory.Rg.Base1

theorem _root_.GlobalTheory.T.local_density_formula : Dens := by
  first | exact @GlobalTheory.CompanionTheory.SW.RankOne.dens | exact GlobalTheory.CompanionTheory.SW.RankOne.dens | (intros; apply GlobalTheory.CompanionTheory.SW.RankOne.dens <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalDensityOfMassOneStatement

section

@[expose] public section

open PositivityTheory.Rg.Base1

theorem _root_.GlobalTheory.T.local_density_of_mass_one : Scal → PositivityTheory.SiegelWeilFormula.Densx.MassOne → LocR := by
  first | exact @GlobalTheory.CompanionTheory.RankOneLoc.locR | exact GlobalTheory.CompanionTheory.RankOneLoc.locR | (intros; apply GlobalTheory.CompanionTheory.RankOneLoc.locR <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalDensityRatioFormulaStatement

section

@[expose] public section

open PositivityTheory.Rg.Base1

theorem _root_.GlobalTheory.T.local_density_ratio_formula : Ratio := by
  first | exact @GlobalTheory.CompanionTheory.RatioBase.ratio | exact GlobalTheory.CompanionTheory.RatioBase.ratio | (intros; apply GlobalTheory.CompanionTheory.RatioBase.ratio <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilRankOneBaseCaseStatement

section

@[expose] public section

open PositivityTheory.Rg.Base1

theorem _root_.GlobalTheory.T.siegel_weil_rank_one_base_case : Prop1 → Simil → Hasse → Cnt → PositivityTheory.SiegelWeilFormula.Densx.BaseOne := by
  first | exact @GlobalTheory.CompanionTheory.Base1.baseOne_of_parts | exact GlobalTheory.CompanionTheory.Base1.baseOne_of_parts | (intros; apply GlobalTheory.CompanionTheory.Base1.baseOne_of_parts <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIdentityOfLocalDensitiesStatement

section

@[expose] public section

open PositivityTheory.Rg.Base1

theorem _root_.GlobalTheory.T.theta_identity_of_local_densities : Scal → LocR → ThetaId := by
  first | exact @GlobalTheory.CompanionTheory.RgBase.Theta.thetaId | exact GlobalTheory.CompanionTheory.RgBase.Theta.thetaId | (intros; apply GlobalTheory.CompanionTheory.RgBase.Theta.thetaId <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelDensities.DensEqOfBase

section

@[expose] public section

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Densx

theorem densEq_of_base (hB : PositivityTheory.PfSWUS.HMass.SchwartzDensInf) (hBase : BaseOne) (hO : MassOne) :
    PositivityTheory.SiegelWeilFormula.Gen.DensEq :=
  densEq_of_pieces PositivityTheory.Rg.Mass.oneVecBinary PositivityTheory.PfSWUS.HMass.oneVecBinaryMass hB hBase hO

end PositivityTheory.SiegelWeilFormula.Densx

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelDensities.PlugInf

section

@[expose] public section

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Densx

theorem densEq_of_one (hBase : BaseOne) (hO : MassOne) : PositivityTheory.SiegelWeilFormula.Gen.DensEq :=
  densEq_of_base PositivityTheory.PfSWUS.SchInf.schwartzDensInf hBase hO

end PositivityTheory.SiegelWeilFormula.Densx

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.BaseOneOf

section

@[expose] public section

namespace PositivityTheory.Rg.Base1

theorem baseOne_of (hM : PositivityTheory.SiegelWeilFormula.Densx.MassOne) : PositivityTheory.SiegelWeilFormula.Densx.BaseOne :=
  GlobalTheory.T.siegel_weil_rank_one_base_case (GlobalTheory.T.length_formula_of_total_mass_one hM) (GlobalTheory.T.similitude_of_scalar_formula GlobalTheory.T.scalar_fibration_formula) GlobalTheory.T.hasse_principle_hermitian
    (GlobalTheory.T.counting_formula_of_components GlobalTheory.T.tate_integral_formula (GlobalTheory.T.character_side_equidistribution GlobalTheory.T.equidistribution) GlobalTheory.T.local_density_ratio_formula GlobalTheory.T.hermitian_existence_principle GlobalTheory.T.existence_test_functions GlobalTheory.T.local_density_formula
      (GlobalTheory.T.l_function_side_equidistribution GlobalTheory.T.equidistribution) (GlobalTheory.T.theta_identity_of_local_densities GlobalTheory.T.scalar_fibration_formula (GlobalTheory.T.local_density_of_mass_one GlobalTheory.T.scalar_fibration_formula hM)))

theorem baseOne : PositivityTheory.SiegelWeilFormula.Densx.BaseOne := baseOne_of PositivityTheory.SiegelWeilFormula.BaseOne.massOne

theorem densEq : PositivityTheory.SiegelWeilFormula.Gen.DensEq := PositivityTheory.SiegelWeilFormula.Densx.densEq_of_one baseOne PositivityTheory.SiegelWeilFormula.BaseOne.massOne

end PositivityTheory.Rg.Base1
end
end
