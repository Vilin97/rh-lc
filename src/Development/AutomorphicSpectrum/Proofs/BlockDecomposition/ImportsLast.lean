module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaFiniteParameterProductMeasure
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbscissaConvergenceIdentity
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOrbitalIntegralUnipotentStatement
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaFiniteParameterProductMeasure
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist
import Mathlib.Tactic.TypeStar
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteOnCompactsOrbitMeasureStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainPropertyStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GramFrameIdentitiesStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedSectionLocalIntegrabilityStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableThetaKernelFibersStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableThetaKernelProductStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IteratedIntegralsFourFactorsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JoinedBlockFormula
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JoinedProjectionFormulaStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LawOfOrbitMeasureStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitFinitenessOfLatticeBoundStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureConcentratedOnQuadricStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureGLRightScalingStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureIntegralPointsNonzero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureTranslationInvariantStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureUnitaryGroupInvariantStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentShiftInvarianceStatement

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbscissaConvergenceIdentityStatement

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.abscissa_convergence_identity : AcEq := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.GramAct.acEq | exact GlobalTheory.CompanionTheory.ColumnSplitting.GramAct.acEq | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.GramAct.acEq <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetNeZeroOfGramNondegenerate

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ColumnSplitting.Frame

theorem det_ne_zero_of_gramQ : ∀ (D : D7) (W : HSp D) (b₀ : HermE D W.rank), b₀.1.det ≠ 0 →
    ∀ x₀, gramQ W x₀ = b₀.1 → x₀.det ≠ 0 := by
  intro D W b₀ hb x₀ hx h0
  apply hb
  rw [← hx]
  unfold gramQ
  simp [Matrix.det_mul, h0]

end GlobalTheory.CompanionTheory.ColumnSplitting.Frame
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetNeZeroOfGramNondegenerateStatement

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.det_ne_zero_of_gram_nondegenerate : ∀ (D : D7) (W : HSp D) (b₀ : HermE D W.rank), b₀.1.det ≠ 0 → ∀ x₀, gramQ W x₀ = b₀.1 → x₀.det ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.Frame.det_ne_zero_of_gramQ | exact GlobalTheory.CompanionTheory.ColumnSplitting.Frame.det_ne_zero_of_gramQ | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.Frame.det_ne_zero_of_gramQ <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExtensionByZeroOrbitFormula

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.ColumnSplitting

theorem map_cols0 {R S : Type*} [Zero R] [Zero S] {a r t n : ℕ} (f : R → S) (hf : f 0 = 0)
    (e : Fin n ≃ Fin r ⊕ Fin t) (x : Matrix (Fin a) (Fin r) R) :
    ((Matrix.fromCols x (0 : Matrix (Fin a) (Fin t) R)).submatrix id e).map f =
      (Matrix.fromCols (x.map f) (0 : Matrix (Fin a) (Fin t) S)).submatrix id e := by
  ext i j
  simp only [Matrix.map_apply, Matrix.submatrix_apply, id]
  rcases e j with k | k
  · simp
  · simp [hf]

theorem mul_cols0 {R : Type*} [NonUnitalNonAssocSemiring R] {a b r t n : ℕ}
    (e : Fin n ≃ Fin r ⊕ Fin t) (A : Matrix (Fin a) (Fin b) R) (x : Matrix (Fin b) (Fin r) R) :
    A * (Matrix.fromCols x (0 : Matrix (Fin b) (Fin t) R)).submatrix id e =
      (Matrix.fromCols (A * x) (0 : Matrix (Fin a) (Fin t) R)).submatrix id e := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, id]
  rcases e j with k | k
  · simp [Matrix.mul_apply]
  · simp

theorem extension_by_zero_orbit_action : Ext0 := by
  intro D n t W hn x₀ h
  have h1 : (rat (L.ext0 hn x₀) : Matrix (Fin W.rank) (Fin n) (AE D)) =
      (Matrix.fromCols (rat x₀ : Matrix (Fin W.rank) (Fin W.rank) (AE D))
        (0 : Matrix (Fin W.rank) (Fin t) (AE D))).submatrix id (finSumFinEquiv.trans (finCongr hn)).symm :=
    map_cols0 (incA D) (map_zero _) _ x₀
  have h2 := mul_cols0 (t := t) (finSumFinEquiv.trans (finCongr hn)).symm (mt W h⁻¹)
    (rat x₀ : Matrix (Fin W.rank) (Fin W.rank) (AE D))
  exact (congrArg (fun M => mt W h⁻¹ * M) h1).trans h2

end GlobalTheory.CompanionTheory.ColumnSplitting

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExtensionByZeroOrbitFormulaStatement

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.extension_by_zero_orbit_formula : Ext0 := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.extension_by_zero_orbit_action | exact GlobalTheory.CompanionTheory.ColumnSplitting.extension_by_zero_orbit_action | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.extension_by_zero_orbit_action <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JoinedBlockFormulaStatement

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.joined_block_formula : JnBl := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.jnBl | exact GlobalTheory.CompanionTheory.ColumnSplitting.jnBl | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.jnBl <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureIntegralPointsNonzeroStatement

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.orbit_measure_integral_points_nonzero : ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ x₀, ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → nuT hn I μ x₀ {z | IntOff S z.1 ∧ IntOff S z.2} ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.nuT_intOff_ne_zero | exact GlobalTheory.CompanionTheory.ColumnSplitting.nuT_intOff_ne_zero | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.nuT_intOff_ne_zero <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImportsLast

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.CompanionTheory.ColumnSplitting

namespace GlobalTheory.CompanionTheory.ColumnSplitting

theorem main : IdemEx → LatBound → QK → IkSch → ThetaSideMeasure := by
  intro _ hLat hQK hIk D n t B W d hn I θ hθ μ hμ b₀ hb x₀ hx
  have hdx := GlobalTheory.T.det_ne_zero_of_gram_nondegenerate D W b₀ hb x₀ hx
  have hDom := GlobalTheory.T.fundamental_domain_property
  have hOF := GlobalTheory.T.orbit_finiteness_of_lattice_bound hLat
  have hZ := GlobalTheory.T.zeta_polynomial_identity
  have hA := GlobalTheory.T.abscissa_convergence_identity
  have hJ := GlobalTheory.T.joined_projection_formula
  have hB := GlobalTheory.T.joined_block_formula
  have hE := GlobalTheory.T.extension_by_zero_orbit_formula
  have hS := GlobalTheory.T.unipotent_shift_invariance
  have hL := GlobalTheory.T.induced_section_local_integrability
  have hF := GlobalTheory.T.iterated_integrals_four_factors
  refine ⟨nuT hn I μ x₀, ⟨GlobalTheory.T.finite_on_compacts_orbit_measure D n t B W d hn I μ hμ b₀ hb x₀ hx, GlobalTheory.T.orbit_measure_concentrated_on_quadric hZ hA D n t B W d hn I μ hμ b₀ hb x₀ hx,
    fun h _ => GlobalTheory.T.orbit_measure_unitary_group_invariant hQK GlobalTheory.T.law_of_orbit_measure D n t B W d hn I μ hμ x₀ h,
    fun y _ => GlobalTheory.T.orbit_measure_translation_invariant D n t B W d hn I μ hμ x₀ y,
    fun g _ => GlobalTheory.T.orbit_measure_GL_right_scaling D n t B W d hn I μ hμ x₀ g⟩,
    GlobalTheory.T.orbit_measure_integral_points_nonzero D n t B W d hn I μ hμ x₀, fun Φ hΦ η hη => ?_⟩
  have hc := GlobalTheory.T.integrable_theta_kernel_product hIk hDom hOF hS hL hF hB D n t B W d hn I θ hθ μ hμ x₀ hdx Φ hΦ η hη
  obtain ⟨h1, h2⟩ := GlobalTheory.T.integrable_theta_kernel_fibers hZ hA hJ hE hF D n t B W d hn I θ hθ μ hμ b₀ hb x₀ hx Φ hΦ η hη hc
  exact ⟨h1, GlobalTheory.T.continuous_orbital_integral_unipotent hIk hDom hOF hS hB hE D n t B W d hn I θ hθ x₀ hdx Φ hΦ, h2⟩

end GlobalTheory.CompanionTheory.ColumnSplitting

end
end
end
