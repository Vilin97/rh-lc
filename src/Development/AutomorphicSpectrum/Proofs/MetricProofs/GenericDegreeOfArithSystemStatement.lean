module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FibreDim
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.CoordinateProjectionOfArithSystemStatement
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.CoordFibreDeg
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBirationalModelExists
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PAdjoinIndepRelfinrank
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PChartScalingIndep
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCoordFibreDeg
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCoordRatioDeg
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PFibreMultiHomog
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PGenFibreChartDeg
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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

-- Source module: Development.WeilBound.CoreStatements.HodgeTatePoints.AigGen

section

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace PositivityTheory.HtPt.Aig

theorem coordFibreDeg : GroundTheory.Heights₂.Heights.Targets.CoordFibreDeg.Statement :=
  GroundTheory.Heights₂.Heights.Targets.CoordFibreDeg.proof GroundTheory.Heights₂.Heights.Targets.FibreMultiHomog.proof
    (GroundTheory.Heights₂.Heights.Targets.GenFibreChartDeg.proof GroundTheory.Heights₂.Heights.Inter.ChartScalingIndep.proof
      GroundTheory.Heights₂.Heights.Inter.AdjoinIndepRelfinrank.proof)
    GroundTheory.Heights₂.Heights.Targets.CoordRatioDeg.proof

theorem genDeg_of_coord (hPF : PFCoordStatement) (hFD : FibreDimStatement) : GenDegStatement := by
  intro I hI K _ ι _ K' _ ι' _ κ v P' d G J L L' hv hP' hP hJ hL hLL'
  obtain ⟨Ω, _, y, hy, -⟩ :=
    GroundTheory.Heights₂.Heights.HilbertSamuel.BirationalModelExists.proof K' ι' P' d hP'
  subst hy
  have : CharZero Ω := by
    refine charZero_of_inj_zero fun n hn => ?_
    have hz : ((n : ℤ) : Ω) = 0 := by exact_mod_cast hn
    have hmem : (C (n : ℤ) : MRing ι') ∈ mCoordIdeal y := by
      simp only [mCoordIdeal, RingHom.mem_ker, mConeMap, eq_intCast]
      rw [map_intCast, ← map_intCast (C : Ω →+* MvPolynomial K' Ω), hz, map_zero]
    have h2 : (n : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι') := hmem
    rw [hP'.2.2.1] at h2
    exact_mod_cast (Ideal.mem_bot).1 h2
  have hV : IsProjVarF (fibreIdeal κ G) 0 := hFD K ι K' ι' κ v (mCoordIdeal y) d 0 G hv hP' hP
  choose i hi using hV.1.2.2
  have h0 := hJ.1 (fibreIdeal κ G) Fin.elim0 i hV hi
  rw [hPF I hI K ι K' ι' κ v Ω y d L L' hv hP' hP hL hLL', h0,
    coordFibreDeg K ι K' ι' κ v Ω y d G i hv hP' hP hi, Int.cast_natCast]

theorem genDeg : PFCoordStatement → FibreDimStatement → GenDegStatement :=
  genDeg_of_coord

end PositivityTheory.HtPt.Aig
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericDegreeOfProjectionAndFibreDim

section

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem _root_.GlobalTheory.CompanionTheory.Relay.generic_degree_of_projection_and_fibre_dim : PFCoordStatement → FibreDimStatement → GenDegStatement := by
  first | exact @PositivityTheory.HtPt.Aig.genDeg | exact PositivityTheory.HtPt.Aig.genDeg
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericDegreeOfProjectionAndFibreDimStatement

section

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem _root_.GlobalTheory.T.generic_degree_of_projection_and_fibre_dim : PFCoordStatement → FibreDimStatement → GenDegStatement := by
  first | exact @GlobalTheory.CompanionTheory.Relay.generic_degree_of_projection_and_fibre_dim | exact GlobalTheory.CompanionTheory.Relay.generic_degree_of_projection_and_fibre_dim | (intros; apply GlobalTheory.CompanionTheory.Relay.generic_degree_of_projection_and_fibre_dim <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericDegreeOfArithSystem

section

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem genDeg_of_system (h : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement) :
    GenDegStatement :=
  GlobalTheory.T.generic_degree_of_projection_and_fibre_dim (GlobalTheory.T.coordinate_projection_of_arith_system h) fibreDim

end GlobalTheory.CompanionTheory.Ar.Giv
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericDegreeOfArithSystemStatement

section

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem _root_.GlobalTheory.T.generic_degree_of_arith_system : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → GenDegStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.genDeg_of_system | exact GlobalTheory.CompanionTheory.Ar.Giv.genDeg_of_system | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.genDeg_of_system <;> assumption)
end
end
