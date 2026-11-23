module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.SmallGeneratedCountUpperOfUse
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeGenericOfDegree
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeOfIsIntersectionSystem
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.EmbeddingPiecesOfIntersectionAndResolutionStatement
public import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.SelfIntersectionLeOfBoundedInjectionUse
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ExistsFormOfMemChartRingZ
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartConstantsDetermined
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PConstantsDescend
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsConstantsRegular
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsConstantsDescend
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartConstantsDetermined
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEmbeddingWeight
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwistIntersectionAnyDegree
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwistIntersectionInt
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEmbeddingPieces
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwistIntersection
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PUnitApprox

-- Source module: GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PConstantsRegular

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry NumberField

theorem ConstantsRegular.proof (hD : ConstantsDescend.Statement)
    (hC : ChartConstantsDetermined.Statement) : ConstantsRegular.Statement := by
  intro K _ ι _ Ω _ F _ _ _ y hy
  classical
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have hfin : Module.Finite ℤ (intsIn F Ω) :=
    Module.Finite.of_surjective
      ((algebraMap F Ω).comp (algebraMap (𝓞 F) F)).toIntAlgHom.rangeRestrict.toLinearMap
      (AlgHom.rangeRestrict_surjective _)
  have key : ∀ c : ∀ k, ι k, ∃ m : ℕ, 1 ≤ m ∧
      ((∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ t ∈ intsIn F Ω, (m : Ω) * t ∈ chartRingZ y c) := by
    intro c
    by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
    · have hfg : (chartRingZ y c).FG :=
        ⟨Finset.univ.image fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩, by
          simp [chartRingZ, Set.image_univ]⟩
      obtain ⟨m, hm, h⟩ := hD Ω (chartRingZ y c) (intsIn F Ω) hfg hfin (hC K ι Ω F y hy c hc)
      exact ⟨m, hm, fun _ => h⟩
    · exact ⟨1, le_rfl, fun h => absurd h hc⟩
  choose m hm hmem using key
  refine ⟨∏ c, m c, Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr
    fun c _ => Nat.one_le_iff_ne_zero.mp (hm c)), ?_⟩
  intro θ c hc
  have ht : algebraMap F Ω (θ : F) ∈ intsIn F Ω := (AlgHom.mem_range _).mpr ⟨θ, rfl⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ c), Nat.cast_mul, mul_assoc]
  exact Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _) (hmem c hc _ ht)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwistIntersectionInt

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology

noncomputable section

namespace TwistIntersectionInt

theorem proof (hPc : EmbeddingPieces.Statement) (hDG : GroundTheory.Heights₂.Heights.Inter.DegreeGeneric.Statement) :
    TwistIntersectionInt.Statement := by
  apply GroundTheory.Heights₂.Heights.HilbertSamuel.TwistIntersectionAnyDegree.proof <;> assumption

end TwistIntersectionInt

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.ArithmeticHilbertSamuelOfSystems

section

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem arithmetic_hilbert_samuel_of_systems :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → PositivityTheory.MbHsUse.HSUse →
      ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement →
      GroundTheory.Heights₂.Heights.HilbertSamuel.ArithmeticVolumeMultiplicative.Statement := by
  intro hSys hU hBig hRes
  exact GroundTheory.Heights₂.Heights.HilbertSamuel.ArithmeticVolumeMultiplicative.proof (selfIntersection_le_of_boundedInjection_use hU hBig)
    GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingWeight.proof
    (GroundTheory.Heights₂.Heights.HilbertSamuel.TwistIntersectionInt.proof (GlobalTheory.T.embedding_pieces_of_intersection_and_resolution hSys hRes)
      (degreeGeneric_of_degree (degree_of_system hSys)))
    GroundTheory.Heights₂.Heights.HilbertSamuel.UnitApprox.proof
    (GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantsRegular.proof
      GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantsDescend.proof
      GroundTheory.Heights₂.Heights.HilbertSamuel.ChartConstantsDetermined.proof)

end GlobalTheory.CompanionTheory.Ar.Giv
end
end
