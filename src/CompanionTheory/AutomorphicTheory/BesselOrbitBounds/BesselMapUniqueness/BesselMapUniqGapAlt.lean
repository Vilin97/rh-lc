module

public import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
public import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.NormPsiGen
public import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.OrbitMult
public import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.ProdNormLe
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AdaptExists
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
import Mathlib.Data.Nat.Choose.Multinomial
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
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CartanDecompositionStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ChartExistenceStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DecompositionOfIwasawaLeviCartan
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DerivedSeriesAdjointStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DerivedSeriesDerivation
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsFactorStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExponentialMembership
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IwasawaDecompositionStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LeviDecomposition
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuotientBoundOfFactorReduceChartStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ReductionOfDerivedSeriesStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.RootVectorsStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SpanGeneratorsStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TorBoundStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TorusConjugacyStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TruncatedDerivationLimitStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TruncatedDerivationStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.WordLengthBoundOfLinear

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AdaptExistsStatement

section

@[expose] public section

open CompanionTheory.Bmu

theorem _root_.GlobalTheory.T.AdaptedBasisExistsAlt : AdaptExists := by
  first | exact @GlobalTheory.CompanionTheory.BmuAdapt.adaptExists | exact GlobalTheory.CompanionTheory.BmuAdapt.adaptExists | (intros; apply GlobalTheory.CompanionTheory.BmuAdapt.adaptExists <;> assumption)
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DecompositionOfIwasawaLeviCartanStatement

section

@[expose] public section

open CompanionTheory.Bmu

theorem _root_.GlobalTheory.T.decomposition_of_iwasawa_levi_cartan : AdaptExists → IwaQ → LeviQ → CartanQ → Decomp := by
  first | exact @GlobalTheory.CompanionTheory.BmuDecomp.decomp | exact GlobalTheory.CompanionTheory.BmuDecomp.decomp | (intros; apply GlobalTheory.CompanionTheory.BmuDecomp.decomp <;> assumption)
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DerivedSeriesDerivationStatement

section

@[expose] public section

open CompanionTheory.Bmu

theorem _root_.GlobalTheory.T.DerivedSeriesDerivation : DsDer := by
  first | exact @GlobalTheory.CompanionTheory.BmuDsDer.dsDer | exact GlobalTheory.CompanionTheory.BmuDsDer.dsDer | (intros; apply GlobalTheory.CompanionTheory.BmuDsDer.dsDer <;> assumption)
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DerivedSeriesLinear

section

@[expose] public section

open CompanionTheory.Bmu CompanionTheory.D.Upq.Sm

namespace GlobalTheory.CompanionTheory.BesselMapSm

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem dsLin : DsLin := by
  intro n Hm H _ _ _ σ hσ u hu
  have h1 : (1 : Mat n) ∈ Formalism.QuantumDeterminants.UH Hm := hσ.grp.2.1
  obtain ⟨U, F, hUo, h1U, hF, hfF⟩ := hu 1 h1
  refine ⟨fderiv ℝ F 1, fun X hX => ?_⟩
  have hmem : ∀ t : ℝ, ex X t ∈ Formalism.QuantumDeterminants.UH Hm := fun t => ex_mem_of_lie hX t
  have hd : HasDerivAt (fun t : ℝ => ex X t) X 0 := by
    simpa using hasDerivAt_mul_ex (1 : Mat n) X
  have hl := hasDerivAt_local (f := fun g => σ g u) hmem (ex_zero X) hd hUo h1U hF hfF
  exact hl.deriv

end GlobalTheory.CompanionTheory.BesselMapSm
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DerivedSeriesLinearStatement

section

@[expose] public section

open CompanionTheory.Bmu

theorem _root_.GlobalTheory.T.DerivedSeriesLinear : DsLin := by
  first | exact @GlobalTheory.CompanionTheory.BesselMapSm.dsLin | exact GlobalTheory.CompanionTheory.BesselMapSm.dsLin | (intros; apply GlobalTheory.CompanionTheory.BesselMapSm.dsLin <;> assumption)
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExponentialMembershipStatement

section

@[expose] public section

open CompanionTheory.Bmu

theorem _root_.GlobalTheory.T.ExponentialMembership : ExpMem := by
  first | exact @GlobalTheory.CompanionTheory.BmuExpMem.expMem | exact GlobalTheory.CompanionTheory.BmuExpMem.expMem | (intros; apply GlobalTheory.CompanionTheory.BmuExpMem.expMem <;> assumption)
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LeviDecompositionStatement

section

@[expose] public section

open CompanionTheory.Bmu

theorem _root_.GlobalTheory.T.LeviDecomposition : LeviQ := by
  first | exact @GlobalTheory.CompanionTheory.BesselLevi.leviQ | exact GlobalTheory.CompanionTheory.BesselLevi.leviQ | (intros; apply GlobalTheory.CompanionTheory.BesselLevi.leviQ <;> assumption)
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.WordLengthBoundOfLinearStatement

section

@[expose] public section

open CompanionTheory.Bmu

theorem _root_.GlobalTheory.T.word_length_bound_of_linear : DsLin → WordBd := by
  first | exact @GlobalTheory.CompanionTheory.BmuWordBd.wordBd_of_dsLin | exact GlobalTheory.CompanionTheory.BmuWordBd.wordBd_of_dsLin | (intros; apply GlobalTheory.CompanionTheory.BmuWordBd.wordBd_of_dsLin <;> assumption)
end
end

-- Source module: CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGapAlt

section

@[expose] public section

namespace CompanionTheory.Bmu

theorem bounded : Bounded :=
  bounded_of (GlobalTheory.T.quotient_bound_of_factor_reduce_chart GlobalTheory.T.factorization' (GlobalTheory.T.reduction_of_derived_series GlobalTheory.T.DerivedSeriesLinear GlobalTheory.T.DerivedSeriesAdjoint GlobalTheory.T.DerivedSeriesDerivation) GlobalTheory.T.ChartExistence)
    (absBound_of GlobalTheory.T.factorization' GlobalTheory.T.DerivedSeriesAdjoint GlobalTheory.T.DerivedSeriesDerivation (GlobalTheory.T.word_length_bound_of_linear GlobalTheory.T.DerivedSeriesLinear)) GlobalTheory.T.AdaptedBasisExistsAlt
    (GlobalTheory.T.decomposition_of_iwasawa_levi_cartan GlobalTheory.T.AdaptedBasisExistsAlt GlobalTheory.T.IwasawaDecomposition GlobalTheory.T.LeviDecomposition GlobalTheory.T.CartanDecomposition) GlobalTheory.T.torBound' GlobalTheory.T.SpanGenerators
    GlobalTheory.T.ExponentialMembership GlobalTheory.T.RootVectors

theorem besselMapUniqGap : BesselMapUniqGap :=
  uniq_of bounded (GlobalTheory.T.truncated_derivation_limit GlobalTheory.T.factorization' GlobalTheory.T.TruncatedDerivation) GlobalTheory.T.TorusConjugacy GlobalTheory.T.DerivedSeriesAdjoint GlobalTheory.T.factorization'

end CompanionTheory.Bmu
end
end
