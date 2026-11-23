module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCharacterExistsUniqueStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetProjectionSurjectiveHoldsStatement
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

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProjMemFixedPiN

section

@[expose] public section

open GlobalTheory.PRep PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.Cass

theorem proj_mem_fixed_piN (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (D : PositivityTheory.SphericalProduct.CassData G) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V) (v : fixed π D.J) : D.proj π (v : V) ∈ fixed (D.piN π) D.JT := by
  intro t
  have ht : ((t : D.T) : G) ∈ D.J := Subgroup.mem_comap.mp t.2
  have hv : π ((t : D.T) : G) (v : V) = (v : V) := by
    have h := v.2 ⟨((t : D.T) : G), ht⟩
    simpa using h
  have hq : (D.piN π) (t : D.T) (D.proj π (v : V)) = D.proj π (π ((t : D.T) : G) (v : V)) := rfl
  rw [hq, hv, MonoidHom.one_apply, Units.val_one, one_smul]

end GlobalTheory.CompanionTheory.Cass
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetLemmaHolds

section

@[expose] public section

open GlobalTheory.PRep PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.Cass

theorem sphericalProduct_A4 : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G], PositivityTheory.SphericalProduct.A4 G := by
  intro G _ _ _
  unfold PositivityTheory.SphericalProduct.A4
  intro D V _ _ π hπ hex
  obtain ⟨t, ht⟩ := hex
  refine ⟨fun v => GlobalTheory.CompanionTheory.Cass.proj_mem_fixed_piN G D V π v, ?_⟩
  have hsm : GlobalTheory.PRep.IsSmooth π := by
    unfold GlobalTheory.PRep.IsAdmissible at hπ
    exact hπ.1
  have hH := GlobalTheory.T.hecke_character_exists_unique
  unfold PositivityTheory.Lbc.HeckeExistsUnique at hH
  obtain ⟨U, hU, -⟩ := hH G D.J D.isOpen_J D.isCompact_J V π hsm (t : G)
  exact GlobalTheory.T.jacquet_projection_surjective_holds G D V π hπ t ht U hU

end GlobalTheory.CompanionTheory.Cass
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetLemmaHoldsStatement

section

@[expose] public section

open GlobalTheory.PRep PositivityTheory.SphericalProduct

theorem _root_.GlobalTheory.T.jacquet_lemma_holds : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G], PositivityTheory.SphericalProduct.A4 G := by
  first | exact @GlobalTheory.CompanionTheory.Cass.sphericalProduct_A4 | exact GlobalTheory.CompanionTheory.Cass.sphericalProduct_A4 | (intros; apply GlobalTheory.CompanionTheory.Cass.sphericalProduct_A4 <;> assumption)
end
end
