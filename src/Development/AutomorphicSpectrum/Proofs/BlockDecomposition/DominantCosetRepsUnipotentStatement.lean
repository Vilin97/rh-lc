module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactGroupFiniteCosetReps
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InterConjIsOpen

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMemInfConjOfIsDom

section

@[expose] public section

open GlobalTheory.PRep PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.Casselman

theorem exists_mem_inf_conj_of_isDom : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (D : PositivityTheory.SphericalProduct.CassData G), ∀ t : D.T, D.IsDom t → ∀ y ∈ D.J,
      ∃ a ∈ D.J ⊓ D.N, a⁻¹ * y ∈ D.J ⊓ D.J.map (MulAut.conj (t : G)).toMonoidHom := by
  intro G _ _ _ D t ht y hy
  obtain ⟨c, hc, b, hb, a, ha, rfl⟩ := D.fact_up y hy
  have hb' : b ∈ D.J := (Subgroup.mem_inf.1 hb).1
  have ha' : a ∈ D.J := (Subgroup.mem_inf.1 ha).1
  have hbt : (t : G)⁻¹ * b * t ∈ D.J := (Subgroup.mem_inf.1 (ht.2.2 b hb).2).1
  have hat : (t : G)⁻¹ * a * t ∈ D.J := (Subgroup.mem_inf.1 (ht.2.1 a ha)).1
  have he : c⁻¹ * (c * b * a) = b * a := by group
  refine ⟨c, hc, Subgroup.mem_inf.2 ⟨?_, ?_⟩⟩
  · rw [he]
    exact D.J.mul_mem hb' ha'
  · rw [he, Subgroup.mem_map]
    refine ⟨((t : G)⁻¹ * b * t) * ((t : G)⁻¹ * a * t), D.J.mul_mem hbt hat, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

end GlobalTheory.CompanionTheory.Casselman
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantCosetRepsUnipotent

section

@[expose] public section

open GlobalTheory.PRep PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.Casselman

theorem exists_fin_coset_reps_of_isDom : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (D : PositivityTheory.SphericalProduct.CassData G), ∀ t : D.T, D.IsDom t → ∃ r : ℕ, 0 < r ∧ ∃ x : Fin r → G,
      (∀ i, x i ∈ D.J ⊓ D.N) ∧
        ∀ y ∈ D.J, ∃! i, (x i)⁻¹ * y ∈ D.J ⊓ D.J.map (MulAut.conj (t : G)).toMonoidHom := by
  intro G _ _ _ D t ht
  exact GlobalTheory.CompanionTheory.CosetReps.exists_fin_coset_reps G D.J
    (D.J ⊓ D.J.map (MulAut.conj (t : G)).toMonoidHom) (D.J ⊓ D.N)
    D.isCompact_J (GlobalTheory.CompanionTheory.TopGroup.inter_conj_isOpen G D.J D.isOpen_J (t : G)) inf_le_left inf_le_left
    (exists_mem_inf_conj_of_isDom G D t ht)

end GlobalTheory.CompanionTheory.Casselman
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantCosetRepsUnipotentStatement

section

@[expose] public section

open GlobalTheory.PRep PositivityTheory.SphericalProduct

theorem _root_.GlobalTheory.T.dominant_coset_reps_unipotent : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (D : PositivityTheory.SphericalProduct.CassData G), ∀ t : D.T, D.IsDom t → ∃ r : ℕ, 0 < r ∧ ∃ x : Fin r → G, (∀ i, x i ∈ D.J ⊓ D.N) ∧ ∀ y ∈ D.J, ∃! i, (x i)⁻¹ * y ∈ D.J ⊓ D.J.map (MulAut.conj (t : G)).toMonoidHom := by
  first | exact @GlobalTheory.CompanionTheory.Casselman.exists_fin_coset_reps_of_isDom | exact GlobalTheory.CompanionTheory.Casselman.exists_fin_coset_reps_of_isDom | (intros; apply GlobalTheory.CompanionTheory.Casselman.exists_fin_coset_reps_of_isDom <;> assumption)
end
end
