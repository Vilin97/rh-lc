module

public import Development.EtaleCohomology.EtaleSheaves.StandardChartsLineOne
public import Development.EtaleCohomology.EtaleSheaves.LineHigh
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.EtaleCohomology.EtaleSheaves.ChartsPf

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.ChartsPf

attribute [local instance] MvPolynomial.gradedAlgebra

abbrev D (i : Fin 2) : P1.Opens :=
  Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ) (MvPolynomial.X i)

lemma X_mem (i : Fin 2) : (MvPolynomial.X i : MvPolynomial (Fin 2) ℤ) ∈ MvPolynomial.homogeneousSubmodule (Fin 2) ℤ 1 :=
  (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X ℤ i)

lemma D_affine (i : Fin 2) : IsAffineOpen (D i) :=
  Proj.isAffineOpen_basicOpen _ _ (X_mem i) one_pos

lemma D_cover : ⨆ i, D i = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top'
  · exact fun i => ⟨1, X_mem i⟩
  · rw [eq_top_iff]
    intro x _
    have hx : x ∈ Algebra.adjoin ℤ (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) ℤ)) := by
      rw [MvPolynomial.adjoin_range_X]; trivial
    have h : Algebra.adjoin ℤ (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) ℤ)) ≤
        (Algebra.adjoin (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ 0)
          (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) ℤ))).restrictScalars ℤ :=
      Algebra.adjoin_le Algebra.subset_adjoin
    exact h hx

end LateralTheory.E.ChartsPf
end
end
end

-- Source module: Development.EtaleCohomology.EtaleSheaves.StdChartsOf

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.StdChartsProof₂

theorem StdCharts_of : LateralTheory.E.StandardEtaleChartsMultivariableHensel.StdCharts := by
  intro A _ _ Z p hp
  obtain ⟨L, u, l, hu, ⟨hl, f, hf⟩, hul⟩ := hp
  have hf' : IsAffineHom f := MorphismProperty.of_isPullback hf.flip inferInstance
  let g : Z ⟶ P1 := u ≫ f
  have hU : ∀ i, IsAffineOpen (g ⁻¹ᵁ LateralTheory.E.ChartsPf.D i) := fun i => (LateralTheory.E.ChartsPf.D_affine i).preimage g
  refine ⟨g ⁻¹ᵁ LateralTheory.E.ChartsPf.D 0, g ⁻¹ᵁ LateralTheory.E.ChartsPf.D 1, (g ⁻¹ᵁ LateralTheory.E.ChartsPf.D 0).ι,
    (g ⁻¹ᵁ LateralTheory.E.ChartsPf.D 1).ι, inferInstance, inferInstance, hU 0, hU 1, ?_, ?_⟩
  · rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    ext x
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    have hx : g x ∈ (⨆ i, LateralTheory.E.ChartsPf.D i : P1.Opens) := by rw [LateralTheory.E.ChartsPf.D_cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr hi
  · refine ⟨L, u, l, f, hu, hl, hf, hul, ?_, ?_⟩
    · rw [Scheme.Opens.range_ι]; rfl
    · rw [Scheme.Opens.range_ι]; rfl

end LateralTheory.E.StdChartsProof₂
end
end
end
