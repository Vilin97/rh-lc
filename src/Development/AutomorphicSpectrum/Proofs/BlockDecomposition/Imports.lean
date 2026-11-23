module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleUnitarySemisimple
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactOpenSubgroupsBasis
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedTwoCharactersNotScalarStatement
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantInducedIsAdmissible
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantModulus
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetInducedTwoCharactersStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProduct
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleUnitarySemisimpleStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

theorem _root_.GlobalTheory.T.admissible_unitary_semisimple : ∀ {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), (∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U) → IsAdmissible ρ → IsUnitarisable ρ → ∀ W : Subrepresentation ρ, ∃ W' : Subrepresentation ρ, IsCompl W W' := by
  first | exact @GlobalTheory.CompanionTheory.UnitSemisimple.exists_isCompl | exact GlobalTheory.CompanionTheory.UnitSemisimple.exists_isCompl | (intros; apply GlobalTheory.CompanionTheory.UnitSemisimple.exists_isCompl <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsAdmissibleDegenerate

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.DegenSeries

theorem isAdmissible_degenerate : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ →
    IsAdmissible (parInd (two (stdSum (rfl : a + b = a + b)))
      ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)) := by
  intro k _ _ _ _ a b χ₁ χ₂ _ _
  exact GlobalTheory.SmGL.ParIndAdm.isAdmissible_parInd _ _

end GlobalTheory.CompanionTheory.DegenSeries
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitarisableDegenerateSeries

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.DegenerateSeries

theorem isUnitarisable_degenerateSeries (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ) (_ : IsSmoothChar χ₁)
    (_ : IsSmoothChar χ₂) (h₁ : IsUnitaryChar χ₁) (h₂ : IsUnitaryChar χ₂) :
    IsUnitarisable (parInd (two (stdSum (rfl : a + b = a + b)))
      ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp
        (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)) := by
  apply GlobalTheory.SmGL.UnitInd.isUnitarisable_prod₂
  · rw [GlobalTheory.SmGL.detRep, GlobalTheory.SmGL.isUnitarisable_ofChar_iff]
    intro g
    exact h₁ _
  · rw [GlobalTheory.SmGL.detRep, GlobalTheory.SmGL.isUnitarisable_ofChar_iff]
    intro g
    exact h₂ _

end GlobalTheory.CompanionTheory.DegenerateSeries
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NontrivialSubrepresentation

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.CompanionTheory.DegPrinSeries

theorem nontrivial_subrepresentation : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → Nontrivial (Subrepresentation (parInd (two (stdSum (rfl : a + b = a + b))) ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom))) := by
  intro k _ _ _ _ a b χ₁ χ₂ hχ₁ hχ₂
  have hdetChar : ∀ (m : ℕ) (χ : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar χ →
      GlobalTheory.PRep.IsSmooth (GlobalTheory.SmGL.detRep (Fin m) χ) := by
    intro m χ hχ
    have hc : Continuous (Matrix.GeneralLinearGroup.det : GL (Fin m) k → kˣ) := by
      rw [Units.continuous_iff]
      constructor
      · have hval : (Units.val ∘ (Matrix.GeneralLinearGroup.det : GL (Fin m) k → kˣ)) =
            fun g : GL (Fin m) k => Matrix.det (g : Matrix (Fin m) (Fin m) k) := by
          funext g
          exact Matrix.GeneralLinearGroup.val_det_apply g
        rw [hval]
        exact Units.continuous_val.matrix_det
      · have hinv : (fun g : GL (Fin m) k => ((Matrix.GeneralLinearGroup.det g)⁻¹ : kˣ).val) =
            fun g => Matrix.det ((g⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) := by
          funext g
          rw [← map_inv, Matrix.GeneralLinearGroup.val_det_apply]
        rw [hinv]
        exact Units.continuous_coe_inv.matrix_det
    unfold GlobalTheory.SmGL.detRep
    rw [GlobalTheory.SmGL.isSmooth_ofChar_iff]
    unfold GlobalTheory.SmGL.IsSmoothChar at hχ ⊢
    exact hc.isOpen_preimage _ hχ
  have hsmooth := GlobalTheory.SmGL.isSmooth_comp
    (GlobalTheory.SmGL.isSmooth_extTensor (hdetChar a χ₁ hχ₁) (hdetChar b χ₂ hχ₂))
    (GlobalTheory.SmGL.leviTwo k (Fin a) (Fin b)).symm.toMonoidHom
    (by exact (continuous_apply Bool.false).prodMk (continuous_apply Bool.true))
  have hu : ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ)) ≠ 0 := by
    intro h0
    have := congrArg (TensorProduct.lid ℂ ℂ) h0
    simp at this
  obtain ⟨f, hf1, -⟩ := GlobalTheory.SmGL.ProdIrr.exists_indSp_apply_one
    (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum (rfl : a + b = a + b))) _
    hsmooth ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ))
  refine ⟨⟨⟨⊥, fun g ⦃v⦄ hv => ?_⟩, ⟨⊤, fun _ ⦃_⦄ _ => Submodule.mem_top⟩, fun hEq => ?_⟩⟩
  · rw [Submodule.mem_bot] at hv ⊢
    rw [hv, map_zero]
  · have hsub := congrArg Subrepresentation.toSubmodule hEq
    have hf : f = 0 := (Submodule.mem_bot ℂ).1 (Submodule.eq_top_iff'.1 hsub f)
    rw [hf] at hf1
    apply hu
    rw [← hf1]
    first
    | rfl
    | simp

end GlobalTheory.CompanionTheory.DegPrinSeries
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Imports

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.SmGL.Bernstein

theorem prod₂_detRep_isIrreducible :
    (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
      JacquetOfInducedFiltration k) →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → IsUnitaryChar χ₁ →
      IsUnitaryChar χ₂ → (a ≠ b ∨ χ₁ ≠ χ₂) →
      (prod₂ (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).IsIrreducible := by
  intro hJ k _ _ _ _ a b χ₁ χ₂ s₁ s₂ u₁ u₂ hne
  haveI := GlobalTheory.CompanionTheory.DegPrinSeries.nontrivial_subrepresentation k a b χ₁ χ₂ s₁ s₂
  show IsSimpleOrder (Subrepresentation (parInd (two (stdSum (rfl : a + b = a + b)))
    ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)))
  refine ⟨fun W => ?_⟩
  obtain ⟨W', hc⟩ := GlobalTheory.T.admissible_unitary_semisimple _ (GlobalTheory.CompanionTheory.SmGL.exists_compact_open_subgroup_subset k (a + b))
    (GlobalTheory.CompanionTheory.DegenSeries.isAdmissible_degenerate k a b χ₁ χ₂ s₁ s₂)
    (GlobalTheory.CompanionTheory.DegenerateSeries.isUnitarisable_degenerateSeries k a b χ₁ χ₂ s₁ s₂ u₁ u₂) W
  by_contra h
  push_neg at h
  have hW' : W' ≠ ⊥ := by
    rintro rfl
    exact h.2 (eq_top_of_isCompl_bot hc)
  exact GlobalTheory.T.induced_two_characters_not_scalar k a b χ₁ χ₂ W W' hc h.1 hW'
    (GlobalTheory.T.jacquet_induced_two_characters k a b χ₁ χ₂ (hJ k) s₁ s₂ u₁ u₂ hne)

end GlobalTheory.CompanionTheory.SmGL.Bernstein
end
end
