module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CellFunctorNonscalarOffdiag
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiltrationUniqueSubquotientStatement
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CellFunctorNonscalarOffdiagStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

theorem _root_.GlobalTheory.T.cell_functor_nonscalar_offdiag : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → IsUnitaryChar χ₁ → IsUnitaryChar χ₂ → (a ≠ b ∨ χ₁ ≠ χ₂) → ∀ (B : SizeMatrix (Two (Fin a) (Fin b)) (Two (Fin a) (Fin b))) (f : ∀ i, (Σ j, Fin (B.1 i j)) ≃ Two (Fin a) (Fin b) i) (g : ∀ j, (Σ i, Fin (B.1 i j)) ≃ Two (Fin a) (Fin b) j), B.1 false true ≠ 0 → ∀ φ : (cellFunctor f g ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)).IntertwiningMap ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom), φ.toLinearMap = 0 := by
  first | exact @GlobalTheory.CompanionTheory.CellOff.offCell_eq_zero | exact GlobalTheory.CompanionTheory.CellOff.offCell_eq_zero | (intros; apply GlobalTheory.CompanionTheory.CellOff.offCell_eq_zero <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CellFunctorScalarDiagonal

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.CellDiag

def evalOne {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup W] [Module ℂ W] (H : Subgroup G) (σ : Representation ℂ H W) :
    smoothPart (ind H σ) →ₗ[ℂ] W :=
  (LinearMap.proj (1 : G)).comp ((indSpace H σ).subtype.comp (smoothPart (ind H σ)).subtype)

theorem evalOne_injective {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup W] [Module ℂ W] (H : Subgroup G) (hH : H = ⊤) (σ : Representation ℂ H W) :
    Function.Injective (evalOne H σ) := by
  subst hH
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro v hv
  have h0 : (v : GlobalTheory.PRep.indSpace (⊤ : Subgroup G) σ).1 1 = 0 := hv
  have hmem : ∀ (h : (⊤ : Subgroup G)) (x : G),
      (v : GlobalTheory.PRep.indSpace (⊤ : Subgroup G) σ).1 (↑h * x) =
        σ h ((v : GlobalTheory.PRep.indSpace (⊤ : Subgroup G) σ).1 x) :=
    (v : GlobalTheory.PRep.indSpace (⊤ : Subgroup G) σ).2
  apply Subtype.ext
  apply Subtype.ext
  funext x
  have key : (v : GlobalTheory.PRep.indSpace (⊤ : Subgroup G) σ).1 x =
      σ ⟨x, Subgroup.mem_top x⟩ ((v : GlobalTheory.PRep.indSpace (⊤ : Subgroup G) σ).1 1) := by
    have := hmem ⟨x, Subgroup.mem_top x⟩ 1
    rwa [mul_one] at this
  rw [key, h0, map_zero]
  first
  | rfl
  | simp

theorem dichotomy {V X T : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup T] [Module ℂ T] [Module.Finite ℂ X] (hX : Module.finrank ℂ X ≤ 1)
    (hT : Module.finrank ℂ T = 1) (ι : V →ₗ[ℂ] X) (hι : Function.Injective ι)
    (φ ψ : V →ₗ[ℂ] T) : φ = 0 ∨ ∃ c : ℂ, ψ = c • φ := by
  classical
  by_cases hφ : φ = 0
  · exact Or.inl hφ
  right
  haveI : Module.Finite ℂ V := Module.Finite.of_injective ι hι
  have hV : Module.finrank ℂ V ≤ 1 := (LinearMap.finrank_le_finrank_of_injective hι).trans hX
  obtain ⟨v, hv⟩ : ∃ v, φ v ≠ 0 := by
    by_contra hne
    push_neg at hne
    exact hφ (LinearMap.ext hne)
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hv (map_zero φ)
  haveI : Nontrivial V := ⟨⟨v, 0, hv0⟩⟩
  have hV1 : Module.finrank ℂ V = 1 := le_antisymm hV Module.finrank_pos
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (φ v) hv).mp hT (ψ v)
  refine ⟨c, LinearMap.ext fun w => ?_⟩
  obtain ⟨t, ht⟩ := (finrank_eq_one_iff_of_nonzero' v hv0).mp hV1 w
  first
  | (rw [← ht, map_smul, map_smul, LinearMap.smul_apply, ← hc]; done)
  | (rw [← ht, ← hc]; simp [smul_comm])
  | (subst ht; simp [← hc, smul_smul, mul_comm])

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sizeMatrix_true_false {a b : ℕ}
    (B : SizeMatrix (Two (Fin a) (Fin b)) (Two (Fin a) (Fin b))) (h : B.1 false true = 0) :
    B.1 true false = 0 := by
  have hr := B.2.1 false
  have hc := B.2.2 false
  first
  | (rw [Fintype.sum_bool] at hr hc; omega)
  | (simp only [Fintype.sum_bool] at hr hc; omega)

theorem relParab_eq_top {a b : ℕ}
    (B : SizeMatrix (Two (Fin a) (Fin b)) (Two (Fin a) (Fin b))) (h : B.1 false true = 0)
    (g : ∀ j, (Σ i, Fin (B.1 i j)) ≃ Two (Fin a) (Fin b) j) :
    relParab k (c := fun j i => Fin (B.1 i j)) g = ⊤ := by
  have h' := GlobalTheory.CompanionTheory.CellDiag.sizeMatrix_true_false B h
  rw [eq_top_iff]
  intro x _
  rw [GlobalTheory.SmGL.relParab, Subgroup.mem_pi]
  intro j _
  rw [GlobalTheory.SmGL.mem_parab_iff]
  intro p q i i' hqp
  rw [Bool.lt_iff] at hqp
  obtain ⟨rfl, rfl⟩ := hqp
  exfalso
  cases j
  · have := i.isLt
    omega
  · have := i'.isLt
    omega

theorem diag_cell_at_most_one_map : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ) (B : SizeMatrix (Two (Fin a) (Fin b)) (Two (Fin a) (Fin b))) (f : ∀ i, (Σ j, Fin (B.1 i j)) ≃ Two (Fin a) (Fin b) i) (g : ∀ j, (Σ i, Fin (B.1 i j)) ≃ Two (Fin a) (Fin b) j), B.1 false true = 0 → (∀ φ ψ : (cellFunctor f g ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)).IntertwiningMap (((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)), φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap) := by
  intro k _ _ _ _ a b χ₁ χ₂ B f g h φ ψ
  have hT : Module.finrank ℂ (ℂ ⊗[ℂ] ℂ) = 1 := by
    first
    | rw [Module.finrank_tensorProduct, Module.finrank_self]
    | simp [Module.finrank_tensorProduct]
    | simp
  refine GlobalTheory.CompanionTheory.CellDiag.dichotomy ?_ hT
    (GlobalTheory.CompanionTheory.CellDiag.evalOne _ _)
    (GlobalTheory.CompanionTheory.CellDiag.evalOne_injective _ (GlobalTheory.CompanionTheory.CellDiag.relParab_eq_top (k := k) B h g) _)
    φ.toLinearMap ψ.toLinearMap
  first
  | exact (Submodule.finrank_quotient_le _).trans hT.le
  | exact (Submodule.finrank_quotient_le _).trans (le_of_eq hT)
  | (refine (Submodule.finrank_quotient_le _).trans ?_; simp)

end GlobalTheory.CompanionTheory.CellDiag
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CellFunctorScalarDiagonalStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

theorem _root_.GlobalTheory.T.cell_functor_scalar_diagonal : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ) (B : SizeMatrix (Two (Fin a) (Fin b)) (Two (Fin a) (Fin b))) (f : ∀ i, (Σ j, Fin (B.1 i j)) ≃ Two (Fin a) (Fin b) i) (g : ∀ j, (Σ i, Fin (B.1 i j)) ≃ Two (Fin a) (Fin b) j), B.1 false true = 0 → (∀ φ ψ : (cellFunctor f g ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)).IntertwiningMap (((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)), φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap) := by
  first | exact @GlobalTheory.CompanionTheory.CellDiag.diag_cell_at_most_one_map | exact GlobalTheory.CompanionTheory.CellDiag.diag_cell_at_most_one_map | (intros; apply GlobalTheory.CompanionTheory.CellDiag.diag_cell_at_most_one_map <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetInducedTwoCharacters

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.SmGL.Bernstein

theorem proportional_of_equiv {G V V' W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W] [Module ℂ W]
    {τ : Representation ℂ G V} {τ' : Representation ℂ G V'} {σ : Representation ℂ G W}
    (E : τ.Equiv τ')
    (h : ∀ φ ψ : τ'.IntertwiningMap σ, φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap)
    (φ ψ : τ.IntertwiningMap σ) :
    φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap := by
  rcases h (φ.comp E.symm.toIntertwiningMap) (ψ.comp E.symm.toIntertwiningMap) with h0 | ⟨c, hc⟩
  · left
    ext v
    have := LinearMap.congr_fun h0 (E v)
    simpa using this
  · right
    refine ⟨c, ?_⟩
    ext v
    have := LinearMap.congr_fun hc (E v)
    simpa using this

theorem eq_zero_of_equiv {G V V' W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W] [Module ℂ W]
    {τ : Representation ℂ G V} {τ' : Representation ℂ G V'} {σ : Representation ℂ G W}
    (E : τ.Equiv τ') (h : ∀ φ : τ'.IntertwiningMap σ, φ.toLinearMap = 0)
    (φ : τ.IntertwiningMap σ) : φ.toLinearMap = 0 := by
  ext v
  have := LinearMap.congr_fun (h (φ.comp E.symm.toIntertwiningMap)) (E v)
  simpa using this

theorem exists_diagonal_sizeMatrix (a b : ℕ) :
    ∃ D : SizeMatrix (Two (Fin a) (Fin b)) (Two (Fin a) (Fin b)),
      ∀ B : SizeMatrix (Two (Fin a) (Fin b)) (Two (Fin a) (Fin b)), B = D ↔ B.1 false true = 0 := by
  have card_f : Fintype.card (Two (Fin a) (Fin b) false) = a := Fintype.card_fin a
  have card_t : Fintype.card (Two (Fin a) (Fin b) true) = b := Fintype.card_fin b
  refine ⟨⟨fun i j => if i = j then (if i then b else a) else 0, ?_, ?_⟩, fun B => ⟨?_, ?_⟩⟩
  · intro i; cases i <;> simp [card_f, card_t]
  · intro j; cases j <;> simp [card_f, card_t]
  · rintro rfl; simp
  · intro hB
    have r0 := B.2.1 false
    have r1 := B.2.1 true
    have c0 := B.2.2 false
    have c1 := B.2.2 true
    simp only [Fintype.sum_bool, card_f, card_t] at r0 r1 c0 c1
    apply Subtype.ext
    funext i j
    cases i <;> cases j <;> simp <;> omega



theorem mackey_maps_proportional : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ), JacquetOfInducedFiltration k → IsSmoothChar χ₁ → IsSmoothChar χ₂ → IsUnitaryChar χ₁ → IsUnitaryChar χ₂ → (a ≠ b ∨ χ₁ ≠ χ₂) → (∀ φ ψ : (jac (two (stdSum (rfl : a + b = a + b))) (parInd (two (stdSum (rfl : a + b = a + b))) ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom))).IntertwiningMap (((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)), φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap) := by
  intro k _ _ _ _ a b χ₁ χ₂ hJ h₁ h₂ u₁ u₂ hne
  have hc : Continuous (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom :=
    continuous_prodMk.2 ⟨continuous_apply _, continuous_apply _⟩
  have hsm : IsSmooth ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp
      (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom) :=
    isSmooth_comp (isSmooth_extTensor ((isSmooth_ofChar_iff _).2 h₁.detChar)
      ((isSmooth_ofChar_iff _).2 h₂.detChar)) _ hc
  obtain ⟨N, bb, hb⟩ := hJ Bool Bool (Fin (a + b)) (Two (Fin a) (Fin b)) (Two (Fin a) (Fin b))
    (two (stdSum (rfl : a + b = a + b))) (two (stdSum (rfl : a + b = a + b)))
  obtain ⟨S, hm, hbot, htop, hE⟩ := hb (TensorProduct ℂ ℂ ℂ) _ hsm
  obtain ⟨D, hD⟩ := exists_diagonal_sizeMatrix a b
  obtain ⟨t₀, ht₀⟩ := bb.surjective D
  refine GlobalTheory.T.filtration_unique_subquotient _ ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom) N S hm hbot htop t₀ ?_ ?_
  · exact proportional_of_equiv (hE t₀ (SizeMatrix.nonempty_rows (bb t₀)).some (SizeMatrix.nonempty_cols (bb t₀)).some).some
      (GlobalTheory.T.cell_functor_scalar_diagonal k a b χ₁ χ₂ (bb t₀) _ _ ((hD _).1 ht₀))
  · intro t ht
    exact eq_zero_of_equiv (hE t (SizeMatrix.nonempty_rows (bb t)).some (SizeMatrix.nonempty_cols (bb t)).some).some
      (GlobalTheory.T.cell_functor_nonscalar_offdiag k a b χ₁ χ₂ h₁ h₂ u₁ u₂ hne (bb t) _ _ fun h0 =>
        ht (bb.injective (((hD _).2 h0).trans ht₀.symm)))

end GlobalTheory.CompanionTheory.SmGL.Bernstein
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetInducedTwoCharactersStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

theorem _root_.GlobalTheory.T.jacquet_induced_two_characters : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ), JacquetOfInducedFiltration k → IsSmoothChar χ₁ → IsSmoothChar χ₂ → IsUnitaryChar χ₁ → IsUnitaryChar χ₂ → (a ≠ b ∨ χ₁ ≠ χ₂) → (∀ φ ψ : (jac (two (stdSum (rfl : a + b = a + b))) (parInd (two (stdSum (rfl : a + b = a + b))) ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom))).IntertwiningMap (((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)), φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap) := by
  first | exact @GlobalTheory.CompanionTheory.SmGL.Bernstein.mackey_maps_proportional | exact GlobalTheory.CompanionTheory.SmGL.Bernstein.mackey_maps_proportional | (intros; apply GlobalTheory.CompanionTheory.SmGL.Bernstein.mackey_maps_proportional <;> assumption)
end
end
