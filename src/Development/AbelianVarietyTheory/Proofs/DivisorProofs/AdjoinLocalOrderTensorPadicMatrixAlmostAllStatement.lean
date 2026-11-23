module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreCompat
public import Mathlib.Algebra.Central.Defs
public import Mathlib.Algebra.Azumaya.Defs
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AzumayaFreeRankSqEquivMatrixOverLocal
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AzumayaMatrixOfFinitePadicAlgebraOfLocalStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrderContainingIntegers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsScalarTowerCenAlgebra
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOrderTensorPadicFreeAlmostAll
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOrderTensorPadicIsAzumayaAlmostAllStatement
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AzumayaFreeRankSqEquivMatrixOverLocalStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.azumaya_free_rank_sq_equiv_matrix_over_local : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [IsLocalRing A] [Algebra ℤ_[ℓ] A]
    [Module.Finite ℤ_[ℓ] A] (Λ : Type) [Ring Λ] [Algebra A Λ] [IsAzumaya A Λ] [Module.Free A Λ]
    (n : ℕ), Module.finrank A Λ = n ^ 2 → Nonempty (Λ ≃ₐ[A] Matrix (Fin n) (Fin n) A) := by
  first | (exact @GlobalTheory.AzumayaLocal.azumaya_local_matrix) | (exact GlobalTheory.AzumayaLocal.azumaya_local_matrix) | (intros; apply GlobalTheory.AzumayaLocal.azumaya_local_matrix  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CenOrderFinite

section

@[expose] public section

open scoped TensorProduct
open GlobalTheory.LKInvGood

namespace GlobalTheory

theorem cenOrder_finite : ∀ (F : Type) [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime],
    Module.Finite ℤ_[ℓ] (cenOrder ℓ F) := by
  intro F _ _ ℓ _
  classical
  let f : NumberField.RingOfIntegers F → ℚ_[ℓ] ⊗[ℚ] F := fun a => (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (a : F)
  obtain ⟨s, hs⟩ := (inferInstance : Module.Finite ℤ (NumberField.RingOfIntegers F)).fg_top
  have hint : ∀ x ∈ (f '' (s : Set (NumberField.RingOfIntegers F))), IsIntegral ℤ_[ℓ] x := by
    rintro _ ⟨a, -, rfl⟩
    have h1 : IsIntegral ℤ ((a : F)) := NumberField.RingOfIntegers.isIntegral_coe a
    have h2 : IsIntegral ℤ (f a) := by
      have := h1.map ((Algebra.TensorProduct.includeRight : F →ₐ[ℚ] ℚ_[ℓ] ⊗[ℚ] F).restrictScalars ℤ)
      simpa [f] using this
    exact h2.tower_top
  have hfin : Module.Finite ℤ_[ℓ] (Algebra.adjoin ℤ_[ℓ] (f '' (s : Set (NumberField.RingOfIntegers F)))) :=
    Algebra.finite_adjoin_of_finite_of_isIntegral ((s.finite_toSet).image f) hint
  have heq : cenOrder ℓ F = Algebra.adjoin ℤ_[ℓ] (f '' (s : Set (NumberField.RingOfIntegers F))) := by
    apply le_antisymm
    · apply Algebra.adjoin_le
      rintro _ ⟨a, rfl⟩
      let A := Algebra.adjoin ℤ_[ℓ] (f '' (s : Set (NumberField.RingOfIntegers F)))
      let N : Submodule ℤ (NumberField.RingOfIntegers F) :=
        { carrier := {x | f x ∈ A}
          add_mem' := by
            intro x y hx hy
            simp only [Set.mem_setOf_eq, f, map_add (f := _), TensorProduct.tmul_add] at hx hy ⊢
            exact A.add_mem hx hy
          zero_mem' := by
            simp only [Set.mem_setOf_eq, f, map_zero, TensorProduct.tmul_zero]
            exact A.zero_mem
          smul_mem' := by
            intro c x hx
            simp only [Set.mem_setOf_eq, f, zsmul_eq_mul, map_mul, map_intCast] at hx ⊢
            have : (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((c : F) * (x : F)) = c • ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (x : F)) := by
              rw [← zsmul_eq_mul, TensorProduct.tmul_smul]
            rw [this]
            exact A.toSubring.zsmul_mem hx c }
      have hsN : (s : Set _) ⊆ N := fun x hx => show f x ∈ A from Algebra.subset_adjoin ⟨x, hx, rfl⟩
      have : a ∈ N := by
        have := Submodule.span_le.mpr hsN
        rw [hs] at this
        exact this Submodule.mem_top
      exact this
    · apply Algebra.adjoin_mono
      rintro _ ⟨a, -, rfl⟩
      exact ⟨a, rfl⟩
  rw [heq]
  exact hfin

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOrderTensorPadicFreeAlmostAllStatement

section

@[expose] public section

open scoped TensorProduct
open GlobalTheory.LKInvGood
open GlobalTheory.LocMatrix in

theorem _root_.GlobalTheory.T.localOrderTensorPadic_free_almost_all : ∀ (F B : Type) [Field F] [NumberField F] [Ring B] [Algebra F B] [Algebra ℚ B]
    [IsScalarTower ℚ F B] [FiniteDimensional F B] (Λ : Subring B)
    (hΛ : ∀ a : NumberField.RingOfIntegers F, algebraMap F B (a : F) ∈ Λ),
    Module.Finite ℤ Λ → (∀ b : B, ∃ m : ℕ, 0 < m ∧ (m : B) * b ∈ Λ) →
    ∃ N : ℕ, 0 < N ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ ℓ ∣ N →
      letI := GlobalTheory.LocMatrix.cenAlgebra ℓ F B Λ hΛ;
      Module.Free (cenOrder ℓ F) (locOrder ℓ Λ) ∧
        Module.finrank (cenOrder ℓ F) (locOrder ℓ Λ) = Module.finrank F B := by
  intro F B _ _ _ _ _ _ _ Λ hΛ hfin hspan
  obtain ⟨v, hvΛ⟩ := exists_basis_mem (F := F) Λ hspan
  obtain ⟨D, hD, hDΛ⟩ := exists_den Λ hfin v
  refine ⟨D, hD, fun ℓ _ hℓ => ?_⟩
  let inst := GlobalTheory.LocMatrix.cenAlgebra ℓ F B Λ hΛ
  have hBasis : Nonempty (Module.Basis (Fin (Module.finrank F B)) (cenOrder ℓ F) (locOrder ℓ Λ)) := by
    let w : Fin (Module.finrank F B) → locOrder ℓ Λ := fun i =>
      ⟨(1 : ℚ_[ℓ]) ⊗ₜ v i, Algebra.subset_adjoin ⟨_, hvΛ i, rfl⟩⟩
    have hsum (c : Fin (Module.finrank F B) → cenOrder ℓ F) :
        ((∑ i, c i • w i : locOrder ℓ Λ) : ℚ_[ℓ] ⊗[ℚ] B) =
          combMap (F := F) ℓ v (fun i => (c i : ℚ_[ℓ] ⊗[ℚ] F)) := by
      rw [AddSubmonoidClass.coe_finsetSum, combMap_apply]
      rfl
    have hli : LinearIndependent (cenOrder ℓ F) w := by
      rw [Fintype.linearIndependent_iff]
      intro c hc i
      have h0 : combMap (F := F) ℓ v (fun i => (c i : ℚ_[ℓ] ⊗[ℚ] F)) = combMap (F := F) ℓ v 0 := by
        rw [← hsum, hc, map_zero]
        rfl
      exact Subtype.ext (congrFun (combMap_injective ℓ v h0) i)
    have hsp : ⊤ ≤ Submodule.span (cenOrder ℓ F) (Set.range w) := by
      rintro ⟨z, hz⟩ -
      obtain ⟨c, hc⟩ := exists_coeffs ℓ Λ v D hDΛ hℓ z hz
      rw [Submodule.mem_span_range_iff_exists_fun]
      exact ⟨c, Subtype.ext ((hsum c).trans hc.symm)⟩
    exact ⟨Module.Basis.mk hli hsp⟩
  have : Nontrivial (ℚ_[ℓ] ⊗[ℚ] F) := by
    apply Module.nontrivial_of_finrank_pos (R := ℚ_[ℓ])
    rw [Module.finrank_baseChange]
    exact Module.finrank_pos
  obtain ⟨basis⟩ := hBasis
  exact ⟨Module.Free.of_basis basis, by rw [Module.finrank_eq_card_basis basis, Fintype.card_fin]⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitSectionAvoidPrime

section

@[expose] public section

open scoped TensorProduct
open GlobalTheory.LKInvGood

namespace GlobalTheory

theorem one_tmul_mem_locOrder_of_nsmul_mem : ∀ {B : Type} [Ring B] [Algebra ℚ B] (OB : Subring B) (b : B) (m : ℕ),
    0 < m → (m : B) * b ∈ OB → ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ ℓ ∣ m →
    (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b ∈ locOrder ℓ OB := by
  intro B _ _ OB b m hm hmb ℓ _ hℓ
  have hunit : IsUnit (m : ℤ_[ℓ]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact ((Nat.Prime.coprime_iff_not_dvd (Fact.out : ℓ.Prime)).mpr hℓ)
  obtain ⟨u, hu⟩ := hunit
  have hgen : (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((m : B) * b) ∈ locOrder ℓ OB :=
    Algebra.subset_adjoin ⟨_, hmb, rfl⟩
  have key : (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b = ((u⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((m : B) * b)) := by
    rw [TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
    have : ((m : B) * b) = (m : ℚ) • b := by rw [Algebra.smul_def]; simp
    rw [this, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    congr 1
    have h1 : ((u : ℤ_[ℓ]) : ℚ_[ℓ]) = (m : ℚ_[ℓ]) := by rw [hu]; simp
    have h2 : (((u⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) : ℚ_[ℓ]) * ((u : ℤ_[ℓ]) : ℚ_[ℓ]) = 1 := by
      rw [← PadicInt.coe_mul]; simp
    rw [h1] at h2
    rw [Algebra.smul_def]
    simp only [map_natCast]
    rw [PadicInt.algebraMap_apply]
    linear_combination h2.symm
  rw [key]
  exact Subalgebra.smul_mem _ hgen _

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinLocalOrderTensorPadicMatrixAlmostAll

section

@[expose] public section

noncomputable section
open scoped TensorProduct
open GlobalTheory.LKInvGood

namespace GlobalTheory.LocMatrix

theorem locOrder_eq_of_le {B : Type} [Ring B] [Algebra ℚ B] (OB Λ : Subring B) (hle : OB ≤ Λ)
    (N : ℕ) (hN : 0 < N) (hNΛ : ∀ x ∈ Λ, (N : B) * x ∈ OB) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ N) :
    locOrder ℓ OB = locOrder ℓ Λ := by
  apply le_antisymm
  · exact Algebra.adjoin_mono (Set.image_mono hle)
  · refine Algebra.adjoin_le ?_
    rintro _ ⟨x, hx, rfl⟩
    exact GlobalTheory.one_tmul_mem_locOrder_of_nsmul_mem OB x N hN (hNΛ x hx) ℓ hℓ

theorem locOrder_matrix : ∀ (F B : Type) [Field F] [NumberField F] [Ring B] [Algebra F B] [Algebra ℚ B]
    [IsScalarTower ℚ F B] [Algebra.IsCentral F B] [IsSimpleRing B] [FiniteDimensional F B] (n : ℕ),
    Module.finrank F B = n ^ 2 → ∀ (OB : Subring B), Module.Finite ℤ OB →
    (∀ b : B, ∃ m : ℕ, 0 < m ∧ (m : B) * b ∈ OB) →
    ∃ N : ℕ, 0 < N ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ ℓ ∣ N →
      ∃ ψ : locOrder ℓ OB ≃ₐ[ℤ_[ℓ]] Matrix (Fin n) (Fin n) (cenOrder ℓ F), CentreCompat ℓ OB ψ := by
  intro F B _ _ _ _ _ _ _ _ _ n hn OB hfin hspan
  obtain ⟨Λ, hle, hΛ, hΛfin, N₁, hN₁, hN₁Λ⟩ := GlobalTheory.T.exists_order_containing_integers F B OB hfin hspan
  have hspanΛ : ∀ b : B, ∃ m : ℕ, 0 < m ∧ (m : B) * b ∈ Λ := fun b => by
    obtain ⟨m, hm, hmb⟩ := hspan b; exact ⟨m, hm, hle hmb⟩
  obtain ⟨N₂, hN₂, hfree⟩ := GlobalTheory.T.localOrderTensorPadic_free_almost_all F B Λ hΛ hΛfin hspanΛ
  obtain ⟨N₃, hN₃, hazu⟩ := GlobalTheory.T.localOrderTensorPadic_isAzumaya_almost_all F B Λ hΛ hΛfin hspanΛ
  refine ⟨N₁ * N₂ * N₃, by positivity, fun ℓ _ hℓ => ?_⟩
  have h₁ : ¬ ℓ ∣ N₁ := fun h => hℓ (Dvd.dvd.mul_right (Dvd.dvd.mul_right h _) _)
  have h₂ : ¬ ℓ ∣ N₂ := fun h => hℓ (Dvd.dvd.mul_right (Dvd.dvd.mul_left h _) _)
  have h₃ : ¬ ℓ ∣ N₃ := fun h => hℓ (Dvd.dvd.mul_left h _)
  have heq := locOrder_eq_of_le OB Λ hle N₁ hN₁ hN₁Λ ℓ h₁
  letI := cenAlgebra ℓ F B Λ hΛ
  haveI := isScalarTower_cenAlgebra ℓ F B Λ hΛ
  haveI : Module.Finite ℤ_[ℓ] (cenOrder ℓ F) := GlobalTheory.cenOrder_finite F ℓ
  obtain ⟨hF, hrank⟩ := hfree ℓ h₂
  haveI := hF
  haveI := hazu ℓ h₃
  obtain ⟨φ⟩ := GlobalTheory.T.azumaya_matrix_of_finite_padic_algebra_of_local GlobalTheory.T.azumaya_free_rank_sq_equiv_matrix_over_local ℓ (cenOrder ℓ F) (locOrder ℓ Λ) n (hrank.trans hn)
  refine ⟨(Subalgebra.equivOfEq _ _ heq).trans (φ.restrictScalars ℤ_[ℓ]), fun a => ?_⟩
  refine ⟨heq ▸ cenMap_mem ℓ F B Λ hΛ a.2, ?_⟩
  have h2 : (Subalgebra.equivOfEq _ _ heq) ⟨cenMap ℓ F B a, heq ▸ cenMap_mem ℓ F B Λ hΛ a.2⟩ =
      algebraMap (cenOrder ℓ F) (locOrder ℓ Λ) a := Subtype.ext rfl
  rw [AlgEquiv.trans_apply, h2, AlgEquiv.restrictScalars_apply, AlgEquiv.commutes]
  ext i j
  simp [Matrix.algebraMap_matrix_apply, Matrix.scalar_apply, Matrix.diagonal_apply]

end GlobalTheory.LocMatrix
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinLocalOrderTensorPadicMatrixAlmostAllStatement

section

@[expose] public section

open scoped TensorProduct
open GlobalTheory.LKInvGood

theorem _root_.GlobalTheory.T.adjoinLocalOrderTensorPadic_matrix_almost_all : ∀ (F B : Type) [Field F] [NumberField F] [Ring B] [Algebra F B] [Algebra ℚ B]
    [IsScalarTower ℚ F B] [Algebra.IsCentral F B] [IsSimpleRing B] [FiniteDimensional F B] (n : ℕ),
    Module.finrank F B = n ^ 2 → ∀ (OB : Subring B), Module.Finite ℤ OB →
    (∀ b : B, ∃ m : ℕ, 0 < m ∧ (m : B) * b ∈ OB) →
    ∃ N : ℕ, 0 < N ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ ℓ ∣ N →
      ∃ ψ : locOrder ℓ OB ≃ₐ[ℤ_[ℓ]] Matrix (Fin n) (Fin n) (cenOrder ℓ F), CentreCompat ℓ OB ψ := by
  first | (exact @GlobalTheory.LocMatrix.locOrder_matrix) | (exact GlobalTheory.LocMatrix.locOrder_matrix) | (intros; apply GlobalTheory.LocMatrix.locOrder_matrix  <;> assumption)
end
end
