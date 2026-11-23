module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSkewHermitianMulAddDetNeZeroOfPairStatement
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.Ideal.BigOperators
import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicGraphDetLowerRowNeZeroField

section

@[expose] public section

open scoped Matrix

namespace GlobalTheory

theorem exists_isotropic_graph_det_lowerRow_ne_zero_field :
    ∀ (k : Type) [Field k] (σ : k →+* k), (∀ x, σ (σ x) = x) → (∃ ε : k, ε ≠ 0 ∧ σ ε = -ε) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) k), (∀ i j, σ (J j i) = J i j) → J.det ≠ 0 →
    ∀ g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k, g.det ≠ 0 →
      gᵀ * Matrix.fromBlocks 0 J J 0 * g.map σ = Matrix.fromBlocks 0 J J 0 →
      ∃ Z : Matrix (Fin n) (Fin n) k, Zᵀ * J + J * Z.map σ = 0 ∧
        (g.toBlocks₂₁ * Z + g.toBlocks₂₂).det ≠ 0 := by
  intro k _ σ hσ hε n J hJ hJd g hg hQ
  obtain ⟨ε, hε0, hε⟩ := hε
  have hmm : ∀ A : Matrix (Fin n) (Fin n) k, (A.map σ).map σ = A := by
    intro A; ext i j; simp [hσ]
  have hJu : IsUnit J.det := isUnit_iff_ne_zero.mpr hJd
  set K : Matrix (Fin n) (Fin n) k := J⁻¹ with hK
  have hJK : J * K = 1 := Matrix.mul_nonsing_inv J hJu
  have hKJ : K * J = 1 := Matrix.nonsing_inv_mul J hJu
  have hJh : (J.map σ)ᵀ = J := by ext i j; simp [hJ]
  have hKh : (K.map σ)ᵀ = K := by
    have h1 : (K.map σ)ᵀ * J = 1 := by
      conv_lhs => rw [← hJh]
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, hJK]
      simp
    calc (K.map σ)ᵀ = (K.map σ)ᵀ * (J * K) := by rw [hJK, Matrix.mul_one]
      _ = K := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hKt : Kᵀ = K.map σ := by
    conv_lhs => rw [← hKh]
    simp
  have hQR : Matrix.fromBlocks 0 K K 0 * Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) k) J J 0
      = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) := by
    rw [Matrix.fromBlocks_multiply]
    simp [hKJ]
  have hRQ : Matrix.fromBlocks 0 J J 0 * Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) k) K K 0
      = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) := mul_eq_one_comm.mp hQR
  have h2 : (Matrix.fromBlocks 0 K K 0 * gᵀ * Matrix.fromBlocks 0 J J 0) * g.map σ = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᵀ, hQ, hQR]
  have h3 := mul_eq_one_comm.mp h2
  have h4 : g.map σ * Matrix.fromBlocks 0 K K 0 * gᵀ = Matrix.fromBlocks 0 K K 0 := by
    calc g.map σ * Matrix.fromBlocks 0 K K 0 * gᵀ
        = g.map σ * Matrix.fromBlocks 0 K K 0 * gᵀ *
          (Matrix.fromBlocks 0 J J 0 * Matrix.fromBlocks 0 K K 0) := by rw [hRQ, Matrix.mul_one]
      _ = (g.map σ * (Matrix.fromBlocks 0 K K 0 * gᵀ * Matrix.fromBlocks 0 J J 0)) *
          Matrix.fromBlocks 0 K K 0 := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h3, Matrix.one_mul]
  obtain ⟨A, B, C, D, rfl⟩ : ∃ A B C D, g = Matrix.fromBlocks A B C D :=
    ⟨_, _, _, _, (Matrix.fromBlocks_toBlocks g).symm⟩
  rw [Matrix.fromBlocks_map, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj] at h4
  have h5 := h4.2.2.2
  simp only [Matrix.mul_zero, zero_add, add_zero] at h5
  have h6 : D * K.map σ * (C.map σ)ᵀ + C * K.map σ * (D.map σ)ᵀ = 0 := by
    have := congrArg (fun M : Matrix (Fin n) (Fin n) k => M.map σ) h5
    simp only [Matrix.map_add σ (map_add σ), Matrix.map_mul, hmm, Matrix.map_zero σ (map_zero σ)] at this
    simpa [Matrix.transpose_map] using this
  have hJσ : K.map σ * J.map σ = 1 := by
    rw [← Matrix.map_mul, hKJ]; simp
  obtain ⟨V, hV, hdet⟩ := GlobalTheory.T.exists_skewHermitian_mul_add_det_ne_zero k σ hσ ε hε0 hε n (C * K.map σ) D
    (by
      rw [Matrix.map_mul, hmm, Matrix.transpose_mul, hKt, ← Matrix.mul_assoc, add_comm]
      exact h6)
    (by
      intro a ha hD
      have hC : a ᵥ* C = 0 := by
        have : a ᵥ* (C * K.map σ * J.map σ) = 0 := by
          rw [← Matrix.vecMul_vecMul, ha, Matrix.zero_vecMul]
        rwa [Matrix.mul_assoc, hJσ, Matrix.mul_one] at this
      have h7 : (Sum.elim 0 a) ᵥ* Matrix.fromBlocks A B C D = 0 := by
        rw [Matrix.vecMul_fromBlocks]
        simp [hC, hD]
      have h8 := Matrix.eq_zero_of_vecMul_eq_zero hg h7
      funext i
      exact congrFun h8 (Sum.inr i))
  refine ⟨K.map σ * V, ?_, ?_⟩
  · rw [Matrix.transpose_mul, hKh, Matrix.mul_assoc, hKJ, Matrix.mul_one, Matrix.map_mul, hmm,
      ← Matrix.mul_assoc, hJK, Matrix.one_mul]
    have : V.map σ = -Vᵀ := by
      rw [← Matrix.transpose_neg, ← hV, Matrix.transpose_transpose]
    rw [this, add_neg_cancel]
  · simpa [Matrix.mul_assoc] using hdet

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicGraphDetLowerRowNeZeroFieldStatement

section

@[expose] public section

open scoped Matrix

theorem _root_.GlobalTheory.T.exists_isotropic_graph_det_ne_zero : ∀ (k : Type) [Field k] (σ : k →+* k), (∀ x, σ (σ x) = x) → (∃ ε : k, ε ≠ 0 ∧ σ ε = -ε) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) k), (∀ i j, σ (J j i) = J i j) → J.det ≠ 0 →
    ∀ g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k, g.det ≠ 0 →
      gᵀ * Matrix.fromBlocks 0 J J 0 * g.map σ = Matrix.fromBlocks 0 J J 0 →
      ∃ Z : Matrix (Fin n) (Fin n) k, Zᵀ * J + J * Z.map σ = 0 ∧ (g.toBlocks₂₁ * Z + g.toBlocks₂₂).det ≠ 0 := by
  first | exact @GlobalTheory.exists_isotropic_graph_det_lowerRow_ne_zero_field | exact GlobalTheory.exists_isotropic_graph_det_lowerRow_ne_zero_field | (intros; apply GlobalTheory.exists_isotropic_graph_det_lowerRow_ne_zero_field <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftModMaximalSkew

section

@[expose] public section

open scoped Matrix

namespace GlobalTheory

theorem lift_mod_maximal_skew : ∀ (O : Type) [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) O), (∀ i j, c (J j i) = J i j) → IsUnit J.det →
    ∀ Z₀ : Matrix (Fin n) (Fin n) O, (∀ i j, (Z₀ᵀ * J + J * Z₀.map c) i j ∈ IsLocalRing.maximalIdeal O) →
      ∃ Z : Matrix (Fin n) (Fin n) O, Zᵀ * J + J * Z.map c = 0 ∧ ∀ i j, Z i j - Z₀ i j ∈ IsLocalRing.maximalIdeal O := by
  intro O _ _ c hc h2 n J hJ hdet Z₀ hZ
  obtain ⟨u, hu⟩ : ∃ u : O, u * 2 = 1 := ⟨h2.unit⁻¹.val, h2.val_inv_mul⟩
  have hcu : c u = u := by
    have h1 : c u * 2 = 1 := by
      have := congrArg c hu
      simpa [map_mul, map_ofNat] using this
    calc c u = c u * (u * 2) := by rw [hu, mul_one]
      _ = (c u * 2) * u := by ring
      _ = u := by rw [h1, one_mul]
  set E := Z₀ᵀ * J + J * Z₀.map c with hE
  have hJc : (J.map c)ᵀ = J := by
    ext i j; simp [Matrix.transpose_apply, Matrix.map_apply, hJ]
  have hEc : (E.map c)ᵀ = E := by
    ext i j

    simp only [hE, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.mul_apply, map_add (f := _), map_sum, map_mul, hc, hJ]
    rw [add_comm]
    congr 1 <;> refine Finset.sum_congr rfl (fun k _ => ?_) <;> ring
  have hJinv : J * ((J⁻¹).map c)ᵀ = 1 := by
    calc J * ((J⁻¹).map c)ᵀ = (J.map c)ᵀ * ((J⁻¹).map c)ᵀ := by rw [hJc]
      _ = ((J⁻¹).map c * J.map c)ᵀ := by rw [Matrix.transpose_mul]
      _ = ((J⁻¹ * J).map c)ᵀ := by rw [Matrix.map_mul]
      _ = 1 := by rw [Matrix.nonsing_inv_mul J hdet, Matrix.map_one c c.map_zero c.map_one, Matrix.transpose_one]
  set D := (u • (E * J⁻¹))ᵀ with hD
  have hDT : Dᵀ * J = u • E := by
    rw [hD, Matrix.transpose_transpose, Matrix.smul_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul J hdet, Matrix.mul_one]
  have hDmap : D.map c = u • (((J⁻¹).map c)ᵀ * (E.map c)ᵀ) := by
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, hD]
    ext i j

    simp [Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.mul_apply, map_sum, map_mul, hcu]
  have hDc : J * D.map c = u • E := by
    rw [hDmap, Matrix.mul_smul, ← Matrix.mul_assoc, hJinv, Matrix.one_mul, hEc]
  refine ⟨Z₀ - D, ?_, ?_⟩
  · have hmap : (Z₀ - D).map c = Z₀.map c - D.map c := by
      ext i j; simp [Matrix.map_apply]
    rw [Matrix.transpose_sub, Matrix.sub_mul, hmap, Matrix.mul_sub, hDT, hDc]
    have : E - u • E - u • E = 0 := by
      rw [sub_sub, ← add_smul, ← two_mul, mul_comm, hu, one_smul, sub_self]
    rw [← this, hE]; abel
  · intro i j
    have : (Z₀ - D) i j - Z₀ i j = -(u * ∑ k, E j k * J⁻¹ k i) := by
      simp [hD, Matrix.transpose_apply, Matrix.mul_apply, Matrix.smul_apply, mul_comm]
    rw [this]
    exact neg_mem (Ideal.mul_mem_left _ _ (Ideal.sum_mem _ (fun k _ => Ideal.mul_mem_right _ _ (hZ j k))))

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftModMaximalSkewStatement

section

@[expose] public section

open scoped Matrix

theorem _root_.GlobalTheory.T.exists_skew_lift_mod_maximalIdeal : ∀ (O : Type) [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) O), (∀ i j, c (J j i) = J i j) → IsUnit J.det →
    ∀ Z₀ : Matrix (Fin n) (Fin n) O, (∀ i j, (Z₀ᵀ * J + J * Z₀.map c) i j ∈ IsLocalRing.maximalIdeal O) →
      ∃ Z : Matrix (Fin n) (Fin n) O, Zᵀ * J + J * Z.map c = 0 ∧ ∀ i j, Z i j - Z₀ i j ∈ IsLocalRing.maximalIdeal O := by
  first | exact @GlobalTheory.lift_mod_maximal_skew | exact GlobalTheory.lift_mod_maximal_skew | (intros; apply GlobalTheory.lift_mod_maximal_skew <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicGraphUnitaryIsUnitLowerBlock

section

@[expose] public section

open scoped Matrix

namespace GlobalTheory

theorem exists_isotropic_graph_isUnit_lowerRow : ∀ (O : Type) [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    (∃ x : O, IsUnit (c x - x)) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) O), (∀ i j, c (J j i) = J i j) → IsUnit J.det →
    ∀ g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O, IsUnit g.det →
      gᵀ * Matrix.fromBlocks 0 J J 0 * g.map c = Matrix.fromBlocks 0 J J 0 →
      ∃ Z : Matrix (Fin n) (Fin n) O, Zᵀ * J + J * Z.map c = 0 ∧ IsUnit (g.toBlocks₂₁ * Z + g.toBlocks₂₂).det := by
  have hfield := GlobalTheory.T.exists_isotropic_graph_det_ne_zero
  have hlift := GlobalTheory.T.exists_skew_lift_mod_maximalIdeal

  intro O _ _ c hc h2 hx0 n J hJ hJdet g hg hgu
  obtain ⟨x, hx⟩ := hx0
  haveI : IsLocalHom c := ⟨fun a ha => by simpa [hc] using ha.map c⟩
  set π := IsLocalRing.residue O with hπ
  set σ : IsLocalRing.ResidueField O →+* IsLocalRing.ResidueField O := IsLocalRing.ResidueField.map c with hσ
  have hσπ : ∀ a, σ (π a) = π (c a) := fun a => IsLocalRing.ResidueField.map_residue c a
  have hσσ : ∀ y, σ (σ y) = y := by
    intro y; obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y; rw [hσπ, hσπ, hc]
  have hε : ∃ ε, ε ≠ 0 ∧ σ ε = -ε := ⟨π (c x - x), (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hx, by
    rw [hσπ, map_sub, hc, ← neg_sub, map_neg]⟩
  have hmapc : ∀ {m : Type} (M : Matrix m m O), (M.map c).map π = (M.map π).map σ := by
    intro m M; ext i j; simp [hσπ]
  have hJ' : ∀ i j, σ (J.map π j i) = J.map π i j := by intro i j; simp [hσπ, hJ]
  have hJdet' : (J.map π).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hJdet
  have hg' : (g.map π).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hg
  have hgu' : (g.map π)ᵀ * Matrix.fromBlocks 0 (J.map π) (J.map π) 0 * (g.map π).map σ
      = Matrix.fromBlocks 0 (J.map π) (J.map π) 0 := by
    have := congrArg (fun M => M.map π) hgu
    simpa only [Matrix.map_mul, Matrix.transpose_map, hmapc, Matrix.fromBlocks_map,
      Matrix.map_zero _ (map_zero π)] using this
  obtain ⟨Zb, hZb, hdet⟩ := hfield _ σ hσσ hε n _ hJ' hJdet' _ hg' hgu'
  obtain ⟨Z₀, hZ₀⟩ : ∃ Z₀ : Matrix (Fin n) (Fin n) O, Z₀.map π = Zb :=
    ⟨fun i j => (IsLocalRing.residue_surjective (Zb i j)).choose, by
      ext i j; exact (IsLocalRing.residue_surjective (Zb i j)).choose_spec⟩
  have hZ₀m : ∀ i j, (Z₀ᵀ * J + J * Z₀.map c) i j ∈ IsLocalRing.maximalIdeal O := by
    intro i j
    rw [← IsLocalRing.residue_eq_zero_iff]
    have := congrArg (fun M => M i j) hZb
    simp only [Matrix.zero_apply] at this
    rw [← this, ← hZ₀, ← hmapc, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add π)]
    rfl
  obtain ⟨Z, hZ, hZm⟩ := hlift O c hc h2 n J hJ hJdet Z₀ hZ₀m
  refine ⟨Z, hZ, ?_⟩
  have hZπ : Z.map π = Zb := by
    rw [← hZ₀]; ext i j
    simp only [Matrix.map_apply]
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]; exact hZm i j
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, ← hπ, RingHom.map_det, RingHom.mapMatrix_apply,
    Matrix.map_add _ (map_add π), Matrix.map_mul, hZπ]
  exact hdet

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicGraphUnitaryIsUnitLowerBlockStatement

section

@[expose] public section

open scoped Matrix

theorem _root_.GlobalTheory.T.exists_isotropic_graph_unitary_isUnit_lowerBlock : ∀ (O : Type) [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    (∃ x : O, IsUnit (c x - x)) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) O), (∀ i j, c (J j i) = J i j) → IsUnit J.det →
    ∀ g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O, IsUnit g.det →
      gᵀ * Matrix.fromBlocks 0 J J 0 * g.map c = Matrix.fromBlocks 0 J J 0 →
      ∃ Z : Matrix (Fin n) (Fin n) O, Zᵀ * J + J * Z.map c = 0 ∧ IsUnit (g.toBlocks₂₁ * Z + g.toBlocks₂₂).det := by
  first | exact @GlobalTheory.exists_isotropic_graph_isUnit_lowerRow | exact GlobalTheory.exists_isotropic_graph_isUnit_lowerRow | (intros; apply GlobalTheory.exists_isotropic_graph_isUnit_lowerRow <;> assumption)
end
end
