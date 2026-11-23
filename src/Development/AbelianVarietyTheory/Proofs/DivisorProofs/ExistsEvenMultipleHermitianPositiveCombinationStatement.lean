module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.Basic.Complex.Basic
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
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitEqPositiveSquaresTimesSelfAdjointStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianEndoMatrixRationalInLatticeBasisStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormEqCombinationOfSelfAdjointIdentityStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NsmulAevalMemLatticeOfIntRationalMatrixStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosDefRealGramPairHermitianFormsStatement
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.HaveILetI
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfAdjointEndoRelatingHermitianForms

section

@[expose] public section

open Matrix

namespace GlobalTheory

theorem herm_gamma_star_map_mulVec {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (v : Fin g → ℂ) :
    star (M.map star *ᵥ v) = M *ᵥ star v := by
  funext i
  simp only [mulVec, dotProduct, Pi.star_apply, star_sum, map_apply, star_mul', star_star]

theorem herm_gamma_map_mulVec_dot {g : ℕ} (B : Matrix (Fin g) (Fin g) ℂ) (z u : Fin g → ℂ) :
    (B *ᵥ z) ⬝ᵥ u = z ⬝ᵥ (Bᵀ *ᵥ u) := by
  rw [dotProduct_comm, dotProduct_mulVec, mulVec_transpose, dotProduct_comm]

theorem herm_gamma_det_ne_zero {g : ℕ} (H₁ : Matrix (Fin g) (Fin g) ℂ)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₁.mulVec (star z)).re) : H₁.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hHv⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 hdet
  have hz : star v ≠ 0 := by
    intro h; apply hv; simpa using congrArg star h
  have := hpos (star v) hz
  rw [star_star, hHv, dotProduct_zero] at this
  simp at this

theorem herm_gamma : ∀ (g : ℕ) (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ), H₁.IsHermitian → H₂.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₁.mulVec (star z)).re) →
    ∃ γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ),
      (∀ z w, z ⬝ᵥ H₂.mulVec (star w) = z ⬝ᵥ H₁.mulVec (star (γ w))) ∧
      ∀ z w, z ⬝ᵥ H₂.mulVec (star (γ w)) = γ z ⬝ᵥ H₂.mulVec (star w) := by
  intro g H₁ H₂ h1 h2 hpos
  have hdet : IsUnit H₁.det := isUnit_iff_ne_zero.2 (herm_gamma_det_ne_zero H₁ hpos)
  refine ⟨Matrix.toLin' ((H₁⁻¹ * H₂).map star), ?_, ?_⟩
  · intro z w
    rw [Matrix.toLin'_apply, herm_gamma_star_map_mulVec, mulVec_mulVec, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul]
  · intro z w
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, herm_gamma_star_map_mulVec, mulVec_mulVec,
      herm_gamma_map_mulVec_dot, mulVec_mulVec]
    congr 2
    have hT : ((H₁⁻¹ * H₂).map star)ᵀ = (H₁⁻¹ * H₂)ᴴ := rfl
    rw [hT, conjTranspose_mul, h2.eq, conjTranspose_nonsing_inv, h1.eq, Matrix.mul_assoc]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfAdjointEndoRelatingHermitianFormsStatement

section

@[expose] public section

open Matrix

theorem _root_.GlobalTheory.T.exists_selfAdjoint_endo_relating_hermitian_forms : ∀ (g : ℕ) (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ), H₁.IsHermitian → H₂.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₁.mulVec (star z)).re) →
    ∃ γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ),
      (∀ z w, z ⬝ᵥ H₂.mulVec (star w) = z ⬝ᵥ H₁.mulVec (star (γ w))) ∧
      ∀ z w, z ⬝ᵥ H₂.mulVec (star (γ w)) = γ z ⬝ᵥ H₂.mulVec (star w) := by
  first | exact @GlobalTheory.herm_gamma | exact GlobalTheory.herm_gamma | (intros; apply GlobalTheory.herm_gamma <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalMatrixIdentityTransferToComplexMap

section

@[expose] public section

open Matrix

namespace GlobalTheory

noncomputable def endRealMatrixRingHom {g n : ℕ} (e : Module.Basis (Fin n) ℝ (Fin g → ℂ)) :
    Module.End ℂ (Fin g → ℂ) →+* Matrix (Fin n) (Fin n) ℝ where
  toFun f := LinearMap.toMatrix e e (f.restrictScalars ℝ)
  map_one' := by
    have : ((1 : Module.End ℂ (Fin g → ℂ)).restrictScalars ℝ) = 1 := rfl
    rw [this]; exact LinearMap.toMatrix_one e
  map_mul' f h := by
    have : ((f * h).restrictScalars ℝ) = f.restrictScalars ℝ * h.restrictScalars ℝ := rfl
    rw [this]; exact LinearMap.toMatrix_mul e _ _
  map_zero' := by
    have : ((0 : Module.End ℂ (Fin g → ℂ)).restrictScalars ℝ) = 0 := rfl
    rw [this]; exact map_zero _
  map_add' f h := by
    have : ((f + h).restrictScalars ℝ) = f.restrictScalars ℝ + h.restrictScalars ℝ := rfl
    rw [this]; exact map_add _ _ _

theorem endRealMatrixRingHom_injective {g n : ℕ} (e : Module.Basis (Fin n) ℝ (Fin g → ℂ)) :
    Function.Injective (endRealMatrixRingHom e) := by
  intro f h hfh
  have h1 : f.restrictScalars ℝ = h.restrictScalars ℝ := (LinearMap.toMatrix e e).injective hfh
  exact LinearMap.restrictScalars_injective ℝ h1

theorem matrix_identity_transfer (g n : ℕ) (e : Module.Basis (Fin n) ℝ (Fin g → ℂ))
    (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (Tq : Matrix (Fin n) (Fin n) ℚ)
    (hT : Tq.map (Rat.cast : ℚ → ℝ) = LinearMap.toMatrix e e (γ.restrictScalars ℝ))
    (c₀ : ℚ) (r : ℕ) (c : Fin r → ℚ) (p : Fin r → Polynomial ℚ)
    (hid : (1 : Matrix (Fin n) (Fin n) ℚ) = c₀ • Tq + ∑ i, c i • ((Polynomial.aeval Tq (p i)) ^ 2 * Tq)) :
    (1 : Module.End ℂ (Fin g → ℂ)) = c₀ • γ + ∑ i, c i • ((Polynomial.aeval γ (p i)) ^ 2 * γ) := by
  let F := (endRealMatrixRingHom e).toRatAlgHom
  let ψ : Matrix (Fin n) (Fin n) ℚ →ₐ[ℚ] Matrix (Fin n) (Fin n) ℝ := (Algebra.ofId ℚ ℝ).mapMatrix
  have hψ : ∀ M, ψ M = M.map (Rat.cast : ℚ → ℝ) := by
    intro M; ext i j; simp [ψ]
  have hFγ : F γ = ψ Tq := by rw [hψ, hT]; rfl
  apply endRealMatrixRingHom_injective e
  change F 1 = F _
  have key := congrArg ψ hid
  rw [map_one] at key
  rw [map_one, key]

  simp only [map_add (f := _), map_sum, map_smul, map_mul, map_pow, ← Polynomial.aeval_algHom_apply, hFγ]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalMatrixIdentityTransferToComplexMapStatement

section

@[expose] public section

open Matrix

theorem _root_.GlobalTheory.T.rational_matrix_identity_transfer_to_complex_map : ∀ (g n : ℕ) (e : Module.Basis (Fin n) ℝ (Fin g → ℂ)) (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (Tq : Matrix (Fin n) (Fin n) ℚ),
    Tq.map (Rat.cast : ℚ → ℝ) = LinearMap.toMatrix e e (γ.restrictScalars ℝ) →
    ∀ (c₀ : ℚ) (r : ℕ) (c : Fin r → ℚ) (p : Fin r → Polynomial ℚ),
    (1 : Matrix (Fin n) (Fin n) ℚ) = c₀ • Tq + ∑ i, c i • ((Polynomial.aeval Tq (p i)) ^ 2 * Tq) →
    (1 : Module.End ℂ (Fin g → ℂ)) = c₀ • γ + ∑ i, c i • ((Polynomial.aeval γ (p i)) ^ 2 * γ) := by
  first | exact @GlobalTheory.matrix_identity_transfer | exact GlobalTheory.matrix_identity_transfer | (intros; apply GlobalTheory.matrix_identity_transfer <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenMultipleHermitianPositiveCombination

section

@[expose] public section

open Matrix

namespace GlobalTheory.Desc.HermComb

theorem lat_basis (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (hd : DiscreteTopology Λ)
    (hs : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) :
    ∃ (n : ℕ) (e : Module.Basis (Fin n) ℝ (Fin g → ℂ)),
      ∀ x, x ∈ Λ ↔ ∀ k, ∃ m : ℤ, e.repr x k = m := by
  haveI : IsZLattice ℝ Λ := ⟨hs⟩
  let b := Module.finBasis ℤ Λ
  refine ⟨_, b.ofZLatticeBasis ℝ Λ, fun x => ⟨fun hx k => ⟨b.repr ⟨x, hx⟩ k, ?_⟩, fun h => ?_⟩⟩
  · exact b.ofZLatticeBasis_repr_apply ℝ Λ ⟨x, hx⟩ k
  · choose m hm using h
    have hx : x = ∑ k, m k • (b k : Fin g → ℂ) := by
      conv_lhs => rw [← (b.ofZLatticeBasis ℝ Λ).sum_repr x]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hm k, Module.Basis.ofZLatticeBasis_apply, Int.cast_smul_eq_zsmul]
    rw [hx]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (b k).2

theorem int_of_den_dvd (q : ℚ) (D : ℕ) (h : q.den ∣ D) : ∃ m : ℤ, (D : ℚ) * q = m := by
  obtain ⟨k, rfl⟩ := h
  refine ⟨k * q.num, ?_⟩
  push_cast
  rw [mul_comm (q.den : ℚ) k, mul_assoc, mul_comm (q.den : ℚ), Rat.mul_den_eq_num]

theorem common_den (n r : ℕ) (c₀ : ℚ) (c : Fin r → ℚ) (M : Fin r → Matrix (Fin n) (Fin n) ℚ) :
    ∃ D : ℕ, 1 ≤ D ∧ (∃ m : ℤ, (D : ℚ) * c₀ = m) ∧ (∀ i, ∃ m : ℤ, (D : ℚ) * c i = m) ∧
      ∀ i k l, ∃ m : ℤ, (D : ℚ) * M i k l = m := by
  classical
  let S : Finset ℚ := insert c₀ (Finset.univ.image c ∪
    Finset.univ.image (fun x : Fin r × Fin n × Fin n => M x.1 x.2.1 x.2.2))
  have hdv : ∀ q ∈ S, q.den ∣ ∏ q ∈ S, q.den := fun q hq => Finset.dvd_prod_of_mem _ hq
  refine ⟨∏ q ∈ S, q.den, Finset.prod_pos fun (q : ℚ) _ => q.den_pos, int_of_den_dvd _ _ (hdv _ ?_),
    fun i => int_of_den_dvd _ _ (hdv _ ?_), fun i k l => int_of_den_dvd _ _ (hdv _ ?_)⟩
  · simp [S]
  · simp [S]
  · simp only [S, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inr (Or.inr ⟨(i, k, l), rfl⟩)

end GlobalTheory.Desc.HermComb

namespace GlobalTheory.Desc.HermComb

theorem main : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
    ∀ (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ), H₁.IsHermitian → H₂.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₁.mulVec (star z)).re) → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₂.mulVec (star z)).re) →
    (∀ l ∈ Λ, ∀ m ∈ Λ, ∃ n : ℤ, (n : ℝ) = (l ⬝ᵥ H₁.mulVec (star m)).im) →
    (∀ l ∈ Λ, ∀ m ∈ Λ, ∃ n : ℤ, (n : ℝ) = (l ⬝ᵥ H₂.mulVec (star m)).im) →
    ∃ (N a₀ r : ℕ) (a : Fin r → ℕ) (F : Fin r → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), 1 ≤ N ∧ 1 ≤ a₀ ∧ Even N ∧ Even a₀ ∧
      (∀ i, Even (a i)) ∧ (∀ i, ∀ l ∈ Λ, F i l ∈ Λ) ∧
      ∀ z w : Fin g → ℂ, (N : ℂ) * (z ⬝ᵥ H₁.mulVec (star w)) =
        (a₀ : ℂ) * (z ⬝ᵥ H₂.mulVec (star w)) + ∑ i, (a i : ℂ) * (F i z ⬝ᵥ H₂.mulVec (star (F i w))) := by
  intro g Λ hd hs H₁ H₂ h₁ h₂ hp₁ hp₂ hi₁ hi₂
  obtain ⟨n, e, he⟩ := lat_basis g Λ hd hs
  have hek : ∀ k, e k ∈ Λ := fun k => (he _).2 fun j =>
    ⟨if k = j then 1 else 0, by rw [e.repr_self, Finsupp.single_apply]; split_ifs <;> simp⟩
  obtain ⟨γ, hγ, hsa⟩ := GlobalTheory.T.exists_selfAdjoint_endo_relating_hermitian_forms g H₁ H₂ h₁ h₂ hp₁
  obtain ⟨Tq, hT⟩ := GlobalTheory.T.hermitian_endo_matrix_rational_in_lattice_basis g n e H₁ H₂ hp₁ (fun k l => hi₁ _ (hek k) _ (hek l))
    (fun k l => hi₂ _ (hek k) _ (hek l)) γ hγ
  obtain ⟨hB, hBT⟩ := GlobalTheory.T.posDef_real_gram_pair_hermitian_forms g n e H₁ H₂ h₁ h₂ hp₁ hp₂ γ hγ
  rw [← hT] at hBT
  obtain ⟨c₀, r, c, p, hc₀, hc, hid⟩ := GlobalTheory.T.exists_unit_eq_positive_squares_times_selfAdjoint n Tq _ hB hBT
  have hform := GlobalTheory.T.hermitian_form_eq_combination_of_selfAdjoint_identity g H₁ H₂ γ hγ hsa c₀ r c p (GlobalTheory.T.rational_matrix_identity_transfer_to_complex_map g n e γ Tq hT c₀ r c p hid)
  obtain ⟨D, hD1, ⟨m₀, hm₀⟩, hci, hM⟩ := common_den n r c₀ c (fun i => Polynomial.aeval Tq (p i))
  choose m hm using hci
  have hm₀p : 0 < m₀ := by
    have : (0 : ℚ) < m₀ := by rw [← hm₀]; exact mul_pos (by exact_mod_cast hD1) hc₀
    exact_mod_cast this
  have hmp : ∀ i, 0 ≤ m i := fun i => by
    have : (0 : ℚ) ≤ m i := by rw [← hm i]; exact (mul_pos (by exact_mod_cast hD1) (hc i)).le
    exact_mod_cast this
  refine ⟨2 * D ^ 3, 2 * D ^ 2 * m₀.toNat, r, fun i => 2 * (m i).toNat,
    fun i => D • Polynomial.aeval γ (p i), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : 1 ≤ D ^ 3 := Nat.one_le_pow _ _ hD1; omega
  · have h1 : 1 ≤ D ^ 2 := Nat.one_le_pow _ _ hD1
    have h2 : 1 ≤ m₀.toNat := by omega
    nlinarith
  · exact even_two_mul _
  · rw [mul_assoc]; exact even_two_mul _
  · exact fun i => even_two_mul _
  · exact fun i => GlobalTheory.T.nsmul_aeval_mem_lattice_of_int_rational_matrix g n Λ e he γ Tq hT (p i) D (hM i)
  · intro z w
    have hm₀' : ((m₀.toNat : ℕ) : ℂ) = (D : ℂ) * (c₀ : ℂ) := by
      have : ((m₀.toNat : ℤ) : ℚ) = (D : ℚ) * c₀ := by rw [Int.toNat_of_nonneg hm₀p.le, hm₀]
      exact_mod_cast congrArg (fun q : ℚ => (q : ℂ)) this
    have hm' : ∀ i, (((m i).toNat : ℕ) : ℂ) = (D : ℂ) * (c i : ℂ) := fun i => by
      have : (((m i).toNat : ℤ) : ℚ) = (D : ℚ) * c i := by rw [Int.toNat_of_nonneg (hmp i), hm i]
      exact_mod_cast congrArg (fun q : ℚ => (q : ℂ)) this
    have hsc : ∀ a b : Fin g → ℂ, (D • a) ⬝ᵥ H₂.mulVec (star (D • b)) = (D : ℂ) * D * (a ⬝ᵥ H₂.mulVec (star b)) := by
      intro a b
      rw [star_nsmul, mulVec_smul, dotProduct_smul, smul_dotProduct, nsmul_eq_mul, nsmul_eq_mul]; ring
    simp only [LinearMap.smul_apply, hsc]
    rw [hform z w]
    push_cast [hm₀', hm']
    rw [mul_add, Finset.mul_sum]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun i _ => ?_
      ring

end GlobalTheory.Desc.HermComb
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenMultipleHermitianPositiveCombinationStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.exists_even_multiple_hermitian_positive_combination : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
    ∀ (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ), H₁.IsHermitian → H₂.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₁.mulVec (star z)).re) → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₂.mulVec (star z)).re) →
    (∀ l ∈ Λ, ∀ m ∈ Λ, ∃ n : ℤ, (n : ℝ) = (l ⬝ᵥ H₁.mulVec (star m)).im) →
    (∀ l ∈ Λ, ∀ m ∈ Λ, ∃ n : ℤ, (n : ℝ) = (l ⬝ᵥ H₂.mulVec (star m)).im) →
    ∃ (N a₀ r : ℕ) (a : Fin r → ℕ) (F : Fin r → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), 1 ≤ N ∧ 1 ≤ a₀ ∧ Even N ∧ Even a₀ ∧
      (∀ i, Even (a i)) ∧ (∀ i, ∀ l ∈ Λ, F i l ∈ Λ) ∧
      ∀ z w : Fin g → ℂ, (N : ℂ) * (z ⬝ᵥ H₁.mulVec (star w)) =
        (a₀ : ℂ) * (z ⬝ᵥ H₂.mulVec (star w)) + ∑ i, (a i : ℂ) * (F i z ⬝ᵥ H₂.mulVec (star (F i w))) := by
  first | exact @GlobalTheory.Desc.HermComb.main | exact GlobalTheory.Desc.HermComb.main | (intros; apply GlobalTheory.Desc.HermComb.main <;> assumption)
end
end
