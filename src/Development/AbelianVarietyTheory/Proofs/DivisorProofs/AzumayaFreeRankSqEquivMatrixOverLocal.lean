module

public import Mathlib.Algebra.Azumaya.Defs
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.LocalRing.Defs
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.LinearAlgebra.DFinsupp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsResidueIdempotentStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
public import Mathlib.NumberTheory.Padics.RingHoms

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AzumayaAlgEquivMatrixOfIdempotent

section

@[expose] public section

open IsLocalRing
open scoped TensorProduct

namespace GlobalTheory

section Corner

variable {A : Type} [CommRing A] {Λ : Type} [Ring Λ] [Algebra A Λ]

noncomputable def leftIdealMulAlgHom (A : Type) [CommRing A] {Λ : Type} [Ring Λ] [Algebra A Λ]
    (e : Λ) : Λ →ₐ[A] Module.End A (LinearMap.range (LinearMap.mulRight A e)) where
  toFun l := (LinearMap.mulLeft A l).restrict (by
    rintro _ ⟨y, rfl⟩
    exact ⟨l * y, by simp [mul_assoc]⟩)
  map_one' := by ext p; simp [LinearMap.restrict_apply]
  map_mul' x y := by ext p; simp [LinearMap.restrict_apply, mul_assoc]
  map_zero' := by ext p; simp [LinearMap.restrict_apply]
  map_add' x y := by ext p; simp [LinearMap.restrict_apply, add_mul]
  commutes' c := by ext p; simp [LinearMap.restrict_apply, Algebra.smul_def]

theorem leftIdealMulAlgHom_apply_coe (e l : Λ) (p : LinearMap.range (LinearMap.mulRight A e)) :
    ((leftIdealMulAlgHom A e l p : LinearMap.range (LinearMap.mulRight A e)) : Λ) = l * p := rfl

theorem leftIdealMulAlgHom_injective (e : Λ)
    (h : ∃ (N : ℕ) (a b : Fin N → Λ), ∑ i, a i * e * b i = 1) :
    Function.Injective (leftIdealMulAlgHom A e) := by
  obtain ⟨N, a, b, hab⟩ := h
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro l hl
  have h0 : ∀ y : Λ, l * (y * e) = 0 := by
    intro y
    have := leftIdealMulAlgHom_apply_coe (A := A) e l ⟨y * e, y, rfl⟩
    rw [hl] at this
    simpa using this.symm
  calc l = l * ∑ i, a i * e * b i := by rw [hab, mul_one]
    _ = ∑ i, l * (a i * e) * b i := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by simp only [mul_assoc]
    _ = 0 := by simp [h0]

theorem exists_mul_eq_mulLeftRight_of_corner (e : Λ)
    (hc : ∀ y : Λ, ∃ c : A, e * y * e = c • e) (t : Λ ⊗[A] Λᵐᵒᵖ) :
    ∃ l : Λ, ∀ y : Λ, AlgHom.mulLeftRight A Λ t (y * e) * e = l * (y * e) := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, fun y => by simp⟩
  | tmul a b =>
    obtain ⟨c, hc⟩ := hc b.unop
    refine ⟨c • a, fun y => ?_⟩
    rw [AlgHom.mulLeftRight_apply]
    calc a * (y * e) * b.unop * e = a * y * (e * b.unop * e) := by simp only [mul_assoc]
      _ = c • a * (y * e) := by rw [hc]; simp [mul_assoc]
  | add s t hs ht =>
    obtain ⟨l, hl⟩ := hs
    obtain ⟨m, hm⟩ := ht
    exact ⟨l + m, fun y => by rw [map_add (f := _), LinearMap.add_apply, add_mul, hl, hm, add_mul]⟩

theorem leftIdealMulAlgHom_surjective [IsAzumaya A Λ] (e : Λ) (he : IsIdempotentElem e)
    (hc : ∀ y : Λ, ∃ c : A, e * y * e = c • e) :
    Function.Surjective (leftIdealMulAlgHom A e) := by
  intro f
  obtain ⟨t, ht⟩ := (IsAzumaya.bij (R := A) (A := Λ)).2
    ((LinearMap.range (LinearMap.mulRight A e)).subtype ∘ₗ f ∘ₗ
      (LinearMap.mulRight A e).rangeRestrict)
  obtain ⟨l, hl⟩ := exists_mul_eq_mulLeftRight_of_corner e hc t
  refine ⟨l, ?_⟩
  ext ⟨_, y, rfl⟩
  rw [leftIdealMulAlgHom_apply_coe]
  change l * (y * e) = _
  rw [← hl y, ht]
  have h1 : (LinearMap.mulRight A e).rangeRestrict (y * e)
      = ⟨LinearMap.mulRight A e y, y, rfl⟩ := by
    ext; simp [mul_assoc, he.eq]
  simp only [LinearMap.comp_apply, h1, Submodule.subtype_apply]
  obtain ⟨z, hz⟩ := (f ⟨LinearMap.mulRight A e y, y, rfl⟩).2
  rw [← hz]
  simp [mul_assoc, he.eq]

end Corner

theorem azumaya_algEquiv_matrix_of_idempotent :
    ∀ (A : Type) [CommRing A] [IsLocalRing A] (Λ : Type) [Ring Λ] [Algebra A Λ] [IsAzumaya A Λ]
      [Module.Free A Λ] (n : ℕ), Module.finrank A Λ = n ^ 2 → ∀ e : Λ, IsIdempotentElem e →
      (∀ y : Λ, ∃ c : A, e * y * e = c • e) →
      (∃ (N : ℕ) (a b : Fin N → Λ), ∑ i, a i * e * b i = 1) →
      Nonempty (Λ ≃ₐ[A] Matrix (Fin n) (Fin n) A) := by
  intro A _ _ Λ _ _ _ _ n hn e he hc hs
  let P := LinearMap.range (LinearMap.mulRight A e)
  let φ : Λ ≃ₐ[A] Module.End A P := AlgEquiv.ofBijective (leftIdealMulAlgHom A e)
    ⟨leftIdealMulAlgHom_injective e hs, leftIdealMulAlgHom_surjective e he hc⟩
  haveI : Module.Projective A P :=
    Module.Projective.of_split P.subtype (LinearMap.mulRight A e).rangeRestrict (by
      ext ⟨_, y, rfl⟩
      simp [mul_assoc, he.eq])
  haveI : Module.Finite A P := Module.Finite.range _
  haveI : Module.Free A P := Module.free_of_flat_of_isLocalRing
  have hr : Module.finrank A P = n := by
    have h1 := φ.toLinearEquiv.finrank_eq
    rw [hn, Module.finrank_linearMap, ← sq] at h1
    exact (Nat.pow_left_injective two_ne_zero h1).symm
  exact ⟨φ.trans (LinearMap.toMatrixAlgEquiv (Module.finBasisOfFinrankEq A P hr))⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AzumayaAlgEquivMatrixOfIdempotentStatement

section

@[expose] public section

open IsLocalRing
open scoped TensorProduct

theorem _root_.GlobalTheory.T.nonempty_algEquiv_matrix_of_isAzumaya_of_full_idempotent : ∀ (A : Type) [CommRing A] [IsLocalRing A] (Λ : Type) [Ring Λ] [Algebra A Λ] [IsAzumaya A Λ] [Module.Free A Λ] (n : ℕ), Module.finrank A Λ = n ^ 2 → ∀ e : Λ, IsIdempotentElem e → (∀ y : Λ, ∃ c : A, e * y * e = c • e) → (∃ (N : ℕ) (a b : Fin N → Λ), ∑ i, a i * e * b i = 1) → Nonempty (Λ ≃ₐ[A] Matrix (Fin n) (Fin n) A) := by
  first | (exact @GlobalTheory.azumaya_algEquiv_matrix_of_idempotent) | (exact GlobalTheory.azumaya_algEquiv_matrix_of_idempotent) | (intros; apply GlobalTheory.azumaya_algEquiv_matrix_of_idempotent  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentLiftAdicCompleteFreeAlgebra

section

@[expose] public section

open IsLocalRing
open scoped TensorProduct

namespace GlobalTheory.IdemNewton

variable {A : Type} [CommRing A] {Λ : Type} [Ring Λ] [Algebra A Λ]

theorem mem_smul_top_iff_repr {ι : Type} [Fintype ι] (b : Module.Basis ι A Λ) (J : Ideal A) (z : Λ) :
    z ∈ J • (⊤ : Submodule A Λ) ↔ ∀ i, b.repr z i ∈ J := by
  constructor
  · intro hz i
    refine Submodule.smul_induction_on hz (fun r hr y _ => ?_) (fun y w hy hw => ?_)
    · rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact J.mul_mem_right _ hr
    · rw [map_add (f := _), Finsupp.add_apply]
      exact add_mem hy hw
  · intro h
    rw [← b.sum_repr z]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top

theorem mul_mem_right {J : Ideal A} {z : Λ} (y : Λ) (hz : z ∈ J • (⊤ : Submodule A Λ)) :
    z * y ∈ J • (⊤ : Submodule A Λ) := by
  refine Submodule.smul_induction_on hz (fun r hr w _ => ?_) (fun u w hu hw => ?_)
  · rw [smul_mul_assoc]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  · rw [add_mul]
    exact add_mem hu hw

theorem mul_mem_left {J : Ideal A} {z : Λ} (y : Λ) (hz : z ∈ J • (⊤ : Submodule A Λ)) :
    y * z ∈ J • (⊤ : Submodule A Λ) := by
  refine Submodule.smul_induction_on hz (fun r hr w _ => ?_) (fun u w hu hw => ?_)
  · rw [mul_smul_comm]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  · rw [mul_add]
    exact add_mem hu hw

theorem mul_mem {J K : Ideal A} {z y : Λ} (hz : z ∈ J • (⊤ : Submodule A Λ))
    (hy : y ∈ K • (⊤ : Submodule A Λ)) : z * y ∈ (J * K) • (⊤ : Submodule A Λ) := by
  refine Submodule.smul_induction_on hz (fun r hr w _ => ?_) (fun u w hu hw => ?_)
  · rw [smul_mul_assoc, Submodule.mul_smul]
    exact Submodule.smul_mem_smul hr (mul_mem_left w hy)
  · rw [add_mul]
    exact add_mem hu hw

theorem exists_idem : ∀ (A : Type) [CommRing A] (I : Ideal A) [IsAdicComplete I A] (Λ : Type) [Ring Λ]
    [Algebra A Λ] [Module.Free A Λ] [Module.Finite A Λ] (x : Λ),
    x * x - x ∈ I • (⊤ : Submodule A Λ) →
      ∃ e : Λ, IsIdempotentElem e ∧ e - x ∈ I • (⊤ : Submodule A Λ) := by
  intro A _ I _ Λ _ _ _ _ x hx
  let b := Module.Free.chooseBasis A Λ
  have mono : ∀ {k m : ℕ}, k ≤ m → ∀ {z : Λ}, z ∈ (I ^ m) • (⊤ : Submodule A Λ) →
      z ∈ (I ^ k) • (⊤ : Submodule A Λ) := fun hkm _ hz =>
    Submodule.smul_mono_left (Ideal.pow_le_pow_right hkm) hz
  let f : ℕ → Λ := fun k => Nat.rec x (fun _ y => 3 * (y * y) - 2 * (y * y * y)) k
  have f0 : f 0 = x := rfl
  have fs : ∀ k, f (k + 1) = 3 * (f k * f k) - 2 * (f k * f k * f k) := fun k => rfl
  have h1 : ∀ k, (f k * f k - f k) ∈ (I ^ (k + 1)) • (⊤ : Submodule A Λ) := by
    intro k
    induction k with
    | zero => simpa [f0] using hx
    | succ k ih =>
      have e : f (k + 1) * f (k + 1) - f (k + 1) =
          ((f k * f k - f k) * (f k * f k - f k)) * (4 * (f k * f k) - 4 * f k - 3) := by
        rw [fs]; noncomm_ring
      rw [e]
      refine mul_mem_right _ ?_
      have := mul_mem ih ih
      rw [← pow_add] at this
      exact mono (by omega) this
  have h2 : ∀ k, (f (k + 1) - f k) ∈ (I ^ (k + 1)) • (⊤ : Submodule A Λ) := by
    intro k
    have e : f (k + 1) - f k = (f k * f k - f k) * (1 - 2 * f k) := by
      rw [fs]; noncomm_ring
    rw [e]
    exact mul_mem_right _ (h1 k)
  have h3 : ∀ k m, k ≤ m → (f m - f k) ∈ (I ^ (k + 1)) • (⊤ : Submodule A Λ) := by
    intro k m hkm
    induction m, hkm using Nat.le_induction with
    | base => simp
    | succ m hkm ih =>
      have e : f (m + 1) - f k = (f (m + 1) - f m) + (f m - f k) := by abel
      rw [e]
      exact add_mem (mono (by omega) (h2 m)) ih
  have h4 : ∀ i, ∃ L : A, ∀ k, b.repr (f k) i - L ∈ I ^ k := by
    intro i
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := I) (fun k => b.repr (f k) i) (fun {k m} hkm => by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_mem_iff, neg_sub]
      have := (mem_smul_top_iff_repr b _ _).1 (mono (Nat.le_succ k) (h3 k m hkm)) i
      rwa [map_sub, Finsupp.sub_apply] at this)
    refine ⟨L, fun k => ?_⟩
    have := hL k
    rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
  choose L hL using h4
  let e : Λ := b.equivFun.symm L
  have he : ∀ i, b.repr e i = L i := fun i => by
    have := congrFun (b.equivFun.apply_symm_apply L) i
    rwa [Module.Basis.equivFun_apply] at this
  have hL' : ∀ k, (f k - e) ∈ (I ^ k) • (⊤ : Submodule A Λ) := fun k =>
    (mem_smul_top_iff_repr b _ _).2 fun i => by
      rw [map_sub, Finsupp.sub_apply, he]
      exact hL i k
  refine ⟨e, ?_, ?_⟩
  · change e * e = e
    rw [← sub_eq_zero]
    refine b.ext_elem fun i => ?_
    rw [map_zero, Finsupp.zero_apply]
    refine IsHausdorff.haus' (I := I) _ fun k => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    refine (mem_smul_top_iff_repr b _ _).1 ?_ i
    have e1 : e * e - e = (f k * f k - f k) - ((f k - e) * (f k - 1) + e * (f k - e)) := by
      noncomm_ring
    rw [e1]
    exact sub_mem (mono (Nat.le_succ k) (h1 k))
      (add_mem (mul_mem_right _ (hL' k)) (mul_mem_left _ (hL' k)))
  · have e1 : e - x = (f 1 - f 0) - (f 1 - e) := by rw [f0]; abel
    rw [e1]
    have a := h2 0
    have c := hL' 1
    rw [zero_add, pow_one] at a
    rw [pow_one] at c
    exact sub_mem a c

end GlobalTheory.IdemNewton
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentLiftAdicCompleteFreeAlgebraStatement

section

@[expose] public section

open IsLocalRing
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_idempotent_lift_adicComplete_free_algebra : ∀ (A : Type) [CommRing A] (I : Ideal A) [IsAdicComplete I A] (Λ : Type) [Ring Λ] [Algebra A Λ] [Module.Free A Λ] [Module.Finite A Λ] (x : Λ), x * x - x ∈ I • (⊤ : Submodule A Λ) → ∃ e : Λ, IsIdempotentElem e ∧ e - x ∈ I • (⊤ : Submodule A Λ) := by
  first | (exact @GlobalTheory.IdemNewton.exists_idem) | (exact GlobalTheory.IdemNewton.exists_idem) | (intros; apply GlobalTheory.IdemNewton.exists_idem  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AzumayaFreeRankSqEquivMatrixOverLocal

section

@[expose] public section

open IsLocalRing
open scoped TensorProduct

namespace GlobalTheory.AzumayaLocal

theorem mem_left {A Λ : Type} [CommRing A] [Ring Λ] [Algebra A Λ] {I : Ideal A} (w : Λ) {z : Λ}
    (hz : z ∈ I • (⊤ : Submodule A Λ)) : w * z ∈ I • (⊤ : Submodule A Λ) := by
  refine Submodule.smul_induction_on hz (fun a ha t _ => ?_) (fun x y hx hy => ?_)
  · rw [mul_smul_comm]; exact Submodule.smul_mem_smul ha trivial
  · rw [mul_add]; exact Submodule.add_mem _ hx hy

theorem mem_right {A Λ : Type} [CommRing A] [Ring Λ] [Algebra A Λ] {I : Ideal A} (w : Λ) {z : Λ}
    (hz : z ∈ I • (⊤ : Submodule A Λ)) : z * w ∈ I • (⊤ : Submodule A Λ) := by
  refine Submodule.smul_induction_on hz (fun a ha t _ => ?_) (fun x y hx hy => ?_)
  · rw [smul_mul_assoc]; exact Submodule.smul_mem_smul ha trivial
  · rw [add_mul]; exact Submodule.add_mem _ hx hy

end GlobalTheory.AzumayaLocal

theorem GlobalTheory.AzumayaLocal.finite_residueField : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [IsLocalRing A] [Algebra ℤ_[ℓ] A] [Module.Finite ℤ_[ℓ] A], Finite (IsLocalRing.ResidueField A) := by
  intro ℓ _ A _ _ _ _
  have hmax : (maximalIdeal A).comap (algebraMap ℤ_[ℓ] A) = maximalIdeal ℤ_[ℓ] :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (maximalIdeal A))
  haveI : IsLocalHom (algebraMap ℤ_[ℓ] A) := ⟨fun x hx => by
    by_contra h
    have : x ∈ (maximalIdeal A).comap (algebraMap ℤ_[ℓ] A) := by rw [hmax]; exact h
    exact (mem_maximalIdeal _).1 this hx⟩
  have : Finite (IsLocalRing.ResidueField ℤ_[ℓ]) := Finite.of_equiv _ (PadicInt.residueField).symm.toEquiv
  exact Module.finite_of_finite (IsLocalRing.ResidueField ℤ_[ℓ])

theorem GlobalTheory.AzumayaLocal.exists_right_inverse : ∀ (A : Type) [CommRing A] [IsLocalRing A] (Λ : Type) [Ring Λ] [Algebra A Λ] [Module.Finite A Λ] (u : Λ), u - 1 ∈ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A Λ) → ∃ v : Λ, u * v = 1 := by
  intro A _ _ Λ _ _ _ u hu
  let f : Λ →ₗ[A] Λ := LinearMap.mulLeft A u
  have hle : (⊤ : Submodule A Λ) ≤ LinearMap.range f ⊔ (maximalIdeal A) • (⊤ : Submodule A Λ) := by
    intro y _
    have hy : y = u * y - (u - 1) * y := by noncomm_ring
    rw [hy]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left ⟨y, rfl⟩)
      (Submodule.mem_sup_right (GlobalTheory.AzumayaLocal.mem_right y hu))
  have htop : LinearMap.range f = ⊤ :=
    top_le_iff.1 (Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
      (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge hle)
  obtain ⟨v, hv⟩ := LinearMap.range_eq_top.1 htop 1
  exact ⟨v, hv⟩

theorem GlobalTheory.AzumayaLocal.corner_eq_smul : ∀ (A : Type) [CommRing A] [IsLocalRing A] (Λ : Type) [Ring Λ] [Algebra A Λ] [Module.Finite A Λ] (e : Λ), IsIdempotentElem e → (∀ y : Λ, ∃ c : A, e * y * e - c • e ∈ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A Λ)) → ∀ y : Λ, ∃ c : A, e * y * e = c • e := by
  intro A _ _ Λ _ _ _ e he h y
  let g : Λ →ₗ[A] Λ := (LinearMap.mulRight A e).comp (LinearMap.mulLeft A e)
  have hg : ∀ z, g z = e * z * e := fun z => rfl
  have hge : g e = e := by rw [hg, he.eq, he.eq]
  have hgg : ∀ z, g (e * z * e) = e * z * e := by
    intro z
    rw [hg, ← mul_assoc, ← mul_assoc, he.eq, mul_assoc (e * z) e e, he.eq]
  have hS : LinearMap.range g ≤ A ∙ e := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (by rw [LinearMap.range_eq_map]; exact Module.Finite.fg_top.map g)
      (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge ?_
    rintro _ ⟨z, rfl⟩
    obtain ⟨c, hc⟩ := h z
    have key : g z - c • e = g (e * z * e - c • e) := by
      rw [map_sub, map_smul, hgg, hge, hg]
    have hmem : g z - c • e ∈ (maximalIdeal A) • LinearMap.range g := by
      rw [key, LinearMap.range_eq_map, ← Submodule.map_smul'']
      exact Submodule.mem_map_of_mem hc
    rw [show g z = c • e + (g z - c • e) by abel]
    exact Submodule.add_mem_sup (Submodule.smul_mem _ c (Submodule.mem_span_singleton_self e)) hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hS ⟨y, rfl⟩)
  exact ⟨c, hc.symm⟩

namespace GlobalTheory.AzumayaLocal

theorem azumaya_local_matrix : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [IsLocalRing A] [Algebra ℤ_[ℓ] A]
    [Module.Finite ℤ_[ℓ] A] (Λ : Type) [Ring Λ] [Algebra A Λ] [IsAzumaya A Λ] [Module.Free A Λ]
    (n : ℕ), Module.finrank A Λ = n ^ 2 → Nonempty (Λ ≃ₐ[A] Matrix (Fin n) (Fin n) A) := by
  intro ℓ _ A _ _ _ _ Λ _ _ _ _ n hn
  haveI : IsAdicComplete (maximalIdeal A) A :=
    GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local ℤ_[ℓ] A
  haveI : Finite (ResidueField A) := GlobalTheory.AzumayaLocal.finite_residueField ℓ A
  haveI : Nontrivial Λ := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact zero_ne_one (FaithfulSMul.algebraMap_injective A Λ
      (Subsingleton.elim (algebraMap A Λ 0) (algebraMap A Λ 1)))
  set M := (maximalIdeal A) • (⊤ : Submodule A Λ) with hM
  obtain ⟨x, h1, h2, N, a, b, h3⟩ := GlobalTheory.T.exists_residue_idempotent' A Λ
  obtain ⟨e, he, hex⟩ := GlobalTheory.T.exists_idempotent_lift_adicComplete_free_algebra A (maximalIdeal A) Λ x h1
  have hcorner : ∀ y : Λ, ∃ c : A, e * y * e - c • e ∈ M := by
    intro y
    obtain ⟨c, hc⟩ := h2 y
    refine ⟨c, ?_⟩
    have : e * y * e - c • e = (x * y * x - c • x) + ((e - x) * (y * e) + x * y * (e - x) - c • (e - x)) := by
      simp only [sub_mul, mul_sub, smul_sub, mul_assoc]; abel
    rw [this]
    exact M.add_mem hc (M.sub_mem (M.add_mem (mem_right _ hex) (mem_left _ hex)) (M.smul_mem c hex))
  have hu : ∑ i, a i * e * b i - 1 ∈ M := by
    have : ∑ i, a i * e * b i - 1 = (∑ i, a i * x * b i - 1) + ∑ i, a i * (e - x) * b i := by
      simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]; abel
    rw [this]
    exact M.add_mem h3 (M.sum_mem fun i _ => mem_right _ (mem_left _ hex))
  obtain ⟨v, hv⟩ := GlobalTheory.AzumayaLocal.exists_right_inverse A Λ _ hu
  exact GlobalTheory.T.nonempty_algEquiv_matrix_of_isAzumaya_of_full_idempotent A Λ n hn e he (GlobalTheory.AzumayaLocal.corner_eq_smul A Λ e he hcorner) ⟨N, a, fun i => b i * v, by
    rw [← hv, Finset.sum_mul]; simp only [mul_assoc]⟩

end GlobalTheory.AzumayaLocal
end
end
