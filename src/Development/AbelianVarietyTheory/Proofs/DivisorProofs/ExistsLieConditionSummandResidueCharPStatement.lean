module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorModOfTmul
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.LocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenCoordinatesIdempotentRangeQuotient
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
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSigmaStableSummandFromLiftedEigenCoordsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MoritaSpreadStableSummandLieDecompositionStatement
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenCoordinatesIdempotentRangeQuotientStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
open IsLocalRing
universe u

theorem _root_.GlobalTheory.T.exists_eigenCoordinates_idempotentRange_quotient : ∀ {C : Type} [CommRing C] [IsLocalRing C] (I : Ideal C), I ^ 2 = ⊥ →
  ∀ {A : Type} [CommRing A] {H : Type u} [AddCommGroup H] [Module C H] [Module.Finite C H] [Module.Projective C H]
  (σ : A →+* Module.End C H) (a : ℕ) (χ : Fin a → A →+* C),
  (∀ i j, i ≠ j → Ideal.span (Set.range fun x => χ i x - χ j x) = ⊤) →
  ∀ (π : Module.End C H), π * π = π → (∀ c, σ c * π = π * σ c) →
  ∀ (F : Submodule C H), I • ⊤ ≤ F → (∀ c, ∀ x ∈ F, σ c x ∈ F) → (∀ x ∈ F, π x ∈ F) →
  (∃ E' M : Submodule C H, IsCompl E' M ∧ E' ⊔ I • ⊤ = F) →
  (∀ d ∈ LinearMap.range π, ∃ w : Fin a → H, (∀ i c, σ c (w i) - χ i c • w i ∈ F) ∧ d - ∑ i, w i ∈ F) →
  ∃ (n : ℕ) (κ : Fin n → Fin a) (ℓ : Fin n → H →ₗ[C] C ⧸ I) (y : Fin n → H),
    (∀ k c x, ℓ k (σ c x) = Ideal.Quotient.mk I (χ (κ k) c) * ℓ k x) ∧
    (∀ x ∈ LinearMap.range π, x ∈ F ↔ ∀ k, ℓ k x = 0) ∧
    (∀ k, y k ∈ LinearMap.range π) ∧ ∀ j k, ℓ j (y k) = if j = k then 1 else 0 := by
  first | exact @GlobalTheory.exists_eigen_coordinates_range_quot | exact GlobalTheory.exists_eigen_coordinates_range_quot | (intros; apply GlobalTheory.exists_eigen_coordinates_range_quot <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatrixActionOfPadicOrderSplitting

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
open IsLocalRing
universe u

namespace GlobalTheory

theorem padicInt_ringHom_eq_val {p : ℕ} [Fact p.Prime] {B : Type*} [Ring B] (k : ℕ) (hB : (p : B) ^ k = 0)
    (f : ℤ_[p] →+* B) (z : ℤ_[p]) : f z = (((PadicInt.toZModPow k z).val : ℕ) : B) := by
  set v : ℕ := (PadicInt.toZModPow k z).val with hv
  have hmem : z - (v : ℤ_[p]) ∈ RingHom.ker (PadicInt.toZModPow (p := p) k) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, hv, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hmem
  obtain ⟨y, hy⟩ := hmem
  have hz : z = (v : ℤ_[p]) + (p : ℤ_[p]) ^ k * y := by rw [← hy]; ring
  calc f z = f ((v : ℤ_[p]) + (p : ℤ_[p]) ^ k * y) := by rw [← hz]
    _ = (v : B) := by rw [map_add (f := _), map_mul, map_pow, map_natCast, map_natCast, hB, zero_mul, add_zero]

theorem exists_matrix_action_of_splitting : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (C : Type) [CommRing C] (k : ℕ), (p : C) ^ k = 0 →
  ∀ (H : Type u) [AddCommGroup H] [Module C H] (ρ : D.O →+* Module.End C H)
  (s : (D.O ⊗[ℤ] ℤ_[p]) ≃ₐ[𝓞 D.F] Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p])),
  ∃ Ψ : Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p]) →+* Module.End C H,
    (∀ c, Ψ (s (c ⊗ₜ 1)) = ρ c) ∧
    (∀ T : Module.End C H, (∀ c, ρ c * T = T * ρ c) → ∀ M, Ψ M * T = T * Ψ M) ∧
    (∀ N : Submodule C H, (∀ c, ∀ x ∈ N, ρ c x ∈ N) → ∀ M, ∀ x ∈ N, Ψ M x ∈ N) ∧
    ∀ y (N : Submodule C H), (∀ a, ∀ x ∈ N, ρ (algebraMap (𝓞 D.F) D.O a) x ∈ N) → ∀ x ∈ N, Ψ (Matrix.scalar _ y) x ∈ N := by
  intro p _ D C _ k hk H _ _ ρ s
  have hdvd : ringChar C ∣ p ^ k := ringChar.dvd (by rw [Nat.cast_pow]; exact hk)
  let ιp : ℤ_[p] →+* C := (ZMod.castHom hdvd C).comp (PadicInt.toZModPow k)
  let g : ℤ_[p] →+* Module.End C H := (algebraMap C (Module.End C H)).comp ιp
  let Φ : D.O ⊗[ℤ] ℤ_[p] →ₐ[ℤ] Module.End C H :=
    Algebra.TensorProduct.lift ρ.toIntAlgHom g.toIntAlgHom
      (fun c z => by
        show Commute (ρ c) (algebraMap C (Module.End C H) (ιp z))
        exact Algebra.commute_algebraMap_right _ _)
  have hΦ : ∀ c z, Φ (c ⊗ₜ z) = ρ c * algebraMap C (Module.End C H) (ιp z) := by
    intro c z; simp [Φ, g]

  have hind : ∀ P : Module.End C H → Prop, P 0 → (∀ a b, P a → P b → P (a + b)) →
      (∀ c r, P (ρ c * algebraMap C (Module.End C H) r)) → ∀ t, P (Φ t) := by
    intro P h0 hadd hgen t
    induction t using TensorProduct.induction_on with
    | zero => simpa using h0
    | tmul c z => rw [hΦ]; exact hgen c (ιp z)
    | add a b ha hb => rw [map_add (f := _)]; exact hadd _ _ ha hb
  let Ψ : Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p]) →+* Module.End C H :=
    (Φ : D.O ⊗[ℤ] ℤ_[p] →+* Module.End C H).comp (s.symm : _ →+* _)
  have hΨ : ∀ M, Ψ M = Φ (s.symm M) := fun M => rfl
  refine ⟨Ψ, ?_, ?_, ?_, ?_⟩
  · intro c
    rw [hΨ, AlgEquiv.symm_apply_apply, hΦ, map_one, map_one, _root_.mul_one]
  · intro T hT M
    rw [hΨ]
    refine hind (fun A => A * T = T * A) (by simp) (fun a b ha hb => by rw [_root_.add_mul, _root_.mul_add, ha, hb])
      (fun c r => ?_) _
    rw [_root_.mul_assoc, Algebra.commutes, ← _root_.mul_assoc, hT, _root_.mul_assoc]
  · intro N hN M x hx
    rw [hΨ]
    refine hind (fun A => ∀ x ∈ N, A x ∈ N) (by simp) (fun a b ha hb x hx => ?_) (fun c r x hx => ?_) _ x hx
    · rw [LinearMap.add_apply]; exact N.add_mem (ha x hx) (hb x hx)
    · rw [Module.End.mul_apply, Module.algebraMap_end_apply]
      exact hN c _ (N.smul_mem r hx)
  · intro y N hN
    have hpk : (p : Module.End C H) ^ k = 0 := by
      rw [← map_natCast (algebraMap C (Module.End C H)), ← map_pow, hk, map_zero]
    have hright : ∀ z : ℤ_[p], ∀ x ∈ N, Ψ (Matrix.scalar (Fin D.m) ((1 : 𝓞 D.F) ⊗ₜ[ℤ] z)) x ∈ N := by
      intro z x hx
      let f : ℤ_[p] →+* Module.End C H :=
        (Ψ.comp (Matrix.scalar (Fin D.m))).comp Algebra.TensorProduct.includeRight.toRingHom
      have hf : Ψ (Matrix.scalar (Fin D.m) ((1 : 𝓞 D.F) ⊗ₜ[ℤ] z)) = f z := rfl
      rw [hf, padicInt_ringHom_eq_val k hpk f z, Module.End.natCast_apply]
      exact N.nsmul_mem hx _
    have hleft : ∀ a : 𝓞 D.F, ∀ x ∈ N, Ψ (Matrix.scalar (Fin D.m) (a ⊗ₜ[ℤ] (1 : ℤ_[p]))) x ∈ N := by
      intro a x hx
      have h1 : Matrix.scalar (Fin D.m) (a ⊗ₜ[ℤ] (1 : ℤ_[p])) =
          algebraMap (𝓞 D.F) (Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p])) a := by
        rw [Matrix.algebraMap_eq_diagonal]; rfl
      have h2 : s.symm (algebraMap (𝓞 D.F) _ a) = algebraMap (𝓞 D.F) D.O a ⊗ₜ[ℤ] (1 : ℤ_[p]) := by
        rw [AlgEquiv.commutes]; rfl
      rw [h1, hΨ, h2, hΦ, map_one, map_one, _root_.mul_one]
      exact hN a x hx
    intro x hx
    induction y using TensorProduct.induction_on generalizing x with
    | zero => simpa using N.zero_mem
    | tmul a z =>
      have : (a ⊗ₜ[ℤ] z : 𝓞 D.F ⊗[ℤ] ℤ_[p]) = (a ⊗ₜ[ℤ] (1 : ℤ_[p])) * ((1 : 𝓞 D.F) ⊗ₜ[ℤ] z) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]
      rw [this, map_mul, map_mul, Module.End.mul_apply]
      exact hleft a _ (hright z x hx)
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), LinearMap.add_apply]; exact N.add_mem (ha x hx) (hb x hx)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatrixActionOfPadicOrderSplittingStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
open IsLocalRing
universe u

theorem _root_.GlobalTheory.T.exists_matrixAction_of_padicOrderSplitting : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (C : Type) [CommRing C] (k : ℕ), (p : C) ^ k = 0 →
  ∀ (H : Type u) [AddCommGroup H] [Module C H] (ρ : D.O →+* Module.End C H)
  (s : (D.O ⊗[ℤ] ℤ_[p]) ≃ₐ[𝓞 D.F] Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p])),
  ∃ Ψ : Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p]) →+* Module.End C H,
    (∀ c, Ψ (s (c ⊗ₜ 1)) = ρ c) ∧
    (∀ T : Module.End C H, (∀ c, ρ c * T = T * ρ c) → ∀ M, Ψ M * T = T * Ψ M) ∧
    (∀ N : Submodule C H, (∀ c, ∀ x ∈ N, ρ c x ∈ N) → ∀ M, ∀ x ∈ N, Ψ M x ∈ N) ∧
    ∀ y (N : Submodule C H), (∀ a, ∀ x ∈ N, ρ (algebraMap (𝓞 D.F) D.O a) x ∈ N) → ∀ x ∈ N, Ψ (Matrix.scalar _ y) x ∈ N := by
  first | (exact @GlobalTheory.exists_matrix_action_of_splitting) | (exact GlobalTheory.exists_matrix_action_of_splitting) | (intros; apply GlobalTheory.exists_matrix_action_of_splitting  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieConditionSummandResidueCharP

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
open IsLocalRing

theorem GlobalTheory.HTSummand.Corep.mat_sum (n : ℕ) (α : Type) [CommRing α] : ∑ i : Fin n, Matrix.single i i (1:α) = 1 := by
  ext a c
  rw [Matrix.sum_apply, Matrix.one_apply]
  split_ifs with h
  · subst h
    rw [Finset.sum_eq_single a (fun b _ hb => by simp [Matrix.single_apply, hb]) (by simp)]
    simp [Matrix.single_apply]
  · exact Finset.sum_eq_zero fun x _ => by
      simp only [Matrix.single_apply]; rw [if_neg]; rintro ⟨rfl, rfl⟩; exact h rfl

theorem GlobalTheory.HTSummand.Corep.mat_sand (n : ℕ) (α : Type) [CommRing α] (i j z : Fin n) (M : Matrix (Fin n) (Fin n) α) :
    Matrix.single z i 1 * M * Matrix.single j z 1 = Matrix.scalar _ (M i j) * Matrix.single z z 1 := by
  rw [Matrix.single_mul_mul_single, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul, Matrix.smul_single,
    smul_eq_mul, _root_.mul_one, _root_.mul_one, _root_.one_mul]

theorem GlobalTheory.HTSummand.Corep.exists_summand_lie_p : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] (I : Ideal C), I ^ 2 = ⊥ → (p : C) ∈ IsLocalRing.maximalIdeal C → ∀ (tR : R →+* C) (H : Type 1) [AddCommGroup H] [Module C H] [Module.Finite C H] [Module.Projective C H] (ρ : D.O →+* Module.End C H), (letI := GlobalTheory.HTSummand.tensorModOf (ρ.comp (algebraMap (𝓞 D.F) D.O)); Module.Projective (C ⊗[ℤ] 𝓞 D.F) H) → ∀ (e : Module.End C H), e * e = e → (∀ c, ρ c * e = e * ρ c) → (∀ x, ρ (algebraMap (𝓞 D.F) D.O D.ω) (e x) = tR b.ρ • e x) → ∀ (F : Submodule C H), I • ⊤ ≤ F → (∀ (c : D.O), ∀ x ∈ F, ρ c x ∈ F) → (∀ x ∈ F, e x ∈ F) → (∃ E' M : Submodule C H, IsCompl E' M ∧ E' ⊔ I • ⊤ = F) → (∀ d ∈ LinearMap.range e, ∃ w : Fin D.a → H, (∀ i (c : 𝓞 D.F), ρ (algebraMap (𝓞 D.F) D.O c) (w i) - tR (b.t i c) • w i ∈ F) ∧ d - ∑ i, w i ∈ F) → ∃ G M : Submodule C H, G ⊓ M = ⊥ ∧ G ⊔ M = LinearMap.range e ∧ (∀ (c : D.O), ∀ x ∈ G, ρ c x ∈ G) ∧ G ⊔ (I • ⊤ ⊓ LinearMap.range e) = F ⊓ LinearMap.range e ∧ ∀ d ∈ LinearMap.range e, ∃ w : Fin D.a → H, (∀ i (c : 𝓞 D.F), ρ (algebraMap (𝓞 D.F) D.O c) (w i) - tR (b.t i c) • w i ∈ G) ∧ d - ∑ i, w i ∈ G := by
  intro p _ D R _ b C _ _ _ I hI hp tR H _ _ _ _ ρ hP e he heρ _heω F hIF hFρ hFe hcompl hLie
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (p : C) ^ k = 0 := by
    have h := IsArtinianRing.isNilpotent_jacobson_bot (R := C)
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at h
    obtain ⟨k, hk⟩ := h
    refine ⟨k, ?_⟩
    have : (p : C) ^ k ∈ (maximalIdeal C) ^ k := Ideal.pow_mem_pow hp k
    rw [hk] at this; simpa using this
  obtain ⟨Ψ, hΨρ, hΨc, hΨN, hΨs⟩ := GlobalTheory.T.exists_matrixAction_of_padicOrderSplitting p D C k hk H ρ D.splitP.some
  haveI : NeZero D.m := ⟨D.m_pos.ne'⟩
  let σ : 𝓞 D.F →+* Module.End C H := ρ.comp (algebraMap (𝓞 D.F) D.O)
  let χ : Fin D.a → 𝓞 D.F →+* C := fun i => tR.comp (b.t i)
  let E : Fin D.m → Fin D.m → Module.End C H := fun i j => Ψ (Matrix.single i j 1)
  have hE : ∀ i j k l, E i j * E k l = if j = k then E i l else 0 := by
    intro i j k l
    simp only [E, ← map_mul]
    split_ifs with h
    · subst h; rw [Matrix.single_mul_single_same, _root_.mul_one]
    · rw [Matrix.single_mul_single_of_ne (h := h), map_zero]
  have hsum : ∑ i, E i i = 1 := by

    simp only [E, ← map_sum, GlobalTheory.HTSummand.Corep.mat_sum, map_one]
  have hρσ : ∀ c c', ρ c' * σ c = σ c * ρ c' := by
    intro c c'
    show ρ c' * ρ (algebraMap _ _ c) = ρ (algebraMap _ _ c) * ρ c'
    rw [← map_mul, ← map_mul, Algebra.commutes]
  have hEσ : ∀ i j c, E i j * σ c = σ c * E i j := fun i j c => hΨc (σ c) (hρσ c) _
  have hEe : ∀ i j, E i j * e = e * E i j := fun i j => hΨc e heρ _
  have hFE : ∀ i j, ∀ x ∈ F, E i j x ∈ F := fun i j => hΨN F hFρ _
  have hθ : ∀ (c : D.O) i j (N : Submodule C H), (∀ c', ∀ x ∈ N, σ c' x ∈ N) → ∀ x ∈ N, E 0 0 x = x →
      E 0 i (ρ c (E j 0 x)) ∈ N := by
    intro c i j N hN x hx h0
    have : E 0 i (ρ c (E j 0 x)) = Ψ (Matrix.scalar _ (D.splitP.some (c ⊗ₜ 1) i j)) (E 0 0 x) := by
      rw [← hΨρ c]
      show (Ψ (Matrix.single 0 i 1) * Ψ _ * Ψ (Matrix.single j 0 1)) x = _
      rw [← map_mul, ← map_mul, GlobalTheory.HTSummand.Corep.mat_sand, map_mul]; rfl
    rw [this, h0]
    exact hΨs _ N (fun a x hx => hN a x hx) x hx
  let π : Module.End C H := E 0 0 * e
  have hππ : π * π = π := by
    show E 0 0 * e * (E 0 0 * e) = E 0 0 * e
    rw [_root_.mul_assoc, ← _root_.mul_assoc e, ← hEe, _root_.mul_assoc, he, ← _root_.mul_assoc, hE]; simp
  have hπσ : ∀ c, σ c * π = π * σ c := by
    intro c
    show σ c * (E 0 0 * e) = E 0 0 * e * σ c
    have h1 : e * σ c = σ c * e := (heρ _).symm
    rw [_root_.mul_assoc, h1, ← _root_.mul_assoc, ← _root_.mul_assoc, hEσ]
  have hFπ : ∀ x ∈ F, π x ∈ F := fun x hx => hFE 0 0 _ (hFe x hx)
  have hFσ : ∀ c, ∀ x ∈ F, σ c x ∈ F := fun c x hx => hFρ _ x hx
  have hπapp : ∀ c x, σ c (π x) = π (σ c x) := fun c x => LinearMap.congr_fun (hπσ c) x
  have hLieπ : ∀ d ∈ LinearMap.range π, ∃ w : Fin D.a → H,
      (∀ i c, σ c (w i) - χ i c • w i ∈ F) ∧ d - ∑ i, w i ∈ F := by
    rintro d ⟨x, rfl⟩
    have hde : π x ∈ LinearMap.range e := by
      refine ⟨π x, ?_⟩
      show e (E 0 0 (e x)) = E 0 0 (e x)
      rw [← Module.End.mul_apply, ← hEe, Module.End.mul_apply, ← Module.End.mul_apply e e, he]
    obtain ⟨w, hw1, hw2⟩ := hLie _ hde
    refine ⟨fun i => π (w i), fun i c => ?_, ?_⟩
    · have := hFπ _ (hw1 i c)
      rw [map_sub, map_smul] at this
      rw [hπapp]; exact this
    · have := hFπ _ hw2

      rw [map_sub, map_sum, ← Module.End.mul_apply π π, hππ] at this
      exact this
  have hcomax : ∀ i j, i ≠ j → Ideal.span (Set.range fun x => χ i x - χ j x) = ⊤ := by
    intro i j hij
    have h2 : Ideal.map tR (Ideal.span (Set.range fun x => b.t i x - b.t j x)) = ⊤ := by
      rw [b.comax i j hij, Ideal.map_top]
    rw [Ideal.map_span, ← Set.range_comp] at h2
    simpa [Function.comp_def, χ] using h2
  obtain ⟨n, κ, ℓ, y, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_eigenCoordinates_idempotentRange_quotient I hI σ D.a χ hcomax π hππ hπσ F hIF hFσ hFπ hcompl hLieπ
  obtain ⟨G₀, M₀, g1, g2, g3, g4, g5⟩ := GlobalTheory.T.exists_sigmaStable_summand_from_lifted_eigenCoords I hI σ hP D.a χ π hππ hπσ F hIF n κ ℓ y h1 h2 h3 h4
  exact GlobalTheory.T.moritaSpread_stableSummand_lieDecomposition I D.m E hE hsum σ hEσ ρ hθ e he hEe F hIF hFE hFe D.a χ G₀ M₀ g1 g2 g3 g4 g5
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieConditionSummandResidueCharPStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_lieCondition_summand_residueCharP : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] (I : Ideal C), I ^ 2 = ⊥ → (p : C) ∈ IsLocalRing.maximalIdeal C → ∀ (tR : R →+* C) (H : Type 1) [AddCommGroup H] [Module C H] [Module.Finite C H] [Module.Projective C H] (ρ : D.O →+* Module.End C H), (letI := GlobalTheory.HTSummand.tensorModOf (ρ.comp (algebraMap (𝓞 D.F) D.O)); Module.Projective (C ⊗[ℤ] 𝓞 D.F) H) → ∀ (e : Module.End C H), e * e = e → (∀ c, ρ c * e = e * ρ c) → (∀ x, ρ (algebraMap (𝓞 D.F) D.O D.ω) (e x) = tR b.ρ • e x) → ∀ (F : Submodule C H), I • ⊤ ≤ F → (∀ (c : D.O), ∀ x ∈ F, ρ c x ∈ F) → (∀ x ∈ F, e x ∈ F) → (∃ E' M : Submodule C H, IsCompl E' M ∧ E' ⊔ I • ⊤ = F) → (∀ d ∈ LinearMap.range e, ∃ w : Fin D.a → H, (∀ i (c : 𝓞 D.F), ρ (algebraMap (𝓞 D.F) D.O c) (w i) - tR (b.t i c) • w i ∈ F) ∧ d - ∑ i, w i ∈ F) → ∃ G M : Submodule C H, G ⊓ M = ⊥ ∧ G ⊔ M = LinearMap.range e ∧ (∀ (c : D.O), ∀ x ∈ G, ρ c x ∈ G) ∧ G ⊔ (I • ⊤ ⊓ LinearMap.range e) = F ⊓ LinearMap.range e ∧ ∀ d ∈ LinearMap.range e, ∃ w : Fin D.a → H, (∀ i (c : 𝓞 D.F), ρ (algebraMap (𝓞 D.F) D.O c) (w i) - tR (b.t i c) • w i ∈ G) ∧ d - ∑ i, w i ∈ G := by
  first | exact @GlobalTheory.HTSummand.Corep.exists_summand_lie_p | exact GlobalTheory.HTSummand.Corep.exists_summand_lie_p | (intros; apply GlobalTheory.HTSummand.Corep.exists_summand_lie_p <;> assumption)
end
end
