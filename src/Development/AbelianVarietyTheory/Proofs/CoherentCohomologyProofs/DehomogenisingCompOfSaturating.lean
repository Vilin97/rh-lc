module

public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
public import Mathlib.RingTheory.Smooth.Basic
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.DehomogenisingEqZeroIff
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsGradedMapLinearCombination
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.QuotSMulTop
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsHomogeneousFamilySaturating
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsPowSmulEqAddSubOneSmul
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsXPowSmulMemSpanOfFiniteQuot
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
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsNoetherianSubringHomogeneousMatrixFlatChar
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FiniteGrCechHomology
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FiniteQuotSMulTopXSubOneOfChart
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FlatHomLocOfFlatHomLocSingleton
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsBaseChangeCokerMatrixMvPolynomial
import Mathlib.Tactic.TypeStar
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.NonemptyBaseChangeGrCubeIso
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsXPowSmulEqZeroOfEqXSubOneSmul
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf

-- Source module: Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsXPowSmulMemSpanOfFiniteQuotStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
theorem _root_.GlobalTheory.T.exists_X_pow_smul_mem_span_of_finite_quotSMulTop : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι), Module.Finite (MvPolynomial ι R) (QuotSMulTop (X i - 1 : MvPolynomial ι R) M) → ∃ T : Finset M, ∀ y : M, ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • y ∈ Submodule.span (MvPolynomial ι R) (T : Set M) := by
  first | exact @GlobalTheory.exists_X_pow_smul_mem_span_of_finite_quot | exact GlobalTheory.exists_X_pow_smul_mem_span_of_finite_quot | (intros; apply GlobalTheory.exists_X_pow_smul_mem_span_of_finite_quot <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsGradedPresentationSaturating

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem exists_graded_presentation_saturating : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (G : Type) [AddCommGroup G] [Module R G] [Module (MvPolynomial ι R) G] [IsScalarTower R (MvPolynomial ι R) G] (𝒢 : ℤ → Submodule R G) [PolyGradedSMul ι 𝒢] [Decomposition 𝒢], (∀ i : ι, Module.FinitePresentation (MvPolynomial ι R) (QuotSMulTop (X i - 1 : MvPolynomial ι R) G)) → ∃ (a b : ℕ) (d : Fin a → ℤ) (e : Fin b → ℤ) (Φ : Matrix (Fin a) (Fin b) (MvPolynomial ι R)) (ψ : ((Fin a → MvPolynomial ι R) ⧸ LinearMap.range Φ.mulVecLin) →ₗ[MvPolynomial ι R] G), (∀ l j, Φ l j ∈ polyGrading ι R (e j - d l)) ∧ IsGradedMap (grQuot (grFree ι R d) (LinearMap.range Φ.mulVecLin)) 𝒢 ψ ∧ ∀ i : ι, (∀ y, ψ y = 0 → ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • y = 0) ∧ (∀ z : G, ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • z ∈ LinearMap.range ψ) := by
  intro ι _ _ R _ G _ _ _ _ 𝒢 _ _ hG
  obtain ⟨a, d, g, hg, hsat⟩ := exists_homogeneous_family_saturating ι R G 𝒢 fun i =>
    GlobalTheory.T.exists_X_pow_smul_mem_span_of_finite_quotSMulTop ι R G 𝒢 i (haveI := hG i; inferInstance)
  set φ := Fintype.linearCombination (MvPolynomial ι R) g with hφdef
  have hφ : IsGradedMap (grFree ι R d) 𝒢 φ := isGradedMap_linearCombination 𝒢 hg
  have hsat' : ∀ (i : ι) (z : G), ∃ k : ℕ,
      (X i : MvPolynomial ι R) ^ k • z ∈ LinearMap.range φ := by
    intro i z
    rw [hφdef, Fintype.range_linearCombination]
    exact hsat i z
  let _ : Decomposition (grSub (grFree ι R d) (LinearMap.ker φ)) :=
    grSubDecomposition _ hφ.isHomogeneous_ker
  obtain ⟨b, e, κ, hκ, hksat⟩ := exists_homogeneous_family_saturating ι R (LinearMap.ker φ)
    (grSub (grFree ι R d) (LinearMap.ker φ)) fun i =>
      GlobalTheory.T.exists_X_pow_smul_mem_span_of_finite_quotSMulTop ι R _ (grSub (grFree ι R d) (LinearMap.ker φ)) i
        (GlobalTheory.finite_quotSMulTop_ker_of_graded ι R _ (grFree ι R d) G 𝒢 φ i hφ inferInstance (hsat' i) (hG i))
  let Φ : Matrix (Fin a) (Fin b) (MvPolynomial ι R) := Matrix.of fun l j => (κ j).1 l
  have hrange : LinearMap.range Φ.mulVecLin =
      (Submodule.span (MvPolynomial ι R) (Set.range κ)).map (LinearMap.ker φ).subtype := by
    rw [Matrix.range_mulVecLin, Submodule.map_span, ← Set.range_comp]
    rfl
  have hle : LinearMap.range Φ.mulVecLin ≤ LinearMap.ker φ := by
    rw [hrange]
    exact Submodule.map_subtype_le _ _
  refine ⟨a, b, d, e, Φ, Submodule.liftQ _ φ hle, fun l j => ?_, hφ.liftQ _ hle,
    fun i => ⟨fun y hy => ?_, fun z => ?_⟩⟩
  · have := mem_grPi.1 (mem_grSub.1 (hκ j)) l
    rw [sub_eq_add_neg]
    exact this
  · obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨k, hk⟩ := hksat i ⟨x, hy⟩
    refine ⟨k, ?_⟩
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hrange]
    exact ⟨_, hk, rfl⟩
  · rw [Submodule.range_liftQ]
    exact hsat' i z

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsHomogeneousRangeMulVecLin

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem isGradedMap_mulVecLin {ι : Type} {R : Type*} [CommRing R] {κ μ : Type*} [Fintype μ]
    {d : κ → ℤ} {e : μ → ℤ} {Φ : Matrix κ μ (MvPolynomial ι R)}
    (h : ∀ l j, Φ l j ∈ polyGrading ι R (e j - d l)) :
    IsGradedMap (grFree ι R e) (grFree ι R d) Φ.mulVecLin := by
  intro n v hv
  refine mem_grPi.2 fun l => ?_
  rw [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, grShift_apply]
  refine Submodule.sum_mem _ fun j _ => ?_
  have := grSMul_mem (polyGrading ι R) (h l j) (mem_grPi.1 hv j)
  rwa [smul_eq_mul, show n + -e j + (e j - d l) = n + -d l by ring] at this

theorem isHomogeneous_range_mulVecLin :
    ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (a b : ℕ) (d : Fin a → ℤ)
      (e : Fin b → ℤ) (Φ : Matrix (Fin a) (Fin b) (MvPolynomial ι R)),
      (∀ l j, Φ l j ∈ polyGrading ι R (e j - d l)) →
        (LinearMap.range Φ.mulVecLin).IsHomogeneous (grFree ι R d) :=
  fun _ _ _ _ _ _ _ _ _ _ h => (isGradedMap_mulVecLin h).isHomogeneous_range

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.NonemptyHomLocSingletonEquivQuotSMulTop

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
open scoped Pointwise

namespace GlobalTheory

theorem nonempty_homLoc_singleton_equiv_quotSMulTop : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι), Nonempty (homLoc ℳ {i} 0 ≃ₗ[R] QuotSMulTop (X i - 1 : MvPolynomial ι R) M) := by
  intro ι _ _ R _ M _ _ _ _ ℳ _ _ i
  obtain ⟨-, h2, h3⟩ := GlobalTheory.X_sub_one_smul_graded ι R M ℳ i
  let K : Submodule (MvPolynomial ι R) M := (X i - 1 : MvPolynomial ι R) • ⊤
  have hK : ∀ y : M, y ∈ K ↔ ∃ w : M, y = (X i - 1 : MvPolynomial ι R) • w := fun y => by
    rw [Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨fun ⟨w, _, h⟩ => ⟨w, h.symm⟩, fun ⟨w, h⟩ => ⟨w, trivial, h.symm⟩⟩
  let φ : ∀ k : ℕ, ℳ (0 + k * (({i} : Finset ι).card : ℤ)) →ₗ[R]
      QuotSMulTop (X i - 1 : MvPolynomial ι R) M :=
    fun k => (K.mkQ.restrictScalars R) ∘ₗ (ℳ _).subtype
  have hφv : ∀ k m, φ k m = Submodule.Quotient.mk (m : M) := fun _ _ => rfl
  have hφ : ∀ (k : ℕ) (m : ℳ (0 + k * (({i} : Finset ι).card : ℤ)))
      (m' : ℳ (0 + (k + 1 : ℕ) * (({i} : Finset ι).card : ℤ))),
      (m' : M) = xProd R {i} • (m : M) → φ (k + 1) m' = φ k m := by
    intro k m m' h
    rw [hφv, hφv, Submodule.Quotient.eq]
    refine (hK _).2 ⟨m, ?_⟩
    rw [h, sub_smul, one_smul, xProd, Finset.prod_singleton]
  refine ⟨LinearEquiv.ofBijective (homLocLift φ hφ) ⟨?_, ?_⟩⟩
  · rw [homLocLift_injective_iff]
    intro k m hm
    rw [hφv, Submodule.Quotient.mk_eq_zero] at hm
    obtain ⟨w, hw⟩ := (hK _).1 hm
    obtain ⟨l, hl⟩ := h2 _ _ w m.2 hw
    exact ⟨l, by rwa [xProd, Finset.prod_singleton]⟩
  · rw [homLocLift_surjective_iff]
    intro t
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ t
    obtain ⟨n₀, hn⟩ := h3 y
    obtain ⟨y', hy', w, hw⟩ := hn (0 + (n₀.toNat : ℕ) * (({i} : Finset ι).card : ℤ))
      (by simp)
    refine ⟨n₀.toNat, ⟨y', hy'⟩, ?_⟩
    rw [hφv, eq_comm, Submodule.Quotient.eq]
    exact (hK _).2 ⟨w, by rw [hw, add_sub_cancel_left]⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.DehomogenisingCompOfSaturating

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits DirectSum TensorProduct

noncomputable section

namespace GlobalTheory

theorem dehomogenising_comp_of_saturating {ι : Type} [LinearOrder ι] [Fintype ι] {R : Type}
    [CommRing R] {N : Type} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
    [IsScalarTower R (MvPolynomial ι R) N] (𝒩 : ℤ → Submodule R N) [PolyGradedSMul ι 𝒩]
    [Decomposition 𝒩] {G : Type} [AddCommGroup G] [Module R G] [Module (MvPolynomial ι R) G]
    (𝒢 : ℤ → Submodule R G) {ψ : N →ₗ[MvPolynomial ι R] G} (hψ : IsGradedMap 𝒩 𝒢 ψ) (i : ι)
    (h₁ : ∀ y, ψ y = 0 → ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial ι R) ^ k • y = 0)
    (h₂ : ∀ z : G, ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial ι R) ^ k • z ∈ LinearMap.range ψ)
    {B : Type} [CommRing B] (π : MvPolynomial ι R →+* B) {P : Type} [AddCommGroup P] [Module B P]
    (ε : G →ₛₗ[π] P) (hπ : π (MvPolynomial.X i) = 1) (hε : Function.Surjective ε)
    (hk : ∀ n, ∀ y ∈ 𝒢 n, ε y = 0 → ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial ι R) ^ k • y = 0) :
    Function.Surjective (ε.comp ψ) ∧
      ∀ y, ε.comp ψ y = 0 ↔ ∃ w : N, y = (MvPolynomial.X i - 1 : MvPolynomial ι R) • w := by
  refine ⟨fun p => ?_, dehomogenising_eq_zero_iff ι R N 𝒩 i B π P (ε.comp ψ) hπ ?_⟩
  · obtain ⟨z, rfl⟩ := hε p
    obtain ⟨k, y, hy⟩ := h₂ z
    refine ⟨y, ?_⟩
    rw [LinearMap.comp_apply, hy, LinearMap.map_smulₛₗ, map_pow, hπ, one_pow, one_smul]
  · intro n y hy h
    obtain ⟨k, hk⟩ := hk n _ (hψ hy) h
    obtain ⟨j, hj⟩ := h₁ _ ((map_smul ψ _ y).trans hk)
    exact ⟨j + k, by rw [pow_add, mul_smul, hj]⟩

theorem exists_noetherian_model_grCube (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type)
    [CommRing R] (G : Type) [AddCommGroup G] [Module R G] [Module (MvPolynomial ι R) G]
    [IsScalarTower R (MvPolynomial ι R) G] (𝒢 : ℤ → Submodule R G) [PolyGradedSMul ι 𝒢]
    [Decomposition 𝒢]
    (H : ∀ i : ι, ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B)
      (π : MvPolynomial ι R →ₐ[R] B) (P : Type) (_ : AddCommGroup P) (_ : Module B P)
      (ε : G →ₛₗ[(π : MvPolynomial ι R →+* B)] P),
      Algebra.Smooth R B ∧ Module.FinitePresentation B P ∧ Module.Projective B P ∧
        Function.Surjective π ∧ π (MvPolynomial.X i) = 1 ∧ Function.Surjective ε ∧
        ∀ n, ∀ y ∈ 𝒢 n, ε y = 0 →
          ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial ι R) ^ k • y = 0) :
    ∃ (R₀ : Subring R) (_ : IsNoetherianRing R₀) (C₀ : Cube.{0} ι R₀)
      (θ : Cube.baseChange R C₀ ⟶ grCube ι 𝒢 0),
      (∀ I : Finset ι, I.Nonempty → Module.Flat R₀ (C₀.obj I)) ∧
        (∀ p, Module.Finite R₀ ((cechComplex C₀).homology p)) ∧
        ∀ I : Finset ι, I.Nonempty → Function.Bijective (θ.app I).hom := by
  obtain ⟨a, b, d, e, Φ, ψ, hΦ, hψ, hsat⟩ :=
    exists_graded_presentation_saturating ι R G 𝒢 fun i => by
      obtain ⟨B, iB, iA, π, P, iP, iM, ε, hs, hfp, -, h⟩ := H i
      exact (finite_quotSMulTop_X_sub_one_of_chart ι R G 𝒢 i B iB iA π P iP iM ε h).2
        inferInstance hfp
  let := grQuotDecomposition (grFree ι R d) (isHomogeneous_range_mulVecLin ι R a b d e Φ hΦ)
  obtain ⟨R₀, Φ₀, hN, hmap, hΦ₀, hflat⟩ :=
    exists_noetherian_subring_homogeneous_matrix_flat_charts ι R a b d e Φ hΦ fun i => by
      obtain ⟨B, iB, iA, π, P, iP, iM, ε, hs, -, hp, hπs, hπ, hε, hk⟩ := H i
      obtain ⟨k₁, k₂⟩ := dehomogenising_comp_of_saturating
        (grQuot (grFree ι R d) (LinearMap.range Φ.mulVecLin)) 𝒢 hψ i (hsat i).1 (hsat i).2
        (π : MvPolynomial ι R →+* B) ε hπ hε hk
      refine ⟨B, iB, iA, π, P, iP, iM, (ε.comp ψ).comp (LinearMap.range Φ.mulVecLin).mkQ, hs, hp,
        hπs, hπ, k₁.comp (Submodule.mkQ_surjective _), fun y => ?_⟩
      rw [LinearMap.comp_apply, k₂]
      constructor
      · rintro ⟨w, hw⟩
        obtain ⟨w', rfl⟩ := Submodule.mkQ_surjective _ w
        rw [← map_smul, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hw
        obtain ⟨v, hv⟩ := hw
        exact ⟨v, w', by rw [← Matrix.mulVecLin_apply, hv, sub_add_cancel]⟩
      · rintro ⟨v, w', rfl⟩
        refine ⟨Submodule.mkQ _ w', ?_⟩
        rw [← map_smul, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
        exact ⟨v, by rw [Matrix.mulVecLin_apply, add_sub_cancel_right]⟩
  let := grQuotDecomposition (grFree ι R₀ d)
    (isHomogeneous_range_mulVecLin ι R₀ a b d e Φ₀ hΦ₀)
  obtain ⟨ψ₀, hbc, hψ₀⟩ := isBaseChange_coker_matrix_mvPolynomial ι R₀ R a b Φ₀ Φ hmap
  obtain ⟨iso⟩ := nonempty_baseChange_grCube_iso ι R₀ R _
    (grQuot (grFree ι R₀ d) (LinearMap.range Φ₀.mulVecLin)) _
    (grQuot (grFree ι R d) (LinearMap.range Φ.mulVecLin)) ψ₀ 0 hbc
    (fun i y => by
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rw [← Submodule.Quotient.mk_smul, hψ₀, hψ₀, ← Submodule.Quotient.mk_smul]
      congr 1
      ext1 l
      simp)
    (by
      rintro j _ ⟨y, hy, rfl⟩
      refine mem_grQuot.2 ⟨_, mem_grPi.2 fun l => ?_, (hψ₀ y).symm⟩
      have := mem_polyGrading_iff.1 (mem_grPi.1 hy l)
      refine mem_polyGrading_iff.2 fun c hc => this c fun h0 => hc ?_
      rw [MvPolynomial.coeff_map, h0, map_zero])
  refine ⟨R₀, hN, grCube ι (grQuot (grFree ι R₀ d) (LinearMap.range Φ₀.mulVecLin)) 0,
    iso.hom ≫ grCubeMap hψ 0, ?_, ?_, ?_⟩
  · rintro I ⟨i, hi⟩
    obtain ⟨f⟩ := nonempty_homLoc_singleton_equiv_quotSMulTop ι R₀ _
      (grQuot (grFree ι R₀ d) (LinearMap.range Φ₀.mulVecLin)) i
    have := hflat i
    exact flat_homLoc_of_flat_homLoc_singleton ι R₀ _ _ i I 0 hi (Module.Flat.of_linearEquiv f)
  · exact finite_grCech_homology ι R₀ _ _ inferInstance 0
  · rintro I ⟨i, hi⟩
    rw [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.coe_comp]
    exact (homLocMap_bijective_of_X hψ hi (hsat i).1 (hsat i).2 0).comp
      (ConcreteCategory.bijective_of_isIso (iso.hom.app I))

end GlobalTheory
end
end
end
