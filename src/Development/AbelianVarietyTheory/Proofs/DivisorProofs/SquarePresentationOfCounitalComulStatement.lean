module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Ideal.Maps
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
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorsDualPointDerivationsAugmentedStatement
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.RingTheory.TensorProduct.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantDerivationOfCounitalComul
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Extension.Presentation.Basic
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusSubalgebraCounitalComulStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerAevalTruncatedPolynomialPresentationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncatedMonomialsLinearIndependentOverConstantsStatement
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationsDualToFamilyOfNilpotentAug

section

@[expose] public section

open scoped TensorProduct

theorem GlobalTheory.derivation_normalise_family : ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A] (ε : A →ₐ[k] k), IsNilpotent (RingHom.ker ε) → ∀ (d : ℕ) (x : Fin d → A) (D : Fin d → Derivation k A A), (∀ i j, ε (D i (x j)) = if i = j then 1 else 0) → ∃ E : Fin d → Derivation k A A, ∀ i j, E i (x j) = if i = j then 1 else 0 := by
  intro k A _ _ _ ε hnil d x D hD
  let M : Matrix (Fin d) (Fin d) A := Matrix.of fun i j => D i (x j)
  have hε : (ε : A →+* k).mapMatrix M = 1 := by
    ext i j
    simp [M, hD, Matrix.one_apply]
  have hdet : ε M.det = 1 := by
    have h := RingHom.map_det (ε : A →+* k) M
    rw [hε, Matrix.det_one] at h
    simpa using h
  have hunit : IsUnit M.det := by
    obtain ⟨n, hn⟩ := hnil
    have hmem : M.det - 1 ∈ RingHom.ker ε := by simp [RingHom.mem_ker, hdet]
    have hN : IsNilpotent (M.det - 1) := ⟨n, by
      have h : (M.det - 1) ^ n ∈ (RingHom.ker ε) ^ n := Ideal.pow_mem_pow hmem n
      rw [hn] at h
      simpa using h⟩
    have h := hN.isUnit_one_add
    simpa using h
  refine ⟨fun i => ∑ l, (M⁻¹ i l) • D l, fun i j => ?_⟩
  have hinv : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hunit
  have h := congrFun (congrFun hinv i) j
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  rw [← h]
  have hev := map_sum (AddMonoidHom.mk' (fun δ : Derivation k A A => δ (x j)) (fun a b => rfl))
    (fun l => M⁻¹ i l • D l) Finset.univ
  simp only [AddMonoidHom.mk'_apply] at hev
  rw [hev]
  simp [M]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationsDualToFamilyOfNilpotentAugStatement

section

@[expose] public section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_derivations_dual_to_family_of_nilpotent_aug : ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A] (ε : A →ₐ[k] k), IsNilpotent (RingHom.ker ε) → ∀ (d : ℕ) (x : Fin d → A) (D : Fin d → Derivation k A A), (∀ i j, ε (D i (x j)) = if i = j then 1 else 0) → ∃ E : Fin d → Derivation k A A, ∀ i j, E i (x j) = if i = j then 1 else 0 := by
  first | exact @GlobalTheory.derivation_normalise_family | exact GlobalTheory.derivation_normalise_family | (intros; apply GlobalTheory.derivation_normalise_family <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantDerivationOfCounitalComulStatement

section

@[expose] public section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_invariant_derivation_of_counital_comul : ∀ (k A : Type) [CommRing k] [CommRing A] [Algebra k A] (ε : A →ₐ[k] k) (Δ : A →ₐ[k] A ⊗[k] A), ((∀ a : A, TensorProduct.lid k A (LinearMap.rTensor A ε.toLinearMap (Δ a)) = a) ∧ (∀ a : A, TensorProduct.rid k A (LinearMap.lTensor A ε.toLinearMap (Δ a)) = a)) → ∀ l : A →ₗ[k] k, (∀ a b, l (a * b) = ε a * l b + ε b * l a) → ∃ D : Derivation k A A, ∀ a, ε (D a) = l a := by
  first | exact @GlobalTheory.invariant_derivation_exists | exact GlobalTheory.invariant_derivation_exists | (intros; apply GlobalTheory.invariant_derivation_exists <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquarePresentationOfTower

section

@[expose] public section

open scoped TensorProduct

namespace GlobalTheory.SquareTower

open MvPolynomial

noncomputable def presOf {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {s : ℕ}
    (φ : MvPolynomial (Fin s) R →ₐ[R] S) (g : Fin s → MvPolynomial (Fin s) R)
    (hs : Function.Surjective φ) (hk : RingHom.ker φ = Ideal.span (Set.range g)) :
    Algebra.Presentation R S (Fin s) (Fin s) :=
  have he : MvPolynomial.aeval (fun i => φ (X i)) = φ := MvPolynomial.algHom_ext (fun i => aeval_X _ _)
  { toGenerators := Algebra.Generators.ofSurjective (fun i => φ (X i)) (by rw [he]; exact hs)
    relation := g
    span_range_relation_eq_ker := by
      rw [Algebra.Generators.ker_eq_ker_aeval_val, ← hk]
      change RingHom.ker φ = RingHom.ker (MvPolynomial.aeval (fun i => φ (X i)))
      rw [he] }

theorem square_of_pres {R T ι σ : Type} [CommRing R] [CommRing T] [Algebra R T] {n : ℕ}
    (P : Algebra.Presentation R T ι σ) (e : Fin n ≃ ι) (f : Fin n ≃ σ) :
    ∃ (s : ℕ) (φ : MvPolynomial (Fin s) R →ₐ[R] T) (g : Fin s → MvPolynomial (Fin s) R),
      Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g) := by
  let E : MvPolynomial (Fin n) R ≃ₐ[R] MvPolynomial ι R := renameEquiv R e
  refine ⟨n, (aeval P.val).comp E.toAlgHom, fun i => E.symm (P.relation (f i)), ?_, ?_⟩
  · intro y
    obtain ⟨x, hx⟩ := P.toGenerators.algebraMap_surjective y
    refine ⟨E.symm x, ?_⟩
    show aeval P.val (E (E.symm x)) = y
    rw [E.apply_symm_apply, ← hx, Algebra.Generators.algebraMap_eq]
    rfl
  · have h1 : Set.range (fun i => E.symm (P.relation (f i))) = E.symm '' Set.range P.relation := by
      rw [← Set.range_comp]
      exact f.surjective.range_comp (⇑E.symm ∘ P.relation)
    rw [h1, ← Ideal.map_span, P.span_range_relation_eq_ker, Algebra.Generators.ker_eq_ker_aeval_val]
    ext x
    rw [RingHom.mem_ker, Ideal.mem_map_of_equiv]
    constructor
    · intro hx
      refine ⟨E x, ?_, by simp⟩
      rw [RingHom.mem_ker]; simpa using hx
    · rintro ⟨y, hy, rfl⟩
      rw [RingHom.mem_ker] at hy
      simpa using hy

theorem tower : ∀ (k B A : Type) [CommRing k] [CommRing B] [CommRing A] [Algebra k B] [Algebra k A] [Algebra B A] [IsScalarTower k B A], (∃ (s : ℕ) (φ : MvPolynomial (Fin s) k →ₐ[k] B) (g : Fin s → MvPolynomial (Fin s) k), Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) → (∃ (s : ℕ) (φ : MvPolynomial (Fin s) B →ₐ[B] A) (g : Fin s → MvPolynomial (Fin s) B), Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) → (∃ (s : ℕ) (φ : MvPolynomial (Fin s) k →ₐ[k] A) (g : Fin s → MvPolynomial (Fin s) k), Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) := by
  intro k B A _ _ _ _ _ _ _
  rintro ⟨t, φ, g, hφ, hg⟩ ⟨d, ψ, h, hψ, hh⟩
  let P := presOf φ g hφ hg
  let Q := presOf ψ h hψ hh
  exact square_of_pres (Q.comp P) finSumFinEquiv.symm finSumFinEquiv.symm

end GlobalTheory.SquareTower
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquarePresentationOfTowerStatement

section

@[expose] public section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_square_presentation_of_tower : ∀ (k B A : Type) [CommRing k] [CommRing B] [CommRing A] [Algebra k B] [Algebra k A] [Algebra B A] [IsScalarTower k B A], (∃ (s : ℕ) (φ : MvPolynomial (Fin s) k →ₐ[k] B) (g : Fin s → MvPolynomial (Fin s) k), Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) → (∃ (s : ℕ) (φ : MvPolynomial (Fin s) B →ₐ[B] A) (g : Fin s → MvPolynomial (Fin s) B), Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) → (∃ (s : ℕ) (φ : MvPolynomial (Fin s) k →ₐ[k] A) (g : Fin s → MvPolynomial (Fin s) k), Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) := by
  first | exact @GlobalTheory.SquareTower.tower | exact GlobalTheory.SquareTower.tower | (intros; apply GlobalTheory.SquareTower.tower <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquarePresentationOfCounitalComul

section

@[expose] public section

open scoped TensorProduct

namespace GlobalTheory

theorem square_presentation_counital_comul_of_finrank (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    [CharP k p] [PerfectRing k p] (n : ℕ) :
    ∀ (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A] (ε : A →ₐ[k] k)
      (Δ : A →ₐ[k] A ⊗[k] A), Module.finrank k A = n →
      ((∀ a : A, TensorProduct.lid k A (LinearMap.rTensor A ε.toLinearMap (Δ a)) = a) ∧
        (∀ a : A, TensorProduct.rid k A (LinearMap.lTensor A ε.toLinearMap (Δ a)) = a)) →
      IsNilpotent (RingHom.ker ε) →
      (∃ (s : ℕ) (φ : MvPolynomial (Fin s) k →ₐ[k] A) (g : Fin s → MvPolynomial (Fin s) k),
        Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A _ _ _ ε Δ hn hΔ hε
  obtain ⟨d, x, l, hl, hlx, hadj⟩ := GlobalTheory.T.exists_generators_dual_point_derivations_augmented k A ε hε
  choose D hD using fun i => GlobalTheory.T.exists_invariant_derivation_of_counital_comul k A ε Δ hΔ (l i) (hl i)
  obtain ⟨E, hE⟩ := GlobalTheory.T.exists_derivations_dual_to_family_of_nilpotent_aug k A ε hε d x D (fun i j => by rw [hD, hlx])
  have hnt : Nontrivial A := ε.toRingHom.domain_nontrivial
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    refine ⟨0, MvPolynomial.aeval x, fun _ => 0, ?_, ?_⟩
    · rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval, hadj]
    · rw [Set.range_eq_empty, Ideal.span_empty, ← RingHom.injective_iff_ker_eq_bot]
      intro f g h
      rw [MvPolynomial.eq_C_of_isEmpty f, MvPolynomial.eq_C_of_isEmpty g] at h ⊢
      simp only [MvPolynomial.aeval_C] at h
      rw [(algebraMap k A).injective h]
  · obtain ⟨B, hB, Δ', hΔ'⟩ := GlobalTheory.T.frobeniusSubalgebra_counital_comul p k A ε Δ hΔ
    have hp : (p : A) = 0 := by
      rw [← map_natCast (algebraMap k A), CharP.cast_eq_zero, map_zero]
    have hEB : ∀ i, ∀ b ∈ B, E i b = 0 := by
      intro i b hb
      obtain ⟨c, rfl⟩ := (hB b).1 hb
      rw [Derivation.leibniz_pow, nsmul_eq_mul, hp, zero_mul]
    have hBtop : B ≠ ⊤ := by
      intro h
      have h1 := hE ⟨0, hd⟩ ⟨0, hd⟩
      rw [hEB _ _ (h ▸ Algebra.mem_top), if_pos rfl] at h1
      exact zero_ne_one h1
    have hlt : Module.finrank k B < n := by
      rw [← hn]
      have : (Subalgebra.toSubmodule B) ≠ ⊤ := by
        intro h
        apply hBtop
        rw [← Algebra.toSubmodule_eq_top]
        exact h
      exact Submodule.finrank_lt this
    have hfin : Module.Finite k B :=
      Module.Finite.of_injective B.val.toLinearMap Subtype.val_injective
    have hε' : IsNilpotent (RingHom.ker (ε.comp B.val)) := by
      obtain ⟨m, hm⟩ := hε
      refine ⟨m, ?_⟩
      have h1 : (RingHom.ker (ε.comp B.val)) = Ideal.comap B.val (RingHom.ker ε) := by
        ext b; simp [RingHom.mem_ker, Ideal.mem_comap]
      rw [h1, Ideal.zero_eq_bot, eq_bot_iff]
      refine (Ideal.le_comap_pow _ m).trans ?_
      rw [hm, Ideal.zero_eq_bot]
      intro b hb
      rw [Ideal.mem_comap, Ideal.mem_bot] at hb
      rw [Ideal.mem_bot]
      exact Subtype.ext hb
    refine GlobalTheory.T.exists_square_presentation_of_tower k B A (ih _ hlt B (ε.comp B.val) Δ' rfl hΔ' hε') ?_
    refine ⟨d, MvPolynomial.aeval x, _, ?_,
      GlobalTheory.T.ker_aeval_truncatedPolynomial_presentation p (Fact.out : p.Prime).pos B A d x
        (fun i => ⟨x i ^ p, (hB _).2 ⟨x i, rfl⟩⟩) (fun i => rfl)
        (GlobalTheory.T.truncatedMonomials_linearIndependent_over_constants p k A d x E hE B hEB)⟩
    rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval, eq_top_iff]
    intro a _
    have ha : a ∈ Algebra.adjoin k (Set.range x) := hadj ▸ Algebra.mem_top
    have hle : Algebra.adjoin k (Set.range x) ≤
        (Algebra.adjoin B (Set.range x)).restrictScalars k :=
      Algebra.adjoin_le Algebra.subset_adjoin
    exact hle ha

theorem square_presentation_of_counital_comul : ∀ (p : ℕ) [Fact p.Prime] (k A : Type) [Field k] [CommRing A] [Algebra k A] [CharP k p] [PerfectRing k p] [Module.Finite k A] (ε : A →ₐ[k] k) (Δ : A →ₐ[k] A ⊗[k] A), ((∀ a : A, TensorProduct.lid k A (LinearMap.rTensor A ε.toLinearMap (Δ a)) = a) ∧ (∀ a : A, TensorProduct.rid k A (LinearMap.lTensor A ε.toLinearMap (Δ a)) = a)) → IsNilpotent (RingHom.ker ε) → (∃ (s : ℕ) (φ : MvPolynomial (Fin s) k →ₐ[k] A) (g : Fin s → MvPolynomial (Fin s) k), Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) := by
  intro p _ k A _ _ _ _ _ _ ε Δ h hε
  exact square_presentation_counital_comul_of_finrank p k _ A ε Δ rfl h hε

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquarePresentationOfCounitalComulStatement

section

@[expose] public section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_square_presentation_of_counit_isNilpotent_ker : ∀ (p : ℕ) [Fact p.Prime] (k A : Type) [Field k] [CommRing A] [Algebra k A] [CharP k p] [PerfectRing k p] [Module.Finite k A] (ε : A →ₐ[k] k) (Δ : A →ₐ[k] A ⊗[k] A), ((∀ a : A, TensorProduct.lid k A (LinearMap.rTensor A ε.toLinearMap (Δ a)) = a) ∧ (∀ a : A, TensorProduct.rid k A (LinearMap.lTensor A ε.toLinearMap (Δ a)) = a)) → IsNilpotent (RingHom.ker ε) → (∃ (s : ℕ) (φ : MvPolynomial (Fin s) k →ₐ[k] A) (g : Fin s → MvPolynomial (Fin s) k), Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) := by
  first | exact @GlobalTheory.square_presentation_of_counital_comul | exact GlobalTheory.square_presentation_of_counital_comul | (intros; apply GlobalTheory.square_presentation_of_counital_comul <;> assumption)
end
end
