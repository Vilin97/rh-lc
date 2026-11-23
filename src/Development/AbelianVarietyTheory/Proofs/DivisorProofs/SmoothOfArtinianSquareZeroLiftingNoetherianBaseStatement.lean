module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSmoothOfDefectZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationExtendingKernelFormOfLiftingStatement
public import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.RingTheory.TotallySplit

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveCotangentComplexBaseChangeOfFormsExtend

section

@[expose] public section

open TensorProduct KaehlerDifferential

namespace GlobalTheory

theorem injective_cotangentComplexBaseChange_of_forms_extend : ∀ (A P R K : Type) [CommRing A] [CommRing P] [CommRing R] [Field K] [Algebra A P] [Algebra A R] [Algebra P R] [IsScalarTower A P R] [Algebra R K] [Algebra P K] [IsScalarTower P R K] [Algebra A K] [IsScalarTower A P K], (∀ ℓ : RingHom.ker (algebraMap P R) →ₗ[P] K, ∃ D : Derivation A P K, ∀ i : RingHom.ker (algebraMap P R), D i = ℓ i) → Function.Injective (KaehlerDifferential.cotangentComplexBaseChange A R P K) := by
  intro A P R K _ _ _ _ _ _ _ _ _ _ _ _ _ hext
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro z hz
  refine (Module.forall_dual_apply_eq_zero_iff K z).1 fun φ => ?_
  let ℓ : RingHom.ker (algebraMap P R) →ₗ[P] K :=
    (φ.restrictScalars P) ∘ₗ (TensorProduct.mk P K (RingHom.ker (algebraMap P R)) 1)
  obtain ⟨D, hD⟩ := hext ℓ
  let Λ : K ⊗[P] Ω[P⁄A] →ₗ[K] K := LinearMap.liftBaseChange K D.liftKaehlerDifferential
  have key : Λ ∘ₗ cotangentComplexBaseChange A R P K = φ := by
    ext i
    simp [Λ, cotangentComplexBaseChange_tmul, kerToTensor_apply, hD, ℓ]
  have h2 := congrArg (fun f => f z) key
  simpa [hz] using h2.symm

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveCotangentComplexBaseChangeOfFormsExtendStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.injective_cotangentComplexBaseChange_of_forms_extend' : ∀ (A P R K : Type) [CommRing A] [CommRing P] [CommRing R] [Field K] [Algebra A P] [Algebra A R] [Algebra P R] [IsScalarTower A P R] [Algebra R K] [Algebra P K] [IsScalarTower P R K] [Algebra A K] [IsScalarTower A P K], (∀ ℓ : RingHom.ker (algebraMap P R) →ₗ[P] K, ∃ D : Derivation A P K, ∀ i : RingHom.ker (algebraMap P R), D i = ℓ i) → Function.Injective (KaehlerDifferential.cotangentComplexBaseChange A R P K) := by
  first | exact @GlobalTheory.injective_cotangentComplexBaseChange_of_forms_extend | exact GlobalTheory.injective_cotangentComplexBaseChange_of_forms_extend | (intros; apply GlobalTheory.injective_cotangentComplexBaseChange_of_forms_extend <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftRingHomAffineOpenOfArtinianSchemeLift

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem lift_ringHom_of_scheme_lift : ∀ (B : Type) [CommRing B] (X : Scheme.{0}) (s : X ⟶ Sp B), (∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (t : Sp C ⟶ Sp B) (x₀ : Sp C₀ ⟶ X), x₀ ≫ s = spMap π ≫ t → ∃ x : Sp C ⟶ X, spMap π ≫ x = x₀ ∧ x ≫ s = t) → ∀ (U : (Sp B).Opens), IsAffineOpen U → ∀ (V : X.Opens), IsAffineOpen V → ∀ (e : V ≤ s ⁻¹ᵁ U), (∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (β : Γ(Sp B, U) →+* C) (φ₀ : Γ(X, V) →+* C₀), φ₀.comp ((s.appLE U V e).hom) = π.comp β → ∃ φ : Γ(X, V) →+* C, π.comp φ = φ₀ ∧ φ.comp ((s.appLE U V e).hom) = β) := by
  intro B _ X s hlift U hU V hV e C C₀ _ _ _ _ π hπ hk β φ₀ hcomp

  haveI : Nontrivial C₀ := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have h1 : (1 : C) ∈ RingHom.ker π := by
      rw [RingHom.mem_ker]; exact Subsingleton.elim _ _
    have h2 : (1 : C) ∈ RingHom.ker π ^ 2 := by
      have := Ideal.mul_mem_mul h1 h1
      simpa [pow_two] using this
    rw [hk, Ideal.mem_bot] at h2
    exact one_ne_zero h2
  have hsub : ∀ a b : PrimeSpectrum C, a = b := by
    intro a b
    ext1
    rw [IsLocalRing.eq_maximalIdeal (IsArtinianRing.isMaximal_of_isPrime a.asIdeal),
      IsLocalRing.eq_maximalIdeal (IsArtinianRing.isMaximal_of_isPrime b.asIdeal)]
  have hA := IsAffineOpen.SpecMap_appLE_fromSpec s hU hV e
  have hx₀ : (Spec.map (CommRingCat.ofHom φ₀) ≫ hV.fromSpec) ≫ s =
      spMap π ≫ (Spec.map (CommRingCat.ofHom β) ≫ hU.fromSpec) := by
    rw [Category.assoc, ← hA, ← Category.assoc, ← Spec.map_comp, ← Category.assoc, spMap,
      ← Spec.map_comp]
    congr 2
    ext1
    exact hcomp
  obtain ⟨x, hx1, hx2⟩ := hlift C C₀ π hπ hk _ _ hx₀
  have hrange : Set.range x ⊆ Set.range hV.fromSpec := by
    rintro _ ⟨p, rfl⟩
    obtain ⟨q⟩ := (inferInstance : Nonempty (PrimeSpectrum C₀))
    have hp : p = (spMap π) q := hsub _ _
    refine ⟨(Spec.map (CommRingCat.ofHom φ₀)) q, ?_⟩
    rw [hp]
    have := congrArg (fun f : Sp C₀ ⟶ X => f q) hx1
    first
      | exact this.symm
      | (rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at this; exact this.symm)
      | (simp only [Scheme.Hom.comp_base, TopCat.comp_app] at this; exact this.symm)
  have hyx : IsOpenImmersion.lift hV.fromSpec x hrange ≫ hV.fromSpec = x :=
    IsOpenImmersion.lift_fac _ _ _
  obtain ⟨φ, hφ⟩ : ∃ φ, Spec.map φ = IsOpenImmersion.lift hV.fromSpec x hrange :=
    ⟨_, Spec.map_preimage _⟩
  rw [← hφ] at hyx
  refine ⟨φ.hom, ?_, ?_⟩
  · have h3 : Spec.map (CommRingCat.ofHom (π.comp φ.hom)) ≫ hV.fromSpec =
        Spec.map (CommRingCat.ofHom φ₀) ≫ hV.fromSpec := by
      rw [← hx1, ← hyx, spMap, ← Category.assoc, ← Spec.map_comp]
      rfl
    have h4 := Spec.map_injective ((cancel_mono hV.fromSpec).1 h3)
    exact congrArg CommRingCat.Hom.hom h4
  · have h3 : Spec.map (CommRingCat.ofHom (φ.hom.comp (s.appLE U V e).hom)) ≫
        hU.fromSpec = Spec.map (CommRingCat.ofHom β) ≫ hU.fromSpec := by
      rw [← hx2, ← hyx, Category.assoc, ← hA, ← Category.assoc,
        ← Spec.map_comp]
      rfl
    have h4 := Spec.map_injective ((cancel_mono hU.fromSpec).1 h3)
    exact congrArg CommRingCat.Hom.hom h4

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftRingHomAffineOpenOfArtinianSchemeLiftStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.lift_ringHom_affine_open_of_artinian_scheme_lift : ∀ (B : Type) [CommRing B] (X : Scheme.{0}) (s : X ⟶ Sp B), (∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (t : Sp C ⟶ Sp B) (x₀ : Sp C₀ ⟶ X), x₀ ≫ s = spMap π ≫ t → ∃ x : Sp C ⟶ X, spMap π ≫ x = x₀ ∧ x ≫ s = t) → ∀ (U : (Sp B).Opens), IsAffineOpen U → ∀ (V : X.Opens), IsAffineOpen V → ∀ (e : V ≤ s ⁻¹ᵁ U), (∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (β : Γ(Sp B, U) →+* C) (φ₀ : Γ(X, V) →+* C₀), φ₀.comp ((s.appLE U V e).hom) = π.comp β → ∃ φ : Γ(X, V) →+* C, π.comp φ = φ₀ ∧ φ.comp ((s.appLE U V e).hom) = β) := by
  first | exact @GlobalTheory.lift_ringHom_of_scheme_lift | exact GlobalTheory.lift_ringHom_of_scheme_lift | (intros; apply GlobalTheory.lift_ringHom_of_scheme_lift <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfArtinianSquareZeroLiftingNoetherianBase

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SmoothCrit

theorem smooth_of_lift (A R : Type) [CommRing A] [IsNoetherianRing A] [CommRing R] (g : A →+* R) (hg : g.FiniteType)
    (H : (∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (β : A →+* C) (φ₀ : R →+* C₀), φ₀.comp (g) = π.comp β → ∃ φ : R →+* C, π.comp φ = φ₀ ∧ φ.comp (g) = β)) : g.Smooth := by
  algebraize [g]
  have : Algebra.FinitePresentation A R := Algebra.FinitePresentation.of_finiteType.mp hg
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp (inferInstance : Algebra.FiniteType A R)
  letI := f.toRingHom.toAlgebra
  haveI : IsScalarTower A (MvPolynomial (Fin n) A) R := IsScalarTower.of_algebraMap_eq fun a => (f.commutes a).symm
  have hs : Function.Surjective (algebraMap (MvPolynomial (Fin n) A) R) := hf
  have hmax : ∀ (m : Ideal R) [m.IsMaximal], Algebra.IsSmoothAt A m := by
    intro m _
    letI : Field (R ⧸ m) := Ideal.Quotient.field m
    have key := GlobalTheory.T.injective_cotangentComplexBaseChange_of_forms_extend' A (MvPolynomial (Fin n) A) R (R ⧸ m) fun ℓ => GlobalTheory.T.exists_derivation_extending_kernel_form_of_lifting A (MvPolynomial (Fin n) A) R (R ⧸ m) hs Ideal.Quotient.mk_surjective H ℓ
    exact (GlobalTheory.SS.DefectZero.isSmoothAt_iff_injective A (MvPolynomial (Fin n) A) R (R ⧸ m) hs m
      (Ideal.mk_ker).symm).mpr key
  have hU : Algebra.smoothLocus A R = Set.univ := by
    refine Set.eq_univ_iff_forall.mpr fun q => ?_
    obtain ⟨m, hm, hqm⟩ := Ideal.exists_le_maximal q.asIdeal q.2.ne_top
    have hm' : (⟨m, hm.isPrime⟩ : PrimeSpectrum R) ∈ Algebra.smoothLocus A R := @hmax m hm
    exact ((PrimeSpectrum.le_iff_specializes q ⟨m, hm.isPrime⟩).mp hqm).mem_open Algebra.isOpen_smoothLocus hm'
  exact ⟨Algebra.smoothLocus_eq_univ_iff.mp hU, inferInstance⟩

theorem smooth_of_artinian_lift : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (X : Scheme.{0}) (s : X ⟶ Sp B), LocallyOfFiniteType s → (∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (t : Sp C ⟶ Sp B) (x₀ : Sp C₀ ⟶ X), x₀ ≫ s = spMap π ≫ t → ∃ x : Sp C ⟶ X, spMap π ≫ x = x₀ ∧ x ≫ s = t) → Smooth s := by
  intro B _ _ X s hs H
  constructor
  intro U hU V hV e
  haveI : IsNoetherianRing Γ(Sp B, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  exact smooth_of_lift _ _ _ (HasRingHomProperty.appLE @LocallyOfFiniteType s hs ⟨U, hU⟩ ⟨V, hV⟩ e) (GlobalTheory.T.lift_ringHom_affine_open_of_artinian_scheme_lift B X s H U hU V hV e)

end GlobalTheory.SmoothCrit
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfArtinianSquareZeroLiftingNoetherianBaseStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.smooth_of_artinian_squareZero_lifting_noetherian_base : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (X : Scheme.{0}) (s : X ⟶ Sp B), LocallyOfFiniteType s → (∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (t : Sp C ⟶ Sp B) (x₀ : Sp C₀ ⟶ X), x₀ ≫ s = spMap π ≫ t → ∃ x : Sp C ⟶ X, spMap π ≫ x = x₀ ∧ x ≫ s = t) → Smooth s := by
  first | exact @GlobalTheory.SmoothCrit.smooth_of_artinian_lift | exact GlobalTheory.SmoothCrit.smooth_of_artinian_lift | (intros; apply GlobalTheory.SmoothCrit.smooth_of_artinian_lift <;> assumption)
end
end
