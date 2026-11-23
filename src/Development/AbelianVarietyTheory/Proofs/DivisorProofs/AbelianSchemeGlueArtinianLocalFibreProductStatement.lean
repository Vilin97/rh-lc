module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGluedCommGroupSchemeArtinFibreProduct
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FerrandGlueFlatArtinianFibreProductStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperGeometricallyConnectedSmoothNilpotentLif
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Tactic.Linter.HaveILetI
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfIsPullbackOfSurjectiveOfFlat

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGluedCommGroupSchemeArtinFibreProductStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_glued_commGroupScheme_artinFibreProduct : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (A₁ : Over (Spec R₁)) [GrpObj A₁] (A₂ : Over (Spec R₂)) [GrpObj A₂] (A₀ : Over (Spec R₀)) [GrpObj A₀] (ψ₁ : A₀.left ⟶ A₁.left) (ψ₂ : A₀.left ⟶ A₂.left), IsCommMonObj A₁ → IsCommMonObj A₂ → IsGrpPullback A₀ A₁ (Spec.map g₁) ψ₁ → IsGrpPullback A₀ A₂ (Spec.map g₂) ψ₂ → ∀ (Y : Over (Spec P)) (j₁ : A₁.left ⟶ Y.left) (j₂ : A₂.left ⟶ Y.left), IsPullback j₁ A₁.hom Y.hom (Spec.map f₁) → IsPullback j₂ A₂.hom Y.hom (Spec.map f₂) → Flat Y.hom → IsPushout ψ₁ ψ₂ j₁ j₂ → ∃ _ : GrpObj Y, IsCommMonObj Y ∧ IsGrpPullback A₁ Y (Spec.map f₁) j₁ ∧ IsGrpPullback A₂ Y (Spec.map f₂) j₂ := by
  first | exact @GlobalTheory.GlueGrpLaw.exists_glued_grp | exact GlobalTheory.GlueGrpLaw.exists_glued_grp | (intros; apply GlobalTheory.GlueGrpLaw.exists_glued_grp <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyOfFinitePresentationOfNilpotentThickening

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

open scoped TensorProduct

namespace GlobalTheory

open Algebra in
theorem finiteType_of_finiteType_quotient_map_nilpotent {P A : Type} [CommRing P] [CommRing A]
    [Algebra P A] (I : Ideal P) (hI : IsNilpotent I)
    [h : Algebra.FiniteType P (A ⧸ I.map (algebraMap P A))] : Algebra.FiniteType P A := by
  set J := I.map (algebraMap P A)
  obtain ⟨s, hs⟩ := h.out
  classical
  let t : Finset A := s.image (fun x => Quotient.out x)
  have hmk : (Ideal.Quotient.mkₐ P J) '' (t : Set A) = (s : Set (A ⧸ J)) := by
    ext x; simp [t]
  let C := Algebra.adjoin P (t : Set A)
  have key : ∀ b : A, ∃ c ∈ C, b - c ∈ J := by
    intro b
    have hb : Ideal.Quotient.mkₐ P J b ∈ (C.map (Ideal.Quotient.mkₐ P J)) := by
      rw [AlgHom.map_adjoin, hmk, hs]; trivial
    obtain ⟨c, hc, hcb⟩ := hb
    exact ⟨c, hc, Ideal.Quotient.eq.mp (by simpa using hcb.symm)⟩
  have base : (⊤ : Submodule P A) ≤ Subalgebra.toSubmodule C ⊔ I • ⊤ := by
    intro b _
    obtain ⟨c, hc, hbc⟩ := key b
    have : b - c ∈ I • (⊤ : Submodule P A) := by
      rw [Ideal.smul_top_eq_map]; exact hbc
    have := Submodule.add_mem_sup (show c ∈ Subalgebra.toSubmodule C from hc) this
    simpa using this
  have step : ∀ n : ℕ, (⊤ : Submodule P A) ≤ Subalgebra.toSubmodule C ⊔ (I ^ n) • ⊤ := by
    intro n
    induction n with
    | zero =>
      intro b _
      exact Submodule.mem_sup_right (by rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]; trivial)
    | succ n ih =>
      refine ih.trans (sup_le le_sup_left ?_)
      calc (I ^ n) • (⊤ : Submodule P A) ≤ (I ^ n) • (Subalgebra.toSubmodule C ⊔ I • ⊤) :=
            Submodule.smul_mono le_rfl base
        _ = (I ^ n) • Subalgebra.toSubmodule C ⊔ (I ^ n) • (I • ⊤) := Submodule.smul_sup _ _ _
        _ ≤ Subalgebra.toSubmodule C ⊔ (I ^ (n + 1)) • ⊤ := by
            rw [pow_succ, Submodule.mul_smul]
            exact sup_le_sup_right Submodule.smul_le_right _
  obtain ⟨N, hN⟩ := hI
  have hC : Subalgebra.toSubmodule C = ⊤ := by
    have := step N
    rw [hN, Submodule.zero_eq_bot, Submodule.bot_smul, sup_bot_eq] at this
    exact top_le_iff.mp this
  exact ⟨⟨t, Algebra.toSubmodule_eq_top.mp hC⟩⟩

theorem finiteType_of_finiteType_tensor_nilpotent {P A R : Type} [CommRing P] [CommRing A]
    [CommRing R] [Algebra P A] [Algebra P R] (hs : Function.Surjective (algebraMap P R))
    (hn : IsNilpotent (RingHom.ker (algebraMap P R)))
    (h : (Algebra.TensorProduct.includeRight : R →ₐ[P] A ⊗[P] R).toRingHom.FiniteType) :
    Algebra.FiniteType P A := by
  have h1 : Algebra.FiniteType P (A ⊗[P] R) := by
    rw [← RingHom.finiteType_algebraMap,
      ← (Algebra.TensorProduct.includeRight : R →ₐ[P] A ⊗[P] R).comp_algebraMap]
    exact h.comp (RingHom.FiniteType.of_surjective _ hs)
  let f : P →ₐ[P] R := Algebra.ofId P R
  have hf : Function.Surjective f := hs
  let I : Ideal P := RingHom.ker f
  let e1 : (A ⧸ I.map (algebraMap P A)) ≃ₐ[P] A ⊗[P] (P ⧸ I) :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A I).restrictScalars P
  let e2 : A ⊗[P] (P ⧸ I) ≃ₐ[P] A ⊗[P] R :=
    Algebra.TensorProduct.congr AlgEquiv.refl (Ideal.quotientKerAlgEquivOfSurjective hf)
  have h2 : Algebra.FiniteType P (A ⧸ I.map (algebraMap P A)) := h1.equiv (e1.trans e2).symm
  exact finiteType_of_finiteType_quotient_map_nilpotent I hn

theorem locallyOfFinitePresentation_specMap_of_isPullback_nilpotent {P R₁ A : CommRingCat.{0}}
    (f₁ : P ⟶ R₁) (hs : Function.Surjective f₁) (hn : IsNilpotent (RingHom.ker f₁.hom))
    [IsNoetherianRing P] (φ : P ⟶ A) {W : Scheme.{0}} (fst : W ⟶ Spec A) (snd : W ⟶ Spec R₁)
    (hsq : IsPullback fst snd (Spec.map φ) (Spec.map f₁)) (hsnd : LocallyOfFinitePresentation snd) :
    LocallyOfFinitePresentation (Spec.map φ) := by
  have h1 : LocallyOfFinitePresentation (pullback.snd (Spec.map φ) (Spec.map f₁)) := by
    have e : pullback.snd (Spec.map φ) (Spec.map f₁) = hsq.isoPullback.inv ≫ snd := by
      rw [Iso.eq_inv_comp, hsq.isoPullback_hom_snd]
    rw [e]
    exact MorphismProperty.comp_mem _ _ _ (locallyOfFinitePresentation_of_isOpenImmersion _) hsnd
  letI := φ.hom.toAlgebra
  letI := f₁.hom.toAlgebra
  have hT : LocallyOfFinitePresentation ((pullbackSpecIso P A R₁).inv ≫ pullback.snd _ _) :=
    MorphismProperty.comp_mem _ _ _ (locallyOfFinitePresentation_of_isOpenImmersion _) h1
  rw [pullbackSpecIso_inv_snd, LocallyOfFinitePresentation.SpecMap_iff] at hT
  rw [LocallyOfFinitePresentation.SpecMap_iff, ← RingHom.FinitePresentation.of_finiteType]
  exact finiteType_of_finiteType_tensor_nilpotent (A := A) hs hn (RingHom.FiniteType.of_finitePresentation hT)

theorem locallyOfFinitePresentation_of_nilpotent_thickening :
    ∀ (P R₁ : CommRingCat.{0}) (f₁ : P ⟶ R₁), Function.Surjective f₁ → IsNilpotent (RingHom.ker f₁.hom) → IsNoetherianRing P → ∀ (Y : Over (Spec P)) (Y₁ : Over (Spec R₁)) (j₁ : Y₁.left ⟶ Y.left), IsPullback j₁ Y₁.hom Y.hom (Spec.map f₁) → LocallyOfFinitePresentation Y₁.hom → LocallyOfFinitePresentation Y.hom := by
  intro P R₁ f₁ hs hn hP Y Y₁ j₁ hpb hY₁
  haveI : IsZariskiLocalAtSource @LocallyOfFinitePresentation.{0} :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @LocallyOfFinitePresentation.{0})
    Y.left.affineOpenCover.openCover]
  intro i
  haveI : IsOpenImmersion (Y.left.affineOpenCover.f i) :=
    inferInstanceAs (IsOpenImmersion (Y.left.affineOpenCover.openCover.f i))
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (Y.left.affineOpenCover.f i ≫ Y.hom)
  have hsq : IsPullback (pullback.fst (Y.left.affineOpenCover.f i) j₁)
      (pullback.snd (Y.left.affineOpenCover.f i) j₁ ≫ Y₁.hom) (Spec.map φ) (Spec.map f₁) := by
    rw [hφ]; exact (IsPullback.of_hasPullback (Y.left.affineOpenCover.f i) j₁).paste_vert hpb
  have hfin := GlobalTheory.locallyOfFinitePresentation_specMap_of_isPullback_nilpotent f₁ hs hn φ _ _ hsq
    (MorphismProperty.comp_mem _ _ _ (locallyOfFinitePresentation_of_isOpenImmersion _) hY₁)
  rw [hφ] at hfin
  exact hfin

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyOfFinitePresentationOfNilpotentThickeningStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.locallyOfFinitePresentation_of_nilpotent_thickening_noetherian : ∀ (P R₁ : CommRingCat.{0}) (f₁ : P ⟶ R₁), Function.Surjective f₁ → IsNilpotent (RingHom.ker f₁.hom) → IsNoetherianRing P → ∀ (Y : Over (Spec P)) (Y₁ : Over (Spec R₁)) (j₁ : Y₁.left ⟶ Y.left), IsPullback j₁ Y₁.hom Y.hom (Spec.map f₁) → LocallyOfFinitePresentation Y₁.hom → LocallyOfFinitePresentation Y.hom := by
  first | exact @GlobalTheory.locallyOfFinitePresentation_of_nilpotent_thickening | exact GlobalTheory.locallyOfFinitePresentation_of_nilpotent_thickening | (intros; apply GlobalTheory.locallyOfFinitePresentation_of_nilpotent_thickening <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeGlueArtinianLocalFibreProduct

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.GlueAb

theorem isNilpotent_ker {P R : CommRingCat.{0}} (f : P ⟶ R) [IsLocalRing P] [IsArtinianRing P]
    [Nontrivial R] : IsNilpotent (RingHom.ker f.hom) := by
  have h : IsNilpotent (IsLocalRing.maximalIdeal P) := by
    have := IsArtinianRing.isNilpotent_jacobson_bot (R := P)
    rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at this
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  have := Ideal.pow_right_mono (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top f.hom)) n
  rw [hn] at this
  exact le_antisymm this bot_le

theorem surjective_spec_map {P R : CommRingCat.{0}} (f : P ⟶ R) [IsLocalRing P] [IsArtinianRing P]
    [Nontrivial R] : Surjective (Spec.map f) := by
  constructor
  intro x
  obtain ⟨y⟩ : Nonempty (PrimeSpectrum R) := inferInstance
  refine ⟨y, ?_⟩
  have : Subsingleton (PrimeSpectrum P) := ⟨fun a b => PrimeSpectrum.ext <| by
    have ha := IsArtinianRing.isMaximal_of_isPrime a.asIdeal
    have hb := IsArtinianRing.isMaximal_of_isPrime b.asIdeal
    rw [IsLocalRing.eq_maximalIdeal ha, IsLocalRing.eq_maximalIdeal hb]⟩
  exact Subsingleton.elim (α := PrimeSpectrum P) _ _

theorem pullback_elem {P R₁ R₂ R₀ : CommRingCat.{0}} {f₁ : P ⟶ R₁} {f₂ : P ⟶ R₂} {g₁ : R₁ ⟶ R₀}
    {g₂ : R₂ ⟶ R₀} (h : IsPullback f₁ f₂ g₁ g₂) :
    (∀ x y : P, f₁ x = f₁ y → f₂ x = f₂ y → x = y) ∧
      (Function.Surjective g₂ → Function.Surjective f₁) := by
  have h' := (Types.isPullback_iff _ _ _ _).mp (h.map (forget CommRingCat))
  refine ⟨fun x y h1 h2 => h'.2.1 x y ⟨h1, h2⟩, fun hg r => ?_⟩
  obtain ⟨s, hs⟩ := hg (g₁ r)
  obtain ⟨p, hp, -⟩ := h'.2.2 r s hs.symm
  exact ⟨p, hp⟩

end GlobalTheory.GlueAb

namespace GlobalTheory.GlueAb

theorem main_of_nontrivial (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀)
    (g₂ : R₂ ⟶ R₀) (hpb : IsPullback f₁ f₂ g₁ g₂) (hl : IsLocalRing P) (ha : IsArtinianRing P)
    (hg₁ : Function.Surjective g₁) (hg₂ : Function.Surjective g₂) (hR : Nontrivial R₁)
    (A₁ : Over (Spec R₁)) [GrpObj A₁] (A₂ : Over (Spec R₂)) [GrpObj A₂] (A₀ : Over (Spec R₀))
    [GrpObj A₀] (ψ₁ : A₀.left ⟶ A₁.left) (ψ₂ : A₀.left ⟶ A₂.left) (h₁ : IsAbelianScheme A₁)
    (h₂ : IsAbelianScheme A₂) (hψ₁ : IsGrpPullback A₀ A₁ (Spec.map g₁) ψ₁)
    (hψ₂ : IsGrpPullback A₀ A₂ (Spec.map g₂) ψ₂) :
    ∃ (A : Over (Spec P)) (_ : GrpObj A) (φ₁ : A₁.left ⟶ A.left) (φ₂ : A₂.left ⟶ A.left),
      IsAbelianScheme A ∧ IsGrpPullback A₁ A (Spec.map f₁) φ₁ ∧ IsGrpPullback A₂ A (Spec.map f₂) φ₂ ∧
        ψ₁ ≫ φ₁ = ψ₂ ≫ φ₂ := by
  haveI := h₁.smooth
  haveI := h₂.smooth
  obtain ⟨Y, j₁, j₂, hj₁, hj₂, hY, hpo⟩ := GlobalTheory.T.ferrand_glue_flat_artinian_fibreProduct P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hpb hl ha hg₁ hg₂
    A₁ A₂ A₀ ψ₁ ψ₂ hψ₁.1 hψ₂.1 inferInstance inferInstance
  obtain ⟨G, hc, hG₁, hG₂⟩ := GlobalTheory.T.exists_glued_commGroupScheme_artinFibreProduct P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hpb hl ha hg₁ hg₂ A₁ A₂ A₀ ψ₁ ψ₂
    h₁.comm h₂.comm hψ₁ hψ₂ Y j₁ j₂ hj₁ hj₂ hY hpo
  refine ⟨Y, G, j₁, j₂, ?_, hG₁, hG₂, hpo.w⟩
  have hf₁ : Function.Surjective f₁ := (pullback_elem hpb).2 hg₂
  have hN : IsNilpotent (RingHom.ker f₁.hom) := isNilpotent_ker f₁
  have hlfp : LocallyOfFinitePresentation Y.hom :=
    GlobalTheory.T.locallyOfFinitePresentation_of_nilpotent_thickening_noetherian P R₁ f₁ hf₁ hN inferInstance Y A₁ j₁ hj₁ inferInstance
  have hsm : Smooth Y.hom := GlobalTheory.smooth_of_isPullback_of_surjective_of_flat _ _ _ _ (Spec.map f₁) j₁
    A₁.hom Y.hom hj₁ (surjective_spec_map f₁) hY hlfp h₁.smooth
  obtain ⟨hp, hgc⟩ := GlobalTheory.NilLift.isProper_and_geometricallyConnected_of_smooth_lift P R₁ f₁.hom hf₁ hN
    Y A₁ j₁ hj₁ hsm h₁.proper h₁.geomConnected
  exact ⟨hc, hsm, hp, hgc⟩

theorem main : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (A₁ : Over (Spec R₁)) [GrpObj A₁] (A₂ : Over (Spec R₂)) [GrpObj A₂] (A₀ : Over (Spec R₀)) [GrpObj A₀] (ψ₁ : A₀.left ⟶ A₁.left) (ψ₂ : A₀.left ⟶ A₂.left), IsAbelianScheme A₁ → IsAbelianScheme A₂ → IsGrpPullback A₀ A₁ (Spec.map g₁) ψ₁ → IsGrpPullback A₀ A₂ (Spec.map g₂) ψ₂ → ∃ (A : Over (Spec P)) (_ : GrpObj A) (φ₁ : A₁.left ⟶ A.left) (φ₂ : A₂.left ⟶ A.left), IsAbelianScheme A ∧ IsGrpPullback A₁ A (Spec.map f₁) φ₁ ∧ IsGrpPullback A₂ A (Spec.map f₂) φ₂ ∧ ψ₁ ≫ φ₁ = ψ₂ ≫ φ₂ := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hpb hl ha hg₁ hg₂ A₁ _ A₂ _ A₀ _ ψ₁ ψ₂ h₁ h₂ hψ₁ hψ₂
  by_cases hR : Nontrivial R₁
  · exact main_of_nontrivial P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hpb hl ha hg₁ hg₂ hR A₁ A₂ A₀ ψ₁ ψ₂ h₁ h₂ hψ₁ hψ₂
  · have hR₂ : Nontrivial R₂ := by
      by_contra hR₂
      rw [not_nontrivial_iff_subsingleton] at hR hR₂
      exact zero_ne_one ((pullback_elem hpb).1 0 1 (Subsingleton.elim _ _) (Subsingleton.elim _ _))
    obtain ⟨A, G, φ₂, φ₁, hA, h₂', h₁', hw⟩ := main_of_nontrivial P R₂ R₁ R₀ f₂ f₁ g₂ g₁ hpb.flip hl ha
      hg₂ hg₁ hR₂ A₂ A₁ A₀ ψ₂ ψ₁ h₂ h₁ hψ₂ hψ₁
    exact ⟨A, G, φ₁, φ₂, hA, h₁', h₂', hw.symm⟩

end GlobalTheory.GlueAb
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeGlueArtinianLocalFibreProductStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.abelianScheme_glue_artinian_local_fibreProduct : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (A₁ : Over (Spec R₁)) [GrpObj A₁] (A₂ : Over (Spec R₂)) [GrpObj A₂] (A₀ : Over (Spec R₀)) [GrpObj A₀] (ψ₁ : A₀.left ⟶ A₁.left) (ψ₂ : A₀.left ⟶ A₂.left), IsAbelianScheme A₁ → IsAbelianScheme A₂ → IsGrpPullback A₀ A₁ (Spec.map g₁) ψ₁ → IsGrpPullback A₀ A₂ (Spec.map g₂) ψ₂ → ∃ (A : Over (Spec P)) (_ : GrpObj A) (φ₁ : A₁.left ⟶ A.left) (φ₂ : A₂.left ⟶ A.left), IsAbelianScheme A ∧ IsGrpPullback A₁ A (Spec.map f₁) φ₁ ∧ IsGrpPullback A₂ A (Spec.map f₂) φ₂ ∧ ψ₁ ≫ φ₁ = ψ₂ ≫ φ₂ := by
  first | exact @GlobalTheory.GlueAb.main | exact GlobalTheory.GlueAb.main | (intros; apply GlobalTheory.GlueAb.main <;> assumption)
end
end
