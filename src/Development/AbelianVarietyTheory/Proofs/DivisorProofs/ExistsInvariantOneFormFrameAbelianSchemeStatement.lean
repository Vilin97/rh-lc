module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RedHomAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRetractionDifferentialsInvariantOneFormsAfStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCrystallineFormLiftDifferenceEqSum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.LocalProperties.FinitePresentation
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
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanInvariantOneFormsAffineOpenAbelianSchemeEqToStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantOneFormsAbelianSchemeFiniteProjective

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.InvFormProj

theorem finite_projective_of_locally_projective (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]
    (h : ∀ q : PrimeSpectrum R, ∃ r : R, r ∉ q.asIdeal ∧ ∃ (F : Type) (_ : AddCommGroup F) (_ : Module R F)
      (_ : Module (Localization.Away r) F) (_ : IsScalarTower R (Localization.Away r) F)
      (_ : Module.Finite (Localization.Away r) F) (_ : Module.Projective (Localization.Away r) F)
      (ϕ : M →ₗ[R] F), IsBaseChange (Localization.Away r) ϕ) :
    Module.Finite R M ∧ Module.Projective R M := by
  let s : Set R := {r | ∃ (F : Type) (_ : AddCommGroup F) (_ : Module R F)
    (_ : Module (Localization.Away r) F) (_ : IsScalarTower R (Localization.Away r) F)
    (_ : Module.Finite (Localization.Away r) F) (_ : Module.Projective (Localization.Away r) F)
    (ϕ : M →ₗ[R] F), IsBaseChange (Localization.Away r) ϕ}
  have hs : Ideal.span s = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hsm⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨r, hr, hP⟩ := h ⟨m, hm.isPrime⟩
    exact hr (hsm (Ideal.subset_span hP))
  have hg : ∀ g : s, g.1 ∈ s := fun g => g.2
  choose F iA iM iL iT iFin iProj ϕ hϕ using hg
  letI := iA
  letI := iM
  letI := iL
  haveI := iT
  haveI := iFin
  haveI := iProj
  haveI (g : s) : IsLocalizedModule (Submonoid.powers g.1) (ϕ g) :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers g.1) (Localization.Away g.1) (ϕ g)).2 (hϕ g)
  haveI (g : s) : Module.Flat R (F g) := by
    haveI : Module.Flat R (Localization.Away g.1) :=
      IsLocalization.flat _ (Submonoid.powers g.1)
    exact Module.Flat.trans R (Localization.Away g.1) (F g)
  haveI hfp : Module.FinitePresentation R M :=
    Module.FinitePresentation.of_localizationSpan' s hs (Mₚ := F)
      (Rₚ := fun g : s => Localization.Away g.1) ϕ
      fun _ => Module.finitePresentation_of_projective _ _
  haveI : Module.Flat R M :=
    Module.flat_of_isLocalized_span R M s hs F ϕ fun _ => inferInstance
  exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation⟩

theorem finite_projective : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → (∀ U : AffOp A.left, IsBaseChange (Sec A.hom U.unop.1) (evForm A.hom U ∘ₗ (GlobalTheory.InvForm.InvForm A).subtype)) → Module.Finite R (GlobalTheory.InvForm.InvForm A) ∧ Module.Projective R (GlobalTheory.InvForm.InvForm A) := by
  intro R _ A _ g _ hsm hbc
  haveI : SmoothOfRelativeDimension g A.hom := hsm
  haveI : Smooth A.hom := SmoothOfRelativeDimension.smooth g A.hom
  apply finite_projective_of_locally_projective
  intro q
  let e : Spec (CommRingCat.of R) ⟶ A.left := η[A].left
  have he : e ≫ A.hom = 𝟙 _ := by simp [e]
  obtain ⟨V, hV, hqV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp A.left.isBasis_affineOpens)
    (show e q ∈ (⊤ : A.left.Opens) from trivial)
  obtain ⟨_, ⟨r, rfl⟩, hr, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (a := q) (u := (e ⁻¹ᵁ V).1) hqV (e ⁻¹ᵁ V).2
  refine ⟨r, hr, ?_⟩
  let y : Sp (Localization.Away r) ⟶ A.left := spMap (algebraMap R (Localization.Away r)) ≫ e
  have hy : ⊤ ≤ y ⁻¹ᵁ V := by
    intro t _
    have : PrimeSpectrum.comap (algebraMap R (Localization.Away r)) t ∈
        (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) := by
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
      exact ⟨t, rfl⟩
    exact hsub this
  have hs : y ≫ A.hom = spMap (algebraMap R (Localization.Away r)) := by
    simp only [y, Category.assoc, he, Category.comp_id]
  let φ := GlobalTheory.CechKS.FormLocal.valHom (s := A.hom) (U := V) y hy hs
  letI : Algebra (Sec A.hom V) (Localization.Away r) := φ.toRingHom.toAlgebra
  haveI : IsScalarTower R (Sec A.hom V) (Localization.Away r) :=
    IsScalarTower.of_algebraMap_eq fun a => (φ.commutes a).symm
  haveI : Algebra.Smooth R (Sec A.hom V) := smooth_sec_affine A.hom ⟨V, hV⟩
  have hb := hbc (Opposite.op ⟨V, hV⟩)
  exact ⟨Localization.Away r ⊗[Sec A.hom V] Ω[Sec A.hom V⁄R], inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, _,
    hb.comp (TensorProduct.isBaseChange (Sec A.hom V) Ω[Sec A.hom V⁄R] (Localization.Away r))⟩

end GlobalTheory.InvFormProj
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantOneFormsAbelianSchemeFiniteProjectiveStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.invariantOneForms_abelianScheme_finite_projective : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → (∀ U : AffOp A.left, IsBaseChange (Sec A.hom U.unop.1) (evForm A.hom U ∘ₗ (GlobalTheory.InvForm.InvForm A).subtype)) → Module.Finite R (GlobalTheory.InvForm.InvForm A) ∧ Module.Projective R (GlobalTheory.InvForm.InvForm A) := by
  first | exact @GlobalTheory.InvFormProj.finite_projective | exact GlobalTheory.InvFormProj.finite_projective | (intros; apply GlobalTheory.InvFormProj.finite_projective <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantOneFormFrameAbelianScheme

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.InvFormBC

open GlobalTheory.InvForm

theorem isBaseChange_invForm : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ U : AffOp A.left, IsBaseChange (Sec A.hom U.unop.1) (evForm A.hom U ∘ₗ (InvForm A).subtype) := by
  intro R _ A _ g hab hdim U
  let f := evForm A.hom U ∘ₗ (InvForm A).subtype
  let L := f.liftBaseChange (Sec A.hom U.unop.1)
  have hs : Function.Surjective L := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← GlobalTheory.T.span_invariantOneForms_affineOpen_abelianScheme_eq_top R A g hab hdim U]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨w, rfl⟩
    exact ⟨1 ⊗ₜ w, by simp [L, f]⟩
  obtain ⟨r, hr⟩ := GlobalTheory.T.exists_retraction_differentials_invariantOneForms_affine R A g hab hdim U
  have hl : ∀ x, r (L x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b w =>
      have : L (b ⊗ₜ w) = b • evForm A.hom U w.1 := by simp [L, f]
      rw [this, map_smul, hr, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hi : Function.Injective L := fun x y h ↦ by rw [← hl x, ← hl y, h]
  have hb : Function.Bijective L := ⟨hi, hs⟩
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective L hb) fun x ↦
    show L (1 ⊗ₜ x) = f x from (LinearMap.liftBaseChange_tmul _ f 1 x).trans (one_smul _ _)

theorem exists_invariant_frame : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∃ (M : Type) (_ : AddCommGroup M) (_ : Module R M) (j : M →ₗ[R] GlobForm A.hom), Module.Finite R M ∧ Module.Projective R M ∧ ∀ U : AffOp A.left, IsBaseChange (Sec A.hom U.unop.1) (evForm A.hom U ∘ₗ j) := by
  intro R _ A _ g hab hdim
  have hbc := isBaseChange_invForm R A g hab hdim
  obtain ⟨hfin, hproj⟩ := GlobalTheory.T.invariantOneForms_abelianScheme_finite_projective R A g hab hdim hbc
  exact ⟨InvForm A, inferInstance, inferInstance, (InvForm A).subtype, hfin, hproj, hbc⟩

end GlobalTheory.InvFormBC
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantOneFormFrameAbelianSchemeStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_invariant_oneForm_frame_abelianScheme : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∃ (M : Type) (_ : AddCommGroup M) (_ : Module R M) (j : M →ₗ[R] GlobForm A.hom), Module.Finite R M ∧ Module.Projective R M ∧ ∀ U : AffOp A.left, IsBaseChange (Sec A.hom U.unop.1) (evForm A.hom U ∘ₗ j) := by
  first | exact @GlobalTheory.InvFormBC.exists_invariant_frame | exact GlobalTheory.InvFormBC.exists_invariant_frame | (intros; apply GlobalTheory.InvFormBC.exists_invariant_frame <;> assumption)
end
end
