module

public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocyclePullbackIffPreimageAffineHomStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageCochainRestrictionBijectiveClosedImmersiStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveDeformationAffineSectionsStatement
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.PreUMono
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackProdSelfIsPullbackStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ObstructionClassNaturalStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatLiftingObstructionClass

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

theorem exists_bock : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)), SmallExt t σ σ₀ → Flat s → ∀ x : HO1 s', ∃ z : HO2 s₀, Bock h.w h₀.w t x z := by
  intro R R' R₀ _ _ _ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ hS hF x
  have hc : IsClosedImmersion (spMap σ) := IsClosedImmersion.spec_of_surjective _ hS.1
  have hc₀ : IsClosedImmersion (spMap σ₀) := IsClosedImmersion.spec_of_surjective _ hS.2.2.1
  haveI : IsClosedImmersion φ := MorphismProperty.of_isPullback h.flip hc
  haveI : IsClosedImmersion φ₀ := MorphismProperty.of_isPullback h₀.flip hc₀
  have sec := fun U ↦ GlobalTheory.T.surjective_deformation_affine_sections R R' R₀ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ hS hF U
  have red := GlobalTheory.T.cocyclePullback_iff_preimage_affineHom R R' X X' s s' σ φ h.w
  have red₀ := GlobalTheory.T.cocyclePullback_iff_preimage_affineHom R R₀ X X₀ s s₀ σ₀ φ₀ h₀.w
  have bij₀ := (GlobalTheory.T.preimageCochainRestriction_bijective_closedImmersion R₀ X X₀ φ₀ s₀).2.1
  obtain ⟨c, hc⟩ := GlobalTheory.CatCoh.H1.mk_surjective _ ((preRes φ s').pull1 x)
  choose f hf using fun (U V : AffOp X) (a : U ⟶ V) ↦ (sec V).1 (c.1 U V a)
  have hd : ∀ (U V W : AffOp X) (a : U ⟶ V) (b : V ⟶ W), preα φ s s' W (d1 (OAff s) f U V W a b) = 0 := by
    intro U V W a b
    have nat := (preCoef h.w).naturality b (f U V a)
    have cc := c.2 a b
    rw [d1_apply, map_add (f := _), map_sub, hf, hf]
    erw [nat, hf]
    rw [cc]; ring
  choose w hw using fun (U V W : AffOp X) (a : U ⟶ V) (b : V ⟶ W) ↦ ((sec W).2.1 _).1 (hd U V W a b)
  have hdw : d1 (OAff s) f = t • w := by
    funext U V W a b; exact hw U V W a b
  have hw2 : ∀ ⦃U V W Y : AffOp X⦄ (a : U ⟶ V) (b : V ⟶ W) (e : W ⟶ Y),
      t • (mp (OAff s) e (w U V W a b) + w U W Y (a ≫ b) e - (w U V Y a (b ≫ e) + w V W Y b e)) = 0 := by
    intro U V W Y a b e
    have := (differential_one_mem_scaled_lattice (OAff s) f) a b e
    rw [hdw] at this
    simp only [Pi.smul_apply, map_smul] at this
    rw [smul_sub, smul_add, smul_add, this, sub_self]
  have hc0 : (fun U V W (a : U ⟶ V) (b : V ⟶ W) ↦ preα φ₀ s s₀ W (w U V W a b) : C2 (OPre φ₀ s₀)) ∈
      Z2 (OPre φ₀ s₀) := by
    intro U V W Y a b e
    have h1 := ((sec Y).2.2.2 _).2 (hw2 a b e)
    have nat := (preCoef h₀.w).naturality e (w U V W a b)
    simp only [map_add (f := _), map_sub] at h1
    erw [nat] at h1
    dsimp only
    exact sub_eq_zero.1 h1
  obtain ⟨z, hz⟩ := bij₀.2 (GlobalTheory.CatCoh.H2.mk _ ⟨_, hc0⟩)
  exact ⟨z, f, w, hdw, (red.1 f x).2 ⟨c, fun U V a ↦ (hf U V a).symm, hc⟩,
    (red₀.2.1 w z).2 ⟨⟨_, hc0⟩, fun U V W a b ↦ rfl, hz.symm⟩⟩

end GlobalTheory.AbCoh
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatLiftingObstructionClassStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_flat_lifting_obstruction_class : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)), SmallExt t σ σ₀ → Flat s → ∀ x : HO1 s', ∃ z : HO2 s₀, Bock h.w h₀.w t x z := by
  first | exact @GlobalTheory.AbCoh.exists_bock | exact GlobalTheory.AbCoh.exists_bock | (intros; apply GlobalTheory.AbCoh.exists_bock <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftOfLiftingObstructionEqZero

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false


namespace GlobalTheory.AbCoh

theorem exists_lift_of_bock_zero : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)), SmallExt t σ σ₀ → Flat s → ∀ x : HO1 s', Bock h.w h₀.w t x 0 → ∃ y : HO1 s, pullHO1 h.w y = x := by
  intro R R' R₀ _ _ _ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ hse hfl x hB
  have hσc : IsClosedImmersion (spMap σ) := IsClosedImmersion.spec_of_surjective _ hse.1
  have hσ₀c : IsClosedImmersion (spMap σ₀) := IsClosedImmersion.spec_of_surjective _ hse.2.2.1
  haveI : IsClosedImmersion φ := MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip hσc
  haveI : IsClosedImmersion φ₀ := MorphismProperty.of_isPullback (P := @IsClosedImmersion) h₀.flip hσ₀c
  obtain ⟨f, w, hfw, hf, hw⟩ := hB
  have R1 := (GlobalTheory.T.cocyclePullback_iff_preimage_affineHom R R' X X' s s' σ φ h.w).1
  have R2 := (GlobalTheory.T.cocyclePullback_iff_preimage_affineHom R R₀ X X₀ s s₀ σ₀ φ₀ h₀.w).2.1
  have R3 := (GlobalTheory.T.cocyclePullback_iff_preimage_affineHom R R' X X' s s' σ φ h.w).2.2.1
  have S := GlobalTheory.T.surjective_deformation_affine_sections R R' R₀ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ hse hfl
  have B := (GlobalTheory.T.preimageCochainRestriction_bijective_closedImmersion R' X X' φ s').1.1
  obtain ⟨c, hc, hcx⟩ := (R1 f x).1 hf
  obtain ⟨c₀, hc₀, hc₀z⟩ := (R2 w 0).1 hw
  rw [map_zero, H2.mk_eq_zero] at hc₀z
  obtain ⟨b, hb⟩ := hc₀z
  choose u hu using fun (U V : AffOp X) (a : U ⟶ V) ↦ (S V).2.2.1 (b U V a)
  have nat₀ : ∀ {V W : AffOp X} (a : V ⟶ W) (y : (OAff s).obj V),
      preα φ₀ s s₀ W (mp (OAff s) a y) = mp (OPre φ₀ s₀) a (preα φ₀ s s₀ V y) :=
    fun a y ↦ (preCoef h₀.w).naturality a y
  have hker : ∀ (U V W : AffOp X) (a : U ⟶ V) (a' : V ⟶ W), t • (w U V W a a' - d1 (OAff s) u U V W a a') = 0 := by
    intro U V W a a'
    rw [← (S W).2.2.2, map_sub, d1_apply, map_add (f := _), map_sub, nat₀, hu, hu, hu, ← hc₀, ← d1_apply, hb, sub_self]
  have hg : f - t • u ∈ Z1 (OAff s) := by
    rw [commAlgFunctorCocyclesOne_eq_ker, LinearMap.mem_ker, map_sub, hfw, map_smul, ← smul_sub]
    funext U V W a a'
    exact hker U V W a a'
  refine ⟨H1.mk _ ⟨f - t • u, hg⟩, B ?_⟩
  rw [R3, CoefMap.pullCohomologyOne_class, ← hcx]
  congr 1
  refine Subtype.ext ?_
  funext U V a
  rw [CoefMap.pullCocycleOne_apply, hc]
  show preα φ s s' V (f U V a - t • u U V a) = _
  rw [map_sub, ((S V).2.1 _).2 ⟨_, rfl⟩, sub_zero]

end GlobalTheory.AbCoh
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftOfLiftingObstructionEqZeroStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_lift_of_lifting_obstruction_eq_zero : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)), SmallExt t σ σ₀ → Flat s → ∀ x : HO1 s', Bock h.w h₀.w t x 0 → ∃ y : HO1 s, pullHO1 h.w y = x := by
  first | exact @GlobalTheory.AbCoh.exists_lift_of_bock_zero | exact GlobalTheory.AbCoh.exists_lift_of_bock_zero | (intros; apply GlobalTheory.AbCoh.exists_lift_of_bock_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftingObstructionBocksteinAdd

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem Bock_add : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : φ ≫ s = s' ≫ spMap σ) (h₀ : φ₀ ≫ s = s₀ ≫ spMap σ₀) (x x' : HO1 s') (z z' : HO2 s₀), Bock h h₀ t x z → Bock h h₀ t x' z' → Bock h h₀ t (x + x') (z + z') := by
  intro R R' R₀ _ _ _ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ x x' z z'
  rintro ⟨f, w, hd, ⟨c, hc, hcx⟩, ⟨e, he, hez⟩⟩ ⟨f', w', hd', ⟨c', hc', hcx'⟩, ⟨e', he', hez'⟩⟩
  refine ⟨f + f', w + w', by rw [map_add (f := _), hd, hd', smul_add], ⟨c + c', fun p q a ↦ ?_, ?_⟩,
    ⟨e + e', fun p q r a b ↦ ?_, ?_⟩⟩
  · simp only [Submodule.coe_add, Pi.add_apply, hc, hc', map_add (f := _)]
  · rw [map_add (f := _), hcx, hcx', map_add (f := _)]
  · simp only [Submodule.coe_add, Pi.add_apply, he, he', map_add (f := _)]
  · rw [map_add (f := _), hez, hez', map_add (f := _)]

end GlobalTheory.AbCoh
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftingObstructionBocksteinAddStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.liftingObstructionBockstein_add : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : φ ≫ s = s' ≫ spMap σ) (h₀ : φ₀ ≫ s = s₀ ≫ spMap σ₀) (x x' : HO1 s') (z z' : HO2 s₀), Bock h h₀ t x z → Bock h h₀ t x' z' → Bock h h₀ t (x + x') (z + z') := by
  first | exact @GlobalTheory.AbCoh.Bock_add | exact GlobalTheory.AbCoh.Bock_add | (intros; apply GlobalTheory.AbCoh.Bock_add <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallExtensionPrimitiveLift

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem pullHO1_surjective_of_smallExt : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (g : ℕ) (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp R')) [GrpObj A'] (A₀ : Over (Sp R₀)) [GrpObj A₀] (φ : A'.left ⟶ A.left) (φ₀ : A₀.left ⟶ A.left) (h : IsGrpPullback A' A (spMap σ) φ) (h₀ : IsGrpPullback A₀ A (spMap σ₀) φ₀), SmallExt t σ σ₀ → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → StructureSheafH1Primitive A' → NoPrimitiveStructureSheafH2 A₀ → Function.Surjective (pullHO1 h.1.w) := by
  intro R R' R₀ _ _ _ t σ σ₀ g A _ A' _ A₀ _ φ φ₀ h h₀ hS hA _ hP hN x
  haveI := hA.smooth
  have hF : Flat A.hom := inferInstance
  have hF2 : Flat (A ⊗ A).hom := by
    show Flat (pullback.fst A.hom A.hom ≫ A.hom)
    infer_instance
  obtain ⟨Φ, hΦ, hm, h1, h2, -, -⟩ := GlobalTheory.T.grpPullback_prod_self_isPullback R R' σ A A' φ h
  obtain ⟨Φ₀, hΦ₀, hm₀, h1₀, h2₀, -, -⟩ := GlobalTheory.T.grpPullback_prod_self_isPullback R R₀ σ₀ A A₀ φ₀ h₀
  obtain ⟨z, hz⟩ := GlobalTheory.T.exists_flat_lifting_obstruction_class R R' R₀ t σ σ₀ A.left A'.left A₀.left A.hom A'.hom A₀.hom φ φ₀ h.1 h₀.1 hS hF x

  have nat : ∀ (ψ : (A ⊗ A).left ⟶ A.left) (ψ' : (A' ⊗ A').left ⟶ A'.left) (ψ₀ : (A₀ ⊗ A₀).left ⟶ A₀.left)
      (w : ψ ≫ A.hom = (A ⊗ A).hom ≫ spMap (RingHom.id R)) (w' : ψ' ≫ A'.hom = (A' ⊗ A').hom ≫ spMap (RingHom.id R'))
      (w₀ : ψ₀ ≫ A₀.hom = (A₀ ⊗ A₀).hom ≫ spMap (RingHom.id R₀)), ψ' ≫ φ = Φ ≫ ψ → ψ₀ ≫ φ₀ = Φ₀ ≫ ψ →
      ∀ z', Bock hΦ.w hΦ₀.w t (pullHO1 w' x) z' → z' = pullHO2 w₀ z := by
    intro ψ ψ' ψ₀ w w' w₀ e e₀ z' hz'
    exact GlobalTheory.T.obstructionClass_natural R R' R₀ t σ σ₀ A.left A'.left A₀.left A.hom A'.hom A₀.hom φ φ₀ h.1 h₀.1
      (A ⊗ A).left (A' ⊗ A').left (A₀ ⊗ A₀).left (A ⊗ A).hom (A' ⊗ A').hom (A₀ ⊗ A₀).hom Φ Φ₀ hΦ hΦ₀
      ψ ψ' ψ₀ w w' w₀ e e₀ hS hF hF2 x z z' hz hz'
  have ex : ∀ y : HO1 (A' ⊗ A').hom, ∃ z' : HO2 (A₀ ⊗ A₀).hom, Bock hΦ.w hΦ₀.w t y z' := fun y ↦
    GlobalTheory.T.exists_flat_lifting_obstruction_class R R' R₀ t σ σ₀ (A ⊗ A).left (A' ⊗ A').left (A₀ ⊗ A₀).left (A ⊗ A).hom (A' ⊗ A').hom (A₀ ⊗ A₀).hom
      Φ Φ₀ hΦ hΦ₀ hS hF2 y
  obtain ⟨z1, hz1⟩ := ex (pO1 (fst A' A') x)
  obtain ⟨z2, hz2⟩ := ex (pO1 (snd A' A') x)
  have e1 : z1 = structureSheafH2Pullback (fst A₀ A₀) z := nat _ _ _ (ovw (fst A A)) (ovw (fst A' A')) (ovw (fst A₀ A₀)) h1 h1₀ z1 hz1
  have e2 : z2 = structureSheafH2Pullback (snd A₀ A₀) z := nat _ _ _ (ovw (snd A A)) (ovw (snd A' A')) (ovw (snd A₀ A₀)) h2 h2₀ z2 hz2
  have hsum := GlobalTheory.T.liftingObstructionBockstein_add R R' R₀ t σ σ₀ (A ⊗ A).left (A' ⊗ A').left (A₀ ⊗ A₀).left (A ⊗ A).hom (A' ⊗ A').hom
    (A₀ ⊗ A₀).hom Φ Φ₀ hΦ.w hΦ₀.w _ _ z1 z2 hz1 hz2
  rw [← hP x] at hsum
  have em : z1 + z2 = structureSheafH2Pullback μ[A₀] z := nat _ _ _ (ovw μ[A]) (ovw μ[A']) (ovw μ[A₀]) hm hm₀ _ hsum
  have z0 : z = 0 := hN z (by rw [← em, e1, e2])
  subst z0
  exact GlobalTheory.T.exists_lift_of_lifting_obstruction_eq_zero R R' R₀ t σ σ₀ A.left A'.left A₀.left A.hom A'.hom A₀.hom φ φ₀ h.1 h₀.1 hS hF x hz

end GlobalTheory.AbCoh
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallExtensionPrimitiveLiftStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.small_extension_primitive_lift : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (g : ℕ) (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp R')) [GrpObj A'] (A₀ : Over (Sp R₀)) [GrpObj A₀] (φ : A'.left ⟶ A.left) (φ₀ : A₀.left ⟶ A.left) (h : IsGrpPullback A' A (spMap σ) φ) (h₀ : IsGrpPullback A₀ A (spMap σ₀) φ₀), SmallExt t σ σ₀ → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → StructureSheafH1Primitive A' → NoPrimitiveStructureSheafH2 A₀ → Function.Surjective (pullHO1 h.1.w) := by
  first | exact @GlobalTheory.AbCoh.pullHO1_surjective_of_smallExt | exact GlobalTheory.AbCoh.pullHO1_surjective_of_smallExt | (intros; apply GlobalTheory.AbCoh.pullHO1_surjective_of_smallExt <;> assumption)
end
end
