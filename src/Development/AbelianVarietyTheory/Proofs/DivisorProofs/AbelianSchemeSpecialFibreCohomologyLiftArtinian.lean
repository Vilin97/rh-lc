module

public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyStructureSheafCohomologyAnyFieldStatement
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArtinianLiftAxesWedgeLocalStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArtinianLiftAxesWedgeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArtinianLocalFiniteLengthAndSocleElementStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeBaseChangeAndSquareStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyPullbackCompCupIdStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommAlgFunctorCohomologyTwoEqZeroOfIsInitial
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullH1SurjectiveBijectiveFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectivePullHO2OfPullHO1Statement
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianOverFieldAxesWedge

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.AbCoh.FieldSq

theorem axes_noPrim_wedge : (∀ (k : Type) [CommRing k], IsField k → ∀ (B : Over (Sp k)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → AxesVanishingStructureSheafDegOne B ∧ NoPrimitiveStructureSheafH2 B ∧ WedgeO (OAff B.hom)) := by
  intro k _ hk B _ g hab hsm
  letI : Field k := hk.toField
  obtain ⟨-, -, hw, hn, ha⟩ := GlobalTheory.T.abelianVariety_structureSheaf_cohomology_anyField k B g hab hsm
  exact ⟨ha, hn, hw⟩

end GlobalTheory.AbCoh.FieldSq
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianOverFieldAxesWedgeStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

theorem _root_.GlobalTheory.T.abelian_over_field_axes_wedge : (∀ (k : Type) [CommRing k], IsField k → ∀ (B : Over (Sp k)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → AxesVanishingStructureSheafDegOne B ∧ NoPrimitiveStructureSheafH2 B ∧ WedgeO (OAff B.hom)) := by
  first | exact @GlobalTheory.AbCoh.FieldSq.axes_noPrim_wedge | exact GlobalTheory.AbCoh.FieldSq.axes_noPrim_wedge | (intros; apply GlobalTheory.AbCoh.FieldSq.axes_noPrim_wedge <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibrePullH1Abelian

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.AbCohWedgeLift

theorem wedgeO_of_iso {k : Type} [CommRing k] {X X' : Scheme.{0}} (s : X ⟶ Sp k) (s' : X' ⟶ Sp k) (e : X' ≅ X)
    (he : e.hom ≫ s = s') (hW : WedgeO (OAff s)) : WedgeO (OAff s') := by
  have h1 : e.hom ≫ s = s' ≫ spMap (RingHom.id k) := by rw [spMap_id, Category.comp_id, he]
  have h2 : e.inv ≫ s' = s ≫ spMap (RingHom.id k) := by
    rw [spMap_id, Category.comp_id, ← he, Iso.inv_hom_id_assoc]
  have hid : (𝟙 X) ≫ s = s ≫ spMap (RingHom.id k) := by rw [spMap_id, Category.comp_id, Category.id_comp]
  have hid' : (𝟙 X') ≫ s' = s' ≫ spMap (RingHom.id k) := by rw [spMap_id, Category.comp_id, Category.id_comp]
  have P := GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id
  have c1 := (P.1 k k X X' s s' (RingHom.id k) e.hom h1 k X s (RingHom.id k) e.inv h2 (RingHom.id k) (𝟙 X) hid
    (by simp) (fun _ ↦ rfl))
  have c2 := (P.1 k k X' X s' s (RingHom.id k) e.inv h2 k X' s' (RingHom.id k) e.hom h1 (RingHom.id k) (𝟙 X') hid'
    (by simp) (fun _ ↦ rfl))
  have i1 := P.2.2 k (Over.mk s)
  have i2 := P.2.2 k (Over.mk s')
  have hcup := (P.2.1 k k X X' s s' (RingHom.id k) e.hom h1).1

  let f1 : HO1 s →ₗ[k] HO1 s' := pullHO1 h1
  let g1 : HO1 s' →ₗ[k] HO1 s := pullHO1 h2
  let f2 : HO2 s →ₗ[k] HO2 s' := pullHO2 h1
  let g2 : HO2 s' →ₗ[k] HO2 s := pullHO2 h2
  have fg1 : ∀ a, f1 (g1 a) = a := fun a ↦ by simp only [f1, g1]; rw [c2.1]; exact i2.1 a
  have gf1 : ∀ a, g1 (f1 a) = a := fun a ↦ by simp only [f1, g1]; rw [c1.1]; exact i1.1 a
  have fg2 : ∀ a, f2 (g2 a) = a := fun a ↦ by simp only [f2, g2]; rw [c2.2.1]; exact i2.2.1 a
  have gf2 : ∀ a, g2 (f2 a) = a := fun a ↦ by simp only [f2, g2]; rw [c1.2.1]; exact i1.2.1 a
  let e2 : HO2 s ≃ₗ[k] HO2 s' := LinearEquiv.ofLinear f2 g2 (LinearMap.ext fg2) (LinearMap.ext gf2)
  let eΛ : ⋀[k]^2 (HO1 s') ≃ₗ[k] ⋀[k]^2 (HO1 s) :=
    LinearEquiv.ofLinear (exteriorPower.map 2 g1) (exteriorPower.map 2 f1)
      (by rw [← exteriorPower.map_comp, show g1 ∘ₗ f1 = LinearMap.id from LinearMap.ext gf1,
        exteriorPower.map_id])
      (by rw [← exteriorPower.map_comp, show f1 ∘ₗ g1 = LinearMap.id from LinearMap.ext fg1,
        exteriorPower.map_id])
  obtain ⟨E, hE⟩ := hW
  refine ⟨(eΛ.trans E).trans e2, fun a b ↦ ?_⟩
  have hm : (⇑g1 ∘ ![a, b]) = ![g1 a, g1 b] := by
    ext i; fin_cases i <;> rfl
  change f2 (E (exteriorPower.map 2 g1 (exteriorPower.ιMulti k 2 ![a, b]))) = _
  rw [exteriorPower.map_apply_ιMulti, hm, hE]
  simp only [f2]
  rw [hcup]
  rw [show pullHO1 h1 (g1 a) = a from fg1 a, show pullHO1 h1 (g1 b) = b from fg1 b]

end GlobalTheory.AbCohWedgeLift

namespace GlobalTheory.AbCohWedgeLift

theorem wedgeO_fibre : (∀ (k : Type) [CommRing k], IsField k → ∀ (B : Over (Sp k)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → AxesVanishingStructureSheafDegOne B ∧ NoPrimitiveStructureSheafH2 B ∧ WedgeO (OAff B.hom)) → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (k : Type) [Field k] (σ : R →+* k) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ A.left) (w : IsPullback ψ s₀ A.hom (spMap σ)), WedgeO (OAff s₀) := by
  intro hF R _ A _ g hA hg k _ σ X₀ s₀ ψ w
  letI : Algebra R k := σ.toAlgebra
  obtain ⟨B, _, pr, -, hB, hBg, hsq, -⟩ := GlobalTheory.T.exists_abelianScheme_baseChange_and_square R k A g hA hg
  have hsq' : IsPullback pr B.hom A.hom (spMap σ) := hsq
  have hW : WedgeO (OAff B.hom) := (hF k (Field.toIsField k) B g hB hBg).2.2
  let e : X₀ ≅ B.left := IsPullback.isoIsPullback _ _ w hsq'
  exact wedgeO_of_iso B.hom s₀ e (IsPullback.isoIsPullback_hom_snd _ _ w hsq') hW

end GlobalTheory.AbCohWedgeLift
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibrePullH1AbelianStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

theorem _root_.GlobalTheory.T.closed_fibre_pull_h1_abelian : (∀ (k : Type) [CommRing k], IsField k → ∀ (B : Over (Sp k)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → AxesVanishingStructureSheafDegOne B ∧ NoPrimitiveStructureSheafH2 B ∧ WedgeO (OAff B.hom)) → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (k : Type) [Field k] (σ : R →+* k) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ A.left) (w : IsPullback ψ s₀ A.hom (spMap σ)), WedgeO (OAff s₀) := by
  first | exact @GlobalTheory.AbCohWedgeLift.wedgeO_fibre | exact GlobalTheory.AbCohWedgeLift.wedgeO_fibre | (intros; apply GlobalTheory.AbCohWedgeLift.wedgeO_fibre <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveOfAxesVanishing

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.AbCoh.PrimLift

theorem pO1_comp {R : Type} [CommRing R] {Y A B : Over (Sp R)} (f : Y ⟶ A) (g : A ⟶ B) (a : HO1 B.hom) :
    pO1 (f ≫ g) a = pO1 f (pO1 g a) := by
  unfold pO1
  exact ((GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id.1 R R B.left A.left B.hom A.hom (RingHom.id R) g.left (ovw g) R Y.left Y.hom
    (RingHom.id R) f.left (ovw f) (RingHom.id R) (f ≫ g).left (ovw (f ≫ g)) (by simp)
    (fun _ => rfl)).1 a).symm

theorem pO1_id {R : Type} [CommRing R] {A : Over (Sp R)} (a : HO1 A.hom) : pO1 (𝟙 A) a = a :=
  (GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id.2.2 R A).1 a

theorem pO1_unit_eq_zero {R : Type} [CommRing R] (a : HO1 (𝟙_ (Over (Sp R))).hom) : a = 0 := by
  haveI : IsAffine (𝟙_ (Over (Sp R))).left := by
    show IsAffine (Sp R)
    infer_instance
  exact (GlobalTheory.AbCoh.Vanish.main.1 R _ _ this).1.elim a 0

theorem primO1_of_axesO1 : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], AxesVanishingStructureSheafDegOne A → StructureSheafH1Primitive A := by
  intro R _ A _ hax x
  have key : ∀ j : A ⟶ A ⊗ A, pO1 (j ≫ μ[A]) x - pO1 (j ≫ fst A A) x - pO1 (j ≫ snd A A) x =
      pO1 j (pO1 μ[A] x - pO1 (fst A A) x - pO1 (snd A A) x) := by
    intro j
    rw [map_sub, map_sub, pO1_comp, pO1_comp, pO1_comp]
  have hη : pO1 (toUnit A ≫ η[A]) x = 0 := by
    rw [pO1_comp, pO1_unit_eq_zero (pO1 η[A] x), map_zero]
  have h := hax (pO1 μ[A] x - pO1 (fst A A) x - pO1 (snd A A) x)
    (by
      rw [← key, lift_comp_one_right, lift_fst, lift_snd, pO1_id, hη]
      simp)
    (by
      rw [← key, lift_comp_one_left, lift_fst, lift_snd, pO1_id, hη]
      simp)
  rw [sub_sub, sub_eq_zero] at h
  exact h

end GlobalTheory.AbCoh.PrimLift
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveOfAxesVanishingStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

theorem _root_.GlobalTheory.T.primitive_of_axes_vanishing : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], AxesVanishingStructureSheafDegOne A → StructureSheafH1Primitive A := by
  first | exact @GlobalTheory.AbCoh.PrimLift.primO1_of_axesO1 | exact GlobalTheory.AbCoh.PrimLift.primO1_of_axesO1 | (intros; apply GlobalTheory.AbCoh.PrimLift.primO1_of_axesO1 <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullH1SurjectiveBijectiveFibreStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

theorem _root_.GlobalTheory.T.pull_h1_surjective_bijective_fibre : ∀ (R k : Type) [CommRing R] [CommRing k] (σ : R →+* k), Function.Bijective σ → ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ X) (w : IsPullback ψ s₀ s (spMap σ)), Function.Surjective (pullHO1 w.w) := by
  first | exact @GlobalTheory.AbCoh.pullHO1_surjective_of_bijective | exact GlobalTheory.AbCoh.pullHO1_surjective_of_bijective | (intros; apply GlobalTheory.AbCoh.pullHO1_surjective_of_bijective <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeSpecialFibreCohomologyLiftArtinian

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

theorem artinian_pullHO_surjective : ∀ (R : Type) [CommRing R] [IsArtinianRing R] [IsLocalRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (k : Type) [Field k] (σ : R →+* k), Function.Surjective σ → ∀ (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ A.left) (w : IsPullback ψ s₀ A.hom (spMap σ)), Function.Surjective (pullHO1 w.w) ∧ Function.Surjective (pullHO2 w.w) := by
  intro R _ _ _ A _ g hA hsm k _ σ hσ X₀ s₀ ψ w
  have FF := GlobalTheory.T.abelian_over_field_axes_wedge
  have key : ∀ n : ℕ, ∀ (R : Type) [CommRing R] [IsArtinianRing R] [IsLocalRing R], Module.length R R ≤ n →
      ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
        (∀ (k : Type) [Field k] (σ : R →+* k), Function.Surjective σ → ∀ (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ A.left) (w : IsPullback ψ s₀ A.hom (spMap σ)), Function.Surjective (pullHO1 w.w)) ∧ StructureSheafH1Primitive A := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro R _ _ _ hlen A _ g hA hsm
      by_cases hF : IsField R
      · refine ⟨?_, GlobalTheory.T.primitive_of_axes_vanishing R A (FF R hF A g hA hsm).1⟩
        intro k _ σ hσ X₀ s₀ ψ w
        letI := hF.toField
        exact GlobalTheory.T.pull_h1_surjective_bijective_fibre R k σ ⟨σ.injective, hσ⟩ _ _ X₀ s₀ ψ w
      · obtain ⟨t, ht0, htm, hlt⟩ := (GlobalTheory.T.isArtinianLocal_length_finite_and_exists_socle_elem R).2 hF
        obtain ⟨n0, hn0⟩ := (GlobalTheory.T.isArtinianLocal_length_finite_and_exists_socle_elem R).1
        have htop : Ideal.span {t} ≠ ⊤ := by
          intro h
          have hu : IsUnit t := by simpa [Ideal.span_singleton_eq_top] using h
          apply hF
          have hm : IsLocalRing.maximalIdeal R = ⊥ := by
            rw [eq_bot_iff]; intro a ha
            have := htm a ha
            simpa [hu.mul_left_eq_zero] using this
          exact (IsLocalRing.isField_iff_maximalIdeal_eq).2 hm
        haveI : Nontrivial (R ⧸ Ideal.span {t}) := Ideal.Quotient.nontrivial_iff.2 htop
        haveI : IsLocalRing (R ⧸ Ideal.span {t}) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
        obtain ⟨n1, hn1⟩ := (GlobalTheory.T.isArtinianLocal_length_finite_and_exists_socle_elem (R ⧸ Ideal.span {t})).1
        have hlt' : n1 < n := by
          rw [hn0, hn1] at hlt; rw [hn0] at hlen
          exact lt_of_lt_of_le (by exact_mod_cast hlt) (by exact_mod_cast hlen)
        have IH := ih n1 hlt' (R ⧸ Ideal.span {t}) (le_of_eq hn1)
        exact ⟨GlobalTheory.T.artinian_lift_axes_wedge R t _ (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective (Ideal.mk_ker) ht0 htm FF
            (fun B _ g hB hs ↦ IH B g hB hs) A g hA hsm,
          GlobalTheory.T.artinian_lift_axes_wedge_local R t _ (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective (Ideal.mk_ker) ht0 htm FF
            (fun B _ g hB hs ↦ (IH B g hB hs).2) A g hA hsm⟩
  obtain ⟨n, hn⟩ := (GlobalTheory.T.isArtinianLocal_length_finite_and_exists_socle_elem R).1
  have h1 := (key n R (le_of_eq hn) A g hA hsm).1 k σ hσ X₀ s₀ ψ w
  exact ⟨h1, GlobalTheory.T.surjective_pullHO2_of_pullHO1 _ _ _ _ _ _ _ _ w.w h1 (GlobalTheory.T.closed_fibre_pull_h1_abelian FF R A g hA hsm k σ X₀ s₀ ψ w)⟩

end GlobalTheory.AbCoh
end
end
end
