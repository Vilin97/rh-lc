module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndKerBaseChangeOfForallResidueField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeSpecialFibreCohomologyLiftArtinianStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSquareAffineH1VanishStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyWedgeNoPrimitiveH2Statement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeBaseChangeAndSquareStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpObjIsGrpPullbackOfIsPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalFunctionsConstantAfterBaseChangeOfAbelianSStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureCohomologyResidueFieldFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyPullbackCompCupIdStatement
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSquareAffineH1Vanish
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AxesVanishingNoetherianAbelianStatement
import Mathlib.Tactic.TypeStar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeNoPrimitiveO2

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh.NoPrimNoeth

theorem injective_of_algClosure (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] (N : Type) [AddCommGroup N] [Module R N] [Module.Finite R N]
    [Module.Projective R N] (f : M →ₗ[R] N)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra R K], Function.Injective (f.baseChange K)) :
    Function.Injective f := by
  obtain ⟨g, hg⟩ : ∃ g : N →ₗ[R] M, g ∘ₗ f = LinearMap.id := by
    refine GlobalTheory.split_injective_of_forall_lTensor_residueField_injective f fun m hm => ?_
    let k := AlgebraicClosure m.ResidueField
    have hinj := h k
    have e : (AlgebraTensorModule.cancelBaseChange R m.ResidueField m.ResidueField k N) ∘
          ((f.baseChange m.ResidueField).lTensor k) =
        (f.lTensor k) ∘ (AlgebraTensorModule.cancelBaseChange R
          m.ResidueField m.ResidueField k M) := by
      funext x
      exact (LinearMap.congr_fun (AlgebraTensorModule.lTensor_comp_cancelBaseChange R
        m.ResidueField m.ResidueField (M := k) f) x).symm
    have h1 : Function.Injective ((f.baseChange m.ResidueField).lTensor k) :=
      Function.Injective.of_comp (e ▸ (hinj.comp (LinearEquiv.injective _)))
    haveI : Module.FaithfullyFlat m.ResidueField k :=
      (fun (F L : Type) [Field F] [Field L] [Algebra F L] ↦ (inferInstance : Module.FaithfullyFlat F L)) _ _
    exact (Module.FaithfullyFlat.lTensor_injective_iff_injective m.ResidueField k _).1 h1
  exact Function.LeftInverse.injective (g := g) fun x ↦ LinearMap.congr_fun hg x

theorem abelian_scheme_second_cohomology_finite_projective (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) :
    (Module.Finite R (HO2 A.hom) ∧ Module.Projective R (HO2 A.hom)) ∧ StructureSheafH2BaseChange A.hom := by
  have hsm : Smooth A.hom := SmoothOfRelativeDimension.smooth g A.hom
  have H := GlobalTheory.T.structure_cohomology_residue_field_fibre R A.left A.hom hA.proper inferInstance (GlobalTheory.T.globalFunctionsConstantAfterBaseChange_of_abelianScheme R A hA) (by
    intro R' _ _ _ _ k _ _ α hα X' s' φ X₀ s₀ ψ hp w
    obtain ⟨_, -, h1, h2⟩ := GlobalTheory.T.exists_grpObj_isGrpPullback_of_isPullback' R R' (algebraMap R R') A X' s' φ hp
    exact GlobalTheory.T.abelianSchemeSpecialFibre_cohomology_lift_artinian R' (Over.mk s' : Over (Sp R')) g (h1 hA) (h2 g hg) k (α : R' →+* k) hα X₀ s₀ ψ w)
  exact ⟨H.2.1, H.2.2.2⟩

theorem pull_comm {R K : Type} [CommRing R] [CommRing K] {σ : R →+* K} {A A' : Over (Sp R)} {B B' : Over (Sp K)}
    {pr : B.left ⟶ A.left} {pr' : B'.left ⟶ A'.left} (h : pr ≫ A.hom = B.hom ≫ spMap σ)
    (h' : pr' ≫ A'.hom = B'.hom ≫ spMap σ) (f : A' ⟶ A) (f' : B' ⟶ B) (e : f'.left ≫ pr = pr' ≫ f.left)
    (c : HO2 A.hom) : pullHO2 h' (structureSheafH2Pullback f c) = structureSheafH2Pullback f' (pullHO2 h c) := by
  have h'' : (pr' ≫ f.left) ≫ A.hom = B'.hom ≫ spMap σ := by rw [Category.assoc, Over.w f, h']
  have a1 := (GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id.1 R R _ _ A.hom A'.hom (RingHom.id R) f.left (ovw f) K _ B'.hom σ pr' h' σ _ h''
    rfl (fun _ ↦ rfl)).2.1 c
  have a2 := (GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id.1 R K _ _ A.hom B.hom σ pr h K _ B'.hom (RingHom.id K) f'.left (ovw f') σ _ h''
    e.symm (fun _ ↦ rfl)).2.1 c
  exact a1.trans a2.symm

theorem noPrimO2_of_isNoetherianRing : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → NoPrimitiveStructureSheafH2 A := by
  intro R _ _ A _ g hA hg
  obtain ⟨⟨_, _⟩, bc⟩ := abelian_scheme_second_cohomology_finite_projective R A g hA hg
  obtain ⟨hA2, hg2⟩ := (GlobalTheory.T.abelian_square_affine_h1_vanish R).1 A g hA hg
  obtain ⟨⟨_, _⟩, bc2⟩ := abelian_scheme_second_cohomology_finite_projective R (A ⊗ A) (g + g) hA2 hg2
  let D : HO2 A.hom →ₗ[R] HO2 (A ⊗ A).hom := structureSheafH2Pullback μ[A] - structureSheafH2Pullback (fst A A) - structureSheafH2Pullback (snd A A)
  have hD : Function.Injective D := by
    refine injective_of_algClosure R _ _ D fun K _ _ _ ↦ ?_
    obtain ⟨B, _, pr, pr', hB, hgB, p1, p2, eμ, e1, e2, -, -⟩ := GlobalTheory.T.exists_abelianScheme_baseChange_and_square R K A g hA hg
    obtain ⟨e, he⟩ := bc K _ _ _ p1
    obtain ⟨e', he'⟩ := bc2 K _ _ _ p2
    have hN := (GlobalTheory.T.abelian_variety_wedge_no_primitive_h2 K B g hB hgB).2
    let DB : HO2 B.hom →ₗ[K] HO2 (B ⊗ B).hom := structureSheafH2Pullback μ[B] - structureSheafH2Pullback (fst B B) - structureSheafH2Pullback (snd B B)
    have key : ∀ x, e' (D.baseChange K x) = DB (e x) := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
      | tmul a c =>
        have : a ⊗ₜ[R] c = a • ((1 : K) ⊗ₜ[R] c) := by rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
        rw [this, map_smul, map_smul, map_smul, map_smul, LinearMap.baseChange_tmul, he, he']
        congr 1
        simp only [D, DB, LinearMap.sub_apply, map_sub]
        rw [pull_comm p1.w p2.w _ _ eμ, pull_comm p1.w p2.w _ _ e1, pull_comm p1.w p2.w _ _ e2]
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    have h0 : DB (e x) = 0 := by rw [← key, hx, map_zero]
    have h1 : e x = 0 := hN _ (by
      simp only [DB, LinearMap.sub_apply] at h0
      rw [sub_sub, sub_eq_zero] at h0
      exact h0)
    exact e.map_eq_zero_iff.1 h1
  intro z hz
  refine (injective_iff_map_eq_zero D).1 hD z ?_
  simp only [D, LinearMap.sub_apply]
  rw [hz]; abel

end GlobalTheory.AbCoh.NoPrimNoeth
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeNoPrimitiveO2Statement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelian_scheme_no_primitive_O2 : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → NoPrimitiveStructureSheafH2 A := by
  first | exact @GlobalTheory.AbCoh.NoPrimNoeth.noPrimO2_of_isNoetherianRing | exact GlobalTheory.AbCoh.NoPrimNoeth.noPrimO2_of_isNoetherianRing | (intros; apply GlobalTheory.AbCoh.NoPrimNoeth.noPrimO2_of_isNoetherianRing <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupSelfZeroAbelianH1

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem pO1_comp {R : Type} [CommRing R] {Z Y A : Over (Sp R)} (i : Z ⟶ Y) (f : Y ⟶ A) (x : HO1 A.hom) :
    pO1 i (pO1 f x) = pO1 (i ≫ f) x :=
  ((GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id).1 _ _ _ _ _ _ _ _ (ovw f) _ _ _ _ _ (ovw i) _ _ (ovw (i ≫ f)) (Over.comp_left _ _ _ _ _)
    (fun _ ↦ rfl)).1 x

theorem pO1_id {R : Type} [CommRing R] {A : Over (Sp R)} (x : HO1 A.hom) : pO1 (𝟙 A) x = x :=
  ((GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id).2.2 R A).1 x

theorem pO1_unit_eq_zero {R : Type} [CommRing R] (x : HO1 (𝟙_ (Over (Sp R))).hom) : x = 0 := by
  have : IsAffine (𝟙_ (Over (Sp R))).left := by
    change IsAffine (Sp R); infer_instance
  exact (GlobalTheory.Obs.sq_abelian_and_affine_H1 R).2 _ _ x

theorem pO1_toUnit_comp {R : Type} [CommRing R] {Y A : Over (Sp R)} (f : 𝟙_ (Over (Sp R)) ⟶ A) (x : HO1 A.hom) :
    pO1 (toUnit Y ≫ f) x = 0 := by
  rw [← pO1_comp, pO1_unit_eq_zero (pO1 f x), map_zero]

theorem primO1_of_axesO1 {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] (h : AxesVanishingStructureSheafDegOne A) : StructureSheafH1Primitive A := by
  intro x
  rw [← sub_eq_zero, sub_add_eq_sub_sub]
  apply h
  · rw [map_sub, map_sub, pO1_comp, pO1_comp, pO1_comp, lift_comp_one_right, lift_fst, lift_snd,
      pO1_toUnit_comp, pO1_id]
    simp
  · rw [map_sub, map_sub, pO1_comp, pO1_comp, pO1_comp, lift_comp_one_left, lift_fst, lift_snd,
      pO1_toUnit_comp, pO1_id]
    simp

theorem cup_add_cup_swap {R : Type} [CommRing R] {C : Type*} [Category C] (F : C ⥤ CommAlgCat.{0} R)
    (a b : CatCoh.H1 F) : cup F a b + cup F b a = 0 := by
  obtain ⟨a, rfl⟩ := GlobalTheory.CatCoh.H1.mk_surjective F a
  obtain ⟨b, rfl⟩ := GlobalTheory.CatCoh.H1.mk_surjective F b
  rw [GlobalTheory.CatCoh.cup_mk, GlobalTheory.CatCoh.cup_mk, ← map_add (f := _)]
  refine GlobalTheory.CatCoh.H2.mk_eq_zero.2 ⟨fun T T' φ ↦ -(a.1 T T' φ * b.1 T T' φ), ?_⟩
  funext T T' T'' φ ψ
  simp only [GlobalTheory.CatCoh.d1_apply, Submodule.coe_add, Pi.add_apply, GlobalTheory.CatCoh.cupZ_apply, GlobalTheory.CatCoh.Z1.comp a,
    GlobalTheory.CatCoh.Z1.comp b, map_mul, map_neg]
  ring

theorem cup_self_eq_zero_of_prim {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] (hP : StructureSheafH1Primitive A)
    (hN : NoPrimitiveStructureSheafH2 A) (x : HO1 A.hom) : cup _ x x = 0 := by
  have key : ∀ f : A ⊗ A ⟶ A, structureSheafH2Pullback f (cup _ x x) = cup _ (pO1 f x) (pO1 f x) := fun f ↦
    ((GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id).2.1 _ _ _ _ _ _ _ _ (ovw f)).1 x x
  apply hN
  rw [key, key, key, hP x]
  simp only [map_add (f := _), LinearMap.add_apply]
  have := cup_add_cup_swap (OAff (A ⊗ A).hom) (pO1 (fst A A) x) (pO1 (snd A A) x)
  linear_combination (norm := module) this

theorem cup_self_eq_zero_of_isAbelianScheme : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R))
    [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ x : HO1 A.hom, cup _ x x = 0 := by
  intro R _ _ A _ g hA hg x
  exact cup_self_eq_zero_of_prim A (primO1_of_axesO1 A (GlobalTheory.T.axes_vanishing_noetherian_abelian R A g hA hg)) (GlobalTheory.T.abelian_scheme_no_primitive_O2 R A g hA hg) x

end GlobalTheory.AbCoh
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupSelfZeroAbelianH1Statement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.cup_self_zero_abelian_h1 : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ x : HO1 A.hom, cup _ x x = 0 := by
  first | exact @GlobalTheory.AbCoh.cup_self_eq_zero_of_isAbelianScheme | exact GlobalTheory.AbCoh.cup_self_eq_zero_of_isAbelianScheme | (intros; apply GlobalTheory.AbCoh.cup_self_eq_zero_of_isAbelianScheme <;> assumption)
end
end
