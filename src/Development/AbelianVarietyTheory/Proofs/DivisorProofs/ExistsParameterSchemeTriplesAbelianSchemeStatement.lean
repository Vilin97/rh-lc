module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesSurjectiveFibrewiseDenseOpenStatement
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
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
import Mathlib.Tactic.Linter.Style
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyIntegralOfIsOpenImmersionCompSurjec

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem geometricallyIntegral_of_isOpenImmersion_comp_surjective :
    ∀ (O Z T : Scheme.{0}) (j : O ⟶ Z) (f : Z ⟶ T) [IsOpenImmersion j] [GeometricallyIntegral f], Surjective (j ≫ f) → GeometricallyIntegral (j ≫ f) := by
  intro O Z T j f _ _ hs
  refine ⟨fun {K} _ y P fst snd h => ?_⟩
  have hZf : IsIntegral (pullback f y) :=
    GeometricallyIntegral.geometrically_isIntegral (f := f) y _ _ (IsPullback.of_hasPullback f y)
  let fst' : P ⟶ pullback f y := pullback.lift (fst ≫ j) snd (by rw [Category.assoc]; exact h.w)
  have sq : IsPullback fst fst' j (pullback.fst f y) := by
    refine IsPullback.of_bot (v₂₁ := pullback.snd f y) (v₂₂ := f) (h₃₁ := y) ?_ (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback f y)
    have e : fst' ≫ pullback.snd f y = snd := pullback.lift_snd _ _ _
    rw [e]; exact h
  have : IsOpenImmersion fst' := MorphismProperty.of_isPullback (P := @IsOpenImmersion) sq inferInstance
  have hsn : Surjective snd := MorphismProperty.of_isPullback (P := @Surjective) h hs
  have : Nonempty P := by
    obtain ⟨z, -⟩ := snd.surjective (Nonempty.some inferInstance : Spec (.of K))
    exact ⟨z⟩
  exact isIntegral_of_isOpenImmersion fst'

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyIntegralOfIsOpenImmersionCompSurjecStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.geometricallyIntegral_comp_of_isOpenImmersion_surjective : ∀ (O Z T : Scheme.{0}) (j : O ⟶ Z) (f : Z ⟶ T) [IsOpenImmersion j] [GeometricallyIntegral f], Surjective (j ≫ f) → GeometricallyIntegral (j ≫ f) := by
  first | exact @GlobalTheory.geometricallyIntegral_of_isOpenImmersion_comp_surjective | exact GlobalTheory.geometricallyIntegral_of_isOpenImmersion_comp_surjective | (intros; apply GlobalTheory.geometricallyIntegral_of_isOpenImmersion_comp_surjective <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsParameterSchemeTriplesAbelianScheme

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ParamTriple

theorem exists_param : ∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S] (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (V : A.left.Opens), (∀ s : S, ∃ x ∈ V, A.hom x = s) → ∃ (Y : Over S) (x a v : Y ⟶ A) (p : Y.left ⟶ V.toScheme) (e : V.toScheme ⟶ (x.left ⁻¹ᵁ V).toScheme), IsIntegral Y.left ∧ Smooth x.left ∧ Surjective x.left ∧ p ≫ V.ι = v.left ∧ (∀ y, (x * a).left y ∈ V ∧ (x * a⁻¹).left y ∈ V ∧ (v * a).left y ∈ V ∧ (v * a⁻¹).left y ∈ V) ∧ Smooth ((x.left ⁻¹ᵁ V).ι ≫ p) ∧ GeometricallyIntegral ((x.left ⁻¹ᵁ V).ι ≫ p) ∧ e ≫ (x.left ⁻¹ᵁ V).ι ≫ p = 𝟙 _ := by
  intro S _ _ A _ hA V hV
  have := hA.smooth
  have : GeometricallyIntegral A.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hA.smooth hA.geomConnected
  have hAA := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have := hAA.smooth
  have : GeometricallyIntegral (A ⊗ A).hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hAA.smooth hAA.geomConnected
  let B : Over S := Over.mk (V.ι ≫ A.hom)
  let j : B ⟶ A := Over.homMk V.ι
  have hBs : Smooth B.hom := by dsimp [B]; infer_instance
  have hBsurj : Surjective (V.ι ≫ A.hom) := ⟨fun s => by
    obtain ⟨x, hx, rfl⟩ := hV s
    exact ⟨⟨x, hx⟩, rfl⟩⟩
  have hBgi : GeometricallyIntegral B.hom := GlobalTheory.T.geometricallyIntegral_comp_of_isOpenImmersion_surjective _ _ _ V.ι A.hom hBsurj
  let P : Over S := (A ⊗ A) ⊗ B
  let X : P ⟶ A := fst _ _ ≫ fst A A
  let Aa : P ⟶ A := fst _ _ ≫ snd A A
  let Vv : P ⟶ A := snd _ _ ≫ j
  let O : P.left.Opens := (X * Aa).left ⁻¹ᵁ V ⊓ (X * Aa⁻¹).left ⁻¹ᵁ V ⊓ (Vv * Aa).left ⁻¹ᵁ V ⊓
    (Vv * Aa⁻¹).left ⁻¹ᵁ V
  have hsurj : Surjective (O.ι ≫ X.left) :=
    GlobalTheory.T.exists_translates_surjective_fibrewise_dense_open S A hA V B j (fun b => b.2) hBs hBgi
  let Y : Over S := Over.mk (O.ι ≫ P.hom)
  let i : Y ⟶ P := Over.homMk O.ι
  have hmem : ∀ (f : P ⟶ A), O ≤ f.left ⁻¹ᵁ V → ∀ y, (i ≫ f).left y ∈ V := by
    intro f hf y
    exact hf y.2

  let s : B ⟶ P := lift (lift j 1) (𝟙 B)
  have hsX : s ≫ X = j := by simp [s, X]
  have hsA : s ≫ Aa = 1 := by simp [s, Aa]
  have hsV : s ≫ Vv = j := by simp [s, Vv]
  have hsO : ∀ b, s.left b ∈ O := by
    intro b
    have h1 : ∀ f : P ⟶ A, s ≫ f = j → s.left b ∈ f.left ⁻¹ᵁ V := by
      intro f hf
      show (s.left ≫ f.left) b ∈ V
      rw [← Over.comp_left, hf]
      exact b.2
    refine ⟨⟨⟨h1 _ ?_, h1 _ ?_⟩, h1 _ ?_⟩, h1 _ ?_⟩
    · rw [MonObj.comp_mul, hsX, hsA, _root_.mul_one]
    · rw [MonObj.comp_mul, GrpObj.comp_inv, hsX, hsA, inv_one, _root_.mul_one]
    · rw [MonObj.comp_mul, hsV, hsA, _root_.mul_one]
    · rw [MonObj.comp_mul, GrpObj.comp_inv, hsV, hsA, inv_one, _root_.mul_one]
  have hrO : Set.range s.left ⊆ Set.range O.ι := by
    rw [Scheme.Opens.range_ι]; rintro _ ⟨b, rfl⟩; exact hsO b
  let e0 : V.toScheme ⟶ O.toScheme := IsOpenImmersion.lift O.ι s.left hrO
  have he0 : e0 ≫ O.ι = s.left := IsOpenImmersion.lift_fac _ _ _
  let x : Y ⟶ A := i ≫ X
  let a : Y ⟶ A := i ≫ Aa
  let v : Y ⟶ A := i ≫ Vv
  let p : Y.left ⟶ V.toScheme := O.ι ≫ (snd (A ⊗ A) B).left
  have hxl : x.left = O.ι ≫ X.left := rfl
  have hre : Set.range e0 ⊆ Set.range (x.left ⁻¹ᵁ V).ι := by
    rw [Scheme.Opens.range_ι]; rintro _ ⟨b, rfl⟩
    show (e0 ≫ x.left) b ∈ V
    rw [hxl, ← Category.assoc, he0, ← Over.comp_left, hsX]
    exact b.2
  let e : V.toScheme ⟶ (x.left ⁻¹ᵁ V).toScheme := IsOpenImmersion.lift _ e0 hre
  have he : e ≫ (x.left ⁻¹ᵁ V).ι = e0 := IsOpenImmersion.lift_fac _ _ _
  have hsec : e ≫ ((x.left ⁻¹ᵁ V).ι ≫ O.ι) ≫ pullback.snd (A ⊗ A).hom B.hom = 𝟙 _ := by
    rw [← Category.assoc, ← Category.assoc, he, he0]
    show (s ≫ snd (A ⊗ A) B).left = _
    rw [lift_snd]; rfl
  obtain ⟨s0⟩ := (inferInstance : Nonempty S)
  obtain ⟨x0, hx0, -⟩ := hV s0
  have : Nonempty V.toScheme := ⟨⟨x0, hx0⟩⟩
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian A.hom
  have : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have : IsLocallyNoetherian V.toScheme := LocallyOfFiniteType.isLocallyNoetherian (V.ι ≫ A.hom)
  have : Flat (A ⊗ A).hom := inferInstance
  have : UniversallyOpen (A ⊗ A).hom := inferInstance
  have : IsIntegral B.left := ‹IsIntegral V.toScheme›
  have : IsLocallyNoetherian B.left := ‹IsLocallyNoetherian V.toScheme›
  have : IsIntegral P.left := inferInstanceAs (IsIntegral (pullback (A ⊗ A).hom B.hom))
  obtain ⟨b0⟩ := (inferInstance : Nonempty V.toScheme)
  have : Nonempty O.toScheme := ⟨⟨s.left b0, hsO b0⟩⟩
  have hYi : IsIntegral O.toScheme := isIntegral_of_isOpenImmersion O.ι
  have hgi : GeometricallyIntegral (((x.left ⁻¹ᵁ V).ι ≫ O.ι) ≫ pullback.snd (A ⊗ A).hom B.hom) := by
    refine GlobalTheory.T.geometricallyIntegral_comp_of_isOpenImmersion_surjective _ _ _ _ _ ?_
    have : Surjective (e ≫ ((x.left ⁻¹ᵁ V).ι ≫ O.ι) ≫ pullback.snd (A ⊗ A).hom B.hom) := by
      rw [hsec]; infer_instance
    exact Surjective.of_comp e _
  have hxa : x * a = i ≫ (X * Aa) := by simp only [x, a, MonObj.comp_mul]
  have hxa' : x * a⁻¹ = i ≫ (X * Aa⁻¹) := by simp only [x, a, MonObj.comp_mul, GrpObj.comp_inv]
  have hva : v * a = i ≫ (Vv * Aa) := by simp only [v, a, MonObj.comp_mul]
  have hva' : v * a⁻¹ = i ≫ (Vv * Aa⁻¹) := by simp only [v, a, MonObj.comp_mul, GrpObj.comp_inv]
  refine ⟨Y, x, a, v, p, e, hYi, ?_, hsurj, ?_, fun y => ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · show Smooth (O.ι ≫ pullback.fst (A ⊗ A).hom B.hom ≫ pullback.fst A.hom A.hom)
    infer_instance
  · show (O.ι ≫ (snd (A ⊗ A) B).left) ≫ V.ι = O.ι ≫ (snd (A ⊗ A) B ≫ j).left
    rw [Category.assoc, Over.comp_left]; rfl
  · rw [hxa]; exact hmem _ (fun z hz => hz.1.1.1) y
  · rw [hxa']; exact hmem _ (fun z hz => hz.1.1.2) y
  · rw [hva]; exact hmem _ (fun z hz => hz.1.2) y
  · rw [hva']; exact hmem _ (fun z hz => hz.2) y
  · show Smooth ((x.left ⁻¹ᵁ V).ι ≫ O.ι ≫ pullback.snd (A ⊗ A).hom B.hom)
    infer_instance
  · show GeometricallyIntegral ((x.left ⁻¹ᵁ V).ι ≫ O.ι ≫ pullback.snd (A ⊗ A).hom B.hom)
    rw [← Category.assoc]; exact hgi
  · show e ≫ (x.left ⁻¹ᵁ V).ι ≫ O.ι ≫ pullback.snd (A ⊗ A).hom B.hom = 𝟙 _
    rw [← hsec]; simp only [Category.assoc]

end GlobalTheory.ParamTriple
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsParameterSchemeTriplesAbelianSchemeStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_parameterScheme_triples_abelianScheme : ∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S] (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (V : A.left.Opens), (∀ s : S, ∃ x ∈ V, A.hom x = s) → ∃ (Y : Over S) (x a v : Y ⟶ A) (p : Y.left ⟶ V.toScheme) (e : V.toScheme ⟶ (x.left ⁻¹ᵁ V).toScheme), IsIntegral Y.left ∧ Smooth x.left ∧ Surjective x.left ∧ p ≫ V.ι = v.left ∧ (∀ y, (x * a).left y ∈ V ∧ (x * a⁻¹).left y ∈ V ∧ (v * a).left y ∈ V ∧ (v * a⁻¹).left y ∈ V) ∧ Smooth ((x.left ⁻¹ᵁ V).ι ≫ p) ∧ GeometricallyIntegral ((x.left ⁻¹ᵁ V).ι ≫ p) ∧ e ≫ (x.left ⁻¹ᵁ V).ι ≫ p = 𝟙 _ := by
  first | exact @GlobalTheory.ParamTriple.exists_param | exact GlobalTheory.ParamTriple.exists_param | (intros; apply GlobalTheory.ParamTriple.exists_param <;> assumption)
end
end
