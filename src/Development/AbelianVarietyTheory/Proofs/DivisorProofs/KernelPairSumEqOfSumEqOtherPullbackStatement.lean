module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentDatumOfDescendedMultiplicationImpor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairUOver
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.Combinatorics.Quiver.ReflQuiver
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomOfSumMapCompFixingNearOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackDescentSquarePairToOpenSquareStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NearOpenSumEqEmbeddingDescendedMultiplicationStatement
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyIrreducibleCompOfIsOpenImmersion

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option autoImplicit false

namespace GlobalTheory.OpenGeomIrr

theorem geometricallyIrreducible_comp_of_isOpenImmersion : ∀ (T W X : Scheme.{0}) (j : W ⟶ X), IsOpenImmersion j →
    ∀ (f : X ⟶ T), GeometricallyIrreducible f → Surjective (j ≫ f) → GeometricallyIrreducible (j ≫ f) := by
  intro T W X j hj f hf hs
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x => ?_⟩
  have h₁ : IrreducibleSpace ↥(Limits.pullback f x) :=
    GeometricallyIrreducible.geometrically_irreducibleSpace _ _ _ (.of_hasPullback _ _)
  have hne : Nonempty ↥(Limits.pullback (j ≫ f) x) := by
    obtain ⟨p⟩ : Nonempty ↥(Spec (.of K)) := inferInstance
    obtain ⟨z, -⟩ := (Limits.pullback.snd (j ≫ f) x).surjective p
    exact ⟨z⟩
  let e := pullbackRightPullbackFstIso f x j
  have hne' : Nonempty ↥(Limits.pullback j (Limits.pullback.fst f x)) := ⟨e.inv hne.some⟩
  have h₂ : IrreducibleSpace ↥(Limits.pullback j (Limits.pullback.fst f x)) :=
    (Limits.pullback.snd j (Limits.pullback.fst f x)).isOpenEmbedding.irreducibleSpace
  exact e.hom.homeomorph.irreducibleSpace_iff.1 h₂

end GlobalTheory.OpenGeomIrr
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyIrreducibleCompOfIsOpenImmersionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.geometricallyIrreducible_comp_of_isOpenImmersion_surjective : ∀ (T W X : Scheme.{0}) (j : W ⟶ X), IsOpenImmersion j → ∀ (f : X ⟶ T), GeometricallyIrreducible f → Surjective (j ≫ f) → GeometricallyIrreducible (j ≫ f) := by
  first | exact @GlobalTheory.OpenGeomIrr.geometricallyIrreducible_comp_of_isOpenImmersion | exact GlobalTheory.OpenGeomIrr.geometricallyIrreducible_comp_of_isOpenImmersion | (intros; apply GlobalTheory.OpenGeomIrr.geometricallyIrreducible_comp_of_isOpenImmersion <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOpenContainingClosedFibreSmoothSquare

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.NearSurj

theorem surjective_of_open_closedFibre : ∀ {R : Type} [CommRing R] [IsLocalRing R] (U : Over (Sp R)), Smooth U.hom → Surjective U.hom → ∀ (V : (U ⊗ U).left.Opens), (∀ z : (U ⊗ U).left, (U ⊗ U).hom z = closedPoint R → z ∈ V) → Surjective (V.ι ≫ (U ⊗ U).hom) := by
  intro R _ _ U hs hsu V hV
  have : Smooth (U ⊗ U).hom := inferInstanceAs (Smooth (pullback.fst U.hom U.hom ≫ U.hom))
  obtain ⟨u, hu⟩ := U.hom.surjective (closedPoint R)
  let d : U.left ⟶ (U ⊗ U).left := pullback.lift (𝟙 _) (𝟙 _) rfl
  have hd : (U ⊗ U).hom (d u) = closedPoint R := by
    rw [← hu, ← Scheme.Hom.comp_apply]
    change (pullback.lift (𝟙 U.left) (𝟙 U.left) rfl ≫ pullback.fst U.hom U.hom ≫ U.hom) u = _
    rw [pullback.lift_fst_assoc, Category.id_comp]
  have hmem : d u ∈ V := hV _ hd
  have ho : IsOpenMap (V.ι ≫ (U ⊗ U).hom) := (V.ι ≫ (U ⊗ U).hom).isOpenMap
  refine ⟨fun r => ?_⟩
  obtain ⟨y, hy⟩ : d u ∈ Set.range V.ι := by rw [Scheme.Opens.range_ι]; exact hmem
  have h₂ : (V.ι ≫ (U ⊗ U).hom) y = closedPoint R := by
    rw [Scheme.Hom.comp_apply, hy]; exact hd
  exact (IsLocalRing.specializes_closedPoint r).mem_open ho.isOpen_range ⟨_, h₂⟩

end GlobalTheory.Mum.NearSurj
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOpenContainingClosedFibreSmoothSquareStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.surjective_open_containing_closedFibre_smooth_square : ∀ {R : Type} [CommRing R] [IsLocalRing R] (U : Over (Sp R)), Smooth U.hom → Surjective U.hom → ∀ (V : (U ⊗ U).left.Opens), (∀ z : (U ⊗ U).left, (U ⊗ U).hom z = closedPoint R → z ∈ V) → Surjective (V.ι ≫ (U ⊗ U).hom) := by
  first | exact @GlobalTheory.Mum.NearSurj.surjective_of_open_closedFibre | exact GlobalTheory.Mum.NearSurj.surjective_of_open_closedFibre | (intros; apply GlobalTheory.Mum.NearSurj.surjective_of_open_closedFibre <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelPairSumEqOfSumEqOtherPullback

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.DescKP

variable {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S} [GrpObj G]

theorem ι_mem {X : Scheme.{0}} (U : X.Opens) (x : U.toScheme) : U.ι x ∈ U := x.2

theorem surjective_Wk (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π)
    (V : (N.U ⊗ N.U).left.Opens) (h : Surjective ((VT N V).ι ≫ (Desc.UT N ⊗ Desc.UT N).hom)) :
    Surjective ((Wk N p hp V).ι ≫ (Pk N p hp).hom) := by
  obtain ⟨z, h1, h2⟩ := exists_lift N p hp (VT N V).toScheme (VT N V).ι (VT N V).ι rfl
  have hr : Set.range z ⊆ Set.range (Wk N p hp V).ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    refine ⟨?_, ?_⟩
    · show (abP N p hp).left (z x) ∈ VT N V
      rw [← Scheme.Hom.comp_apply, h1]; exact ι_mem _ x
    · show (cdP N p hp).left (z x) ∈ VT N V
      rw [← Scheme.Hom.comp_apply, h2]; exact ι_mem _ x
  let z' := IsOpenImmersion.lift (Wk N p hp V).ι z hr
  have e : z' ≫ (Wk N p hp V).ι ≫ (Pk N p hp).hom = (VT N V).ι ≫ (Desc.UT N ⊗ Desc.UT N).hom := by
    rw [← Category.assoc, IsOpenImmersion.lift_fac, ← h1, Category.assoc, Over.w (abP N p hp)]
  have : Surjective (z' ≫ (Wk N p hp V).ι ≫ (Pk N p hp).hom) := by rw [e]; exact h
  exact Surjective.of_comp z' _

theorem agree_Wk (N : Near π G) (V : (N.U ⊗ N.U).left.Opens) (m : V.toScheme ⟶ N.U.left)
    (hm : m ≫ N.U.hom = V.ι ≫ (N.U ⊗ N.U).hom) (p p' : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π)
    (hp' : p' ≫ π = pullback.fst π π ≫ π)
    (h : (VT N V).ι ≫ (Desc.sum N p hp).left = mT N V m hm ≫ (Desc.emb N p hp).left)
    (h' : (VT N V).ι ≫ (Desc.sum N p' hp').left = mT N V m hm ≫ (Desc.emb N p' hp').left) :
    (Wk N p hp V).ι ≫ (abP N p hp ≫ Desc.sum N p' hp').left =
      (Wk N p hp V).ι ≫ (cdP N p hp ≫ Desc.sum N p' hp').left := by
  let a' := IsOpenImmersion.lift (VT N V).ι ((Wk N p hp V).ι ≫ (abP N p hp).left) (by
    rintro _ ⟨x, rfl⟩; rw [Scheme.Opens.range_ι]; exact (ι_mem _ x).1)
  let c' := IsOpenImmersion.lift (VT N V).ι ((Wk N p hp V).ι ≫ (cdP N p hp).left) (by
    rintro _ ⟨x, rfl⟩; rw [Scheme.Opens.range_ι]; exact (ι_mem _ x).2)
  have ea : a' ≫ (VT N V).ι = (Wk N p hp V).ι ≫ (abP N p hp).left := IsOpenImmersion.lift_fac _ _ _
  have ec : c' ≫ (VT N V).ι = (Wk N p hp V).ι ≫ (cdP N p hp).left := IsOpenImmersion.lift_fac _ _ _
  have e0 := congrArg (fun f => (Wk N p hp V).ι ≫ Over.Hom.left f) (abP_sum N p hp)
  simp only [Over.comp_left] at e0
  have hemb := GlobalTheory.Mum.DescHom.isOpenImmersion_emb N p hp
  have e2 : a' ≫ mT N V m hm = c' ≫ mT N V m hm := by
    refine (cancel_mono (Desc.emb N p hp).left).1 ?_
    simp only [Category.assoc]
    rw [← h, ← Category.assoc, ea, ← Category.assoc, ec, Category.assoc, Category.assoc]
    exact e0
  simp only [Over.comp_left]
  rw [← Category.assoc, ← ea, Category.assoc, h', ← Category.assoc, e2, Category.assoc, ← h', ← Category.assoc, ec,
    Category.assoc]

end GlobalTheory.Mum.DescKP


open GlobalTheory.Mum.DescKP in
theorem GlobalTheory.Mum.DescKP.sum_eq_of_sum_eq : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', N.Law → ∀ (p p' : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) (hp' : p' ≫ π = pullback.fst π π ≫ π), ∀ (Z : Scheme.{0}) (g g' : Z ⟶ (Desc.UT N ⊗ Desc.UT N).left), g ≫ (Desc.sum N p hp).left = g' ≫ (Desc.sum N p hp).left → g ≫ (Desc.sum N p' hp').left = g' ≫ (Desc.sum N p' hp').left := by
  intro R _ _ _ _ S π _ _ _ G _ _ hG N hLaw p p' hp hp' Z g g' hgg
  obtain ⟨V, m, hV, hm, hL⟩ := hLaw
  have hlaw := fun (q : pullback π π ⟶ S) (hq : q ≫ π = pullback.fst π π ≫ π) => GlobalTheory.T.nearOpen_sum_eq_embedding_descendedMultiplication N V m hm hL q hq
  have : Smooth N.U.hom := N.smooth
  have : Surjective N.U.hom := DescHom.surjective_near N
  have : Smooth G.hom := hG.smooth
  have : IsSeparated G.hom := hG.separated
  have := DescHom.geometricallyIrreducible_of_semiAbelian G hG

  have sV := GlobalTheory.T.surjective_open_containing_closedFibre_smooth_square N.U N.smooth inferInstance V hV
  have sq : IsPullback (DescKP.pairU N ∣_ V) ((VT N V).ι ≫ (Desc.UT N ⊗ Desc.UT N).hom)
      (V.ι ≫ (N.U ⊗ N.U).hom) (pullback.fst π π ≫ π) :=
    (isPullback_morphismRestrict (DescKP.pairU N) V).paste_vert (GlobalTheory.T.isPullback_descentSquarePairToOpenSquare N)
  have sVT : Surjective ((VT N V).ι ≫ (Desc.UT N ⊗ Desc.UT N).hom) :=
    MorphismProperty.of_isPullback (P := @Surjective) sq sV
  have sW := DescKP.surjective_Wk N p hp V sVT

  have : Smooth (Desc.UT N).hom := inferInstanceAs (Smooth (pullback.snd N.U.hom (pullback.fst π π ≫ π)))
  have : Surjective (Desc.UT N).hom := inferInstanceAs (Surjective (pullback.snd N.U.hom (pullback.fst π π ≫ π)))
  have hGp : GeometricallyIrreducible ((Over.pullback p).obj G).hom :=
    inferInstanceAs (GeometricallyIrreducible (pullback.snd G.hom p))
  have := DescHom.isOpenImmersion_emb N p hp
  have : GeometricallyIrreducible (Desc.UT N).hom := by
    have e : (Desc.emb N p hp).left ≫ ((Over.pullback p).obj G).hom = (Desc.UT N).hom := Over.w _
    have h := GlobalTheory.T.geometricallyIrreducible_comp_of_isOpenImmersion_surjective _ _ _ (Desc.emb N p hp).left inferInstance _ hGp (by rw [e]; infer_instance)
    rwa [e] at h
  have : Smooth (Desc.UT N ⊗ Desc.UT N).hom :=
    inferInstanceAs (Smooth (pullback.fst (Desc.UT N).hom (Desc.UT N).hom ≫ (Desc.UT N).hom))
  have : GeometricallyIrreducible (Desc.UT N ⊗ Desc.UT N).hom :=
    GeometricallyIrreducible.comp (pullback.fst (Desc.UT N).hom (Desc.UT N).hom) (Desc.UT N).hom
  have : Smooth ((Desc.UT N ⊗ Desc.UT N) ⊗ Desc.UT N).hom :=
    inferInstanceAs (Smooth (pullback.fst (Desc.UT N ⊗ Desc.UT N).hom (Desc.UT N).hom ≫ (Desc.UT N ⊗ Desc.UT N).hom))
  have h3 : GeometricallyIrreducible ((Desc.UT N ⊗ Desc.UT N) ⊗ Desc.UT N).hom :=
    GeometricallyIrreducible.comp (pullback.fst (Desc.UT N ⊗ Desc.UT N).hom (Desc.UT N).hom) (Desc.UT N ⊗ Desc.UT N).hom
  have : Surjective (DescKP.Pk N p hp).hom := Surjective.of_comp (DescKP.Wk N p hp V).ι _
  have : Smooth (DescKP.Pk N p hp).hom :=
    inferInstanceAs (Smooth (pullback.snd (Desc.emb N p hp).left (DescKP.trip N p hp).left ≫
      ((Desc.UT N ⊗ Desc.UT N) ⊗ Desc.UT N).hom))
  have : GeometricallyIrreducible (DescKP.Pk N p hp).hom :=
    GlobalTheory.T.geometricallyIrreducible_comp_of_isOpenImmersion_surjective _ _ _ (pullback.snd (Desc.emb N p hp).left (DescKP.trip N p hp).left) inferInstance _ h3
      (inferInstanceAs (Surjective (DescKP.Pk N p hp).hom))
  have : IsSeparated ((Over.pullback p').obj G).hom := inferInstanceAs (IsSeparated (pullback.snd G.hom p'))

  let j : Over.mk ((DescKP.Wk N p hp V).ι ≫ (DescKP.Pk N p hp).hom) ⟶ DescKP.Pk N p hp :=
    Over.homMk (DescKP.Wk N p hp V).ι rfl
  have : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion (DescKP.Wk N p hp V).ι)
  have : Surjective (Over.mk ((DescKP.Wk N p hp V).ι ≫ (DescKP.Pk N p hp).hom)).hom := sW
  have hF : DescKP.abP N p hp ≫ Desc.sum N p' hp' = DescKP.cdP N p hp ≫ Desc.sum N p' hp' := by
    refine DescHom.ext_of_open j ?_
    ext1
    exact DescKP.agree_Wk N V m hm p p' hp hp' (hlaw p hp) (hlaw p' hp')
  obtain ⟨z, hz, hz'⟩ := DescKP.exists_lift N p hp Z g g' hgg
  rw [← hz, ← hz', Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, hF]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelPairSumEqOfSumEqOtherPullbackStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.kernelPair_sum_eq_of_sum_eq_other_pullback : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', N.Law → ∀ (p p' : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) (hp' : p' ≫ π = pullback.fst π π ≫ π), ∀ (Z : Scheme.{0}) (g g' : Z ⟶ (Desc.UT N ⊗ Desc.UT N).left), g ≫ (Desc.sum N p hp).left = g' ≫ (Desc.sum N p hp).left → g ≫ (Desc.sum N p' hp').left = g' ≫ (Desc.sum N p' hp').left := by
  first | exact @GlobalTheory.Mum.DescKP.sum_eq_of_sum_eq | exact GlobalTheory.Mum.DescKP.sum_eq_of_sum_eq | (intros; apply GlobalTheory.Mum.DescKP.sum_eq_of_sum_eq <;> assumption)
end
end
