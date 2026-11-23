module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasOpens
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
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleLiftObstructionEqOfIsoStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResPullURes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitCocycleLiftObstructionPullbackNaturality
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleLiftObstructionRefineFinerBasisStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPairRestrictBaseChangeBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyRestrictBasisExtendedBijective
import Mathlib.Tactic.Linter.Style
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonAffineRefinementAlongMorphism

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LBObs

variable {X Z : Scheme.{0}} (φ : Z ⟶ X) {C C' : Type} [Category.{0} C] [Category.{0} C']
  (G : C ⥤ AffOp X) (G' : C' ⥤ AffOp Z)

def RefineTriple : Type :=
  {q : Pair φ × C × C' // q.1.1.2.1 ≤ opOf G q.2.1 ∧ q.1.1.1.1 ≤ opOf G' q.2.2}

instance RefineTriple.instPreorder : Preorder (RefineTriple φ G G') where
  le d e := e.1.1 ≤ d.1.1 ∧ Nonempty (d.1.2.1 ⟶ e.1.2.1) ∧ Nonempty (d.1.2.2 ⟶ e.1.2.2)
  le_refl d := ⟨le_rfl, ⟨𝟙 _⟩, ⟨𝟙 _⟩⟩
  le_trans a b c h₁ h₂ := ⟨h₂.1.trans h₁.1, ⟨h₁.2.1.some ≫ h₂.2.1.some⟩, ⟨h₁.2.2.some ≫ h₂.2.2.some⟩⟩

def RefineTriple.pair : RefineTriple φ G G' ⥤ (Pair φ)ᵒᵖ where
  obj d := Opposite.op d.1.1
  map f := (homOfLE (leOfHom f).1).op

def RefineTriple.idx [Quiver.IsThin C] : RefineTriple φ G G' ⥤ C where
  obj d := d.1.2.1
  map f := (leOfHom f).2.1.some
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

def RefineTriple.idx' [Quiver.IsThin C'] : RefineTriple φ G G' ⥤ C' where
  obj d := d.1.2.2
  map f := (leOfHom f).2.2.some
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

end GlobalTheory.LBObs

namespace GlobalTheory.LBObs

theorem exists_pair_refine : ∀ (X Z : Scheme.{0}) (φ : Z ⟶ X) (C C' : Type) [Category.{0} C] [Category.{0} C'] [Quiver.IsThin C] [Quiver.IsThin C'] (G : C ⥤ AffOp X) (G' : C' ⥤ AffOp Z), IsBas (opOf G) → IsBas (opOf G') → ∃ (D : Type) (_ : Category.{0} D) (_ : Quiver.IsThin D) (K : D ⥤ (Pair φ)ᵒᵖ) (H : D ⥤ C) (H' : D ⥤ C'), Nonempty (H ⋙ G ⟶ K ⋙ pairSnd φ) ∧ Nonempty (H' ⋙ G' ⟶ K ⋙ pairFst φ) ∧ IsBas (opOf (K ⋙ pairFst φ)) := by
  intro X Z φ C C' _ _ _ _ G G' hG hG'
  refine ⟨RefineTriple φ G G', inferInstance, inferInstance, RefineTriple.pair φ G G',
    RefineTriple.idx φ G G', RefineTriple.idx' φ G G', ⟨{ app := fun d ↦ (homOfLE d.2.1).op }⟩,
    ⟨{ app := fun d ↦ (homOfLE d.2.2).op }⟩, ?_, ?_⟩
  · intro z U hz
    obtain ⟨t, ht, -⟩ := hG.1 (φ z) ⊤ trivial
    obtain ⟨t', ht', hle⟩ := hG'.1 z (U ⊓ φ ⁻¹ᵁ opOf G t) ⟨hz, ht⟩
    refine ⟨⟨(⟨((G'.obj t').unop, (G.obj t).unop), fun y hy ↦ (hle hy).2⟩, t, t'), le_rfl, le_rfl⟩,
      ht', fun y hy ↦ (hle hy).1⟩
  · intro d₁ d₂ z U hz h₁ h₂
    have k₁ : φ z ∈ d₁.1.1.1.2.1 := d₁.1.1.2 h₁
    have k₂ : φ z ∈ d₂.1.1.1.2.1 := d₂.1.1.2 h₂
    obtain ⟨t, a₁, a₂, ht, hle⟩ := hG.2 d₁.1.2.1 d₂.1.2.1 (φ z) (d₁.1.1.1.2.1 ⊓ d₂.1.1.1.2.1)
      ⟨k₁, k₂⟩ (d₁.2.1 k₁) (d₂.2.1 k₂)
    obtain ⟨t', b₁, b₂, ht', hle'⟩ := hG'.2 d₁.1.2.2 d₂.1.2.2 z
      (U ⊓ d₁.1.1.1.1.1 ⊓ d₂.1.1.1.1.1 ⊓ φ ⁻¹ᵁ opOf G t) ⟨⟨⟨hz, h₁⟩, h₂⟩, ht⟩ (d₁.2.2 h₁) (d₂.2.2 h₂)
    let d : RefineTriple φ G G' :=
      ⟨(⟨((G'.obj t').unop, (G.obj t).unop), fun y hy ↦ (hle' hy).2⟩, t, t'), le_rfl, le_rfl⟩
    refine ⟨d, ⟨homOfLE ⟨?_, a₁, b₁⟩⟩, ⟨homOfLE ⟨?_, a₂, b₂⟩⟩, ht', fun y hy ↦ (hle' hy).1.1.1⟩
    · exact Prod.le_def.2 ⟨fun y hy ↦ (hle' hy).1.1.2, fun y hy ↦ (hle hy).1⟩
    · exact Prod.le_def.2 ⟨fun y hy ↦ (hle' hy).1.2, fun y hy ↦ (hle hy).2⟩

end GlobalTheory.LBObs
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonAffineRefinementAlongMorphismStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_common_affine_refinement_along_morphism : ∀ (X Z : Scheme.{0}) (φ : Z ⟶ X) (C C' : Type) [Category.{0} C] [Category.{0} C'] [Quiver.IsThin C] [Quiver.IsThin C'] (G : C ⥤ AffOp X) (G' : C' ⥤ AffOp Z), IsBas (opOf G) → IsBas (opOf G') → ∃ (D : Type) (_ : Category.{0} D) (_ : Quiver.IsThin D) (K : D ⥤ (Pair φ)ᵒᵖ) (H : D ⥤ C) (H' : D ⥤ C'), Nonempty (H ⋙ G ⟶ K ⋙ pairSnd φ) ∧ Nonempty (H' ⋙ G' ⟶ K ⋙ pairFst φ) ∧ IsBas (opOf (K ⋙ pairFst φ)) := by
  first | exact @GlobalTheory.LBObs.exists_pair_refine | exact GlobalTheory.LBObs.exists_pair_refine | (intros; apply GlobalTheory.LBObs.exists_pair_refine <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleLiftObstructionPairPullback

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LBObs

theorem obAt_pairPull : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ Z₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (t₀ : Z₀ ⟶ Sp R₀) (S : Sys I π s₀) (S' : Sys I π t₀) (f₀ : Z₀ ⟶ X₀) (h : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (l : ∀ T : (Pair f₀)ᵒᵖ, (ofSys S).B ((pairPull h).G.obj T) →ₐ[R] (pairPre S' f₀).B T) (hl : (ofSys S).IsLift (pairPre S' f₀) (pairPull h) l) (hn : (ofSys S).IsNat (pairPre S' f₀) (pairPull h) l) (L : LB X₀) (c : GlobalTheory.CatCoh.H2 (ext R₁ (OAff s₀))) (D : Type) [Category.{0} D] (K : D ⥤ (Pair f₀)ᵒᵖ), ObAt S α L (K ⋙ pairSnd f₀) ((extMap R₁ (CoefMap.restrict (OAff s₀) (K ⋙ pairSnd f₀))).pull2 c) → ObAt S' α (L.pull f₀) (K ⋙ pairFst f₀) ((extMap R₁ (CoefMap.restrict (OPair f₀ t₀) K)).pull2 ((extMap R₁ (pairPull h)).pull2 c)) := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α X₀ Z₀ s₀ t₀ S S' f₀ h l hl hn L c D _ K hob
  obtain ⟨u, hfr, hu⟩ := hob
  let n : CoefMap (RingHom.id R₀) ((K ⋙ pairSnd f₀) ⋙ OAff s₀) ((K ⋙ pairFst f₀) ⋙ OAff t₀) :=
    { G := 𝟭 D
      α := fun T ↦ (pairPull h).α (K.obj T)
      naturality := fun a b ↦ (pairPull h).naturality (K.map a) b
      smul := fun T r b ↦ (pairPull h).smul (K.obj T) r b }
  have hH : ∀ T : D, opOf (K ⋙ pairFst f₀) T ≤ f₀ ⁻¹ᵁ opOf (K ⋙ pairSnd f₀) ((𝟭 D).obj T) :=
    fun T ↦ (K.obj T).unop.2
  refine ⟨_, isFrame_pull X₀ D _ (opOf_le (K ⋙ pairSnd f₀)) L u Z₀ f₀ D _ (opOf_le (K ⋙ pairFst f₀)) (𝟭 D) hH hfr, ?_⟩
  have key : (extMap R₁ (CoefMap.restrict (OPair f₀ t₀) K)).pull2 ((extMap R₁ (pairPull h)).pull2 c) =
      (extMap R₁ n).pull2 ((extMap R₁ (CoefMap.restrict (OAff s₀) (K ⋙ pairSnd f₀))).pull2 c) := by
    obtain ⟨z, rfl⟩ := H2.mk_surjective _ c
    have hy : ∀ (T : D) (y : R₁ ⊗[R₀] (OAff s₀).obj ((pairSnd f₀).obj (K.obj T))),
        (extMap R₁ (CoefMap.restrict (OPair f₀ t₀) K)).α T ((extMap R₁ (pairPull h)).α (K.obj T) y) =
          (extMap R₁ n).α T ((extMap R₁ (CoefMap.restrict (OAff s₀) (K ⋙ pairSnd f₀))).α T y) := by
      intro T y
      induction y using TensorProduct.induction_on with
      | zero => repeat erw [map_zero]
      | tmul x y => rfl
      | add x y hx hy => erw [map_add, map_add, map_add, map_add, hx, hy]
    rw [CoefMap.pullCohomologyTwo_class, CoefMap.pullCohomologyTwo_class, CoefMap.pullCohomologyTwo_class, CoefMap.pullCohomologyTwo_class]
    congr 1
    apply Subtype.ext
    funext T T' T'' a b
    simp only [CoefMap.pullCocycleTwo_apply]
    exact hy T'' _
  rw [key]
  refine isObU_pull R R₀ I hI π hπ hk R₁ α D _ ((ofSys S).restrict (K ⋙ pairSnd f₀)) D _
    ((ofSys S').restrict (K ⋙ pairFst f₀)) n (fun T ↦ l (K.obj T)) u _ _
    (fun T b ↦ hl (K.obj T) b) (fun T T' a b ↦ hn (K.map a) b) ?_ hu
  intro T T' a
  change (Z₀.presheaf.map _).hom ((f₀.app _).hom _) = (f₀.appLE _ _ _).hom _
  rfl

end GlobalTheory.LBObs
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleLiftObstructionPairPullbackStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.lineBundleLiftObstruction_pairPullback : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ Z₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (t₀ : Z₀ ⟶ Sp R₀) (S : Sys I π s₀) (S' : Sys I π t₀) (f₀ : Z₀ ⟶ X₀) (h : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (l : ∀ T : (Pair f₀)ᵒᵖ, (ofSys S).B ((pairPull h).G.obj T) →ₐ[R] (pairPre S' f₀).B T) (hl : (ofSys S).IsLift (pairPre S' f₀) (pairPull h) l) (hn : (ofSys S).IsNat (pairPre S' f₀) (pairPull h) l) (L : LB X₀) (c : GlobalTheory.CatCoh.H2 (ext R₁ (OAff s₀))) (D : Type) [Category.{0} D] (K : D ⥤ (Pair f₀)ᵒᵖ), ObAt S α L (K ⋙ pairSnd f₀) ((extMap R₁ (CoefMap.restrict (OAff s₀) (K ⋙ pairSnd f₀))).pull2 c) → ObAt S' α (L.pull f₀) (K ⋙ pairFst f₀) ((extMap R₁ (CoefMap.restrict (OPair f₀ t₀) K)).pull2 ((extMap R₁ (pairPull h)).pull2 c)) := by
  first | exact @GlobalTheory.LBObs.obAt_pairPull | exact GlobalTheory.LBObs.obAt_pairPull | (intros; apply GlobalTheory.LBObs.obAt_pairPull <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictPairInjective

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LBObs.PairInj

theorem pull2_pairRes_restrict (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] {X₀ Z₀ : Scheme.{0}}
    (t₀ : Z₀ ⟶ Sp R₀) (f₀ : Z₀ ⟶ X₀) {D : Type} [Category.{0} D] (K : D ⥤ (Pair f₀)ᵒᵖ)
    (c : CatCoh.H2 (ext R₁ (OAff t₀))) :
    (extMap R₁ (CoefMap.restrict (OPair f₀ t₀) K)).pull2 ((extMap R₁ (pairRes f₀ t₀)).pull2 c) =
      (extMap R₁ (CoefMap.restrict (OAff t₀) (K ⋙ pairFst f₀))).pull2 c := by
  obtain ⟨z, rfl⟩ := H2.mk_surjective _ c
  rw [CoefMap.pullCohomologyTwo_class, CoefMap.pullCohomologyTwo_class, CoefMap.pullCohomologyTwo_class]
  refine congrArg _ (Subtype.ext ?_)
  funext T T' T'' a b
  show extHom R₁ (coefHom (CoefMap.restrict (OPair f₀ t₀) K) T'')
      (extHom R₁ (coefHom (pairRes f₀ t₀) (K.obj T'')) _) =
    extHom R₁ (coefHom (CoefMap.restrict (OAff t₀) (K ⋙ pairFst f₀)) T'') _
  exact (PairExt.extHom_of_id R₁ _ (fun _ ↦ rfl) _).trans ((PairExt.extHom_of_id R₁ _ (fun _ ↦ rfl) _).trans
    (PairExt.extHom_of_id R₁ _ (fun _ ↦ rfl) _).symm)

theorem restrict_pair_injective : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (X₀ Z₀ : Scheme.{0}) (t₀ : Z₀ ⟶ Sp R₀) (f₀ : Z₀ ⟶ X₀) (D : Type) [Category.{0} D] [Quiver.IsThin D] (K : D ⥤ (Pair f₀)ᵒᵖ), IsBas (opOf (K ⋙ pairFst f₀)) → Function.Injective (extMap R₁ (CoefMap.restrict (OPair f₀ t₀) K)).pull2 := by
  intro R₀ R₁ _ _ _ X₀ Z₀ t₀ f₀ D _ _ K hB x y e
  have hG := (BasisExt.restrict_ext_bijective R₀ R₁ Z₀ t₀ D (K ⋙ pairFst f₀) hB.1 hB.2).2.1
  have hP := ((PairExt.pairRes_ext_bijective R₀ R₁ X₀ Z₀ t₀ f₀).1.2).2
  obtain ⟨x0, rfl⟩ := hP x
  obtain ⟨y0, rfl⟩ := hP y
  rw [pull2_pairRes_restrict, pull2_pairRes_restrict] at e
  rw [hG e]

end GlobalTheory.LBObs.PairInj
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleLiftObstructionNatural

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBObs

theorem lineBundleLiftObstruction_natural_alt : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ Z₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (t₀ : Z₀ ⟶ Sp R₀) (S : Sys I π s₀) (S' : Sys I π t₀) (f₀ : Z₀ ⟶ X₀) (h : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (l : ∀ T : (Pair f₀)ᵒᵖ, (ofSys S).B ((pairPull h).G.obj T) →ₐ[R] (pairPre S' f₀).B T) (hl : (ofSys S).IsLift (pairPre S' f₀) (pairPull h) l) (hn : (ofSys S).IsNat (pairPre S' f₀) (pairPull h) l) (L : LB X₀) (L' : LB Z₀) (c : GlobalTheory.CatCoh.H2 (ext R₁ (OAff s₀))) (c' : GlobalTheory.CatCoh.H2 (ext R₁ (OAff t₀))), L.IsLB → L'.IsLB → LBIso L' (L.pull f₀) → IsObL S α L c → IsObL S' α L' c' → IsExtendedPullbackDegTwo R₁ h c c' := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α X₀ Z₀ s₀ t₀ S S' f₀ h l hl hn L L' c c' hL hL' hiso hc hc'
  obtain ⟨C, _, _, G, hGb, hG⟩ := hc
  obtain ⟨C', _, _, G', hG'b, hG'⟩ := hc'
  obtain ⟨D, _, _, K, H, H', ⟨θ⟩, ⟨θ'⟩, hKb⟩ := GlobalTheory.T.exists_common_affine_refinement_along_morphism X₀ Z₀ f₀ C C' G G' hGb hG'b
  have h1 := GlobalTheory.T.lineBundleLiftObstruction_refine_finerBasis R R₀ I hI π hπ hk R₁ α X₀ s₀ S L c C D G (K ⋙ pairSnd f₀) H θ hG
  have h2 := GlobalTheory.T.lineBundleLiftObstruction_pairPullback R R₀ I hI π hπ hk R₁ α X₀ Z₀ s₀ t₀ S S' f₀ h l hl hn L c D K h1
  have h3 := GlobalTheory.T.lineBundleLiftObstruction_refine_finerBasis R R₀ I hI π hπ hk R₁ α Z₀ t₀ S' L' c' C' D G' (K ⋙ pairFst f₀) H' θ' hG'
  have h4 := GlobalTheory.T.lineBundleLiftObstruction_eq_of_iso R R₀ I hI π hπ hk R₁ α Z₀ t₀ S' L' (L.pull f₀) D (K ⋙ pairFst f₀) _ _ hL'
    (pull_isLB hL f₀) hiso h3 h2
  apply GlobalTheory.LBObs.PairInj.restrict_pair_injective R₀ R₁ X₀ Z₀ t₀ f₀ D K hKb
  refine h4.symm.trans ?_
  have e : ∀ {E : Type} [Category.{0} E] {E' : Type} [Category.{0} E'] (F : E ⥤ CommAlgCat.{0} R₀) (G : E' ⥤ E)
      (T : E') (x : R₁ ⊗[R₀] F.obj (G.obj T)), (extMap R₁ (CoefMap.restrict F G)).α T x = x := by
    intro E _ E' _ F G T x
    induction x using TensorProduct.induction_on with
    | zero => exact map_zero _
    | tmul y b => rfl
    | add x y hx hy => exact (map_add _ x y).trans (congrArg₂ (· + ·) hx hy)
  obtain ⟨z, rfl⟩ := H2.mk_surjective _ c'
  rw [CoefMap.pullCohomologyTwo_class, CoefMap.pullCohomologyTwo_class, CoefMap.pullCohomologyTwo_class]
  congr 1
  refine Subtype.ext ?_
  funext T T' T'' φ ψ
  exact (e _ _ _ _).trans ((e (OPair f₀ t₀) K _ _).trans (e (OAff t₀) (pairFst f₀) _ _)).symm

end GlobalTheory.LBObs
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleLiftObstructionNaturalStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.lineBundleLiftObstruction_natural : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ Z₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (t₀ : Z₀ ⟶ Sp R₀) (S : Sys I π s₀) (S' : Sys I π t₀) (f₀ : Z₀ ⟶ X₀) (h : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (l : ∀ T : (Pair f₀)ᵒᵖ, (ofSys S).B ((pairPull h).G.obj T) →ₐ[R] (pairPre S' f₀).B T) (hl : (ofSys S).IsLift (pairPre S' f₀) (pairPull h) l) (hn : (ofSys S).IsNat (pairPre S' f₀) (pairPull h) l) (L : LB X₀) (L' : LB Z₀) (c : GlobalTheory.CatCoh.H2 (ext R₁ (OAff s₀))) (c' : GlobalTheory.CatCoh.H2 (ext R₁ (OAff t₀))), L.IsLB → L'.IsLB → LBIso L' (L.pull f₀) → IsObL S α L c → IsObL S' α L' c' → IsExtendedPullbackDegTwo R₁ h c c' := by
  first | exact @GlobalTheory.LBObs.lineBundleLiftObstruction_natural_alt | exact GlobalTheory.LBObs.lineBundleLiftObstruction_natural_alt | (intros; apply GlobalTheory.LBObs.lineBundleLiftObstruction_natural_alt <;> assumption)
end
end
