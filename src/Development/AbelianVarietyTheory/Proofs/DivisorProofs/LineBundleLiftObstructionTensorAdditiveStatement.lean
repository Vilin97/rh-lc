module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasOpens
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
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
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleLiftObstructionRefineFinerBasisStatement
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommonRefinement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBObs

structure CommonRef {X : Scheme.{0}} {C C' : Type} [Category.{0} C] [Category.{0} C']
    (G : C ⥤ AffOp X) (G' : C' ⥤ AffOp X) : Type where

  t : C

  t' : C'

  W : X.affineOpens
  le : W.1 ≤ opOf G t
  le' : W.1 ≤ opOf G' t'

namespace CommonRef

variable {X : Scheme.{0}} {C C' : Type} [Category.{0} C] [Category.{0} C'] [Quiver.IsThin C] [Quiver.IsThin C']
  {G : C ⥤ AffOp X} {G' : C' ⥤ AffOp X}

instance : Category.{0} (CommonRef G G') where
  Hom a b := (a.t ⟶ b.t) × (a.t' ⟶ b.t') × PLift (b.W.1 ≤ a.W.1)
  id a := (𝟙 _, 𝟙 _, ⟨le_rfl⟩)
  comp f g := (f.1 ≫ g.1, f.2.1 ≫ g.2.1, ⟨g.2.2.down.trans f.2.2.down⟩)
  id_comp f := by ext <;> simp
  comp_id f := by ext <;> simp
  assoc f g h := by ext <;> simp

instance : Quiver.IsThin (CommonRef G G') := fun a b =>
  ⟨fun f g => Prod.ext (Subsingleton.elim _ _) (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _))⟩

variable (G G')

def fst : CommonRef G G' ⥤ C where
  obj d := d.t
  map f := f.1

def snd : CommonRef G G' ⥤ C' where
  obj d := d.t'
  map f := f.2.1

def opn : CommonRef G G' ⥤ AffOp X where
  obj d := Opposite.op d.W
  map f := (homOfLE f.2.2.down).op

def toFst : fst G G' ⋙ G ⟶ opn G G' where
  app d := (homOfLE (show d.W ≤ (G.obj d.t).unop from d.le)).op
  naturality _ _ _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)

def toSnd : snd G G' ⋙ G' ⟶ opn G G' where
  app d := (homOfLE (show d.W ≤ (G'.obj d.t').unop from d.le')).op
  naturality _ _ _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)

theorem isBas (hG : IsBas (opOf G)) (hG' : IsBas (opOf G')) : IsBas (opOf (opn G G')) := by
  refine ⟨fun x U hx => ?_, fun d₁ d₂ x U hx h₁ h₂ => ?_⟩
  · obtain ⟨t, hxt, htU⟩ := hG.1 x U hx
    obtain ⟨t', hxt', ht'⟩ := hG'.1 x (opOf G t ⊓ U) ⟨hxt, hx⟩
    exact ⟨⟨t, t', (G'.obj t').unop, ht'.trans inf_le_left, le_rfl⟩, hxt', ht'.trans inf_le_right⟩
  · have hx₃ : x ∈ U ⊓ d₁.W.1 ⊓ d₂.W.1 := ⟨⟨hx, h₁⟩, h₂⟩
    obtain ⟨t, a₁, a₂, hxt, htU⟩ := hG.2 d₁.t d₂.t x _ hx₃ (d₁.le h₁) (d₂.le h₂)
    obtain ⟨t', b₁, b₂, hxt', ht'⟩ := hG'.2 d₁.t' d₂.t' x (opOf G t) hxt (d₁.le' h₁) (d₂.le' h₂)
    refine ⟨⟨t, t', (G'.obj t').unop, ht', le_rfl⟩, ⟨(a₁.some, b₁.some, ⟨?_⟩)⟩, ⟨(a₂.some, b₂.some, ⟨?_⟩)⟩, hxt', ?_⟩
    · exact ht'.trans (htU.trans (inf_le_left.trans inf_le_right))
    · exact ht'.trans (htU.trans inf_le_right)
    · exact ht'.trans (htU.trans (inf_le_left.trans inf_le_left))

end CommonRef

theorem common_refinement : ∀ (X : Scheme.{0}) (C C' : Type) [Category.{0} C] [Category.{0} C'] [Quiver.IsThin C] [Quiver.IsThin C'] (G : C ⥤ AffOp X) (G' : C' ⥤ AffOp X), IsBas (opOf G) → IsBas (opOf G') → ∃ (D : Type) (_ : Category.{0} D) (_ : Quiver.IsThin D) (K : D ⥤ AffOp X) (H : D ⥤ C) (H' : D ⥤ C'), Nonempty (H ⋙ G ⟶ K) ∧ Nonempty (H' ⋙ G' ⟶ K) ∧ IsBas (opOf K) :=
  fun X C C' _ _ _ _ G G' hG hG' =>
    ⟨CommonRef G G', inferInstance, inferInstance, CommonRef.opn G G', CommonRef.fst G G', CommonRef.snd G G',
      ⟨CommonRef.toFst G G'⟩, ⟨CommonRef.toSnd G G'⟩, CommonRef.isBas G G' hG hG'⟩

end GlobalTheory.LBObs
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineBundleFrameOnBasisLineBundleCechTensor

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBObs

theorem isFrame_tens : ∀ (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens)
    (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) (L L' : LB X) (u u' : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ),
    IsFrame L V hV u → IsFrame L' V hV u' → IsFrame (tens L L') V hV fun T T' a ↦ u T T' a * u' T T' a := by
  intro X C _ V hV L L' u u' ⟨τ, hτg, hτf⟩ ⟨τ', hτ'g, hτ'f⟩
  dsimp only [IsFrame, IsGenOn, tens]
  refine ⟨fun T p ↦ res (inf_le_inf_left (V T) (inf_le_left : L.U p.1 ⊓ L'.U p.2 ≤ L.U p.1)) (τ T p.1) *
      res (inf_le_inf_left (V T) (inf_le_right : L.U p.1 ⊓ L'.U p.2 ≤ L'.U p.2)) (τ' T p.2), ?_, ?_⟩
  · intro T p q
    refine unit_ext fun y hy ↦ ?_
    have h1 := congrArg (gm (𝟙 X) y _) (hτg T p.1 q.1)
    have h2 := congrArg (gm (𝟙 X) y _) (hτ'g T p.2 q.2)
    have m1 : (𝟙 X : X ⟶ X) y ∈ V T ⊓ L.U p.1 ⊓ L.U q.1 := ⟨⟨hy.1.1, hy.1.2.1⟩, hy.2.1⟩
    have m2 : (𝟙 X : X ⟶ X) y ∈ V T ⊓ L'.U p.2 ⊓ L'.U q.2 := ⟨⟨hy.1.1, hy.1.2.2⟩, hy.2.2⟩
    have m3 : (𝟙 X : X ⟶ X) y ∈ L.U p.1 ⊓ L'.U p.2 ⊓ (L.U q.1 ⊓ L'.U q.2) := ⟨hy.1.2, hy.2⟩
    have m4 : (𝟙 X : X ⟶ X) y ∈ V T ⊓ (L.U p.1 ⊓ L'.U p.2) := hy.1
    have m5 : (𝟙 X : X ⟶ X) y ∈ V T ⊓ (L.U q.1 ⊓ L'.U q.2) := ⟨hy.1.1, hy.2⟩
    simp only [map_mul, gm_res (𝟙 X) y _ m1] at h1
    simp only [map_mul, gm_res (𝟙 X) y _ m2] at h2
    simp only [map_mul, gm_res (𝟙 X) y _ hy, gm_res (𝟙 X) y _ m3, gm_res (𝟙 X) y _ m4, gm_res (𝟙 X) y _ m5]
    rw [h1, h2]
    ac_rfl
  · intro T T' a p
    refine unit_ext fun y hy ↦ ?_
    have h1 := congrArg (gm (𝟙 X) y _) (hτf T T' a p.1)
    have h2 := congrArg (gm (𝟙 X) y _) (hτ'f T T' a p.2)
    have m1 : (𝟙 X : X ⟶ X) y ∈ V T' ⊓ L.U p.1 := ⟨hy.1, hy.2.1⟩
    have m2 : (𝟙 X : X ⟶ X) y ∈ V T' ⊓ L'.U p.2 := ⟨hy.1, hy.2.2⟩
    have m3 : (𝟙 X : X ⟶ X) y ∈ V T ⊓ (L.U p.1 ⊓ L'.U p.2) := ⟨hV a hy.1, hy.2⟩
    simp only [map_mul, gm_res (𝟙 X) y _ m1] at h1
    simp only [map_mul, gm_res (𝟙 X) y _ m2] at h2
    simp only [map_mul, gm_res (𝟙 X) y _ hy, gm_res (𝟙 X) y _ m1, gm_res (𝟙 X) y _ m2, gm_res (𝟙 X) y _ m3]
    rw [h1, h2]
    ac_rfl

end GlobalTheory.LBObs
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineBundleFrameOnBasisLineBundleCechTensorStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isLineBundleFrameOnBasis_lineBundleCechTensor : ∀ (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens) (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) (L L' : LB X) (u u' : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ), IsFrame L V hV u → IsFrame L' V hV u' → IsFrame (tens L L') V hV fun T T' a ↦ u T T' a * u' T T' a := by
  first | exact @GlobalTheory.LBObs.isFrame_tens | exact GlobalTheory.LBObs.isFrame_tens | (intros; apply GlobalTheory.LBObs.isFrame_tens <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SigOneAddMul

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LBObs

section Additive

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {R₁ : Type} [CommRing R₁]
  [Algebra R₀ R₁]

theorem sig_mem_map (α : Aug I π R₁) {B B₀ : Type} [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀]
    (p : B →+* B₀) (hp : Function.Surjective p) (σ : R₁ ⊗[R₀] B₀ →+ B) (hσ : α.IsSig p σ) (y : R₁ ⊗[R₀] B₀) :
    σ y ∈ I.map (algebraMap R B) := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Ideal.zero_mem _
  | tmul x b₀ =>
    obtain ⟨b, rfl⟩ := hp b₀
    rw [hσ, Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (α.mem x))
  | add x y hx hy => rw [map_add (f := _)]; exact Ideal.add_mem _ hx hy

theorem sig_unique (α : Aug I π R₁) {B B₀ : Type} [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀]
    (p : B →+* B₀) (hp : Function.Surjective p) (σ σ' : R₁ ⊗[R₀] B₀ →+ B) (hσ : α.IsSig p σ)
    (hσ' : α.IsSig p σ') (y : R₁ ⊗[R₀] B₀) : σ y = σ' y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul x b₀ =>
    obtain ⟨b, rfl⟩ := hp b₀
    rw [hσ, hσ']
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem sig_one_add_mul (hI : I ^ 2 = 0) (α : Aug I π R₁) {B B₀ : Type} [CommRing B] [Algebra R B] [CommRing B₀]
    [Algebra R₀ B₀] (p : B →+* B₀) (hp : Function.Surjective p) (σ : R₁ ⊗[R₀] B₀ →+ B) (hσ : α.IsSig p σ)
    (z z' : R₁ ⊗[R₀] B₀) : (1 + σ z) * (1 + σ z') = 1 + σ (z + z') := by
  have h0 : σ z * σ z' = 0 := by
    have hm := Ideal.mul_mem_mul (sig_mem_map α p hp σ hσ z) (sig_mem_map α p hp σ hσ z')
    rw [← Ideal.map_mul, ← sq, hI, Ideal.zero_eq_bot, Ideal.map_bot] at hm
    exact (Submodule.mem_bot _).1 hm
  rw [map_add (f := _)]
  linear_combination h0

end Additive

theorem isObU_mul : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (u u' : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ) (c c' : GlobalTheory.CatCoh.H2 (ext R₁ F)), IsObU L α u c → IsObU L α u' c' → IsObU L α (fun T T' a ↦ u T T' a * u' T T' a) (c + c') := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F L u u' c c' h h'
  obtain ⟨v, σ, z, hv, hσ, rfl, hz⟩ := h
  obtain ⟨v', σ', z', hv', hσ', rfl, hz'⟩ := h'
  refine ⟨fun T T' a ↦ v T T' a * v' T T' a, σ, z + z', fun T T' a ↦ ?_, hσ, (map_add _ _ _).symm,
    fun T T' T'' a b ↦ ⟨?_, ?_⟩⟩
  · simp only [Units.val_mul, map_mul, hv, hv']
  · have h1 := (hz T T' T'' a b).1
    have h2 := (hz' T T' T'' a b).1
    unfold Aug.KerQ at h1 h2 ⊢
    change Algebra.TensorProduct.map α.q (AlgHom.id R₀ _) (z.1 T T' T'' a b + z'.1 T T' T'' a b) = 0
    rw [map_add (f := _), h1, h2, add_zero]
  · have e := (hz T T' T'' a b).2
    have e' := (hz' T T' T'' a b).2
    have hs : σ' T'' (z'.1 T T' T'' a b) = σ T'' (z'.1 T T' T'' a b) :=
      sig_unique α (L.p T'') (L.surj T'') _ _ (hσ' T'') (hσ T'') _
    rw [hs] at e'
    change _ = (1 + σ T'' (z.1 T T' T'' a b + z'.1 T T' T'' a b)) * _
    rw [← sig_one_add_mul hI α (L.p T'') (L.surj T'') (σ T'') (hσ T'')]
    simp only [Units.val_mul, map_mul]
    calc L.ρ b (v T T' a : L.B T') * L.ρ b (v' T T' a : L.B T') * ((v T' T'' b : L.B T'') * (v' T' T'' b : L.B T''))
        = (L.ρ b (v T T' a : L.B T') * (v T' T'' b : L.B T'')) *
            (L.ρ b (v' T T' a : L.B T') * (v' T' T'' b : L.B T'')) := by ring
      _ = _ := by rw [e, e']; ring

end GlobalTheory.LBObs
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleLiftObstructionTensorAdditive

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBObs

theorem isObL_tens : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (S : Sys I π s₀) (L L' : LB X₀) (c c' : GlobalTheory.CatCoh.H2 (ext R₁ (OAff s₀))), IsObL S α L c → IsObL S α L' c' → IsObL S α (tens L L') (c + c') := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α X₀ s₀ S L L' c c' hL hL'
  obtain ⟨C, _, _, G, hG, hLG⟩ := hL
  obtain ⟨C', _, _, G', hG', hLG'⟩ := hL'
  obtain ⟨D, _, _, K, H, H', ⟨θ⟩, ⟨θ'⟩, hK⟩ := GlobalTheory.LBObs.common_refinement X₀ C C' G G' hG hG'
  have h₁ := GlobalTheory.T.lineBundleLiftObstruction_refine_finerBasis R R₀ I hI π hπ hk R₁ α X₀ s₀ S L c C D G K H θ hLG
  have h₂ := GlobalTheory.T.lineBundleLiftObstruction_refine_finerBasis R R₀ I hI π hπ hk R₁ α X₀ s₀ S L' c' C' D G' K H' θ' hLG'
  obtain ⟨u, hu, hU⟩ := h₁
  obtain ⟨u', hu', hU'⟩ := h₂
  refine ⟨D, inferInstance, inferInstance, K, hK, fun T T' a ↦ u T T' a * u' T T' a,
    GlobalTheory.T.isLineBundleFrameOnBasis_lineBundleCechTensor X₀ D (opOf K) (opOf_le K) L L' u u' hu hu', ?_⟩
  rw [map_add (f := _)]
  exact GlobalTheory.LBObs.isObU_mul R R₀ I hI π hπ hk R₁ α D (K ⋙ OAff s₀) ((ofSys S).restrict K) u u' _ _ hU hU'

end GlobalTheory.LBObs
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleLiftObstructionTensorAdditiveStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.lineBundleLiftObstruction_tensor_additive : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (S : Sys I π s₀) (L L' : LB X₀) (c c' : GlobalTheory.CatCoh.H2 (ext R₁ (OAff s₀))), IsObL S α L c → IsObL S α L' c' → IsObL S α (tens L L') (c + c') := by
  first | exact @GlobalTheory.LBObs.isObL_tens | exact GlobalTheory.LBObs.isObL_tens | (intros; apply GlobalTheory.LBObs.isObL_tens <;> assumption)
end
end
