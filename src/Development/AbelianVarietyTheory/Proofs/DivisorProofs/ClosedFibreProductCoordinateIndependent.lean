module

public import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonFieldExtension
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapFieldExtCancel

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreEmbeddingMulImageEqOfFieldPoint

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

theorem closed_product_image (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R) (G' : Over M.S) [GrpObj G']
    (E : Emb M.π G') (N : Near M.π G') (fU : N.U.left ⟶ PSpace R E.N) (l : pullback N.U.hom M.π ⟶ E.H.toScheme)
    (hl : l ≫ E.H.ι = N.u) (hf : l ≫ E.f = pullback.fst _ _ ≫ fU) (Ω : Type) [Field Ω] (κ : ResidueField R →+* Ω)
    (s : Sp Ω ⟶ M.S) (a b c : Sp Ω ⟶ N.U.left) (x y : Over.mk s ⟶ G') (hs : s ≫ M.π = spMap (κ.comp (residue R)))
    (ha : N.Pt s a x.left) (hb : N.Pt s b y.left) (hc : N.Pt s c (x * y).left) :
    ∃ (Ω' : Type) (_ : Field Ω') (io : Ω →+* Ω') (ca cb : Over.mk (spMap (io.comp κ)) ⟶ E.Y),
      ca.left ≫ E.j = spMap io ≫ a ≫ fU ∧ cb.left ≫ E.j = spMap io ≫ b ≫ fU ∧
      (ca * cb).left ≫ E.j = spMap io ≫ c ≫ fU := by
  obtain ⟨Ω', _, io, e, l', he, hl1, hl2⟩ := E.fib Ω s κ hs
  haveI : IsMonHom e.hom := he
  have hP := isGrpPullback_pullback G' (spMap io ≫ s)
  have hY : IsGrpPullback ((Over.pullback (spMap io ≫ s)).obj G') E.Y (spMap (io.comp κ)) (e.hom.left ≫ pullback.fst E.Y.hom (spMap (io.comp κ))) :=
    ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback E.Y (spMap (io.comp κ)))).congr (Category.id_comp _) rfl

  let sec : (Over.mk s ⟶ G') → (Over.mk (𝟙 (Sp Ω')) ⟶ (Over.pullback (spMap io ≫ s)).obj G') := fun z =>
    Over.homMk (pullback.lift (spMap io ≫ z.left) (𝟙 _) (by
      rw [Category.assoc, Over.w z, Category.id_comp]; rfl)) (pullback.lift_snd _ _ _)
  have sec_fst : ∀ z, (sec z).left ≫ pullback.fst G'.hom (spMap io ≫ s) = spMap io ≫ z.left := fun z => pullback.lift_fst _ _ _

  have sec_mul : sec (x * y) = sec x * sec y := by
    let r : Over.mk (𝟙 (Sp Ω') ≫ (spMap io ≫ s)) ⟶ Over.mk s := Over.homMk (spMap io) (by simp)
    have e₁ := hP.2 (Over.mk (𝟙 (Sp Ω'))) (sec x) (sec y) (r ≫ x) (r ≫ y) (sec_fst x).symm (sec_fst y).symm
    rw [← MonObj.comp_mul] at e₁
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [sec_fst, ← e₁]; rfl
    · have h1 := Over.w (sec (x * y))
      have h2 := Over.w (sec x * sec y)
      simp only [Over.mk_hom] at h1 h2
      exact h1.trans h2.symm

  let cp : (Over.mk s ⟶ G') → (Over.mk (spMap (io.comp κ)) ⟶ E.Y) := fun z =>
    Over.homMk ((sec z).left ≫ e.hom.left ≫ pullback.fst E.Y.hom (spMap (io.comp κ))) (by
      have h := Over.w (pushPt hY.1.w (sec z))
      simp only [Over.mk_hom, pushPt, Over.homMk_left] at h
      simpa using h)
  have cp_mul : (cp x * cp y).left = (cp (x * y)).left := by
    have e₂ := hY.2 (Over.mk (𝟙 (Sp Ω'))) (sec x) (sec y) (pushPt hY.1.w (sec x)) (pushPt hY.1.w (sec y)) rfl rfl
    rw [← sec_mul] at e₂
    refine Eq.trans ?_ e₂
    exact mul_left_congr (Category.id_comp (spMap (io.comp κ))).symm _ _ _ _ rfl rfl

  have img : ∀ (z : Over.mk s ⟶ G') (d : Sp Ω ⟶ N.U.left), N.Pt s d z.left → (cp z).left ≫ E.j = spMap io ≫ d ≫ fU := by
    intro z d ⟨z₀, h₁, _, h₃⟩
    have hsec : (sec z).left ≫ l' = spMap io ≫ z₀ ≫ l := by
      rw [← cancel_mono E.H.ι, Category.assoc, hl1, sec_fst, Category.assoc, Category.assoc, hl, h₃]
    show ((sec z).left ≫ e.hom.left ≫ pullback.fst E.Y.hom (spMap (io.comp κ))) ≫ E.j = _
    rw [Category.assoc, Category.assoc, ← hl2, ← Category.assoc, hsec, Category.assoc, Category.assoc, hf,
      ← Category.assoc z₀, h₁]
  exact ⟨Ω', inferInstance, io, cp x, cp y, img x a ha, img y b hb, by rw [cp_mul]; exact img _ c hc⟩

end GlobalTheory.Mum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreEmbeddingMulImageEqOfFieldPointStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.closedFibre_embedding_mul_image_eq_of_field_point : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R) (G' : Over M.S) [GrpObj G'] (E : Emb M.π G') (N : Near M.π G') (fU : N.U.left ⟶ PSpace R E.N) (l : pullback N.U.hom M.π ⟶ E.H.toScheme), l ≫ E.H.ι = N.u → l ≫ E.f = pullback.fst _ _ ≫ fU → ∀ (Ω : Type) [Field Ω] (κ : ResidueField R →+* Ω) (s : Sp Ω ⟶ M.S) (a b c : Sp Ω ⟶ N.U.left) (x y : Over.mk s ⟶ G'), s ≫ M.π = spMap (κ.comp (residue R)) → N.Pt s a x.left → N.Pt s b y.left → N.Pt s c (x * y).left → ∃ (Ω' : Type) (_ : Field Ω') (io : Ω →+* Ω') (ca cb : Over.mk (spMap (io.comp κ)) ⟶ E.Y), ca.left ≫ E.j = spMap io ≫ a ≫ fU ∧ cb.left ≫ E.j = spMap io ≫ b ≫ fU ∧ (ca * cb).left ≫ E.j = spMap io ≫ c ≫ fU := by
  first | exact @GlobalTheory.Mum.closed_product_image | exact GlobalTheory.Mum.closed_product_image | (intros; apply GlobalTheory.Mum.closed_product_image <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreFieldPointsInjectiveProjectiveMap

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.ClosedFibreInj

theorem spMap_epi {K L : Type} [Field K] [Field L] (f : K →+* L) : Epi (spMap f) := by
  letI := f.toAlgebra
  haveI : Flat (spMap f) := by
    rw [spMap, HasRingHomProperty.Spec_iff (P := @Flat)]
    exact (show Module.Flat K L from inferInstance)
  haveI : Surjective (spMap f) := ⟨fun z => ⟨⟨⊥, Ideal.isPrime_bot⟩, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem point_lift (Ω : Type) [Field Ω] (X Y : Scheme.{0}) (g : Y ⟶ X) (hg : Surjective g) (x : Sp Ω ⟶ X) :
    ∃ (Ω' : Type) (_ : Field Ω') (io : Ω →+* Ω') (y : Sp Ω' ⟶ Y), y ≫ g = spMap io ≫ x := by
  haveI := hg
  obtain ⟨w⟩ : Nonempty ↥(Sp Ω) := inferInstance
  obtain ⟨z, -⟩ := (pullback.fst x g).surjective w
  refine ⟨(pullback x g).residueField z, inferInstance,
    (Spec.preimage ((pullback x g).fromSpecResidueField z ≫ pullback.fst x g)).hom,
    (pullback x g).fromSpecResidueField z ≫ pullback.snd x g, ?_⟩
  rw [Category.assoc, ← pullback.condition, ← Category.assoc]
  exact congrArg (· ≫ x) (Spec.map_preimage _).symm

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

theorem closedFibre_inj : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R) (G' : Over M.S) [GrpObj G'] (E : Emb M.π G') (N : Near M.π G') (fU : N.U.left ⟶ PSpace R E.N) (l : pullback N.U.hom M.π ⟶ E.H.toScheme), l ≫ E.H.ι = N.u → l ≫ E.f = pullback.fst _ _ ≫ fU → Surjective M.π → ∀ (Ω : Type) [Field Ω] (κ : ResidueField R →+* Ω) (a a' : Sp Ω ⟶ N.U.left), a ≫ N.U.hom = spMap (κ.comp (residue R)) → a' ≫ N.U.hom = spMap (κ.comp (residue R)) → a ≫ fU = a' ≫ fU → a = a' := by
  intro R _ _ _ M G' _ E N fU l hl hlf hπ Ω _ κ a a' ha ha' hf
  haveI := N.isOpen
  haveI := E.imm
  obtain ⟨Ω', _, io, s, hs⟩ := point_lift Ω (Sp R) M.S M.π hπ (spMap (κ.comp (residue R)))
  have hs' : s ≫ M.π = spMap ((io.comp κ).comp (residue R)) := by
    rw [hs, ← spMap_comp, RingHom.comp_assoc]
  obtain ⟨Ω'', _, io', e, l', -, hl'1, hl'2⟩ := E.fib Ω' s (io.comp κ) hs'

  have pt : ∀ (b : Sp Ω ⟶ N.U.left) (hb : b ≫ N.U.hom = spMap (κ.comp (residue R))),
      ∃ x : Sp Ω'' ⟶ pullback G'.hom (spMap io' ≫ s),
        x ≫ pullback.fst _ _ = spMap io' ≫ pullback.lift (spMap io ≫ b) s (by rw [Category.assoc, hb, hs]) ≫ N.u ∧
        x ≫ pullback.snd _ _ = 𝟙 _ ∧
        x ≫ e.hom.left ≫ pullback.fst _ _ ≫ E.j = spMap io' ≫ spMap io ≫ b ≫ fU := by
    intro b hb
    have hc : (spMap io ≫ b) ≫ N.U.hom = s ≫ M.π := by rw [Category.assoc, hb, hs]
    set p := pullback.lift (spMap io ≫ b) s hc with hp
    refine ⟨pullback.lift (spMap io' ≫ p ≫ N.u) (𝟙 _) (by
      rw [Category.id_comp, Category.assoc, Category.assoc, N.u_over, hp, pullback.lift_snd]), pullback.lift_fst _ _ _,
      pullback.lift_snd _ _ _, ?_⟩
    have h1 : pullback.lift (spMap io' ≫ p ≫ N.u) (𝟙 _) (by
        rw [Category.id_comp, Category.assoc, Category.assoc, N.u_over, hp, pullback.lift_snd]) ≫ l' =
        spMap io' ≫ p ≫ l := by
      rw [← cancel_mono E.H.ι, Category.assoc, hl'1, pullback.lift_fst, Category.assoc, Category.assoc, hl]
    rw [← hl'2, ← Category.assoc, h1, Category.assoc, Category.assoc, hlf, ← Category.assoc p, hp,
      pullback.lift_fst, Category.assoc]
  obtain ⟨x, hx1, hx2, hx3⟩ := pt a ha
  obtain ⟨x', hx1', hx2', hx3'⟩ := pt a' ha'
  have hj : x ≫ e.hom.left ≫ pullback.fst _ _ = x' ≫ e.hom.left ≫ pullback.fst _ _ := by
    rw [← cancel_mono E.j, Category.assoc, Category.assoc, Category.assoc, Category.assoc, hx3, hx3', hf]
  have hsec : ∀ y : Sp Ω'' ⟶ pullback G'.hom (spMap io' ≫ s), y ≫ pullback.snd _ _ = 𝟙 _ →
      y ≫ e.hom.left ≫ pullback.snd _ _ = 𝟙 _ := by
    intro y hy
    have hw := Over.w e.hom
    simp only [Over.pullback_obj_hom] at hw
    rw [hw, hy]
  have he : x ≫ e.hom.left = x' ≫ e.hom.left :=
    pullback.hom_ext (by simpa using hj) (by rw [Category.assoc, Category.assoc, hsec x hx2, hsec x' hx2'])
  have hxx : x = x' := by
    have := congrArg (· ≫ e.inv.left) he
    simpa [← Over.comp_left] using this
  subst hxx
  rw [hx1'] at hx1
  simp only [← Category.assoc, cancel_mono] at hx1
  have h2 := congrArg (· ≫ pullback.fst N.U.hom M.π) hx1
  simp only [Category.assoc, pullback.lift_fst] at h2
  haveI := spMap_epi io'
  haveI := spMap_epi io
  rw [cancel_epi, cancel_epi] at h2
  exact h2.symm

end GlobalTheory.Mum.ClosedFibreInj
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreFieldPointsInjectiveProjectiveMapStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.closedFibre_fieldPoints_injective_projective_map : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R) (G' : Over M.S) [GrpObj G'] (E : Emb M.π G') (N : Near M.π G') (fU : N.U.left ⟶ PSpace R E.N) (l : pullback N.U.hom M.π ⟶ E.H.toScheme), l ≫ E.H.ι = N.u → l ≫ E.f = pullback.fst _ _ ≫ fU → Surjective M.π → ∀ (Ω : Type) [Field Ω] (κ : ResidueField R →+* Ω) (a a' : Sp Ω ⟶ N.U.left), a ≫ N.U.hom = spMap (κ.comp (residue R)) → a' ≫ N.U.hom = spMap (κ.comp (residue R)) → a ≫ fU = a' ≫ fU → a = a' := by
  first | exact @GlobalTheory.Mum.ClosedFibreInj.closedFibre_inj | exact GlobalTheory.Mum.ClosedFibreInj.closedFibre_inj | (intros; apply GlobalTheory.Mum.ClosedFibreInj.closedFibre_inj <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonFieldExtensionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_common_field_extension' : ∀ (Ω Ω₁ Ω₂ : Type) [Field Ω] [Field Ω₁] [Field Ω₂] (i₁ : Ω →+* Ω₁) (i₂ : Ω →+* Ω₂), ∃ (Ω₃ : Type) (_ : Field Ω₃) (j₁ : Ω₁ →+* Ω₃) (j₂ : Ω₂ →+* Ω₃), j₁.comp i₁ = j₂.comp i₂ := by
  first | exact @GlobalTheory.exists_common_field_extension | exact GlobalTheory.exists_common_field_extension | (intros; apply GlobalTheory.exists_common_field_extension <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapFieldExtCancelStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.spMap_field_ext_cancel : ∀ (Ω Ω' : Type) [Field Ω] [Field Ω'] (io : Ω →+* Ω') (X : Scheme.{0}) (a b : Sp Ω ⟶ X), spMap io ≫ a = spMap io ≫ b → a = b := by
  first | exact @GlobalTheory.Mum.spMap_field_cancel | exact GlobalTheory.Mum.spMap_field_cancel | (intros; apply GlobalTheory.Mum.spMap_field_cancel <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreProductCoordinateIndependent

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem specMap_contravariant_comp_ringHom {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp [spMap, ← Spec.map_comp]

theorem Near.closed_product_unique : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R) (G' : Over M.S) [GrpObj G'] (E : Emb M.π G') (N : Near M.π G') (fU : N.U.left ⟶ PSpace R E.N) (l : pullback N.U.hom M.π ⟶ E.H.toScheme), l ≫ E.H.ι = N.u → l ≫ E.f = pullback.fst _ _ ≫ fU → Surjective M.π → ∀ (Ω : Type) [Field Ω] (κ : ResidueField R →+* Ω) (s s' : Sp Ω ⟶ M.S) (a b c c' : Sp Ω ⟶ N.U.left) (x y : Over.mk s ⟶ G') (x' y' : Over.mk s' ⟶ G'), s ≫ M.π = spMap (κ.comp (residue R)) → s' ≫ M.π = spMap (κ.comp (residue R)) → N.Pt s a x.left → N.Pt s b y.left → N.Pt s c (x * y).left → N.Pt s' a x'.left → N.Pt s' b y'.left → N.Pt s' c' (x' * y').left → c = c' := by
  intro R _ _ _ M G' _ E N fU l hl1 hl2 hsurj Ω _ κ s s' a b c c' x y x' y' hs hs' ha hb hc ha' hb' hc'
  obtain ⟨Ω₁, _, io₁, ca, cb, hca, hcb, hcc⟩ := GlobalTheory.T.closedFibre_embedding_mul_image_eq_of_field_point R M G' E N fU l hl1 hl2 Ω κ s a b c x y hs ha hb hc
  obtain ⟨Ω₂, _, io₂, ca', cb', hca', hcb', hcc'⟩ :=
    GlobalTheory.T.closedFibre_embedding_mul_image_eq_of_field_point R M G' E N fU l hl1 hl2 Ω κ s' a b c' x' y' hs' ha' hb' hc'
  obtain ⟨Ω₃, _, j₁, j₂, hj⟩ := GlobalTheory.T.exists_common_field_extension' Ω Ω₁ Ω₂ io₁ io₂
  have : Mono E.j := by haveI := E.imm; infer_instance

  let g₁ : Over.mk (spMap ((j₁.comp io₁).comp κ)) ⟶ Over.mk (spMap (io₁.comp κ)) :=
    Over.homMk (spMap j₁) (by simp only [Over.mk_hom, specMap_contravariant_comp_ringHom])
  let g₂ : Over.mk (spMap ((j₁.comp io₁).comp κ)) ⟶ Over.mk (spMap (io₂.comp κ)) :=
    Over.homMk (spMap j₂) (by simp only [Over.mk_hom, specMap_contravariant_comp_ringHom, hj])
  have hg₁ : g₁.left = spMap j₁ := rfl
  have hg₂ : g₂.left = spMap j₂ := rfl
  have e₁ : spMap j₁ ≫ spMap io₁ = spMap (j₁.comp io₁) := specMap_contravariant_comp_ringHom _ _
  have e₂ : spMap j₂ ≫ spMap io₂ = spMap (j₁.comp io₁) := by rw [specMap_contravariant_comp_ringHom, hj]
  have hA : g₁ ≫ ca = g₂ ≫ ca' := by
    ext1
    rw [← cancel_mono E.j]
    simp only [Over.comp_left, Over.homMk_left, Category.assoc, hca, hca']
    rw [hg₁, hg₂, reassoc_of% e₁, reassoc_of% e₂]
  have hB : g₁ ≫ cb = g₂ ≫ cb' := by
    ext1
    rw [← cancel_mono E.j]
    simp only [Over.comp_left, Over.homMk_left, Category.assoc, hcb, hcb']
    rw [hg₁, hg₂, reassoc_of% e₁, reassoc_of% e₂]
  have hC : g₁ ≫ (ca * cb) = g₂ ≫ (ca' * cb') := by
    rw [MonObj.comp_mul, MonObj.comp_mul, hA, hB]
  have hfU : spMap (j₁.comp io₁) ≫ c ≫ fU = spMap (j₁.comp io₁) ≫ c' ≫ fU := by
    have := congrArg (fun g => g.left ≫ E.j) hC
    simp only [Over.comp_left, Over.homMk_left, Category.assoc, hcc, hcc'] at this
    rw [hg₁, hg₂, reassoc_of% e₁, reassoc_of% e₂] at this
    exact this

  have hlies : ∀ (t : Sp Ω ⟶ M.S) (d : Sp Ω ⟶ N.U.left) (z : Sp Ω ⟶ G'.left), t ≫ M.π = spMap (κ.comp (residue R)) →
      N.Pt t d z → d ≫ N.U.hom = spMap (κ.comp (residue R)) := by
    rintro t d z ht ⟨x₀, h₁, h₂, -⟩
    rw [← h₁, Category.assoc, pullback.condition, ← Category.assoc, h₂, ht]
  have hco : ∀ d : Sp Ω ⟶ N.U.left, d ≫ N.U.hom = spMap (κ.comp (residue R)) →
      (spMap (j₁.comp io₁) ≫ d) ≫ N.U.hom = spMap (((j₁.comp io₁).comp κ).comp (residue R)) := by
    intro d hd
    rw [Category.assoc, hd, specMap_contravariant_comp_ringHom]
  have key := GlobalTheory.T.closedFibre_fieldPoints_injective_projective_map R M G' E N fU l hl1 hl2 hsurj Ω₃ ((j₁.comp io₁).comp κ) (spMap (j₁.comp io₁) ≫ c)
    (spMap (j₁.comp io₁) ≫ c') (hco c (hlies s c _ hs hc)) (hco c' (hlies s' c' _ hs' hc'))
    (by simpa only [Category.assoc] using hfU)
  exact GlobalTheory.T.spMap_field_ext_cancel Ω Ω₃ (j₁.comp io₁) N.U.left c c' key

end GlobalTheory.Mum
end
end
