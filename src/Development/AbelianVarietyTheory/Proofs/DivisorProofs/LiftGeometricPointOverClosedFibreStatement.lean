module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedSpaceClosedFibreModificationFieldExtensStatement
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfCompEqOfConnectedSpacePullbackStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftFieldExtStatement
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricFibreProjEmbeddingFixedGroupConnectedStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedSpacePullbackOfCompSurjective

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem connectedSpace_pullback_of_comp_surjective (X P Q Z : Scheme.{0}) (a : X ⟶ P)
    (b : P ⟶ Q) (g : X ⟶ Q) (ν : Z ⟶ Q) (hg : a ≫ b = g) (ha : Surjective a)
    (hc : ConnectedSpace (pullback g ν : Scheme.{0})) :
    ConnectedSpace (pullback b ν : Scheme.{0}) := by
  subst hg
  let f : pullback (a ≫ b) ν ⟶ pullback b ν :=
    (pullbackRightPullbackFstIso b ν a).inv ≫ pullback.snd a (pullback.fst b ν)
  have hf : Surjective f := inferInstance
  exact Function.Surjective.connectedSpace hf.surj f.base.hom.continuous

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedSpacePullbackOfCompSurjectiveStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.connectedSpace_pullback_of_comp_of_surjective : ∀ (X P Q Z : Scheme.{0}) (a : X ⟶ P) (b : P ⟶ Q) (g : X ⟶ Q) (ν : Z ⟶ Q), a ≫ b = g → Surjective a → ConnectedSpace (pullback g ν : Scheme.{0}) → ConnectedSpace (pullback b ν : Scheme.{0}) := by
  first | exact @GlobalTheory.connectedSpace_pullback_of_comp_surjective | exact GlobalTheory.connectedSpace_pullback_of_comp_surjective | (intros; apply GlobalTheory.connectedSpace_pullback_of_comp_surjective <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedSpacePullbackRestrictOpenContainingFibr

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem geomFibre_restrict_open_connected : ∀ (H Q Z : Scheme.{0}) (U : H.Opens) (f : H ⟶ Q) (ν : Z ⟶ Q), (∀ h : H, f h ∈ Set.range ν → h ∈ U) → ConnectedSpace (pullback f ν : Scheme.{0}) → ConnectedSpace (pullback (U.ι ≫ f) ν : Scheme.{0}) := by
  intro H Q Z U f ν hU hc
  have hs : IsIso (pullback.snd U.ι (pullback.fst f ν)) := by
    refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ ?_
    rw [Scheme.Hom.opensRange_pullbackSnd]
    refine top_unique fun z _ => ?_
    show pullback.fst f ν z ∈ U.ι.opensRange
    rw [Scheme.Opens.opensRange_ι]
    refine hU _ ⟨pullback.snd f ν z, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  let e := Scheme.homeoOfIso ((pullbackRightPullbackFstIso f ν U.ι).symm ≪≫
    asIso (pullback.snd U.ι (pullback.fst f ν)))
  exact e.connectedSpace_iff.2 hc

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedSpacePullbackRestrictOpenContainingFibrStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.connectedSpace_pullback_restrict_open_containing_fibre : ∀ (H Q Z : Scheme.{0}) (U : H.Opens) (f : H ⟶ Q) (ν : Z ⟶ Q), (∀ h : H, f h ∈ Set.range ν → h ∈ U) → ConnectedSpace (pullback f ν : Scheme.{0}) → ConnectedSpace (pullback (U.ι ≫ f) ν : Scheme.{0}) := by
  first | exact @GlobalTheory.Mum.geomFibre_restrict_open_connected | exact GlobalTheory.Mum.geomFibre_restrict_open_connected | (intros; apply GlobalTheory.Mum.geomFibre_restrict_open_connected <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalPointOfPointOverFieldExtension

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_pt_of_pt_ext : ∀ (H Q : Scheme.{0}) (φ : H ⟶ Q), LocallyOfFiniteType φ → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (ν : Sp Ω ⟶ Q) (Ω' : Type) [Field Ω'] (io : Ω →+* Ω') (q : Sp Ω' ⟶ H), q ≫ φ = spMap io ≫ ν →
    ∃ p : Sp Ω ⟶ H, p ≫ φ = ν := by
  intro H Q φ hφ Ω _ _ ν Ω' _ io q hq
  have : JacobsonSpace ↥(pullback φ ν) := LocallyOfFiniteType.jacobsonSpace (pullback.snd φ ν)
  have hne : (Set.univ : Set ↥(pullback φ ν)).Nonempty :=
    ⟨pullback.lift q (spMap io) hq (IsLocalRing.closedPoint Ω'), trivial⟩
  obtain ⟨c, -, hc⟩ := nonempty_inter_closedPoints hne isOpen_univ.isLocallyClosed
  have hc' : IsClosed ({c} : Set ↥(pullback φ ν)) := hc
  refine ⟨pointOfClosedPoint (pullback.snd φ ν) c hc' ≫ pullback.fst φ ν, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalPointOfPointOverFieldExtensionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_rational_point_of_point_over_field_extension : ∀ (H Q : Scheme.{0}) (φ : H ⟶ Q), LocallyOfFiniteType φ → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ν : Sp Ω ⟶ Q) (Ω' : Type) [Field Ω'] (io : Ω →+* Ω') (q : Sp Ω' ⟶ H), q ≫ φ = spMap io ≫ ν → ∃ p : Sp Ω ⟶ H, p ≫ φ = ν := by
  first | exact @GlobalTheory.Mum.exists_pt_of_pt_ext | exact GlobalTheory.Mum.exists_pt_of_pt_ext | (intros; apply GlobalTheory.Mum.exists_pt_of_pt_ext <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftGeometricPointOverClosedFibre

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum



theorem GlobalTheory.Mum.Emb.lift_closedPoint : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ E : Emb M.π G', ∀ (P' : Scheme.{0}) (b : P' ⟶ PSpace R E.N) (X : E.H.toScheme.Opens) (a : X.toScheme ⟶ P'), LocallyQuasiFinite b → Surjective a → a ≫ b = X.ι ≫ E.f → (∀ z : E.H.toScheme, M.π (G'.hom (E.H.ι z)) = closedPoint R → z ∈ X) → ∀ x : P', IsClosed ({x} : Set P') → (b ≫ PSpace.str R E.N) x = closedPoint R → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ P') (s : Sp Ω ⟶ M.S), Set.range ξ = {x} → ξ ≫ b ≫ PSpace.str R E.N = s ≫ M.π → ∃ p : Sp Ω ⟶ X.toScheme, p ≫ a = ξ ∧ p ≫ X.ι ≫ E.H.ι ≫ G'.hom = s := by
  intro R _ _ _ hAdm M G' _ _ hG E P' b X a hb ha hab hX x hx hxc Ω _ _ ξ s hξ hs
  have hxr : ∀ w, ξ w = x := fun w => by
    have : ξ w ∈ Set.range ξ := ⟨w, rfl⟩
    rw [hξ] at this; exact this
  have hfo : ∀ h : E.H.toScheme, PSpace.str R E.N (E.f h) = M.π (G'.hom (E.H.ι h)) := fun h => by
    rw [← Scheme.Hom.comp_apply, E.f_over]; rfl
  have hcl : ∀ h : E.H.toScheme, E.f h ∈ Set.range (ξ ≫ b) → M.π (G'.hom (E.H.ι h)) = closedPoint R := by
    rintro h ⟨w, hw⟩
    rw [← hfo, ← hw, ← Scheme.Hom.comp_apply, Category.assoc, Scheme.Hom.comp_apply, hxr]
    exact hxc
  obtain ⟨z, hz⟩ := ha.surj x
  have hzx : E.f (X.ι z) = b x := by
    rw [← hz, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hab]
  have hrng : E.f (X.ι z) ∈ Set.range (ξ ≫ b) := by
    let w : Sp Ω := Nonempty.some inferInstance
    exact ⟨w, by rw [Scheme.Hom.comp_apply, hxr, hzx]⟩
  have hg : ∃ g : E.H.toScheme, M.π (G'.hom (E.H.ι g)) = closedPoint R ∧ E.f g ∈ Set.range (ξ ≫ b) :=
    ⟨X.ι z, hcl _ hrng, hrng⟩
  have hs' : (ξ ≫ b) ≫ PSpace.str R E.N = s ≫ M.π := by rw [Category.assoc]; exact hs
  obtain ⟨Ω', _, io, q, hq1, hq2⟩ := GlobalTheory.T.exists_lift_after_field_extension R M.S M.π G' E Ω (ξ ≫ b) s hs' hg
  let φ : E.H.toScheme ⟶ pullback M.π (PSpace.str R E.N) :=
    pullback.lift (E.H.ι ≫ G'.hom) E.f (by rw [E.f_over, Category.assoc])
  haveI : Smooth G'.hom := hG.smooth
  have hφ : LocallyOfFiniteType φ := by
    have : LocallyOfFiniteType (φ ≫ pullback.fst _ _) := by
      rw [pullback.lift_fst]; infer_instance
    exact HasRingHomProperty.of_comp (fun _ _ => RingHom.FiniteType.of_comp_finiteType) this
  obtain ⟨p₀, hp₀⟩ := GlobalTheory.T.exists_rational_point_of_point_over_field_extension _ _ φ hφ Ω (pullback.lift s (ξ ≫ b) hs'.symm) Ω' io q (by
    apply pullback.hom_ext
    · simp only [φ, Category.assoc, pullback.lift_fst]; exact hq2
    · simp only [φ, Category.assoc, pullback.lift_snd]; exact hq1)
  have hp1 : p₀ ≫ E.f = ξ ≫ b := by
    have := congrArg (· ≫ pullback.snd M.π (PSpace.str R E.N)) hp₀
    simp only [φ, Category.assoc] at this
    rwa [pullback.lift_snd, pullback.lift_snd] at this
  have hp2 : p₀ ≫ E.H.ι ≫ G'.hom = s := by
    have := congrArg (· ≫ pullback.fst M.π (PSpace.str R E.N)) hp₀
    simp only [φ, Category.assoc] at this
    rwa [pullback.lift_fst, pullback.lift_fst, ← Category.assoc] at this
  have hU : ∀ h : E.H.toScheme, E.f h ∈ Set.range (ξ ≫ b) → h ∈ X := fun h hh => hX h (hcl h hh)
  have hpX : Set.range p₀ ⊆ Set.range X.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    refine hU _ ⟨w, ?_⟩
    rw [← Scheme.Hom.comp_apply, hp1]
  let p : Sp Ω ⟶ X.toScheme := IsOpenImmersion.lift X.ι p₀ hpX
  have hpι : p ≫ X.ι = p₀ := IsOpenImmersion.lift_fac _ _ _
  haveI : IsNoetherianRing R := hAdm.1
  have c4 := GlobalTheory.T.geometricFibre_projEmbedding_fixedGroup_connected R M.S M.π (by have := M.proper; infer_instance) G' hG.smooth E
    (GlobalTheory.T.connectedSpace_closedFibre_modification_fieldExtension R hAdm M) Ω (ξ ≫ b) hg
  have c3 := GlobalTheory.T.connectedSpace_pullback_restrict_open_containing_fibre _ _ _ X E.f (ξ ≫ b) hU c4
  have c2 := GlobalTheory.T.connectedSpace_pullback_of_comp_of_surjective _ _ _ _ a b (X.ι ≫ E.f) (ξ ≫ b) hab ha c3
  refine ⟨p, GlobalTheory.T.eq_of_comp_eq_of_connectedSpace_pullback' _ _ b hb Ω (ξ ≫ b) (p ≫ a) ξ ?_ rfl c2, ?_⟩
  · rw [Category.assoc, hab, ← Category.assoc, hpι, hp1]
  · rw [← Category.assoc, hpι, hp2]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftGeometricPointOverClosedFibreStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.lift_geometricPoint_over_closed_fibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ E : Emb M.π G', ∀ (P' : Scheme.{0}) (b : P' ⟶ PSpace R E.N) (X : E.H.toScheme.Opens) (a : X.toScheme ⟶ P'), LocallyQuasiFinite b → Surjective a → a ≫ b = X.ι ≫ E.f → (∀ z : E.H.toScheme, M.π (G'.hom (E.H.ι z)) = closedPoint R → z ∈ X) → ∀ x : P', IsClosed ({x} : Set P') → (b ≫ PSpace.str R E.N) x = closedPoint R → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ P') (s : Sp Ω ⟶ M.S), Set.range ξ = {x} → ξ ≫ b ≫ PSpace.str R E.N = s ≫ M.π → ∃ p : Sp Ω ⟶ X.toScheme, p ≫ a = ξ ∧ p ≫ X.ι ≫ E.H.ι ≫ G'.hom = s := by
  first | exact @GlobalTheory.Mum.Emb.lift_closedPoint | exact GlobalTheory.Mum.Emb.lift_closedPoint | (intros; apply GlobalTheory.Mum.Emb.lift_closedPoint <;> assumption)
end
end
