module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedCommGroupOfPullbackProperSurjectionStatement
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ProdSurjectiveGeometricPoints
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
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupInverseDescendsProperSurjectionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupMultiplicationDescendsProperSurjectionStatement
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentOfEqualisedProperCoverNormalStatement
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSeparatedOfIsPullbackUniversallyClosedSurjectiStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyConnectedOfIsPullbackSurjectiveLft

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem geometricallyConnected_of_isPullback_of_surjective :
    ∀ (R : Type) [CommRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), LocallyOfFiniteType π → Surjective π →
    ∀ (G' : Over S) (G : Over (Sp R)) (β : G'.left ⟶ G.left), IsPullback β G'.hom G.hom π →
    GeometricallyConnected G'.hom → GeometricallyConnected G.hom := by
  intro R _ S π hlft hsurj G' G β hpb hG'
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ y ↦ ?_⟩
  let jK : Spec (.of (AlgebraicClosure K)) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
  obtain ⟨t, ht⟩ := GlobalTheory.GeomSurj.exists_lift_of_surjective (Ω := AlgebraicClosure K) π (jK ≫ y)
  have hct : ConnectedSpace ↥(pullback G'.hom t) :=
    pullback_of_geometrically hG'.geometrically_connectedSpace _ t
  have hP : IsPullback (pullback.fst G'.hom t ≫ β) (pullback.snd G'.hom t) G.hom (t ≫ π) :=
    (IsPullback.of_hasPullback G'.hom t).paste_horiz hpb
  rw [← ht] at hP
  have hc' : ConnectedSpace ↥(pullback G.hom (jK ≫ y)) :=
    hP.isoPullback.hom.homeomorph.connectedSpace_iff.mp hct
  have hjK : Surjective jK := ⟨fun z ↦ by
    obtain ⟨w⟩ : Nonempty ↥(Spec (.of (AlgebraicClosure K))) := inferInstance
    exact ⟨w, Subsingleton.elim _ _⟩⟩
  have hc'' : ConnectedSpace ↥(pullback (pullback.snd G.hom y) jK) :=
    (pullbackLeftPullbackSndIso G.hom y jK).hom.homeomorph.connectedSpace_iff.mpr hc'
  exact (pullback.fst (pullback.snd G.hom y) jK).surjective.connectedSpace
    (pullback.fst (pullback.snd G.hom y) jK).continuous

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyConnectedOfIsPullbackSurjectiveLftStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.geometricallyConnected_of_isPullback_surjective_lft : ∀ (R : Type) [CommRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), LocallyOfFiniteType π → Surjective π → ∀ (G' : Over S) (G : Over (Sp R)) (β : G'.left ⟶ G.left), IsPullback β G'.hom G.hom π → GeometricallyConnected G'.hom → GeometricallyConnected G.hom := by
  first | exact @GlobalTheory.Mum.geometricallyConnected_of_isPullback_of_surjective | exact GlobalTheory.Mum.geometricallyConnected_of_isPullback_of_surjective | (intros; apply GlobalTheory.Mum.geometricallyConnected_of_isPullback_of_surjective <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupUnitDescendsProperSurjection

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem pullback_one_left_fst {S P : Scheme.{0}} (f : P ⟶ S) (G' : Over S) [GrpObj G'] :
    (η[(Over.pullback f).obj G'] : _ ⟶ _).left ≫ pullback.fst G'.hom f = f ≫ η[G'].left := by
  simp [Functor.monObjObj]

theorem descend_one : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S : Scheme.{0})
    (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] (G : Over (Sp R))
    (β : G'.left ⟶ G.left), IsPullback β G'.hom G.hom π →
    ∀ φ : (Over.pullback (pullback.fst π π)).obj G' ≅ (Over.pullback (pullback.snd π π)).obj G', IsMonHom φ.hom →
    pullback.fst G'.hom (pullback.fst π π) ≫ β = φ.hom.left ≫ pullback.fst G'.hom (pullback.snd π π) ≫ β →
    ∃ e : 𝟙_ (Over (Sp R)) ⟶ G, ∀ (T : Over S),
      (toUnit (Over.mk (T.hom ≫ π)) ≫ e).left = (1 : T ⟶ G').left ≫ β := by
  intro R _ _ _ _ S π hP hS hI G' _ G β hβ φ hφ hc
  have sq : IsPullback π (𝟙 S) (𝟙 (Sp R)) π := IsPullback.of_id_snd
  have hfl : Flat (𝟙 (Sp R)) := inferInstance

  have heq : pullback.fst π π ≫ (η[G'].left ≫ β) = pullback.snd π π ≫ (η[G'].left ≫ β) := by
    have h1 := pullback_one_left_fst (pullback.fst π π) G'
    have h2 := pullback_one_left_fst (pullback.snd π π) G'
    have hu : (η : _ ⟶ (Over.pullback (pullback.fst π π)).obj G').left ≫ φ.hom.left =
        (η : _ ⟶ (Over.pullback (pullback.snd π π)).obj G').left := by
      rw [← Over.comp_left, IsMonHom.one_hom]
    calc pullback.fst π π ≫ (η[G'].left ≫ β)
        = (η : _ ⟶ (Over.pullback (pullback.fst π π)).obj G').left ≫ pullback.fst G'.hom (pullback.fst π π) ≫ β := by
          rw [reassoc_of% h1]
      _ = (η : _ ⟶ (Over.pullback (pullback.fst π π)).obj G').left ≫ φ.hom.left ≫
            pullback.fst G'.hom (pullback.snd π π) ≫ β := by rw [hc]
      _ = pullback.snd π π ≫ (η[G'].left ≫ β) := by rw [reassoc_of% hu, reassoc_of% h2]
  obtain ⟨h₀, hh₀, -⟩ := GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S (Sp R) S G.left π (𝟙 _) π (𝟙 S) hP hS hI hfl sq _ heq

  have hepi : ∀ {W : Scheme.{0}} (a b : Sp R ⟶ W), π ≫ a = π ≫ b → a = b := by
    intro W a b hab
    obtain ⟨c, -, hc'⟩ := GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S (Sp R) S W π (𝟙 _) π (𝟙 S) hP hS hI hfl sq (π ≫ a)
      (by rw [pullback.condition_assoc])
    exact (hc' a rfl).trans (hc' b hab.symm).symm
  have hsec : h₀ ≫ G.hom = 𝟙 (Sp R) := by
    apply hepi
    rw [reassoc_of% hh₀, hβ.w]
    simp
  refine ⟨Over.homMk h₀ (by simpa using hsec), fun T => ?_⟩
  simp [Hom.one_def]
  rw [hh₀]

end GlobalTheory.Mum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupUnitDescendsProperSurjectionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.group_unit_descends_proper_surjection : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] (G : Over (Sp R)) (β : G'.left ⟶ G.left), IsPullback β G'.hom G.hom π → ∀ φ : (Over.pullback (pullback.fst π π)).obj G' ≅ (Over.pullback (pullback.snd π π)).obj G', IsMonHom φ.hom → pullback.fst G'.hom (pullback.fst π π) ≫ β = φ.hom.left ≫ pullback.fst G'.hom (pullback.snd π π) ≫ β → ∃ e : 𝟙_ (Over (Sp R)) ⟶ G, ∀ (T : Over S), (toUnit (Over.mk (T.hom ≫ π)) ≫ e).left = (1 : T ⟶ G').left ≫ β := by
  first | exact @GlobalTheory.Mum.descend_one | exact GlobalTheory.Mum.descend_one | (intros; apply GlobalTheory.Mum.descend_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionGeometricFibresOfDescendedGroup

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem torusExtension_of_descended : ∀ (R : Type) [CommRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), LocallyOfFiniteType π → Surjective π → ∀ (G' : Over S) [GrpObj G'] (G : Over (Sp R)) [GrpObj G] (β : G'.left ⟶ G.left), IsGrpPullback G' G π β → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ S), Nonempty (TorusExtension ((Over.pullback t).obj G'))) → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (p : Spec (.of Ω) ⟶ Sp R), Nonempty (TorusExtension ((Over.pullback p).obj G)) := by
  intro R _ S π hlft hsurj G' _ G _ β h hG' Ω _ _ p
  haveI := hlft
  haveI := hsurj
  obtain ⟨t, rfl⟩ := GlobalTheory.GeomSurj.exists_lift_of_surjective π p
  have h1 := (isGrpPullback_pullback G' t).comp h
  have h2 := isGrpPullback_pullback G (t ≫ π)
  obtain ⟨e, he, -⟩ := grpPullback_iso h1 h2
  haveI := he
  exact ⟨torusExtOfIso e (hG' Ω t).some⟩

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionGeometricFibresOfDescendedGroupStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.torusExtension_geometricFibres_of_descended_group : ∀ (R : Type) [CommRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), LocallyOfFiniteType π → Surjective π → ∀ (G' : Over S) [GrpObj G'] (G : Over (Sp R)) [GrpObj G] (β : G'.left ⟶ G.left), IsGrpPullback G' G π β → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ S), Nonempty (TorusExtension ((Over.pullback t).obj G'))) → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (p : Spec (.of Ω) ⟶ Sp R), Nonempty (TorusExtension ((Over.pullback p).obj G)) := by
  first | exact @GlobalTheory.Mum.torusExtension_of_descended | exact GlobalTheory.Mum.torusExtension_of_descended | (intros; apply GlobalTheory.Mum.torusExtension_of_descended <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianDescentAlongProperSurjective

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.DescGrp

theorem quasiCompact_of_isPullback {R : Type} [CommRing R] {S : Scheme.{0}} (π : S ⟶ Sp R) [Surjective π]
    (G' : Over S) (G : Over (Sp R)) (β : G'.left ⟶ G.left) (h : IsPullback β G'.hom G.hom π) [QuasiCompact π]
    [QuasiCompact G'.hom] : QuasiCompact G.hom := by
  have hs : Surjective β := MorphismProperty.of_isPullback (P := @Surjective) h.flip ‹_›
  have hc : QuasiCompact (β ≫ G.hom) := by rw [h.w]; infer_instance
  rw [quasiCompact_iff] at hc ⊢
  intro U hU hK
  have := (hc U hU hK).image β.continuous
  rwa [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp, Set.image_preimage_eq _ hs.surj] at this

theorem exists_semiAbelian_descent : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (G : Over (Sp R)) (β : G'.left ⟶ G.left), Smooth G.hom → IsPullback β G'.hom G.hom π → ∀ φ : (Over.pullback (pullback.fst π π)).obj G' ≅ (Over.pullback (pullback.snd π π)).obj G', IsMonHom φ.hom → pullback.fst G'.hom (pullback.fst π π) ≫ β = φ.hom.left ≫ pullback.fst G'.hom (pullback.snd π π) ≫ β → ∃ (_ : GrpObj G) (_ : IsCommMonObj G), IsSemiAbelian G ∧ IsGrpPullback G' G π β := by
  intro R _ _ _ _ S π hp hs hi G' _ _ hG G β hsm hpb φ hφ hc
  obtain ⟨m, hm⟩ := GlobalTheory.T.group_multiplication_descends_proper_surjection R S π hp hs hi G' G β hsm hpb φ hφ hc
  obtain ⟨e, he⟩ := GlobalTheory.T.group_unit_descends_proper_surjection R S π hp hs hi G' G β hpb φ hφ hc
  obtain ⟨i, hiv⟩ := GlobalTheory.T.group_inverse_descends_proper_surjection R S π hp hs hi G' G β hsm hpb φ hφ hc
  obtain ⟨g, c, hP⟩ := GlobalTheory.T.descended_comm_group_of_pullback_proper_surjection R S π hp hs hi G' G β hsm hpb m e i hm he hiv
  haveI := hG.quasiCompact
  refine ⟨g, c, ⟨c, hsm, GlobalTheory.T.isSeparated_of_isPullback_universallyClosed_surjective' R S π inferInstance hs G' G β hpb hG.separated,
    quasiCompact_of_isPullback π G' G β hpb,
    GlobalTheory.T.geometricallyConnected_of_isPullback_surjective_lft R S π inferInstance hs G' G β hpb hG.geomConnected,
    GlobalTheory.T.torusExtension_geometricFibres_of_descended_group R S π inferInstance hs G' G β hP hG.fibres⟩, hP⟩

end GlobalTheory.DescGrp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianDescentAlongProperSurjectiveStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_semiAbelian_descent_along_proper_surjective : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (G : Over (Sp R)) (β : G'.left ⟶ G.left), Smooth G.hom → IsPullback β G'.hom G.hom π → ∀ φ : (Over.pullback (pullback.fst π π)).obj G' ≅ (Over.pullback (pullback.snd π π)).obj G', IsMonHom φ.hom → pullback.fst G'.hom (pullback.fst π π) ≫ β = φ.hom.left ≫ pullback.fst G'.hom (pullback.snd π π) ≫ β → ∃ (_ : GrpObj G) (_ : IsCommMonObj G), IsSemiAbelian G ∧ IsGrpPullback G' G π β := by
  first | exact @GlobalTheory.DescGrp.exists_semiAbelian_descent | exact GlobalTheory.DescGrp.exists_semiAbelian_descent | (intros; apply GlobalTheory.DescGrp.exists_semiAbelian_descent <;> assumption)
end
end
