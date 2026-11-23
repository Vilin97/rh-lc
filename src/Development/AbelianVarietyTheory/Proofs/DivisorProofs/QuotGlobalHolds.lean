module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.QuotientIsAbelianSchemeOfQuotientScheme
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientAbelianSchemeFiniteFlatSubgroup
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
public import Mathlib.AlgebraicGeometry.Pullbacks
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalQuotientTransitionIsomorphismsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GluedQuotientMapFiniteFlatSurjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSemiAbelianOfCharts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackGluedQuotientKernelPairOfCoverStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalQuotientTransitionCocycleStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GlueSchemesOverOpensAlongCocycle

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianQuotientAffineCover

section

@[expose] public section

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbQuotientLocal

theorem exists_quotient_of_openImmersion (S : Scheme.{0}) [IsLocallyNoetherian S] (R : CommRingCat.{0})
    (f : Spec R ⟶ S) [IsOpenImmersion f] (A : Over S) [GrpObj A] (H : Over S) [GrpObj H] (i : H ⟶ A)
    (hA : IsAbelianScheme A) (hi : IsMonHom i) (hm : Mono i) (hf : IsFinite H.hom) (hfl : Flat H.hom) :
    ∃ (B : Over (Spec R)) (_ : GrpObj B) (q : (Over.pullback f).obj A ⟶ B),
      IsAbelianScheme B ∧ IsMonHom q ∧ IsFinite q.left ∧ Flat q.left ∧ Surjective q.left ∧
      IsPullback ((fst ((Over.pullback f).obj H) ((Over.pullback f).obj A) ≫
          (Over.pullback f).map i) * snd ((Over.pullback f).obj H) ((Over.pullback f).obj A))
        (snd ((Over.pullback f).obj H) ((Over.pullback f).obj A)) q q := by
  have hN : IsLocallyNoetherian (Spec R) := isLocallyNoetherian_of_isOpenImmersion f
  have : IsNoetherianRing R := (isLocallyNoetherian_Spec (R := R)).1 hN
  have hA' : IsAbelianScheme ((Over.pullback f).obj A) := GlobalTheory.isAbelianScheme_pullback_obj f A hA
  have hi' : IsMonHom ((Over.pullback f).map i) := inferInstance
  have hm' : Mono ((Over.pullback f).map i) := inferInstance
  have hf' : IsFinite ((Over.pullback f).obj H).hom := by
    show IsFinite (pullback.snd H.hom f)
    infer_instance
  have hfl' : Flat ((Over.pullback f).obj H).hom := by
    show Flat (pullback.snd H.hom f)
    infer_instance
  obtain ⟨B, hB, q, -, h1, h2, h3, h4, h5, -, h6⟩ :=
    GlobalTheory.AbQuotientAny.exists_quotient_abelianScheme R ((Over.pullback f).obj A)
      ((Over.pullback f).obj H) ((Over.pullback f).map i) hA' hi' hm' hf' hfl'
  exact ⟨B, hB, q, h1, h2, h3, h4, h5, h6⟩

theorem exists_local_quotient : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] (H : Over S) [GrpObj H] (i : H ⟶ A),
    IsAbelianScheme A → IsMonHom i → Mono i → IsFinite H.hom → Flat H.hom → ∀ j : S.affineCover.I₀,
    ∃ (B : Over (S.affineCover.X j)) (_ : GrpObj B) (q : (Over.pullback (S.affineCover.f j)).obj A ⟶ B),
      IsAbelianScheme B ∧ IsMonHom q ∧ IsFinite q.left ∧ Flat q.left ∧ Surjective q.left ∧
      IsPullback ((fst ((Over.pullback (S.affineCover.f j)).obj H) ((Over.pullback (S.affineCover.f j)).obj A) ≫
          (Over.pullback (S.affineCover.f j)).map i) *
          snd ((Over.pullback (S.affineCover.f j)).obj H) ((Over.pullback (S.affineCover.f j)).obj A))
        (snd ((Over.pullback (S.affineCover.f j)).obj H) ((Over.pullback (S.affineCover.f j)).obj A)) q q := by
  intro S _ A _ H _ i hA hi hm hf hfl j
  haveI : IsOpenImmersion (S.affineCover.f j) := S.affineCover.map_prop j
  exact @exists_quotient_of_openImmersion S _ _ (S.affineCover.f j) this A _ H _ i hA hi hm hf hfl

end GlobalTheory.AbQuotientLocal
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianQuotientAffineCoverStatement

section

@[expose] public section

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_abelianQuotient_affineCover : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] (H : Over S) [GrpObj H] (i : H ⟶ A),
    IsAbelianScheme A → IsMonHom i → Mono i → IsFinite H.hom → Flat H.hom → ∀ j : S.affineCover.I₀,
    ∃ (B : Over (S.affineCover.X j)) (_ : GrpObj B) (q : (Over.pullback (S.affineCover.f j)).obj A ⟶ B),
      IsAbelianScheme B ∧ IsMonHom q ∧ IsFinite q.left ∧ Flat q.left ∧ Surjective q.left ∧
      IsPullback ((fst ((Over.pullback (S.affineCover.f j)).obj H) ((Over.pullback (S.affineCover.f j)).obj A) ≫
          (Over.pullback (S.affineCover.f j)).map i) *
          snd ((Over.pullback (S.affineCover.f j)).obj H) ((Over.pullback (S.affineCover.f j)).obj A))
        (snd ((Over.pullback (S.affineCover.f j)).obj H) ((Over.pullback (S.affineCover.f j)).obj A)) q q := by
  first | (exact @GlobalTheory.AbQuotientLocal.exists_local_quotient) | (exact GlobalTheory.AbQuotientLocal.exists_local_quotient) | (intros; apply GlobalTheory.AbQuotientLocal.exists_local_quotient  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGluedQuotientMapOfLocalQuotients

section

@[expose] public section

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.QuotGlue

theorem exists_glueMap (S : Scheme.{0}) (𝒰 : S.OpenCover.{0}) (A H : Over S) [GrpObj A] [GrpObj H] (i : H ⟶ A)
    (B : ∀ j, Over (𝒰.X j)) (q : ∀ j, (Over.pullback (𝒰.f j)).obj A ⟶ B j)
    (b : ∀ j k, pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k) ⟶ (B k).left)
    (G : Scheme.{0}) (F : G ⟶ S) (ψ : ∀ j, (B j).left ⟶ G)
    (hb : ∀ (j k : 𝒰.I₀) (T : Scheme.{0}) (y : T ⟶ pullback A.hom (𝒰.f j)) (z : T ⟶ pullback A.hom (𝒰.f k))
        (w : T ⟶ pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k)), y ≫ pullback.fst _ _ = z ≫ pullback.fst _ _ →
        w ≫ pullback.fst _ _ = y ≫ (q j).left → w ≫ pullback.snd _ _ = z ≫ pullback.snd _ _ → w ≫ b j k = z ≫ (q k).left)
    (hψ : ∀ j k, pullback.fst _ _ ≫ ψ j = b j k ≫ ψ k) (hψF : ∀ j, ψ j ≫ F = (B j).hom ≫ 𝒰.f j) :
    ∃ Qm : A.left ⟶ G, Qm ≫ F = A.hom ∧ ∀ j, (q j).left ≫ ψ j = pullback.fst A.hom (𝒰.f j) ≫ Qm := by
  let qL : ∀ j, pullback A.hom (𝒰.f j) ⟶ (B j).left := fun j => (q j).left
  have hq : ∀ j, qL j ≫ (B j).hom = pullback.snd A.hom (𝒰.f j) := fun j => Over.w (q j)
  have hb' : ∀ (j k : 𝒰.I₀) (T : Scheme.{0}) (y : T ⟶ pullback A.hom (𝒰.f j)) (z : T ⟶ pullback A.hom (𝒰.f k))
      (w : T ⟶ pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k)), y ≫ pullback.fst _ _ = z ≫ pullback.fst _ _ →
      w ≫ pullback.fst _ _ = y ≫ qL j → w ≫ pullback.snd _ _ = z ≫ pullback.snd _ _ → w ≫ b j k = z ≫ qL k := hb
  have key : ∀ j k, pullback.fst (pullback.fst A.hom (𝒰.f j)) (pullback.fst A.hom (𝒰.f k)) ≫ qL j ≫ ψ j =
      pullback.snd (pullback.fst A.hom (𝒰.f j)) (pullback.fst A.hom (𝒰.f k)) ≫ qL k ≫ ψ k := by
    intro j k
    have e : pullback.fst (pullback.fst A.hom (𝒰.f j)) (pullback.fst A.hom (𝒰.f k)) ≫ pullback.fst A.hom (𝒰.f j) =
        pullback.snd (pullback.fst A.hom (𝒰.f j)) (pullback.fst A.hom (𝒰.f k)) ≫ pullback.fst A.hom (𝒰.f k) :=
      pullback.condition
    have hw : (pullback.fst (pullback.fst A.hom (𝒰.f j)) (pullback.fst A.hom (𝒰.f k)) ≫ qL j) ≫ ((B j).hom ≫ 𝒰.f j) =
        (pullback.snd (pullback.fst A.hom (𝒰.f j)) (pullback.fst A.hom (𝒰.f k)) ≫ pullback.snd A.hom (𝒰.f k)) ≫ 𝒰.f k := by
      rw [Category.assoc, reassoc_of% (hq j), ← pullback.condition, ← Category.assoc, e,
        Category.assoc, Category.assoc, pullback.condition]
    have h1 := hb' j k _ _ _ (pullback.lift _ _ hw) e (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
    rw [← Category.assoc, ← pullback.lift_fst _ _ hw, Category.assoc, hψ, ← Category.assoc, h1, Category.assoc]
  have hc : ∀ j k, pullback.fst ((𝒰.pullback₁ A.hom).f j) ((𝒰.pullback₁ A.hom).f k) ≫ (qL j ≫ ψ j) =
      pullback.snd ((𝒰.pullback₁ A.hom).f j) ((𝒰.pullback₁ A.hom).f k) ≫ (qL k ≫ ψ k) := key
  have hι : ∀ j, pullback.fst A.hom (𝒰.f j) ≫ Scheme.Cover.glueMorphisms (𝒰.pullback₁ A.hom) (fun j => qL j ≫ ψ j) hc =
      qL j ≫ ψ j := fun j => Scheme.Cover.ι_glueMorphisms (𝒰.pullback₁ A.hom) (fun j => qL j ≫ ψ j) hc j
  refine ⟨Scheme.Cover.glueMorphisms (𝒰.pullback₁ A.hom) (fun j => qL j ≫ ψ j) hc, ?_, fun j => (hι j).symm⟩
  refine Scheme.Cover.hom_ext (𝒰.pullback₁ A.hom) _ _ fun (j : 𝒰.I₀) => ?_
  show pullback.fst A.hom (𝒰.f j) ≫ _ ≫ F = pullback.fst A.hom (𝒰.f j) ≫ A.hom
  rw [reassoc_of% (hι j), hψF, reassoc_of% (hq j), pullback.condition]

end GlobalTheory.QuotGlue
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGluedQuotientMapOfLocalQuotientsStatement

section

@[expose] public section

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_gluedQuotientMap_of_local_quotients : ∀ (S : Scheme.{0}) (𝒰 : S.OpenCover.{0}) (A H : Over S) [GrpObj A] [GrpObj H] (i : H ⟶ A)
    (B : ∀ j, Over (𝒰.X j)) (q : ∀ j, (Over.pullback (𝒰.f j)).obj A ⟶ B j) (b : ∀ j k, pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k) ⟶ (B k).left)
    (G : Scheme.{0}) (F : G ⟶ S) (ψ : ∀ j, (B j).left ⟶ G),
    (∀ (j k : 𝒰.I₀) (T : Scheme.{0}) (y : T ⟶ pullback A.hom (𝒰.f j)) (z : T ⟶ pullback A.hom (𝒰.f k))
        (w : T ⟶ pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k)), y ≫ pullback.fst _ _ = z ≫ pullback.fst _ _ →
        w ≫ pullback.fst _ _ = y ≫ (q j).left → w ≫ pullback.snd _ _ = z ≫ pullback.snd _ _ → w ≫ b j k = z ≫ (q k).left) →
    (∀ j k, pullback.fst _ _ ≫ ψ j = b j k ≫ ψ k) → (∀ j, ψ j ≫ F = (B j).hom ≫ 𝒰.f j) →
    ∃ Qm : A.left ⟶ G, Qm ≫ F = A.hom ∧ ∀ j, (q j).left ≫ ψ j = pullback.fst A.hom (𝒰.f j) ≫ Qm := by
  first | (exact @GlobalTheory.QuotGlue.exists_glueMap) | (exact GlobalTheory.QuotGlue.exists_glueMap) | (intros; apply GlobalTheory.QuotGlue.exists_glueMap  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOfChartsSurjectiveImage

section

@[expose] public section

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.QuotAbelian

theorem isAbelianScheme_of_charts_of_surjective :
    ∀ (S : Scheme.{0}) (𝒰 : S.OpenCover.{0}) (A G : Over S) [GrpObj A] [GrpObj G] (Q : A ⟶ G)
    (B : ∀ j, Over (𝒰.X j)) [∀ j, GrpObj (B j)] (ψ : ∀ j, (B j).left ⟶ G.left),
    IsAbelianScheme A → IsCommMonObj G → Surjective Q.left → (∀ j, IsPullback (ψ j) (B j).hom G.hom (𝒰.f j)) →
    (∀ j, IsAbelianScheme (B j)) → IsAbelianScheme G := by
  intro S 𝒰 A G _ _ Q B _ ψ hA hG hQ hψ hB
  have : IsZariskiLocalAtTarget @Smooth.{0} := HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Smooth)
  have hsm : Smooth G.hom := GlobalTheory.GroupGlue.of_charts @Smooth hψ fun j => (hB j).smooth
  have hpr : IsProper G.hom := GlobalTheory.GroupGlue.of_charts @IsProper hψ fun j => (hB j).proper
  have hw : Q.left ≫ G.hom = A.hom := Over.w Q
  have := hA.geomConnected
  have : GeometricallyConnected (Q.left ≫ G.hom) := by rw [hw]; infer_instance
  exact ⟨hG, hsm, hpr, GlobalTheory.AbelianQuotient.geometricallyConnected_of_comp Q.left G.hom⟩

end GlobalTheory.QuotAbelian
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOfChartsSurjectiveImageStatement

section

@[expose] public section

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isAbelianScheme_of_charts_surjective_image : ∀ (S : Scheme.{0}) (𝒰 : S.OpenCover.{0}) (A G : Over S) [GrpObj A] [GrpObj G] (Q : A ⟶ G)
    (B : ∀ j, Over (𝒰.X j)) [∀ j, GrpObj (B j)] (ψ : ∀ j, (B j).left ⟶ G.left),
    IsAbelianScheme A → IsCommMonObj G → Surjective Q.left → (∀ j, IsPullback (ψ j) (B j).hom G.hom (𝒰.f j)) →
    (∀ j, IsAbelianScheme (B j)) → IsAbelianScheme G := by
  first | exact @GlobalTheory.QuotAbelian.isAbelianScheme_of_charts_of_surjective | exact GlobalTheory.QuotAbelian.isAbelianScheme_of_charts_of_surjective | (intros; apply GlobalTheory.QuotAbelian.isAbelianScheme_of_charts_of_surjective <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotGlobalHolds

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IwLevel

theorem quotGlobal_holds : QuotGlobal := by
  intro S _ A _ H _ i hA hi hm hf hfl
  have := hA.comm
  choose B instB q hq using GlobalTheory.T.exists_abelianQuotient_affineCover S A H i hA hi hm hf hfl
  have hfin : ∀ j, IsFinite (q j).left := fun j => (hq j).2.2.1
  have hflat : ∀ j, Flat (q j).left := fun j => (hq j).2.2.2.1
  have hsurj : ∀ j, Surjective (q j).left := fun j => (hq j).2.2.2.2.1
  have hqc : ∀ j, QuasiCompact (q j).left := fun j => by have := hfin j; infer_instance
  have hsq : ∀ j, _ := fun j => (hq j).2.2.2.2.2
  obtain ⟨b, hb1, hb2, hchar⟩ := GlobalTheory.T.exists_local_quotient_transition_isomorphisms S S.affineCover A H i B q hflat hsurj hqc hsq
  have hcoc := GlobalTheory.T.local_quotient_transition_cocycle S S.affineCover A H i B q b hflat hsurj hqc hb1 hchar
  obtain ⟨G0, F, ψ, hψ, hψ2⟩ := GlobalTheory.CocycleGlue.exists_glue (fun j => S.affineCover.X j) (fun j => (B j).left)
    (fun j => S.affineCover.f j) (fun j => inferInstance) (fun j => (B j).hom)
    (fun j k => pullback ((B j).hom ≫ S.affineCover.f j) (S.affineCover.f k)) (fun j k => pullback.fst _ _) b
    (fun j k => by rw [hb1]; exact IsPullback.of_hasPullback _ _) hb2 hcoc
  obtain ⟨Qm, hQF, hQm⟩ := GlobalTheory.T.exists_gluedQuotientMap_of_local_quotients S S.affineCover A H i B q b G0 F ψ hchar (fun j k => (hψ2 j k).w)
    (fun j => (hψ j).w)
  let G : Over S := Over.mk F
  let Q : A ⟶ G := Over.homMk Qm hQF
  have hpb : IsPullback ((fst H A ≫ i) * snd H A) (snd H A) Q Q :=
    GlobalTheory.T.isPullback_gluedQuotient_kernelPair_of_cover S S.affineCover A H G i Q B ψ q hψ hQm hsq
  obtain ⟨hQfin, hQfl, hQs⟩ := GlobalTheory.T.gluedQuotientMap_finite_flat_surjective S S.affineCover A G Q B ψ q hψ hQm hfin hflat hsurj
  have : IsCommMonObj A := hA.comm
  have : IsMonHom i := hi
  have : QuasiCompact Q.left := inferInstance
  obtain ⟨instG, hcomm, hhom, -⟩ := GlobalTheory.AbelianQuotient.exists_grpObj i Q hpb
  exact ⟨G, instG, Q, GlobalTheory.T.isAbelianScheme_of_charts_surjective_image S S.affineCover A G Q B ψ hA hcomm hQs hψ (fun j => (hq j).1), hhom, hQfin, hQfl, hQs, hpb⟩

end GlobalTheory.IwLevel
end
end
end
