module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCarriedAlong
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GmEqMapGm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CarriedSectionOfFrameCarriedAlongLiftsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecCarriedOver
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleFrameOfSectionUnitsOnClosedFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFlatLocalBaseChangeOfProperProperties
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoefficientsDescendFiniteFreeAffineOpenStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisTransitiveOnFibresFlatBaseChange
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameCoefficientUnitGermsFiniteFree

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem exists_isUnit_gs_of_frame_eq_sum : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ₁ : R →+* R₁) (d : ℕ) (b : Fin d → R₁) (X : Scheme.{0}) (f : X ⟶ Sp R) (L : LB X), L.IsLB → ∀ (W O : X.Opens), O ≤ W → ∀ (τ : ∀ k : L.ι, Γ((pullback f (spMap ρ₁)), (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k)ˣ) (s : Fin d → ∀ k : L.ι, Γ(X, O ⊓ L.U k)), (∀ l, IsSecOver L O (s l)) → (∀ (z : (pullback f (spMap ρ₁) : Scheme.{0})) (k : L.ι), (pullback.fst f (spMap ρ₁)) z ∈ O → (pullback.fst f (spMap ρ₁)) z ∈ L.U k → gs (𝟙 (pullback f (spMap ρ₁))) z ((pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k) (τ k).val = ∑ l, gs (pullback.snd f (spMap ρ₁)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs (pullback.fst f (spMap ρ₁)) z (O ⊓ L.U k) (s l k)) → ∀ z : (pullback f (spMap ρ₁) : Scheme.{0}), (pullback.fst f (spMap ρ₁)) z ∈ O → ∃ l, ∀ k, (pullback.fst f (spMap ρ₁)) z ∈ L.U k → IsUnit (gs (𝟙 X) ((pullback.fst f (spMap ρ₁)) z) (O ⊓ L.U k) (s l k)) := by
  intro R R₁ _ _ ρ₁ d b X f L hL W O hOW τ s hs hτ z hz
  obtain ⟨k₀, hk₀⟩ := exists_chart hL ((pullback.fst f (spMap ρ₁)) z)
  have hm : (𝟙 (pullback f (spMap ρ₁) : Scheme.{0})) z ∈
      (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k₀ := ⟨hOW hz, hk₀⟩
  have hm' : (pullback.fst f (spMap ρ₁)) z ∈ O ⊓ L.U k₀ := ⟨hz, hk₀⟩
  have hu : IsUnit (gs (𝟙 (pullback f (spMap ρ₁))) z
      ((pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k₀) (τ k₀).val) := by
    rw [gs_unit _ z _ hm]
    exact Units.isUnit _
  rw [hτ z k₀ hz hk₀] at hu
  obtain ⟨l, -, hl⟩ := IsLocalRing.exists_of_isUnit_sum hu
  have hl2 := isUnit_of_mul_isUnit_right hl
  rw [gs_eq_map_gs _ z _ hm'] at hl2
  have hl3 := (isUnit_map_iff _ _).1 hl2
  refine ⟨l, fun k hk => ?_⟩
  rw [hs l _ k k₀ hz hk hk₀]
  exact (Units.isUnit _).mul hl3

end GlobalTheory.Mum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameCoefficientUnitGermsFiniteFreeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_frameCoefficient_unitGerms_finiteFree : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ₁ : R →+* R₁) (d : ℕ) (b : Fin d → R₁) (X : Scheme.{0}) (f : X ⟶ Sp R) (L : LB X), L.IsLB → ∀ (W O : X.Opens), O ≤ W → ∀ (τ : ∀ k : L.ι, Γ((pullback f (spMap ρ₁)), (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k)ˣ) (s : Fin d → ∀ k : L.ι, Γ(X, O ⊓ L.U k)), (∀ l, IsSecOver L O (s l)) → (∀ (z : (pullback f (spMap ρ₁) : Scheme.{0})) (k : L.ι), (pullback.fst f (spMap ρ₁)) z ∈ O → (pullback.fst f (spMap ρ₁)) z ∈ L.U k → gs (𝟙 (pullback f (spMap ρ₁))) z ((pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k) (τ k).val = ∑ l, gs (pullback.snd f (spMap ρ₁)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs (pullback.fst f (spMap ρ₁)) z (O ⊓ L.U k) (s l k)) → ∀ z : (pullback f (spMap ρ₁) : Scheme.{0}), (pullback.fst f (spMap ρ₁)) z ∈ O → ∃ l, ∀ k, (pullback.fst f (spMap ρ₁)) z ∈ L.U k → IsUnit (gs (𝟙 X) ((pullback.fst f (spMap ρ₁)) z) (O ⊓ L.U k) (s l k)) := by
  first | exact @GlobalTheory.Mum.exists_isUnit_gs_of_frame_eq_sum | exact GlobalTheory.Mum.exists_isUnit_gs_of_frame_eq_sum | (intros; apply GlobalTheory.Mum.exists_isUnit_gs_of_frame_eq_sum <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisActsTransitivelyFibresFlatBaseChange

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.GalFibre

theorem exists_act_apply_eq : ∀ (R R' : Type) [CommRing R] [CommRing R'] (ρ : R →+* R'), ρ.Finite → IsGal ρ →
    ∀ (Y X : Scheme.{0}) (p : Y ⟶ Sp R) (p' : X ⟶ Sp R') (β : X ⟶ Y), Flat p → IsPullback β p' p (spMap ρ) →
    ∀ (act : Gal ρ → (X ⟶ X)), (∀ σ, act σ ≫ p' = p' ≫ spMap (Gal.hom σ)) → (∀ σ, act σ ≫ β = β) →
    ∀ z₀ z : X, β z₀ = β z → ∃ σ : Gal ρ, act σ z₀ = z := by
  intro R R' _ _ ρ _ hG Y X p p' β hfl hpb act hact hactβ z₀ z hz
  have : Flat p := hfl
  let π : R →+* ρ.range := ρ.rangeRestrict
  have hπ : Function.Surjective π := ρ.rangeRestrict_surjective
  have hfac : spMap ρ = spMap (algebraMap ρ.range R') ≫ spMap π := by
    rw [← Spec.map_comp]; rfl
  have hsq : IsPullback (pullback.fst p (spMap π)) (pullback.snd p (spMap π)) p (spMap π) :=
    IsPullback.of_hasPullback _ _
  let p₀ : X ⟶ pullback p (spMap π) :=
    hsq.lift β (p' ≫ spMap (algebraMap ρ.range R')) (by rw [hpb.w, hfac, Category.assoc])
  have hp₀ : p₀ ≫ pullback.fst p (spMap π) = β := hsq.lift_fst _ _ _
  have hp₀' : p₀ ≫ pullback.snd p (spMap π) = p' ≫ spMap (algebraMap ρ.range R') := hsq.lift_snd _ _ _
  have outer : IsPullback (p₀ ≫ pullback.fst p (spMap π)) p' p (spMap (algebraMap ρ.range R') ≫ spMap π) := by
    rw [hp₀, ← hfac]; exact hpb
  have hpb₀ : IsPullback p₀ p' (Over.mk (pullback.snd p (spMap π))).hom (spMap (algebraMap ρ.range R')) :=
    IsPullback.of_right outer hp₀' hsq
  have hinj : Function.Injective (algebraMap ρ.range R') := Subtype.val_injective
  let toG : Gal (algebraMap ρ.range R') → Gal ρ := fun σ => ⟨σ.1, fun r => σ.2 (π r)⟩
  have hG₀ : IsGal (algebraMap ρ.range R') := by
    refine ⟨?_, fun x hx => ?_⟩
    · have : Finite (Gal ρ) := hG.1
      exact Finite.of_injective toG (fun a b h => Subtype.ext (show a.1 = b.1 from congrArg (fun s : Gal ρ => s.1) h))
    · have hx' : ∀ σ ∈ Gal ρ, σ x = x := fun σ hσ => by
        refine hx σ ?_
        rintro ⟨_, r, rfl⟩
        exact hσ r
      exact ⟨⟨x, hG.2 x hx'⟩, rfl⟩
  have hflat : Flat (Over.mk (pullback.snd p (spMap π))).hom := by
    change Flat (pullback.snd p (spMap π)); infer_instance
  have : IsClosedImmersion (spMap π) := IsClosedImmersion.spec_of_surjective _ hπ
  have hz₀ : p₀ z₀ = p₀ z := by
    apply (pullback.fst p (spMap π)).isClosedEmbedding.injective
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hp₀, hz]
  obtain ⟨σ', h, h₁, h₂, h₃⟩ := gal_transitive_on_fibres ρ.range R' hinj hG₀ (Over.mk (pullback.snd p (spMap π)))
    hflat X p₀ p' hpb₀ z₀ z hz₀
  refine ⟨toG σ', ?_⟩
  have he : act (toG σ') = h := by
    refine hpb.hom_ext ?_ ?_
    · rw [hactβ, ← hp₀, ← Category.assoc, h₁]
    · rw [hact, h₂]; rfl
  rw [he, h₃]

end GlobalTheory.Mum.GalFibre
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisActsTransitivelyFibresFlatBaseChangeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.galois_acts_transitively_fibres_flat_baseChange : ∀ (R R' : Type) [CommRing R] [CommRing R'] (ρ : R →+* R'), ρ.Finite → IsGal ρ → ∀ (Y X : Scheme.{0}) (p : Y ⟶ Sp R) (p' : X ⟶ Sp R') (β : X ⟶ Y), Flat p → IsPullback β p' p (spMap ρ) → ∀ (act : Gal ρ → (X ⟶ X)), (∀ σ, act σ ≫ p' = p' ≫ spMap (Gal.hom σ)) → (∀ σ, act σ ≫ β = β) → ∀ z₀ z : X, β z₀ = β z → ∃ σ : Gal ρ, act σ z₀ = z := by
  first | exact @GlobalTheory.Mum.GalFibre.exists_act_apply_eq | exact GlobalTheory.Mum.GalFibre.exists_act_apply_eq | (intros; apply GlobalTheory.Mum.GalFibre.exists_act_apply_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCarriedDescendFiniteEtaleExtension

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum



theorem FrameCarried.descend_finiteEtale : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hF : FinExt ρ) (hG : IsGal ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (hS' : IsSemiAbelian G') (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (hS : IsSemiAbelian G) (hβ : IsGrpPullback G' G (spMap ρ) β) (hact : ∀ σ, a.act σ ≫ β = β) (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ₁ : R →+* R₁), FinExt ρ₁ → ρ₁.Etale → ∀ (V₀ : G.left.Opens) (y : G.left), y ∈ V₀ → ∀ τ : ∀ k : U'.LG.L.ι, Γ(pullback (G'.hom ≫ spMap ρ) (spMap ρ₁), (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ (β ⁻¹ᵁ V₀) ⊓ (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ U'.LG.L.U k)ˣ, FrameAlong U'.LG.L (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ((pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ (β ⁻¹ᵁ V₀)) τ → (∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h → ∀ f' : (pullback (G'.hom ≫ spMap ρ) (spMap ρ₁) : Scheme.{0}) ⟶ pullback (G'.hom ≫ spMap ρ) (spMap ρ₁), f' ≫ (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) = (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ≫ a.act σ → f' ≫ (pullback.snd (G'.hom ≫ spMap ρ) (spMap ρ₁)) = (pullback.snd (G'.hom ≫ spMap ρ) (spMap ρ₁)) → FrameCarriedAlong U'.LG.L (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ((pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ (β ⁻¹ᵁ V₀)) τ _ (Classical.choose hP.lg) f') → ∃ V : G.left.Opens, y ∈ V ∧ ∃ T : ∀ k : U'.LG.L.ι, Γ(G'.left, β ⁻¹ᵁ V ⊓ U'.LG.L.U k)ˣ, IsFrameOver U'.LG.L (β ⁻¹ᵁ V) T ∧ ∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h → FrameCarried U'.LG.L (β ⁻¹ᵁ V) T _ (Classical.choose hP.lg) := by
  intro R _ _ _ hB R' _ _ _ ρ hF hG D D' hD A' G' _ _ hS' U' a G _ _ β hS hβ hact R₁ _ _ _ ρ₁ hF₁ hE₁ V₀ y hy τ hτ hτc
  have hL : U'.LG.L.IsLB := U'.LG.isLB
  haveI : IsNoetherianRing R := hB.1.1
  have hfl : ρ₁.Flat := (RingHom.Etale.iff_flat_and_formallyUnramified.1 hE₁).1
  obtain ⟨-, -, -, hqs, -, -, -, d, b, hb⟩ := GlobalTheory.finiteFlat_proper_baseChange_facts R R₁ ρ₁ hF₁.2.1 hF₁.2.2 hfl
    G'.left G'.left (pullback (G'.hom ≫ spMap ρ) (spMap ρ₁)) (pullback (G'.hom ≫ spMap ρ) (spMap ρ₁)) (𝟙 _) (𝟙 _)
    (G'.hom ≫ spMap ρ) (pullback.snd _ _) (pullback.fst _ _) (pullback.fst _ _) (IsPullback.of_hasPullback _ _)
    (IsPullback.id_vert _) inferInstance
  have hβf : IsFinite β :=
    MorphismProperty.of_isPullback (P := @IsFinite) hβ.1.flip ((IsFinite.SpecMap_iff _).2 hF.2.2)
  have hβc : IsClosedMap β.base := β.isClosedMap
  have hGfl : Flat G.hom := by haveI := hS.smooth; infer_instance
  obtain ⟨V₁, hV₁a, hyV₁, hV₁⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp G.left.isBasis_affineOpens) hy
  have hOa : IsAffineOpen (β ⁻¹ᵁ V₁) := IsAffineOpen.preimage hV₁a β
  have hOW : β ⁻¹ᵁ V₁ ≤ β ⁻¹ᵁ V₀ := fun x hx => hV₁ hx
  obtain ⟨s, hs, hdec⟩ := GlobalTheory.T.frame_coefficients_descend_finiteFree_affineOpen R R₁ ρ₁ d b hb G'.left (G'.hom ≫ spMap ρ) U'.LG.L hL (β ⁻¹ᵁ V₀) (β ⁻¹ᵁ V₁) hOW hOa τ hτ
  have hcar : ∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre)
      (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'),
      bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U',
      PullOver hD h → ∀ l, SecCarriedOver U'.LG.L (β ⁻¹ᵁ V₁) (s l) _ (Classical.choose hP.lg) := by
    intro σ h bc hbc hP hPO
    refine GlobalTheory.T.carried_section_of_frame_carried_along_lifts R R₁ ρ₁ d b hb G'.left (G'.hom ≫ spMap ρ) U'.LG.L (β ⁻¹ᵁ V₀) (β ⁻¹ᵁ V₁) hOW τ s hdec _
      (Classical.choose hP.lg) ?_ ?_
    · rw [hbc, ← hβ.1.w, ← Category.assoc, hact]
    · intro f' h1 h2
      exact hτc σ h bc hbc hP hPO f' (h1.trans (by rw [hbc])) h2
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · subst h0
      obtain ⟨c, hc, -⟩ := hb 1
      simp at hc
    · exact h0
  have key : ∃ l, ∀ (z : G'.left) (k : U'.LG.L.ι), β z = y → z ∈ U'.LG.L.U k →
      IsUnit (gs (𝟙 G'.left) z (β ⁻¹ᵁ V₁ ⊓ U'.LG.L.U k) (s l k)) := by
    by_cases hne : ∃ z₀, β z₀ = y
    · obtain ⟨z₀, hz₀⟩ := hne
      obtain ⟨z', hz'⟩ := hqs z₀
      have hz'O : (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) z' ∈ β ⁻¹ᵁ V₁ := by
        show β ((pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)).base z') ∈ V₁
        rw [hz', hz₀]; exact hyV₁
      obtain ⟨l, hl⟩ := GlobalTheory.T.exists_frameCoefficient_unitGerms_finiteFree R R₁ ρ₁ d b G'.left (G'.hom ≫ spMap ρ) U'.LG.L hL (β ⁻¹ᵁ V₀) (β ⁻¹ᵁ V₁) hOW τ s hs
        hdec z' hz'O
      have hl' : ∀ k, z₀ ∈ U'.LG.L.U k → IsUnit (gs (𝟙 G'.left) z₀ (β ⁻¹ᵁ V₁ ⊓ U'.LG.L.U k) (s l k)) := by
        intro k hk
        have := hl k (by show (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)).base z' ∈ _; rw [hz']; exact hk)
        revert this
        show IsUnit (gs (𝟙 G'.left) ((pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)).base z') _ _) → _
        rw [hz']; exact id
      refine ⟨l, fun z k hz hk => ?_⟩
      obtain ⟨σ, hσ⟩ := GlobalTheory.T.galois_acts_transitively_fibres_flat_baseChange R R' ρ hF.2.2 hG G.left G'.left G.hom G'.hom β hGfl hβ.1 a.act
        (fun σ => (a.cart σ).1.w) hact z₀ z (hz₀.trans hz.symm)
      obtain ⟨h, bc, hbc, hP, hPO⟩ := a.unif σ
      obtain ⟨k₀, hk₀⟩ := exists_chart hL z₀
      have hz₀O : z₀ ∈ β ⁻¹ᵁ V₁ := show β z₀ ∈ V₁ from hz₀ ▸ hyV₁
      have hφ : (bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))) z₀ = z := by rw [hbc]; exact hσ
      subst hφ
      have hzO : (bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))) z₀ ∈ β ⁻¹ᵁ V₁ :=
        show β _ ∈ V₁ from hz ▸ hyV₁
      have e := hcar σ h bc hbc hP hPO l z₀ k k₀ hz₀O hzO hk₀ hk
      have hu : IsUnit (gs (bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))) z₀ _ (s l k)) := by
        rw [e]; exact (Units.isUnit _).mul (hl' k₀ hk₀)
      rw [gs_eq_map_gs (bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))) z₀ (β ⁻¹ᵁ V₁ ⊓ U'.LG.L.U k) ⟨hzO, hk⟩] at hu
      exact (isUnit_map_iff _ _).1 hu
    · push_neg at hne
      exact ⟨⟨0, hd⟩, fun z k hz _ => absurd hz (hne z)⟩
  obtain ⟨l, hl⟩ := key
  obtain ⟨V, hyV, -, T, hT, hTc⟩ :=
    GlobalTheory.Mum.exists_frame_of_isUnit_on_fibre G'.left G.left β hβc U'.LG.L hL V₁ (s l) (hs l) y hyV₁ hl
  exact ⟨V, hyV, T, hT, fun σ h bc hbc hP hPO => hTc _ _ (hcar σ h bc hbc hP hPO l)⟩

end GlobalTheory.Mum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCarriedDescendFiniteEtaleExtensionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.frameCarried_descend_finiteEtale_extension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hF : FinExt ρ) (hG : IsGal ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (hS' : IsSemiAbelian G') (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (hS : IsSemiAbelian G) (hβ : IsGrpPullback G' G (spMap ρ) β) (hact : ∀ σ, a.act σ ≫ β = β) (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ₁ : R →+* R₁), FinExt ρ₁ → ρ₁.Etale → ∀ (V₀ : G.left.Opens) (y : G.left), y ∈ V₀ → ∀ τ : ∀ k : U'.LG.L.ι, Γ(pullback (G'.hom ≫ spMap ρ) (spMap ρ₁), (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ (β ⁻¹ᵁ V₀) ⊓ (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ U'.LG.L.U k)ˣ, FrameAlong U'.LG.L (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ((pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ (β ⁻¹ᵁ V₀)) τ → (∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h → ∀ f' : (pullback (G'.hom ≫ spMap ρ) (spMap ρ₁) : Scheme.{0}) ⟶ pullback (G'.hom ≫ spMap ρ) (spMap ρ₁), f' ≫ (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) = (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ≫ a.act σ → f' ≫ (pullback.snd (G'.hom ≫ spMap ρ) (spMap ρ₁)) = (pullback.snd (G'.hom ≫ spMap ρ) (spMap ρ₁)) → FrameCarriedAlong U'.LG.L (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ((pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ (β ⁻¹ᵁ V₀)) τ _ (Classical.choose hP.lg) f') → ∃ V : G.left.Opens, y ∈ V ∧ ∃ T : ∀ k : U'.LG.L.ι, Γ(G'.left, β ⁻¹ᵁ V ⊓ U'.LG.L.U k)ˣ, IsFrameOver U'.LG.L (β ⁻¹ᵁ V) T ∧ ∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h → FrameCarried U'.LG.L (β ⁻¹ᵁ V) T _ (Classical.choose hP.lg) := by
  first | exact @GlobalTheory.Mum.FrameCarried.descend_finiteEtale | exact GlobalTheory.Mum.FrameCarried.descend_finiteEtale | (intros; apply GlobalTheory.Mum.FrameCarried.descend_finiteEtale <;> assumption)
end
end
