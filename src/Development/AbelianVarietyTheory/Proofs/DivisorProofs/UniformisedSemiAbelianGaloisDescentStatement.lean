module

public import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNearGaloisQuotient
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenCubicalTrivialisationDescendedClosedTorusStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisationCompleteLocalEvenOnTorusStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationPullbackInjectiveLocStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolarisedAVIsoDescendsOfRationalThreeTorsion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyDegDataIsoOfGaloisDescendedGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedGenericFibreDescendsGaloisStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationBundleDescendsAlongGaloisExtensionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDescendsOfDescendsNearClosedFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleSpaceOfSmoothOfGeometricallyConnectedStatement
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoGenericFibreDescendFiniteExt

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.Mum

theorem exists_comp_eq_fst {S S' U U' X X' : Scheme.{0}} {g : X ⟶ S} {g' : X' ⟶ S'} {s : S' ⟶ S} {β : X' ⟶ X}
    (pb : IsPullback β g' g s) {j : U ⟶ S} [Mono j] {j' : U' ⟶ S'} {u : U' ⟶ U} (sq : u ≫ j = j' ≫ s)
    (κ : pullback g' j' ⟶ pullback g j) (hκ : κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β) :
    ∃ c : pullback (pullback.snd g j) u ⟶ pullback g' j', c ≫ κ = pullback.fst _ _ := by
  have w : (pullback.fst (pullback.snd g j) u ≫ pullback.fst g j) ≫ g = (pullback.snd (pullback.snd g j) u ≫ j') ≫ s := by
    rw [Category.assoc, pullback.condition, pullback.condition_assoc, sq, Category.assoc]
  refine ⟨pullback.lift (pb.lift _ _ w) _ (pb.lift_snd _ _ w), ?_⟩
  rw [← cancel_mono (pullback.fst g j), Category.assoc, hκ, pullback.lift_fst_assoc, pb.lift_fst]

theorem lbIso_pull_pull_of_third {Q Y X Z Z' B : Scheme.{0}} {c : Q ⟶ Y} {κ : Y ⟶ X} {q : Q ⟶ X} (hc : c ≫ κ = q)
    {p : X ⟶ Z} {p' : Y ⟶ Z'} {β : Z' ⟶ Z} (hκ : κ ≫ p = p' ≫ β) {a : X ⟶ B} {M : LB B} {N : LB Z} {L' : LB Z'}
    (hM : M.IsLB) (hN : N.IsLB) (hL' : L'.IsLB) (h₁ : LBIso (L'.pull p') (M.pull (κ ≫ a))) (h₂ : LBIso L' (N.pull β)) :
    LBIso ((M.pull a).pull q) ((N.pull p).pull q) := by
  have hA := pull_isLB hM a
  have hP := pull_isLB hN p
  have e₁ : LBIso (L'.pull (c ≫ p')) (M.pull (q ≫ a)) :=
    GlobalTheory.GenSpread.lbIso_pull_comp c rfl (by rw [← Category.assoc, hc]) h₁
  have e₂ : LBIso (L'.pull (c ≫ p')) (N.pull (q ≫ p)) :=
    GlobalTheory.GenSpread.lbIso_pull_of_lbIso h₂ _ (by rw [Category.assoc, ← hκ, ← hc, Category.assoc])
  exact LBIso.trans (pull_isLB hA _) (pull_isLB hM _) (pull_isLB hP _)
    (GlobalTheory.GenSpread.lbIso_pull_pull hM q rfl).symm
    (LBIso.trans (pull_isLB hM _) (pull_isLB hL' _) (pull_isLB hP _) e₁.symm
      (LBIso.trans (pull_isLB hL' _) (pull_isLB hN _) (pull_isLB hP _) e₂
        (GlobalTheory.GenSpread.lbIso_pull_pull hN q rfl)))

theorem exists_fractionRing_map {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R')
    (hρ : Function.Injective ρ) : ∃ g : FractionRing R →+* FractionRing R',
      g.comp (algebraMap R (FractionRing R)) = (algebraMap R' (FractionRing R')).comp ρ := by
  have hinj : Function.Injective ((algebraMap R' (FractionRing R')).comp ρ) :=
    fun a b h => hρ (IsFractionRing.injective R' (FractionRing R') h)
  exact ⟨IsFractionRing.lift (K := FractionRing R) hinj,
    RingHom.ext fun r => IsFractionRing.lift_algebraMap (K := FractionRing R) hinj r⟩

theorem lbIso_generic_descend : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → ∀ (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G' → IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → ∀ (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A) (κ : pullback G'.hom (jK R') ⟶ pullback G.hom (jK R)), IsMonHom gen.hom → κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β → ∀ (L' : LB G'.left), L'.IsLB → LBIso (L'.pull (pullback.fst G'.hom (jK R'))) (A.L.pull (κ ≫ gen.hom.left)) → ∀ P : GlobalTheory.UU.CP G, LBIso L' (P.L.L.pull β) → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) := by
  intro R _ _ _ _ R' _ _ _ ρ hρ G' _ _ G _ _ β _ _ pb A gen κ hgen hκ L' hL' h₁ P h₂
  obtain ⟨gam, hgam⟩ := exists_fractionRing_map ρ hρ.2.1
  have sq : spMap gam ≫ jK R = jK R' ≫ spMap ρ :=
    (spMap_comp _ gam).symm.trans ((congrArg spMap hgam).trans (spMap_comp ρ _))
  have hX : IsAbelianScheme ((Over.pullback (jK R)).obj G) :=
    GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback A.isAb (isGrpPullback_of_iso gen)
  have : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  obtain ⟨c, hc⟩ := exists_comp_eq_fst pb.1 sq κ hκ
  exact GlobalTheory.PolIsoDescent.lbIso_descend GlobalTheory.globalFns_holds (spMap gam) _ hX (pull_isLB A.isLB _)
    (pull_isLB P.L.isLB _) (lbIso_pull_pull_of_third hc hκ A.isLB P.L.isLB hL' h₁ h₂)

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoGenericFibreDescendFiniteExtStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.lineBundleIso_genericFibre_descend_finite_ext : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → ∀ (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G' → IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → ∀ (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A) (κ : pullback G'.hom (jK R') ⟶ pullback G.hom (jK R)), IsMonHom gen.hom → κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β → ∀ (L' : LB G'.left), L'.IsLB → LBIso (L'.pull (pullback.fst G'.hom (jK R'))) (A.L.pull (κ ≫ gen.hom.left)) → ∀ P : GlobalTheory.UU.CP G, LBIso L' (P.L.L.pull β) → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) := by
  first | exact @GlobalTheory.Mum.lbIso_generic_descend | exact GlobalTheory.Mum.lbIso_generic_descend | (intros; apply GlobalTheory.Mum.lbIso_generic_descend <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyDegDataIsoOfGaloisDescendedGroupStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.nonempty_degData_iso_of_galoisDescendedGroup : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), ∀ (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → (∀ σ, a.act σ ≫ β = β) → ∀ (A : PolAV (Sp (FractionRing R))) (D₁ : DegData R (maximalIdeal R)) (U₁ : Unif (maximalIdeal R) D₁ A G), LBIso U'.LG.L (U₁.LG.L.pull β) → Nonempty (IsPullDeg (RingHom.id R) D₁.toPre D.toPre) := by
  first | exact @GlobalTheory.Mum.nonempty_isPullDeg_of_galAct | exact GlobalTheory.Mum.nonempty_isPullDeg_of_galAct | (intros; apply GlobalTheory.Mum.nonempty_isPullDeg_of_galAct <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasOfGalAct

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem has_of_galAct : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), ∀ (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → (∀ σ, a.act σ ≫ β = β) → Has D := by
  intro R _ _ _ hR R' _ _ _ ρ hfin hgal D D' hD A' G' _ _ hS' U' a G _ _ β hS pb hinv
  obtain ⟨A, gen, κ, hgen, hκ, hLA⟩ := GlobalTheory.T.polarised_generic_fibre_descends_galois R hR R' ρ hfin hgal D D' hD A' G' hS' U' a G β hS pb hinv
  obtain ⟨P, hP⟩ := GlobalTheory.T.uniformisationBundle_descends_along_galoisExtension R hR R' ρ hfin hgal D D' hD A' G' hS' U' a G β hS pb hinv
  have hAP := GlobalTheory.T.lineBundleIso_genericFibre_descend_finite_ext R hR R' ρ hfin G' G β hS' hS pb A gen κ hgen hκ U'.LG.L U'.LG.isLB hLA P hP
  have hev := GlobalTheory.T.evenCubicalTrivialisation_descended_closedTorus R hR R' ρ hfin hgal D D' hD A' G' hS' U' a G β hS pb hinv P hP
  obtain ⟨D₁, U₁, hLG, -⟩ := GlobalTheory.T.exists_uniformisation_completeLocal_evenOnTorus R hR G P hS hev A gen hgen hAP
  have hP₁ : LBIso U'.LG.L (U₁.LG.L.pull β) := by rw [hLG]; exact hP
  have h₁ := GlobalTheory.T.nonempty_degData_iso_of_galoisDescendedGroup R hR R' ρ hfin hgal D D' hD A' G' hS' U' a G β hS pb hinv A D₁ U₁ hP₁
  exact GlobalTheory.T.hasSemiAbelianUniformisation_pullback_injective_local R R (RingHom.id R) hR.1 hR.1 Function.injective_id inferInstance D₁ D h₁
    ⟨G, inferInstance, inferInstance, A, hS, ⟨U₁⟩⟩

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapClosedPointOfFinite

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem dense_of_closedFibre_sub : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G],
    IsSemiAbelian G → ∀ O : G.left.Opens, (∀ g : G.left, G.hom g = closedPoint R → g ∈ O) → Dense (O : Set G.left) := by
  intro R _ _ _ G _ hG O hO
  haveI := hG.smooth
  haveI := hG.geomConnected
  let g₀ : G.left := (1 : Over.mk (𝟙 (Sp R)) ⟶ G).left (closedPoint R)
  have hg₀ : G.hom g₀ = closedPoint R := by
    have := Over.w (1 : Over.mk (𝟙 (Sp R)) ⟶ G)
    change ((1 : Over.mk (𝟙 (Sp R)) ⟶ G).left ≫ G.hom) (closedPoint R) = closedPoint R
    rw [this]; rfl
  have : IrreducibleSpace G.left := GlobalTheory.T.irreducibleSpace_of_smooth_geometricallyConnected_domain R G inferInstance inferInstance ⟨g₀⟩
  exact O.isOpen.dense ⟨g₀, hO g₀ hg₀⟩

theorem spMap_closedPoint_of_finite {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    (ρ : R →+* R') (hf : ρ.Finite) : spMap ρ (closedPoint R') = closedPoint R := by
  algebraize [ρ]
  have : Algebra.IsIntegral R R' := ⟨fun x => hf.to_isIntegral x⟩
  apply PrimeSpectrum.ext
  show Ideal.comap ρ (maximalIdeal R') = maximalIdeal R
  have : (Ideal.comap (algebraMap R R') (maximalIdeal R')).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (maximalIdeal R')
  exact IsLocalRing.eq_maximalIdeal this

theorem comp_eq_of_near {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R']
    (ρ : R →+* R') (hf : ρ.Finite) (G' : Over (Sp R')) [GrpObj G'] (hG' : IsSemiAbelian G') (N : Near (spMap ρ) G')
    (G : Over (Sp R)) [GrpObj G] (hG : IsSeparated G.hom) (β : G'.left ⟶ G.left) (hβ : β ≫ G.hom = G'.hom ≫ spMap ρ)
    (i : N.U ⟶ G) (hu : N.u ≫ β = pullback.fst _ _ ≫ i.left) (σ : Gal ρ) (g : G'.left ⟶ G'.left)
    (hg : g ≫ G'.hom = G'.hom ≫ spMap (Gal.hom σ))
    (hinv : ∀ (T : Scheme.{0}) (s : T ⟶ Sp R') (u : T ⟶ N.U.left) (x : T ⟶ G'.left), N.Pt s u x →
      N.Pt (s ≫ spMap (Gal.hom σ)) u (x ≫ g)) : g ≫ β = β := by
  haveI := hG'.smooth
  haveI := N.isOpen
  have hred : IsReduced G'.left := GlobalTheory.isReduced_of_smooth_of_isReduced G'.hom
  have hd := dense_of_closedFibre_sub R' G' hG' N.u.opensRange (fun x hx => by
    obtain ⟨y, hy⟩ := N.all x (by rw [hx]; exact spMap_closedPoint_of_finite ρ hf)
    exact ⟨y, hy⟩)
  haveI : IsDominant N.u := ⟨by simpa [DenseRange] using hd⟩
  have hσ : spMap (Gal.hom σ) ≫ spMap ρ = spMap ρ := by
    unfold spMap
    rw [← Spec.map_comp]
    congr 1
    ext r
    exact σ.2 r
  refine ext_of_isDominant_of_isSeparated G.hom ?_ N.u ?_
  · rw [Category.assoc, hβ, ← Category.assoc, hg, Category.assoc, hσ]
  · obtain ⟨x₁, h1, -, h3⟩ := hinv _ (pullback.snd _ _) (pullback.fst _ _) N.u ⟨𝟙 _, by simp, by simp, by simp⟩
    rw [← Category.assoc, ← h3, Category.assoc, hu, ← Category.assoc, h1]

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedSemiAbelianGaloisDescent

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem has_of_galois_action : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), Base R → FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), GalAct ρ hD U' → Has D := by
  intro R R' _ _ _ _ _ _ ρ hB hF hG D D' hD A' G' _ _ hG' U' a
  obtain ⟨N, hL, hinv⟩ := exists_near_galois_quotient R hB R' ρ hF hG D D' hD A' G' hG' U' a
  have hP : IsProper (spMap ρ) := by
    have : IsFinite (spMap ρ) := (IsFinite.SpecMap_iff _).2 hF.2.2
    infer_instance
  have hS : Surjective (spMap ρ) := ⟨hF.2.2.to_isIntegral.comap_surjective hF.2.1⟩
  obtain ⟨G, _, _, β, i, hGs, hpb, -, hu⟩ :=
    descend_of_near R hB.1 (Sp R') (spMap ρ) hP hS inferInstance G' hG' N hL
  exact has_of_galAct R hB R' ρ hF hG D D' hD A' G' hG' U' a G β hGs hpb fun σ =>
    comp_eq_of_near ρ hF.2.2 G' hG' N G hGs.separated β hpb.1.w i hu σ (a.act σ) (a.cart σ).1.w (hinv σ)

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedSemiAbelianGaloisDescentStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.uniformised_semiAbelian_galois_descent : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), Base R → FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), GalAct ρ hD U' → Has D := by
  first | exact @GlobalTheory.Mum.has_of_galois_action | exact GlobalTheory.Mum.has_of_galois_action | (intros; apply GlobalTheory.Mum.has_of_galois_action <;> assumption)
end
end
