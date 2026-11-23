module

public import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GmEqMapGm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCarriedSectionNonzeroNearClosedFibreStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameNearClosedFibrePointStatement
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCarriedSectionOffClosedFibreStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecCarriedOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleFrameOfSectionUnitsOnClosedFibre
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExp
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.Tactic.Linter.Style
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GlobalFunctionsDvrPowers

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCarriedFrameNearClosedFibre

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem closed_spec {R : Type} [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] (hS : IsSemiAbelian G)
    (y : G.left) (hy : G.hom y = closedPoint R) :
    ∃ y₀ : G.left, y ⤳ y₀ ∧ IsClosed ({y₀} : Set G.left) ∧ G.hom y₀ = closedPoint R := by
  have : QuasiCompact G.hom := hS.quasiCompact
  have hc : CompactSpace G.left := by
    constructor
    have := QuasiCompact.isCompact_preimage (f := G.hom) Set.univ isOpen_univ isCompact_univ
    simpa using this
  obtain ⟨y₀, hy₀, hcl⟩ := (isClosed_closure (s := ({y} : Set G.left))).exists_closed_singleton ⟨y, subset_closure rfl⟩
  have hsp : y ⤳ y₀ := specializes_iff_mem_closure.2 hy₀
  refine ⟨y₀, hsp, hcl, ?_⟩
  have h1 : G.hom y ⤳ G.hom y₀ := hsp.map G.hom.continuous
  rw [hy] at h1
  have h2 := specializes_iff_mem_closure.1 h1
  exact (isClosed_singleton_closedPoint R).closure_subset h2



theorem FrameCarried.exists_near_closed_fibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hF : FinExt ρ) (hG : IsGal ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (hS' : IsSemiAbelian G') (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (hS : IsSemiAbelian G) (hβ : IsGrpPullback G' G (spMap ρ) β) (hact : ∀ σ, a.act σ ≫ β = β), ∀ y : G.left, G.hom y = closedPoint R → ∃ V : G.left.Opens, y ∈ V ∧ ∃ T : ∀ k : U'.LG.L.ι, Γ(G'.left, β ⁻¹ᵁ V ⊓ U'.LG.L.U k)ˣ, IsFrameOver U'.LG.L (β ⁻¹ᵁ V) T ∧ ∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h → FrameCarried U'.LG.L (β ⁻¹ᵁ V) T _ (Classical.choose hP.lg) := by
  intro R _ _ _ hB R' _ _ _ ρ hF hG D D' hD A' G' _ _ hS' U' a G _ _ β hS hβ hact y hy
  obtain ⟨θ, hθ, O, hO, hnz⟩ := GlobalTheory.T.exists_carried_section_nonzero_near_closedFibre R hB R' ρ hF hG D D' hD A' G' hS' U' a G β hS hβ hact
  obtain ⟨y₀, hsp, hcl, hy₀c⟩ := closed_spec G hS y hy
  obtain ⟨V, hV, rest⟩ := GlobalTheory.T.exists_frame_near_closedFibre_point R hB R' ρ hF hG D D' hD A' G' hS' U' a G β hS hβ hact θ hθ O hO hnz y₀ hcl hy₀c
  exact ⟨V, hsp.mem_open V.isOpen hV, rest⟩

end GlobalTheory.Mum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCarriedFrameNearClosedFibreStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_carried_frame_near_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hF : FinExt ρ) (hG : IsGal ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (hS' : IsSemiAbelian G') (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (hS : IsSemiAbelian G) (hβ : IsGrpPullback G' G (spMap ρ) β) (hact : ∀ σ, a.act σ ≫ β = β), ∀ y : G.left, G.hom y = closedPoint R → ∃ V : G.left.Opens, y ∈ V ∧ ∃ T : ∀ k : U'.LG.L.ι, Γ(G'.left, β ⁻¹ᵁ V ⊓ U'.LG.L.U k)ˣ, IsFrameOver U'.LG.L (β ⁻¹ᵁ V) T ∧ ∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h → FrameCarried U'.LG.L (β ⁻¹ᵁ V) T _ (Classical.choose hP.lg) := by
  first | exact @GlobalTheory.Mum.FrameCarried.exists_near_closed_fibre | exact GlobalTheory.Mum.FrameCarried.exists_near_closed_fibre | (intros; apply GlobalTheory.Mum.FrameCarried.exists_near_closed_fibre <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleFrameOfSectionUnitsOnClosedFibreStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_lineBundleFrame_of_section_units_on_closedFibre : ∀ (X Y : Scheme.{0}) (β : X ⟶ Y), IsClosedMap β.base → ∀ (L : LB X), L.IsLB → ∀ (V : Y.Opens) (s : ∀ k : L.ι, Γ(X, β ⁻¹ᵁ V ⊓ L.U k)), IsSecOver L (β ⁻¹ᵁ V) s → ∀ y : Y, y ∈ V → (∀ (z : X) (k : L.ι), β z = y → z ∈ L.U k → IsUnit (gs (𝟙 X) z (β ⁻¹ᵁ V ⊓ L.U k) (s k))) → ∃ V' : Y.Opens, y ∈ V' ∧ V' ≤ V ∧ ∃ T : ∀ k : L.ι, Γ(X, β ⁻¹ᵁ V' ⊓ L.U k)ˣ, IsFrameOver L (β ⁻¹ᵁ V') T ∧ ∀ (f : X ⟶ X) (w : LB.Iso L (L.pull f)), SecCarriedOver L (β ⁻¹ᵁ V) s f w → FrameCarried L (β ⁻¹ᵁ V') T f w := by
  first | exact @GlobalTheory.Mum.exists_frame_of_isUnit_on_fibre | exact GlobalTheory.Mum.exists_frame_of_isUnit_on_fibre | (intros; apply GlobalTheory.Mum.exists_frame_of_isUnit_on_fibre <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationBundleRigidLinearisationsSameLocal

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.RigLinUnique

theorem eq_pull_section {X S S' : Scheme.{0}} (p : X ⟶ S) (e : S ⟶ X) (he : e ≫ p = 𝟙 S) (j : S' ⟶ S)
    (hi : Function.Injective (pullback.fst p j).appTop.hom)
    (hs : Function.Surjective (pullback.snd p j).appTop.hom) (u : Γ(X, ⊤)) :
    u = p.appTop.hom (e.appTop.hom u) := by
  have cmp : ∀ {A B C : Scheme.{0}} (a : A ⟶ B) (b : B ⟶ C) (x : Γ(C, ⊤)),
      a.appTop.hom (b.appTop.hom x) = (a ≫ b).appTop.hom x := fun a b x => by
    rw [Scheme.Hom.comp_appTop]; rfl
  obtain ⟨c, hc⟩ := hs ((pullback.fst p j).appTop.hom u)
  let e' : S' ⟶ pullback p j := pullback.lift (j ≫ e) (𝟙 S') (by rw [Category.assoc, he, Category.comp_id, Category.id_comp])
  have h1 : e' ≫ pullback.fst p j = j ≫ e := pullback.lift_fst _ _ _
  have h2 : e' ≫ pullback.snd p j = 𝟙 S' := pullback.lift_snd _ _ _
  have hc' : c = j.appTop.hom (e.appTop.hom u) := by
    have := congrArg e'.appTop.hom hc
    rw [cmp, cmp, h1, h2, ← cmp, Scheme.Hom.id_appTop] at this
    exact this
  apply hi
  rw [cmp, pullback.condition, ← cmp, ← hc', hc]

theorem exists_ratio {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (hL : L.IsLB) (hL' : L'.IsLB)
    (w₁ w₂ : LB.Iso L' (L.pull F)) (h₁ : PGen w₁) (h₂ : PGen w₂) :
    ∃ u : Γ(X', ⊤)ˣ, ∀ (Y : Scheme.{0}) (g : Y ⟶ X') (y : Y) (j : L.ι) (k : L'.ι), F (g y) ∈ L.U j → g y ∈ L'.U k →
      gw w₂ g y j k = gm g y ⊤ u * gw w₁ g y j k := by
  have key : ∀ (Y : Scheme.{0}) (g : Y ⟶ X') (y : Y) (j : L.ι) (k : L'.ι),
      gm g y ((L.pull F).U (fun _ => j) ⊓ L'.U k) (w₂.s (fun _ => j, k) * (w₁.s (fun _ => j, k))⁻¹) =
        gw w₂ g y j k * (gw w₁ g y j k)⁻¹ := fun Y g y j k =>
    (map_mul _ _ _).trans (congrArg (gw w₂ g y j k * ·) (map_inv _ _))
  obtain ⟨u, hu⟩ := glue_unit (X := X') (J := L.ι × L'.ι) ⊤ (fun p => (L.pull F).U (fun _ => p.1) ⊓ L'.U p.2)
    (fun _ => le_top) (fun x _ => by
      obtain ⟨j, hj⟩ := exists_chart hL (F x)
      obtain ⟨k, hk⟩ := exists_chart hL' x
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(j, k), mem_pull.2 hj, hk⟩)
    (fun p => w₂.s (fun _ => p.1, p.2) * (w₁.s (fun _ => p.1, p.2))⁻¹) (fun p q x hx => by
      have a := h₁ _ (𝟙 X') x p.1 q.1 p.2 q.2 (mem_pull.1 hx.1.1) (mem_pull.1 hx.2.1) hx.1.2 hx.2.2
      have b := h₂ _ (𝟙 X') x p.1 q.1 p.2 q.2 (mem_pull.1 hx.1.1) (mem_pull.1 hx.2.1) hx.1.2 hx.2.2
      refine (key _ _ x p.1 p.2).trans (Eq.trans ?_ (key _ _ x q.1 q.2).symm)
      rw [a, b, ← div_eq_mul_inv, mul_div_mul_left_eq_div, div_eq_mul_inv])
  refine ⟨u, fun Y g y j k hj hk => ?_⟩
  have hm : g y ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
  have : gm g y ⊤ u = gw w₂ g y j k * (gw w₁ g y j k)⁻¹ := (gm_res g y le_top hm u).symm.trans
    ((congrArg (gm g y ((L.pull F).U (fun _ => j) ⊓ L'.U k)) (hu (j, k))).trans (key Y g y j k))
  rw [this]
  exact (inv_mul_cancel_right _ _).symm

theorem gw_eq_of_rigidified : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (D' : DegData R' (maximalIdeal R')) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (s : Sp R' ⟶ Sp R') (f₁ f₂ : G'.left ⟶ G'.left), f₁ = f₂ → ∀ (he₁ : eSec G' ≫ f₁ = s ≫ eSec G') (he₂ : eSec G' ≫ f₂ = s ≫ eSec G') (w₁ : LB.Iso U'.LG.L (U'.LG.L.pull f₁)) (w₂ : LB.Iso U'.LG.L (U'.LG.L.pull f₂)), w₁.IsGen → w₂.IsGen → LB.Gen.Maps (LB.linCombIso w₁ (K := PUnit) (fun _ => eSec G') (fun _ => 1)) U'.LG.rig (rigPullOf f₁ s he₁ U'.LG.L U'.LG.rig) → LB.Gen.Maps (LB.linCombIso w₂ (K := PUnit) (fun _ => eSec G') (fun _ => 1)) U'.LG.rig (rigPullOf f₂ s he₂ U'.LG.L U'.LG.rig) → ∀ (z : G'.left) (j k : U'.LG.L.ι), z ∈ U'.LG.L.U k → f₁ z ∈ U'.LG.L.U j → gw w₁ (𝟙 G'.left) z j k = gw w₂ (𝟙 G'.left) z j k := by
  intro R' _ _ _ D' A' G' _ _ hS U' s f₁ f₂ hf he₁ he₂ w₁ w₂ g₁ g₂ m₁ m₂ z j k hk hj
  subst hf
  have hL := U'.LG.isLB
  obtain ⟨u, hu⟩ := exists_ratio hL hL w₁ w₂ ((isGen_iff w₁).1 g₁) ((isGen_iff w₂).1 g₂)
  have p₁ := (maps_iff w₁ _ (fun _ => eSec G') _ U'.LG.rig U'.LG.rig s _ (rigPull_le f₁ s he₁ U'.LG.L)
    (fun _ => rfl)).1 m₁
  have p₂ := (maps_iff w₂ _ (fun _ => eSec G') _ U'.LG.rig U'.LG.rig s _ (rigPull_le f₁ s he₂ U'.LG.L)
    (fun _ => rfl)).1 m₂
  have he1 : pullU (eSec G') ⊤ u = 1 := by
    apply unit_ext
    intro x _
    obtain ⟨a, ha⟩ := exists_chart hL (f₁ (eSec G' x))
    obtain ⟨b, hb⟩ := exists_chart hL (eSec G' x)
    have q₁ := p₁ _ (𝟙 _) x (fun _ => a) (fun _ => b) (fun _ => ha) (fun _ => hb)
    have q₂ := p₂ _ (𝟙 _) x (fun _ => a) (fun _ => b) (fun _ => ha) (fun _ => hb)
    have q := mul_right_cancel (q₂.symm.trans q₁)
    rw [Fintype.prod_unique, Fintype.prod_unique, zpow_one, zpow_one, hu _ (𝟙 _ ≫ eSec G') x a b ha hb] at q
    rw [map_one]
    exact (gm_pull (𝟙 _) (eSec G') x ⊤ trivial u).trans (mul_eq_right.1 q)
  have := U'.smooth
  have : Flat G'.hom := inferInstance
  have : IsDominant (jK R') := by
    rw [isDominant_iff]
    show DenseRange (PrimeSpectrum.comap (algebraMap R' (FractionRing R')))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R' (FractionRing R'))]
    exact bot_le
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R')
  have : IsSchemeTheoreticallyDominant (pullback.fst G'.hom (jK R')) :=
    IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback G'.hom (jK R')).flip
  have hb := GlobalFunctionsDvrPowers.bijective_of_iso U'.gen (GlobalTheory.SemiRigid.globalFns _ A'.A A'.isAb)
  have hv := eq_pull_section G'.hom (eSec G') (Over.w η[G']) (jK R')
    ((pullback.fst G'.hom (jK R')).app_injective ⊤) hb.2 u.val
  have he2 : (eSec G').appTop.hom u.val = 1 := congrArg Units.val he1
  have hu1 : u = 1 := Units.ext (hv.trans ((congrArg G'.hom.appTop.hom he2).trans (map_one _)))
  rw [hu _ (𝟙 _) z j k hj hk, hu1, map_one, _root_.one_mul]

end GlobalTheory.Mum.RigLinUnique
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationBundleRigidLinearisationsSameLocalStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.uniformisationBundle_rigidLinearisations_same_localUnits : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (D' : DegData R' (maximalIdeal R')) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (s : Sp R' ⟶ Sp R') (f₁ f₂ : G'.left ⟶ G'.left), f₁ = f₂ → ∀ (he₁ : eSec G' ≫ f₁ = s ≫ eSec G') (he₂ : eSec G' ≫ f₂ = s ≫ eSec G') (w₁ : LB.Iso U'.LG.L (U'.LG.L.pull f₁)) (w₂ : LB.Iso U'.LG.L (U'.LG.L.pull f₂)), w₁.IsGen → w₂.IsGen → LB.Gen.Maps (LB.linCombIso w₁ (K := PUnit) (fun _ => eSec G') (fun _ => 1)) U'.LG.rig (rigPullOf f₁ s he₁ U'.LG.L U'.LG.rig) → LB.Gen.Maps (LB.linCombIso w₂ (K := PUnit) (fun _ => eSec G') (fun _ => 1)) U'.LG.rig (rigPullOf f₂ s he₂ U'.LG.L U'.LG.rig) → ∀ (z : G'.left) (j k : U'.LG.L.ι), z ∈ U'.LG.L.U k → f₁ z ∈ U'.LG.L.U j → gw w₁ (𝟙 G'.left) z j k = gw w₂ (𝟙 G'.left) z j k := by
  first | exact @GlobalTheory.Mum.RigLinUnique.gw_eq_of_rigidified | exact GlobalTheory.Mum.RigLinUnique.gw_eq_of_rigidified | (intros; apply GlobalTheory.Mum.RigLinUnique.gw_eq_of_rigidified <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCarriedFrameOffClosedFibre

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum



theorem exists_carried_frame_off_closed : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hF : FinExt ρ) (hG : IsGal ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (hS' : IsSemiAbelian G') (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (hS : IsSemiAbelian G) (hβ : IsGrpPullback G' G (spMap ρ) β) (hact : ∀ σ, a.act σ ≫ β = β), ∀ y : G.left, G.hom y ≠ closedPoint R → ∃ V : G.left.Opens, y ∈ V ∧ ∃ T : ∀ k : U'.LG.L.ι, Γ(G'.left, β ⁻¹ᵁ V ⊓ U'.LG.L.U k)ˣ, IsFrameOver U'.LG.L (β ⁻¹ᵁ V) T ∧ ∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h → FrameCarried U'.LG.L (β ⁻¹ᵁ V) T _ (Classical.choose hP.lg) := by
  intro R _ _ _ hB R' _ _ _ ρ hF hG D D' hD A' G' _ _ hS' U' a G _ _ β hS hβ hact y hy
  have hβc : IsClosedMap β.base := by
    haveI : IsFinite (spMap ρ) := (IsFinite.SpecMap_iff _).2 hF.2.2
    haveI : IsFinite β := MorphismProperty.of_isPullback (P := @IsFinite) hβ.1.flip inferInstance
    exact β.isClosedMap
  obtain ⟨V, hyV, s, hs, hun, hcar⟩ := GlobalTheory.T.exists_carried_section_off_closedFibre R hB R' ρ hF hG D D' hD A' G' hS' U' a G β hS hβ hact y hy
  obtain ⟨V', hyV', -, T, hT, htr⟩ := GlobalTheory.T.exists_lineBundleFrame_of_section_units_on_closedFibre _ _ β hβc U'.LG.L U'.LG.isLB V s hs y hyV hun
  refine ⟨V', hyV', T, hT, ?_⟩
  intro σ h bc hbc hP hPO
  refine (hcar σ).elim fun h₀ hc => hc.elim fun bc₀ hc => ?_
  refine hc.2.elim fun hP₀ hc' => ?_
  have hF₀ := htr _ _ hc'.2
  have e : bc₀.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) =
      bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) := hc.1.trans hbc.symm
  have s₁ := Classical.choose_spec hP.lg
  have s₀ := Classical.choose_spec hP₀.lg
  refine s₁.2.elim fun he₁ m₁ => s₀.2.elim fun he₀ m₀ => ?_
  have hg := GlobalTheory.T.uniformisationBundle_rigidLinearisations_same_localUnits R' D' A' G' hS' U' (specOf (Gal.hom σ)) _ _ e he₀ he₁ _ _ s₀.1 s₁.1 m₀.1 m₁.1
  intro z j k hz hfz hzk hfzj
  have h1 := hF₀ z j k hz (by rw [e]; exact hfz) hzk (by rw [e]; exact hfzj)
  rw [hg z j k hzk (by rw [e]; exact hfzj)] at h1
  rw [e] at h1
  exact h1

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCarriedFrameOffClosedFibreStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_carried_frame_off_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hF : FinExt ρ) (hG : IsGal ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (hS' : IsSemiAbelian G') (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (hS : IsSemiAbelian G) (hβ : IsGrpPullback G' G (spMap ρ) β) (hact : ∀ σ, a.act σ ≫ β = β), ∀ y : G.left, G.hom y ≠ closedPoint R → ∃ V : G.left.Opens, y ∈ V ∧ ∃ T : ∀ k : U'.LG.L.ι, Γ(G'.left, β ⁻¹ᵁ V ⊓ U'.LG.L.U k)ˣ, IsFrameOver U'.LG.L (β ⁻¹ᵁ V) T ∧ ∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h → FrameCarried U'.LG.L (β ⁻¹ᵁ V) T _ (Classical.choose hP.lg) := by
  first | exact @GlobalTheory.Mum.exists_carried_frame_off_closed | exact GlobalTheory.Mum.exists_carried_frame_off_closed | (intros; apply GlobalTheory.Mum.exists_carried_frame_off_closed <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisInvariantLocalFramesUniformisation

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem unif_lb_frames_gal : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), ∀ (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → (∀ σ, a.act σ ≫ β = β) → ∃ (V : G.left → G.left.Opens) (T : ∀ (y : G.left) (k : U'.LG.L.ι), Γ(G'.left, β ⁻¹ᵁ V y ⊓ U'.LG.L.U k)ˣ), (∀ y, y ∈ V y) ∧ (∀ y k k', res (inf_le_left : β ⁻¹ᵁ V y ⊓ U'.LG.L.U k ⊓ (β ⁻¹ᵁ V y ⊓ U'.LG.L.U k') ≤ β ⁻¹ᵁ V y ⊓ U'.LG.L.U k) (T y k) = res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) : β ⁻¹ᵁ V y ⊓ U'.LG.L.U k ⊓ (β ⁻¹ᵁ V y ⊓ U'.LG.L.U k') ≤ U'.LG.L.U k ⊓ U'.LG.L.U k') (U'.LG.L.g k k') * res (inf_le_right : β ⁻¹ᵁ V y ⊓ U'.LG.L.U k ⊓ (β ⁻¹ᵁ V y ⊓ U'.LG.L.U k') ≤ β ⁻¹ᵁ V y ⊓ U'.LG.L.U k') (T y k')) ∧ ∀ (y y' : G.left) (r : Γ(G'.left, β ⁻¹ᵁ (V y ⊓ V y'))ˣ), (∀ (z : G'.left) (k : U'.LG.L.ι), z ∈ β ⁻¹ᵁ (V y ⊓ V y') → z ∈ U'.LG.L.U k → gm (𝟙 G'.left) z _ r = gm (𝟙 G'.left) z _ (T y' k) * (gm (𝟙 G'.left) z _ (T y k))⁻¹) → ∀ σ (h : β ⁻¹ᵁ (V y ⊓ V y') ≤ a.act σ ⁻¹ᵁ (β ⁻¹ᵁ (V y ⊓ V y'))), ((a.act σ).appLE _ _ h).hom r.val = r.val := by
  intro R _ _ _ hB R' _ _ _ ρ hF hG D D' hD A' G' _ _ hS' U' a G _ _ β hS hβ hact
  have key : ∀ y : G.left, ∃ V : G.left.Opens, y ∈ V ∧ ∃ T : ∀ k : U'.LG.L.ι, Γ(G'.left, β ⁻¹ᵁ V ⊓ U'.LG.L.U k)ˣ, IsFrameOver U'.LG.L (β ⁻¹ᵁ V) T ∧ ∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h → FrameCarried U'.LG.L (β ⁻¹ᵁ V) T _ (Classical.choose hP.lg) := by
    intro y
    by_cases hy : G.hom y = closedPoint R
    · exact GlobalTheory.T.exists_carried_frame_near_closedFibre R hB R' ρ hF hG D D' hD A' G' hS' U' a G β hS hβ hact y hy
    · exact GlobalTheory.T.exists_carried_frame_off_closedFibre R hB R' ρ hF hG D D' hD A' G' hS' U' a G β hS hβ hact y hy
  choose V hV T hT hI using key
  refine ⟨V, T, hV, hT, ?_⟩
  intro y y' r hr σ h
  obtain ⟨hh, bc, hf, hP, hPO⟩ := a.unif σ
  have i₁ := hI y σ hh bc hf hP hPO
  have i₂ := hI y' σ hh bc hf hP hPO
  revert h
  rw [← hf]
  intro h
  exact FrameCarried.ratio_fixed U'.LG.isLB i₁ i₂ (fun z (hz : z ∈ β ⁻¹ᵁ (V y ⊓ V y')) => hz.1)
    (fun z (hz : z ∈ β ⁻¹ᵁ (V y ⊓ V y')) => hz.2) r hr h

end GlobalTheory.Mum
end
end
