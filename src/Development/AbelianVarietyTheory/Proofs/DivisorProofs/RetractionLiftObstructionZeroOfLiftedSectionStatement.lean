module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechTripleRestrictCompositeInjectiveSecond
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPairRestrictBaseChangeBijectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNaturalChartLiftsOfMorphism
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLiftsSqZeroClassifiedByDifferentials
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapBasicPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapInjectiveOfFlatStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapNaturalStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAugmentationTensorSigmaMapStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDifferenceDerivationOfLiftsAddSwapUniqueStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDifferenceDerivationOfLiftsCompStatement
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.AlgebraicGeometry.Modules.Sheaf

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNaturalChartLiftsOfMorphismStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_natural_chart_lifts_of_morphism : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ Z₀ X Z : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (t₀ : Z₀ ⟶ Sp R₀) (s : X ⟶ Sp R) (t : Z ⟶ Sp R) (i : X₀ ⟶ X) (k : Z₀ ⟶ Z) (hi : IsPullback i s₀ s (spMap π)) (hkk : IsPullback k t₀ t (spMap π)) (S : Sys I π s₀) (S' : Sys I π t₀) (P : S.Presents s i) (P' : S'.Presents t k) (f₀ : Z₀ ⟶ X₀) (h : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (f : Z ⟶ X), f ≫ s = t → k ≫ f = f₀ ≫ i → ∃ (l : ∀ T : (Pair f₀)ᵒᵖ, (ofSys S).B ((pairPull h).G.obj T) →ₐ[R] (pairPre S' f₀).B T), (ofSys S).IsLift (pairPre S' f₀) (pairPull h) l ∧ (ofSys S).IsNat (pairPre S' f₀) (pairPull h) l := by
  first | exact @GlobalTheory.Obs.exists_chart_lifts | exact GlobalTheory.Obs.exists_chart_lifts | (intros; apply GlobalTheory.Obs.exists_chart_lifts <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ObstructionPullbackEqZeroOfNaturalLift

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs

theorem obstructionPullback_eq_zero_of_naturalLift : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (C' : Type) [Category.{0} C'] (F' : C' ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (L' : Pre I π F') (n : CoefMap (RingHom.id R₀) F F') (l : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T) (C'' : Type) [Category.{0} C''] (F'' : C'' ⥤ CommAlgCat.{0} R₀) (L'' : Pre I π F'') (m : CoefMap (RingHom.id R₀) F' F'') (u : ∀ T : C'', L'.B (m.G.obj T) →ₐ[R] L''.B T) (v : ∀ T : C'', L.B (n.G.obj (m.G.obj T)) →ₐ[R] L''.B T), L.IsLift L' n l → L'.IsLift L'' m u → L'.IsNat L'' m u → (∀ T b, L''.p T (v T b) = m.α T (n.α _ (L.p _ b))) → (∀ (T T' : C'') (a : T ⟶ T') b, L''.ρ a (v T b) = v T' (L.ρ (n.G.map (m.G.map a)) b)) → ∀ (w : Glob1 F) (c : GlobalTheory.CatCoh.H1 (ext R₁ F')), L.IsOb1 L' n l α w c → (extMap R₁ m).pull1 c = 0 := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F C' _ F' L L' n l C'' _ F'' L'' m u v hl hu hun hvp hvn w c hc
  obtain ⟨κ, σ', z, hκ, hσ', rfl, hz⟩ := hc
  choose σ'' hσ'' using fun T : C'' ↦ GlobalTheory.T.exists_augmentation_tensor_sigma_map R R₀ I hI π hπ hk R₁ α (L''.B T) (F''.obj T) (L''.p T)
    (L''.semi T) (L''.surj T) (L''.ker T)

  have hdiff : ∀ (T : C'') (b : L.B (n.G.obj (m.G.obj T))),
      (u T).comp (l (m.G.obj T)) b - v T b ∈ I.map (algebraMap R (L''.B T)) := fun T b ↦ by
    refine (L''.ker T _).1 ?_
    rw [map_sub, sub_eq_zero]
    exact (hu T _).trans ((congrArg (m.α T) (hl _ b)).trans (hvp T b).symm)
  choose th hth using fun T : C'' ↦ ((theta_classify R R₀ (L.B (n.G.obj (m.G.obj T))) (F.obj (n.G.obj (m.G.obj T)))
    (L''.B T) I hI π hπ (L.p _) (L.semi _) (L.surj _) (L.ker _) ((u T).comp (l (m.G.obj T)))).1 (v T) (hdiff T)).exists

  have key : ∀ (T T' : C'') (a : T ⟶ T'),
      L''.ρ a (th T (w.1 (n.G.obj (m.G.obj T)))) =
        u T' (κ _ _ (m.G.map a) (w.1 (n.G.obj (m.G.obj T)))) + th T' (w.1 (n.G.obj (m.G.obj T'))) := by
    intro T T' a
    have h1 := (GlobalTheory.T.isDifferenceDerivationOfLifts_comp R R₀ I hI π hπ hk (L.B (n.G.obj (m.G.obj T))) (F.obj (n.G.obj (m.G.obj T))) (L.p _)
      (L.semi _) (L.surj _) (L.ker _) (L.B (n.G.obj (m.G.obj T))) (F.obj (n.G.obj (m.G.obj T))) (L.p _)
      (L.semi _) (L.surj _) (L.ker _) (L'.B (m.G.obj T')) (L''.B T') _ _ _ (hκ _ _ (m.G.map a))).1 (u T')
    have h2 := (GlobalTheory.T.isDifferenceDerivationOfLifts_comp R R₀ I hI π hπ hk (L.B (n.G.obj (m.G.obj T'))) (F.obj (n.G.obj (m.G.obj T'))) (L.p _)
      (L.semi _) (L.surj _) (L.ker _) (L.B (n.G.obj (m.G.obj T))) (F.obj (n.G.obj (m.G.obj T))) (L.p _)
      (L.semi _) (L.surj _) (L.ker _) (L''.B T') (L''.B T') _ _ _ (hth T')).2 (L.ρ (n.G.map (m.G.map a)))
      (mp F (n.G.map (m.G.map a))) (fun x ↦ L.nat _ x)
    rw [AlgHom.comp_assoc] at h2
    have h3 := (GlobalTheory.T.isDifferenceDerivationOfLifts_add_swap_unique R R₀ I hI π hπ hk _ _ (L.p (n.G.obj (m.G.obj T))) (L.semi _) (L.surj _) (L.ker _)
      (L''.B T') _ _ _ _ _ h1).2.1 h2
    have h4 := (GlobalTheory.T.isDifferenceDerivationOfLifts_comp R R₀ I hI π hπ hk (L.B (n.G.obj (m.G.obj T))) (F.obj (n.G.obj (m.G.obj T))) (L.p _)
      (L.semi _) (L.surj _) (L.ker _) (L.B (n.G.obj (m.G.obj T))) (F.obj (n.G.obj (m.G.obj T))) (L.p _)
      (L.semi _) (L.surj _) (L.ker _) (L''.B T) (L''.B T') _ _ _ (hth T)).1 (L''.ρ a)
    have e1 : (L''.ρ a).comp ((u T).comp (l (m.G.obj T))) =
        (u T').comp ((L'.ρ (m.G.map a)).comp (l (m.G.obj T))) := AlgHom.ext fun b ↦ hun a _
    have e2 : (L''.ρ a).comp (v T) = (v T').comp (L.ρ (n.G.map (m.G.map a))) := AlgHom.ext fun b ↦ hvn T T' a b
    rw [e1, e2] at h4
    have h5 := (GlobalTheory.T.isDifferenceDerivationOfLifts_add_swap_unique R R₀ I hI π hπ hk _ _ (L.p (n.G.obj (m.G.obj T))) (L.semi _) (L.surj _) (L.ker _)
      (L''.B T') _ _ ((v T').comp (L.ρ (n.G.map (m.G.map a)))) _ _ h4).2.2 |>.1 <| h3
    have h6 := DFunLike.congr_fun h5 (w.1 (n.G.obj (m.G.obj T)))
    rw [w.2 (n.G.map (m.G.map a))]
    exact h6
  choose g hgK hg using fun T : C'' ↦ (GlobalTheory.T.augmentation_sigma_map_basic_properties R R₀ I hI π hπ hk R₁ α (L''.B T) (F''.obj T) (L''.p T)
    (L''.semi T) (L''.surj T) (L''.ker T) (σ'' T) (hσ'' T)).2.2.2 (-(th T (w.1 (n.G.obj (m.G.obj T)))))
    (neg_mem ((hth T).mem _))
  rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_zero]
  refine ⟨g, ?_⟩
  funext T T' a
  have sg := GlobalTheory.T.augmentation_sigma_map_natural R R₀ I hI π hπ hk R₁ α (L''.B T) (F''.obj T) (L''.p T) (L''.semi T) (L''.surj T)
    (L''.ker T) (L''.B T') (F''.obj T') (L''.p T') (L''.semi T') (L''.surj T') (L''.ker T') (L''.ρ a) (mp F'' a)
    (fun b ↦ L''.nat a b) (σ'' T) (σ'' T') (hσ'' T) (hσ'' T')
  have su := GlobalTheory.T.augmentation_sigma_map_natural R R₀ I hI π hπ hk R₁ α (L'.B (m.G.obj T')) (F'.obj (m.G.obj T')) (L'.p _) (L'.semi _)
    (L'.surj _) (L'.ker _) (L''.B T') (F''.obj T') (L''.p T') (L''.semi T') (L''.surj T') (L''.ker T') (u T')
    (coefHom m T') (fun b ↦ hu T' b) (σ' _) (σ'' T') (hσ' _) (hσ'' T')
  haveI : Algebra.Smooth R (L''.B T') := L''.smooth T'
  change g T' - extHom R₁ (mp F'' a) (g T) = extHom R₁ (coefHom m T') (z.1 _ _ (m.G.map a))
  refine sub_eq_zero.1 (GlobalTheory.T.augmentation_sigma_map_injective_of_flat R R₀ I hI π hπ hk R₁ α (L''.B T') (F''.obj T') (L''.p T') (L''.semi T')
    (L''.surj T') (L''.ker T') (σ'' T') (hσ'' T') _ ?_ ?_)
  · have k1 := hgK T'
    have k2 := sg.2 _ (hgK T)
    have k3 := su.2 _ (hz _ _ (m.G.map a)).1
    unfold Aug.KerQ at k1 k2 k3 ⊢
    rw [map_sub, map_sub, k1, k2, k3, sub_zero, sub_zero]
  · rw [map_sub, map_sub, hg T', ← sg.1, hg T, ← su.1, (hz _ _ _).2, map_neg, key T T' a]
    abel

end GlobalTheory.Obs
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ObstructionPullbackEqZeroOfNaturalLiftStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.obstructionPullback_eq_zero_of_naturalLift_alt : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (C' : Type) [Category.{0} C'] (F' : C' ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (L' : Pre I π F') (n : CoefMap (RingHom.id R₀) F F') (l : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T) (C'' : Type) [Category.{0} C''] (F'' : C'' ⥤ CommAlgCat.{0} R₀) (L'' : Pre I π F'') (m : CoefMap (RingHom.id R₀) F' F'') (u : ∀ T : C'', L'.B (m.G.obj T) →ₐ[R] L''.B T) (v : ∀ T : C'', L.B (n.G.obj (m.G.obj T)) →ₐ[R] L''.B T), L.IsLift L' n l → L'.IsLift L'' m u → L'.IsNat L'' m u → (∀ T b, L''.p T (v T b) = m.α T (n.α _ (L.p _ b))) → (∀ (T T' : C'') (a : T ⟶ T') b, L''.ρ a (v T b) = v T' (L.ρ (n.G.map (m.G.map a)) b)) → ∀ (w : Glob1 F) (c : GlobalTheory.CatCoh.H1 (ext R₁ F')), L.IsOb1 L' n l α w c → (extMap R₁ m).pull1 c = 0 := by
  first | exact @GlobalTheory.Obs.obstructionPullback_eq_zero_of_naturalLift | exact GlobalTheory.Obs.obstructionPullback_eq_zero_of_naturalLift | (intros; apply GlobalTheory.Obs.obstructionPullback_eq_zero_of_naturalLift <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RetractionLiftObstructionZeroOfLiftedSection

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs

theorem appLE_apply_of_eq_id {X : Scheme.{0}} {g : X ⟶ X} (hg : g = 𝟙 X) {U V : X.Opens} (e : V ≤ g ⁻¹ᵁ U)
    (e' : V ≤ U) (x : Γ(X, U)) : (g.appLE U V e).hom x = (X.presheaf.map (homOfLE e').op).hom x := by
  subst hg
  simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp]
  rfl

theorem appLE_appLE_of_retr {X₀ Z₀ : Scheme.{0}} {j₀ : X₀ ⟶ Z₀} {f₀ : Z₀ ⟶ X₀} (hjf : j₀ ≫ f₀ = 𝟙 X₀)
    (U : X₀.Opens) (U' : Z₀.Opens) (U'' : X₀.Opens) (e₁ : U' ≤ f₀ ⁻¹ᵁ U) (e₂ : U'' ≤ j₀ ⁻¹ᵁ U')
    (e : U'' ≤ U) (x : Γ(X₀, U)) :
    (j₀.appLE U' U'' e₂).hom ((f₀.appLE U U' e₁).hom x) = (X₀.presheaf.map (homOfLE e).op).hom x := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  exact appLE_apply_of_eq_id hjf _ e x

theorem ext_tri_res_pull1 {R₀ : Type} [CommRing R₀] (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁]
    {X X' X'' : Scheme.{0}} {ψ : X'' ⟶ X'} {φ : X' ⟶ X} {s' : X' ⟶ Sp R₀} {s'' : X'' ⟶ Sp R₀}
    (h' : ψ ≫ s' = s'' ≫ spMap (RingHom.id R₀)) (a : CatCoh.H1 (ext R₁ (OAff s'))) :
    (extMap R₁ (cechTriplePullbackSecond (φ := φ) h')).pull1 ((extMap R₁ (pairRes φ s')).pull1 a) =
      (extMap R₁ (cechTripleRestrictFirst ψ φ s'')).pull1 ((extMap R₁ (pairPull h')).pull1 a) := by
  rw [← CoefMap.pullCohomologyOne_comp, ← CoefMap.pullCohomologyOne_comp]
  refine CoefMap.pullCohomologyOne_eq_of_natTrans ((extMap R₁ (pairRes φ s')).comp (extMap R₁ (cechTriplePullbackSecond (φ := φ) h')))
    ((extMap R₁ (pairPull h')).comp (extMap R₁ (cechTripleRestrictFirst ψ φ s''))) { app U := 𝟙 _ } (fun U b ↦ ?_) a
  erw [mp_id]
  induction b using TensorProduct.induction_on with
  | zero => (erw [map_zero]) <;> rfl
  | tmul x y => rfl
  | add x y hx hy => erw [map_add, map_add, hx, hy]

theorem retractionLiftObstruction_zero_of_liftedSection_alt : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ Z₀ X Z : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (t₀ : Z₀ ⟶ Sp R₀) (s : X ⟶ Sp R) (t : Z ⟶ Sp R) (i : X₀ ⟶ X) (k : Z₀ ⟶ Z) (hi : IsPullback i s₀ s (spMap π)) (hkk : IsPullback k t₀ t (spMap π)) (S : Sys I π s₀) (S' : Sys I π t₀) (P : S.Presents s i) (P' : S'.Presents t k) (f₀ : Z₀ ⟶ X₀) (h : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (j₀ : X₀ ⟶ Z₀) (hj : j₀ ≫ t₀ = s₀ ≫ spMap (RingHom.id R₀)) (j : X ⟶ Z), j₀ ≫ f₀ = 𝟙 X₀ → j ≫ t = s → i ≫ j = j₀ ≫ k → ∀ (l : ∀ T : (Pair f₀)ᵒᵖ, (ofSys S).B ((pairPull h).G.obj T) →ₐ[R] (pairPre S' f₀).B T), (ofSys S).IsLift (pairPre S' f₀) (pairPull h) l → ∀ (w : GlobForm s₀) (c : GlobalTheory.CatCoh.H1 (ext R₁ (OAff t₀))), (ofSys S).IsOb1 (pairPre S' f₀) (pairPull h) l α w ((extMap R₁ (pairRes f₀ t₀)).pull1 c) → IsExtendedPullbackDegOne R₁ hj c 0 := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α X₀ Z₀ X Z s₀ t₀ s t i k hi hkk S S' P P' f₀ h j₀ hj j hjf hjt hij l hl w c hob
  obtain ⟨l', hl'L, hl'N⟩ := GlobalTheory.T.exists_natural_chart_lifts_of_morphism R R₀ I hI π hπ hk Z₀ X₀ Z X t₀ s₀ t s k i hkk hi S' S P' P j₀ hj j hjt hij
  have hle : ∀ T : (Triple j₀ f₀)ᵒᵖ, T.unop.1.1 ≤ T.unop.1.2.2 := fun T x hx ↦ by
    have h1 := T.unop.2.2 (T.unop.2.1 hx)
    have e := congrArg (fun g : X₀ ⟶ X₀ ↦ g.base x) hjf
    simp at e
    exact e ▸ h1
  let L'' : Pre I π (OTriple j₀ f₀ s₀) := (ofSys S).restrict (cechTripleProjFirstThird j₀ f₀ ⋙ pairFst (j₀ ≫ f₀))
  let u : ∀ T : (Triple j₀ f₀)ᵒᵖ, (pairPre S' f₀).B ((cechTriplePullbackSecond (φ := f₀) hj).G.obj T) →ₐ[R] L''.B T :=
    fun T ↦ l' ((cechTripleProjFirstSecond j₀ f₀).obj T)
  let v : ∀ T : (Triple j₀ f₀)ᵒᵖ, (ofSys S).B ((pairPull h).G.obj ((cechTriplePullbackSecond (φ := f₀) hj).G.obj T)) →ₐ[R] L''.B T :=
    fun T ↦ mp S.F (homOfLE (hle T)).op
  have hvan := GlobalTheory.T.obstructionPullback_eq_zero_of_naturalLift_alt R R₀ I hI π hπ hk R₁ α (AffOp X₀) (OAff s₀) (Pair f₀)ᵒᵖ (OPair f₀ t₀) (ofSys S)
    (pairPre S' f₀) (pairPull h) l (Triple j₀ f₀)ᵒᵖ (OTriple j₀ f₀ s₀) L'' (cechTriplePullbackSecond hj) u v hl
    (fun T b ↦ hl'L ((cechTripleProjFirstSecond j₀ f₀).obj T) b)
    (fun T T' a b ↦ by
      have e1 : (cechTripleProjFirstThird j₀ f₀ ⋙ pairFst (j₀ ≫ f₀)).map a = (pairFst j₀).map ((cechTripleProjFirstSecond j₀ f₀).map a) :=
        Quiver.Hom.unop_inj (Subsingleton.elim _ _)
      have e2 : (pairFst f₀).map ((cechTripleProjSecondThird j₀ f₀).map a) = (pairSnd j₀).map ((cechTripleProjFirstSecond j₀ f₀).map a) :=
        Quiver.Hom.unop_inj (Subsingleton.elim _ _)
      change mp S.F ((cechTripleProjFirstThird j₀ f₀ ⋙ pairFst (j₀ ≫ f₀)).map a) (l' ((cechTripleProjFirstSecond j₀ f₀).obj T) b) =
        l' ((cechTripleProjFirstSecond j₀ f₀).obj T') (mp S'.F ((pairFst f₀).map ((cechTripleProjSecondThird j₀ f₀).map a)) b)
      rw [e1, e2]
      exact hl'N ((cechTripleProjFirstSecond j₀ f₀).map a) b)
    (fun T b ↦ by
      change S.p _ (mp S.F _ b) = (j₀.appLE _ _ _).hom ((f₀.appLE _ _ _).hom (S.p _ b))
      exact (S.nat _ b).trans (appLE_appLE_of_retr hjf _ _ _ _ _ (hle T) _).symm)
    (fun T T' a b ↦ by
      change mp S.F _ (mp S.F _ b) = mp S.F _ (mp S.F _ b)
      exact (mp_comp S.F _ _ b).symm.trans ((congrArg (fun q ↦ mp S.F q b)
        (Quiver.Hom.unop_inj (Subsingleton.elim _ _))).trans (mp_comp S.F _ _ b)))
    w ((extMap R₁ (pairRes f₀ t₀)).pull1 c) hob
  rw [ext_tri_res_pull1] at hvan
  have inj := (GlobalTheory.T.cechPairRestrict_baseChange_bijective R₀ R₁ Z₀ X₀ s₀ j₀).2 X₀ f₀
  unfold IsExtendedPullbackDegOne
  rw [map_zero]
  exact inj (hvan.trans (map_zero _).symm)

end GlobalTheory.Obs
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RetractionLiftObstructionZeroOfLiftedSectionStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.retractionLiftObstruction_zero_of_liftedSection : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ Z₀ X Z : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (t₀ : Z₀ ⟶ Sp R₀) (s : X ⟶ Sp R) (t : Z ⟶ Sp R) (i : X₀ ⟶ X) (k : Z₀ ⟶ Z) (hi : IsPullback i s₀ s (spMap π)) (hkk : IsPullback k t₀ t (spMap π)) (S : Sys I π s₀) (S' : Sys I π t₀) (P : S.Presents s i) (P' : S'.Presents t k) (f₀ : Z₀ ⟶ X₀) (h : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (j₀ : X₀ ⟶ Z₀) (hj : j₀ ≫ t₀ = s₀ ≫ spMap (RingHom.id R₀)) (j : X ⟶ Z), j₀ ≫ f₀ = 𝟙 X₀ → j ≫ t = s → i ≫ j = j₀ ≫ k → ∀ (l : ∀ T : (Pair f₀)ᵒᵖ, (ofSys S).B ((pairPull h).G.obj T) →ₐ[R] (pairPre S' f₀).B T), (ofSys S).IsLift (pairPre S' f₀) (pairPull h) l → ∀ (w : GlobForm s₀) (c : GlobalTheory.CatCoh.H1 (ext R₁ (OAff t₀))), (ofSys S).IsOb1 (pairPre S' f₀) (pairPull h) l α w ((extMap R₁ (pairRes f₀ t₀)).pull1 c) → IsExtendedPullbackDegOne R₁ hj c 0 := by
  first | exact @GlobalTheory.Obs.retractionLiftObstruction_zero_of_liftedSection_alt | exact GlobalTheory.Obs.retractionLiftObstruction_zero_of_liftedSection_alt | (intros; apply GlobalTheory.Obs.retractionLiftObstruction_zero_of_liftedSection_alt <;> assumption)
end
end
