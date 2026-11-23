module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjModelBaseChangeStandardOpenAppInjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjModelBaseChangeStandardOpenAppSurjectiveStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQuasiAffineCartierSectionGeneratingLocusAmple

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.Desc.LocusQA

open GlobalTheory.Cartier.CartierDiv

variable {Y : Scheme.{0}} [IsIntegral Y] {y : Y}

theorem regAt_pow {f : Y.functionField} (hf : RegAt y f) (n : ℕ) : RegAt y (f ^ n) := by
  obtain ⟨a, rfl⟩ := hf
  exact ⟨a ^ n, map_pow _ _ _⟩

theorem unitAt_pow_iff {f : Y.functionField} (hf : RegAt y f) {n : ℕ} (hn : n ≠ 0) :
    UnitAt y (f ^ n) ↔ UnitAt y f := by
  obtain ⟨a, rfl⟩ := hf
  refine ⟨fun ⟨b, hb, e⟩ => ?_, fun ⟨b, hb, e⟩ => ⟨b ^ n, hb.pow n, by rw [map_pow, e]⟩⟩
  rw [← map_pow] at e
  obtain rfl := IsFractionRing.injective (Y.presheaf.stalk y) Y.functionField e
  exact ⟨a, (isUnit_pow_iff hn).1 hb, rfl⟩

theorem regAt_div {f g : Y.functionField} (hf : RegAt y f) (hg : UnitAt y g) : RegAt y (f / g) := by
  rw [div_eq_mul_inv]; exact hf.mul hg.inv.regAt

theorem unitAt_div_iff {f g : Y.functionField} (hg : UnitAt y g) : UnitAt y (f / g) ↔ UnitAt y f := by
  refine ⟨fun h => ?_, fun h => by rw [div_eq_mul_inv]; exact h.mul hg.inv⟩
  have := h.mul hg
  rwa [div_mul_cancel₀ _ hg.ne_zero] at this

theorem pow_div_pow_eqn {K : Type} [Field K] (a b c : K) (hc : c ≠ 0) (m n : ℕ) :
    (a * c ^ m) ^ n / (b * c ^ n) ^ m = a ^ n / b ^ m := by
  rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm m n, mul_div_mul_right _ _ (pow_ne_zero _ hc)]

theorem isQuasiAffine_locus : ∀ (Y : Scheme.{0}) [IsIntegral Y] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (D : CartierDiv Y), AmpleDiv D → ∀ (k : ℕ), 1 ≤ k → ∀ s ∈ Sec D k, ∀ V : Y.Opens,
    (V : Set Y) = locus D k s → V.toScheme.IsQuasiAffine := by
  intro Y _ _ _ D hD k hk s hs V hV
  have memV : ∀ y, y ∈ V ↔ (k • D).GeneratesAt y s := fun y => by
    rw [← SetLike.mem_coe, hV]; rfl
  have loc : ∀ (y : Y) (e : Y.functionFieldˣ), D.IsEqn y e →
      RegAt y (s * (e : Y.functionField) ^ k) ∧ (y ∈ V ↔ UnitAt y (s * (e : Y.functionField) ^ k)) := by
    intro y e he
    have h := he.nsmul k
    have h1 := h.regularAt_iff.1 (hs y)
    have h2 := (memV y).trans h.generatesAt_iff
    rw [Units.val_pow_eq_pow_val] at h1 h2
    exact ⟨h1, h2⟩
  have stepC : ∀ k', 1 ≤ k' → ∀ u ∈ Sec D k', ∀ U : Y.Opens, IsAffineOpen U → (U : Set Y) = locus D k' u →
      IsAffineOpen (V ⊓ U) := by
    intro k' hk' u hu U hUa hUl
    have memU : ∀ y, y ∈ U ↔ (k' • D).GeneratesAt y u := fun y => by
      rw [← SetLike.mem_coe, hUl]; rfl
    have locU : ∀ (y : Y) (e : Y.functionFieldˣ), D.IsEqn y e →
        (y ∈ U ↔ UnitAt y (u * (e : Y.functionField) ^ k')) := by
      intro y e he
      have h := he.nsmul k'
      have h2 := (memU y).trans h.generatesAt_iff
      rw [Units.val_pow_eq_pow_val] at h2
      exact h2
    by_cases hg : genericPoint Y ∈ U
    swap
    · have : U = ⊥ := eq_bot_iff.2 fun y hy => (hg (gen_mem hy)).elim
      rw [this, inf_bot_eq]
      exact isAffineOpen_bot Y
    have hreg : ∀ y ∈ U, RegAt y (s ^ k' / u ^ k) := by
      intro y hy
      obtain ⟨e, he⟩ := D.exists_isEqn y
      have hB := (locU y e he).1 hy
      rw [← pow_div_pow_eqn s u _ e.ne_zero k k']
      exact regAt_div (regAt_pow (loc y e he).1 _) ((unitAt_pow_iff hB.regAt (by omega)).2 hB)
    obtain ⟨a, ha⟩ := exists_fnOf_eq hg hreg
    have e₁ : V ⊓ U = Y.basicOpen a := by
      ext y
      refine ⟨fun ⟨hyV, hyU⟩ => ?_, fun hy => ?_⟩
      · obtain ⟨e, he⟩ := D.exists_isEqn y
        have hB := (locU y e he).1 hyU
        refine (unitAt_fnOf_iff hyU hg a).1 ?_
        rw [ha, ← pow_div_pow_eqn s u _ e.ne_zero k k', unitAt_div_iff ((unitAt_pow_iff hB.regAt (by omega)).2 hB),
          unitAt_pow_iff (loc y e he).1 (by omega)]
        exact (loc y e he).2.1 hyV
      · have hyU : y ∈ U := Y.basicOpen_le a hy
        obtain ⟨e, he⟩ := D.exists_isEqn y
        have hB := (locU y e he).1 hyU
        have h := (unitAt_fnOf_iff hyU hg a).2 hy
        rw [ha, ← pow_div_pow_eqn s u _ e.ne_zero k k', unitAt_div_iff ((unitAt_pow_iff hB.regAt (by omega)).2 hB),
          unitAt_pow_iff (loc y e he).1 (by omega)] at h
        exact ⟨(loc y e he).2.2 h, hyU⟩
    rw [e₁]
    exact hUa.basicOpen a
  have : CompactSpace V := by
    choose kk hkk u hu U hUa hUl hxU using hD
    obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => (U y : Set Y)) (fun y => (U y).isOpen)
      (fun y _ => Set.mem_iUnion.2 ⟨y, hxU y⟩)
    have e : (V : Set Y) = ⋃ y ∈ t, ((V ⊓ U y : Y.Opens) : Set Y) := by
      refine Set.Subset.antisymm (fun z hz => ?_) (Set.iUnion₂_subset fun y _ => fun z hz => hz.1)
      obtain ⟨y, hy, hzy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ z))
      exact Set.mem_iUnion₂.2 ⟨y, hy, hz, hzy⟩
    have hc : IsCompact (V : Set Y) := e ▸ t.isCompact_biUnion fun y _ =>
      (stepC (kk y) (hkk y) (u y) (hu y) (U y) (hUa y) (hUl y)).isCompact
    exact isCompact_iff_compactSpace.mp hc
  have : CompactSpace V.toScheme := inferInstanceAs (CompactSpace V)
  refine Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen _ fun x => ?_
  obtain ⟨k', hk', u, hu, U, hUa, hUl, hxU⟩ := hD x.1
  have memU : ∀ y, y ∈ U ↔ (k' • D).GeneratesAt y u := fun y => by
    rw [← SetLike.mem_coe, hUl]; rfl
  have locU : ∀ (y : Y) (e : Y.functionFieldˣ), D.IsEqn y e →
      RegAt y (u * (e : Y.functionField) ^ k') ∧ (y ∈ U ↔ UnitAt y (u * (e : Y.functionField) ^ k')) := by
    intro y e he
    have h := he.nsmul k'
    have h1 := h.regularAt_iff.1 (hu y)
    have h2 := (memU y).trans h.generatesAt_iff
    rw [Units.val_pow_eq_pow_val] at h1 h2
    exact ⟨h1, h2⟩
  have hg : genericPoint Y ∈ V := gen_mem x.2
  have hreg : ∀ y ∈ V, RegAt y (u ^ k / s ^ k') := by
    intro y hy
    obtain ⟨e, he⟩ := D.exists_isEqn y
    have hA := (loc y e he).2.1 hy
    rw [← pow_div_pow_eqn u s _ e.ne_zero k' k]
    exact regAt_div (regAt_pow (locU y e he).1 _) ((unitAt_pow_iff hA.regAt (by omega)).2 hA)
  obtain ⟨a, ha⟩ := exists_fnOf_eq hg hreg
  have e₁ : Y.basicOpen a = V ⊓ U := by
    ext y
    refine ⟨fun hy => ?_, fun ⟨hyV, hyU⟩ => ?_⟩
    · have hyV : y ∈ V := Y.basicOpen_le a hy
      obtain ⟨e, he⟩ := D.exists_isEqn y
      have hA := (loc y e he).2.1 hyV
      have h := (unitAt_fnOf_iff hyV hg a).2 hy
      rw [ha, ← pow_div_pow_eqn u s _ e.ne_zero k' k, unitAt_div_iff ((unitAt_pow_iff hA.regAt (by omega)).2 hA),
        unitAt_pow_iff (locU y e he).1 (by omega)] at h
      exact ⟨hyV, (locU y e he).2.2 h⟩
    · obtain ⟨e, he⟩ := D.exists_isEqn y
      have hA := (loc y e he).2.1 hyV
      refine (unitAt_fnOf_iff hyV hg a).1 ?_
      rw [ha, ← pow_div_pow_eqn u s _ e.ne_zero k' k, unitAt_div_iff ((unitAt_pow_iff hA.regAt (by omega)).2 hA),
        unitAt_pow_iff (locU y e he).1 (by omega)]
      exact (locU y e he).2.1 hyU
  have him := Scheme.Opens.ι_image_basicOpen_topIso_inv (U := V) a
  rw [e₁] at him
  refine ⟨V.topIso.inv a, ?_, ?_⟩
  · rw [← V.ι.isAffineOpen_iff_of_isOpenImmersion, him]
    exact stepC k' hk' u hu U hUa hUl
  · have hm : V.ι x ∈ V.ι ''ᵁ V.toScheme.basicOpen (V.topIso.inv a) := by
      rw [him]; exact ⟨x.2, hxU⟩
    obtain ⟨z, hz, hzx⟩ := hm
    rwa [V.ι.isOpenEmbedding.injective hzx] at hz

end GlobalTheory.Desc.LocusQA
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQuasiAffineCartierSectionGeneratingLocusAmpleStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.isQuasiAffine_cartierSectionGeneratingLocus_ample : ∀ (Y : Scheme.{0}) [IsIntegral Y] [CompactSpace Y] [QuasiSeparatedSpace Y] (D : CartierDiv Y), AmpleDiv D → ∀ (k : ℕ), 1 ≤ k → ∀ s ∈ Sec D k, ∀ V : Y.Opens, (V : Set Y) = locus D k s → V.toScheme.IsQuasiAffine := by
  first | exact @GlobalTheory.Desc.LocusQA.isQuasiAffine_locus | exact GlobalTheory.Desc.LocusQA.isQuasiAffine_locus | (intros; apply GlobalTheory.Desc.LocusQA.isQuasiAffine_locus <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionToGradedModelFlatBaseChange

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.OpenImmersionDescent

theorem openImm_of_isIso_appTop {X Y : Scheme.{0}} [IsAffine Y] [X.IsQuasiAffine] (g : X ⟶ Y) [IsIso g.appTop] :
    IsOpenImmersion g := by
  have e : g = X.toSpecΓ ≫ Spec.map g.appTop ≫ Y.isoSpec.inv := by
    rw [← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc, Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]
  rw [e]; infer_instance

theorem bij_congr {X Y : Scheme.{0}} (f : X ⟶ Y) (V W : Y.Opens) (h : V = W) (hb : Function.Bijective (f.app W)) :
    Function.Bijective (f.app V) := by subst h; exact hb

end GlobalTheory.Desc.OpenImmersionDescent


open GlobalTheory.Desc.OpenImmersionDescent in
theorem GlobalTheory.Desc.openIn_model : ∀ (R F : Type) [CommRing R] [IsDomain R] [Field F] (c₀ : R →+* F) (N : ℕ → Set F), GradedFam c₀ N → ∀ (P : Scheme.{0}) [IsIntegral P] (p : P ⟶ Sp R) (ψ : P.functionField →+* F) (Dp : ℕ → F → P.Opens), IsModel c₀ N p ψ Dp → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (ρ : R →+* R₁), ρ.Flat → Function.Injective c₀ → ∀ (Y : Scheme.{0}) [IsIntegral Y] [CompactSpace Y] [QuasiSeparatedSpace Y] (q : Y ⟶ Sp R₁) (θ : F →+* Y.functionField) (D₁ : CartierDiv Y), θ.comp c₀ = (GlobalTheory.Desc.cst q).comp ρ → LinDisj c₀ (GlobalTheory.Desc.cst q) θ → AmpleDiv D₁ → (∀ k, Sec D₁ k = spanBy (GlobalTheory.Desc.cst q) (θ '' N k)) → ∀ m : Y ⟶ P, m ≫ p = q ≫ spMap ρ → PFF (𝟙 _) m (θ.comp ψ) → (∀ k, 1 ≤ k → ∀ b ∈ N k, ∀ y, m y ∈ Dp k b ↔ y ∈ locus D₁ k (θ b)) → OpenIn m q p (spMap ρ) := by
  intro R F _ _ _ c₀ N hN P _ p ψ Dp hP R₁ _ _ ρ hρ hc₀ Y _ _ _ q θ D₁ hθ hLD hamp hSec m hm hPFF hloc
  refine ⟨hm, ?_⟩
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := @IsOpenImmersion) fun z => ?_
  obtain ⟨k, hk, b, hb, hz⟩ := hP.cover (pullback.fst p (spMap ρ) z)
  refine ⟨(pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b, hz, ?_⟩
  haveI : IsAffineHom (pullback.fst p (spMap ρ)) := by first | infer_instance | exact MorphismProperty.pullback_fst (P := @IsAffineHom) p (spMap ρ) inferInstance | exact (isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback p (spMap ρ)).flip inferInstance)
  have hA : IsAffineOpen ((pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b) := (hP.affine k hk b hb).preimage _
  haveI : IsAffine ((pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b).toScheme := hA
  have hpre : ((pullback.lift m q hm) ⁻¹ᵁ ((pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b) : Set Y) = locus D₁ k (θ b) := by
    ext y
    change pullback.fst p (spMap ρ) (pullback.lift m q hm y) ∈ Dp k b ↔ _
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
    exact hloc k hk b hb y
  haveI : ((pullback.lift m q hm) ⁻¹ᵁ ((pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b)).toScheme.IsQuasiAffine :=
    GlobalTheory.T.isQuasiAffine_cartierSectionGeneratingLocus_ample Y D₁ hamp k hk (θ b) (by rw [hSec]; exact subset_spanBy _ _ ⟨b, hb, rfl⟩) _ hpre
  haveI : IsIso (pullback.lift m q hm ∣_ ((pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b)).appTop := by
    rw [morphismRestrict_appTop]
    have h1 := bij_congr (pullback.lift m q hm) _ _ (Scheme.Opens.ι_image_top _)
      ⟨GlobalTheory.T.proj_model_baseChange_standard_open_app_injective R F c₀ N hN P p ψ Dp hP R₁ ρ hρ hc₀ Y q θ D₁ hθ hLD hamp hSec m hPFF hloc hm k hk b hb,
       GlobalTheory.T.proj_model_baseChange_standard_open_app_surjective R F c₀ N hN P p ψ Dp hP R₁ ρ hρ hc₀ Y q θ D₁ hθ hLD hamp hSec m hPFF hloc hm k hk b hb⟩
    have h2 : IsIso (Scheme.Hom.app (pullback.lift m q hm) ((pullback.fst p (spMap ρ) ⁻¹ᵁ Dp k b).ι ''ᵁ ⊤)) :=
      (ConcreteCategory.isIso_iff_bijective _).2 h1
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h2 (Functor.map_isIso _ _)
  exact openImm_of_isIso_appTop _
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionToGradedModelFlatBaseChangeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.isOpenImmersion_to_graded_model_flat_base_change : ∀ (R F : Type) [CommRing R] [IsDomain R] [Field F] (c₀ : R →+* F) (N : ℕ → Set F), GradedFam c₀ N → ∀ (P : Scheme.{0}) [IsIntegral P] (p : P ⟶ Sp R) (ψ : P.functionField →+* F) (Dp : ℕ → F → P.Opens), IsModel c₀ N p ψ Dp → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (ρ : R →+* R₁), ρ.Flat → Function.Injective c₀ → ∀ (Y : Scheme.{0}) [IsIntegral Y] [CompactSpace Y] [QuasiSeparatedSpace Y] (q : Y ⟶ Sp R₁) (θ : F →+* Y.functionField) (D₁ : CartierDiv Y), θ.comp c₀ = (GlobalTheory.Desc.cst q).comp ρ → LinDisj c₀ (GlobalTheory.Desc.cst q) θ → AmpleDiv D₁ → (∀ k, Sec D₁ k = spanBy (GlobalTheory.Desc.cst q) (θ '' N k)) → ∀ m : Y ⟶ P, m ≫ p = q ≫ spMap ρ → PFF (𝟙 _) m (θ.comp ψ) → (∀ k, 1 ≤ k → ∀ b ∈ N k, ∀ y, m y ∈ Dp k b ↔ y ∈ locus D₁ k (θ b)) → OpenIn m q p (spMap ρ) := by
  first | exact @GlobalTheory.Desc.openIn_model | exact GlobalTheory.Desc.openIn_model | (intros; apply GlobalTheory.Desc.openIn_model <;> assumption)
end
end
