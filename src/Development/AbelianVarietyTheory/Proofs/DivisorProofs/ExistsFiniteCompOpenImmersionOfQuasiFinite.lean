module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
import Mathlib.Topology.Sheaves.Presheaf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteCoequifiberedSubalgebraStatement
public import Mathlib.RingTheory.FiniteType
import Mathlib.Data.Finset.Functor
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizationBasicOpenCoverStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelSpecMapIsIsoOverBasicOpenStatement
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayMapBijectiveOfRangeEqSubalgebra

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits Scheme.AffineZariskiSite

namespace GlobalTheory

theorem awayMap_bijective_of_range_eq_subalgebra :
    ∀ (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [Algebra R B] (C : Subalgebra R B) (φ : A →+* B), Function.Injective φ → ∀ (_ : ∀ x, x ∈ C ↔ ∃ y, φ y = x) (a : A) (b : B), φ a = b → (∀ hb : b ∈ C, Function.Bijective (Localization.awayMap C.val.toRingHom (⟨b, hb⟩ : C))) → Function.Bijective (Localization.awayMap φ a) := by
  intro R A B _ _ _ _ C φ hφ hC a b hab hloc
  subst hab
  have hmem : ∀ y, φ y ∈ C := fun y => (hC _).2 ⟨y, rfl⟩
  let f : A →+* C := φ.codRestrict C.toSubsemiring hmem
  have hf : Function.Bijective f := by
    refine ⟨fun x y h => hφ (congrArg Subtype.val h), fun c => ?_⟩
    obtain ⟨y, hy⟩ := (hC c.1).1 c.2
    exact ⟨y, Subtype.ext hy⟩
  let e : A ≃+* C := RingEquiv.ofBijective f hf
  have H : Submonoid.map e.toMonoidHom (Submonoid.powers a) = Submonoid.powers (f a) :=
    Submonoid.map_powers e.toMonoidHom a
  have h1 : Function.Bijective (Localization.awayMap f a) := by
    have hb := (IsLocalization.ringEquivOfRingEquiv (Localization.Away a)
      (Localization.Away (f a)) e H).bijective
    have key : ∀ z, Localization.awayMap f a z =
        IsLocalization.ringEquivOfRingEquiv (Localization.Away a) (Localization.Away (f a)) e H z := by
      intro z
      rw [IsLocalization.ringEquivOfRingEquiv_apply]
      rfl
    rw [show (Localization.awayMap f a : Localization.Away a → Localization.Away (f a)) = _ from funext key]
    exact hb
  have h2 : Localization.awayMap φ a =
      (Localization.awayMap C.val.toRingHom (f a)).comp (Localization.awayMap f a) := by
    simp only [Localization.awayMap, IsLocalization.Away.map]
    rw [IsLocalization.map_comp_map]
    rfl
  rw [h2]
  exact (hloc (hmem a)).comp h1

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayMapBijectiveOfRangeEqSubalgebraStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits Scheme.AffineZariskiSite

theorem _root_.GlobalTheory.T.awayMap_bijective_of_injective_of_range_eq_subalgebra : ∀ (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [Algebra R B] (C : Subalgebra R B) (φ : A →+* B), Function.Injective φ → ∀ (_ : ∀ x, x ∈ C ↔ ∃ y, φ y = x) (a : A) (b : B), φ a = b → (∀ hb : b ∈ C, Function.Bijective (Localization.awayMap C.val.toRingHom (⟨b, hb⟩ : C))) → Function.Bijective (Localization.awayMap φ a) := by
  first | exact @GlobalTheory.awayMap_bijective_of_range_eq_subalgebra | exact GlobalTheory.awayMap_bijective_of_range_eq_subalgebra | (intros; apply GlobalTheory.awayMap_bijective_of_range_eq_subalgebra <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetAwayMapSubalgebraBijective

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory

theorem exists_finset_awayMap_subalgebra_bijective :
    ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (g : Finset B),
      (∀ b ∈ g, Algebra.FiniteType R (Localization.Away b)) →
      ∃ s : Finset B, (↑g : Set B) ⊆ ↑s ∧ ∀ C : Subalgebra R B, (↑s : Set B) ⊆ ↑C →
        ∀ b ∈ g, ∀ hb : b ∈ C,
          Function.Bijective (Localization.awayMap C.val.toRingHom (⟨b, hb⟩ : C)) := by
  intro R B _ _ _ g hg
  classical
  have key : ∀ b ∈ g, ∃ t : Finset B, ∀ C : Subalgebra R B, (↑t : Set B) ⊆ ↑C → b ∈ C →
      ∀ x : B, ∃ m : ℕ, b ^ m * x ∈ C := by
    intro b hb
    obtain ⟨t, ht⟩ := (hg b hb).out
    refine ⟨t.image fun z => (IsLocalization.sec (Submonoid.powers b) z).1, fun C hC hbC x => ?_⟩
    have main : ∀ z : Localization.Away b, ∃ (m : ℕ) (c : B), c ∈ C ∧
        z * algebraMap B _ b ^ m = algebraMap B _ c := by
      intro z
      have hz : z ∈ Algebra.adjoin R (t : Set (Localization.Away b)) := ht ▸ Algebra.mem_top
      induction hz using Algebra.adjoin_induction with
      | mem z hz =>
        obtain ⟨m, hm⟩ := (IsLocalization.sec (Submonoid.powers b) z).2.2
        refine ⟨m, (IsLocalization.sec (Submonoid.powers b) z).1, hC ?_, ?_⟩
        · simp only [Finset.coe_image]
          exact ⟨z, hz, rfl⟩
        · rw [← map_pow]
          have := IsLocalization.sec_spec (Submonoid.powers b) z
          rw [← hm] at this
          exact this
      | algebraMap r =>
        exact ⟨0, algebraMap R B r, C.algebraMap_mem r, by
          rw [pow_zero, mul_one, IsScalarTower.algebraMap_apply R B]⟩
      | add x y _ _ hx hy =>
        obtain ⟨m, c, hc, e⟩ := hx
        obtain ⟨n, d, hd, e'⟩ := hy
        refine ⟨m + n, c * b ^ n + d * b ^ m,
          add_mem (mul_mem hc (pow_mem hbC _)) (mul_mem hd (pow_mem hbC _)), ?_⟩
        rw [map_add (f := _), map_mul, map_mul, map_pow, map_pow, ← e, ← e']
        ring
      | mul x y _ _ hx hy =>
        obtain ⟨m, c, hc, e⟩ := hx
        obtain ⟨n, d, hd, e'⟩ := hy
        refine ⟨m + n, c * d, mul_mem hc hd, ?_⟩
        rw [map_mul, ← e, ← e']
        ring
    obtain ⟨m, c, hc, e⟩ := main (algebraMap B _ x)
    rw [← map_pow, ← map_mul] at e
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers b) _).1 e
    refine ⟨k + m, ?_⟩
    have : b ^ (k + m) * x = b ^ k * c := by
      have hk' : b ^ k * (x * b ^ m) = b ^ k * c := hk
      rw [← hk']; ring
    rw [this]
    exact mul_mem (pow_mem hbC _) hc
  choose! t ht using key
  refine ⟨g ∪ g.biUnion t, by simp, fun C hC b hb hbC => ⟨?_, ?_⟩⟩
  · refine (Localization.awayMap_injective_iff).2 fun a ha => ⟨0, ?_⟩
    have : a = 0 := Subtype.ext ha
    simp [this]
  · refine (Localization.awayMap_surjective_iff).2 fun x => ?_
    obtain ⟨m, hm⟩ := ht b hb C (fun y hy => hC (by
      simp only [Finset.coe_union, Finset.coe_biUnion, Set.mem_union, Set.mem_iUnion]
      exact Or.inr ⟨b, hb, hy⟩)) hbC x
    exact ⟨⟨_, hm⟩, m, rfl⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetAwayMapSubalgebraBijectiveStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

theorem _root_.GlobalTheory.T.exists_finset_awayMap_bijective_of_subalgebra_ge : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (g : Finset B), (∀ b ∈ g, Algebra.FiniteType R (Localization.Away b)) → ∃ s : Finset B, (↑g : Set B) ⊆ ↑s ∧ ∀ C : Subalgebra R B, (↑s : Set B) ⊆ ↑C → ∀ b ∈ g, ∀ hb : b ∈ C, Function.Bijective (Localization.awayMap C.val.toRingHom (⟨b, hb⟩ : C)) := by
  first | exact @GlobalTheory.exists_finset_awayMap_subalgebra_bijective | exact GlobalTheory.exists_finset_awayMap_subalgebra_bijective | (intros; apply GlobalTheory.exists_finset_awayMap_subalgebra_bijective <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteCompOpenImmersionOfQuasiFinite

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits Scheme.AffineZariskiSite
namespace GlobalTheory.ZMTFin

theorem exists_glued_map (X : Scheme.{0}) (F F' : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat)
    (α : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F) (α' : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F')
    (hα : α.Coequifibered) (hα' : α'.Coequifibered) (ι : F' ⟶ F) (hι : α' ≫ ι = α) :
    ∃ g : (relativeGluingData hα).glued ⟶ (relativeGluingData hα').glued,
      g ≫ (relativeGluingData hα').toBase = (relativeGluingData hα).toBase ∧
      ∀ V, (relativeGluingData hα).cover.f V ≫ g =
        Spec.map (ι.app (Opposite.op V)) ≫ (relativeGluingData hα').cover.f V := by
  haveI : ((relativeGluingData hα).functor ⋙ Scheme.forget).IsLocallyDirected :=
    Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..
  haveI : ((relativeGluingData hα').functor ⋙ Scheme.forget).IsLocallyDirected :=
    Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..
  let η : (relativeGluingData hα).functor ⟶ (relativeGluingData hα').functor :=
    { app V := Spec.map (ι.app (Opposite.op V))
      naturality U V i := by
        dsimp [relativeGluingData]
        rw [← Spec.map_comp, ← Spec.map_comp]
        congr 1
        exact (ι.naturality i.op).symm }
  refine ⟨colimMap η, ?_, ?_⟩
  · apply colimit.hom_ext; intro V
    rw [ι_colimMap_assoc, Scheme.Cover.RelativeGluingData.ι_toBase, Scheme.Cover.RelativeGluingData.ι_toBase]
    subst hι
    show Spec.map (ι.app _) ≫ (Spec.map (α'.app (Opposite.op V)) ≫ (restrictIsoSpec X).inv.app V) ≫ (V.1).ι =
      (Spec.map ((α' ≫ ι).app (Opposite.op V)) ≫ (restrictIsoSpec X).inv.app V) ≫ (V.1).ι
    rw [NatTrans.comp_app, Spec.map_comp]; exact (Category.assoc _ _ _).symm
  · intro V
    exact ι_colimMap η V

theorem isIso_morphismRestrict_iSup {Z T : Scheme.{0}} (g : Z ⟶ T) {ι : Type} (W : ι → T.Opens)
    (hW : ∀ i, IsIso (g ∣_ W i)) : IsIso (g ∣_ ⨆ i, W i) := by
  let 𝒰 := Scheme.Opens.iSupOpenCover W
  refine (IsZariskiLocalAtTarget.iff_of_openCover (P := .isomorphisms _) 𝒰).mpr fun x ↦ ?_
  refine (MorphismProperty.arrow_mk_iso_iff (.isomorphisms _)
    ((morphismRestrictRestrict ..).symm ≪≫ morphismRestrictOpensRange ..)).mp ?_
  have : Scheme.Opens.ι _ ''ᵁ (𝒰.f x).opensRange = W x := by
    simp only [Scheme.Opens.iSupOpenCover, 𝒰, ← Scheme.Hom.opensRange_comp, Scheme.homOfLE_ι, Scheme.Opens.opensRange_ι]
  convert! hW x

theorem isOpenImmersion_comp_of_isIso_restrict {U Z T : Scheme.{0}} (h : U ⟶ Z) (g : Z ⟶ T)
    (W : T.Opens) [IsOpenImmersion h] (hg : IsIso (g ∣_ W)) (hr : Set.range h ⊆ (g ⁻¹ᵁ W : Set Z)) :
    IsOpenImmersion (h ≫ g) := by
  let h' : U ⟶ (g ⁻¹ᵁ W).toScheme := IsOpenImmersion.lift (g ⁻¹ᵁ W).ι h (by simpa using hr)
  have e : h = h' ≫ (g ⁻¹ᵁ W).ι := (IsOpenImmersion.lift_fac _ _ _).symm
  have : IsOpenImmersion (h' ≫ (g ⁻¹ᵁ W).ι) := by rw [← e]; infer_instance
  have : IsOpenImmersion h' := IsOpenImmersion.of_comp h' (g ⁻¹ᵁ W).ι
  rw [e, Category.assoc, ← morphismRestrict_ι]
  infer_instance

theorem toBase_of_Spec (X : Scheme.{0}) (F' : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat)
    (α' : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F') (h : α'.Coequifibered)
    (P : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget P]
    (hP : ∀ V, P (Spec.map (α'.app V))) : P (relativeGluingData h).toBase := by
  haveI : ((relativeGluingData h).functor ⋙ Scheme.forget).IsLocallyDirected :=
    Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P) _ (iSup_affineOpens_eq_top _)]
  intro U
  let V0 : X.AffineZariskiSite := ⟨U.1, U.2⟩
  haveI : IsOpenImmersion ((relativeGluingData h).cover.f V0) := (relativeGluingData h).cover.map_prop V0
  have hpre : (relativeGluingData h).toBase ⁻¹ᵁ U.1 =
      ((relativeGluingData h).cover.f V0).opensRange := by
    simpa using! (relativeGluingData h).toBase_preimage_eq_opensRange_ι V0
  let e := IsOpenImmersion.isoOfRangeEq ((relativeGluingData h).toBase ⁻¹ᵁ U.1).ι
    ((relativeGluingData h).cover.f V0) (by rw [Scheme.Opens.range_ι, ← Scheme.Hom.coe_opensRange, ← hpre])
  have hU : IsAffineOpen U.1 := U.2
  haveI : Mono hU.fromSpec := inferInstance
  have key : e.inv ≫ ((relativeGluingData h).toBase ∣_ U.1) ≫ hU.isoSpec.hom =
      Spec.map (α'.app (Opposite.op V0)) := by
    apply (cancel_mono hU.fromSpec).mp
    have := (relativeGluingData h).ι_toBase V0
    simp [IsAffineOpen.isoSpec_hom, e]
    refine (congrArg (· ≫ (relativeGluingData h).toBase) (IsOpenImmersion.isoOfRangeEq_inv_fac ((relativeGluingData h).toBase ⁻¹ᵁ U.1).ι ((relativeGluingData h).cover.f V0) (by rw [Scheme.Opens.range_ι, ← Scheme.Hom.coe_opensRange, ← hpre]))).trans ?_
    refine this.trans ?_
    show (Spec.map (α'.app (Opposite.op V0)) ≫ hU.isoSpec.inv) ≫ U.1.ι = _
    exact (Category.assoc _ _ _).trans (congrArg (Spec.map (α'.app (Opposite.op V0)) ≫ ·) (IsAffineOpen.isoSpec_inv_ι hU))
  rw [← MorphismProperty.cancel_left_of_respectsIso P e.inv,
    ← MorphismProperty.cancel_right_of_respectsIso P _ hU.isoSpec.hom, Category.assoc, key]
  exact hP _


set_option backward.isDefEq.respectTransparency false in
theorem isFinite_toBase (X : Scheme.{0}) (F' : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat)
    (α' : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F') (h : α'.Coequifibered)
    (hfin : ∀ V, (α'.app V).hom.Finite) : IsFinite (relativeGluingData h).toBase := by
  rw [IsFinite.iff_isIntegralHom_and_locallyOfFiniteType]
  exact ⟨toBase_of_Spec X F' α' h (@IsIntegralHom : MorphismProperty Scheme.{0}) fun V ↦ IsIntegralHom.SpecMap_iff.mpr (hfin V).to_isIntegral,
    toBase_of_Spec X F' α' h (@LocallyOfFiniteType : MorphismProperty Scheme.{0}) fun V ↦
      (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr (hfin V).finiteType⟩

theorem isIso_restrict_basicOpen (X : Scheme.{0}) (F F' : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat)
    (α : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F) (α' : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F')
    (hα : α.Coequifibered) (hα' : α'.Coequifibered) (ι : F' ⟶ F) (hι : α' ≫ ι = α)
    (g : (relativeGluingData hα).glued ⟶ (relativeGluingData hα').glued)
    (hg₁ : g ≫ (relativeGluingData hα').toBase = (relativeGluingData hα).toBase)
    (hg₂ : ∀ V, (relativeGluingData hα).cover.f V ≫ g =
      Spec.map (ι.app (Opposite.op V)) ≫ (relativeGluingData hα').cover.f V)
    (V : X.AffineZariskiSite) (b : F'.obj (Opposite.op V))
    (hb : Function.Bijective (Localization.awayMap (ι.app (Opposite.op V)).hom b))
    (W : (relativeGluingData hα').glued.Opens)
    (hW : (W : Set (relativeGluingData hα').glued) =
      (relativeGluingData hα').cover.f V '' (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum (F'.obj (Opposite.op V))))) :
    IsIso (g ∣_ W) ∧ ((g ⁻¹ᵁ W : (relativeGluingData hα).glued.Opens) : Set (relativeGluingData hα).glued) =
      (relativeGluingData hα).cover.f V '' (PrimeSpectrum.basicOpen ((ι.app (Opposite.op V)).hom b) :
        Set (PrimeSpectrum (F.obj (Opposite.op V)))) :=
  GlobalTheory.T.relSpec_map_isIso_over_basicOpen_alt X F F' α α' hα hα' ι hι g hg₁ hg₂ V b hb W hW

theorem exists_basicOpen_cover (U X : Scheme.{0}) (f : U ⟶ X) (h₁ : IsSeparated f)
    (h₂ : LocallyOfFiniteType f) (h₃ : QuasiCompact f) (h₄ : LocallyQuasiFinite f)
    (V : X.AffineZariskiSite) :
    ∃ G : Finset (f.normalizationDiagram.obj (Opposite.op V.1)),
      (∀ b ∈ G, letI := (f.normalizationDiagramMap.app (Opposite.op V.1)).hom.toAlgebra
        Algebra.FiniteType Γ(X, V.1) (Localization.Away b)) ∧
      ∀ x : U, f x ∈ V.1 → ∃ b ∈ G, f.toNormalization x ∈
        f.normalizationOpenCover.f V '' (PrimeSpectrum.basicOpen b :
          Set (PrimeSpectrum (f.normalizationDiagram.obj (Opposite.op V.1)))) :=
  GlobalTheory.T.normalization_basicOpen_cover' U X f V

theorem bijective_awayMap_of_range (R A B : Type) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R B] (C : Subalgebra R B) (φ : A →+* B) (hφ : Function.Injective φ)
    (hC : ∀ x, x ∈ C ↔ ∃ y, φ y = x) (a : A) (b : B) (hab : φ a = b)
    (h : ∀ hb : b ∈ C, Function.Bijective (Localization.awayMap C.val.toRingHom (⟨b, hb⟩ : C))) :
    Function.Bijective (Localization.awayMap φ a) :=
  GlobalTheory.T.awayMap_bijective_of_injective_of_range_eq_subalgebra R A B C φ hφ hC a b hab h


set_option backward.isDefEq.respectTransparency false in
theorem exists_finite_openImmersion : ∀ (U X : Scheme.{0}) (f : U ⟶ X), IsNoetherian X →
    IsSeparated f → LocallyOfFiniteType f → QuasiCompact f → LocallyQuasiFinite f →
    ∃ (T : Scheme.{0}) (q : T ⟶ X) (j : U ⟶ T), IsFinite q ∧ IsOpenImmersion j ∧ j ≫ q = f := by
  intro U X f hX h₁ h₂ h₃ h₄
  obtain ⟨t, ht⟩ : ∃ t : Finset X.affineOpens, ∀ x : X, ∃ W ∈ t, x ∈ (W : X.Opens) := by
    obtain ⟨t, ht⟩ := (isCompact_univ : IsCompact (Set.univ : Set X)).elim_finite_subcover
      (fun W : X.affineOpens ↦ ((W : X.Opens) : Set X)) (fun W ↦ (W : X.Opens).2) (fun x _ ↦ by
        obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
          X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
        exact Set.mem_iUnion.mpr ⟨⟨W, hW⟩, hxW⟩)
    exact ⟨t, fun x ↦ by simpa using ht (Set.mem_univ x)⟩
  let n := t.card
  let V : Fin n → X.AffineZariskiSite := fun k ↦ ⟨(t.equivFin.symm k).1.1, (t.equivFin.symm k).1.2⟩
  have hV : ∀ x : X, ∃ k, x ∈ (V k).1 := fun x ↦ by
    obtain ⟨W, hWt, hxW⟩ := ht x
    exact ⟨t.equivFin ⟨W, hWt⟩, by simpa [V] using hxW⟩
  choose G hGfin hGcov using fun k ↦ exists_basicOpen_cover U X f h₁ h₂ h₃ h₄ (V k)
  have hs : ∀ k, ∃ s : Finset (f.normalizationDiagram.obj (Opposite.op (V k).1)),
      (G k : Set (f.normalizationDiagram.obj (Opposite.op (V k).1))) ⊆ s ∧
      letI := (f.normalizationDiagramMap.app (Opposite.op (V k).1)).hom.toAlgebra
      ∀ C : Subalgebra Γ(X, (V k).1) (f.normalizationDiagram.obj (Opposite.op (V k).1)),
        (s : Set (f.normalizationDiagram.obj (Opposite.op (V k).1))) ⊆ (C : Set _) → ∀ b ∈ G k, ∀ hb : b ∈ C,
          Function.Bijective (Localization.awayMap C.val.toRingHom (⟨b, hb⟩ : C)) := by
    intro k
    letI := (f.normalizationDiagramMap.app (Opposite.op (V k).1)).hom.toAlgebra
    exact GlobalTheory.T.exists_finset_awayMap_bijective_of_subalgebra_ge _ _ (G k) (hGfin k)
  choose s hGs hsC using hs
  have hint : ∀ W : X.Opens, IsAffineOpen W →
      (f.normalizationDiagramMap.app (Opposite.op W)).hom.IsIntegral := by
    intro W _
    letI := (f.app W).hom.toAlgebra
    change (algebraMap Γ(X, W) (integralClosure Γ(X, W) Γ(U, f ⁻¹ᵁ W))).IsIntegral
    exact algebraMap_isIntegral_iff.mpr inferInstance
  obtain ⟨F', α', ι, hα', hι, hιinj, hfin, hιS⟩ := GlobalTheory.T.exists_finite_coequifibered_subalgebra_alt X hX f.normalizationDiagram
    f.normalizationDiagramMap f.coequifibered_normalizationDiagramMap hint n V s
  obtain ⟨g, hg₁, hg₂⟩ := exists_glued_map X _ F' _ α' f.coequifibered_normalizationDiagramMap hα' ι hι
  refine ⟨_, (relativeGluingData hα').toBase, f.toNormalization ≫ g,
    isFinite_toBase X F' α' hα' hfin, ?_, ?_⟩
  rotate_left
  · rw [Category.assoc, hg₁]; exact f.toNormalization_fromNormalization
  choose b' hb' using fun (k : Fin n) (b : G k) ↦ hιS k b.1 (hGs k b.2)
  haveI : ∀ k, IsOpenImmersion ((relativeGluingData hα').cover.f (V k)) :=
    fun k ↦ (relativeGluingData hα').cover.map_prop _
  let Wp : (Σ k, G k) → (relativeGluingData hα').glued.Opens := fun p ↦
    (relativeGluingData hα').cover.f (V p.1) ''ᵁ PrimeSpectrum.basicOpen (b' p.1 p.2)
  have hbij : ∀ p : Σ k, G k, Function.Bijective
      (Localization.awayMap (ι.app (Opposite.op (V p.1))).hom (b' p.1 p.2)) := by
    rintro ⟨k, b⟩
    letI := (f.normalizationDiagramMap.app (Opposite.op (V k).1)).hom.toAlgebra
    let C : Subalgebra Γ(X, (V k).1) (f.normalizationDiagram.obj (Opposite.op (V k).1)) :=
      { (ι.app (Opposite.op (V k))).hom.range with
        algebraMap_mem' := fun r ↦ ⟨(α'.app (Opposite.op (V k))).hom r, by
          rw [← CommRingCat.comp_apply, ← NatTrans.comp_app, hι]; rfl⟩ }
    have hsub : ((s k : Finset _) : Set (f.normalizationDiagram.obj (Opposite.op (V k).1))) ⊆ (C : Set _) :=
      fun x hx ↦ by obtain ⟨y, hy⟩ := hιS k x hx; exact ⟨y, hy⟩
    have hC : ∀ x, x ∈ C ↔ ∃ y, (ι.app (Opposite.op (V k))).hom y = x := fun x ↦ Iff.rfl
    have hB := hsC k C hsub b.1 b.2
    have hφ : Function.Injective (ι.app (Opposite.op (V k))).hom := hιinj _
    exact bijective_awayMap_of_range Γ(X, (V k).1) (F'.obj (Opposite.op (V k)))
      (f.normalizationDiagram.obj (Opposite.op (V k).1)) C (ι.app _).hom hφ hC (b' k b) b.1
      (hb' k b) hB
  have hiso := fun p : Σ k, G k ↦ isIso_restrict_basicOpen X _ F' _ α'
    f.coequifibered_normalizationDiagramMap hα' ι hι g hg₁ hg₂ (V p.1) (b' p.1 p.2) (hbij p)
    (Wp p) rfl
  refine isOpenImmersion_comp_of_isIso_restrict f.toNormalization g (⨆ p, Wp p)
    (isIso_morphismRestrict_iSup g Wp fun p ↦ (hiso p).1) ?_
  rintro _ ⟨x, rfl⟩
  obtain ⟨k, hk⟩ := hV (f x)
  obtain ⟨b, hbG, hxb⟩ := hGcov k x hk
  have h2 := (hiso ⟨k, ⟨b, hbG⟩⟩).2
  rw [hb' k ⟨b, hbG⟩] at h2
  have h3 : f.toNormalization x ∈ SetLike.coe (g ⁻¹ᵁ Wp ⟨k, ⟨b, hbG⟩⟩) := by rw [h2]; exact hxb
  exact g.preimage_mono (le_iSup Wp ⟨k, ⟨b, hbG⟩⟩) h3

end GlobalTheory.ZMTFin
end
end
