module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RangeSubsetAbLocusOfIsProper
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsProjOverIsPullbackOfIsLocalization
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsNormalFiniteModelOfFiniteOverOpen
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartDenseProOpen
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSemiAbelianTripleGlueCommonGenericPartStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartDenseProOpen
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsJoinNormalProjectiveModels

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.JoinModels

theorem isNormalScheme_of_flat_preimmersion {U X : Scheme.{0}} (j : U ⟶ X) [IsPreimmersion j] [Flat j]
    (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme U := by
  intro x
  obtain ⟨h1, h2⟩ := h (j x)
  have hf : (j.stalkMap x).hom.Flat := Flat.stalkMap j x
  have hs : Function.Surjective (j.stalkMap x).hom := j.stalkMap_surjective x
  have hi : Function.Injective (j.stalkMap x).hom := by
    letI := (j.stalkMap x).hom.toAlgebra
    have : Module.Flat (X.presheaf.stalk (j x)) (U.presheaf.stalk x) := hf
    have : IsLocalHom (algebraMap (X.presheaf.stalk (j x)) (U.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom (j.stalkMap x).hom)
    have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := X.presheaf.stalk (j x))
      (B := U.presheaf.stalk x)
    exact FaithfulSMul.algebraMap_injective (X.presheaf.stalk (j x)) (U.presheaf.stalk x)
  let e := RingEquiv.ofBijective (j.stalkMap x).hom ⟨hi, hs⟩
  have h3 : IsDomain (U.presheaf.stalk x) := e.symm.toMulEquiv.isDomain _
  exact ⟨h3, IsIntegrallyClosed.of_equiv e⟩

theorem isPullback_toImage_comp {U P Z : Scheme.{0}} (j : U ⟶ P) (q : P ⟶ Z) (v : U ⟶ Z)
    (h : j ≫ q = v) [QuasiCompact j] [IsSeparated q] [Flat v] [Mono v] :
    IsPullback (𝟙 U) j.toImage v (j.imageι ≫ q) := by
  have Hu := IsPullback.of_hasPullback v q
  have : Mono (pullback.snd v q) := inferInstance
  let c : U ⟶ pullback v q := pullback.lift (𝟙 U) j (by simpa using h.symm)
  have hc₁ : c ≫ pullback.fst _ _ = 𝟙 U := pullback.lift_fst _ _ _
  have hc₂ : c ≫ pullback.snd _ _ = j := pullback.lift_snd _ _ _
  have : IsClosedImmersion (c ≫ pullback.fst _ _) := by rw [hc₁]; infer_instance
  have : IsClosedImmersion c := .of_comp c (pullback.fst _ _)
  have H := (GlobalTheory.isPullback_toImage_of_isClosedImmersion j c _ hc₂).paste_horiz Hu
  rwa [hc₁] at H

theorem exists_common_projective {O : Type} [CommRing O] {U : Scheme.{0}} (σ : U ⟶ Sp O) {I : Type}
    [Finite I] [Nonempty I] (X : I → Scheme.{0}) (s : ∀ i, X i ⟶ Sp O) (hs : ∀ i, IsProjOver (s i))
    (u : ∀ i, U ⟶ X i) (hu : ∀ i, u i ≫ s i = σ) :
    ∃ (P : Scheme.{0}) (r : P ⟶ Sp O) (j : U ⟶ P) (p : ∀ i, P ⟶ X i), IsProjOver r ∧ j ≫ r = σ ∧
      ∀ i, p i ≫ s i = r ∧ j ≫ p i = u i := by
  classical
  have key : ∀ S : Finset I, ∃ (P : Scheme.{0}) (r : P ⟶ Sp O) (j : U ⟶ P), IsProjOver r ∧ j ≫ r = σ ∧
      ∀ i ∈ S, ∃ p : P ⟶ X i, p ≫ s i = r ∧ j ≫ p = u i := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      obtain ⟨i⟩ := ‹Nonempty I›
      exact ⟨X i, s i, u i, hs i, hu i, by simp⟩
    | insert k S _ ih =>
      obtain ⟨P, r, j, h1, h2, h3⟩ := ih
      refine ⟨pullback r (s k), pullback.fst _ _ ≫ r, pullback.lift j (u k) (h2.trans (hu k).symm),
        GlobalTheory.ProjSpace.isProjOver_pullback h1 (hs k), by rw [pullback.lift_fst_assoc, h2], fun i hi => ?_⟩
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact ⟨pullback.snd _ _, pullback.condition.symm, pullback.lift_snd _ _ _⟩
      · obtain ⟨p, hp1, hp2⟩ := h3 i hi
        exact ⟨pullback.fst _ _ ≫ p, by rw [Category.assoc, hp1], by rw [pullback.lift_fst_assoc, hp2]⟩
  have := Fintype.ofFinite I
  obtain ⟨P, r, j, h1, h2, h3⟩ := key Finset.univ
  choose p hp using fun i => h3 i (Finset.mem_univ i)
  exact ⟨P, r, j, p, h1, h2, hp⟩

theorem isProper_of_proj {O : Type} [CommRing O] {X : Scheme.{0}} {s : X ⟶ Sp O} (h : IsProjOver s) :
    IsProper s := by
  obtain ⟨N, i, hi, rfl⟩ := h
  have := isProper_str O N
  infer_instance

theorem exists_join {O : Type} [CommRing O] {U : Scheme.{0}} (σ : U ⟶ Sp O) {I : Type}
    [Finite I] [Nonempty I] (X : I → Scheme.{0}) (s : ∀ i, X i ⟶ Sp O) (hs : ∀ i, IsProjOver (s i))
    (u : ∀ i, U ⟶ X i) (hu : ∀ i, u i ≫ s i = σ) [∀ i, Flat (u i)] [∀ i, Mono (u i)]
    [∀ i, QuasiCompact (u i)] :
    ∃ (P : Scheme.{0}) (r : P ⟶ Sp O) (j : U ⟶ P) (p : ∀ i, P ⟶ X i), IsProjOver r ∧ j ≫ r = σ ∧
      ∀ i, p i ≫ s i = r ∧ IsPullback (𝟙 U) j (u i) (p i) := by
  obtain ⟨P, r, j, p, h1, h2, h3⟩ := exists_common_projective σ X s hs u hu
  have := isProper_of_proj h1
  have hsep : ∀ i, IsSeparated (p i) := fun i => by
    have : IsSeparated (p i ≫ s i) := by rw [(h3 i).1]; infer_instance
    exact IsSeparated.of_comp (p i) (s i)
  have : QuasiCompact j := by
    obtain ⟨i⟩ := ‹Nonempty I›
    have : QuasiCompact (j ≫ p i) := by rw [(h3 i).2]; infer_instance
    exact QuasiCompact.of_comp j (p i)
  obtain ⟨N, e, he, hr⟩ := h1
  refine ⟨j.image, j.imageι ≫ r, j.toImage, fun i => j.imageι ≫ p i,
    ⟨N, j.imageι ≫ e, inferInstance, by rw [Category.assoc, hr]⟩, by simpa using h2, fun i => ⟨?_, ?_⟩⟩
  · rw [Category.assoc, (h3 i).1]
  · exact isPullback_toImage_comp j (p i) (u i) (h3 i).2

theorem exists_join_scheme : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (I : Type) [Finite I] [Nonempty I] (R : I → Type) [∀ i, CommRing (R i)] (a : I → O) (b : ∀ i, O →+* R i) (ω : ∀ i, R i →+* F) (C : ∀ i, Cpt c t (ω i)), IsDedFrac β → (∀ i, IsDedFrac (ω i) ∧ (ω i).comp (b i) = β ∧ @IsLocalization.Away O _ (a i) (R i) _ (b i).toAlgebra) → Ideal.span (Set.range a) = ⊤ → CharZero O → ∃ (X : Scheme.{0}) (s : X ⟶ Sp O) (jQ : U ⟶ pullback s (spMap β)) (f : ∀ i, pullback s (spMap (b i)) ⟶ (C i).X), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X ∧ IsProjOver s ∧ Flat s ∧ jQ ≫ pullback.snd _ _ = c ∧ IsOpenImmersion jQ ∧ Dense (Set.range jQ) ∧ ∀ i, f i ≫ (C i).s = pullback.snd _ _ ∧ (∀ g : U ⟶ pullback s (spMap (b i)), g ≫ pullback.fst _ _ = jQ ≫ pullback.fst _ _ → g ≫ f i = (C i).j) ∧ ∀ x : ↥(pullback s (spMap (b i))), f i x ∈ Set.range (C i).j → pullback.fst s (spMap (b i)) x ∈ Set.range (jQ ≫ pullback.fst s (spMap β)) := by
  intro E _ _ _ H U F O _ _ c t β I _ _ R _ a b ω C hβ hR _ _
  obtain ⟨⟨_, _⟩, _, hfr⟩ := hβ
  letI := β.toAlgebra
  have hβ : algebraMap O F = β := rfl
  have hcl : ∀ i, ∃ (X' : Scheme.{0}) (s' : X' ⟶ Sp O) (κ : (C i).X ⟶ X'), IsProjOver s' ∧
      IsPullback κ (C i).s s' (spMap (b i)) := fun i => by
    letI := (b i).toAlgebra
    have := (hR i).2.2
    exact GlobalTheory.ProjClosure.exists_projective_closure O (R i) (a i) (C i).X (C i).s (C i).proj
  choose X' s' κ hs' hk using hcl
  have hbo : ∀ i, IsOpenImmersion (spMap (b i)) := fun i => by
    letI := (b i).toAlgebra
    have := (hR i).2.2
    exact IsOpenImmersion.of_isLocalization (a i)
  have hko : ∀ i, IsOpenImmersion (κ i) := fun i => MorphismProperty.of_isPullback (hk i).flip (hbo i)
  have hj : ∀ i, IsPreimmersion (C i).j ∧ Flat (C i).j ∧ QuasiCompact (C i).j ∧ QuasiCompact (κ i) :=
    fun i => by
      obtain ⟨⟨⟨_, _⟩, _, hfr⟩, _, _⟩ := hR i
      letI := (ω i).toAlgebra
      obtain ⟨-, -, -, h1, h2, -, h3⟩ := GlobalTheory.genericPart_dense_proOpen (R i) F (C i).X U (C i).s (C i).jQ
        (C i).flat (C i).proj (C i).jQ_open (C i).jQ_dense
      exact ⟨h1, h2, h3, MorphismProperty.of_isPullback (hk i).flip inferInstance⟩
  have hωb : ∀ i, spMap (ω i) ≫ spMap (b i) = spMap β := fun i => by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, (hR i).2.1]
  have hjs : ∀ i, (C i).j ≫ (C i).s = c ≫ spMap (ω i) := fun i => by
    rw [Cpt.j, Category.assoc, pullback.condition, reassoc_of% (C i).jQ_over]
  have h1 := fun i => (hj i).1
  have h2 := fun i => (hj i).2.1
  have h3 := fun i => (hj i).2.2.1
  have h4 := fun i => (hj i).2.2.2
  obtain ⟨P, r, j, p, hr, hjr, hp⟩ := exists_join (c ≫ spMap β) X' s' hs' (fun i => (C i).j ≫ κ i)
    (fun i => by rw [Category.assoc, (hk i).w, reassoc_of% (hjs i), hωb])
  have hjp : ∀ i, j ≫ p i = (C i).j ≫ κ i := fun i => by simpa using (hp i).2.w.symm
  let jP : U ⟶ pullback r (spMap β) := pullback.lift j c hjr
  have hjP₁ : jP ≫ pullback.fst _ _ = j := pullback.lift_fst _ _ _
  have hjP₂ : jP ≫ pullback.snd _ _ = c := pullback.lift_snd _ _ _
  obtain ⟨i₀⟩ := ‹Nonempty I›
  have hU : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme U :=
    isNormalScheme_of_flat_preimmersion (C i₀).j (C i₀).normal
  have hjPo : IsOpenImmersion jP := by
    have G := (IsPullback.of_hasPullback (C i₀).s (spMap (ω i₀))).flip.paste_vert (hk i₀).flip
    rw [hωb] at G
    let ρ : pullback r (spMap β) ⟶ pullback (C i₀).s (spMap (ω i₀)) :=
      G.lift (pullback.snd _ _) (pullback.fst _ _ ≫ p i₀)
        (by rw [Category.assoc, (hp i₀).1, pullback.condition])
    have hρ₁ : ρ ≫ pullback.snd _ _ = pullback.snd _ _ := G.lift_fst _ _ _
    have hρ₂ : ρ ≫ pullback.fst _ _ ≫ κ i₀ = pullback.fst _ _ ≫ p i₀ := G.lift_snd _ _ _
    have A : IsPullback ρ (pullback.fst r (spMap β)) (pullback.fst _ _ ≫ κ i₀) (p i₀) := by
      refine IsPullback.of_right (h₁₂ := pullback.snd _ _) (h₂₂ := s' i₀) (v₁₃ := spMap β) ?_ hρ₂ G
      rw [hρ₁, (hp i₀).1]
      exact (IsPullback.of_hasPullback _ _).flip
    have B : IsPullback (𝟙 U) jP (C i₀).jQ ρ := by
      refine IsPullback.of_bot (v₂₁ := pullback.fst _ _) (v₂₂ := pullback.fst _ _ ≫ κ i₀) (h₃₁ := p i₀)
        ?_ ?_ A
      · rw [hjP₁, ← Category.assoc]
        exact (hp i₀).2
      · refine G.hom_ext ?_ ?_
        · rw [Category.id_comp, Category.assoc, hρ₁, hjP₂, (C i₀).jQ_over]
        · rw [Category.id_comp, Category.assoc, hρ₂, reassoc_of% hjP₁, hjp, Cpt.j, Category.assoc]
    exact MorphismProperty.of_isPullback B (C i₀).jQ_open
  obtain ⟨Y, π, jQ, -, hY, hproj, hflat, hq₁, hq₂, hqo, hqd, hqr⟩ :=
    GlobalTheory.exists_normal_finite_model_of_finite_over_open O F P U r c j jP.opensRange jP.isoOpensRange.hom hr hU inferInstance
      (by rw [Scheme.Hom.isoOpensRange_hom_ι_assoc]; exact hjP₁)
      (by rw [Scheme.Hom.isoOpensRange_hom_ι_assoc]; exact hjP₂)
  let f : ∀ i, pullback (π ≫ r) (spMap (b i)) ⟶ (C i).X := fun i =>
    (hk i).lift (pullback.fst _ _ ≫ π ≫ p i) (pullback.snd _ _)
      (by rw [Category.assoc, Category.assoc, (hp i).1, pullback.condition])
  have hf : ∀ i, f i ≫ κ i = pullback.fst _ _ ≫ π ≫ p i := fun i => (hk i).lift_fst _ _ _
  refine ⟨Y, π ≫ r, jQ, f, hY, hproj, hflat, hq₁, hqo, hqd, fun i => ⟨(hk i).lift_snd _ _ _, ?_, ?_⟩⟩
  · intro g hg
    have hq₂' : jQ ≫ pullback.fst (π ≫ r) (spMap β) ≫ π = j := hq₂
    rw [← cancel_mono (κ i), Category.assoc, hf, reassoc_of% hg, reassoc_of% hq₂', hjp]
  · rintro x ⟨y, hy⟩
    have e1 : p i (π (pullback.fst (π ≫ r) (spMap (b i)) x)) = ((C i).j ≫ κ i) y := by
      rw [Scheme.Hom.comp_apply, hy, ← Scheme.Hom.comp_apply (f i), hf]
      simp only [Scheme.Hom.comp_apply]
    obtain ⟨z, -, hz⟩ := Scheme.exists_preimage_of_isPullback (hp i).2 y _ e1.symm
    obtain ⟨w, hw⟩ : pullback.fst (π ≫ r) (spMap (b i)) x ∈ Set.range (pullback.fst (π ≫ r) (spMap β)) := by
      rw [Scheme.Pullback.range_fst]
      refine ⟨c z, ?_⟩
      rw [Scheme.Hom.comp_apply π r, ← hz, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hjr]
    obtain ⟨v, hv⟩ := (hqr w).mpr ⟨jP.isoOpensRange.hom z, by
      rw [← Scheme.Hom.comp_apply, Scheme.Hom.isoOpensRange_hom_ι_assoc]
      exact (congrArg (fun m : U ⟶ P => m z) hjP₁).trans (hz.trans (congrArg π hw.symm))⟩
    exact ⟨v, by rw [Scheme.Hom.comp_apply, ← hw]; exact congrArg _ hv⟩

end GlobalTheory.JoinModels
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsJoinNormalProjectiveModelsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

theorem _root_.GlobalTheory.T.exists_join_normal_projective_models : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (I : Type) [Finite I] [Nonempty I] (R : I → Type) [∀ i, CommRing (R i)] (a : I → O) (b : ∀ i, O →+* R i) (ω : ∀ i, R i →+* F) (C : ∀ i, Cpt c t (ω i)), IsDedFrac β → (∀ i, IsDedFrac (ω i) ∧ (ω i).comp (b i) = β ∧ @IsLocalization.Away O _ (a i) (R i) _ (b i).toAlgebra) → Ideal.span (Set.range a) = ⊤ → CharZero O → ∃ (X : Scheme.{0}) (s : X ⟶ Sp O) (jQ : U ⟶ pullback s (spMap β)) (f : ∀ i, pullback s (spMap (b i)) ⟶ (C i).X), IsNormalScheme X ∧ IsProjOver s ∧ Flat s ∧ jQ ≫ pullback.snd _ _ = c ∧ IsOpenImmersion jQ ∧ Dense (Set.range jQ) ∧ ∀ i, f i ≫ (C i).s = pullback.snd _ _ ∧ (∀ g : U ⟶ pullback s (spMap (b i)), g ≫ pullback.fst _ _ = jQ ≫ pullback.fst _ _ → g ≫ f i = (C i).j) ∧ ∀ x : ↥(pullback s (spMap (b i))), f i x ∈ Set.range (C i).j → pullback.fst s (spMap (b i)) x ∈ Set.range (jQ ≫ pullback.fst s (spMap β)) := by
  first | exact @GlobalTheory.JoinModels.exists_join_scheme | exact GlobalTheory.JoinModels.exists_join_scheme | (intros; apply GlobalTheory.JoinModels.exists_join_scheme <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModelDominatingModelsOnOpenCover

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

namespace ModelJoin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem comp_of_eq {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S}
    {g : S'' ⟶ S'} {h : S'' ⟶ S} (m : SABMap t' t f) (m' : SABMap t'' t' g) (e : g ≫ f = h) :
    ∃ n : SABMap t'' t h, n.φ = m'.φ ≫ m.φ := by
  subst e
  exact sabComp pullCubComp E H _ _ _ t t' t'' f g m m'

theorem cancel_of_eq {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S}
    {g : S'' ⟶ S'} {h : S'' ⟶ S} (m : SABMap t' t f) (n : SABMap t'' t h) (e : g ≫ f = h) :
    ∃ m' : SABMap t'' t' g, n.φ = m'.φ ≫ m.φ := by
  subst e
  exact sabCancel pullCubCancel E H _ _ _ t t' t'' f g m n

theorem exists_pull {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) :
    ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
  obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull Out.CubePf.cubePull f t
  exact ⟨_, ⟨m⟩⟩

theorem isOpenImmersion_away {O R : Type} [CommRing O] [CommRing R] (a : O) (b : O →+* R)
    (h : @IsLocalization.Away O _ a R _ b.toAlgebra) : IsOpenImmersion (spMap b) := by
  letI := b.toAlgebra
  exact IsOpenImmersion.of_isLocalization (R := O) (S := R) a

theorem mem_range_away {O R : Type} [CommRing O] [CommRing R] (a : O) (b : O →+* R)
    (h : @IsLocalization.Away O _ a R _ b.toAlgebra) (x : Sp O) (hx : a ∉ x.asIdeal) :
    x ∈ Set.range (spMap b) := by
  letI := b.toAlgebra
  have := PrimeSpectrum.localization_away_comap_range R a
  have h2 : (x : PrimeSpectrum O) ∈ Set.range (PrimeSpectrum.comap (algebraMap O R)) := by
    rw [this]; exact hx
  exact h2

theorem arith_base (O : Type) [CommRing O] [IsDomain O] [CharZero O] [Algebra.FiniteType ℤ O] :
    LocallyOfFiniteType (spMap (algebraMap ℤ O)) ∧ Flat (spMap (algebraMap ℤ O)) := by
  constructor
  · rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  · rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance

end ModelJoin

open ModelJoin

theorem exists_join_of_models : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (I : Type) [Finite I] [Nonempty I] (R : I → Type) [∀ i, CommRing (R i)] (a : I → O) (b : ∀ i, O →+* R i) (ω : ∀ i, R i →+* F) (C : ∀ i, Cpt c t (ω i)), IsDedFrac β → (∀ i, IsDedFrac (ω i) ∧ (ω i).comp (b i) = β ∧ @IsLocalization.Away O _ (a i) (R i) _ (b i).toAlgebra) → Ideal.span (Set.range a) = ⊤ → Algebra.FiniteType ℤ O → IsProper t.G.hom → ∃ C' : Cpt c t β, ∀ i, ∃ (f : pullback C'.s (spMap (b i)) ⟶ (C i).X) (t₁ : SAB H (pullback C'.s (spMap (b i)))) (m₁ : SABMap t₁ C'.t (pullback.fst _ _)) (m₂ : SABMap t₁ (C i).t f), f ≫ (C i).s = pullback.snd _ _ ∧ (∀ g : U ⟶ pullback C'.s (spMap (b i)), g ≫ pullback.fst _ _ = C'.j → g ≫ f = (C i).j) ∧ ∀ y : t.G.left ⟶ t₁.G.left, y ≫ m₁.φ = C'.m.φ → y ≫ m₂.φ = (C i).m.φ := by
  intro hext E _ _ _ H U F O _ _ c t β I _ _ R _ a b ω C hβ hω hspan hft hprop
  obtain ⟨⟨hdom, hded⟩, hchar, hfrac⟩ := id hβ
  obtain ⟨X, s, jQ, f, hn, hproj, hflat, hover, hopen, hdense, hf⟩ :=
    GlobalTheory.T.exists_join_normal_projective_models E H U F O c t β I R a b ω C hβ hω hspan hchar
  have hpo : IsPreimmersion (jQ ≫ pullback.fst s (spMap β)) ∧ Flat (jQ ≫ pullback.fst s (spMap β)) ∧
      IsDominant (jQ ≫ pullback.fst s (spMap β)) ∧ QuasiCompact (jQ ≫ pullback.fst s (spMap β)) := by
    letI := β.toAlgebra
    exact (genericPart_dense_proOpen O F X U s jQ hflat hproj hopen hdense).2.2.2
  have hβp : IsPreimmersion (spMap β) := by
    letI := β.toAlgebra
    exact IsPreimmersion.of_isLocalization (R := CommRingCat.of O) (S := F) (nonZeroDivisors O)
  have hfp : IsPreimmersion (pullback.fst s (spMap β)) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip hβp
  have hb : ∀ i, IsOpenImmersion (spMap (b i)) := fun i => isOpenImmersion_away (a i) (b i) (hω i).2.2
  have hβe : ∀ i, spMap β = spMap (ω i) ≫ spMap (b i) := fun i => by
    rw [← (hω i).2.1]; exact Spec.map_comp (CommRingCat.ofHom (b i)) (CommRingCat.ofHom (ω i))
  have hsp : IsProper s := projProper O X s hproj
  let V : I → X.Opens := fun i => (pullback.fst s (spMap (b i))).opensRange
  let e : ∀ i, pullback s (spMap (b i)) ≅ (V i).toScheme := fun i =>
    (pullback.fst s (spMap (b i))).isoOpensRange
  have he : ∀ i, (e i).hom ≫ (V i).ι = pullback.fst s (spMap (b i)) := fun i =>
    Scheme.Hom.isoOpensRange_hom_ι _
  have hcov' : ∀ x : X, ∃ i, x ∈ Set.range (pullback.fst s (spMap (b i))) := by
    intro x
    have : ∃ i, a i ∉ (s x).asIdeal := by
      by_contra hc
      push Not at hc
      refine (s x).isPrime.ne_top (top_le_iff.mp ?_)
      rw [← hspan, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact hc i
    obtain ⟨i, hi⟩ := this
    refine ⟨i, ?_⟩
    rw [Scheme.Pullback.range_fst]
    exact mem_range_away (a i) (b i) (hω i).2.2 _ hi
  have hcov : ⨆ i, V i = ⊤ := by
    refine top_le_iff.mp fun x _ => ?_
    obtain ⟨i, hi⟩ := hcov' x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  have hw : ∀ i, (jQ ≫ pullback.fst s (spMap β)) ≫ s = (c ≫ spMap (ω i)) ≫ spMap (b i) := fun i => by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hover, Category.assoc, ← hβe]
  let g : ∀ i, U ⟶ pullback s (spMap (b i)) := fun i => pullback.lift _ _ (hw i)
  have hg : ∀ i, g i ≫ pullback.fst _ _ = jQ ≫ pullback.fst s (spMap β) := fun i => pullback.lift_fst _ _ _
  choose tV mV using fun i => exists_pull ((e i).inv ≫ f i) (C i).t
  replace mV := fun i => (mV i).some
  choose t₁ k using fun i => exists_pull (e i).hom (tV i)
  replace k := fun i => (k i).some
  choose aV haV using fun i => cancel_of_eq (g := g i ≫ (e i).hom) (mV i) (C i).m (by
    rw [Category.assoc, Iso.hom_inv_id_assoc]; exact (hf i).2.1 _ (hg i))
  obtain ⟨hz₁, hz₂⟩ := arith_base O
  obtain ⟨t', a', n, hn'⟩ := GlobalTheory.T.exists_semiAbelianTriple_glue_common_genericPart hext E H X U (jQ ≫ pullback.fst s (spMap β)) t I V
    (fun i => g i ≫ (e i).hom) tV aV inferInstance
    ⟨hn, s ≫ spMap (algebraMap ℤ O), inferInstance, inferInstance⟩ hpo.1 hpo.2.1 hpo.2.2.1 hpo.2.2.2 hprop hcov
    (fun i => by rw [Category.assoc, he, hg])
  choose m₁ hm₁ using fun i => comp_of_eq (n i) (k i) (he i)
  choose m₂ hm₂ using fun i => comp_of_eq (h := f i) (mV i) (k i) (Iso.hom_inv_id_assoc _ _)
  have hab : pullback.fst s (spMap β) ⁻¹' abLocus t'.G = Set.range jQ := by
    apply Set.Subset.antisymm
    · intro z hz
      obtain ⟨i, w, hw'⟩ := hcov' (pullback.fst s (spMap β) z)
      have h1 : w ∈ abLocus (t₁ i).G :=
        (abLocus_pullback abLocusOne t'.semi (m₁ i).cart.1 w).1 (by rw [hw']; exact hz)
      have h2 : f i w ∈ abLocus (C i).t.G :=
        (abLocus_pullback abLocusOne (C i).t.semi (m₂ i).cart.1 w).2 h1
      have h3 : f i w ∈ Set.range (pullback.fst (C i).s (spMap (ω i))) := by
        rw [Scheme.Pullback.range_fst]
        refine ⟨pullback.snd s (spMap β) z, (spMap (b i)).isOpenEmbedding.injective ?_⟩
        rw [← Scheme.Hom.comp_apply, ← hβe, ← Scheme.Hom.comp_apply, ← pullback.condition,
          ← Scheme.Hom.comp_apply (f i), (hf i).1, ← Scheme.Hom.comp_apply, ← pullback.condition,
          Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hw']
      obtain ⟨z', hz'⟩ := h3
      have h4 : z' ∈ Set.range (C i).jQ := by
        rw [← (C i).ab_gen]
        show _ ∈ abLocus (C i).t.G
        rw [hz']; exact h2
      obtain ⟨u, hu⟩ := h4
      obtain ⟨u', hu'⟩ := (hf i).2.2 w ⟨u, by rw [Cpt.j, Scheme.Hom.comp_apply, hu, hz']⟩
      refine ⟨u', (pullback.fst s (spMap β)).isEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, hu', hw']
    · rintro _ ⟨u, rfl⟩
      exact range_subset_abLocus_of_isProper t'.semi a'.cart.1 ⟨u, Scheme.Hom.comp_apply _ _ _⟩
  refine ⟨⟨X, s, hn, hproj, hflat, jQ, hover, hopen, hdense, t', a', hab⟩, fun i => ?_⟩
  refine ⟨f i, t₁ i, m₁ i, m₂ i, (hf i).1, (hf i).2.1, fun y hy => ?_⟩
  have hmono : IsOpenImmersion (n i).φ :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (n i).cart.1.flip inferInstance
  have hy' : y ≫ (k i).φ = (aV i).φ := by
    rw [← cancel_mono (n i).φ, Category.assoc, ← hm₁, hn']; exact hy
  rw [hm₂, ← Category.assoc, hy', haV]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModelDominatingModelsOnOpenCoverStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

theorem _root_.GlobalTheory.T.exists_model_dominating_models_on_open_cover : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (I : Type) [Finite I] [Nonempty I] (R : I → Type) [∀ i, CommRing (R i)] (a : I → O) (b : ∀ i, O →+* R i) (ω : ∀ i, R i →+* F) (C : ∀ i, Cpt c t (ω i)), IsDedFrac β → (∀ i, IsDedFrac (ω i) ∧ (ω i).comp (b i) = β ∧ @IsLocalization.Away O _ (a i) (R i) _ (b i).toAlgebra) → Ideal.span (Set.range a) = ⊤ → Algebra.FiniteType ℤ O → IsProper t.G.hom → ∃ C' : Cpt c t β, ∀ i, ∃ (f : pullback C'.s (spMap (b i)) ⟶ (C i).X) (t₁ : SAB H (pullback C'.s (spMap (b i)))) (m₁ : SABMap t₁ C'.t (pullback.fst _ _)) (m₂ : SABMap t₁ (C i).t f), f ≫ (C i).s = pullback.snd _ _ ∧ (∀ g : U ⟶ pullback C'.s (spMap (b i)), g ≫ pullback.fst _ _ = C'.j → g ≫ f = (C i).j) ∧ ∀ y : t.G.left ⟶ t₁.G.left, y ≫ m₁.φ = C'.m.φ → y ≫ m₂.φ = (C i).m.φ := by
  first | exact @GlobalTheory.exists_join_of_models | exact GlobalTheory.exists_join_of_models | (intros; apply GlobalTheory.exists_join_of_models <;> assumption)
end
end
