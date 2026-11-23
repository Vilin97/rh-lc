module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FerrandPushoutAffineFlatAndPushouts
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
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPushoutAppLEOfIsPullbackOfIsAffine
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.AlgebraicGeometry.Morphisms.Finite

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FerrandPushoutAffineFlatAndPushoutsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

theorem _root_.GlobalTheory.T.ferrandPushout_affine_flat_and_pushouts : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → Function.Surjective g₁ → Function.Surjective g₂ → IsNilpotent (RingHom.ker g₁.hom) → IsNilpotent (RingHom.ker g₂.hom) → ∀ (Y₁ Y₂ Y₀ : Scheme.{0}) (p₁ : Y₁ ⟶ Spec R₁) (p₂ : Y₂ ⟶ Spec R₂) (p₀ : Y₀ ⟶ Spec R₀) (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂), IsPullback i₁ p₀ p₁ (Spec.map g₁) → IsPullback i₂ p₀ p₂ (Spec.map g₂) → Flat p₁ → Flat p₂ → ∀ (Y : Scheme.{0}) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) (hw : i₁ ≫ j₁ = i₂ ≫ j₂), IsClosedImmersion j₁ → IsClosedImmersion j₂ → (∀ V : Y.Opens, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl) (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl))) → ∀ (y : Y ⟶ Spec P), j₁ ≫ y = p₁ ≫ Spec.map f₁ → j₂ ≫ y = p₂ ≫ Spec.map f₂ → ∀ V : Y.Opens, IsAffineOpen V → (y.appLE ⊤ V (fun _ _ => trivial)).hom.Flat ∧ IsPushout (y.appLE ⊤ V (fun _ _ => trivial)) (Spec.map f₁).appTop (j₁.app V) (p₁.appLE ⊤ (j₁ ⁻¹ᵁ V) (fun _ _ => trivial)) ∧ IsPushout (y.appLE ⊤ V (fun _ _ => trivial)) (Spec.map f₂).appTop (j₂.app V) (p₂.appLE ⊤ (j₂ ⁻¹ᵁ V) (fun _ _ => trivial)) := by
  first | exact @GlobalTheory.SchlessingerAffine.flat_and_pushouts | exact GlobalTheory.SchlessingerAffine.flat_and_pushouts | (intros; apply GlobalTheory.SchlessingerAffine.flat_and_pushouts <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackOfForallIsPushoutApp

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option autoImplicit false

namespace GlobalTheory.PushoutSquare

theorem isPullback_of_forall_isPushout_app :
    ∀ (X Y S S' : Scheme.{0}) (j : X ⟶ Y) (p : X ⟶ S') (y : Y ⟶ S) (q : S' ⟶ S), IsAffine S → IsAffine S' → IsAffineHom j → j ≫ y = p ≫ q → (∀ V : Y.Opens, IsAffineOpen V → IsPushout (y.appLE ⊤ V (fun _ _ => trivial)) q.appTop (j.app V) (p.appLE ⊤ (j ⁻¹ᵁ V) (fun _ _ => trivial))) → IsPullback j p y q := by
  intro X Y S S' j p y q hS hS' hj w H
  let φ : X ⟶ pullback y q := pullback.lift j p w
  have hφ1 : φ ≫ pullback.fst y q = j := pullback.lift_fst _ _ _
  have hφ2 : φ ≫ pullback.snd y q = p := pullback.lift_snd _ _ _
  suffices hiso : IsIso φ by
    exact IsPullback.of_iso_pullback ⟨w⟩ (asIso φ) hφ1 hφ2
  have hPb : IsPullback (pullback.fst y q) (pullback.snd y q) y q := IsPullback.of_hasPullback y q
  haveI : IsAffineHom q := inferInstance
  haveI : IsAffineHom (pullback.fst y q) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback hPb.flip inferInstance
  let U : Y.affineOpens → (pullback y q).Opens := fun V => pullback.fst y q ⁻¹ᵁ V.1
  have hU : ⨆ V, U V = ⊤ := by
    show ⨆ V : Y.affineOpens, pullback.fst y q ⁻¹ᵁ (V : Y.Opens) = ⊤
    rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]
  show MorphismProperty.isomorphisms Scheme φ
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme) U hU]
  intro V
  have hpre : φ ⁻¹ᵁ U V = j ⁻¹ᵁ V.1 := by
    show φ ⁻¹ᵁ (pullback.fst y q ⁻¹ᵁ V.1) = j ⁻¹ᵁ V.1
    rw [← Scheme.Hom.comp_preimage, hφ1]
  have hUa : IsAffineOpen (U V) := V.2.preimage _
  have hSa : IsAffineOpen (φ ⁻¹ᵁ U V) := by rw [hpre]; exact V.2.preimage j
  haveI : IsAffine (U V).toScheme := hUa
  haveI : IsAffine (φ ⁻¹ᵁ U V).toScheme := hSa

  have P1 := GlobalTheory.AffBaseChange.isPushout_appLE_of_isPullback_of_isAffine Y (pullback y q) S S'
    (pullback.fst y q) (pullback.snd y q) y q hPb hS hS' V.1 V.2
  have P2 := H V.1 V.2
  let c : Γ(pullback y q, U V) ⟶ Γ(X, j ⁻¹ᵁ V.1) := φ.appLE (U V) (j ⁻¹ᵁ V.1) hpre.ge
  have key : ∀ {T : Scheme.{0}} (g j' : X ⟶ T) (hg : g = j') (A : T.Opens) (e : j' ⁻¹ᵁ A ≤ g ⁻¹ᵁ A),
      g.appLE A (j' ⁻¹ᵁ A) e = j'.appLE A (j' ⁻¹ᵁ A) le_rfl := by
    intro T g j' hg A e; subst hg; rfl
  have hc1 : (pullback.fst y q).app V.1 ≫ c = j.app V.1 := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.app_eq_appLE]
    exact key _ _ hφ1 _ _
  have hc2 : (pullback.snd y q).appLE ⊤ (pullback.fst y q ⁻¹ᵁ V.1) (fun _ _ => trivial) ≫ c =
      p.appLE ⊤ (j ⁻¹ᵁ V.1) (fun _ _ => trivial) := by
    refine (Scheme.Hom.appLE_comp_appLE φ (pullback.snd y q) ⊤ (pullback.fst y q ⁻¹ᵁ V.1) (j ⁻¹ᵁ V.1)
      (fun _ _ => trivial) hpre.ge).trans ?_
    have e2 : ∀ (e : j ⁻¹ᵁ V.1 ≤ (φ ≫ pullback.snd y q) ⁻¹ᵁ ⊤),
        (φ ≫ pullback.snd y q).appLE ⊤ (j ⁻¹ᵁ V.1) e = p.appLE ⊤ (j ⁻¹ᵁ V.1) (fun _ _ => trivial) := by
      intro e
      have gen : ∀ (g : X ⟶ S') (hg : g = p) (e' : j ⁻¹ᵁ V.1 ≤ g ⁻¹ᵁ ⊤),
          g.appLE ⊤ (j ⁻¹ᵁ V.1) e' = p.appLE ⊤ (j ⁻¹ᵁ V.1) (fun _ _ => trivial) := by
        intro g hg e'; subst hg; rfl
      exact gen _ hφ2 e
    exact e2 _
  have hcE : c = (P1.isoIsPushout _ _ P2).hom := by
    apply P1.hom_ext
    · rw [IsPushout.inl_isoIsPushout_hom]; exact hc1
    · rw [IsPushout.inr_isoIsPushout_hom]; exact hc2
  have hcI : IsIso c := by rw [hcE]; infer_instance
  have hTop : IsIso (φ ∣_ U V).appTop := by
    rw [Scheme.Hom.appTop, morphismRestrict_app']
    refine (Scheme.Hom.appLE_congr φ _ (Scheme.Opens.ι_image_top (U V))
      ((Scheme.Opens.ι_image_top (φ ⁻¹ᵁ U V)).trans hpre) (fun f => IsIso f)).mpr ?_
    exact hcI
  exact (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms _)
    (arrowIsoSpecΓOfIsAffine (φ ∣_ U V))).mpr (inferInstanceAs (IsIso (Spec.map _)))

end GlobalTheory.PushoutSquare
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackOfForallIsPushoutAppStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

theorem _root_.GlobalTheory.T.isPullback_of_isAffine_of_forall_isPushout_appLE : ∀ (X Y S S' : Scheme.{0}) (j : X ⟶ Y) (p : X ⟶ S') (y : Y ⟶ S) (q : S' ⟶ S), IsAffine S → IsAffine S' → IsAffineHom j → j ≫ y = p ≫ q → (∀ V : Y.Opens, IsAffineOpen V → IsPushout (y.appLE ⊤ V (fun _ _ => trivial)) q.appTop (j.app V) (p.appLE ⊤ (j ⁻¹ᵁ V) (fun _ _ => trivial))) → IsPullback j p y q := by
  first | exact @GlobalTheory.PushoutSquare.isPullback_of_forall_isPushout_app | exact GlobalTheory.PushoutSquare.isPullback_of_forall_isPushout_app | (intros; apply GlobalTheory.PushoutSquare.isPullback_of_forall_isPushout_app <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFerrandPushoutOverFibreProduct

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option autoImplicit false

namespace GlobalTheory.FerrandFlat

theorem flat_of_appLE {Y : Scheme.{0}} {P : CommRingCat.{0}} (y : Y ⟶ Spec P) (h : ∀ V : Y.Opens, IsAffineOpen V → (y.appLE ⊤ V (fun _ _ => trivial)).hom.Flat) : Flat y :=
  HasRingHomProperty.of_iSup_eq_top (P := @Flat) (fun V : Y.affineOpens => V) (iSup_affineOpens_eq_top Y) (fun V => h V.1 V.2)

theorem flat_pushout : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → Function.Surjective g₁ → Function.Surjective g₂ → IsNilpotent (RingHom.ker g₁.hom) → IsNilpotent (RingHom.ker g₂.hom) → ∀ (Y₁ Y₂ Y₀ : Scheme.{0}) (p₁ : Y₁ ⟶ Spec R₁) (p₂ : Y₂ ⟶ Spec R₂) (p₀ : Y₀ ⟶ Spec R₀) (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂), IsPullback i₁ p₀ p₁ (Spec.map g₁) → IsPullback i₂ p₀ p₂ (Spec.map g₂) → Flat p₁ → Flat p₂ → ∀ (Y : Scheme.{0}) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) (hw : i₁ ≫ j₁ = i₂ ≫ j₂), IsClosedImmersion j₁ → IsClosedImmersion j₂ → (∀ V : Y.Opens, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl) (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl))) → ∀ (y : Y ⟶ Spec P), j₁ ≫ y = p₁ ≫ Spec.map f₁ → j₂ ≫ y = p₂ ≫ Spec.map f₂ → IsPullback j₁ p₁ y (Spec.map f₁) ∧ IsPullback j₂ p₂ y (Spec.map f₂) ∧ Flat y := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hg₁ hg₂ hn₁ hn₂ Y₁ Y₂ Y₀ p₁ p₂ p₀ i₁ i₂ h₁ h₂ hf₁ hf₂ Y j₁ j₂ hw hj₁ hj₂ hV y hy₁ hy₂
  have H := GlobalTheory.T.ferrandPushout_affine_flat_and_pushouts P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hg₁ hg₂ hn₁ hn₂ Y₁ Y₂ Y₀ p₁ p₂ p₀ i₁ i₂ h₁ h₂ hf₁ hf₂ Y j₁ j₂ hw
    hj₁ hj₂ hV y hy₁ hy₂
  exact ⟨GlobalTheory.T.isPullback_of_isAffine_of_forall_isPushout_appLE _ _ _ _ j₁ p₁ y (Spec.map f₁) inferInstance inferInstance inferInstance hy₁
      (fun V hV => (H V hV).2.1),
    GlobalTheory.T.isPullback_of_isAffine_of_forall_isPushout_appLE _ _ _ _ j₂ p₂ y (Spec.map f₂) inferInstance inferInstance inferInstance hy₂
      (fun V hV => (H V hV).2.2),
    flat_of_appLE y (fun V hV => (H V hV).1)⟩

end GlobalTheory.FerrandFlat
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFerrandPushoutOverFibreProductStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

theorem _root_.GlobalTheory.T.flat_ferrandPushout_over_fibreProduct : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → Function.Surjective g₁ → Function.Surjective g₂ → IsNilpotent (RingHom.ker g₁.hom) → IsNilpotent (RingHom.ker g₂.hom) → ∀ (Y₁ Y₂ Y₀ : Scheme.{0}) (p₁ : Y₁ ⟶ Spec R₁) (p₂ : Y₂ ⟶ Spec R₂) (p₀ : Y₀ ⟶ Spec R₀) (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂), IsPullback i₁ p₀ p₁ (Spec.map g₁) → IsPullback i₂ p₀ p₂ (Spec.map g₂) → Flat p₁ → Flat p₂ → ∀ (Y : Scheme.{0}) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) (hw : i₁ ≫ j₁ = i₂ ≫ j₂), IsClosedImmersion j₁ → IsClosedImmersion j₂ → (∀ V : Y.Opens, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl) (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl))) → ∀ (y : Y ⟶ Spec P), j₁ ≫ y = p₁ ≫ Spec.map f₁ → j₂ ≫ y = p₂ ≫ Spec.map f₂ → IsPullback j₁ p₁ y (Spec.map f₁) ∧ IsPullback j₂ p₂ y (Spec.map f₂) ∧ Flat y := by
  first | exact @GlobalTheory.FerrandFlat.flat_pushout | exact GlobalTheory.FerrandFlat.flat_pushout | (intros; apply GlobalTheory.FerrandFlat.flat_pushout <;> assumption)
end
end
