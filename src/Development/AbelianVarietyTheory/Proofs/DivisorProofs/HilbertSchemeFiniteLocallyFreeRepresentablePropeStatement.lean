module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagonalDescendedBundleGaloisCover
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHilbRep
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSchemeFiniteFreeAlgebraAffineExistsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHilbRep
import Mathlib.Tactic.Lemma
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHilbertSchemeRepresentableOfOpenCover

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSpecFiniteFreeOfFiniteFlat

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch

namespace GlobalTheory.FiniteFlatLocal

theorem exists_finFree_local : ∀ (S Z : Scheme.{0}) (z : Z ⟶ S), IsFinite z → Flat z → LocallyOfFinitePresentation z → ∀ s : S, ∃ (W : S.Opens) (A B : Type) (_ : CommRing A) (_ : CommRing B) (_ : Algebra A B) (_ : Module.Free A B) (_ : Module.Finite A B) (eW : W.toScheme ≅ Spec (CommRingCat.of A)) (eZ : (z ⁻¹ᵁ W).toScheme ≅ Spec (CommRingCat.of B)), s ∈ W ∧ eZ.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) = (z ∣_ W) ≫ eW.hom := by
  intro S Z z h1 h2 h3 s
  obtain ⟨V, hV, hsV, -, hF⟩ := GlobalTheory.FiniteAmpleFP.exists_finFree_app_fp z (x := s) (U := ⊤) trivial
  have hZ : IsAffineOpen (z ⁻¹ᵁ V) := hV.preimage z
  letI : Algebra Γ(S, V) Γ(Z, z ⁻¹ᵁ V) := (z.app V).hom.toAlgebra
  have hfin : Module.Finite Γ(S, V) Γ(Z, z ⁻¹ᵁ V) := hF.1
  have hfree : Module.Free Γ(S, V) Γ(Z, z ⁻¹ᵁ V) := hF.2
  refine ⟨V, Γ(S, V), Γ(Z, z ⁻¹ᵁ V), inferInstance, inferInstance, inferInstance, hfree, hfin,
    hV.isoSpec, hZ.isoSpec, hsV, ?_⟩
  have e := IsAffineOpen.SpecMap_appLE_fromSpec z hV hZ le_rfl
  rw [← Scheme.Hom.app_eq_appLE] at e
  rw [← cancel_mono (hV.isoSpec.inv ≫ V.ι)]
  rw [IsAffineOpen.isoSpec_inv_ι, Category.assoc, Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec,
    morphismRestrict_ι, ← IsAffineOpen.isoSpec_hom_fromSpec hZ, Category.assoc, ← e]
  rfl

end GlobalTheory.FiniteFlatLocal
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSpecFiniteFreeOfFiniteFlatStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch

theorem _root_.GlobalTheory.T.exists_local_spec_finite_free_of_finite_flat : ∀ (S Z : Scheme.{0}) (z : Z ⟶ S), IsFinite z → Flat z → LocallyOfFinitePresentation z → ∀ s : S, ∃ (W : S.Opens) (A B : Type) (_ : CommRing A) (_ : CommRing B) (_ : Algebra A B) (_ : Module.Free A B) (_ : Module.Finite A B) (eW : W.toScheme ≅ Spec (CommRingCat.of A)) (eZ : (z ⁻¹ᵁ W).toScheme ≅ Spec (CommRingCat.of B)), s ∈ W ∧ eZ.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) = (z ∣_ W) ≫ eW.hom := by
  first | exact @GlobalTheory.FiniteFlatLocal.exists_finFree_local | exact GlobalTheory.FiniteFlatLocal.exists_finFree_local | (intros; apply GlobalTheory.FiniteFlatLocal.exists_finFree_local <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHilbertSchemeRepresentableOfIso

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HilbertSch

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

def transferMap {S Z S' Z' : Scheme.{0}} (z : Z ⟶ S) (z' : Z' ⟶ S') (eS : S' ≅ S) (eZ : Z' ≅ Z)
    (hsq : eZ.hom ≫ z = z' ≫ eS.hom) {T : Scheme.{0}} (g' : T ⟶ S') (g : T ⟶ S) (hg : g' ≫ eS.hom = g) :
    pullback z' g' ⟶ pullback z g :=
  pullback.map z' g' z g eZ.hom (𝟙 T) eS.hom hsq.symm (by rw [Category.id_comp, hg])

instance {S Z S' Z' : Scheme.{0}} (z : Z ⟶ S) (z' : Z' ⟶ S') (eS : S' ≅ S) (eZ : Z' ≅ Z)
    (hsq : eZ.hom ≫ z = z' ≫ eS.hom) {T : Scheme.{0}} (g' : T ⟶ S') (g : T ⟶ S) (hg : g' ≫ eS.hom = g) :
    IsIso (transferMap z z' eS eZ hsq g' g hg) := by
  unfold transferMap; infer_instance

def transferIso {S Z S' Z' : Scheme.{0}} (z : Z ⟶ S) (z' : Z' ⟶ S') (eS : S' ≅ S) (eZ : Z' ≅ Z)
    (hsq : eZ.hom ≫ z = z' ≫ eS.hom) {T : Scheme.{0}} (g' : T ⟶ S') (g : T ⟶ S) (hg : g' ≫ eS.hom = g) :
    pullback z' g' ≅ pullback z g :=
  asIso (transferMap z z' eS eZ hsq g' g hg)

lemma transferIso_hom_snd {S Z S' Z' : Scheme.{0}} (z : Z ⟶ S) (z' : Z' ⟶ S') (eS : S' ≅ S) (eZ : Z' ≅ Z)
    (hsq : eZ.hom ≫ z = z' ≫ eS.hom) {T : Scheme.{0}} (g' : T ⟶ S') (g : T ⟶ S) (hg : g' ≫ eS.hom = g) :
    (transferIso z z' eS eZ hsq g' g hg).hom ≫ pullback.snd z g = pullback.snd z' g' := by
  simp only [transferIso, asIso_hom, transferMap]
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

lemma transferIso_inv_snd {S Z S' Z' : Scheme.{0}} (z : Z ⟶ S) (z' : Z' ⟶ S') (eS : S' ≅ S) (eZ : Z' ≅ Z)
    (hsq : eZ.hom ≫ z = z' ≫ eS.hom) {T : Scheme.{0}} (g' : T ⟶ S') (g : T ⟶ S) (hg : g' ≫ eS.hom = g) :
    (transferIso z z' eS eZ hsq g' g hg).inv ≫ pullback.snd z' g' = pullback.snd z g := by
  rw [Iso.inv_comp_eq, transferIso_hom_snd]

lemma transferIso_map {S Z S' Z' : Scheme.{0}} (z : Z ⟶ S) (z' : Z' ⟶ S') (eS : S' ≅ S) (eZ : Z' ≅ Z)
    (hsq : eZ.hom ≫ z = z' ≫ eS.hom) {T H : Scheme.{0}} (g' : T ⟶ S') (g : T ⟶ S) (hg : g' ≫ eS.hom = g)
    (h' : H ⟶ S') (f : T ⟶ H) (hf' : f ≫ h' = g') (hf : f ≫ (h' ≫ eS.hom) = g) :
    pullback.map z' g' z' h' (𝟙 Z') f (𝟙 S') (by simp) (by rw [Category.comp_id, hf'])
        ≫ (transferIso z z' eS eZ hsq h' (h' ≫ eS.hom) rfl).hom =
      (transferIso z z' eS eZ hsq g' g hg).hom ≫
        pullback.map z g z (h' ≫ eS.hom) (𝟙 Z) f (𝟙 S) (by simp) (by rw [Category.comp_id, hf]) := by
  simp only [transferIso, asIso_hom, transferMap, pullback.map]
  apply pullback.hom_ext <;>
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp]

theorem isHilbRep_transfer : ∀ {S Z S' Z' : Scheme.{0}} (z : Z ⟶ S) (z' : Z' ⟶ S') (eS : S' ≅ S) (eZ : Z' ≅ Z),
    eZ.hom ≫ z = z' ≫ eS.hom → ∀ r : ℕ, IsHilbRep z' r → IsHilbRep z r := by
  intro S Z S' Z' z z' eS eZ hsq r hrep
  obtain ⟨H, h', U, u', hP, hC, hF, hFl, hR, hU⟩ := hrep
  set ΦH := transferIso z z' eS eZ hsq h' (h' ≫ eS.hom) rfl with hΦH
  have eu : (u' ≫ ΦH.hom) ≫ pullback.snd z (h' ≫ eS.hom) = u' ≫ pullback.snd z' h' := by
    rw [Category.assoc, transferIso_hom_snd]
  refine ⟨H, h' ≫ eS.hom, U, u' ≫ ΦH.hom, inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩
  · rw [eu]; exact hF
  · rw [eu]; exact hFl
  · rw [eu]; exact hR
  intro T g V v hv hvF hvFl hvR
  have hg : (g ≫ eS.inv) ≫ eS.hom = g := by simp
  set ΦT := transferIso z z' eS eZ hsq (g ≫ eS.inv) g hg with hΦT
  have ev : (v ≫ ΦT.inv) ≫ pullback.snd z' (g ≫ eS.inv) = v ≫ pullback.snd z g := by
    rw [Category.assoc, transferIso_inv_snd]
  have hv' : IsClosedImmersion (v ≫ ΦT.inv) := inferInstance
  obtain ⟨f, ⟨hf', w, hpb⟩, huniq⟩ := hU T (g ≫ eS.inv) V (v ≫ ΦT.inv) hv' (by rw [ev]; exact hvF)
    (by rw [ev]; exact hvFl) (by rw [ev]; exact hvR)
  have hf : f ≫ (h' ≫ eS.hom) = g := by rw [← Category.assoc, hf', hg]
  refine ⟨f, ⟨hf, w, ?_⟩, ?_⟩
  · refine hpb.of_iso (Iso.refl _) ΦT (Iso.refl _) ΦH ?_ ?_ ?_ ?_
    · simp
    · simp
    · exact transferIso_map z z' eS eZ hsq (g ≫ eS.inv) g hg h' f hf' hf
    · simp
  · rintro f₂ ⟨hf₂, w₂, hpb₂⟩
    have hf₂' : f₂ ≫ h' = g ≫ eS.inv := by rw [← hf₂]; simp
    apply huniq f₂ ⟨hf₂', w₂, ?_⟩
    refine hpb₂.of_iso (Iso.refl _) ΦT.symm (Iso.refl _) ΦH.symm ?_ ?_ ?_ ?_
    · simp
    · simp
    · rw [Iso.symm_hom, Iso.symm_hom, Iso.comp_inv_eq, Category.assoc,
        transferIso_map z z' eS eZ hsq (g ≫ eS.inv) g hg h' f₂ hf₂' hf₂, Iso.inv_hom_id_assoc]
    · simp [hΦH]

end GlobalTheory.HilbertSch
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHilbertSchemeRepresentableOfIsoStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch

theorem _root_.GlobalTheory.T.isHilbertSchemeRepresentable_of_iso : ∀ {S Z S' Z' : Scheme.{0}} (z : Z ⟶ S) (z' : Z' ⟶ S') (eS : S' ≅ S) (eZ : Z' ≅ Z), eZ.hom ≫ z = z' ≫ eS.hom → ∀ r : ℕ, IsHilbRep z' r → IsHilbRep z r := by
  first | exact @GlobalTheory.HilbertSch.isHilbRep_transfer | exact GlobalTheory.HilbertSch.isHilbRep_transfer | (intros; apply GlobalTheory.HilbertSch.isHilbRep_transfer <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHilbertSchemeRepresentableOfOpenCoverStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch

theorem _root_.GlobalTheory.T.isHilbertSchemeRepresentable_of_open_cover : ∀ (S Z : Scheme.{0}) (z : Z ⟶ S), IsFinite z → Flat z → LocallyOfFinitePresentation z → ∀ r : ℕ, (∀ s : S, ∃ W : S.Opens, s ∈ W ∧ IsHilbRep (z ∣_ W) r) → IsHilbRep z r := by
  first | (exact @GlobalTheory.HilbGlue.isHilbRep_of_cover) | (exact GlobalTheory.HilbGlue.isHilbRep_of_cover) | (intros; apply GlobalTheory.HilbGlue.isHilbRep_of_cover <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSchemeFiniteLocallyFreeRepresentablePrope

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HilbertSch

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

theorem main : ∀ (S Z : Scheme.{0}) (z : Z ⟶ S), IsFinite z → Flat z → LocallyOfFinitePresentation z → ∀ r : ℕ, ∃ (H : Scheme.{0}) (h : H ⟶ S) (U : Scheme.{0}) (u : U ⟶ pullback z h), IsProper h ∧ IsClosedImmersion u ∧ IsFinite (u ≫ pullback.snd z h) ∧ Flat (u ≫ pullback.snd z h) ∧ (∀ y, (u ≫ pullback.snd z h).finrank y = r) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S) (V : Scheme.{0}) (v : V ⟶ pullback z g), IsClosedImmersion v → IsFinite (v ≫ pullback.snd z g) → Flat (v ≫ pullback.snd z g) → (∀ y, (v ≫ pullback.snd z g).finrank y = r) → ∃! f : T ⟶ H, ∃ hf : f ≫ h = g, ∃ w : V ⟶ U, IsPullback v w (pullback.map z g z h (𝟙 Z) f (𝟙 S) (by simp) (by rw [Category.comp_id, hf])) u := by
  intro S Z z hfin hflat hlfp r
  refine GlobalTheory.T.isHilbertSchemeRepresentable_of_open_cover S Z z hfin hflat hlfp r fun s => ?_
  obtain ⟨W, A, B, _, _, _, _, _, eW, eZ, hs, hc⟩ := GlobalTheory.T.exists_local_spec_finite_free_of_finite_flat S Z z hfin hflat hlfp s
  refine ⟨W, hs, GlobalTheory.T.isHilbertSchemeRepresentable_of_iso (z ∣_ W) (Spec.map (CommRingCat.ofHom (algebraMap A B))) eW.symm eZ.symm ?_ r
    (GlobalTheory.T.hilbert_scheme_finite_free_algebra_affine_exists A B r)⟩
  rw [Iso.symm_hom, Iso.symm_hom, Iso.inv_comp_eq, ← Category.assoc, hc, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

end GlobalTheory.HilbertSch
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSchemeFiniteLocallyFreeRepresentablePropeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

theorem _root_.GlobalTheory.T.hilbertScheme_finite_locallyFree_representable_proper : ∀ (S Z : Scheme.{0}) (z : Z ⟶ S), IsFinite z → Flat z → LocallyOfFinitePresentation z → ∀ r : ℕ, ∃ (H : Scheme.{0}) (h : H ⟶ S) (U : Scheme.{0}) (u : U ⟶ pullback z h), IsProper h ∧ IsClosedImmersion u ∧ IsFinite (u ≫ pullback.snd z h) ∧ Flat (u ≫ pullback.snd z h) ∧ (∀ y, (u ≫ pullback.snd z h).finrank y = r) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S) (V : Scheme.{0}) (v : V ⟶ pullback z g), IsClosedImmersion v → IsFinite (v ≫ pullback.snd z g) → Flat (v ≫ pullback.snd z g) → (∀ y, (v ≫ pullback.snd z g).finrank y = r) → ∃! f : T ⟶ H, ∃ hf : f ≫ h = g, ∃ w : V ⟶ U, IsPullback v w (pullback.map z g z h (𝟙 Z) f (𝟙 S) (by simp) (by rw [Category.comp_id, hf])) u := by
  first | (exact @GlobalTheory.HilbertSch.main) | (exact GlobalTheory.HilbertSch.main) | (intros; apply GlobalTheory.HilbertSch.main <;> assumption)
end
end
