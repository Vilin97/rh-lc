module

public import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.TypeStar
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Combinatorics.Quiver.ReflQuiver

-- Source module: ReciprocityTheory.AnalyticForms.RegularLocalRings.LogResStC

section

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace ReciprocityTheory.AnForm.R.FinalTheorems

noncomputable abbrev reesChart {R : Type u} [CommRing R] {m : ℕ} (g : Fin m → R) (i : Fin m) :
    Subalgebra R (Localization.Away (g i)) :=
  Algebra.adjoin R (Set.range fun k => IsLocalization.mk' (Localization.Away (g i)) (g k)
    (⟨g i, Submonoid.mem_powers _⟩ : Submonoid.powers (g i)))

def ReesCharts {X W : Scheme.{u}} (π : W ⟶ X) (J : X.IdealSheafData) : Prop :=
  ∀ U : X.affineOpens, ∃ (m : ℕ) (g : Fin m → Γ(X, U.1)),
    Ideal.span (Set.range g) = J.ideal U ∧
    ∃ V : Fin m → W.Opens, (⨆ i, V i) = π ⁻¹ᵁ U.1 ∧
      ∀ i, ∃ e : (V i).toScheme ≅ Spec (CommRingCat.of (reesChart g i)),
        e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) (reesChart g i))) ≫ U.2.fromSpec =
          (V i).ι ≫ π

def LogResStC (X : Scheme.{u}) (B : TopologicalSpace.Closeds X) : Prop :=
  ∃ (J : X.IdealSheafData) (W : Scheme.{u}) (π : W ⟶ X), (J.support : Set X) ⊆ B ∧ Blowup π J ∧
    (∀ w : W, IsRegularLocalRing (W.presheaf.stalk w)) ∧
    Snc (Scheme.IdealSheafData.vanishingIdeal
      ⟨π.base ⁻¹' (B : Set X), IsClosed.preimage π.base.hom.continuous B.2⟩) ∧
    (∀ x : X, SncAt (Scheme.IdealSheafData.vanishingIdeal B) x →
      ∃ f ∈ nonZeroDivisors (X.presheaf.stalk x), stalkId J x = Ideal.span {f}) ∧
    (∃ U : X.Opens, (U : Set X) = {x : X | SncAt (Scheme.IdealSheafData.vanishingIdeal B) x} ∧
      IsIso (π ∣_ U)) ∧
    IsSeparated π ∧ LocallyOfFiniteType π ∧ ReesCharts π J

def GFLogStCR : Prop :=
  ∀ (X : Scheme.{u}) [IsNoetherian X], QE X → IsReduced X → FFinRes X →
    ∀ B : TopologicalSpace.Closeds X, Sing X ⊆ B → interior (B : Set X) = ∅ → LogResStC X B

end ReciprocityTheory.AnForm.R.FinalTheorems
end
end

-- Source module: ReciprocityTheory.AnalyticForms.RegularLocalRings.WChartsA

section

@[expose] public section

namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory

noncomputable section

theorem mem_nonZeroDivisors_of_bijective {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hb : Function.Bijective φ) {a : R} (ha : a ∈ nonZeroDivisors R) : φ a ∈ nonZeroDivisors S := by
  have key : ∀ x : S, x * φ a = 0 → x = 0 := by
    intro x hx
    obtain ⟨z, rfl⟩ := hb.2 x
    have hz : z * a = 0 := hb.1 (by rw [map_mul, map_zero]; exact hx)
    rw [(mem_nonZeroDivisors_iff.mp ha).2 z hz, map_zero]
  exact mem_nonZeroDivisors_iff.mpr ⟨fun x hx => key x (by rwa [mul_comm] at hx), key⟩

theorem isAffineOpen_of_iso {W : Scheme.{0}} (V : W.Opens) {A : CommRingCat.{0}}
    (e : V.toScheme ≅ Spec A) : IsAffineOpen V :=
  IsAffine.of_isIso e.hom

theorem sec_mem_nonZeroDivisors {W : Scheme.{0}} (V : W.Opens) {A : CommRingCat.{0}}
    (e : V.toScheme ≅ Spec A) {a : A} (ha : a ∈ nonZeroDivisors A) :
    V.topIso.hom (e.hom.appTop ((Scheme.ΓSpecIso A).inv a)) ∈ nonZeroDivisors Γ(W, V) := by
  have : IsIso e.hom.appTop := inferInstanceAs (IsIso (e.hom.app ⊤))
  have hb : Function.Bijective ((V.topIso.hom.hom).comp ((e.hom.appTop).hom.comp
      (Scheme.ΓSpecIso A).inv.hom)) :=
    (ConcreteCategory.bijective_of_isIso V.topIso.hom).comp
      ((ConcreteCategory.bijective_of_isIso e.hom.appTop).comp
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).inv))
  exact mem_nonZeroDivisors_of_bijective _ hb ha

theorem sec_algebraMap_of_iso {X W : Scheme.{0}} (π : W ⟶ X) (U : X.affineOpens) (V : W.Opens)
    (hV : V ≤ π ⁻¹ᵁ U.1) (A : Type) [CommRing A] [Algebra Γ(X, U.1) A]
    (e : V.toScheme ≅ Spec (.of A))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) A)) ≫ U.2.fromSpec = V.ι ≫ π)
    (r : Γ(X, U.1)) :
    V.topIso.hom (e.hom.appTop ((Scheme.ΓSpecIso (.of A)).inv (algebraMap _ A r))) = π.appLE _ V hV r := by
  have hVa := isAffineOpen_of_iso V e
  have h1 := IsAffineOpen.SpecMap_appLE_fromSpec π U.2 hVa hV
  have : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
  have : Mono U.2.fromSpec := IsOpenImmersion.mono _
  have h3 : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) A)) =
      hVa.isoSpec.hom ≫ Spec.map (π.appLE _ V hV) := by
    rw [← cancel_mono U.2.fromSpec, Category.assoc, he, Category.assoc, h1, ← Category.assoc,
      IsAffineOpen.isoSpec_hom_fromSpec]
  have n1 : (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) A))).appTop
      ((Scheme.ΓSpecIso _).inv r) = (Scheme.ΓSpecIso (.of A)).inv (algebraMap _ A r) := by
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
    rfl
  have n2 : (Spec.map (π.appLE _ V hV)).appTop ((Scheme.ΓSpecIso _).inv r) =
      (Scheme.ΓSpecIso _).inv (π.appLE _ V hV r) := by
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
  have n3 : ∀ x : Γ(W, V), hVa.isoSpec.hom.appTop ((Scheme.ΓSpecIso _).inv x) = V.topIso.inv x := by
    intro x
    rw [IsAffineOpen.isoSpec_hom_appTop, CommRingCat.comp_apply, ← CommRingCat.comp_apply
      (Scheme.ΓSpecIso _).inv, Iso.inv_hom_id, CommRingCat.id_apply]
  calc V.topIso.hom (e.hom.appTop ((Scheme.ΓSpecIso (.of A)).inv (algebraMap _ A r)))
      = V.topIso.hom ((e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) A))).appTop
          ((Scheme.ΓSpecIso _).inv r)) := by
        rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, n1]
    _ = V.topIso.hom ((hVa.isoSpec.hom ≫ Spec.map (π.appLE _ V hV)).appTop
          ((Scheme.ΓSpecIso _).inv r)) := by rw [h3]; rfl
    _ = π.appLE _ V hV r := by
        rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
        erw [n2, n3]
        rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]

theorem germ_mem_nonZeroDivisors {W : Scheme.{0}} {V : W.Opens} (hV : IsAffineOpen V) {a : Γ(W, V)}
    (ha : a ∈ nonZeroDivisors Γ(W, V)) (w : W) (hw : w ∈ V) :
    W.presheaf.germ V w hw a ∈ nonZeroDivisors (W.presheaf.stalk w) := by
  let := TopCat.Presheaf.algebra_section_stalk W.presheaf ⟨w, hw⟩
  have := hV.isLocalization_stalk ⟨w, hw⟩
  have h := IsLocalization.map_nonZeroDivisors_le (hV.primeIdealOf ⟨w, hw⟩).asIdeal.primeCompl
    (W.presheaf.stalk w) (Submonoid.mem_map_of_mem (algebraMap Γ(W, V) (W.presheaf.stalk w)) ha)
  exact h

theorem res_mem_nonZeroDivisors {W : Scheme.{0}} {V O : W.Opens} (h : O ≤ V) (hV : IsAffineOpen V)
    {a : Γ(W, V)} (ha : a ∈ nonZeroDivisors Γ(W, V)) :
    W.presheaf.map (homOfLE h).op a ∈ nonZeroDivisors Γ(W, O) := by
  have key : ∀ x : Γ(W, O), x * W.presheaf.map (homOfLE h).op a = 0 → x = 0 := by
    intro x hx
    refine TopCat.Presheaf.section_ext W.sheaf O x 0 (fun w hw => ?_)
    have hg := germ_mem_nonZeroDivisors hV ha w (h hw)
    have h1 : W.presheaf.germ O w hw x * W.presheaf.germ V w (h hw) a = 0 := by
      rw [← W.presheaf.germ_res_apply (homOfLE h) w hw a, ← map_mul, hx, map_zero]
    change W.presheaf.germ O w hw x = W.presheaf.germ O w hw 0
    rw [(mem_nonZeroDivisors_iff.mp hg).2 _ h1, map_zero]
  exact mem_nonZeroDivisors_iff.mpr ⟨fun x hx => key x (by rwa [mul_comm] at hx), key⟩

end

end ReciprocityTheory.AnForm.R
end
end

-- Source module: ReciprocityTheory.AnalyticForms.RegularLocalRings.WChartsB

section

@[expose] public section

namespace ReciprocityTheory.AnForm.R

open AlgebraicGeometry CategoryTheory

noncomputable section

theorem algebraMap_mem_nonZeroDivisors_of_isLocalization {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (M : Submonoid R) [IsLocalization M S] {a : R} (ha : a ∈ nonZeroDivisors R) :
    algebraMap R S a ∈ nonZeroDivisors S := by
  rw [mem_nonZeroDivisors_iff_right] at ha ⊢
  intro x hx
  obtain ⟨⟨y, m⟩, rfl⟩ := IsLocalization.mk'_surjective M x
  have h1 : algebraMap R S (y * a) = 0 := by
    rw [map_mul, ← IsLocalization.mk'_spec S y m, mul_right_comm, hx, zero_mul]
  obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff M S _).1 h1
  exact (IsLocalization.mk'_eq_zero_iff y m).2 ⟨c, ha _ (by rw [← hc, mul_assoc])⟩

theorem reesChart_lift {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {m : ℕ} (g : Fin m → R)
    (j : Fin m) (hj : φ (g j) ∈ nonZeroDivisors S) (c : Fin m → S) (hc : ∀ k, φ (g k) = c k * φ (g j)) :
    ∃ ψ : FinalTheorems.reesChart g j →+* S, ψ.comp (algebraMap R (FinalTheorems.reesChart g j)) = φ := by
  let S' := Localization.Away (φ (g j))
  have hinj : Function.Injective (algebraMap S S') :=
    IsLocalization.injective S' (Submonoid.powers_le.2 hj)
  let L : Localization.Away (g j) →+* S' := IsLocalization.Away.map _ _ φ (g j)
  have hL : ∀ r, L (algebraMap R _ r) = algebraMap S S' (φ r) := fun r =>
    IsLocalization.map_eq _ _
  have key : ∀ x ∈ FinalTheorems.reesChart g j, L x ∈ (algebraMap S S').range := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      refine ⟨c k, ?_⟩
      have hu : IsUnit (algebraMap S S' (φ (g j))) := IsLocalization.Away.algebraMap_isUnit _
      apply hu.mul_left_injective
      have := congrArg L (IsLocalization.mk'_spec (Localization.Away (g j)) (g k)
        (⟨g j, Submonoid.mem_powers _⟩ : Submonoid.powers (g j)))
      rw [map_mul, hL, hL] at this
      show algebraMap S S' (c k) * _ = L _ * _
      rw [← map_mul, ← hc]; exact this.symm
    | algebraMap r => exact ⟨φ r, (hL r).symm⟩
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  let F : FinalTheorems.reesChart g j →+* (algebraMap S S').range :=
    (L.comp (FinalTheorems.reesChart g j).val.toRingHom).codRestrict _ (fun x => key x.1 x.2)
  let E : S ≃+* (algebraMap S S').range :=
    RingEquiv.ofBijective (algebraMap S S').rangeRestrict
      ⟨fun a b h => hinj (congrArg Subtype.val h), (algebraMap S S').rangeRestrict_surjective⟩
  refine ⟨E.symm.toRingHom.comp F, ?_⟩
  ext r
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  rw [RingEquiv.symm_apply_eq]
  apply Subtype.ext
  simp [F, E, hL]
  try rfl

theorem ringEquiv_mem_nonZeroDivisors {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) {a : A}
    (ha : a ∈ nonZeroDivisors A) : e a ∈ nonZeroDivisors B := by
  rw [mem_nonZeroDivisors_iff_right] at ha ⊢
  intro x hx
  have : e.symm x * a = 0 := by
    apply e.injective; rw [map_mul, e.apply_symm_apply, hx, map_zero]
  simpa using congrArg e (ha _ this)

theorem effCartier_comap_of_isOpenImmersion' {X Y : Scheme.{0}} (I : Y.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f] (hI : FinalTheorems.EffCartier I) : FinalTheorems.EffCartier (I.comap f) := by
  intro x
  obtain ⟨U, h, hxU, hh, hU⟩ := hI (f x)
  obtain ⟨r, hrle, hxr⟩ := U.2.exists_basicOpen_le (V := f.opensRange) ⟨f x, ⟨x, rfl⟩⟩ hxU
  have himg : f ''ᵁ (f ⁻¹ᵁ Y.basicOpen r) = Y.basicOpen r := by
    rw [f.image_preimage_eq_opensRange_inf, inf_eq_right.2 hrle]
  have hUX : IsAffineOpen (f ⁻¹ᵁ Y.basicOpen r) := by
    rw [← f.isAffineOpen_iff_of_isOpenImmersion, himg]; exact U.2.basicOpen r
  have hle : f ''ᵁ (f ⁻¹ᵁ Y.basicOpen r) ≤ U.1 := himg.le.trans (Y.basicOpen_le r)
  have hnzd : ∀ (O : Y.Opens) (hO : O = Y.basicOpen r) (hOU : O ≤ U.1),
      Y.presheaf.map (homOfLE hOU).op h ∈ nonZeroDivisors Γ(Y, O) := by
    rintro O rfl hOU
    have := U.2.isLocalization_basicOpen r
    exact algebraMap_mem_nonZeroDivisors_of_isLocalization (Submonoid.powers r) hh
  let e := (f.appIso (f ⁻¹ᵁ Y.basicOpen r)).commRingCatIsoToRingEquiv
  refine ⟨⟨_, hUX⟩, e (Y.presheaf.map (homOfLE hle).op h), hxr, ?_, ?_⟩
  · exact ringEquiv_mem_nonZeroDivisors e (hnzd _ himg hle)
  · rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
    rw [← I.map_ideal (U := ⟨_, (f.isAffineOpen_iff_of_isOpenImmersion).2 hUX⟩) (V := U) hle, hU,
      Ideal.map_span, Set.image_singleton]
    rw [show ((f.appIso (f ⁻¹ᵁ Y.basicOpen r)).inv.hom : _ →+* _) = (e.symm : _ →+* _) from rfl,
      Ideal.comap_coe, Ideal.comap_symm, Ideal.map_span, Set.image_singleton]
    rfl

theorem inter_reesCharts' {X W : Scheme.{0}} (π : W ⟶ X) (J : X.IdealSheafData) (hB : FinalTheorems.Blowup π J)
    (U : X.affineOpens) {m : ℕ} (g : Fin m → Γ(X, U.1)) (_hg : Ideal.span (Set.range g) = J.ideal U)
    (V : Fin m → W.Opens) (hV : ∀ i, V i ≤ π ⁻¹ᵁ U.1)
    (e : ∀ i, (V i).toScheme ≅ Spec (CommRingCat.of (FinalTheorems.reesChart g i)))
    (he : ∀ i, (e i).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) (FinalTheorems.reesChart g i))) ≫
      U.2.fromSpec = (V i).ι ≫ π)
    (i j : Fin m) (t : Γ(W, V i))
    (ht : t = (V i).topIso.hom ((e i).hom.appTop ((Scheme.ΓSpecIso _).inv
      ⟨IsLocalization.mk' (Localization.Away (g i)) (g j) (⟨g i, Submonoid.mem_powers _⟩ : Submonoid.powers (g i)),
        Algebra.subset_adjoin ⟨j, rfl⟩⟩))) :
    V i ⊓ V j = W.basicOpen t := by
  classical
  let σ : ∀ k, FinalTheorems.reesChart g k →+* Γ(W, V k) := fun k =>
    (V k).topIso.hom.hom.comp (((e k).hom.appTop).hom.comp
      (Scheme.ΓSpecIso (.of (FinalTheorems.reesChart g k))).inv.hom)
  let q : ∀ k l, FinalTheorems.reesChart g k := fun k l =>
    ⟨IsLocalization.mk' (Localization.Away (g k)) (g l) (⟨g k, Submonoid.mem_powers _⟩ : Submonoid.powers (g k)),
      Algebra.subset_adjoin ⟨l, rfl⟩⟩
  have hq : ∀ k l, algebraMap Γ(X, U.1) (FinalTheorems.reesChart g k) (g l) =
      q k l * algebraMap Γ(X, U.1) (FinalTheorems.reesChart g k) (g k) := fun k l =>
    Subtype.ext (IsLocalization.mk'_spec _ _ _).symm
  have hsec : ∀ k r, σ k (algebraMap _ _ r) = π.appLE _ (V k) (hV k) r := fun k r =>
    sec_algebraMap_of_iso π U (V k) (hV k) _ (e k) (he k) r
  have hP : ∀ k l, π.appLE _ (V k) (hV k) (g l) = σ k (q k l) * π.appLE _ (V k) (hV k) (g k) := by
    intro k l; rw [← hsec, ← hsec, ← map_mul, ← hq]
  have hnz : ∀ k, π.appLE _ (V k) (hV k) (g k) ∈ nonZeroDivisors Γ(W, V k) := by
    intro k
    rw [← hsec]
    apply sec_mem_nonZeroDivisors (V k) (e k)
    rw [mem_nonZeroDivisors_iff_right]
    intro x hx
    have hu : IsUnit (algebraMap Γ(X, U.1) (Localization.Away (g k)) (g k)) :=
      IsLocalization.Away.algebraMap_isUnit _
    apply Subtype.ext
    exact hu.mul_left_eq_zero.1 (congrArg Subtype.val hx)
  have hti : t = σ i (q i j) := ht
  have hVi : IsAffineOpen (V i) := isAffineOpen_of_iso (V i) (e i)
  apply le_antisymm
  · intro w hw
    have hwi : w ∈ V i := hw.1
    have hwj : w ∈ V j := hw.2
    rw [Scheme.mem_basicOpen W t w hwi, hti]
    have hg : ∀ k l (hwk : w ∈ V k), W.presheaf.germ (V k) w hwk (π.appLE _ (V k) (hV k) (g l)) =
        W.presheaf.germ (π ⁻¹ᵁ U.1) w (hV k hwk) (π.app U.1 (g l)) := by
      intro k l hwk
      simp only [Scheme.Hom.appLE, CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]
    have h1 := congrArg (W.presheaf.germ (V i) w hwi) (hP i j)
    have h2 := congrArg (W.presheaf.germ (V j) w hwj) (hP j i)
    rw [map_mul, hg, hg] at h1
    rw [map_mul, hg, hg] at h2
    have hA := germ_mem_nonZeroDivisors hVi (hnz i) w hwi
    rw [hg] at hA
    have h3 : (W.presheaf.germ (V j) w hwj (σ j (q j i)) * W.presheaf.germ (V i) w hwi (σ i (q i j)) - 1) *
        W.presheaf.germ (π ⁻¹ᵁ U.1) w (hV i hwi) (π.app U.1 (g i)) = 0 := by
      rw [sub_mul, one_mul, mul_assoc, ← h1, ← h2, sub_self]
    have h4 := sub_eq_zero.1 ((mem_nonZeroDivisors_iff_right.1 hA) _ h3)
    exact IsUnit.of_mul_eq_one_right _ h4
  · have hD : IsAffineOpen (W.basicOpen t) := hVi.basicOpen t
    have hDle : W.basicOpen t ≤ V i := W.basicOpen_le t
    have hDU : W.basicOpen t ≤ π ⁻¹ᵁ U.1 := hDle.trans (hV i)
    let ρ := W.presheaf.map (homOfLE hDle).op
    let φ := π.appLE U.1 (W.basicOpen t) hDU
    have hφ : ∀ l, φ (g l) = ρ (π.appLE _ (V i) (hV i) (g l)) := fun l => by
      show _ = (π.appLE _ (V i) (hV i) ≫ W.presheaf.map (homOfLE hDle).op) (g l)
      rw [Scheme.Hom.appLE_map]
    have hu : IsUnit (ρ t) := W.toRingedSpace.isUnit_res_basicOpen t
    have key : ∀ (a b u x : Γ(W, W.basicOpen t)), u * x = 1 → a * b = a * u * (x * b) := by
      intro a b u x h; linear_combination (-(a * b)) * h
    have hc : ∀ l, φ.hom (g l) = (ρ (σ i (q i l)) * ↑hu.unit⁻¹) * φ.hom (g j) := by
      intro l
      show φ (g l) = _ * φ (g j)
      rw [hφ, hφ, hP i l, hP i j, ← hti, map_mul, map_mul]
      exact key _ _ _ _ hu.val_inv_mul
    have hnzj : φ.hom (g j) ∈ nonZeroDivisors Γ(W, W.basicOpen t) := by
      show φ (g j) ∈ _
      rw [hφ, hP i j, map_mul, ← hti]
      exact mul_mem hu.mem_nonZeroDivisors (res_mem_nonZeroDivisors hDle hVi (hnz i))
    obtain ⟨ψ, hψ⟩ := reesChart_lift φ.hom g j hnzj _ hc
    let a := hD.fromSpec
    let b := Spec.map (CommRingCat.ofHom ψ) ≫ (e j).inv ≫ (V j).ι
    have hab : b ≫ π = a ≫ π := by
      simp only [a, b, Category.assoc]
      rw [← he j, Iso.inv_hom_id_assoc, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, hψ,
        ← IsAffineOpen.SpecMap_appLE_fromSpec π U.2 hD hDU]
      rfl
    have hE : FinalTheorems.EffCartier (J.comap (a ≫ π)) := by
      rw [Scheme.IdealSheafData.comap_comp]; exact effCartier_comap_of_isOpenImmersion' _ a hB.1
    obtain ⟨h0, -, huniq⟩ := hB.2 _ (a ≫ π) hE
    have hab' : b = a := (huniq b hab).trans (huniq a rfl).symm
    intro w hw
    have hw' : w ∈ Set.range hD.fromSpec := by rw [hD.range_fromSpec]; exact hw
    obtain ⟨x, rfl⟩ := hw'
    refine ⟨hDle hw, ?_⟩
    change a x ∈ V j
    rw [← hab']
    change (V j).ι ((Spec.map (CommRingCat.ofHom ψ) ≫ (e j).inv) x) ∈ V j
    exact ((Spec.map (CommRingCat.ofHom ψ) ≫ (e j).inv) x).2

end

end ReciprocityTheory.AnForm.R
end
end
