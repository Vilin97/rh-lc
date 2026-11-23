module

public import Development.EtaleCohomology.CohomologicalPurity.LeafClCut
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
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
import Mathlib.Tactic.Linter.Style
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

-- Source module: Development.EtaleCohomology.CohomologicalPurity.LeafGenPf

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.CohomologicalPurity.Cl

def LeafGenCart : Prop := ∀ {X Z : Scheme.{0}} (ι : Z ⟶ X) [IsClosedImmersion ι] (V : X.affineOpens) (r : Γ(X, V.1)),
  ∃ z : Spec (CommRingCat.of (Localization.Away r ⧸ (ι.ker.ideal V).map (algebraMap Γ(X, V.1) (Localization.Away r)))) ⟶ Z,
    IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _))) z
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1) (Localization.Away r))) ≫ V.2.fromSpec) ι

def LeafGenKer : Prop := ∀ {X Z : Scheme.{0}} (ι : Z ⟶ X) [IsClosedImmersion ι] (V : X.affineOpens) (r : Γ(X, V.1)),
  (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      ((ι.ker.ideal V).map (algebraMap Γ(X, V.1) (Localization.Away r)))))).ker =
    ι.ker.comap (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1) (Localization.Away r))) ≫ V.2.fromSpec)

theorem LeafGenCart_of (hK : LeafGenKer) : LeafGenCart := by
  intro X Z ι _ V r
  have hK' := hK ι V r
  have hm : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      ((ι.ker.ideal V).map (algebraMap Γ(X, V.1) (Localization.Away r)))))) :=
    IsClosedImmersion.spec_of_quotient_mk (R := CommRingCat.of (Localization.Away r)) _
  have hfst := Scheme.IdealSheafData.ker_fst_of_isClosedImmersion ι
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1) (Localization.Away r))) ≫ V.2.fromSpec)
  let e := IsClosedImmersion.lift (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1)
    (Localization.Away r))) ≫ V.2.fromSpec) ι) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      ((ι.ker.ideal V).map (algebraMap Γ(X, V.1) (Localization.Away r)))))) (by rw [hfst, hK'])
  refine ⟨e ≫ pullback.snd _ _, isPullback_of_isClosedImmersion _ ι _ _ ?_ hK'.symm⟩
  rw [Category.assoc, ← pullback.condition, IsClosedImmersion.lift_fac_assoc]

theorem span_loc {d : ℕ} {A : Type} [CommRing A] (I : Ideal A) (a : Fin d → A) (r : A) (ha : ∀ j, a j ∈ I)
    (hra : ∀ y ∈ I, r * y ∈ Ideal.span (Set.range a)) :
    Ideal.span (Set.range (algebraMap A (Localization.Away r) ∘ a)) = I.map (algebraMap A (Localization.Away r)) := by
  rw [Set.range_comp, ← Ideal.map_span]
  apply le_antisymm
  · exact Ideal.map_mono (Ideal.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact ha j))
  · rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [Ideal.mem_comap]
    have hu : IsUnit (algebraMap A (Localization.Away r) r) := IsLocalization.Away.algebraMap_isUnit r
    have h1 : algebraMap A (Localization.Away r) (r * y) ∈ (Ideal.span (Set.range a)).map (algebraMap A (Localization.Away r)) :=
      Ideal.mem_map_of_mem _ (hra y hy)
    rw [map_mul] at h1
    obtain ⟨u, hu'⟩ := hu
    have := Ideal.mul_mem_left _ (↑u⁻¹ : Localization.Away r) h1
    rwa [← hu', ← mul_assoc, Units.inv_mul, one_mul] at this

theorem LeafGen_of (hC : LeafChart) (hGR : LeafGenRing) (hKer : LeafGenKer) : LeafGen := by
  have hCart : LeafGenCart := LeafGenCart_of @hKer
  intro d P x hx
  obtain ⟨V, hxV, -, hfg, hch⟩ := hC d P x ⊤ trivial
  obtain ⟨a, r, hr1, ha, hra⟩ := hGR d Γ(P.X, V.1) (P.ι.ker.ideal V) hfg hch
  have := P.cl
  obtain ⟨z, hz⟩ := hCart P.ι V r
  have hxr : x ∈ Set.range P.ι := by
    by_contra h; exact hx (by rw [← SetLike.mem_coe, P.hU]; exact h)
  refine ⟨⟨Localization.Away r, (P.ι.ker.ideal V).map (algebraMap _ _), algebraMap _ _ ∘ a,
    span_loc _ a r ha hra, Spec.map (CommRingCat.ofHom (algebraMap _ _)) ≫ V.2.fromSpec, z, ?_, hz⟩, ?_, ?_⟩
  · intro y hy
    change (_ ≫ V.2.fromSpec) y ∈ P.U
    rw [← SetLike.mem_coe, P.hU]
    rintro ⟨t, ht⟩
    obtain ⟨s, hs, -⟩ := Scheme.exists_preimage_of_isPullback hz y t ht.symm
    apply hy
    rw [← hs]
    intro g hg
    change Ideal.Quotient.mk _ g ∈ s.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hg]; exact zero_mem _
  · change IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap _ _)) ≫ V.2.fromSpec)
    have h1 := Scheme.isOpenImmersion_SpecMap_localizationAway (R := Γ(P.X, V.1)) r
    have h2 := V.2.isOpenImmersion_fromSpec
    infer_instance
  · have hxV' : x ∈ (V.1 : Set P.X) := hxV
    rw [← V.2.range_fromSpec] at hxV'
    obtain ⟨p, hp⟩ := hxV'
    have hz0 : x ∈ P.X.zeroLocus (U := V.1) (P.ι.ker.ideal V) := by
      rw [← Scheme.IdealSheafData.mem_support_iff_of_mem hxV, ← SetLike.mem_coe, Scheme.Hom.support_ker]; exact subset_closure hxr
    have hIp : ∀ g ∈ P.ι.ker.ideal V, g ∈ p.asIdeal := by
      intro g hg
      have h1 := (Scheme.mem_zeroLocus_iff _ _ _).1 hz0 g hg
      by_contra h2
      apply h1
      rw [← hp]
      change p ∈ V.2.fromSpec ⁻¹ᵁ P.X.basicOpen g
      rw [V.2.fromSpec_preimage_basicOpen]; exact h2
    have hr : p ∈ PrimeSpectrum.basicOpen r := by
      intro h; apply p.2.ne_top; rw [Ideal.eq_top_iff_one]
      have := p.asIdeal.sub_mem h (hIp _ hr1); simpa using this
    have hr' : p ∈ Set.range (PrimeSpectrum.comap (algebraMap Γ(P.X, V.1) (Localization.Away r))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]; exact hr
    obtain ⟨q, hq⟩ := hr'
    refine ⟨q, ?_⟩
    show V.2.fromSpec ((Spec.map (CommRingCat.ofHom (algebraMap Γ(P.X, V.1) (Localization.Away r)))) q) = x
    rw [← hp]
    exact congrArg V.2.fromSpec hq

end LateralTheory.CohomologicalPurity.Cl
end
end
end

-- Source module: Development.EtaleCohomology.CohomologicalPurity.LeafGenKerPf

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.CohomologicalPurity.Cl

theorem ker_specMap_mk_appTop {R : CommRingCat.{0}} (I : Ideal R) :
    RingHom.ker (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).appTop.hom =
      I.comap (Scheme.ΓSpecIso R).hom.hom := by
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk I))
  calc RingHom.ker (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).appTop.hom
      = RingHom.ker ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).appTop ≫
          (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ I))).hom).hom := by
        rw [← RingHom.ker_equiv_comp _ (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv]; rfl
    _ = RingHom.ker ((Scheme.ΓSpecIso R).hom ≫ CommRingCat.ofHom (Ideal.Quotient.mk I)).hom := by rw [h]; rfl
    _ = _ := by rw [CommRingCat.hom_comp, ← RingHom.comap_ker, CommRingCat.hom_ofHom, Ideal.mk_ker]

theorem comap_iso_inv {A B : CommRingCat.{0}} (e : A ≅ B) (J : Ideal A) :
    J.comap e.inv.hom = J.map e.hom.hom := by
  have h := Ideal.comap_symm (I := J) e.commRingCatIsoToRingEquiv
  exact h

theorem ker_specMap_mk_top {B : CommRingCat.{0}} (IB : Ideal B) :
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk IB))).ker.ideal ⟨⊤, isAffineOpen_top _⟩ =
      IB.comap (Scheme.ΓSpecIso B).hom.hom := by
  rw [Scheme.ker_of_isAffine, Scheme.IdealSheafData.ofIdealTop_ideal, ← ker_specMap_mk_appTop]
  convert Ideal.map_id _
  rw [show (homOfLE (X := (Spec (CommRingCat.of B)).Opens) (le_top (a := ⊤))).op = 𝟙 _ from Subsingleton.elim _ _,
    CategoryTheory.Functor.map_id]
  rfl

theorem comap_ideal_top {X : Scheme.{0}} {B : CommRingCat.{0}} (I : X.IdealSheafData) (w : Spec B ⟶ X)
    [IsOpenImmersion w] (V : X.affineOpens) (ψ : Γ(X, V.1) ⟶ B) (hle : w ''ᵁ ⊤ ≤ V.1)
    (key : X.presheaf.map (homOfLE hle).op ≫ (w.appIso ⊤).hom = ψ ≫ (Scheme.ΓSpecIso B).inv) :
    (I.comap w).ideal ⟨⊤, isAffineOpen_top _⟩ = (I.ideal V).map (ψ ≫ (Scheme.ΓSpecIso B).inv).hom := by
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  rw [← Scheme.IdealSheafData.map_ideal I (U := ⟨w ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion w⟩) (V := V) hle]
  rw [comap_iso_inv, Ideal.map_map, ← CommRingCat.hom_comp]
  exact congrArg (fun f => Ideal.map (CommRingCat.Hom.hom f) (I.ideal V)) key

theorem key_gen {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (r : Γ(X, U))
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r))) ≫ hU.fromSpec)]
    (hle : (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r))) ≫ hU.fromSpec) ''ᵁ ⊤ ≤ U) :
    X.presheaf.map (homOfLE hle).op ≫
      (Scheme.Hom.appIso (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r))) ≫ hU.fromSpec) ⊤).hom =
      CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r)) ≫ (Scheme.ΓSpecIso _).inv := by
  have e : (⊤ : (Spec (CommRingCat.of (Localization.Away r))).Opens) ≤
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r))) ≫ hU.fromSpec) ⁻¹ᵁ U := by
    intro x _
    exact hle ⟨x, trivial, rfl⟩
  have e1 := Scheme.Hom.appLE_appIso_inv
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r))) ≫ hU.fromSpec) e
  have h1 : (⊤ : (Spec Γ(X, U)).Opens) ≤ hU.fromSpec ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
  have h2 : (⊤ : (Spec (CommRingCat.of (Localization.Away r))).Opens) ≤
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r))) ⁻¹ᵁ ⊤ := le_top
  have a1 : hU.fromSpec.appLE U ⊤ h1 = (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    rw [show ((eqToHom hU.fromSpec_preimage_self).op ≫ (homOfLE h1).op : Opposite.op (⊤ : (Spec Γ(X, U)).Opens) ⟶ Opposite.op ⊤) = 𝟙 _ from Subsingleton.elim _ _]
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
  have a2 : (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r)))).appLE ⊤ ⊤ h2 =
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r)))).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  calc _ = (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r))) ≫ hU.fromSpec).appLE U ⊤ e := by
        rw [← e1, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = _ := by
      rw [← Scheme.Hom.appLE_comp_appLE _ _ U ⊤ ⊤ h1 h2, a1, a2, Scheme.ΓSpecIso_inv_naturality]
      rfl

theorem hle_loc {X : Scheme.{0}} (V : X.affineOpens) (r : Γ(X, V.1))
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1) (Localization.Away r))) ≫ V.2.fromSpec)] :
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1) (Localization.Away r))) ≫ V.2.fromSpec) ''ᵁ ⊤ ≤ V.1 := by
  rw [Scheme.Hom.image_top_eq_opensRange]
  rintro _ ⟨y, rfl⟩
  show V.2.fromSpec _ ∈ (V.1 : Set X)
  rw [← V.2.range_fromSpec]; exact ⟨_, rfl⟩

theorem LeafGenKer_of : LeafGenKer := by
  intro X Z ι _ V r
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1) (Localization.Away r))) ≫ V.2.fromSpec) := by
    have h1 := Scheme.isOpenImmersion_SpecMap_localizationAway (R := Γ(X, V.1)) r
    have h2 := V.2.isOpenImmersion_fromSpec
    infer_instance
  have hle := hle_loc V r
  apply Scheme.IdealSheafData.ext_of_isAffine
  have hL := ker_specMap_mk_top (B := CommRingCat.of (Localization.Away r))
    ((ι.ker.ideal V).map (algebraMap Γ(X, V.1) (Localization.Away r)))
  have hR := comap_ideal_top ι.ker _ V _ hle (key_gen V.2 r hle)
  refine hL.trans (Eq.trans ?_ hR.symm)
  have hc := comap_iso_inv (Scheme.ΓSpecIso (CommRingCat.of (Localization.Away r))).symm
    ((ι.ker.ideal V).map (algebraMap Γ(X, V.1) (Localization.Away r)))
  simp only [Iso.symm_inv, Iso.symm_hom] at hc
  rw [hc, Ideal.map_map]
  rfl

end LateralTheory.CohomologicalPurity.Cl
end
end
end
