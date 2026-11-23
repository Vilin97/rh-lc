module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapBcComp
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.RingTheory.Flat.Basic
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafDataComapIdealTopOfIsAffine
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsAlt

section

@[expose] public section

open scoped TensorProduct

namespace GlobalTheory.ValuativeQuotient

attribute [local instance] Algebra.TensorProduct.rightAlgebra

theorem main : ∀ (V K B : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K]
    [Algebra V K] [IsFractionRing V K] [CommRing B] [Algebra V B] (JK : Ideal (K ⊗[V] B)),
    ∃! J : Ideal B, Module.Flat V (B ⧸ J) ∧
      J.map (Algebra.TensorProduct.includeRight : B →ₐ[V] K ⊗[V] B) = JK := by
  intro V K B _ _ _ _ _ _ _ _ JK
  have hloc := IsLocalization.tensorRight (S := B) K (nonZeroDivisors V)
  set M := Algebra.algebraMapSubmonoid B (nonZeroDivisors V) with hM
  have hmap : ∀ I : Ideal B,
      I.map (Algebra.TensorProduct.includeRight : B →ₐ[V] K ⊗[V] B) =
        I.map (algebraMap B (K ⊗[V] B)) := fun I => rfl
  have hsmul : ∀ (J : Ideal B) (v : V) (b : B),
      v • Ideal.Quotient.mk J b = Ideal.Quotient.mk J (algebraMap V B v * b) := by
    intro J v b
    rw [← Algebra.smul_def, ← Ideal.Quotient.mkₐ_eq_mk V, map_smul]
  have hflat : ∀ J : Ideal B, Module.Flat V (B ⧸ J) ↔ ∀ m ∈ M, ∀ b : B, m * b ∈ J → b ∈ J := by
    intro J
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, Submodule.eq_bot_iff]
    constructor
    · rintro h m ⟨v, hv, rfl⟩ b hb
      have h0 := h (Ideal.Quotient.mk J b) ((Submodule.mem_torsion_iff _).mpr
        ⟨⟨v, hv⟩, by
          show v • Ideal.Quotient.mk J b = 0
          rw [hsmul, Ideal.Quotient.eq_zero_iff_mem]
          exact hb⟩)
      exact Ideal.Quotient.eq_zero_iff_mem.mp h0
    · intro h x hx
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨⟨v, hv⟩, hvb⟩ := (Submodule.mem_torsion_iff _).mp hx
      change v • Ideal.Quotient.mk J b = 0 at hvb
      rw [hsmul, Ideal.Quotient.eq_zero_iff_mem] at hvb
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (h _ ⟨v, hv, rfl⟩ b hvb)
  refine ⟨JK.comap (algebraMap B (K ⊗[V] B)), ⟨?_, ?_⟩, ?_⟩
  · rw [hflat]
    intro m hm b hb
    rw [Ideal.mem_comap, map_mul] at hb
    exact (Ideal.unit_mul_mem_iff_mem JK (IsLocalization.map_units (K ⊗[V] B) ⟨m, hm⟩)).mp hb
  · rw [hmap]
    exact IsLocalization.map_under M (K ⊗[V] B) JK
  · rintro J' ⟨hJ'f, hJ'⟩
    rw [hmap] at hJ'
    rw [hflat] at hJ'f
    apply le_antisymm
    · rw [← hJ']
      exact Ideal.le_comap_map
    · intro b hb
      rw [Ideal.mem_comap, ← hJ', IsLocalization.mem_map_algebraMap_iff M] at hb
      obtain ⟨⟨x, m⟩, hxm⟩ := hb
      rw [← map_mul, IsLocalization.eq_iff_exists M] at hxm
      obtain ⟨c, hc⟩ := hxm
      apply hJ'f (c * m) (M.mul_mem c.2 m.2)
      have : (c : B) * (m : B) * b = c * x.1 := by rw [← hc]; ring
      rw [this]
      exact J'.mul_mem_left _ x.2

end GlobalTheory.ValuativeQuotient
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatIdealValuationRingPullback

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace GlobalTheory.FlatHilbAff


attribute [local instance] Algebra.TensorProduct.rightAlgebra in
theorem exists_flat_ideal : ∀ (V K : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (X X' : Scheme.{0}) [IsAffine X] [IsAffine X'] (p : X ⟶ Spec (CommRingCat.of V)) (p' : X' ⟶ Spec (CommRingCat.of K)) (b : X' ⟶ X), IsPullback b p' p (Spec.map (CommRingCat.ofHom (algebraMap V K))) → ∀ I : Ideal Γ(X', ⊤), ∃ J : Ideal Γ(X, ⊤), ((Ideal.Quotient.mk J).comp (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom)).Flat ∧ Ideal.map b.appTop.hom J = I := by
  intro V K _ _ _ _ _ _ X X' _ _ p p' b h I
  set φ : V →+* Γ(X, ⊤) := p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom with hφ
  letI : Algebra V Γ(X, ⊤) := φ.toAlgebra
  have H0 := isPushout_appTop_of_isPullback h
  have H : IsPushout (CommRingCat.ofHom (algebraMap V K)) (CommRingCat.ofHom (algebraMap V Γ(X, ⊤)))
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ p'.appTop) b.appTop := by
    refine H0.flip.of_iso (Scheme.ΓSpecIso _) (Scheme.ΓSpecIso _) (Iso.refl _) (Iso.refl _)
      ?_ ?_ ?_ ?_
    · exact Scheme.ΓSpecIso_naturality _
    · ext x; simp [φ, RingHom.algebraMap_toAlgebra]
    · simp
    · simp
  let e : K ⊗[V] Γ(X, ⊤) ≃+* Γ(X', ⊤) :=
    ((CommRingCat.isPushout_tensorProduct V K Γ(X, ⊤)).isoPushout ≪≫
      H.isoPushout.symm).commRingCatIsoToRingEquiv
  have he : ∀ x : Γ(X, ⊤), e (Algebra.TensorProduct.includeRight x) = b.appTop.hom x := by
    intro x
    have h1 := congr($((CommRingCat.isPushout_tensorProduct V K Γ(X, ⊤)).inr_isoPushout_hom).hom x)
    have h4 := congr($(H.inr_isoPushout_inv).hom x)
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h1 h4
    have : e (Algebra.TensorProduct.includeRight x) = H.isoPushout.inv.hom
        ((CommRingCat.isPushout_tensorProduct V K Γ(X, ⊤)).isoPushout.hom.hom
          (Algebra.TensorProduct.includeRight x)) := rfl
    rw [this]
    exact (congrArg H.isoPushout.inv.hom h1).trans h4
  obtain ⟨J, ⟨hJf, hJ⟩, -⟩ := GlobalTheory.ValuativeQuotient.main V K Γ(X, ⊤) (I.comap e.toRingHom)
  refine ⟨J, ?_, ?_⟩
  · have : (algebraMap V (Γ(X, ⊤) ⧸ J)) =
        (Ideal.Quotient.mk J).comp (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom) :=
      rfl
    rw [← this, RingHom.flat_algebraMap_iff]
    exact hJf
  · have hb : b.appTop.hom = e.toRingHom.comp
        (Algebra.TensorProduct.includeRight : Γ(X, ⊤) →ₐ[V] K ⊗[V] Γ(X, ⊤)).toRingHom := by
      ext x; exact (he x).symm
    rw [hb, ← Ideal.map_map]
    change Ideal.map e.toRingHom (J.map (Algebra.TensorProduct.includeRight : Γ(X, ⊤) →ₐ[V] K ⊗[V] Γ(X, ⊤))) = I
    rw [hJ]
    exact Ideal.map_comap_of_surjective _ e.surjective I

end GlobalTheory.FlatHilbAff
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatIdealValuationRingPullbackStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

theorem _root_.GlobalTheory.T.exists_flat_ideal_valuationRing_pullback : ∀ (V K : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (X X' : Scheme.{0}) [IsAffine X] [IsAffine X'] (p : X ⟶ Spec (CommRingCat.of V)) (p' : X' ⟶ Spec (CommRingCat.of K)) (b : X' ⟶ X), IsPullback b p' p (Spec.map (CommRingCat.ofHom (algebraMap V K))) → ∀ I : Ideal Γ(X', ⊤), ∃ J : Ideal Γ(X, ⊤), ((Ideal.Quotient.mk J).comp (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom)).Flat ∧ Ideal.map b.appTop.hom J = I := by
  first | exact @GlobalTheory.FlatHilbAff.exists_flat_ideal | exact GlobalTheory.FlatHilbAff.exists_flat_ideal | (intros; apply GlobalTheory.FlatHilbAff.exists_flat_ideal <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSubschemeOfQuotientFlatAffine

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace GlobalTheory

theorem closedSub_flat_of_quotient_flat : ∀ (V : Type) [CommRing V] (X : Scheme.{0}) [IsAffine X] (p : X ⟶ Spec (CommRingCat.of V)) (J : X.IdealSheafData), ((Ideal.Quotient.mk (J.ideal ⟨⊤, isAffineOpen_top X⟩)).comp (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom)).Flat → Flat (J.subschemeι ≫ p) := by
  intro V _ X _ p J h
  have : IsAffine J.subscheme := isAffine_of_isAffineHom J.subschemeι
  rw [HasRingHomProperty.iff_of_isAffine (P := @Flat)]
  set U : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  have e : (J.subschemeι ≫ p).appTop.hom =
      (J.subschemeObjIso U).inv.hom.comp
        (((Ideal.Quotient.mk (J.ideal U)).comp (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom)).comp
          (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom) := by
    have h2 := J.subschemeι_app U
    have h3 : J.subschemeι.appTop = CommRingCat.ofHom (Ideal.Quotient.mk (J.ideal U)) ≫ (J.subschemeObjIso U).inv := h2
    rw [Scheme.Hom.comp_appTop, h3]
    ext x
    change (J.subschemeObjIso U).inv.hom (Ideal.Quotient.mk (J.ideal U) (p.appTop.hom x)) =
      (J.subschemeObjIso U).inv.hom (Ideal.Quotient.mk (J.ideal U) (p.appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom x))))
    rw [Iso.hom_inv_id_apply]
  rw [e]
  refine RingHom.Flat.comp ?_ (RingHom.Flat.of_bijective (J.subschemeObjIso U).commRingCatIsoToRingEquiv.symm.bijective)
  refine RingHom.Flat.comp (RingHom.Flat.of_bijective (Scheme.ΓSpecIso (CommRingCat.of V)).commRingCatIsoToRingEquiv.bijective) h

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSubschemeOfQuotientFlatAffineStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

theorem _root_.GlobalTheory.T.flat_subscheme_of_quotient_flat_affine : ∀ (V : Type) [CommRing V] (X : Scheme.{0}) [IsAffine X] (p : X ⟶ Spec (CommRingCat.of V)) (J : X.IdealSheafData), ((Ideal.Quotient.mk (J.ideal ⟨⊤, isAffineOpen_top X⟩)).comp (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom)).Flat → Flat (J.subschemeι ≫ p) := by
  first | (exact @GlobalTheory.closedSub_flat_of_quotient_flat) | (exact GlobalTheory.closedSub_flat_of_quotient_flat) | (intros; apply GlobalTheory.closedSub_flat_of_quotient_flat  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafDataComapIdealTopOfIsAffineStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

theorem _root_.GlobalTheory.T.idealSheafData_comap_ideal_top_of_isAffine : ∀ (X Y : Scheme.{0}) [IsAffine X] [IsAffine Y] (f : X ⟶ Y) (J : Y.IdealSheafData), (J.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ = Ideal.map f.appTop.hom (J.ideal ⟨⊤, isAffineOpen_top Y⟩) := by
  first | exact @GlobalTheory.IdealSheafData.ideal_comap_top_of_isAffine | exact GlobalTheory.IdealSheafData.ideal_comap_top_of_isAffine | (intros; apply GlobalTheory.IdealSheafData.ideal_comap_top_of_isAffine <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertSchemeValuativeCriterionExistence

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace GlobalTheory.HilbAff

theorem exists_flat_ideal_extension (V K : Type) [CommRing V] [IsDomain V] [ValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] (X X' : Scheme.{0}) [IsAffine X] [IsAffine X']
    (p : X ⟶ Spec (CommRingCat.of V)) (p' : X' ⟶ Spec (CommRingCat.of K)) (b : X' ⟶ X)
    (h : IsPullback b p' p (Spec.map (CommRingCat.ofHom (algebraMap V K))))
    (I : X'.IdealSheafData) : ∃ J : X.IdealSheafData, Flat (J.subschemeι ≫ p) ∧ J.comap b = I := by
  obtain ⟨J₀, hf, hJ⟩ := GlobalTheory.T.exists_flat_ideal_valuationRing_pullback V K X X' p p' b h (I.ideal ⟨⊤, isAffineOpen_top X'⟩)
  have e : (Scheme.IdealSheafData.ofIdealTop J₀).ideal ⟨⊤, isAffineOpen_top X⟩ = J₀ :=
    Scheme.IdealSheafData.equivOfIsAffine.apply_symm_apply J₀
  refine ⟨Scheme.IdealSheafData.ofIdealTop J₀, GlobalTheory.T.flat_subscheme_of_quotient_flat_affine V X p _ (by rw [e]; exact hf), ?_⟩
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [GlobalTheory.T.idealSheafData_comap_ideal_top_of_isAffine, e, hJ]

theorem finrank_const_of_isLocalRing (V : Type) [CommRing V] [IsLocalRing V] (Z : Scheme.{0})
    (f : Z ⟶ Spec (CommRingCat.of V)) (h1 : IsFinite f) (h2 : Flat f) (x y : Spec (CommRingCat.of V)) :
    f.finrank x = f.finrank y := by
  have : IsAffine Z := isAffine_of_isAffineHom f
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (Z.isoSpec.inv ≫ f)
  have ef : f = Z.isoSpec.hom ≫ Spec.map φ := by rw [hφ]; simp
  have hf1 : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  have hf2 : Flat (Spec.map φ) := by rw [hφ]; infer_instance
  have hr1 := hf1
  have hr2 := hf2
  rw [IsFinite.SpecMap_iff] at hr1
  rw [Flat.SpecMap_iff] at hr2
  rw [ef, Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_SpecMap_eq_finrank hr1 hr2]
  algebraize [φ.hom]
  have : Module.Free V Γ(Z, ⊤) := Module.free_of_flat_of_isLocalRing
  rw [← RingHom.algebraMap_toAlgebra φ.hom, RingHom.finrank_algebraMap]
  simp only [Module.rankAtStalk_eq_finrank_of_free]
  rfl

theorem exists_good_extension (A B : Type) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] (r : ℕ) (V K : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K]
    [Algebra V K] [IsFractionRing V K] (g : Spec (CommRingCat.of V) ⟶ Spec (CommRingCat.of A))
    (I : (pullback (str A B) (Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ g)).IdealSheafData)
    (hI : Good A B r _ I) :
    ∃ J, Good A B r g J ∧ J.comap (bc A B g (Spec.map (CommRingCat.ofHom (algebraMap V K)))) = I := by
  obtain ⟨J, hJf, hJ⟩ := exists_flat_ideal_extension V K _ _ (pullback.snd (str A B) g) (pullback.snd _ _) _
    (isPullback_bc A B g _) I
  have : IsFinite (str A B) := by
    rw [IsFinite.SpecMap_iff]; exact RingHom.finite_algebraMap.mpr inferInstance
  have h1 : IsFinite (J.subschemeι ≫ pullback.snd (str A B) g) := inferInstance
  refine ⟨J, ⟨h1, hJf, fun y => ?_⟩, hJ⟩
  obtain ⟨_, _, h3⟩ := hI
  subst hJ
  set a := Spec.map (CommRingCat.ofHom (algebraMap V K))
  obtain ⟨pt⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  rw [finrank_const_of_isLocalRing V _ _ h1 hJf y (a pt)]
  have H : IsPullback (pullback.snd (bc A B g a) J.subschemeι)
      (pullback.fst (bc A B g a) J.subschemeι ≫ pullback.snd _ (a ≫ g))
      (J.subschemeι ≫ pullback.snd _ g) a :=
    (IsPullback.of_hasPullback (bc A B g a) J.subschemeι).flip.paste_vert (isPullback_bc A B g a)
  have e : (J.comap (bc A B g a)).subschemeι ≫ pullback.snd _ (a ≫ g) =
      (J.comapIso (bc A B g a)).hom ≫ (pullback.fst (bc A B g a) J.subschemeι ≫
        pullback.snd _ (a ≫ g)) := by
    rw [← Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst]
  have f1 : IsFinite (pullback.fst (bc A B g a) J.subschemeι ≫ pullback.snd _ (a ≫ g)) :=
    MorphismProperty.of_isPullback (P := @IsFinite) H h1
  have f2 : Flat (pullback.fst (bc A B g a) J.subschemeι ≫ pullback.snd _ (a ≫ g)) :=
    MorphismProperty.of_isPullback (P := @Flat) H hJf
  have := h3 pt
  rw [e, Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_of_isPullback _ _ _ _ H pt]
    at this
  exact this

theorem valuativeExistence (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B]
    [Module.Finite A B] (r : ℕ) (H : Scheme.{0}) (R : (GlobalTheory.HilbAff.functor A B r).RepresentableBy H) :
    ValuativeCriterion.Existence (R.homEquiv (𝟙 H)).1 := by
  intro S
  have key : ∀ {T : Scheme.{0}} (f : T ⟶ H), (R.homEquiv f).1 = f ≫ (R.homEquiv (𝟙 H)).1 := by
    intro T f
    have h := R.homEquiv_comp f (𝟙 H)
    rw [Category.comp_id] at h
    rw [h]; rfl
  set ι := Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) with hι
  have gen : ∀ x : (functor A B r).obj (op (Spec (CommRingCat.of S.K))), x.1 = ι ≫ S.i₂ →
      ∃ y : (functor A B r).obj (op (Spec (CommRingCat.of S.R))),
        y.1 = S.i₂ ∧ (functor A B r).map ι.op y = x := by
    rintro ⟨g', I, hI⟩ hx
    dsimp only at hx
    subst hx
    obtain ⟨J, hJ, hJI⟩ := exists_good_extension A B r S.R S.K S.i₂ I hI
    subst hJI
    exact ⟨⟨S.i₂, J, hJ⟩, rfl, rfl⟩
  obtain ⟨y, hy1, hy2⟩ := gen (R.homEquiv S.i₁) ((key S.i₁).trans S.commSq.w)
  refine ⟨⟨{ l := R.homEquiv.symm y, fac_left := ?_, fac_right := ?_ }⟩⟩
  · apply R.homEquiv.injective
    rw [R.homEquiv_comp, Equiv.apply_symm_apply, hy2]
  · rw [← key, Equiv.apply_symm_apply, hy1]

end GlobalTheory.HilbAff
end
end
