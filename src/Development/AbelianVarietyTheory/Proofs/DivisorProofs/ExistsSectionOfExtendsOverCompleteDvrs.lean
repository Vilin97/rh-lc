module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleGeneratorExtendingDensePart
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteTraitOverClosedPointModification
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
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SabMapOfIsoOfExtendGen
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThValAtAndNotIsThValue
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.TotallySplit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsSecNeObj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.LevelFrameOfLaws
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TraitSectionBasisDescendsFiniteDvrExtension
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Mathlib.AlgebraicGeometry.QuasiAffine
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DivMemOfForallPowSuccDivPowMem
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThValAtAndNotIsThValue

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCDvrOfIsDiscreteValuationRing

section

@[expose] public section

namespace GlobalTheory.DvrCompletion

theorem exists_cDvr_of_isDiscreteValuationRing : ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CharZero A], ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V), GlobalTheory.LN.CDvr V ∧ ∃ ι : A →+* V, Function.Injective ι ∧ IsLocalHom ι := by
  intro A _ _ _ _
  obtain ⟨V, _, _, _, ι, h, h1, h2⟩ := GlobalTheory.Mum.exists_cDvr_injective_isLocalHom A
  exact ⟨V, inferInstance, inferInstance, inferInstance, h, ι, h1, h2⟩

end GlobalTheory.DvrCompletion
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendsAtOfCodimLeOneOverCompleteDVRs

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.CodimOneExtend

theorem extAt_of_flat {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    {X XK XV XF : Scheme.{0}} {p : X ⟶ Sp R} {J : XK ⟶ X} {q : XK ⟶ Sp K}
    (H : IsPullback J q p (spMap (algebraMap R K))) (φ : XV ⟶ X) [Flat φ] (A : XF ⟶ XV)
    (hA : ∀ U, Function.Injective (A.app U).hom) (B : XF ⟶ XK) (w : B ≫ J = A ≫ φ) (W : X.Opens)
    (f : Γ(XK, J ⁻¹ᵁ W)) (s : Γ(XV, φ ⁻¹ᵁ W)) (h₂ : A ⁻¹ᵁ φ ⁻¹ᵁ W ≤ B ⁻¹ᵁ J ⁻¹ᵁ W)
    (hs : (A.appLE _ _ le_rfl).hom s = (B.appLE _ _ h₂).hom f) (v : XV) (hv : φ v ∈ W) :
    GenericExtend.ExtAt J W f (φ v) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hvU, hUW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hv W.isOpen
  have hUW : U ≤ W := hUW
  obtain ⟨a, ha, b, hb⟩ := loc_surj (nonZeroDivisors R) H hU (resG XK (J.preimage_mono hUW) f)
  have hb' : ∀ z, J z ∈ U → gs (𝟙 XK) z (J ⁻¹ᵁ U) ((J.app U).hom b) =
      cst (J ≫ p) z a * gs (𝟙 XK) z (J ⁻¹ᵁ W) f := fun z hz ↦ by
    rw [gs_pull (𝟙 XK) J z U hz, Category.id_comp, hb z hz, gs_res (𝟙 XK) z _ hz]
  have hw : ∀ t, J (B t) = φ (A t) := fun t ↦ by
    rw [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply]
  have e : (φ.app U).hom b = constFn (φ ≫ p) _ a * resG XV (φ.preimage_mono hUW) s := by
    refine hA _ (fn_ext fun t ht ↦ ?_)
    have ht' : J (B t) ∈ U := by rw [hw]; exact ht
    have k := congrArg (B.stalkMap t).hom (hb' (B t) ht')
    rw [map_mul, ← gs_stalkMap B t _ ht', ← gs_stalkMap B t _ (hUW ht'), H1.cst_stalkMap, gs_pull B J t U ht',
      w] at k
    have k' := congrArg (gs (𝟙 XF) t _) hs
    rw [gs_appLE A _ _ _ (𝟙 XF) t (hUW ht), gs_appLE B _ _ _ (𝟙 XF) t (hUW ht), Category.id_comp,
      Category.id_comp] at k'
    rw [gs_pull (𝟙 XF) A t _ ht, gs_pull (𝟙 XF) A t _ ht, Category.id_comp, gs_mul A t _ ht,
      gs_pull A φ t U ht, gs_constFn _ _ A t ht, gs_res A t _ ht, k, k', reassoc_of% w]
  have hd : cst p (φ v) a ∣ gs (𝟙 X) (φ v) U b := by
    refine dvd_descend φ v ?_
    have k := congrArg (gs (𝟙 XV) v _) e
    rw [gs_pull (𝟙 XV) φ v U hvU, gs_mul (𝟙 XV) v _ hvU, gs_constFn _ _ (𝟙 XV) v hvU, Category.id_comp,
      Category.id_comp] at k
    rw [← gs_stalkMap φ v U hvU, H1.cst_stalkMap, k]
    exact dvd_mul_right _ _
  obtain ⟨t, ht⟩ := hd
  obtain ⟨U', hU', c, rfl⟩ := X.presheaf.exists_germ_eq t
  have hm : φ v ∈ U ⊓ U' := ⟨hvU, hU'⟩
  have e₁ : gs (𝟙 X) (φ v) (U ⊓ U') (resG X inf_le_left b) =
      gs (𝟙 X) (φ v) (U ⊓ U') (constFn p (U ⊓ U') a * resG X inf_le_right c) := by
    rw [gs_res (𝟙 X) (φ v) _ hm, gs_mul (𝟙 X) (φ v) _ hm, gs_res (𝟙 X) (φ v) _ hm, gs_constFn p _ (𝟙 X) (φ v) hm,
      Category.id_comp, ht, gs_eq (𝟙 X) (φ v) U' hU']
    rfl
  rw [gs_eq (𝟙 X) (φ v) _ hm, gs_eq (𝟙 X) (φ v) _ hm] at e₁
  obtain ⟨O, hO, i₁, i₂, e'⟩ := X.presheaf.germ_eq (φ v) hm hm _ _ e₁
  have le : O ≤ U ⊓ U' := i₁.le
  refine ⟨O, le.trans (inf_le_left.trans hUW), resG X (le.trans inf_le_right) c, hO, fn_ext fun z hz ↦ ?_⟩
  have hz' : J z ∈ U ⊓ U' := le hz
  have k := (gs_res J z le hz _).symm.trans ((congrArg (gs J z O) e').trans (gs_res J z le hz _))
  have k' : gs J z (U ⊓ U') (resG X inf_le_left b) =
      gs J z (U ⊓ U') (constFn p (U ⊓ U') a * resG X inf_le_right c) := k
  rw [gs_res J z _ hz', gs_mul J z _ hz', gs_res J z _ hz', gs_constFn p _ J z hz'] at k'
  have k₂ := hb' z hz'.1
  rw [gs_pull (𝟙 XK) J z U hz'.1, Category.id_comp, k'] at k₂
  have hu : IsUnit (cst (J ≫ p) z a) := by
    rw [H.w, cst_comp]
    refine IsUnit.of_mul_eq_one (cst q z (algebraMap R K a)⁻¹) ?_
    rw [← H1.cst_mul, mul_inv_cancel₀ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ha), H1.cst_one]
  rw [gs_appLE J _ _ _ (𝟙 XK) z hz, Category.id_comp, gs_res J z _ hz, gs_res (𝟙 XK) z _ hz]
  exact hu.mul_left_cancel k₂

theorem exists_cDvr_flat (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [CharZero R] (𝔭 : Ideal R) [𝔭.IsPrime] (h : 𝔭.height = 1) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V), GlobalTheory.LN.CDvr V ∧ ∃ φ : R →+* V,
      Function.Injective φ ∧ φ.Flat ∧ (IsLocalRing.maximalIdeal V).comap φ = 𝔭 := by
  have := ((GlobalTheory.normal_domain_height_one.{0, 0, 0} R (FractionRing R)).1 𝔭 h).1
  have hi : Function.Injective (algebraMap R (Localization.AtPrime 𝔭)) :=
    IsLocalization.injective _ 𝔭.primeCompl_le_nonZeroDivisors
  have : CharZero (Localization.AtPrime 𝔭) := charZero_of_injective_algebraMap hi
  obtain ⟨V, _, _, _, hV, j, hj, hl⟩ :=
    GlobalTheory.DvrCompletion.exists_cDvr_of_isDiscreteValuationRing (Localization.AtPrime 𝔭)
  refine ⟨V, _, _, _, hV, j.comp (algebraMap R _), hj.comp hi, ?_, ?_⟩
  · refine RingHom.Flat.comp (RingHom.flat_algebraMap_iff.2 inferInstance) ?_
    let _ := j.toAlgebra
    have : FaithfulSMul (Localization.AtPrime 𝔭) V := (faithfulSMul_iff_algebraMap_injective _ _).2 hj
    exact (inferInstance : Module.Flat (Localization.AtPrime 𝔭) V)
  · rw [← Ideal.comap_comap, IsLocalRing.maximalIdeal_comap]
    exact Localization.AtPrime.under_maximalIdeal

theorem exists_map_fractionRing {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (φ : R →+* V)
    (hφ : Function.Injective φ) : ∃ φK : FractionRing R →+* FractionRing V,
      φK.comp (algebraMap R (FractionRing R)) = (algebraMap V (FractionRing V)).comp φ :=
  ⟨IsLocalization.map (M := nonZeroDivisors R) (T := nonZeroDivisors V) (FractionRing V) φ
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective φ hφ), IsLocalization.map_comp _⟩

theorem extAt_of_coheight_le_one : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (χ : Sp R ⟶ S) (W : (Over.mk χ ⊗ G).left.Opens) (f : Γ((Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⊗ G).left, ((Over.homMk (spMap (algebraMap R (FractionRing R))) rfl : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ) ▷ G).left ⁻¹ᵁ W)), (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (φ : R →+* V) (φK : FractionRing R →+* FractionRing V) (h : spMap φK ≫ spMap (algebraMap R (FractionRing R)) ≫ χ = spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ), φK.comp (algebraMap R (FractionRing R)) = (algebraMap V (FractionRing V)).comp φ → ∃ s : Γ((Over.mk (spMap φ ≫ χ) ⊗ G).left, ((Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ χ) ⟶ Over.mk χ) ▷ G).left ⁻¹ᵁ W), ∀ (O : (Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) ⊗ G).left.Opens) (h₁ : O ≤ ((Over.homMk (spMap (algebraMap V (FractionRing V))) rfl : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) ⟶ Over.mk (spMap φ ≫ χ)) ▷ G).left ⁻¹ᵁ (((Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ χ) ⟶ Over.mk χ) ▷ G).left ⁻¹ᵁ W)) (h₂ : O ≤ ((Over.homMk (spMap φK) h : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) ⟶ Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ)) ▷ G).left ⁻¹ᵁ (((Over.homMk (spMap (algebraMap R (FractionRing R))) rfl : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ) ▷ G).left ⁻¹ᵁ W)), (((Over.homMk (spMap (algebraMap V (FractionRing V))) rfl : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) ⟶ Over.mk (spMap φ ≫ χ)) ▷ G).left.appLE _ O h₁).hom s = (((Over.homMk (spMap φK) h : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) ⟶ Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ)) ▷ G).left.appLE _ O h₂).hom f) → ∀ y ∈ W, Order.coheight y ≤ 1 → y ∉ Set.range ((Over.homMk (spMap (algebraMap R (FractionRing R))) rfl : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ) ▷ G).left → GlobalTheory.GenericExtend.ExtAt ((Over.homMk (spMap (algebraMap R (FractionRing R))) rfl : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ) ▷ G).left W f y := by
  intro S G _ hG R _ _ _ _ _ χ W f hf y hy h1 hr
  have := hG.smooth
  have fl : ∀ T : Over S, Flat (fst T G).left := fun T ↦
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback T.hom G.hom).flip inferInstance
  have := fl (Over.mk χ)
  have H := ThetaRuleCompare.isPullback_whisker (A := G)
    (Over.homMk (spMap (algebraMap R (FractionRing R))) rfl :
      Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ)
  let x : PrimeSpectrum R := (fst (Over.mk χ) G).left y
  have hx1 : Order.coheight ((fst (Over.mk χ) G).left y) ≤ 1 := GenericExtend.coheight_apply_le_one _ h1
  have hx0 : x.asIdeal ≠ ⊥ := fun h0 ↦ hr (by
    obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback H y (⊥ : PrimeSpectrum (FractionRing R)) (by
      refine PrimeSpectrum.ext (h0.trans ?_)
      exact (Ideal.comap_bot_of_injective _ (IsFractionRing.injective R (FractionRing R))).symm)
    exact ⟨z, hz⟩)
  have hx : x.asIdeal.height = 1 := by
    refine le_antisymm ?_ (ENat.one_le_iff_ne_zero.2 fun h0 ↦ hx0 (Ideal.height_eq_zero_iff_eq_bot.1 h0))
    exact (idealHeight_eq_coheight (CommRingCat.of R) x).trans_le hx1
  obtain ⟨V, _, _, _, hV, φ, hφ, hfl, hc⟩ := exists_cDvr_flat R x.asIdeal hx
  obtain ⟨φK, hK⟩ := exists_map_fractionRing φ hφ
  have hK' : spMap φK ≫ spMap (algebraMap R (FractionRing R)) =
      spMap (algebraMap V (FractionRing V)) ≫ spMap φ := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hK]
  obtain ⟨s, hs⟩ := hf V hV φ φK (by rw [reassoc_of% hK']) hK
  have HV := ThetaRuleCompare.isPullback_whisker (A := G)
    (Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ χ) ⟶ Over.mk χ)
  have HF := ThetaRuleCompare.isPullback_whisker (A := G)
    (Over.homMk (spMap (algebraMap V (FractionRing V))) rfl :
      Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) ⟶ Over.mk (spMap φ ≫ χ))
  have hφf : Flat (spMap φ) := Flat.SpecMap_iff.2 hfl
  have := MorphismProperty.of_isPullback (P := @Flat) HV.flip hφf
  have := fl (Over.mk (spMap φ ≫ χ))
  obtain ⟨v, rfl, -⟩ := Scheme.exists_preimage_of_isPullback HV y (IsLocalRing.closedPoint V)
    (PrimeSpectrum.ext hc.symm)
  have w : ((Over.homMk (spMap φK) (by simp only [Over.mk_hom]; rw [reassoc_of% hK']) :
      Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) ⟶
        Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ)) ▷ G).left ≫
      ((Over.homMk (spMap (algebraMap R (FractionRing R))) rfl :
        Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ) ▷ G).left =
      ((Over.homMk (spMap (algebraMap V (FractionRing V))) rfl :
        Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) ⟶ Over.mk (spMap φ ≫ χ)) ▷ G).left ≫
      ((Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ χ) ⟶ Over.mk χ) ▷ G).left := by
    rw [← Over.comp_left, ← Over.comp_left, ← comp_whiskerRight, ← comp_whiskerRight]
    congr 2
    exact Over.OverMorphism.ext hK'
  have hA := Exist.CubicalExtension.app_injective_generic HF
  have h₂ := congrArg (· ⁻¹ᵁ W) w
  simp only [Scheme.Hom.comp_preimage] at h₂
  exact extAt_of_flat H _ _ hA _ w W f s h₂.ge (hs _ le_rfl h₂.ge) v hy

end GlobalTheory.CodimOneExtend
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendsAtOfCodimLeOneOverCompleteDVRsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.extendsAt_of_codim_le_one_over_completeDVRs : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (χ : Sp R ⟶ S) (W : (Over.mk χ ⊗ G).left.Opens) (f : Γ((Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⊗ G).left, ((Over.homMk (spMap (algebraMap R (FractionRing R))) rfl : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ) ▷ G).left ⁻¹ᵁ W)), (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (φ : R →+* V) (φK : FractionRing R →+* FractionRing V) (h : spMap φK ≫ spMap (algebraMap R (FractionRing R)) ≫ χ = spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ), φK.comp (algebraMap R (FractionRing R)) = (algebraMap V (FractionRing V)).comp φ → ∃ s : Γ((Over.mk (spMap φ ≫ χ) ⊗ G).left, ((Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ χ) ⟶ Over.mk χ) ▷ G).left ⁻¹ᵁ W), ∀ (O : (Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) ⊗ G).left.Opens) (h₁ : O ≤ ((Over.homMk (spMap (algebraMap V (FractionRing V))) rfl : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) ⟶ Over.mk (spMap φ ≫ χ)) ▷ G).left ⁻¹ᵁ (((Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ χ) ⟶ Over.mk χ) ▷ G).left ⁻¹ᵁ W)) (h₂ : O ≤ ((Over.homMk (spMap φK) h : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) ⟶ Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ)) ▷ G).left ⁻¹ᵁ (((Over.homMk (spMap (algebraMap R (FractionRing R))) rfl : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ) ▷ G).left ⁻¹ᵁ W)), (((Over.homMk (spMap (algebraMap V (FractionRing V))) rfl : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) ⟶ Over.mk (spMap φ ≫ χ)) ▷ G).left.appLE _ O h₁).hom s = (((Over.homMk (spMap φK) h : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) ⟶ Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ)) ▷ G).left.appLE _ O h₂).hom f) → ∀ y ∈ W, Order.coheight y ≤ 1 → y ∉ Set.range ((Over.homMk (spMap (algebraMap R (FractionRing R))) rfl : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ) ▷ G).left → GlobalTheory.GenericExtend.ExtAt ((Over.homMk (spMap (algebraMap R (FractionRing R))) rfl : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ) ▷ G).left W f y := by
  first | exact @GlobalTheory.CodimOneExtend.extAt_of_coheight_le_one | exact GlobalTheory.CodimOneExtend.extAt_of_coheight_le_one | (intros; apply GlobalTheory.CodimOneExtend.extAt_of_coheight_le_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianBaseChangeNormalDomainGenericFibre

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SemiAbGenericFibre

theorem baseChange_normal_generic : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (χ : Sp R ⟶ S), IsLocallyNoetherian (Over.mk χ ⊗ G).left ∧ GlobalTheory.IsNormalScheme (Over.mk χ ⊗ G).left ∧ IsPreimmersion ((Over.homMk (spMap (algebraMap R (FractionRing R))) rfl : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ) ▷ G).left ∧ ∀ W : (Over.mk χ ⊗ G).left.Opens, Function.Injective ((((Over.homMk (spMap (algebraMap R (FractionRing R))) rfl : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ) ▷ G).left.app W).hom) := by
  intro S G _ hG R _ _ _ _ χ
  set K := FractionRing R
  set T : Over S := Over.mk χ
  set TK : Over S := Over.mk (spMap (algebraMap R K) ≫ χ)
  set h : TK ⟶ T := Over.homMk (spMap (algebraMap R K)) rfl
  have hpb : IsPullback (h ▷ G).left (CartesianMonoidalCategory.fst TK G).left
      (CartesianMonoidalCategory.fst T G).left (spMap (algebraMap R K)) :=
    GlobalTheory.ThetaRuleCompare.isPullback_whisker h
  have hsm : Smooth G.hom := hG.smooth
  have h1 : IsPullback (CartesianMonoidalCategory.snd T G).left (CartesianMonoidalCategory.fst T G).left G.hom T.hom :=
    (IsPullback.of_hasPullback T.hom G.hom).flip
  have hsf : Smooth (CartesianMonoidalCategory.fst T G).left := MorphismProperty.of_isPullback h1 hsm
  have : IsLocallyNoetherian T.left := (inferInstance : IsLocallyNoetherian (Sp R))
  have : IsLocallyNoetherian (T ⊗ G).left := LocallyOfFiniteType.isLocallyNoetherian (CartesianMonoidalCategory.fst T G).left
  have : GlobalTheory.IsNormalScheme T.left := (inferInstance : GlobalTheory.IsNormalScheme (Sp R))
  have : IsPreimmersion (spMap (algebraMap R K)) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  refine ⟨inferInstance, GlobalTheory.isNormalScheme_of_smooth (CartesianMonoidalCategory.fst T G).left,
    MorphismProperty.of_isPullback hpb.flip ‹_›, fun W => ?_⟩
  have : IsDominant (spMap (algebraMap R K)) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K)).le.trans bot_le)⟩
  have : QuasiCompact (spMap (algebraMap R K)) := by
    set_option backward.isDefEq.respectTransparency.types false in
      exact (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr (by infer_instance)
  have : IsSchemeTheoreticallyDominant (spMap (algebraMap R K)) :=
    IsSchemeTheoreticallyDominant.of_isDominant _
  have : IsSchemeTheoreticallyDominant (h ▷ G).left :=
    IsSchemeTheoreticallyDominant.of_isPullback hpb.flip
  have : QuasiCompact (h ▷ G).left :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) hpb.flip inferInstance
  exact (h ▷ G).left.app_injective W

end GlobalTheory.SemiAbGenericFibre
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianBaseChangeNormalDomainGenericFibreStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.semiAbelian_baseChange_normal_domain_generic_fibre : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (χ : Sp R ⟶ S), IsLocallyNoetherian (Over.mk χ ⊗ G).left ∧ GlobalTheory.IsNormalScheme (Over.mk χ ⊗ G).left ∧ IsPreimmersion ((Over.homMk (spMap (algebraMap R (FractionRing R))) rfl : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ) ▷ G).left ∧ ∀ W : (Over.mk χ ⊗ G).left.Opens, Function.Injective ((((Over.homMk (spMap (algebraMap R (FractionRing R))) rfl : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ) ▷ G).left.app W).hom) := by
  first | exact @GlobalTheory.SemiAbGenericFibre.baseChange_normal_generic | exact GlobalTheory.SemiAbGenericFibre.baseChange_normal_generic | (intros; apply GlobalTheory.SemiAbGenericFibre.baseChange_normal_generic <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionOfExtendsOverCompleteDvrs

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.SecExtend

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] {L : LB G.left}

theorem pullS_homMk_id {F : Type} [CommRing F] {x : Sp F ⟶ S} (t : SecAt G L x) :
    VVRank.pullS G _ (Over.homMk (𝟙 _) (by simp) : Over.mk x ⟶ Over.mk x) t = t := by
  have e : (Over.homMk (𝟙 _) (by simp) : Over.mk x ⟶ Over.mk x) = 𝟙 _ := Over.OverMorphism.ext rfl
  refine ThetaRuleCompare.sec_ext fun j => fn_ext fun y hy => ?_
  refine (ThetaRuleCompare.gs_pullS _ t (𝟙 _) y j hy).trans ?_
  rw [e, MonoidalCategory.id_whiskerRight, Over.id_left, Category.id_comp]

theorem eq_pullS_of_cast {F : Type} [CommRing F] {x₁ x₂ : Sp F ⟶ S} (h : x₁ = x₂)
    (t : SecAt G L x₁) (u : SecAt G L x₂) (E : SecM.ofSec G u = SecM.ofSec G (h ▸ t)) :
    u = VVRank.pullS G _ (Over.homMk (𝟙 _) (by simp [h]) : Over.mk x₂ ⟶ Over.mk x₁) t := by
  subst h
  rw [pullS_homMk_id]
  exact ThetaRuleCompare.sec_ext fun j => congrFun (congrArg Subtype.val E) j

theorem gs_appLE {Z Y : Scheme.{0}} (g : Z ⟶ Y) (U : Y.Opens) (O : Z.Opens) (h : O ≤ g ⁻¹ᵁ U) (b : Γ(Y, U))
    (z : Z) (hz : z ∈ O) : gs (𝟙 Z) z O ((g.appLE U O h).hom b) = gs g z U b :=
  (gs_res (𝟙 Z) z h hz ((g.app U).hom b)).trans
    ((gs_pull (𝟙 Z) g z U (h hz) b).trans (by rw [Category.id_comp]))

theorem exists_sec_of_extends : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left), L.IsLB → IsSemiAbelian G → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (χ : Sp R ⟶ S) (θ : SecAt G L (spMap (algebraMap R (FractionRing R)) ≫ χ)), (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (φ : R →+* V) (φK : FractionRing R →+* FractionRing V) (h : spMap φK ≫ spMap (algebraMap R (FractionRing R)) ≫ χ = spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ), φK.comp (algebraMap R (FractionRing R)) = (algebraMap V (FractionRing V)).comp φ → ∃ σ : SecAt G L (spMap φ ≫ χ), SecM.ofSec G (SecAt.pull G L σ (algebraMap V (FractionRing V))) = SecM.ofSec G (h ▸ SecAt.pull G L θ φK)) → ∃ σ : SecAt G L χ, SecM.ofSec G (SecAt.pull G L σ (algebraMap R (FractionRing R))) = SecM.ofSec G θ := by
  intro S G _ L hL hG R _ _ _ _ _ χ θ H
  obtain ⟨hLN, hN, hPre, hInj⟩ := GlobalTheory.T.semiAbelian_baseChange_normal_domain_generic_fibre S G hG R χ
  let hK : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ :=
    Over.homMk (spMap (algebraMap R (FractionRing R))) rfl
  let fK : ∀ j, Γ((Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⊗ G).left,
      (hK ▷ G).left ⁻¹ᵁ (LPow G L ((1 : ℕ) : ℤ) (Over.mk χ)).U j) := fun j =>
    ((Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⊗ G).left.presheaf.map
      (homOfLE (ThetaRuleCompare.chart_ge hK j)).op).hom (θ.f j)
  have ext : ∀ j, ∃ s : Γ((Over.mk χ ⊗ G).left, (LPow G L ((1 : ℕ) : ℤ) (Over.mk χ)).U j),
      ((hK ▷ G).left.app _).hom s = fK j := fun j =>
    GenericExtend.exists_app_eq (hK ▷ G).left hInj _ (fK j) (GlobalTheory.T.extendsAt_of_codim_le_one_over_completeDVRs S G hG R χ _ (fK j) (by
      intro V _ _ _ hV φ φK h hφ
      obtain ⟨σV, E⟩ := H V hV φ φK h hφ
      let hφR : Over.mk (spMap φ ≫ χ) ⟶ Over.mk χ := Over.homMk (spMap φ) rfl
      let hVV : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) ⟶ Over.mk (spMap φ ≫ χ) :=
        Over.homMk (spMap (algebraMap V (FractionRing V))) rfl
      let B : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) ⟶
          Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) := Over.homMk (spMap φK) h
      have E' := eq_pullS_of_cast G h _ _ E
      have E'' : VVRank.pullS G _ hVV σV = VVRank.pullS G _ B θ := by
        refine E'.trans ((ThetaRuleCompare.pullS_comp _ _ θ).trans ?_)
        congr 1
      refine ⟨((Over.mk (spMap φ ≫ χ) ⊗ G).left.presheaf.map
        (homOfLE (ThetaRuleCompare.chart_ge hφR j)).op).hom (σV.f j), fun O h₁ h₂ => fn_ext fun x hx => ?_⟩
      have hx₁ := h₁ hx
      have hx₂ := h₂ hx
      have hxc : x ∈ (LPow G L ((1 : ℕ) : ℤ) (Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ))).U j :=
        ThetaRuleCompare.chart_ge (a := ((1 : ℕ) : ℤ)) hVV j (ThetaRuleCompare.chart_ge (a := ((1 : ℕ) : ℤ)) hφR j hx₁)
      rw [gs_appLE _ _ _ _ _ x hx, gs_appLE _ _ _ _ _ x hx, gs_res _ x _ hx₁, gs_res _ x _ hx₂]
      have a₁ := ThetaRuleCompare.gs_pullS hVV σV (𝟙 _) x j hxc
      have a₂ := ThetaRuleCompare.gs_pullS B θ (𝟙 _) x j hxc
      rw [Category.id_comp] at a₁ a₂
      rw [← a₁, ← a₂, E'']))
  choose s hs using ext
  have hv : ∀ j (w : (Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⊗ G).left),
      (hK ▷ G).left w ∈ (LPow G L ((1 : ℕ) : ℤ) (Over.mk χ)).U j →
      gs (𝟙 _ ≫ (hK ▷ G).left) w _ (s j) = gs (𝟙 _) w _ (θ.f j) := fun j w hw =>
    (gs_pull (𝟙 _) _ w _ hw _).symm.trans ((congrArg (gs (𝟙 _) w _) (hs j)).trans
      (gs_res (𝟙 _) w (ThetaRuleCompare.chart_ge hK j) hw _))
  refine ⟨⟨s, fun j j' => hInj _ (fn_ext fun w hw => ?_)⟩,
    congrArg (SecM.ofSec G) (ThetaRuleCompare.sec_ext fun j => fn_ext fun w hw => ?_)⟩
  · have hw' : (𝟙 _ ≫ (hK ▷ G).left) w ∈ (LPow G L ((1 : ℕ) : ℤ) (Over.mk χ)).U j ⊓
        (LPow G L ((1 : ℕ) : ℤ) (Over.mk χ)).U j' := hw
    refine (gs_pull (𝟙 _) _ w _ hw' _).trans (Eq.trans ?_ (gs_pull (𝟙 _) _ w _ hw' _).symm)
    refine ((gs_res _ w _ hw' _).trans ((hv j w hw'.1).trans
      (sec_trans (L := L) (φ := fun _ : Fin 1 => (snd (Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ)) G).left)
        (ε := fun _ => ((1 : ℕ) : ℤ)) θ (𝟙 _) w
        (ThetaRuleCompare.chart_ge (a := ((1 : ℕ) : ℤ)) hK j hw'.1)
        (ThetaRuleCompare.chart_ge (a := ((1 : ℕ) : ℤ)) hK j' hw'.2)))).trans (Eq.symm ?_)
    refine (gs_mul _ w _ hw' _ _).trans (congrArg₂ (· * ·) ((gs_unit _ w _ hw' _).trans (congrArg Units.val
      ((gm_linComb L _ _ _ w j j' hw'.1 hw'.2).trans ?_))) ((gs_res _ w _ hw' _).trans (hv j' w hw'.2)))
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Category.assoc, VVRank.whisker_snd_left]
  · exact (ThetaRuleCompare.gs_pullS hK _ _ w j hw).trans
      (hv j w (chart_le_res G L (hK ▷ G) (whiskerRight_snd _ _) _ j hw))
end GlobalTheory.UMin.SecExtend
end
end
end
