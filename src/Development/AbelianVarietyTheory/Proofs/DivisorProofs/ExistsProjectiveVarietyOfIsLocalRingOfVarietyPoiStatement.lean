module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqOfOpenImmersionIntegralSche
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTypeLocalizationSameFractionField

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory.FieldPair

theorem IsLocModel.exists_finiteType_localization :
    ∀ (L : Type) [Field L] (c : ℂ →+* L) (R : Subring L), IsLocModel c R →
    ∃ (S : Subring L) (hS : ∀ a, c a ∈ S) (q : Ideal S), q.IsPrime ∧ (c.codRestrict S hS).FiniteType ∧
      (∀ f : L, ∃ a ∈ S, ∃ b ∈ S, b ≠ 0 ∧ f * b = a) ∧
      ∀ f : L, f ∈ R ↔ ∃ a b : S, b ∉ q ∧ f * b = a := by
  intro L _ c R hR
  letI := hR.isLocalRing
  letI : Algebra ℂ R := (c.codRestrict R hR.const_mem).toAlgebra
  haveI : Algebra.EssFiniteType ℂ R := hR.essFiniteType
  obtain ⟨σ, hσ⟩ := (Algebra.essFiniteType_iff ℂ R).mp inferInstance
  set A := Algebra.adjoin ℂ (σ : Set R) with hA
  let S : Subring L := A.toSubring.map R.subtype
  have hSR : S ≤ R := by
    rintro _ ⟨x, -, rfl⟩; exact x.2
  have memS : ∀ x : R, x ∈ A → (x : L) ∈ S := fun x hx => ⟨x, hx, rfl⟩
  have hS : ∀ a, c a ∈ S := fun a => memS ⟨c a, hR.const_mem a⟩ (A.algebraMap_mem a)
  let q : Ideal S := (IsLocalRing.maximalIdeal R).comap (Subring.inclusion hSR)
  have unit_ne : ∀ t : R, IsUnit t → (t : L) ≠ 0 := by
    intro t ht h0
    obtain ⟨u, hu⟩ := ht.exists_right_inv
    have := congrArg (fun x : R => (x : L)) hu
    simp [h0] at this
  refine ⟨S, hS, q, Ideal.comap_isPrime _ _, ?_, ?_, ?_⟩
  · have hA' : Algebra.FiniteType ℂ A :=
      (Subalgebra.fg_iff_finiteType A).mp (Subalgebra.fg_adjoin_finset σ)
    let e : A.toSubring ≃+* S := A.toSubring.equivMapOfInjective R.subtype Subtype.val_injective
    have he : c.codRestrict S hS = (e.toRingHom : A →+* S).comp (algebraMap ℂ A) := by
      ext a; rfl
    have h2 : (algebraMap ℂ A).FiniteType := RingHom.finiteType_algebraMap.mpr hA'
    rw [he]
    exact RingHom.FiniteType.comp (RingHom.FiniteType.of_surjective _ e.surjective) h2
  · intro f
    obtain ⟨r1, hr1, r2, hr2, hr20, e⟩ := hR.frac f
    obtain ⟨t1, ht1A, ht1, h1⟩ := hσ ⟨r1, hr1⟩
    obtain ⟨t2, ht2A, ht2, h2⟩ := hσ ⟨r2, hr2⟩
    refine ⟨r1 * t1 * t2, ?_, r2 * t2 * t1, ?_, ?_, ?_⟩
    · simpa using memS _ (A.mul_mem h1 ht2A)
    · simpa using memS _ (A.mul_mem h2 ht1A)
    · exact mul_ne_zero (mul_ne_zero hr20 (unit_ne _ ht2)) (unit_ne _ ht1)
    · rw [← e]; ring
  · intro f
    constructor
    · intro hf
      obtain ⟨t, htA, ht, h⟩ := hσ ⟨f, hf⟩
      refine ⟨⟨_, memS _ h⟩, ⟨_, memS _ htA⟩, ?_, rfl⟩
      intro hq
      exact (IsLocalRing.mem_maximalIdeal _).1 hq ht
    · rintro ⟨a, b, hb, e⟩
      have hu : IsUnit (Subring.inclusion hSR b) := by
        by_contra h; exact hb ((IsLocalRing.mem_maximalIdeal _).2 h)
      obtain ⟨u, hu'⟩ := hu.exists_right_inv
      have hu'' : (b : L) * (u : L) = 1 := by
        have := congrArg (fun x : R => (x : L)) hu'; simpa using this
      have hf : f = a * u := by rw [← e, mul_assoc, hu'', mul_one]
      rw [hf]; exact R.mul_mem (hSR a.2) u.2

end GlobalTheory.FieldPair
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTypeLocalizationSameFractionFieldStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_finiteType_localization_same_fractionField : ∀ (L : Type) [Field L] (c : ℂ →+* L) (R : Subring L), IsLocModel c R →
    ∃ (S : Subring L) (hS : ∀ a, c a ∈ S) (q : Ideal S), q.IsPrime ∧ (c.codRestrict S hS).FiniteType ∧
      (∀ f : L, ∃ a ∈ S, ∃ b ∈ S, b ≠ 0 ∧ f * b = a) ∧
      ∀ f : L, f ∈ R ↔ ∃ a b : S, b ∉ q ∧ f * b = a := by
  first | exact @GlobalTheory.FieldPair.IsLocModel.exists_finiteType_localization | exact GlobalTheory.FieldPair.IsLocModel.exists_finiteType_localization | (intros; apply GlobalTheory.FieldPair.IsLocModel.exists_finiteType_localization <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctionFieldEquivOpenImmersionSpec

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.OpenSpecField

variable {S : Type} [CommRing S] [IsDomain S] {Y : Scheme.{0}} [IsIntegral Y]
  (j : Sp S ⟶ Y) [IsOpenImmersion j]

abbrev img : Y.Opens := j ''ᵁ ⊤

theorem isAffineOpen_img : IsAffineOpen (img j) := (isAffineOpen_top _).image_of_isOpenImmersion j

theorem mem_img (q : Sp S) : j.base q ∈ img j := ⟨q, trivial, rfl⟩

instance : Nonempty (img j) := ⟨⟨_, mem_img j (Classical.arbitrary (PrimeSpectrum S))⟩⟩

theorem gen_mem_img : genericPoint Y ∈ img j :=
  gen_mem (mem_img j (Classical.arbitrary (PrimeSpectrum S)))

def secEquiv : Γ(Y, img j) ≃+* S :=
  ((j.appIso ⊤) ≪≫ Scheme.ΓSpecIso (CommRingCat.of S)).commRingCatIsoToRingEquiv

instance : IsFractionRing Γ(Y, img j) Y.functionField :=
  functionField_isFractionRing_of_isAffineOpen Y _ (isAffineOpen_img j)

def fieldEquiv : Y.functionField ≃+* FractionRing S := IsFractionRing.ringEquivOfRingEquiv (secEquiv j)

theorem fieldEquiv_fnOf (a : Γ(Y, img j)) :
    fieldEquiv j (fnOf _ (gen_mem_img j) a) = algebraMap S (FractionRing S) (secEquiv j a) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ a

theorem mem_basicOpen_iff (q : Sp S) (b : Γ(Y, img j)) :
    j.base q ∈ Y.basicOpen b ↔ secEquiv j b ∉ q.asIdeal := by
  have h : (Sp S).basicOpen ((j.appIso ⊤).hom b) = (Sp S).basicOpen (j.app (img j) b) := by
    rw [Scheme.Hom.appIso_hom, CommRingCat.comp_apply, Scheme.basicOpen_res]
    exact top_inf_eq _
  change q ∈ j ⁻¹ᵁ Y.basicOpen b ↔ _
  rw [Scheme.preimage_basicOpen, ← h, basicOpen_eq_of_affine']
  exact PrimeSpectrum.mem_basicOpen _ _

theorem secEquiv_algX [Algebra ℂ S] (p : Y ⟶ Sp ℂ) (hjp : j ≫ p = spMap (algebraMap ℂ S)) (a : ℂ) :
    secEquiv j (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (img j) a) = algebraMap ℂ S a := by
  have key : p.appLE ⊤ (img j) (show img j ≤ p ⁻¹ᵁ ⊤ from le_top) ≫ (j.appIso ⊤).hom ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).hom =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ≫ CommRingCat.ofHom (algebraMap ℂ S) := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.appLE_comp_appLE_assoc]
    simp only [hjp]
    have e : (spMap (algebraMap ℂ S)).appLE ⊤ ⊤ (show (⊤ : (Sp S).Opens) ≤ spMap (algebraMap ℂ S) ⁻¹ᵁ ⊤ from le_top) = (spMap (algebraMap ℂ S)).appTop := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    rw [e]
    exact Scheme.ΓSpecIso_naturality _
  have := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv a)) key
  refine Eq.trans ?_ (this.trans ?_)
  · rfl
  · simp

theorem fieldEquiv_constFn [Algebra ℂ S] (p : Y ⟶ Sp ℂ) (hjp : j ≫ p = spMap (algebraMap ℂ S))
    (a : ℂ) : fieldEquiv j (GlobalTheory.Cartier.constFn p a) = algebraMap ℂ (FractionRing S) a := by
  rw [← fnOf_comp_algX p (img j) (gen_mem_img j), RingHom.comp_apply, fieldEquiv_fnOf,
    secEquiv_algX j p hjp, IsScalarTower.algebraMap_apply ℂ S (FractionRing S)]

theorem mem_map_locRing (q : Sp S) (g : FractionRing S) :
    g ∈ (locRing (j.base q)).map (fieldEquiv j).toRingHom ↔
      ∃ a b : S, b ∉ q.asIdeal ∧
        g * algebraMap S (FractionRing S) b = algebraMap S (FractionRing S) a := by
  have hU := isAffineOpen_img j
  have hy := mem_img j q
  have hg := gen_mem_img j
  constructor
  · rintro ⟨f, hf, rfl⟩
    obtain ⟨V, hyV, c, rfl⟩ := (mem_locRing.1 hf).exists_fnOf
    obtain ⟨b, hbV, hyb⟩ := hU.exists_basicOpen_le ⟨_, hyV⟩ hy
    have := hU.isLocalization_basicOpen b
    obtain ⟨⟨t, s, hs⟩, hts⟩ := IsLocalization.surj (Submonoid.powers b) (resG Y hbV c)
    obtain ⟨n, rfl⟩ := hs
    have hW : genericPoint Y ∈ Y.basicOpen b := gen_mem hyb
    have e1 := congrArg (fnOf _ hW) hts
    change fnOf _ hW (resG Y hbV c * resG Y (Y.basicOpen_le b) (b ^ n)) =
      fnOf _ hW (resG Y (Y.basicOpen_le b) t) at e1
    rw [map_mul, fnOf_resG, fnOf_resG, fnOf_resG] at e1
    refine ⟨secEquiv j t, secEquiv j (b ^ n), ?_, ?_⟩
    · rw [map_pow]
      exact fun h => (mem_basicOpen_iff j q b).1 hyb (q.isPrime.mem_of_pow_mem n h)
    · rw [← fieldEquiv_fnOf, ← fieldEquiv_fnOf]
      change fieldEquiv j _ * _ = _
      rw [← map_mul, e1]
  · rintro ⟨a, b, hb, e⟩
    let a' := (secEquiv j).symm a
    let b' := (secEquiv j).symm b
    have hb' : j.base q ∈ Y.basicOpen b' :=
      (mem_basicOpen_iff j q b').2 (by simpa [b'] using hb)
    refine ⟨fnOf _ hg a' * (fnOf _ hg b')⁻¹, ?_, ?_⟩
    · exact mem_locRing.2 ((regAt_fnOf hy hg a').mul
        ((unitAt_fnOf_iff hy hg b').2 hb').inv.regAt)
    · have hb0 : algebraMap S (FractionRing S) b ≠ 0 := by
        refine IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero ?_)
        rintro rfl
        exact hb q.asIdeal.zero_mem
      change fieldEquiv j _ = g
      rw [map_mul, map_inv₀, fieldEquiv_fnOf, fieldEquiv_fnOf]
      simp only [a', b', RingEquiv.apply_symm_apply]
      rw [← e, mul_inv_cancel_right₀ hb0]

theorem exists_fieldEquiv (S : Type) [CommRing S] [IsDomain S] [Algebra ℂ S] (Y : Scheme.{0})
    [IsIntegral Y] (p : Y ⟶ Sp ℂ) (j : Sp S ⟶ Y) [IsOpenImmersion j]
    (hjp : j ≫ p = spMap (algebraMap ℂ S)) :
    ∃ e : Y.functionField ≃+* FractionRing S,
      (∀ a : ℂ, e (GlobalTheory.Cartier.constFn p a) = algebraMap ℂ (FractionRing S) a) ∧
      ∀ (q : PrimeSpectrum S) (g : FractionRing S), g ∈ (locRing (j.base q)).map e.toRingHom ↔
        ∃ a b : S, b ∉ q.asIdeal ∧
          g * algebraMap S (FractionRing S) b = algebraMap S (FractionRing S) a :=
  ⟨fieldEquiv j, fieldEquiv_constFn j p hjp, mem_map_locRing j⟩

end GlobalTheory.OpenSpecField
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctionFieldEquivOpenImmersionSpecStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_functionFieldEquiv_openImmersionSpec : ∀ (S : Type) [CommRing S] [IsDomain S] [Algebra ℂ S] (Y : Scheme.{0}) [IsIntegral Y]
    (p : Y ⟶ Sp ℂ) (j : Sp S ⟶ Y) [IsOpenImmersion j], j ≫ p = spMap (algebraMap ℂ S) →
    ∃ e : Y.functionField ≃+* FractionRing S,
      (∀ a : ℂ, e (GlobalTheory.Cartier.constFn p a) = algebraMap ℂ (FractionRing S) a) ∧
      ∀ (q : PrimeSpectrum S) (g : FractionRing S), g ∈ (locRing (j.base q)).map e.toRingHom ↔
        ∃ a b : S, b ∉ q.asIdeal ∧ g * algebraMap S (FractionRing S) b = algebraMap S (FractionRing S) a := by
  first | exact @GlobalTheory.OpenSpecField.exists_fieldEquiv | exact GlobalTheory.OpenSpecField.exists_fieldEquiv | (intros; apply GlobalTheory.OpenSpecField.exists_fieldEquiv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjectiveVarietyOfIsLocalRingOfVarietyPoi

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LocModelProj


open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw in
theorem exists_projective_openImmersion (S : Type) [CommRing S] [IsDomain S] [Algebra ℂ S] [Algebra.FiniteType ℂ S] :
    ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (p : Y ⟶ Sp ℂ) (j : Sp S ⟶ Y),
      IsProjOver p ∧ IsOpenImmersion j ∧ LocallyOfFiniteType p ∧ j ≫ p = spMap (algebraMap ℂ S) := by
  have : LocallyOfFiniteType (spMap (algebraMap ℂ S)) :=
    HasRingHomProperty.Spec_iff.2 (RingHom.finiteType_algebraMap.2 inferInstance)
  obtain ⟨N, i, _, _, e⟩ := (isAmpleLB_of_isAffine (LB.isLB_triv (Sp S))).isQProjOver (spMap (algebraMap ℂ S))
  have := isProper_str ℂ N
  exact ⟨i.image, isIntegral_image i, i.imageι ≫ PSpace.str ℂ N, i.toImage, ⟨N, i.imageι, inferInstance, rfl⟩,
    inferInstance, inferInstance, by rw [i.toImage_imageι_assoc, e]⟩

theorem topologicalKrullDim_eq_of_openImmersion (S : Type) [CommRing S] [IsDomain S] [Algebra ℂ S] [Algebra.FiniteType ℂ S] (Y : Scheme.{0}) [IsIntegral Y]
    (p : Y ⟶ Sp ℂ) [LocallyOfFiniteType p] (j : Sp S ⟶ Y) [IsOpenImmersion j] (n : ℕ) (h : Algebra.trdeg ℂ S = n) :
    topologicalKrullDim Y = n := by
  have : Nonempty (Sp S) := inferInstance
  rw [← GlobalTheory.OpenImmDim.topologicalKrullDim_eq_of_isOpenImmersion ℂ Y (Sp S) p j]
  change topologicalKrullDim (PrimeSpectrum S) = _
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, GlobalTheory.ringKrullDim_eq_of_trdeg_eq ℂ S h]

theorem exists_projective_of_isLocModel : ∀ (L : Type) [Field L] (c : ℂ →+* L) (R : Subring L) (n : ℕ) (x : Fin n → L), IsLocModel c R → TrBasis c x →
  ∃ (Y : AlgebraicGeometry.Scheme.{0}) (_ : AlgebraicGeometry.IsIntegral Y) (p : Y ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ) (e : Y.functionField ≃+* L) (y : Y),
    IsProjOver p ∧ topologicalKrullDim Y = n ∧ (∀ a, e (GlobalTheory.Cartier.constFn p a) = c a) ∧ (locRing y).map e.toRingHom = R := by
  intro L _ c R n x hR hx
  obtain ⟨S, hS, q, hq, hft, hfrac, hmem⟩ := GlobalTheory.T.exists_finiteType_localization_same_fractionField L c R hR
  letI : Algebra ℂ S := (c.codRestrict S hS).toAlgebra
  letI : Algebra S L := S.subtype.toAlgebra
  letI : Algebra ℂ L := c.toAlgebra
  haveI : IsScalarTower ℂ S L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.FiniteType ℂ S := hft
  haveI : FaithfulSMul S L := (faithfulSMul_iff_algebraMap_injective _ _).2 Subtype.val_injective
  haveI : IsFractionRing S L := by
    refine IsFractionRing.of_field S L fun f => ?_
    obtain ⟨a, ha, b, hb, hb0, e⟩ := hfrac f
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_⟩
    change f = a / b
    rw [← e, mul_div_cancel_right₀ _ hb0]
  have htr : Algebra.trdeg ℂ S = n := by
    have h2 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hx
    have : Algebra.IsAlgebraic S L := IsLocalization.isAlgebraic L (nonZeroDivisors S)
    rw [← trdeg_add_eq ℂ S (A := L), trdeg_eq_zero (R := S) (A := L), add_zero] at h2
    rw [← h2, Cardinal.mk_fin]
  obtain ⟨Y, hY, p, j, hproj, hj, hlft, hjp⟩ := exists_projective_openImmersion S
  obtain ⟨e, hc, hloc⟩ := GlobalTheory.T.exists_functionFieldEquiv_openImmersionSpec S Y p j hjp
  let e2 : FractionRing S ≃ₐ[S] L := IsLocalization.algEquiv (nonZeroDivisors S) (FractionRing S) L
  refine ⟨Y, hY, p, e.trans e2.toRingEquiv, j.base ⟨q, hq⟩, hproj, topologicalKrullDim_eq_of_openImmersion S Y p j n htr, fun a => ?_, ?_⟩
  · change e2 (e (GlobalTheory.Cartier.constFn p a)) = c a
    rw [hc, IsScalarTower.algebraMap_apply ℂ S (FractionRing S), AlgEquiv.commutes]
    rfl
  · ext g
    have h1 : g ∈ (locRing (j.base ⟨q, hq⟩)).map (e.trans e2.toRingEquiv).toRingHom ↔
        e2.symm g ∈ (locRing (j.base ⟨q, hq⟩)).map e.toRingHom := by
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨u, hu, by simp⟩
      · rintro ⟨u, hu, hu'⟩
        refine ⟨u, hu, ?_⟩
        change e2 (e u) = g
        rw [show e u = e2.symm g from hu', AlgEquiv.apply_symm_apply]
    rw [h1, hloc ⟨q, hq⟩, hmem g]
    refine exists₂_congr fun a b => and_congr_right fun _ => ?_
    constructor
    · intro h
      have := congrArg e2 h
      rwa [map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.commutes, AlgEquiv.commutes] at this
    · intro h
      apply e2.injective
      rw [map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.commutes, AlgEquiv.commutes]
      exact h

end GlobalTheory.LocModelProj
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjectiveVarietyOfIsLocalRingOfVarietyPoiStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_projectiveVariety_of_isLocalRingOfVarietyPoint : ∀ (L : Type) [Field L] (c : ℂ →+* L) (R : Subring L) (n : ℕ) (x : Fin n → L), IsLocModel c R → TrBasis c x →
  ∃ (Y : AlgebraicGeometry.Scheme.{0}) (_ : AlgebraicGeometry.IsIntegral Y) (p : Y ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ) (e : Y.functionField ≃+* L) (y : Y),
    IsProjOver p ∧ topologicalKrullDim Y = n ∧ (∀ a, e (GlobalTheory.Cartier.constFn p a) = c a) ∧ (locRing y).map e.toRingHom = R := by
  first | exact @GlobalTheory.LocModelProj.exists_projective_of_isLocModel | exact GlobalTheory.LocModelProj.exists_projective_of_isLocModel | (intros; apply GlobalTheory.LocModelProj.exists_projective_of_isLocModel <;> assumption)
end
end
