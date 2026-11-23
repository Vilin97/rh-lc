module

public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsNonzeroLocusEqAffineOpenLocallyFactorial
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsPowMulMemRangeOfLocalDenominators
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
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.WChartsB
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsHasProjectiveDimensionLEOfResidueField
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsPrincipalMapAwayOfHasProjectiveDimensionLE
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfIsDiscreteValuationRing
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfSmooth
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.UniqueFactorizationMonoidOfIsRegularRingOfIsLoca
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonvanishingLocusPullbackAndVanishIntoLocus

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffCartierComapOfLocal

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FactorialLocus

open ReciprocityTheory.AnForm.R

theorem exists_affine_gen {X : Scheme.{0}} [IsLocallyNoetherian X] (G : X.IdealSheafData) (x : X)
    (t : X.presheaf.stalk x) (htnzd : t ∈ nonZeroDivisors (X.presheaf.stalk x))
    (ht : FinalTheorems.stalkId G x = Ideal.span {t}) :
    ∃ (U : X.affineOpens) (f : Γ(X, U.1)), x ∈ U.1 ∧ f ∈ nonZeroDivisors Γ(X, U.1) ∧
      G.ideal U = Ideal.span {f} := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let U' : X.affineOpens := ⟨U, hU⟩
  have hx : x ∈ U'.1 := hxU
  rw [ds_stalkId_eq_map G U' x hx] at ht
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U'
  letI : Algebra Γ(X, U) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  haveI := hU.isLocalization_stalk ⟨x, hx⟩
  have halg : algebraMap Γ(X, U) (X.presheaf.stalk x) = (X.presheaf.germ U x hx).hom := rfl
  rw [Ideal.map] at ht
  obtain ⟨y, ⟨a, haI, rfl⟩, c, hc⟩ := ds_gen_of_span _ t htnzd ht
  have hmap : (G.ideal U').map (algebraMap Γ(X, U) (X.presheaf.stalk x)) =
      Ideal.span {algebraMap Γ(X, U) (X.presheaf.stalk x) a} := by
    rw [halg, Ideal.map, ht, hc, Ideal.span_singleton_mul_left_unit c.isUnit]
  have hnzd : algebraMap Γ(X, U) (X.presheaf.stalk x) a ∈ nonZeroDivisors (X.presheaf.stalk x) := by
    rw [halg, hc]
    exact mul_mem (IsUnit.mem_nonZeroDivisors c.isUnit) htnzd
  obtain ⟨σ, hσP, hT⟩ := ds_spread (hU.primeIdealOf ⟨x, hx⟩).asIdeal (G.ideal U') a haI hmap hnzd
  haveI := hU.isLocalization_basicOpen σ
  obtain ⟨h1, h2⟩ := hT Γ(X, X.basicOpen σ)
  refine ⟨X.affineBasicOpen (U := U') σ, algebraMap Γ(X, U) Γ(X, X.basicOpen σ) a, ?_, h2, ?_⟩
  · show x ∈ X.basicOpen σ
    rw [X.mem_basicOpen σ x hx]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal σ).2 hσP
  · rw [← G.map_ideal_basicOpen U' σ]
    exact h1

theorem stalkId_eq_span_of_mem {X : Scheme.{0}} (G : X.IdealSheafData) (U : X.affineOpens)
    (f : Γ(X, U.1)) (hf : f ∈ nonZeroDivisors Γ(X, U.1)) (hG : G.ideal U = Ideal.span {f})
    (y : X) (hy : y ∈ U.1) :
    ∃ t ∈ nonZeroDivisors (X.presheaf.stalk y), FinalTheorems.stalkId G y = Ideal.span {t} := by
  refine ⟨X.presheaf.germ U.1 y hy f, ?_, ?_⟩
  · letI : Algebra Γ(X, U.1) (X.presheaf.stalk y) := X.presheaf.algebra_section_stalk ⟨y, hy⟩
    haveI := U.2.isLocalization_stalk ⟨y, hy⟩
    exact algebraMap_mem_nonZeroDivisors_of_isLocalization
      (U.2.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl hf
  · rw [ds_stalkId_eq_map G U y hy, hG, Ideal.map_span, Set.image_singleton]

theorem effCartier_comap_of_local {X Y : Scheme.{0}} (I : Y.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f]
    (hI : ∀ x : X, ∃ (U : Y.affineOpens) (h : Γ(Y, U.1)), f x ∈ U.1 ∧
      h ∈ nonZeroDivisors Γ(Y, U.1) ∧ I.ideal U = Ideal.span {h}) :
    FinalTheorems.EffCartier (I.comap f) := by
  intro x
  obtain ⟨U, h, hxU, hh, hU⟩ := hI x
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

theorem exists_isLocus : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [X.IsSeparated] (V : X.Opens), IsAffineOpen V → (V : Set X).Nonempty → ∃ W : X.Opens, V ≤ W ∧ (∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) → x ∈ W) ∧ ∃ c : Pic W.toScheme, IsLocus c (W.ι ⁻¹ᵁ V) := by
  intro X _ _ _ V hV hne
  have hι : IsAffineHom V.ι :=
    haveI : IsAffine V := hV
    haveI : IsAffineHom (V.ι ≫ terminal.from X) := inferInstance
    IsAffineHom.of_comp _ (terminal.from X)
  let G := Scheme.IdealSheafData.vanishingIdeal V.compl
  let P : X → Prop := fun x =>
    ∃ t ∈ nonZeroDivisors (X.presheaf.stalk x), FinalTheorems.stalkId G x = Ideal.span {t}
  have hopen : IsOpen {x | P x} := by
    refine isOpen_iff_forall_mem_open.2 fun x hx => ?_
    obtain ⟨t, ht, htG⟩ := hx
    obtain ⟨U, f, hxU, hf, hG⟩ := exists_affine_gen G x t ht htG
    exact ⟨U.1, fun y hy => stalkId_eq_span_of_mem G U f hf hG y hy, U.1.isOpen, hxU⟩
  let W : X.Opens := ⟨{x | P x}, hopen⟩
  have hVW : V ≤ W := by
    intro x hx
    refine ⟨1, one_mem _, ?_⟩
    have h : ∀ q : PrimeSpectrum (X.presheaf.stalk x),
        X.fromSpecStalk x q ∈ V ↔ (1 : X.presheaf.stalk x) ∉ q.asIdeal := fun q => by
      refine iff_of_true ?_ fun h1 => q.2.ne_top ((Ideal.eq_top_iff_one _).2 h1)
      have hs : X.fromSpecStalk x q ∈ Set.range (X.fromSpecStalk x) := ⟨q, rfl⟩
      rw [Scheme.range_fromSpecStalk] at hs
      exact Specializes.mem_open hs V.isOpen hx
    rw [GlobalTheory.AffineComplement.stalkId_vanishingIdeal_compl V x 1 h, Ideal.span_singleton_one,
      Ideal.radical_top]
  have hfac : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) → x ∈ W := by
    intro x hufd
    have hd : IsDomain (X.presheaf.stalk x) := inferInstance
    have hn : IsNoetherianRing (X.presheaf.stalk x) := inferInstance
    have hA : IsAffineOpen (X.fromSpecStalk x ⁻¹ᵁ V) := by
      have : IsAffineHom (X.fromSpecStalk x ⁻¹ᵁ V).ι :=
        MorphismProperty.of_isPullback (P := @IsAffineHom)
          (isPullback_morphismRestrict (X.fromSpecStalk x) V) hι
      exact isAffine_of_isAffineHom (X.fromSpecStalk x ⁻¹ᵁ V).ι
    have hg : genericPoint X ∈ Set.range (X.fromSpecStalk x) := by
      rw [Scheme.range_fromSpecStalk]
      exact (genericPoint_spec X).specializes trivial
    obtain ⟨q, hq⟩ := hg
    have hqV : q ∈ X.fromSpecStalk x ⁻¹ᵁ V := by
      change X.fromSpecStalk x q ∈ V
      rw [hq]
      exact ((genericPoint_spec X).mem_open_set_iff V.isOpen).2 (by simpa using hne)
    obtain ⟨a, ha⟩ := @GlobalTheory.exists_eq_basicOpen_of_isAffineOpen_of_uniqueFactorization
      (X.presheaf.stalk x) (X.presheaf.stalk x).commRing hd hn hufd
      (X.fromSpecStalk x ⁻¹ᵁ V) hA ⟨q, hqV⟩
    have h : ∀ q : PrimeSpectrum (X.presheaf.stalk x),
        X.fromSpecStalk x q ∈ V ↔ a ∉ q.asIdeal := fun q =>
      iff_of_eq (congrArg (fun V => q ∈ V) ha)
    have ha0 : a ≠ 0 := fun h0 => (h q).1 hqV (h0 ▸ zero_mem _)
    show P x
    simp only [P, G]
    rw [GlobalTheory.AffineComplement.stalkId_vanishingIdeal_compl V x a h]
    exact GlobalTheory.AffineComplement.exists_radical_span_singleton_eq ha0
  refine ⟨W, hVW, hfac, ?_⟩
  have hE : FinalTheorems.EffCartier (G.comap W.ι) := by
    refine effCartier_comap_of_local G W.ι fun y => ?_
    have hy : P (W.ι y) := y.2
    obtain ⟨t, ht, htG⟩ := hy
    exact exists_affine_gen G _ t ht htG
  obtain ⟨D, hD⟩ := EffCartierData.exists_idealSheaf_eq hE
  refine ⟨cls D.lb D.isLB_lb, D.lb, D.isLB_lb, D.canonical, rfl, TopologicalSpace.Opens.ext ?_⟩
  refine D.coe_nonzeroLocus_canonical.trans ?_
  rw [hD, Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]
  ext y
  simp

end GlobalTheory.FactorialLocus
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffinePreimageLe

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Tube

theorem exists_affine_preimage_le :
    ∀ (X S : Scheme.{0}) (f : X ⟶ S) [UniversallyClosed f] (s : S) (W : X.Opens), (∀ x, f x = s → x ∈ W) → ∃ U : S.Opens, IsAffineOpen U ∧ s ∈ U ∧ f ⁻¹ᵁ U ≤ W := by
  intro X S f _ s W hW
  have hc : IsClosed (f '' (W : Set X)ᶜ) := f.isClosedMap _ W.isOpen.isClosed_compl
  have hs : s ∈ (f '' (W : Set X)ᶜ)ᶜ := by
    rintro ⟨x, hx, rfl⟩
    exact hx (hW x rfl)
  obtain ⟨U, hU, hsU, hUV⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens)
    (show s ∈ (⟨_, hc.isOpen_compl⟩ : S.Opens) from hs)
  refine ⟨U, hU, hsU, fun x hx => ?_⟩
  by_contra hxW
  exact hUV hx ⟨x, hxW, rfl⟩

end GlobalTheory.Tube
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularRingLocalizationOfComapEqBot

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenericFibreFactorial

theorem isRegularRing_localization_of_comap_eq_bot (R A : Type) [CommRing R] [IsDomain R]
    [CommRing A] [Algebra R A] [Algebra.Smooth R A] (p : Ideal A) [p.IsPrime]
    (hp : p.comap (algebraMap R A) = ⊥) : IsRegularRing (Localization.AtPrime p) := by
  let K := FractionRing R
  let M := Algebra.algebraMapSubmonoid A (nonZeroDivisors R)
  let B := Localization M
  letI : Algebra K B := localizationAlgebra (nonZeroDivisors R) A
  haveI : IsScalarTower R K B := inferInstance
  haveI h1 : Algebra.IsPushout R A K B :=
    Algebra.isPushout_of_isLocalization (nonZeroDivisors R) K A B
  haveI : Algebra.IsPushout R K A B := h1.symm
  haveI : Algebra.Smooth K B := Algebra.Smooth.of_equiv (Algebra.IsPushout.equiv (R := R) (S := K) (R' := A) (S' := B))
  haveI : IsRegularRing B := GlobalTheory.isRegularRing_of_smooth K B
  have disj : Disjoint (M : Set A) (p : Set A) := by
    rw [Set.disjoint_left]
    rintro _ ⟨r, hr, rfl⟩ hrp
    have : r ∈ p.comap (algebraMap R A) := hrp
    rw [hp, Ideal.mem_bot] at this
    exact nonZeroDivisors.ne_zero hr this
  let q := p.map (algebraMap A B)
  haveI : q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M B p inferInstance disj
  haveI : IsLocalization.AtPrime (Localization.AtPrime q) p := by
    convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
      (Localization.AtPrime q) q
    exact (IsLocalization.under_map_of_isPrime_disjoint M B inferInstance disj).symm
  haveI : IsRegularRing (Localization.AtPrime q) :=
    GlobalTheory.ExtendRig.isRegularRing_of_isLocalization q.primeCompl _
  exact IsRegularRing.of_ringEquiv (IsLocalization.algEquiv p.primeCompl
    (Localization.AtPrime q) (Localization.AtPrime p)).toRingEquiv

theorem ufd_stalk_of_generic : ∀ (R : Type) [CommRing R] [IsDomain R] (X : Scheme.{0}) [IsIntegral X]
    (f : X ⟶ Sp R) [Smooth f] (x : X), (show PrimeSpectrum R from f x).asIdeal = ⊥ →
    UniqueFactorizationMonoid (X.presheaf.stalk x) := by
  intro R _ _ X _ f _ x hx
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hs : (f.appLE ⊤ U le_top).hom.Smooth :=
    HasRingHomProperty.appLE @Smooth f inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  haveI : Nonempty (⊤ : (Sp R).Opens) := ⟨⟨f x, trivial⟩⟩
  haveI : IsDomain Γ(Sp R, ⊤) := inferInstance
  have hgen : f x = genericPoint (Sp R) := by
    rw [genericPoint_eq_bot_of_affine]
    exact PrimeSpectrum.ext hx
  have h1 := IsAffineOpen.comap_primeIdealOf_appLE (f := f) ⊤ (isAffineOpen_top _) U hU le_top hxU
  have h2 : (isAffineOpen_top (Sp R)).primeIdealOf ⟨f x, (show f x ∈ (⊤ : (Sp R).Opens) from trivial)⟩ =
      genericPoint (Spec Γ(Sp R, ⊤)) := by
    rw [← (isAffineOpen_top (Sp R)).primeIdealOf_genericPoint]
    congr 1
    exact Subtype.ext hgen
  rw [h2, genericPoint_eq_bot_of_affine] at h1
  have hcomap : (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.comap (f.appLE ⊤ U le_top).hom = ⊥ :=
    congrArg PrimeSpectrum.asIdeal h1
  algebraize [(f.appLE ⊤ U le_top).hom]
  have hreg := isRegularRing_localization_of_comap_eq_bot Γ(Sp R, ⊤) Γ(X, U)
    (hU.primeIdealOf ⟨x, hxU⟩).asIdeal hcomap
  let := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  haveI : IsRegularRing (X.presheaf.stalk x) :=
    IsRegularRing.of_ringEquiv (IsLocalization.algEquiv (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
      (Localization.AtPrime (hU.primeIdealOf ⟨x, hxU⟩).asIdeal) (X.presheaf.stalk x)).toRingEquiv
  exact GlobalTheory.uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing
    GlobalTheory.exists_hasProjectiveDimensionLE_of_isRegularLocalRing
    GlobalTheory.isPrincipal_map_away_of_hasProjectiveDimensionLE _

end GlobalTheory.GenericFibreFactorial
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierLocusOverDenseOpenBase

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.DivStart

theorem exists_locus_over_dense_open : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsDomain R] [IsIntegrallyClosed R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ V : A.left.Opens, IsAffineOpen V → (∀ s : Sp R, ∃ x ∈ V, A.hom x = s) → ∃ (U : (Sp R).Opens) (c : Pic (A.hom ⁻¹ᵁ U ⊔ V).toScheme), (U : Set (Sp R)).Nonempty ∧ IsLocus c ((A.hom ⁻¹ᵁ U ⊔ V).ι ⁻¹ᵁ V) := by
  intro R _ _ _ _ A _ hA V hV hsurj
  have := hA.smooth
  have := hA.proper
  have : GeometricallyIntegral A.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hA.smooth hA.geomConnected
  have : IsLocallyNoetherian (Sp R) := inferInstance
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian A.hom
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have : A.left.IsSeparated := ⟨by rw [← terminal.comp_from A.hom]; infer_instance⟩
  let s₀ : Sp R := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)
  obtain ⟨x₀, hx₀, -⟩ := hsurj s₀
  obtain ⟨W₀, hVW, hufd, c₀, hc₀⟩ := GlobalTheory.FactorialLocus.exists_isLocus A.left V hV ⟨x₀, hx₀⟩
  have hfib : ∀ x, A.hom x = s₀ → x ∈ W₀ := fun x hx =>
    hufd x (GlobalTheory.GenericFibreFactorial.ufd_stalk_of_generic R A.left A.hom x (by rw [hx]))
  obtain ⟨U, -, hsU, hUW⟩ := GlobalTheory.Tube.exists_affine_preimage_le A.left (Sp R) A.hom s₀ W₀ hfib
  have hle : A.hom ⁻¹ᵁ U ⊔ V ≤ W₀ := sup_le hUW hVW
  refine ⟨U, GlobalTheory.CechPic.pull (A.left.homOfLE hle) c₀, ⟨s₀, hsU⟩, ?_⟩
  have h := GlobalTheory.LocusPull.isLocus_pull (A.left.homOfLE hle) hc₀
  convert h using 1
  ext x
  change (A.hom ⁻¹ᵁ U ⊔ V).ι x ∈ V ↔ W₀.ι (A.left.homOfLE hle x) ∈ V
  rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]

end GlobalTheory.DivStart
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierLocusOverDenseOpenBaseStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_cartier_locus_over_dense_open_base : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsDomain R] [IsIntegrallyClosed R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ V : A.left.Opens, IsAffineOpen V → (∀ s : Sp R, ∃ x ∈ V, A.hom x = s) → ∃ (U : (Sp R).Opens) (c : Pic (A.hom ⁻¹ᵁ U ⊔ V).toScheme), (U : Set (Sp R)).Nonempty ∧ IsLocus c ((A.hom ⁻¹ᵁ U ⊔ V).ι ⁻¹ᵁ V) := by
  first | exact @GlobalTheory.DivStart.exists_locus_over_dense_open | exact GlobalTheory.DivStart.exists_locus_over_dense_open | (intros; apply GlobalTheory.DivStart.exists_locus_over_dense_open <;> assumption)
end
end
