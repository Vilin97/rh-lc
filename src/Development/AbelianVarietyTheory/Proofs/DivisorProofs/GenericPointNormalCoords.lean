module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMaximalIdealEqOrigin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodIffEtaleAt
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMaximalIdealEqOrigin
public import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Smooth.IntegralClosure
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureFiniteEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
public import Mathlib.RingTheory.Flat.TorsionFree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosureBaseChangeMapsAndRetractionStatement
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.RingTheory.Smooth.IntegralClosure
import Mathlib.RingTheory.TotallySplit

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleAtPrimeBaseChangeOfIntegralClosureEtale

section

@[expose] public section

open IsLocalRing Polynomial
open scoped TensorProduct
open GlobalTheory.LocAcyc GlobalTheory.KeyOriginNoeth GlobalTheory.KeyOriginBC

noncomputable section

namespace GlobalTheory.KeyOriginEnlarge

theorem closureEtaleAt_comap_baseChange_atPrime : ∀ (A R R₁ DA : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing R₁]
    [CommRing DA] [Algebra (GenFib A R) DA] (κ : R →+* R₁) (P₁ : Ideal R₁) [P₁.IsPrime],
    GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A R DA (P₁.comap κ) →
    letI := closureAlg A R DA
    letI : Algebra R (Localization.AtPrime P₁) :=
      ((algebraMap R₁ (Localization.AtPrime P₁)).comp κ).toAlgebra
    Algebra.Etale (Localization.AtPrime P₁) (Localization.AtPrime P₁ ⊗[R] closure A R DA) := by
  intro A R R₁ DA _ _ _ _ _ _ κ P₁ _ h
  letI := closureAlg A R DA
  letI iRS : Algebra R (Localization.AtPrime P₁) :=
    ((algebraMap R₁ (Localization.AtPrime P₁)).comp κ).toAlgebra
  have hunit : ∀ y : (P₁.comap κ).primeCompl,
      IsUnit (algebraMap R (Localization.AtPrime P₁) y) := by
    intro y
    exact IsLocalization.map_units (Localization.AtPrime P₁)
      (⟨κ y, y.2⟩ : P₁.primeCompl)
  letI : Algebra (Localization.AtPrime (P₁.comap κ)) (Localization.AtPrime P₁) :=
    (IsLocalization.lift (M := (P₁.comap κ).primeCompl) hunit).toAlgebra
  haveI : IsScalarTower R (Localization.AtPrime (P₁.comap κ)) (Localization.AtPrime P₁) :=
    IsScalarTower.of_algebraMap_eq (fun x =>
      (IsLocalization.lift_eq (M := (P₁.comap κ).primeCompl) hunit x).symm)
  haveI : Algebra.Etale (Localization.AtPrime (P₁.comap κ))
      (Localization.AtPrime (P₁.comap κ) ⊗[R] closure A R DA) := h
  haveI : Algebra.Etale (Localization.AtPrime P₁) (Localization.AtPrime P₁ ⊗[Localization.AtPrime (P₁.comap κ)]
      (Localization.AtPrime (P₁.comap κ) ⊗[R] closure A R DA)) :=
    Algebra.Etale.baseChange _ _ _
  exact Algebra.Etale.of_equiv
    (Algebra.TensorProduct.cancelBaseChange R (Localization.AtPrime (P₁.comap κ))
      (Localization.AtPrime P₁) (Localization.AtPrime P₁) (closure A R DA))

end GlobalTheory.KeyOriginEnlarge
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleAtPrimeBaseChangeOfIntegralClosureEtaleStatement

section

@[expose] public section

open IsLocalRing Polynomial
open scoped TensorProduct
open GlobalTheory.LocAcyc GlobalTheory.KeyOriginNoeth GlobalTheory.KeyOriginBC

theorem _root_.GlobalTheory.T.etale_atPrime_baseChange_of_integralClosureEtale : ∀ (A R R₁ DA : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing R₁]
    [CommRing DA] [Algebra (GenFib A R) DA] (κ : R →+* R₁) (P₁ : Ideal R₁) [P₁.IsPrime],
    GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A R DA (P₁.comap κ) →
    letI := closureAlg A R DA
    letI : Algebra R (Localization.AtPrime P₁) :=
      ((algebraMap R₁ (Localization.AtPrime P₁)).comp κ).toAlgebra
    Algebra.Etale (Localization.AtPrime P₁) (Localization.AtPrime P₁ ⊗[R] closure A R DA) :=
  @GlobalTheory.KeyOriginEnlarge.closureEtaleAt_comap_baseChange_atPrime
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleIntegrallyClosedInLocalization

section

@[expose] public section

open IsLocalRing Polynomial
open scoped TensorProduct
open GlobalTheory.LocAcyc GlobalTheory.KeyOriginNoeth GlobalTheory.KeyOriginBC

namespace GlobalTheory.EtaleNormalLoc

theorem isIntegrallyClosedIn_localization (S : Type) [CommRing S] [IsDomain S]
    [IsIntegrallyClosed S] (M : Submonoid S) (hM : M ≤ nonZeroDivisors S) :
    IsIntegrallyClosedIn S (Localization M) := by
  let K := FractionRing S
  letI : Algebra (Localization M) K :=
    IsLocalization.localizationAlgebraOfSubmonoidLe (Localization M) K M _ hM
  haveI : IsScalarTower S (Localization M) K :=
    IsLocalization.localization_isScalarTower_of_submonoid_le (Localization M) K M _ hM
  haveI : IsFractionRing (Localization M) K :=
    IsFractionRing.isFractionRing_of_isLocalization M (Localization M) K hM
  haveI : IsDomain (Localization M) := IsLocalization.isDomain_localization hM
  have hK : Function.Injective (algebraMap (Localization M) K) := IsFractionRing.injective _ _
  refine isIntegrallyClosedIn_iff.mpr ⟨fun x y hxy ↦ ?_, fun {x} hx ↦ ?_⟩
  · apply IsFractionRing.injective S K
    rw [IsScalarTower.algebraMap_apply S (Localization M) K, hxy, ← IsScalarTower.algebraMap_apply]
  · obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (hx.algebraMap (B := K))
    exact ⟨y, hK (by rw [← hy, IsScalarTower.algebraMap_apply S (Localization M) K])⟩

theorem etale_integrallyClosed_localization : ∀ (S E : Type) [CommRing S] [IsDomain S] [IsIntegrallyClosed S]
    [CommRing E] [Algebra S E] [Algebra.Etale S E] (M : Submonoid S), M ≤ nonZeroDivisors S →
    Function.Injective (algebraMap E (Localization (Algebra.algebraMapSubmonoid E M))) ∧
    ∀ x : Localization (Algebra.algebraMapSubmonoid E M), IsIntegral S x →
      x ∈ (algebraMap E (Localization (Algebra.algebraMapSubmonoid E M))).range := by
  intro S E _ _ _ _ _ _ M hM
  have hle : Algebra.algebraMapSubmonoid E M ≤ nonZeroDivisors E := by
    rintro _ ⟨m, hm, rfl⟩
    have hreg : IsSMulRegular E m := Module.Flat.isSMulRegular_of_nonZeroDivisors (hM hm)
    refine mem_nonZeroDivisors_iff.mpr ⟨fun x hx ↦ hreg ?_, fun x hx ↦ hreg ?_⟩
    · show m • x = m • (0 : E)
      rw [smul_zero, Algebra.smul_def]
      exact hx
    · show m • x = m • (0 : E)
      rw [smul_zero, Algebra.smul_def, mul_comm]
      exact hx
  refine ⟨IsLocalization.injective _ hle, fun x hx ↦ ?_⟩
  let SM := Localization M
  let T := E ⊗[S] SM
  letI : Algebra SM T := Algebra.TensorProduct.rightAlgebra
  haveI : IsScalarTower S SM T := inferInstance
  haveI : Algebra.IsPushout S E SM T := inferInstance
  haveI : IsLocalization (Algebra.algebraMapSubmonoid E M) T :=
    (Algebra.isLocalization_iff_isPushout M SM).2 (Algebra.IsPushout.symm inferInstance)
  let e : T ≃ₐ[E] Localization (Algebra.algebraMapSubmonoid E M) :=
    IsLocalization.algEquiv (Algebra.algebraMapSubmonoid E M) T _
  have hic := isIntegrallyClosedIn_localization S M hM
  have htS : IsIntegral S (e.symm x) := hx.map (e.symm.toAlgHom.restrictScalars S)
  have htE : IsIntegral E (e.symm x) := htS.tower_top
  obtain ⟨y, hy⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth
    (R := S) (S := E) (B := SM)).2 ⟨e.symm x, htE⟩
  have hy' : (TensorProduct.toIntegralClosure S E SM y : T) = e.symm x := congrArg Subtype.val hy
  have key : ∀ y : E ⊗[S] integralClosure S SM, ∃ b : E,
      (TensorProduct.toIntegralClosure S E SM y : T) = b ⊗ₜ[S] (1 : SM) := by
    intro y
    induction y with
    | tmul b c =>
      obtain ⟨r, hr⟩ := IsIntegrallyClosedIn.isIntegral_iff.1 c.2
      refine ⟨r • b, ?_⟩
      rw [TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one, hr]
      rfl
    | add u v hu hv =>
      obtain ⟨a, ha⟩ := hu
      obtain ⟨b, hb⟩ := hv
      exact ⟨a + b, by rw [map_add (f := _), Subalgebra.coe_add, ha, hb, TensorProduct.add_tmul]⟩
  obtain ⟨b, hb⟩ := key y
  refine ⟨b, ?_⟩
  have : e.symm x = algebraMap E T b := by
    rw [← hy', hb]; rfl
  rw [← e.apply_symm_apply x, this, AlgEquiv.commutes]

end GlobalTheory.EtaleNormalLoc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleIntegrallyClosedInLocalizationStatement

section

@[expose] public section

open IsLocalRing Polynomial
open scoped TensorProduct
open GlobalTheory.LocAcyc GlobalTheory.KeyOriginNoeth GlobalTheory.KeyOriginBC

theorem _root_.GlobalTheory.T.etale_integrallyClosed_in_localization : ∀ (S E : Type) [CommRing S] [IsDomain S] [IsIntegrallyClosed S]
    [CommRing E] [Algebra S E] [Algebra.Etale S E] (M : Submonoid S), M ≤ nonZeroDivisors S →
    Function.Injective (algebraMap E (Localization (Algebra.algebraMapSubmonoid E M))) ∧
    ∀ x : Localization (Algebra.algebraMapSubmonoid E M), IsIntegral S x →
      x ∈ (algebraMap E (Localization (Algebra.algebraMapSubmonoid E M))).range := by
  first | (exact @GlobalTheory.EtaleNormalLoc.etale_integrallyClosed_localization) | (exact GlobalTheory.EtaleNormalLoc.etale_integrallyClosed_localization) | (intros; apply GlobalTheory.EtaleNormalLoc.etale_integrallyClosed_localization <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointNormalCoords

section

@[expose] public section

open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.KeyOriginBCEt

open GlobalTheory.LocAcyc GlobalTheory.KeyOriginNoeth GlobalTheory.KeyOriginBC

theorem closureEtaleAt_bc : ∀ (A R A₁ R₁ : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R]
    [CommRing A₁] [IsDomain A₁] [CommRing R₁] [IsDomain R₁] [IsIntegrallyClosed R₁] [Algebra A₁ R₁]
    (f : A →+* A₁), Function.Injective f → Function.Injective (algebraMap A₁ R₁) →
    ∀ (κ : R →+* R₁), κ.comp (algebraMap A R) = (algebraMap A₁ R₁).comp f →
    ∀ (β : GenFib A R →+* GenFib A₁ R₁),
    β.comp (algebraMap R (GenFib A R)) = (algebraMap R₁ (GenFib A₁ R₁)).comp κ →
    ∀ (DA : Type) [CommRing DA] [Algebra (GenFib A R) DA] [Algebra.IsIntegral (GenFib A R) DA]
    (P₁ : Ideal R₁) [P₁.IsPrime],
    GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A R DA (P₁.comap κ) →
    GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A₁ R₁ (BC β DA) P₁ := by
  intro A R A₁ R₁ _ _ _ _ _ _ _ _ _ _ f hf hA₁ κ hκ β hβ DA _ _ _ P₁ _ hP
  letI := closureAlg A R DA
  letI : Algebra R (Localization.AtPrime P₁) :=
    ((algebraMap R₁ (Localization.AtPrime P₁)).comp κ).toAlgebra
  letI : Algebra R₁ (BC β DA) := (baseHom A₁ R₁ (BC β DA)).toAlgebra
  haveI hE : Algebra.Etale (Localization.AtPrime P₁) (Localization.AtPrime P₁ ⊗[R] closure A R DA) :=
    GlobalTheory.T.etale_atPrime_baseChange_of_integralClosureEtale A R R₁ DA κ P₁ hP
  haveI : IsDomain (Localization.AtPrime P₁) :=
    IsLocalization.isDomain_localization P₁.primeCompl_le_nonZeroDivisors
  haveI : IsIntegrallyClosed (Localization.AtPrime P₁) :=
    isIntegrallyClosed_of_isLocalization _ P₁.primeCompl P₁.primeCompl_le_nonZeroDivisors
  have hinjS : Function.Injective (algebraMap R₁ (Localization.AtPrime P₁)) :=
    IsLocalization.injective _ P₁.primeCompl_le_nonZeroDivisors
  have hM : (nonZeroDivisors A₁).map ((algebraMap R₁ (Localization.AtPrime P₁)).comp (algebraMap A₁ R₁))
      ≤ nonZeroDivisors (Localization.AtPrime P₁) := by
    rintro _ ⟨a, ha, rfl⟩
    apply mem_nonZeroDivisors_of_ne_zero
    intro h
    have h1 : algebraMap A₁ R₁ a = 0 := hinjS (by simpa using h)
    exact nonZeroDivisors.ne_zero ha (hA₁ (by simpa using h1))
  obtain ⟨hinj, hint⟩ := GlobalTheory.T.etale_integrallyClosed_in_localization (Localization.AtPrime P₁)
    (Localization.AtPrime P₁ ⊗[R] closure A R DA) _ hM
  obtain ⟨φ, ψ, hψφ, hunit, hsurj⟩ := GlobalTheory.T.exists_closureBaseChange_maps_and_retraction A R A₁ R₁ f hf κ hκ β hβ DA (Localization.AtPrime P₁)
  have hψφ' : ∀ e, ψ (φ e) = algebraMap _ _ e := fun e => by
    rw [← AlgHom.comp_apply, hψφ]; rfl
  have hφinj : Function.Injective φ := by
    intro x y hxy
    apply hinj
    rw [← hψφ', ← hψφ', hxy]
  have hφint : ∀ x : Localization.AtPrime P₁ ⊗[R₁] BC β DA, IsIntegral (Localization.AtPrime P₁) x →
      x ∈ φ.range := by
    intro x hx
    obtain ⟨e, he⟩ := hint (ψ x) (hx.map ψ)
    obtain ⟨m, hm, e', he'⟩ := hsurj x
    have he'' : φ e' = x * algebraMap _ _ m := he'
    have h2 : e * algebraMap _ _ m = e' := by
      apply hinj
      rw [map_mul, he, ← hψφ' e', he'', map_mul, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
    refine ⟨e, ?_⟩
    show φ e = x
    apply (hunit m hm).mul_right_cancel
    calc φ e * algebraMap _ _ m = φ (e * algebraMap _ _ m) := by rw [map_mul, AlgHom.commutes]
      _ = x * _ := by rw [h2, he'']
  haveI : Algebra.IsIntegral R (closure A R DA) := by
    letI := (baseHom A R DA).toAlgebra
    let ι : closure A R DA →ₐ[R] DA := { (closure A R DA).subtype with commutes' := fun _ => rfl }
    exact ⟨fun x => (isIntegral_algHom_iff ι Subtype.val_injective).1 x.2⟩
  haveI : Algebra.IsIntegral (Localization.AtPrime P₁) (Localization.AtPrime P₁ ⊗[R] closure A R DA) :=
    inferInstance
  let φ' : Localization.AtPrime P₁ ⊗[R] closure A R DA →ₐ[Localization.AtPrime P₁]
      integralClosure (Localization.AtPrime P₁) (Localization.AtPrime P₁ ⊗[R₁] BC β DA) :=
    φ.codRestrict _ (fun e => (Algebra.IsIntegral.isIntegral e).map φ)
  have hφ' : Function.Bijective φ' := by
    refine ⟨fun x y h => hφinj (congrArg Subtype.val h), fun ⟨x, hx⟩ => ?_⟩
    obtain ⟨e, he⟩ := hφint x hx
    exact ⟨e, Subtype.ext he⟩
  haveI : Algebra.Etale (Localization.AtPrime P₁)
      (integralClosure (Localization.AtPrime P₁) (Localization.AtPrime P₁ ⊗[R₁] BC β DA)) :=
    Algebra.Etale.of_equiv (AlgEquiv.ofBijective φ' hφ')
  have hloc := TensorProduct.toIntegralClosure_bijective_of_isLocalization (R := R₁)
    (S := Localization.AtPrime P₁) (B := BC β DA) P₁.primeCompl
  haveI : Algebra.Etale (Localization.AtPrime P₁)
      (Localization.AtPrime P₁ ⊗[R₁] integralClosure R₁ (BC β DA)) :=
    Algebra.Etale.of_equiv (AlgEquiv.ofBijective _ hloc).symm
  unfold GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt
  letI := closureAlg A₁ R₁ (BC β DA)
  let eC : closure A₁ R₁ (BC β DA) ≃ₐ[R₁] integralClosure R₁ (BC β DA) :=
    { toFun := fun x => ⟨x.1, x.2⟩, invFun := fun x => ⟨x.1, x.2⟩, left_inv := fun _ => rfl,
      right_inv := fun _ => rfl, map_mul' := fun _ _ => rfl, map_add' := fun _ _ => rfl,
      commutes' := fun _ => rfl }
  exact Algebra.Etale.of_equiv (Algebra.TensorProduct.congr AlgEquiv.refl eC).symm

theorem closureEtaleAt_baseChange : ∀ (T O : Type) [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O] [Algebra T[X] O]
    [IsScalarTower T T[X] O]
    (A A₁ : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [Algebra.EssFiniteType ℤ A] [CommRing A₁] [IsDomain A₁] [IsLocalRing A₁] [IsNoetherianRing A₁]
    [IsIntegrallyClosed A₁] [Algebra.EssFiniteType ℤ A₁] (f : A →+* A₁) (i : A →+* T)
    (i₁ : A₁ →+* T) (hf : Function.Injective f)
    (EA : Type) [CommRing EA] [Algebra A[X] EA] [Algebra A EA] [IsScalarTower A A[X] EA]
    [Algebra.Etale A[X] EA]
    (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O) (hcomp : i₁.comp f = i)
    (hj : jA.comp (algebraMap A[X] (Localization.AtPrime QA)) =
      (algebraMap T[X] O).comp (Polynomial.mapRingHom i))
    (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA] (q : ℕ)
    (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    0 < q → IsUnit (q : A) →
    GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
    ∀ a : A, a ≠ 0 →
    (∀ (P : Ideal (Localization.AtPrime QA)) [P.IsPrime],
      algebraMap A (Localization.AtPrime QA) a ∉ P →
      GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A (Localization.AtPrime QA) DA P) →
    ∀ (P₁ : Ideal (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj)) [P₁.IsPrime], algebraMap A₁ (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj) (f a) ∉ P₁ →
      GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A₁ (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj) (GlobalTheory.KeyOriginBC.BC (GlobalTheory.KeyOriginBC.fibBC f i i₁ EA QA jA hcomp hj hf) DA) P₁ := by
  intro T O _ _ _ _ _ _ A A₁ _ _ _ _ _ _ _ _ _ _ _ _ f i i₁ hf EA _ _ _ _ _ QA _ jA hcomp hj DA _ _ q actA
    _ _ htors a _ hyp P₁ _ haP₁
  obtain ⟨hd, hn⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_etale (Polynomial A₁)
    (ideal₁ f i i₁ EA QA jA hcomp hj) (Loc₁ f i i₁ EA QA jA hcomp hj)
  haveI := hd
  haveI := hn
  haveI : Module.Flat (Polynomial A₁) (Loc₁ f i i₁ EA QA jA hcomp hj) :=
    Module.Flat.trans (Polynomial A₁) (Ext f EA) (Loc₁ f i i₁ EA QA jA hcomp hj)
  have hA₁ : Function.Injective (algebraMap A₁ (Loc₁ f i i₁ EA QA jA hcomp hj)) := by
    have h1 : Function.Injective (algebraMap (Polynomial A₁) (Loc₁ f i i₁ EA QA jA hcomp hj)) := by

      exact FaithfulSMul.algebraMap_injective (Polynomial A₁) (Loc₁ f i i₁ EA QA jA hcomp hj)
    rw [IsScalarTower.algebraMap_eq A₁ (Polynomial A₁) (Loc₁ f i i₁ EA QA jA hcomp hj)]
    exact h1.comp Polynomial.C_injective
  haveI : Module.Finite (GenFib A (Localization.AtPrime QA)) DA := htors.1
  haveI : Algebra.IsIntegral (GenFib A (Localization.AtPrime QA)) DA := inferInstance
  have hκ : (locBC f i i₁ EA QA jA hcomp hj).comp (algebraMap A (Localization.AtPrime QA)) =
      (algebraMap A₁ (Loc₁ f i i₁ EA QA jA hcomp hj)).comp f :=
    RingHom.ext (locBC_algebraMap_base f i i₁ EA QA jA hcomp hj)
  have hβ : (fibBC f i i₁ EA QA jA hcomp hj hf).comp
      (algebraMap (Localization.AtPrime QA) (GenFib A (Localization.AtPrime QA))) =
      (algebraMap (Loc₁ f i i₁ EA QA jA hcomp hj) (GenFib A₁ (Loc₁ f i i₁ EA QA jA hcomp hj))).comp
        (locBC f i i₁ EA QA jA hcomp hj) :=
    RingHom.ext (fibBC_algebraMap f i i₁ EA QA jA hcomp hj hf)
  refine closureEtaleAt_bc A (Localization.AtPrime QA) A₁ (Loc₁ f i i₁ EA QA jA hcomp hj) f hf hA₁
    (locBC f i i₁ EA QA jA hcomp hj) hκ (fibBC f i i₁ EA QA jA hcomp hj hf) hβ DA P₁ ?_
  apply hyp
  rw [Ideal.mem_comap, ← RingHom.comp_apply, hκ, RingHom.comp_apply]
  exact haP₁

end GlobalTheory.KeyOriginBCEt
end
end
end
