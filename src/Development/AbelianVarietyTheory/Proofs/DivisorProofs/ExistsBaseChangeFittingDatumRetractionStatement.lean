module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointAtZero
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChangeRetractStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZmodTorsorBaseChangeTransportPointStatement
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicFiniteVolumeIntegralBound

section

@[expose] public section

open IsLocalRing Polynomial

namespace GlobalTheory.GenFibBaseChange

theorem exists_genFib_maps : ∀ (T O A A₁ R R₁ : Type) [CommRing T] [IsDomain T] [CommRing O] [Algebra T O]
    [CommRing A] [IsDomain A] [CommRing A₁] [IsDomain A₁] [CommRing R] [Algebra A R] [CommRing R₁] [Algebra A₁ R₁]
    (j : A →+* A₁) (i₁ : A₁ →+* T), Function.Injective j → Function.Injective i₁ →
    ∀ (jA : R →+* O) (jA₁ : R₁ →+* O) (γ : R →+* R₁)
      (ψA : GlobalTheory.LocAcyc.GenFib A R →+* GlobalTheory.LocAcyc.GenFib T O),
    jA₁.comp (algebraMap A₁ R₁) = (algebraMap T O).comp i₁ →
    γ.comp (algebraMap A R) = (algebraMap A₁ R₁).comp j →
    jA₁.comp γ = jA →
    ψA.comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) = (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA →
    ∃ (ψA₁ : GlobalTheory.LocAcyc.GenFib A₁ R₁ →+* GlobalTheory.LocAcyc.GenFib T O)
      (β : GlobalTheory.LocAcyc.GenFib A R →+* GlobalTheory.LocAcyc.GenFib A₁ R₁),
      ψA₁.comp (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)) = (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA₁ ∧
      ψA₁.comp β = ψA ∧
      β.comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) = (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)).comp γ := by
  intro T O A A₁ R R₁ _ _ _ _ _ _ _ _ _ _ _ _ j i₁ hj hi₁ jA jA₁ γ ψA h1 h2 h3 h4
  have hu1 : ∀ y : Algebra.algebraMapSubmonoid R₁ (nonZeroDivisors A₁),
      IsUnit (((algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA₁) y) := by
    rintro ⟨y, a, ha, rfl⟩
    have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
    have hi : i₁ a ∈ nonZeroDivisors T := mem_nonZeroDivisors_of_ne_zero (fun h => ha0 (hi₁ (by simpa using h)))
    have e : jA₁ (algebraMap A₁ R₁ a) = algebraMap T O (i₁ a) := by
      simpa using congrArg (fun f => f a) h1
    simp only [RingHom.coe_comp, Function.comp_apply, e]
    exact IsLocalization.map_units (GlobalTheory.LocAcyc.GenFib T O)
      (⟨algebraMap T O (i₁ a), ⟨i₁ a, hi, rfl⟩⟩ : Algebra.algebraMapSubmonoid O (nonZeroDivisors T))
  have hu2 : ∀ y : Algebra.algebraMapSubmonoid R (nonZeroDivisors A),
      IsUnit (((algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)).comp γ) y) := by
    rintro ⟨y, a, ha, rfl⟩
    have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
    have hi : j a ∈ nonZeroDivisors A₁ := mem_nonZeroDivisors_of_ne_zero (fun h => ha0 (hj (by simpa using h)))
    have e : γ (algebraMap A R a) = algebraMap A₁ R₁ (j a) := by
      simpa using congrArg (fun f => f a) h2
    simp only [RingHom.coe_comp, Function.comp_apply, e]
    exact IsLocalization.map_units (GlobalTheory.LocAcyc.GenFib A₁ R₁)
      (⟨algebraMap A₁ R₁ (j a), ⟨j a, hi, rfl⟩⟩ : Algebra.algebraMapSubmonoid R₁ (nonZeroDivisors A₁))
  let ψA₁ : GlobalTheory.LocAcyc.GenFib A₁ R₁ →+* GlobalTheory.LocAcyc.GenFib T O :=
    IsLocalization.lift (M := Algebra.algebraMapSubmonoid R₁ (nonZeroDivisors A₁)) hu1
  let β : GlobalTheory.LocAcyc.GenFib A R →+* GlobalTheory.LocAcyc.GenFib A₁ R₁ :=
    IsLocalization.lift (M := Algebra.algebraMapSubmonoid R (nonZeroDivisors A)) hu2
  have k1 : ψA₁.comp (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)) =
      (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA₁ := IsLocalization.lift_comp hu1
  have k3 : β.comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) =
      (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)).comp γ := IsLocalization.lift_comp hu2
  refine ⟨ψA₁, β, k1, ?_, k3⟩
  apply IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid R (nonZeroDivisors A))
  rw [RingHom.comp_assoc, k3, ← RingHom.comp_assoc, k1, RingHom.comp_assoc, h3, h4]

end GlobalTheory.GenFibBaseChange
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreCompatibility

section

@[expose] public section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.generic_fibre_compatibility : ∀ (T O A A₁ R R₁ : Type) [CommRing T] [IsDomain T] [CommRing O] [Algebra T O]
    [CommRing A] [IsDomain A] [CommRing A₁] [IsDomain A₁] [CommRing R] [Algebra A R] [CommRing R₁] [Algebra A₁ R₁]
    (j : A →+* A₁) (i₁ : A₁ →+* T), Function.Injective j → Function.Injective i₁ →
    ∀ (jA : R →+* O) (jA₁ : R₁ →+* O) (γ : R →+* R₁)
      (ψA : GlobalTheory.LocAcyc.GenFib A R →+* GlobalTheory.LocAcyc.GenFib T O),
    jA₁.comp (algebraMap A₁ R₁) = (algebraMap T O).comp i₁ →
    γ.comp (algebraMap A R) = (algebraMap A₁ R₁).comp j →
    jA₁.comp γ = jA →
    ψA.comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) = (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA →
    ∃ (ψA₁ : GlobalTheory.LocAcyc.GenFib A₁ R₁ →+* GlobalTheory.LocAcyc.GenFib T O)
      (β : GlobalTheory.LocAcyc.GenFib A R →+* GlobalTheory.LocAcyc.GenFib A₁ R₁),
      ψA₁.comp (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)) = (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA₁ ∧
      ψA₁.comp β = ψA ∧
      β.comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) = (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)).comp γ := by
  first | (exact @GlobalTheory.GenFibBaseChange.exists_genFib_maps) | (exact GlobalTheory.GenFibBaseChange.exists_genFib_maps) | (intros; apply GlobalTheory.GenFibBaseChange.exists_genFib_maps  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyOriginRetractionLocalises

section

@[expose] public section

open IsLocalRing Polynomial

namespace GlobalTheory.KeyOriginEnlargeLoc

theorem retract_localises : ∀ (T O A₁ EA₁ : Type) [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O] [Algebra (Polynomial T) O]
    [CommRing A₁] [IsLocalRing A₁] (i₁ : A₁ →+* T), IsLocalHom i₁ → IsLocalHom (algebraMap T O) →
    ∀ [CommRing EA₁] [Algebra (Polynomial A₁) EA₁] [Algebra A₁ EA₁]
      (QA₁ : Ideal EA₁) [QA₁.IsPrime] (jA₁ : Localization.AtPrime QA₁ →+* O) (ρ' : EA₁ →+* A₁),
    algebraMap (Polynomial T) O Polynomial.X ∈ maximalIdeal O →
    ρ'.comp (algebraMap A₁ EA₁) = RingHom.id A₁ →
    ρ' (algebraMap (Polynomial A₁) EA₁ Polynomial.X) = 0 →
    (∀ x : EA₁, algebraMap T O (i₁ (ρ' x)) - jA₁ (algebraMap EA₁ (Localization.AtPrime QA₁) x) ∈
      Ideal.span {algebraMap (Polynomial T) O Polynomial.X}) →
    (∀ x : EA₁, ρ' x = 0 → ∃ s ∉ QA₁, s * x ∈ Ideal.span {algebraMap (Polynomial A₁) EA₁ Polynomial.X}) →
    ∃ ρ₁ : Localization.AtPrime QA₁ →+* A₁,
      GlobalTheory.KeyOriginEnlarge.Retracts T O A₁ i₁ EA₁ QA₁ jA₁ ρ₁ ∧
      ρ₁.comp (algebraMap EA₁ (Localization.AtPrime QA₁)) = ρ' := by
  intro T O A₁ EA₁ _ _ _ _ _ _ _ i₁ hi₁ hTO _ _ _ QA₁ _ jA₁ ρ' hX hret hρX hcong hker
  set L := Localization.AtPrime QA₁
  set I : Ideal O := Ideal.span {algebraMap (Polynomial T) O Polynomial.X}
  have hI : I ≤ maximalIdeal O := by
    rw [Ideal.span_le]; simpa using hX
  have hunit : ∀ y : QA₁.primeCompl, IsUnit (ρ' y) := by
    intro y
    by_contra hy
    have h1 : ρ' y ∈ maximalIdeal A₁ := (mem_maximalIdeal _).2 hy
    have h2 : algebraMap T O (i₁ (ρ' y)) ∈ maximalIdeal O := by
      rw [mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact hy ((isUnit_map_iff i₁ _).1 ((isUnit_map_iff (algebraMap T O) _).1 hu))
    have h3 : jA₁ (algebraMap EA₁ L y) ∈ maximalIdeal O := by
      have := hI (hcong y)
      have := (maximalIdeal O).sub_mem h2 this
      simpa using this
    have h4 : IsUnit (jA₁ (algebraMap EA₁ L y)) :=
      (IsLocalization.map_units L y).map jA₁
    exact (mem_maximalIdeal _ |>.1 h3) h4
  let ρ₁ : L →+* A₁ := IsLocalization.lift (M := QA₁.primeCompl) hunit
  have hcomp : ρ₁.comp (algebraMap EA₁ L) = ρ' := by
    ext x; exact IsLocalization.lift_eq _ _
  refine ⟨ρ₁, ⟨?_, ?_, ?_⟩, hcomp⟩
  · rw [IsScalarTower.algebraMap_eq A₁ EA₁ L, ← RingHom.comp_assoc, hcomp, hret]
  · apply le_antisymm
    · intro z hz
      rw [RingHom.mem_ker] at hz
      obtain ⟨⟨x, y⟩, rfl⟩ := IsLocalization.mk'_surjective QA₁.primeCompl z
      dsimp only at hz ⊢
      have hx : ρ' x = 0 := by
        have := IsLocalization.lift_mk' (M := QA₁.primeCompl) (S := L) hunit x y
        change ρ₁ _ = _ at this
        rw [hz] at this
        exact (Units.mul_left_eq_zero _).1 this.symm
      obtain ⟨s, hs, hsx⟩ := hker x hx
      have hsy : s * (y : EA₁) ∈ QA₁.primeCompl := QA₁.primeCompl.mul_mem hs y.2
      have heq : IsLocalization.mk' L x y = IsLocalization.mk' L (s * x) (⟨s * y, hsy⟩ : QA₁.primeCompl) := by
        rw [IsLocalization.mk'_eq_iff_eq]
        simp only
        ring_nf
      rw [heq, IsLocalization.mk'_eq_mul_mk'_one]
      apply Ideal.mul_mem_right
      have : algebraMap EA₁ L (s * x) ∈ (Ideal.span {algebraMap (Polynomial A₁) EA₁ Polynomial.X}).map (algebraMap EA₁ L) :=
        Ideal.mem_map_of_mem _ hsx
      rwa [Ideal.map_span, Set.image_singleton, ← IsScalarTower.algebraMap_apply] at this
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker,
        IsScalarTower.algebraMap_apply (Polynomial A₁) EA₁ L]
      change (ρ₁.comp (algebraMap EA₁ L)) _ = 0
      rw [hcomp, hρX]
  · have key : (Ideal.Quotient.mk I).comp ((algebraMap T O).comp (i₁.comp ρ₁)) = (Ideal.Quotient.mk I).comp jA₁ := by
      apply IsLocalization.ringHom_ext QA₁.primeCompl
      ext x
      simp only [RingHom.comp_apply]
      rw [Ideal.Quotient.eq]
      have := hcong x
      rw [← hcomp] at this
      simpa using this
    intro x
    have := congrArg (fun f => f x) key
    simp only [RingHom.comp_apply] at this
    exact Ideal.Quotient.eq.1 this

end GlobalTheory.KeyOriginEnlargeLoc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyOriginRetractionLocalisesStatement

section

@[expose] public section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.keyOrigin_retraction_localises : ∀ (T O A₁ EA₁ : Type) [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O] [Algebra (Polynomial T) O]
    [CommRing A₁] [IsLocalRing A₁] (i₁ : A₁ →+* T), IsLocalHom i₁ → IsLocalHom (algebraMap T O) →
    ∀ [CommRing EA₁] [Algebra (Polynomial A₁) EA₁] [Algebra A₁ EA₁]
      (QA₁ : Ideal EA₁) [QA₁.IsPrime] (jA₁ : Localization.AtPrime QA₁ →+* O) (ρ' : EA₁ →+* A₁),
    algebraMap (Polynomial T) O Polynomial.X ∈ maximalIdeal O →
    ρ'.comp (algebraMap A₁ EA₁) = RingHom.id A₁ →
    ρ' (algebraMap (Polynomial A₁) EA₁ Polynomial.X) = 0 →
    (∀ x : EA₁, algebraMap T O (i₁ (ρ' x)) - jA₁ (algebraMap EA₁ (Localization.AtPrime QA₁) x) ∈
      Ideal.span {algebraMap (Polynomial T) O Polynomial.X}) →
    (∀ x : EA₁, ρ' x = 0 → ∃ s ∉ QA₁, s * x ∈ Ideal.span {algebraMap (Polynomial A₁) EA₁ Polynomial.X}) →
    ∃ ρ₁ : Localization.AtPrime QA₁ →+* A₁,
      GlobalTheory.KeyOriginEnlarge.Retracts T O A₁ i₁ EA₁ QA₁ jA₁ ρ₁ ∧
      ρ₁.comp (algebraMap EA₁ (Localization.AtPrime QA₁)) = ρ' := by
  first | (exact @GlobalTheory.KeyOriginEnlargeLoc.retract_localises) | (exact GlobalTheory.KeyOriginEnlargeLoc.retract_localises) | (intros; apply GlobalTheory.KeyOriginEnlargeLoc.retract_localises  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChangeFittingDatumRetraction

section

@[expose] public section

open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.KeyOriginEnlarge

theorem exists_baseChange_fits : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O]
    (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T)
      (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
      (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    GlobalTheory.KeyOriginEnlarge.Fits T O q A i EA QA jA ψA DA actA →
    ∀ ρ : Localization.AtPrime QA →+* A, GlobalTheory.KeyOriginEnlarge.Retracts T O A i EA QA jA ρ →
    ∀ (A₁ : Type) [CommRing A₁] [IsDomain A₁] [IsLocalRing A₁] [IsNoetherianRing A₁] [IsIntegrallyClosed A₁]
      [Algebra.EssFiniteType ℤ A₁] (j : A →+* A₁) (i₁ : A₁ →+* T),
      Function.Injective j → Function.Injective i₁ → IsLocalHom i₁ → i₁.comp j = i →
    ∃ (EA₁ : Type) (_ : CommRing EA₁) (_ : Algebra (Polynomial A₁) EA₁) (_ : Algebra A₁ EA₁)
      (_ : IsScalarTower A₁ (Polynomial A₁) EA₁) (_ : Algebra.Etale (Polynomial A₁) EA₁)
      (QA₁ : Ideal EA₁) (_ : QA₁.IsPrime) (jA₁ : Localization.AtPrime QA₁ →+* O)
      (ψA₁ : GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA₁ : Type) (_ : CommRing DA₁) (_ : Algebra (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)) DA₁)
      (actA₁ : Multiplicative (ZMod q) →* (DA₁ ≃ₐ[GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)] DA₁))
      (ρ₁ : Localization.AtPrime QA₁ →+* A₁),
      GlobalTheory.KeyOriginEnlarge.Fits T O q A₁ i₁ EA₁ QA₁ jA₁ ψA₁ DA₁ actA₁ ∧
      GlobalTheory.KeyOriginEnlarge.Retracts T O A₁ i₁ EA₁ QA₁ jA₁ ρ₁ ∧
      ∃ (β : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁))
        (h : DA →+* DA₁),
        ψA₁.comp β = ψA ∧
        h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) =
          (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)) DA₁).comp β ∧
        ∀ σ : DA →+* FractionRing A₁,
          (σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA)).comp
              (algebraMap (Localization.AtPrime QA) (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))) =
            (algebraMap A₁ (FractionRing A₁)).comp (j.comp ρ) →
          ∃ σ₁ : DA₁ →+* FractionRing A₁,
            (σ₁.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)) DA₁)).comp
                (algebraMap (Localization.AtPrime QA₁) (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁))) =
              (algebraMap A₁ (FractionRing A₁)).comp ρ₁ := by
  intro T O _ _ _ _ _ _ _ _ P _ φ hφ hSH hP q hq A _ _ _ _ _ _ i EA _ _ _ _ _ QA _ jA ψA DA _ _ actA hFits ρ hRet
    A₁ _ _ _ _ _ _ j i₁ hj hi₁ hi₁l hij
  haveI hφl : IsLocalHom φ := hSH.2.2.1
  have hX : algebraMap (Polynomial T) O Polynomial.X ∈ maximalIdeal O := by
    rw [← hφ, RingHom.comp_apply]
    apply map_nonunit φ
    refine (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P _).2 ?_
    rw [hP]; exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  have hTO : IsLocalHom (algebraMap T O) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have h1 : Polynomial.C a ∈ P := by
      rw [hP]; exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ((IsLocalRing.mem_maximalIdeal _).2 hna))
    refine (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime P) P (Polynomial.C a)).1
      (isUnit_of_map_unit φ _ ?_) h1
    rw [← RingHom.comp_apply, hφ]
    rw [IsScalarTower.algebraMap_apply T (Polynomial T) O] at ha
    exact ha
  obtain ⟨hi, hil, hqu, hQA, hjA, hψA, htors⟩ := hFits
  obtain ⟨EA₁, _, _, _, _, _, QA₁, _, jA₁, γ₀, γ, ρ', hQA₁, hjA₁, hjγ, hγ₀, hγA, hρ'γ, hρ'id, hρ'X, hρ'c, hρ'k⟩ :=
    GlobalTheory.T.exists_baseChange_retract_alt T O hTO hX A i EA QA jA ρ hQA hjA hRet A₁ j i₁ hi₁ hi₁l hij
  obtain ⟨ρ₁, hRet₁, hρ₁⟩ := GlobalTheory.T.keyOrigin_retraction_localises T O A₁ EA₁ i₁ hi₁l hTO QA₁ jA₁ ρ' hX hρ'id hρ'X hρ'c hρ'k
  have hjA₁c : jA₁.comp (algebraMap A₁ (Localization.AtPrime QA₁)) = (algebraMap T O).comp i₁ := by
    ext a
    have e1 : algebraMap A₁ (Localization.AtPrime QA₁) a =
        algebraMap (Polynomial A₁) (Localization.AtPrime QA₁) (Polynomial.C a) := by
      rw [IsScalarTower.algebraMap_apply A₁ EA₁ (Localization.AtPrime QA₁),
        IsScalarTower.algebraMap_apply A₁ (Polynomial A₁) EA₁,
        IsScalarTower.algebraMap_apply (Polynomial A₁) EA₁ (Localization.AtPrime QA₁)]
      rfl
    rw [RingHom.comp_apply, e1, ← RingHom.comp_apply, hjA₁, RingHom.comp_apply, Polynomial.coe_mapRingHom,
      Polynomial.map_C, RingHom.comp_apply, IsScalarTower.algebraMap_apply T (Polynomial T) O]
    rfl
  obtain ⟨ψA₁, β, hψA₁, hψβ, hβ⟩ := GlobalTheory.T.generic_fibre_compatibility T O A A₁ _ _ j i₁ hj hi₁ jA jA₁ γ ψA hjA₁c hγA hjγ hψA
  have hργ : ρ₁.comp γ = j.comp ρ := by
    apply IsLocalization.ringHom_ext QA.primeCompl
    rw [RingHom.comp_assoc, hγ₀, ← RingHom.comp_assoc, hρ₁, hρ'γ, RingHom.comp_assoc]
  obtain ⟨DA₁, _, _, actA₁, h, htors₁, hh, hpt⟩ :=
    GlobalTheory.T.zmodTorsor_baseChange_transport_point A A₁ _ _ j γ ρ ρ₁ β hβ hRet₁.1 hργ q hq DA actA htors
  refine ⟨EA₁, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, QA₁, inferInstance,
    jA₁, ψA₁, DA₁, inferInstance, inferInstance, actA₁, ρ₁, ⟨hi₁, hi₁l, ?_, hQA₁, hjA₁, hψA₁, htors₁⟩, hRet₁,
    β, h, hψβ, hh, hpt⟩
  have := hqu.map j
  simpa using this

end GlobalTheory.KeyOriginEnlarge
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChangeFittingDatumRetractionStatement

section

@[expose] public section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.exists_baseChange_fittingDatum_retraction : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O]
    (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T)
      (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
      (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    GlobalTheory.KeyOriginEnlarge.Fits T O q A i EA QA jA ψA DA actA →
    ∀ ρ : Localization.AtPrime QA →+* A, GlobalTheory.KeyOriginEnlarge.Retracts T O A i EA QA jA ρ →
    ∀ (A₁ : Type) [CommRing A₁] [IsDomain A₁] [IsLocalRing A₁] [IsNoetherianRing A₁] [IsIntegrallyClosed A₁]
      [Algebra.EssFiniteType ℤ A₁] (j : A →+* A₁) (i₁ : A₁ →+* T),
      Function.Injective j → Function.Injective i₁ → IsLocalHom i₁ → i₁.comp j = i →
    ∃ (EA₁ : Type) (_ : CommRing EA₁) (_ : Algebra (Polynomial A₁) EA₁) (_ : Algebra A₁ EA₁)
      (_ : IsScalarTower A₁ (Polynomial A₁) EA₁) (_ : Algebra.Etale (Polynomial A₁) EA₁)
      (QA₁ : Ideal EA₁) (_ : QA₁.IsPrime) (jA₁ : Localization.AtPrime QA₁ →+* O)
      (ψA₁ : GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA₁ : Type) (_ : CommRing DA₁) (_ : Algebra (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)) DA₁)
      (actA₁ : Multiplicative (ZMod q) →* (DA₁ ≃ₐ[GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)] DA₁))
      (ρ₁ : Localization.AtPrime QA₁ →+* A₁),
      GlobalTheory.KeyOriginEnlarge.Fits T O q A₁ i₁ EA₁ QA₁ jA₁ ψA₁ DA₁ actA₁ ∧
      GlobalTheory.KeyOriginEnlarge.Retracts T O A₁ i₁ EA₁ QA₁ jA₁ ρ₁ ∧
      ∃ (β : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁))
        (h : DA →+* DA₁),
        ψA₁.comp β = ψA ∧
        h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) =
          (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)) DA₁).comp β ∧
        ∀ σ : DA →+* FractionRing A₁,
          (σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA)).comp
              (algebraMap (Localization.AtPrime QA) (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))) =
            (algebraMap A₁ (FractionRing A₁)).comp (j.comp ρ) →
          ∃ σ₁ : DA₁ →+* FractionRing A₁,
            (σ₁.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)) DA₁)).comp
                (algebraMap (Localization.AtPrime QA₁) (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁))) =
              (algebraMap A₁ (FractionRing A₁)).comp ρ₁ := by
  first | (exact @GlobalTheory.KeyOriginEnlarge.exists_baseChange_fits) | (exact GlobalTheory.KeyOriginEnlarge.exists_baseChange_fits) | (intros; apply GlobalTheory.KeyOriginEnlarge.exists_baseChange_fits <;> assumption)
end
end
