module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodIffEtaleAt
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureFiniteEtale
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
public import Mathlib.RingTheory.Etale.Locus
import Mathlib.Order.CompletePartialOrder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalizationAtPrimeIsDomainIsIntegrallyClos
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteIntegralClosureOverGenericFibreOfEtaleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZmodTorsorExistsPointFiniteSeparable
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.RingTheory.Polynomial.IsIntegral

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CountingBound

section

@[expose] public section

open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.KeyOriginNoeth

theorem isEtaleAt_closure_of_disjoint : ∀ (A R D : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R] [CommRing D]
    [Algebra (GlobalTheory.LocAcyc.GenFib A R) D]
    [Module.Finite (GlobalTheory.LocAcyc.GenFib A R) D] [Algebra.Etale (GlobalTheory.LocAcyc.GenFib A R) D],
    letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D;
    ∀ (Q : Ideal (GlobalTheory.KeyOriginNoeth.closure A R D)) [Q.IsPrime],
      (∀ a : A, a ≠ 0 → algebraMap R (GlobalTheory.KeyOriginNoeth.closure A R D) (algebraMap A R a) ∉ Q) →
      Algebra.IsEtaleAt R Q := by
  intro A R D _ _ _ _ _ _ _ _
  letI := closureAlg A R D
  intro Q _ hQ
  letI : Algebra R D := (baseHom A R D).toAlgebra
  haveI : IsScalarTower R (GlobalTheory.LocAcyc.GenFib A R) D := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let SR : Submonoid R := Algebra.algebraMapSubmonoid R (nonZeroDivisors A)
  let SC : Submonoid (closure A R D) := Algebra.algebraMapSubmonoid (closure A R D) SR
  have hCD : ∀ r : R, algebraMap (closure A R D) D (algebraMap R (closure A R D) r) = algebraMap R D r :=
    fun _ => rfl
  haveI : IsScalarTower R (closure A R D) D := IsScalarTower.of_algebraMap_eq (fun r => (hCD r).symm)
  have hunit : ∀ a : A, a ∈ nonZeroDivisors A → IsUnit (algebraMap R D (algebraMap A R a)) := by
    intro a ha
    have h1 : IsUnit (algebraMap R (GlobalTheory.LocAcyc.GenFib A R) (algebraMap A R a)) :=
      IsLocalization.map_units (GlobalTheory.LocAcyc.GenFib A R) (⟨algebraMap A R a, a, ha, rfl⟩ : SR)
    rw [IsScalarTower.algebraMap_apply R (GlobalTheory.LocAcyc.GenFib A R) D]
    exact h1.map _
  haveI hloc : IsLocalization SC D := by
    refine (isLocalization_iff SC D).2 ⟨?_, ?_, ?_⟩
    · rintro ⟨_, ⟨_, ⟨a, ha, rfl⟩, rfl⟩⟩
      exact hCD _ ▸ hunit a ha
    · intro d
      have hd : IsIntegral (GlobalTheory.LocAcyc.GenFib A R) d := Algebra.IsIntegral.isIntegral d
      obtain ⟨⟨m, hm⟩, hmi⟩ := IsIntegral.exists_multiple_integral_of_isLocalization SR
        (Rₘ := GlobalTheory.LocAcyc.GenFib A R) d hd
      obtain ⟨a, ha, rfl⟩ := hm
      refine ⟨(⟨_, hmi⟩, ⟨algebraMap R (closure A R D) (algebraMap A R a), _, ⟨a, ha, rfl⟩, rfl⟩), ?_⟩
      show d * algebraMap (closure A R D) D (algebraMap R (closure A R D) (algebraMap A R a)) = _
      rw [hCD, mul_comm, ← Algebra.smul_def]
      rfl
    · intro x y h
      exact ⟨1, by rw [Subtype.ext h]⟩
  have hle : SC ≤ Q.primeCompl := by
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact hQ a (nonZeroDivisors.ne_zero ha)
  letI : Algebra D (Localization.AtPrime Q) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe D (Localization.AtPrime Q) SC Q.primeCompl hle
  haveI : IsScalarTower (closure A R D) D (Localization.AtPrime Q) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le D (Localization.AtPrime Q) SC Q.primeCompl hle
  haveI : IsLocalization (Algebra.algebraMapSubmonoid D Q.primeCompl) (Localization.AtPrime Q) :=
    IsLocalization.isLocalization_of_submonoid_le D (Localization.AtPrime Q) SC Q.primeCompl hle
  haveI : Algebra.FormallyEtale D (Localization.AtPrime Q) :=
    Algebra.FormallyEtale.of_isLocalization (Algebra.algebraMapSubmonoid D Q.primeCompl)
  haveI : Algebra.FormallyEtale R (GlobalTheory.LocAcyc.GenFib A R) := Algebra.FormallyEtale.of_isLocalization SR
  haveI : Algebra.FormallyEtale R D := Algebra.FormallyEtale.comp R (GlobalTheory.LocAcyc.GenFib A R) D
  haveI : IsScalarTower R D (Localization.AtPrime Q) := IsScalarTower.of_algebraMap_eq (fun r => by
    rw [IsScalarTower.algebraMap_apply R (closure A R D) (Localization.AtPrime Q),
      IsScalarTower.algebraMap_apply (closure A R D) D (Localization.AtPrime Q), hCD])
  exact Algebra.FormallyEtale.comp R D (Localization.AtPrime Q)

end GlobalTheory.KeyOriginNoeth
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosurePrimeRegularHeight

section

@[expose] public section

open IsLocalRing Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.closure_prime_regular_height : ∀ (A R D : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R] [CommRing D]
    [Algebra (GlobalTheory.LocAcyc.GenFib A R) D]
    [Module.Finite (GlobalTheory.LocAcyc.GenFib A R) D] [Algebra.Etale (GlobalTheory.LocAcyc.GenFib A R) D],
    letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D
    ∀ (Q : Ideal (GlobalTheory.KeyOriginNoeth.closure A R D)) [Q.IsPrime],
      (∀ a : A, a ≠ 0 → algebraMap R (GlobalTheory.KeyOriginNoeth.closure A R D) (algebraMap A R a) ∉ Q) →
      Algebra.IsEtaleAt R Q := by
  first | (exact @GlobalTheory.KeyOriginNoeth.isEtaleAt_closure_of_disjoint) | (exact GlobalTheory.KeyOriginNoeth.isEtaleAt_closure_of_disjoint) | (intros; apply GlobalTheory.KeyOriginNoeth.isEtaleAt_closure_of_disjoint <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleAwayOfIsEtaleAtOffSubmonoid

section

@[expose] public section

open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory

theorem etale_away_of_isEtaleAt_off_submonoid :
  ∀ (R C : Type) [CommRing R] [CommRing C] [Algebra R C] [Algebra.FinitePresentation R C]
    (M : Submonoid R),
    (∀ (Q : Ideal C) [Q.IsPrime], (∀ m ∈ M, algebraMap R C m ∉ Q) → Algebra.IsEtaleAt R Q) →
    ∃ m ∈ M, Algebra.Etale R (Localization.Away (algebraMap R C m)) := by
  intro R C _ _ _ _ M hM
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal (Algebra.etaleLocus R C)ᶜ).1
    (Algebra.isOpen_etaleLocus (R := R) (A := C)).isClosed_compl
  by_cases hd : Disjoint (I : Set C) (M.map (algebraMap R C) : Set C)
  · exfalso
    obtain ⟨Q, hQ, hIQ, hQd⟩ := Ideal.exists_le_prime_disjoint I (M.map (algebraMap R C)) hd
    have hE : Algebra.IsEtaleAt R Q := by
      refine hM Q fun m hm hmQ => ?_
      exact Set.disjoint_left.1 hQd hmQ ⟨m, hm, rfl⟩
    have h1 : (⟨Q, hQ⟩ : PrimeSpectrum C) ∈ Algebra.etaleLocus R C := hE
    have h2 : (⟨Q, hQ⟩ : PrimeSpectrum C) ∈ (Algebra.etaleLocus R C)ᶜ := by
      rw [hI]; exact hIQ
    exact h2 h1
  · rw [Set.not_disjoint_iff] at hd
    obtain ⟨x, hxI, m, hm, rfl⟩ := hd
    refine ⟨m, hm, ?_⟩
    rw [← Algebra.basicOpen_subset_etaleLocus_iff_etale]
    intro p hp
    by_contra hc
    have : p ∈ (Algebra.etaleLocus R C)ᶜ := hc
    rw [hI] at this
    exact hp (this hxI)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleAwayOfIsEtaleAtOffSubmonoidStatement

section

@[expose] public section

open IsLocalRing Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_etale_away_of_isEtaleAt : ∀ (R C : Type) [CommRing R] [CommRing C] [Algebra R C] [Algebra.FinitePresentation R C]
    (M : Submonoid R),
    (∀ (Q : Ideal C) [Q.IsPrime], (∀ m ∈ M, algebraMap R C m ∉ Q) → Algebra.IsEtaleAt R Q) →
    ∃ m ∈ M, Algebra.Etale R (Localization.Away (algebraMap R C m)) := by
  first | (exact @GlobalTheory.etale_away_of_isEtaleAt_off_submonoid) | (exact GlobalTheory.etale_away_of_isEtaleAt_off_submonoid) | (intros; apply GlobalTheory.etale_away_of_isEtaleAt_off_submonoid <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalizationAtPrimeTensorOfEtaleAway

section

@[expose] public section

open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory

theorem etale_localization_atPrime_tensor_of_etale_away : ∀ (R C : Type) [CommRing R] [CommRing C] [Algebra R C] (b : R),
    Algebra.Etale R (Localization.Away (algebraMap R C b)) →
    ∀ (P : Ideal R) [P.IsPrime], b ∉ P →
      Algebra.Etale (Localization.AtPrime P) (TensorProduct R (Localization.AtPrime P) C) := by
  intro R C _ _ _ b hE P _ hb
  let Rp := Localization.AtPrime P
  let Cb := Localization.Away (algebraMap R C b)
  haveI : Algebra.Etale Rp (Rp ⊗[R] Cb) := Algebra.Etale.baseChange R Cb Rp
  have hu : IsUnit ((Algebra.TensorProduct.includeRight : C →ₐ[R] Rp ⊗[R] C).toRingHom
      (algebraMap R C b)) := by
    change IsUnit ((Algebra.TensorProduct.includeRight : C →ₐ[R] Rp ⊗[R] C) (algebraMap R C b))
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R Rp (Rp ⊗[R] C)]
    exact (IsLocalization.map_units Rp (⟨b, hb⟩ : P.primeCompl)).map _
  let g0 : Cb →+* Rp ⊗[R] C := IsLocalization.Away.lift (algebraMap R C b) hu
  have hg0 : ∀ c : C, g0 (algebraMap C Cb c) = (1 : Rp) ⊗ₜ[R] c := fun c =>
    IsLocalization.Away.lift_eq (algebraMap R C b) hu c
  let g : Cb →ₐ[R] Rp ⊗[R] C :=
    { g0 with
      commutes' := fun r => by
        change g0 (algebraMap R Cb r) = _
        rw [IsScalarTower.algebraMap_apply R C Cb, hg0]
        exact (Algebra.TensorProduct.includeRight : C →ₐ[R] Rp ⊗[R] C).commutes r }
  let Φ : Rp ⊗[R] Cb →ₐ[Rp] Rp ⊗[R] C :=
    Algebra.TensorProduct.lift (Algebra.ofId Rp _) g (fun _ _ => Commute.all _ _)
  let Ψ : Rp ⊗[R] C →ₐ[Rp] Rp ⊗[R] Cb :=
    Algebra.TensorProduct.map (AlgHom.id Rp Rp) (IsScalarTower.toAlgHom R C Cb)
  have h1 : Φ.comp Ψ = AlgHom.id Rp _ := by
    ext c
    simp [Φ, Ψ, g, hg0]
  have h2 : Ψ.comp Φ = AlgHom.id Rp _ := by
    ext x
    simp only [AlgHom.comp_apply, AlgHom.id_apply]
    change Ψ (Φ ((1 : Rp) ⊗ₜ[R] algebraMap C Cb x)) = (1 : Rp) ⊗ₜ[R] algebraMap C Cb x
    have : Φ ((1 : Rp) ⊗ₜ[R] algebraMap C Cb x) = (1 : Rp) ⊗ₜ[R] x := by
      simp [Φ, g, hg0]
    rw [this]
    simp [Ψ]
  exact Algebra.Etale.of_equiv (AlgEquiv.ofAlgHom Ψ Φ h2 h1).symm

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalizationAtPrimeTensorOfEtaleAwayStatement

section

@[expose] public section

open IsLocalRing Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.etale_localization_atPrime_tensor_of_etale_away' : ∀ (R C : Type) [CommRing R] [CommRing C] [Algebra R C] (b : R),
    Algebra.Etale R (Localization.Away (algebraMap R C b)) →
    ∀ (P : Ideal R) [P.IsPrime], b ∉ P →
      Algebra.Etale (Localization.AtPrime P) (TensorProduct R (Localization.AtPrime P) C) := by
  first | (exact @GlobalTheory.etale_localization_atPrime_tensor_of_etale_away) | (exact GlobalTheory.etale_localization_atPrime_tensor_of_etale_away) | (intros; apply GlobalTheory.etale_localization_atPrime_tensor_of_etale_away <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroClosureEtaleAt

section

@[expose] public section

open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.KeyOriginEnlarge

theorem etale_of_isZTorsor (B D : Type) [CommRing B] [IsNoetherianRing B] [CommRing D] [Algebra B D]
    (q : ℕ) (hq : 0 < q) (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D))
    (h : GlobalTheory.KeyOriginCut.IsZTorsor B D q act) : Algebra.Etale B D := by
  haveI := GlobalTheory.TorsorFieldPoint.formallyUnramified_of_isZTorsor B D q hq act h
  obtain ⟨hfin, hproj, _, _⟩ := h
  haveI := hfin
  haveI := hproj
  haveI : Algebra.FinitePresentation B D :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact Algebra.Etale.of_formallyUnramified_of_flat

theorem exists_ne_zero_closureEtaleAt : ∀ (q : ℕ) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [Algebra.EssFiniteType ℤ A]
    (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
    [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
    (QA : Ideal EA) [QA.IsPrime]
    (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
    (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    0 < q → IsUnit (q : A) →
    GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
    ∃ a : A, a ≠ 0 ∧ ∀ (P : Ideal (Localization.AtPrime QA)) [P.IsPrime],
      algebraMap A (Localization.AtPrime QA) a ∉ P →
      GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A (Localization.AtPrime QA) DA P := by
  intro q A _ _ _ _ _ _ EA _ _ _ _ _ QA _ DA _ _ actA hq _ htor
  haveI : IsNoetherianRing EA := Algebra.FiniteType.isNoetherianRing (Polynomial A) EA
  obtain ⟨_, _⟩ := GlobalTheory.etale_localization_atPrime_isDomain_isIntegrallyClosed (Polynomial A) EA QA
  set R := Localization.AtPrime QA
  haveI : Module.Finite (GlobalTheory.LocAcyc.GenFib A R) DA := htor.1
  haveI := etale_of_isZTorsor _ DA q hq actA htor
  letI := GlobalTheory.KeyOriginNoeth.closureAlg A R DA
  haveI : Module.Finite R (GlobalTheory.KeyOriginNoeth.closure A R DA) := GlobalTheory.T.finite_integralClosureOverGenericFibre_of_etale A R DA
  haveI : Algebra.FinitePresentation R (GlobalTheory.KeyOriginNoeth.closure A R DA) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨m, hm, hE⟩ := GlobalTheory.T.exists_etale_away_of_isEtaleAt R (GlobalTheory.KeyOriginNoeth.closure A R DA)
    (Algebra.algebraMapSubmonoid R (nonZeroDivisors A)) (fun Q _ hQ =>
      GlobalTheory.T.closure_prime_regular_height A R DA Q (fun a ha => hQ _ ⟨a, mem_nonZeroDivisors_of_ne_zero ha, rfl⟩))
  obtain ⟨a, ha, rfl⟩ := hm
  refine ⟨a, nonZeroDivisors.ne_zero ha, fun P _ hP => ?_⟩
  exact GlobalTheory.T.etale_localization_atPrime_tensor_of_etale_away' R _ _ hE P hP

end GlobalTheory.KeyOriginEnlarge
end
end
end
