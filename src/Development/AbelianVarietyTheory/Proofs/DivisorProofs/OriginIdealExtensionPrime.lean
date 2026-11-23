module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsLocalRingOfIsIntegralOfHenselian
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
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSubMemMaximalIdealEtaleOverOriginStatement
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdealUniquePrimeOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorIsLocalRingOfUniquePrimeOverStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalizationAtPrimeIsDomainIsIntegrallyClos
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.TotallySplit

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalLocalDomainOverHenselianPrime

section

@[expose] public section

open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.NormalLocal

theorem exists_normal_local (A : Type) [CommRing A] [HenselianLocalRing A] (𝔭 : Ideal A) [𝔭.IsPrime] :
    ∃ (S : Type) (_ : CommRing S) (_ : IsDomain S) (_ : IsIntegrallyClosed S) (_ : IsLocalRing S) (f : A →+* S),
      f.IsIntegral ∧ RingHom.ker f = 𝔭 := by
  let B := A ⧸ 𝔭
  let K := FractionRing B
  let S := integralClosure B K
  have : IsFractionRing S K := inferInstance
  have hic : IsIntegrallyClosed S := (isIntegrallyClosed_iff_isIntegrallyClosedIn K).mpr inferInstance
  letI : Algebra A S := ((algebraMap B S).comp (Ideal.Quotient.mk 𝔭)).toAlgebra
  have h1 : (Ideal.Quotient.mk 𝔭).IsIntegral := RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective
  have h2 : (algebraMap B S).IsIntegral := fun x => Algebra.IsIntegral.isIntegral (R := B) x
  have hint : (algebraMap A S).IsIntegral := RingHom.IsIntegral.trans _ _ h1 h2
  haveI : Algebra.IsIntegral A S := ⟨fun x => hint x⟩
  have hloc : IsLocalRing S := GlobalTheory.IntClLocal.isLocalRing_of_isIntegral_of_henselian A S
  have hinjK : Function.Injective (algebraMap B K) := IsFractionRing.injective B K
  have hinj : Function.Injective (algebraMap B S) := by
    intro x y h
    exact hinjK (congrArg Subtype.val h)
  refine ⟨S, inferInstance, inferInstance, hic, hloc, algebraMap A S, hint, ?_⟩
  ext a
  rw [RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem]
  change (algebraMap B S) (Ideal.Quotient.mk 𝔭 a) = 0 ↔ _
  rw [← map_zero (algebraMap B S), hinj.eq_iff]

end GlobalTheory.NormalLocal
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalLocalDomainOverHenselianPrimeStatement

section

@[expose] public section

open IsLocalRing Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_normal_local_domain_over_henselian_prime : ∀ (A : Type) [CommRing A] [HenselianLocalRing A] (𝔭 : Ideal A) [𝔭.IsPrime],
    ∃ (S : Type) (_ : CommRing S) (_ : IsDomain S) (_ : IsIntegrallyClosed S) (_ : IsLocalRing S) (f : A →+* S), f.IsIntegral ∧ RingHom.ker f = 𝔭 := by
  first | (exact @GlobalTheory.NormalLocal.exists_normal_local) | (exact GlobalTheory.NormalLocal.exists_normal_local) | (intros; apply GlobalTheory.NormalLocal.exists_normal_local  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleModelDegree

section

@[expose] public section

open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory

theorem flat_one_tmul_eq_zero_mem_map (P T L : Type) [CommRing P] [CommRing T] [CommRing L] [Algebra P T] [Algebra P L] [Module.Flat P L] (I : Ideal P) :
    RingHom.ker (algebraMap P T) = I → ∀ y : L, (1 : T) ⊗ₜ[P] y = 0 → y ∈ I.map (algebraMap P L) := by
  intro hI y hy
  subst hI
  set K := RingHom.ker (algebraMap P T)
  let f : (P ⧸ K) →ₗ[P] T := (Ideal.Quotient.liftₐ K (Algebra.ofId P T) (fun a ha => RingHom.mem_ker.mp ha)).toLinearMap
  have hf : Function.Injective f := by
    intro a b hab
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [Ideal.Quotient.eq, RingHom.mem_ker, map_sub, sub_eq_zero]
    simpa [f] using hab
  have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := L) f hf
  have h0 : (1 : P ⧸ K) ⊗ₜ[P] y = 0 := by
    apply hinj
    rw [LinearMap.rTensor_tmul, map_zero]
    simpa [f] using hy
  have h1 := congrArg (TensorProduct.quotTensorEquivQuotSMul L K) h0
  rw [map_zero, TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero] at h1
  rw [Ideal.smul_top_eq_map] at h1
  exact h1

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatTensorKernelMemMapIdeal

section

@[expose] public section

open IsLocalRing Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.flat_tensor_kernel_mem_map_ideal : ∀ (P T L : Type) [CommRing P] [CommRing T] [CommRing L] [Algebra P T] [Algebra P L] [Module.Flat P L] (I : Ideal P),
    RingHom.ker (algebraMap P T) = I → ∀ y : L, (1 : T) ⊗ₜ[P] y = 0 → y ∈ I.map (algebraMap P L) := by
  first | (exact @GlobalTheory.flat_one_tmul_eq_zero_mem_map) | (exact GlobalTheory.flat_one_tmul_eq_zero_mem_map) | (intros; apply GlobalTheory.flat_one_tmul_eq_zero_mem_map  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLocalizationAtPrimeIsDomainOfIsLocalRingEt

section

@[expose] public section

open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory

theorem tensor_localization_atPrime_isDomain_of_isLocalRing_etale :
    ∀ (P R E : Type) [CommRing P] [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Algebra P R]
      [CommRing E] [Algebra P E] [Algebra.Etale P E] (Q : Ideal E) [Q.IsPrime],
      IsLocalRing (TensorProduct P R (Localization.AtPrime Q)) →
        IsDomain (TensorProduct P R (Localization.AtPrime Q)) := by
  intro P R E _ _ _ _ _ _ _ _ Q _ hloc
  letI : Algebra (R ⊗[P] E) (R ⊗[P] Localization.AtPrime Q) :=
    (Algebra.TensorProduct.map (AlgHom.id P R)
      (IsScalarTower.toAlgHom P E (Localization.AtPrime Q))).toAlgebra
  haveI : IsScalarTower R (R ⊗[P] E) (R ⊗[P] Localization.AtPrime Q) :=
    .of_algebraMap_eq <| by intro; simp [RingHom.algebraMap_toAlgebra]
  haveI hl := IsLocalization.tensorProduct_tensorProduct_right P R Q.primeCompl
    (Localization.AtPrime Q) (by ext; simp [RingHom.algebraMap_toAlgebra])
  let 𝔭 : Ideal (R ⊗[P] E) :=
    (maximalIdeal (R ⊗[P] Localization.AtPrime Q)).comap
      (algebraMap (R ⊗[P] E) (R ⊗[P] Localization.AtPrime Q))
  haveI : 𝔭.IsPrime := Ideal.comap_isPrime _ _
  have hle : Q.primeCompl.map (Algebra.TensorProduct.includeRight (R := P) (A := R)) ≤
      𝔭.primeCompl := by
    intro x hx
    have hu := IsLocalization.map_units (R ⊗[P] Localization.AtPrime Q)
      (⟨x, hx⟩ : Q.primeCompl.map (Algebra.TensorProduct.includeRight (R := P) (A := R)))
    intro h
    exact ((mem_maximalIdeal _).mp (Ideal.mem_comap.mp h)) hu
  haveI : IsLocalization 𝔭.primeCompl (R ⊗[P] Localization.AtPrime Q) :=
    IsLocalization.of_le _ _ hle (fun r hr => by
      by_contra hu
      exact hr (Ideal.mem_comap.mpr ((mem_maximalIdeal _).mpr hu)))
  obtain ⟨hd, -⟩ := etale_localization_atPrime_isDomain_isIntegrallyClosed R (R ⊗[P] E) 𝔭
  let e : Localization.AtPrime 𝔭 ≃ₐ[R ⊗[P] E] (R ⊗[P] Localization.AtPrime Q) :=
    IsLocalization.algEquiv 𝔭.primeCompl _ _
  exact e.symm.injective.isDomain _

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLocalizationAtPrimeIsDomainOfIsLocalRingEtStatement

section

@[expose] public section

open IsLocalRing Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.isDomain_tensor_atPrime_of_isLocalRing_of_etale : ∀ (P R E : Type) [CommRing P] [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Algebra P R] [CommRing E] [Algebra P E] [Algebra.Etale P E] (Q : Ideal E) [Q.IsPrime],
    IsLocalRing (TensorProduct P R (Localization.AtPrime Q)) → IsDomain (TensorProduct P R (Localization.AtPrime Q)) := by
  first | (exact @GlobalTheory.tensor_localization_atPrime_isDomain_of_isLocalRing_etale) | (exact GlobalTheory.tensor_localization_atPrime_isDomain_of_isLocalRing_etale) | (intros; apply GlobalTheory.tensor_localization_atPrime_isDomain_of_isLocalRing_etale <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HopfOrdersOfZmodPExtremes

section

@[expose] public section

open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.OriginPrimes

theorem origin_primes : ∀ (A' : Type) [CommRing A'] [HenselianLocalRing A'] [IsSepClosed (ResidueField A')]
    (𝔭 : Ideal A') [𝔭.IsPrime] (E : Type) [CommRing E] [Algebra (Polynomial A') E]
    [Algebra.Etale (Polynomial A') E] (Q : Ideal E) [Q.IsPrime],
    Q.comap (algebraMap (Polynomial A') E) = GlobalTheory.KeyOriginCut.originIdeal A' →
    (𝔭.map ((algebraMap (Polynomial A') (Localization.AtPrime Q)).comp Polynomial.C)).IsPrime := by
  intro A' _ _ _ 𝔭 _ E _ _ _ Q _ hQ
  obtain ⟨S, _, _, _, _, f, hfi, hker⟩ := GlobalTheory.T.exists_normal_local_domain_over_henselian_prime A' 𝔭
  obtain ⟨hXi, hOp, hOc, hOu⟩ := GlobalTheory.T.origin_ideal_unique_prime_over A' S f hfi
  letI : Algebra (Polynomial A') (Polynomial S) := (Polynomial.mapRingHom f).toAlgebra
  haveI : Algebra.IsIntegral (Polynomial A') (Polynomial S) := ⟨hXi⟩
  have hmax : (maximalIdeal (Localization.AtPrime Q)).comap
      (algebraMap (Polynomial A') (Localization.AtPrime Q)) = GlobalTheory.KeyOriginCut.originIdeal A' := by
    have h0 : (maximalIdeal (Localization.AtPrime Q)).comap (algebraMap E (Localization.AtPrime Q)) = Q :=
      Localization.AtPrime.under_maximalIdeal (I := Q)
    rw [IsScalarTower.algebraMap_eq (Polynomial A') E (Localization.AtPrime Q), ← Ideal.comap_comap,
      h0, hQ]
  haveI hloc : IsLocalRing (TensorProduct (Polynomial A') (Polynomial S) (Localization.AtPrime Q)) :=
    GlobalTheory.T.isLocalRing_tensor_of_unique_prime_over (Polynomial A') (Polynomial S) (Localization.AtPrime Q) (GlobalTheory.KeyOriginCut.originIdeal S)
      (by rw [hmax]; exact hOc) (by intro 𝔔 h1 h2; rw [hmax] at h2; exact hOu 𝔔 h1 h2)
      (GlobalTheory.T.exists_sub_mem_maximalIdeal_etale_over_origin A' E Q hQ)
  haveI hdom : IsDomain (TensorProduct (Polynomial A') (Polynomial S) (Localization.AtPrime Q)) :=
    GlobalTheory.T.isDomain_tensor_atPrime_of_isLocalRing_of_etale (Polynomial A') (Polynomial S) E Q hloc
  haveI : Module.Flat (Polynomial A') (Localization.AtPrime Q) :=
    Module.Flat.trans (Polynomial A') E (Localization.AtPrime Q)
  have hkerX : RingHom.ker (algebraMap (Polynomial A') (Polynomial S)) = 𝔭.map Polynomial.C := by
    change RingHom.ker (Polynomial.mapRingHom f) = _
    rw [Polynomial.ker_mapRingHom, hker]
  have hJ : 𝔭.map ((algebraMap (Polynomial A') (Localization.AtPrime Q)).comp Polynomial.C) =
      (𝔭.map Polynomial.C).map (algebraMap (Polynomial A') (Localization.AtPrime Q)) := by
    rw [Ideal.map_map]
  let g : Localization.AtPrime Q →+* TensorProduct (Polynomial A') (Polynomial S) (Localization.AtPrime Q) :=
    (Algebra.TensorProduct.includeRight : Localization.AtPrime Q →ₐ[Polynomial A'] _).toRingHom
  have hg0 : ∀ y ∈ 𝔭.map ((algebraMap (Polynomial A') (Localization.AtPrime Q)).comp Polynomial.C), g y = 0 := by
    rw [hJ]
    have hle : (𝔭.map Polynomial.C).map (algebraMap (Polynomial A') (Localization.AtPrime Q)) ≤ RingHom.ker g := by
      rw [Ideal.map_le_iff_le_comap]
      intro m hm
      rw [Ideal.mem_comap, RingHom.mem_ker]
      change (Algebra.TensorProduct.includeRight : Localization.AtPrime Q →ₐ[Polynomial A'] _)
        (algebraMap (Polynomial A') (Localization.AtPrime Q) m) = 0
      rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply]
      have : algebraMap (Polynomial A') (Polynomial S) m = 0 := by
        rw [← RingHom.mem_ker, hkerX]; exact hm
      rw [this, TensorProduct.zero_tmul]
    exact fun y hy => hle hy
  have hg1 : ∀ y, g y = 0 → y ∈ 𝔭.map ((algebraMap (Polynomial A') (Localization.AtPrime Q)).comp Polynomial.C) := by
    intro y hy
    rw [hJ]
    exact GlobalTheory.T.flat_tensor_kernel_mem_map_ideal (Polynomial A') (Polynomial S) (Localization.AtPrime Q) _ hkerX y hy
  refine ⟨?_, ?_⟩
  · intro htop
    have h1 := hg0 1 (by rw [htop]; exact Submodule.mem_top)
    rw [map_one] at h1
    exact one_ne_zero h1
  · intro x y hxy
    have h := hg0 _ hxy
    rw [map_mul] at h
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (hg1 x h)
    · exact Or.inr (hg1 y h)

end GlobalTheory.OriginPrimes
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdealExtensionPrime

section

@[expose] public section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.origin_ideal_extension_prime : ∀ (A' : Type) [CommRing A'] [HenselianLocalRing A'] [IsSepClosed (ResidueField A')]
    (𝔭 : Ideal A') [𝔭.IsPrime] (E : Type) [CommRing E] [Algebra (Polynomial A') E]
    [Algebra.Etale (Polynomial A') E] (Q : Ideal E) [Q.IsPrime],
    Q.comap (algebraMap (Polynomial A') E) = GlobalTheory.KeyOriginCut.originIdeal A' →
    (𝔭.map ((algebraMap (Polynomial A') (Localization.AtPrime Q)).comp Polynomial.C)).IsPrime := by
  first | (exact @GlobalTheory.OriginPrimes.origin_primes) | (exact GlobalTheory.OriginPrimes.origin_primes) | (intros; apply GlobalTheory.OriginPrimes.origin_primes <;> assumption)
end
end
