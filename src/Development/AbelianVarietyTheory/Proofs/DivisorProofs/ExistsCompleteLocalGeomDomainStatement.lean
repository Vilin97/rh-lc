module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRingEquivAdicCompletionLocalizationProd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRegularLocalRingAdicCompletion
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherian
public import ReciprocityTheory.CommutativeAlgebra.MaximalIdealSquares.RingKrullDimQuotientSpanSingletonAddOne
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowPowMemRangeIncludeRight

section

@[expose] public section

namespace GlobalTheory.PowerInRangeTensorRight

open TensorProduct

theorem exists_pow_pow_mem_range_includeRight (k K B : Type) [Field k] [Field K] [Algebra k K]
    [IsPurelyInseparable k K] [CommRing B] [Nontrivial B] [Algebra k B] (q : ℕ) [ExpChar k q]
    (z : TensorProduct k K B) :
    ∃ n : ℕ, z ^ q ^ n ∈
      AlgHom.range (Algebra.TensorProduct.includeRight : B →ₐ[k] TensorProduct k K B) := by
  rcases subsingleton_or_nontrivial (TensorProduct k K B) with hs | hnt
  · exact ⟨0, by rw [Subsingleton.elim (z ^ q ^ 0) 0]; exact zero_mem _⟩
  have : ExpChar (TensorProduct k K B) q :=
    expChar_of_injective_algebraMap (algebraMap k (TensorProduct k K B)).injective q
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul x b =>
    obtain ⟨n, c, hc⟩ := IsPurelyInseparable.pow_mem k q x
    refine ⟨n, (AlgHom.mem_range _).mpr ⟨c • b ^ q ^ n, ?_⟩⟩
    rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_pow, ← hc,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  | add x y hx hy =>
    obtain ⟨n1, h1⟩ := hx
    obtain ⟨n2, h2⟩ := hy
    refine ⟨n1 + n2, ?_⟩
    have e1 : x ^ q ^ (n1 + n2) = (x ^ q ^ n1) ^ q ^ n2 := by rw [pow_add, pow_mul]
    have e2 : y ^ q ^ (n1 + n2) = (y ^ q ^ n2) ^ q ^ n1 := by rw [pow_add, mul_comm, pow_mul]
    rw [add_pow_expChar_pow, e1, e2]
    exact add_mem (pow_mem h1 _) (pow_mem h2 _)

end GlobalTheory.PowerInRangeTensorRight
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentTensorEqZeroOrOneOfIsPurelyInseparable

section

@[expose] public section

open IsLocalRing
open scoped TensorProduct

namespace GlobalTheory

theorem pow_mem_range_includeRight_of_isPurelyInseparable (k K B : Type) [Field k] [Field K]
    [Algebra k K] [IsPurelyInseparable k K] [CommRing B] [Nontrivial B] [Algebra k B]
    (q : ℕ) [ExpChar k q] (z : K ⊗[k] B) :
    ∃ n : ℕ, z ^ q ^ n ∈
      (Algebra.TensorProduct.includeRight : B →ₐ[k] K ⊗[k] B).range := by
  first
  | exact @_root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight
  | exact _root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight
  | (apply _root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight ..)

theorem idempotent_tensor_eq_zero_or_one_of_isPurelyInseparable (k K B : Type) [Field k] [Field K]
    [Algebra k K] [IsPurelyInseparable k K] [CommRing B] [IsLocalRing B] [Algebra k B]
    (e : K ⊗[k] B) (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  have hinj : Function.Injective (Algebra.TensorProduct.includeRight : B →ₐ[k] K ⊗[k] B) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap k K).injective
  obtain ⟨n, b, hb⟩ :=
    pow_mem_range_includeRight_of_isPurelyInseparable k K B (ringExpChar k) e
  have hpos : ringExpChar k ^ n ≠ 0 := (pow_pos (expChar_pos k _) n).ne'
  have h1 : e ^ (ringExpChar k ^ n) = e := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos
    rw [hm]; exact he.pow_succ_eq m
  rw [h1] at hb
  have hb' : (Algebra.TensorProduct.includeRight : B →ₐ[k] K ⊗[k] B) b = e := hb
  have hbi : b * b = b := by
    apply hinj
    rw [map_mul, hb']; exact he
  rcases isUnit_or_isUnit_one_sub_self b with hu | hu
  · right
    have : b = 1 := hu.mul_left_cancel (by rw [hbi, mul_one])
    rw [← hb', this, map_one]
  · left
    have : b = 0 := hu.mul_left_cancel (by rw [sub_mul, hbi, one_mul, sub_self, mul_zero])
    rw [← hb', this, map_zero]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentTensorEqZeroOrOneOfIsPurelyInseparableStatement

section

@[expose] public section

open IsLocalRing
open scoped TensorProduct

theorem _root_.GlobalTheory.T.idempotent_tensor_eq_zero_or_one_of_isPurelyInseparable' : ∀ (k K B : Type) [Field k] [Field K] [Algebra k K] [IsPurelyInseparable k K] [CommRing B] [IsLocalRing B] [Algebra k B] (e : K ⊗[k] B), IsIdempotentElem e → e = 0 ∨ e = 1 := by
  first | exact @GlobalTheory.idempotent_tensor_eq_zero_or_one_of_isPurelyInseparable | exact GlobalTheory.idempotent_tensor_eq_zero_or_one_of_isPurelyInseparable | (intros; apply GlobalTheory.idempotent_tensor_eq_zero_or_one_of_isPurelyInseparable <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularLocalRingAtPrimeLocalizationTensor

section

@[expose] public section

open IsLocalRing
open scoped TensorProduct

namespace GlobalTheory

theorem isRegularLocalRing_atPrime_of_ringEquiv_isLocalization {B T T' : Type} [CommRing B]
    [IsRegularRing B] [CommRing T] [CommRing T'] [Algebra B T'] (M : Submonoid B)
    [IsLocalization M T'] (e : T ≃+* T') (𝔫 : Ideal T) [𝔫.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime 𝔫) := by
  letI : Algebra B T := ((e.symm : T' →+* T).comp (algebraMap B T')).toAlgebra
  let e' : T' ≃ₐ[B] T := AlgEquiv.ofRingEquiv (f := e.symm) (fun x => rfl)
  haveI : IsLocalization M T := IsLocalization.isLocalization_of_algEquiv M e'
  haveI : IsLocalization.AtPrime (Localization.AtPrime 𝔫) (𝔫.comap (algebraMap B T)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M (Localization.AtPrime 𝔫) 𝔫
  haveI : IsRegularLocalRing (Localization.AtPrime (𝔫.comap (algebraMap B T))) :=
    IsRegularRing.isRegularLocalRing_localization _
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv (𝔫.comap (algebraMap B T)).primeCompl
      (Localization.AtPrime (𝔫.comap (algebraMap B T))) (Localization.AtPrime 𝔫)).toRingEquiv

theorem isRegularLocalRing_atPrime_localization_tensor : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (r : ℕ) (𝔪 : Ideal (MvPolynomial (Fin r) k)) [𝔪.IsPrime] (𝔫 : Ideal (Localization.AtPrime 𝔪 ⊗[k] K)) [𝔫.IsPrime], IsRegularLocalRing (Localization.AtPrime 𝔫) := by
  intro k K _ _ _ r 𝔪 _ 𝔫 _
  letI : Algebra (MvPolynomial (Fin r) k ⊗[k] K)
      (Localization.AtPrime 𝔪 ⊗[MvPolynomial (Fin r) k] (MvPolynomial (Fin r) k ⊗[k] K)) :=
    Algebra.TensorProduct.rightAlgebra
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (MvPolynomial (Fin r) k ⊗[k] K) 𝔪.primeCompl)
      (Localization.AtPrime 𝔪 ⊗[MvPolynomial (Fin r) k] (MvPolynomial (Fin r) k ⊗[k] K)) :=
    IsLocalization.tensorRight (Localization.AtPrime 𝔪) 𝔪.primeCompl
  let h : (MvPolynomial (Fin r) k ⊗[k] K) ≃+* MvPolynomial (Fin r) K :=
    (Algebra.TensorProduct.comm k (MvPolynomial (Fin r) k) K).toRingEquiv.trans
      (MvPolynomial.algebraTensorAlgEquiv k K).toRingEquiv
  haveI := IsLocalization.isLocalization_of_base_ringEquiv
    (Algebra.algebraMapSubmonoid (MvPolynomial (Fin r) k ⊗[k] K) 𝔪.primeCompl)
    (Localization.AtPrime 𝔪 ⊗[MvPolynomial (Fin r) k] (MvPolynomial (Fin r) k ⊗[k] K)) h
  letI : Algebra (MvPolynomial (Fin r) K)
      (Localization.AtPrime 𝔪 ⊗[MvPolynomial (Fin r) k] (MvPolynomial (Fin r) k ⊗[k] K)) :=
    ((algebraMap (MvPolynomial (Fin r) k ⊗[k] K) _).comp h.symm.toRingHom).toAlgebra
  exact isRegularLocalRing_atPrime_of_ringEquiv_isLocalization
    (Submonoid.map h (Algebra.algebraMapSubmonoid (MvPolynomial (Fin r) k ⊗[k] K) 𝔪.primeCompl))
    (Algebra.TensorProduct.cancelBaseChange k (MvPolynomial (Fin r) k) (Localization.AtPrime 𝔪)
      (Localization.AtPrime 𝔪) K).symm.toRingEquiv 𝔫

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularLocalRingAtPrimeLocalizationTensorStatement

section

@[expose] public section

open IsLocalRing
open scoped TensorProduct

theorem _root_.GlobalTheory.T.isRegularLocalRing_localization_atPrime_tensor_field : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (r : ℕ) (𝔪 : Ideal (MvPolynomial (Fin r) k)) [𝔪.IsPrime] (𝔫 : Ideal (Localization.AtPrime 𝔪 ⊗[k] K)) [𝔫.IsPrime], IsRegularLocalRing (Localization.AtPrime 𝔫) := by
  first | exact @GlobalTheory.isRegularLocalRing_atPrime_localization_tensor | exact GlobalTheory.isRegularLocalRing_atPrime_localization_tensor | (intros; apply GlobalTheory.isRegularLocalRing_atPrime_localization_tensor <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteLocalGeomDomain

section

@[expose] public section

open IsLocalRing
open scoped TensorProduct

namespace GlobalTheory.SepRing




theorem isDomain_tensor_of_reg (k K S : Type) [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsPurelyInseparable k K] [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] [Algebra k S]
    (hreg : ∀ (𝔫 : Ideal (S ⊗[k] K)) [𝔫.IsPrime], IsRegularLocalRing (Localization.AtPrime 𝔫)) :
    IsDomain (K ⊗[k] AdicCompletion (maximalIdeal S) S) := by
  have hinj : Function.Injective (algebraMap S (S ⊗[k] K)) :=
    Algebra.TensorProduct.includeLeft_injective (R := k) (S := k) (A := S) (B := K)
      (algebraMap k K).injective
  have hker : RingHom.ker (algebraMap S (S ⊗[k] K)) ≤ maximalIdeal S := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    rw [hinj (hx.trans (map_zero _).symm)]
    exact zero_mem _
  obtain ⟨𝔫, h𝔫max, h𝔫⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := S ⊗[k] K)
    (maximalIdeal S) hker
  haveI := h𝔫max.isPrime
  obtain ⟨S', _, e, -⟩ := GlobalTheory.CompletionFactor.exists_ringEquiv_completion_prod S (S ⊗[k] K)
    (Localization.AtPrime 𝔫) 𝔫 h𝔫
  haveI : IsRegularLocalRing (Localization.AtPrime 𝔫) := hreg 𝔫
  haveI : IsRegularLocalRing (AdicCompletion (maximalIdeal (Localization.AtPrime 𝔫))
      (Localization.AtPrime 𝔫)) := GlobalTheory.RegularCompletion.isRegularLocalRing_adicCompletion _
  haveI hdom : IsDomain (AdicCompletion (maximalIdeal (Localization.AtPrime 𝔫))
      (Localization.AtPrime 𝔫)) := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isDomain _
  let f : K ⊗[k] AdicCompletion (maximalIdeal S) S ≃+* _ :=
    (Algebra.TensorProduct.comm k K (AdicCompletion (maximalIdeal S) S)).toRingEquiv.trans
    ((Algebra.TensorProduct.cancelBaseChange k S (AdicCompletion (maximalIdeal S) S)
      (AdicCompletion (maximalIdeal S) S) K).symm.toRingEquiv.trans e)
  have hS' : Subsingleton S' := by
    have hid : IsIdempotentElem (f.symm (0, 1)) := by
      show f.symm (0,1) * f.symm (0,1) = f.symm (0,1)
      rw [← map_mul]; simp
    rcases GlobalTheory.T.idempotent_tensor_eq_zero_or_one_of_isPurelyInseparable' k K (AdicCompletion (maximalIdeal S) S) (f.symm (0, 1)) hid with h | h
    · have h2 := congrArg (fun z => (f z).2) h
      simp at h2
      exact subsingleton_of_zero_eq_one h2.symm
    · have h2 := congrArg (fun z => (f z).1) h
      simp at h2
  exact Function.Injective.isDomain ((RingHom.fst _ _).comp f.toRingHom) (by
    intro x y hxy
    apply f.injective
    exact Prod.ext hxy (Subsingleton.elim _ _))

end GlobalTheory.SepRing

namespace GlobalTheory.SepRing




theorem exists_complete_local_geomDomain : ∀ (k k' : Type) [Field k] [CommRing k'] [IsDomain k']
    [Algebra k k'], Module.Finite k k' → ∃ (C : Type) (_ : CommRing C) (_ : IsLocalRing C)
    (_ : IsNoetherianRing C) (_ : Algebra k C), IsAdicComplete (maximalIdeal C) C ∧
    Nonempty (k' →ₐ[k] ResidueField C) ∧ ∀ (K : Type) [Field K] [Algebra k K],
    FiniteDimensional k K → IsPurelyInseparable k K → IsDomain (K ⊗[k] C) := by
  intro k k' _ _ _ _ hfin
  haveI : Algebra.FiniteType k k' := inferInstance
  obtain ⟨r, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp this
  have hk' : IsField k' :=
    (Algebra.IsIntegral.isField_iff_isField (algebraMap k k').injective).mp (Field.toIsField k)
  letI : Field k' := hk'.toField
  let 𝔪 : Ideal (MvPolynomial (Fin r) k) := RingHom.ker φ.toRingHom
  haveI h𝔪 : 𝔪.IsMaximal := RingHom.ker_isMaximal_of_surjective φ.toRingHom hφ
  let S := Localization.AtPrime 𝔪
  haveI : IsNoetherianRing S := IsLocalization.isNoetherianRing 𝔪.primeCompl S inferInstance
  refine ⟨AdicCompletion (maximalIdeal S) S, inferInstance, inferInstance,
    GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion S _, inferInstance, inferInstance, ?_, ?_⟩
  · let C := AdicCompletion (maximalIdeal S) S
    let g : MvPolynomial (Fin r) k →ₐ[k] ResidueField C :=
      IsScalarTower.toAlgHom k (MvPolynomial (Fin r) k) (ResidueField C)
    have hg : ∀ a ∈ 𝔪, g a = 0 := by
      intro a ha
      have h1 : algebraMap (MvPolynomial (Fin r) k) S a ∈ maximalIdeal S := by
        rw [← Localization.AtPrime.map_eq_maximalIdeal]; exact Ideal.mem_map_of_mem _ ha
      have h2 : algebraMap S C (algebraMap _ S a) ∈ maximalIdeal C := by
        rw [AdicCompletion.maximalIdeal_eq_map]; exact Ideal.mem_map_of_mem _ h1
      show algebraMap _ (ResidueField C) a = 0
      rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin r) k) C (ResidueField C),
        IsScalarTower.algebraMap_apply (MvPolynomial (Fin r) k) S C]
      exact (residue_eq_zero_iff _).mpr h2
    exact ⟨(Ideal.Quotient.liftₐ 𝔪 g hg).comp
      (Ideal.quotientKerAlgEquivOfSurjective hφ).symm.toAlgHom⟩
  · intro K _ _ hK hpi
    exact isDomain_tensor_of_reg k K S (fun 𝔫 _ => GlobalTheory.T.isRegularLocalRing_localization_atPrime_tensor_field k K r 𝔪 𝔫)

end GlobalTheory.SepRing
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteLocalGeomDomainStatement

section

@[expose] public section

open IsLocalRing
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_complete_local_geomDomain' : ∀ (k k' : Type) [Field k] [CommRing k'] [IsDomain k'] [Algebra k k'], Module.Finite k k' → ∃ (C : Type) (_ : CommRing C) (_ : IsLocalRing C) (_ : IsNoetherianRing C) (_ : Algebra k C), IsAdicComplete (maximalIdeal C) C ∧ Nonempty (k' →ₐ[k] ResidueField C) ∧ ∀ (K : Type) [Field K] [Algebra k K], FiniteDimensional k K → IsPurelyInseparable k K → IsDomain (K ⊗[k] C) := by
  first | exact @GlobalTheory.SepRing.exists_complete_local_geomDomain | exact GlobalTheory.SepRing.exists_complete_local_geomDomain | (intros; apply GlobalTheory.SepRing.exists_complete_local_geomDomain <;> assumption)
end
end
