module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdicCompletionQuotientRingEquivStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AssociatedPrimeLocalizationDvrStatement
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
public import Mathlib.RingTheory.AdicCompletion.Exactness
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
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteIntegralClosureOfEssFiniteTypeIntDomain
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherianStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsReducedOfNonZeroDivisorMemJacobsonOfAssociatedStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLtTopOfEssFiniteType
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Integral

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInjectiveAdicCompletionMapOfFinite

section

@[expose] public section

open IsLocalRing

namespace GlobalTheory

theorem adicCompletion_evalₐ_of_val {R : Type} [CommRing R] (I : Ideal R) (x : AdicCompletion I R)
    {n : ℕ} (d : R) (hd : x.val n = Submodule.Quotient.mk d) :
    AdicCompletion.evalₐ I n x = Ideal.Quotient.mk (I ^ n) d := by
  rw [← AdicCompletion.factor_eval_eq_evalₐ I x (by simp), AdicCompletion.eval_apply]
  erw [hd]
  rfl

theorem adicCompletion_val_of_le {R : Type} [CommRing R] (I : Ideal R) (x : AdicCompletion I R)
    {m n : ℕ} (hmn : m ≤ n) (d : R) (hd : x.val n = Submodule.Quotient.mk d) :
    x.val m = Submodule.Quotient.mk d := by
  rw [← x.prop hmn, hd]
  rfl

theorem adicCompletion_injective_ringHom_of_finite
    (D N : Type) [CommRing D] [CommRing N] [IsNoetherianRing D] [Algebra D N]
    [Module.Finite D N] (hinj : Function.Injective (algebraMap D N)) (J : Ideal D) :
    ∃ f : AdicCompletion J D →+* AdicCompletion (J.map (algebraMap D N)) N,
      Function.Injective f := by
  set φ := algebraMap D N with hφ
  have hle : ∀ n : ℕ, J ^ n ≤ ((J.map φ) ^ n).comap φ := fun n => by
    rw [← Ideal.map_pow]; exact Ideal.le_comap_map
  let g : (n : ℕ) → AdicCompletion J D →+* N ⧸ (J.map φ) ^ n := fun n =>
    (Ideal.quotientMap ((J.map φ) ^ n) φ (hle n)).comp (AdicCompletion.evalₐ J n).toRingHom
  have hg : ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorPow (J.map φ) hmn).comp (g n) = g m := by
    intro m n hmn
    ext x
    obtain ⟨d, hd⟩ := Submodule.Quotient.mk_surjective _ (x.val n)
    have hn := adicCompletion_evalₐ_of_val J x d hd.symm
    have hm := adicCompletion_evalₐ_of_val J x d (adicCompletion_val_of_le J x hmn d hd.symm)
    simp only [g, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hn, hm,
      Ideal.quotientMap_mk]
    rfl
  refine ⟨AdicCompletion.liftRingHom _ g hg, ?_⟩
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  have hmap := AdicCompletion.map_injective J (f := Algebra.linearMap D N) hinj
  apply hmap
  rw [map_zero]
  apply AdicCompletion.ext
  intro n
  obtain ⟨d, hd⟩ := Submodule.Quotient.mk_surjective _ (x.val n)
  have h1 := adicCompletion_evalₐ_of_val J x d hd.symm
  have h2 := congrArg (AdicCompletion.evalₐ (J.map φ) n) hx
  rw [AdicCompletion.evalₐ_liftRingHom, map_zero] at h2
  simp only [g, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, h1,
    Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem] at h2
  rw [AdicCompletion.map_val_apply]
  erw [← hd]
  rw [LinearMap.reduceModIdeal_apply]
  refine ((Submodule.Quotient.mk_eq_zero _).2 ?_).trans rfl
  rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, Ideal.map_pow]
  exact h2

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInjectiveAdicCompletionMapOfFiniteStatement

section

@[expose] public section

open IsLocalRing

theorem _root_.GlobalTheory.T.exists_injective_adicCompletion_map_of_finite : ∀ (D N : Type) [CommRing D] [CommRing N] [IsNoetherianRing D] [Algebra D N] [Module.Finite D N], Function.Injective (algebraMap D N) → ∀ J : Ideal D, ∃ f : AdicCompletion J D →+* AdicCompletion (J.map (algebraMap D N)) N, Function.Injective f := by
  first | exact @GlobalTheory.adicCompletion_injective_ringHom_of_finite | exact GlobalTheory.adicCompletion_injective_ringHom_of_finite | (intros; apply GlobalTheory.adicCompletion_injective_ringHom_of_finite <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteIntegralClosureOfEssFiniteTypeIntDomainStatement

section

@[expose] public section

open IsLocalRing

theorem _root_.GlobalTheory.T.finite_integralClosure_of_essFiniteType_int_domain : ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.EssFiniteType ℤ D], Module.Finite D (integralClosure D (FractionRing D)) := by
  first | exact @GlobalTheory.finite_integralClosure_of_essFiniteType_int | exact GlobalTheory.finite_integralClosure_of_essFiniteType_int | (intros; apply GlobalTheory.finite_integralClosure_of_essFiniteType_int <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLtTopOfEssFiniteTypeStatement

section

@[expose] public section

open IsLocalRing

theorem _root_.GlobalTheory.T.ringKrullDim_finite_of_essFiniteType_int : ∀ (D : Type) [CommRing D] [Algebra.EssFiniteType ℤ D], ringKrullDim D < ⊤ := by
  first | exact @GlobalTheory.ringKrullDim_lt_top_of_essFiniteType | exact GlobalTheory.ringKrullDim_lt_top_of_essFiniteType | (intros; apply GlobalTheory.ringKrullDim_lt_top_of_essFiniteType <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdicCompletionReducedOfJacobson

section

@[expose] public section

open IsLocalRing

namespace GlobalTheory.CompletionReduced

theorem map_le_jacobson_of_comap_isMaximal {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : ∀ M : Ideal B, M.IsMaximal → (M.comap f).IsMaximal) (I : Ideal A)
    (hI : I ≤ Ideal.jacobson (⊥ : Ideal A)) : I.map f ≤ Ideal.jacobson (⊥ : Ideal B) := by
  rw [Ideal.jacobson, le_sInf_iff]
  rintro M ⟨-, hM⟩
  rw [Ideal.map_le_iff_le_comap]
  exact hI.trans (sInf_le ⟨bot_le, hf M hM⟩)

theorem exists_lt_of_add_one_le (e : WithBot ℕ∞) (n : ℕ) (h0 : 0 ≤ e) (h : e + 1 ≤ (n : WithBot ℕ∞)) :
    ∃ m : ℕ, m < n ∧ e ≤ (m : WithBot ℕ∞) := by
  induction e using WithBot.recBotCoe with
  | bot => exact absurd h0 (by simp)
  | coe k =>
    induction k using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : ((⊤ + 1 : ℕ∞) : WithBot ℕ∞) ≤ ((n : ℕ∞) : WithBot ℕ∞) := h
      rw [WithBot.coe_le_coe, top_add] at h'
      exact absurd h' (by simp)
    | coe k =>
      refine ⟨k, ?_, le_rfl⟩
      have : ((k + 1 : ℕ) : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) := by exact_mod_cast h
      exact_mod_cast this

theorem isReduced_of_normal (n : ℕ)
    (ih : ∀ m < n, ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.EssFiniteType ℤ D],
      ringKrullDim D ≤ (m : WithBot ℕ∞) → ∀ (J : Ideal D), J ≤ Ideal.jacobson (⊥ : Ideal D) →
        IsReduced (AdicCompletion J D))
    (N : Type) [CommRing N] [IsDomain N] [IsIntegrallyClosed N] [Algebra.EssFiniteType ℤ N]
    (hdimN : ringKrullDim N ≤ (n : WithBot ℕ∞)) (I : Ideal N)
    (hIjac : I ≤ Ideal.jacobson (⊥ : Ideal N)) : IsReduced (AdicCompletion I N) := by
  haveI : IsNoetherianRing N := Algebra.EssFiniteType.isNoetherianRing ℤ N
  by_cases hbot : I = ⊥
  · subst hbot
    exact isReduced_of_injective (AdicCompletion.ofAlgEquiv (⊥ : Ideal N)).symm.toRingEquiv.toRingHom
      (AdicCompletion.ofAlgEquiv (⊥ : Ideal N)).symm.injective
  obtain ⟨x, hxI, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  let R := AdicCompletion I N
  haveI : IsNoetherianRing R := GlobalTheory.T.isNoetherianRing_adicCompletion_of_noetherian N I
  haveI : Module.Flat N R := AdicCompletion.flat_of_isNoetherian I
  have hxR : algebraMap N R x ∈ nonZeroDivisors R := by
    have hxA : IsSMulRegular N x := IsSMulRegular.of_ne_zero hx0
    have h : IsSMulRegular R (algebraMap N R x) := hxA.of_flat
    rw [mem_nonZeroDivisors_iff_right]
    intro y hy
    refine h ?_
    simpa [smul_eq_mul, mul_comm] using hy
  have hxjac : algebraMap N R x ∈ Ideal.jacobson (⊥ : Ideal R) := by
    have h1 : IsAdicComplete I R := AdicCompletion.isAdicComplete (IsNoetherian.noetherian I)
    have h2 : IsAdicComplete (I.map (algebraMap N R)) R := (IsAdicComplete.map_algebraMap_iff _ _).2 h1
    exact IsAdicComplete.le_jacobson_bot (I.map (algebraMap N R)) (Ideal.mem_map_of_mem _ hxI)
  have hredq : ∀ q : Ideal N, q.IsPrime → x ∈ q → IsReduced (R ⧸ q.map (algebraMap N R)) := by
    intro q hq hxq
    obtain ⟨e⟩ := GlobalTheory.T.nonempty_adicCompletion_quotient_ringEquiv N I q
    haveI : IsDomain (N ⧸ q) := Ideal.Quotient.isDomain q
    haveI : Algebra.EssFiniteType N (N ⧸ q) := inferInstance
    haveI hess : @Algebra.EssFiniteType ℤ (N ⧸ q) _ _ (Ring.toIntAlgebra _) := by
      letI := Ring.toIntAlgebra (N ⧸ q)
      haveI : IsScalarTower ℤ N (N ⧸ q) := .of_algebraMap_eq fun z => by simp
      exact Algebra.EssFiniteType.comp ℤ N (N ⧸ q)
    have hj : I.map (Ideal.Quotient.mk q) ≤ Ideal.jacobson (⊥ : Ideal (N ⧸ q)) :=
      map_le_jacobson_of_comap_isMaximal _
        (fun M hM => Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective) I hIjac
    have hd1 : ringKrullDim (N ⧸ q) + 1 ≤ (n : WithBot ℕ∞) := by
      have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hx0)
      have h2 : ringKrullDim (N ⧸ q) ≤ ringKrullDim (N ⧸ Ideal.span {x}) :=
        ringKrullDim_le_of_surjective _
          (Ideal.Quotient.factor_surjective (by rwa [Ideal.span_singleton_le_iff_mem]))
      exact ((add_le_add h2 le_rfl).trans h1).trans hdimN
    obtain ⟨m, hmn, hm⟩ := exists_lt_of_add_one_le _ n ringKrullDim_nonneg_of_nontrivial hd1
    haveI := ih m hmn (N ⧸ q) hm _ hj
    exact isReduced_of_injective e.toRingHom e.injective
  refine GlobalTheory.T.isReduced_of_nonZeroDivisor_mem_jacobson_of_assocPrimes R (algebraMap N R x) hxR hxjac ?_
  intro P _ hP
  obtain ⟨h1, -⟩ := GlobalTheory.T.associated_prime_localization_dvr N R x hx0 hredq P hP
  exact h1

theorem isReduced_of_dim_le : ∀ (n : ℕ) (D : Type) [CommRing D] [IsDomain D] [Algebra.EssFiniteType ℤ D],
    ringKrullDim D ≤ (n : WithBot ℕ∞) → ∀ (J : Ideal D), J ≤ Ideal.jacobson (⊥ : Ideal D) →
      IsReduced (AdicCompletion J D) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro D _ _ _ hdim J hJ
  haveI : IsNoetherianRing D := Algebra.EssFiniteType.isNoetherianRing ℤ D

  let N := integralClosure D (FractionRing D)
  haveI : Module.Finite D N := GlobalTheory.T.finite_integralClosure_of_essFiniteType_int_domain D
  haveI : IsIntegrallyClosed N := integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing D)
  have hinj : Function.Injective (algebraMap D N) := by
    intro a b hab
    have := congrArg (fun y : N => (y : FractionRing D)) hab
    exact IsFractionRing.injective D (FractionRing D) this
  have hdimN : ringKrullDim N ≤ (n : WithBot ℕ∞) := by
    rw [ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective hinj]; exact hdim
  haveI : Algebra.EssFiniteType D N := inferInstance
  haveI hessN : @Algebra.EssFiniteType ℤ N _ _ (Ring.toIntAlgebra _) := by
    letI := Ring.toIntAlgebra N
    haveI : IsScalarTower ℤ D N := .of_algebraMap_eq fun z => by simp
    exact Algebra.EssFiniteType.comp ℤ D N
  have hIjac : J.map (algebraMap D N) ≤ Ideal.jacobson (⊥ : Ideal N) :=
    map_le_jacobson_of_comap_isMaximal _
      (fun M hM => Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := D) M) J hJ
  obtain ⟨f, hf⟩ := GlobalTheory.T.exists_injective_adicCompletion_map_of_finite D N hinj J
  haveI := isReduced_of_normal n ih N hdimN _ hIjac
  exact isReduced_of_injective f hf

theorem isReduced_adicCompletion : ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.EssFiniteType ℤ D]
    (J : Ideal D), J ≤ Ideal.jacobson (⊥ : Ideal D) → IsReduced (AdicCompletion J D) := by
  intro D _ _ _ J hJ
  have hlt := GlobalTheory.T.ringKrullDim_finite_of_essFiniteType_int D
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ringKrullDim D ≤ (m : WithBot ℕ∞) := by
    generalize ringKrullDim D = e at hlt ⊢
    induction e using WithBot.recBotCoe with
    | bot => exact ⟨0, bot_le⟩
    | coe k =>
      induction k using ENat.recTopCoe with
      | top => exact absurd hlt (by simp)
      | coe k => exact ⟨k, le_rfl⟩
  exact isReduced_of_dim_le m D hm J hJ

end GlobalTheory.CompletionReduced
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdicCompletionReducedOfJacobsonStatement

section

@[expose] public section

open IsLocalRing

theorem _root_.GlobalTheory.T.adic_completion_reduced_of_jacobson : ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.EssFiniteType ℤ D] (J : Ideal D), J ≤ Ideal.jacobson (⊥ : Ideal D) → IsReduced (AdicCompletion J D) := by
  first | exact @GlobalTheory.CompletionReduced.isReduced_adicCompletion | exact GlobalTheory.CompletionReduced.isReduced_adicCompletion | (intros; apply GlobalTheory.CompletionReduced.isReduced_adicCompletion <;> assumption)
end
end
