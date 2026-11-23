module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Ideal.Height
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
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleOfEtaleAtHeightOnePrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeOfEtalePuncturedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeOfIsIntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtPrimeTensorIsDomainIsIntegrallyClosedFaithfulS

section

@[expose] public section

open IsLocalRing

namespace GlobalTheory

theorem atPrime_tensor_isDomain_isIntegrallyClosed_faithfulSMul : ∀ (R A : Type) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra R A] [FaithfulSMul R A] (p : Ideal R) [p.IsPrime], IsDomain (TensorProduct R (Localization.AtPrime p) A) ∧ IsIntegrallyClosed (TensorProduct R (Localization.AtPrime p) A) ∧ FaithfulSMul (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A) := by
  intro R A _ _ _ _ _ _ _ p _
  set Rp := Localization.AtPrime p
  set B := TensorProduct R Rp A
  letI : Algebra A B := Algebra.TensorProduct.rightAlgebra
  have hpush : Algebra.IsPushout R A Rp B := TensorProduct.isPushout'
  haveI hloc : IsLocalization (Algebra.algebraMapSubmonoid A p.primeCompl) B :=
    (Algebra.isLocalization_iff_isPushout p.primeCompl Rp).mpr hpush
  have hinj : Function.Injective (algebraMap R A) := FaithfulSMul.algebraMap_injective R A
  have hle : Algebra.algebraMapSubmonoid A p.primeCompl ≤ nonZeroDivisors A := by
    rintro _ ⟨r, hr, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero ?_
    intro h0
    apply hr
    have : r = 0 := hinj (by simpa using h0)
    rw [this]; exact p.zero_mem
  haveI hdom : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors B hle
  refine ⟨hdom, isIntegrallyClosed_of_isLocalization B _ hle, ?_⟩
  have hAB : Function.Injective (algebraMap A B) := IsLocalization.injective B hle
  refine (faithfulSMul_iff_algebraMap_injective Rp B).mpr ?_
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl x
  have hcomp : ∀ r : R, algebraMap Rp B (algebraMap R Rp r) = algebraMap A B (algebraMap R A r) := by
    intro r
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have h1 : algebraMap Rp B (algebraMap R Rp r) = 0 := by
    have := congrArg (algebraMap Rp B) (IsLocalization.mk'_spec Rp r s)
    rw [map_mul, hx, zero_mul] at this
    exact this.symm
  rw [hcomp] at h1
  have hr : r = 0 := hinj ((hAB (h1.trans (map_zero _).symm)).trans (map_zero _).symm)
  simp [hr]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleFractionFieldOfEtaleHeightOne

section

@[expose] public section

open IsLocalRing

namespace GlobalTheory

theorem etale_fractionField_of_etale_height_one :
    ∀ (R A : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R] [CommRing A]
      [Algebra R A], ¬ IsField R →
      (∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
        Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) →
      Algebra.Etale (Localization.AtPrime (⊥ : Ideal R))
        (TensorProduct R (Localization.AtPrime (⊥ : Ideal R)) A) := by
  intro R A _ _ _ _ _ _ hR h

  have hm : maximalIdeal R ≠ ⊥ := fun hm => hR ((isField_iff_maximalIdeal_eq).mpr hm)
  obtain ⟨x, hxm, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  obtain ⟨P, hPmin, -⟩ := Ideal.exists_minimalPrimes_le
    ((Ideal.span_singleton_le_iff_mem _).mpr hxm)
  haveI hP : P.IsPrime := hPmin.1.1
  have hxP : x ∈ P := (Ideal.span_singleton_le_iff_mem _).mp hPmin.1.2
  have hPne : P ≠ ⊥ := fun e => hx0 (by simpa [e] using hxP)
  haveI : (Ideal.span {x}).IsPrincipal := ⟨⟨x, rfl⟩⟩
  have h1 : P.height = 1 := le_antisymm
    (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hPmin)
    (Order.one_le_iff_ne_zero.mpr (fun e => hPne (Ideal.height_eq_zero_iff_eq_bot.mp e)))
  haveI := h P h1
  set K := Localization.AtPrime (⊥ : Ideal R)
  have hunit : ∀ y : P.primeCompl, IsUnit (algebraMap R K y) := by
    intro y
    have hy : (y : R) ∈ (⊥ : Ideal R).primeCompl := by
      intro hb
      have hb' : (y : R) = 0 := Ideal.mem_bot.mp hb
      exact y.2 (by rw [hb']; exact P.zero_mem)
    exact IsLocalization.map_units K (⟨y, hy⟩ : (⊥ : Ideal R).primeCompl)
  letI : Algebra (Localization.AtPrime P) K :=
    (IsLocalization.lift (M := P.primeCompl) (S := Localization.AtPrime P) hunit).toAlgebra
  haveI : IsScalarTower R (Localization.AtPrime P) K :=
    IsScalarTower.of_algebraMap_eq (fun r => by
      change _ = IsLocalization.lift (M := P.primeCompl) (S := Localization.AtPrime P) hunit _
      rw [IsLocalization.lift_eq])
  exact Algebra.Etale.of_equiv
    (Algebra.TensorProduct.cancelBaseChange R (Localization.AtPrime P) K K A)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalizationAtPrimeOfHeightOne

section

@[expose] public section

open IsLocalRing

namespace GlobalTheory

theorem etale_localization_atPrime_of_height_one :
    ∀ (R A : Type) [CommRing R] [IsNoetherianRing R] [IsDomain R] [CommRing A] [Algebra R A]
      (p : Ideal R) [p.IsPrime],
      (∀ (P : Ideal R) [P.IsPrime], P.height = 1 →
        Algebra.Etale (Localization.AtPrime P) (TensorProduct R (Localization.AtPrime P) A)) →
      ∀ (q : Ideal (Localization.AtPrime p)) [q.IsPrime], q.height = 1 →
        Algebra.Etale (Localization.AtPrime q)
          (TensorProduct (Localization.AtPrime p) (Localization.AtPrime q)
            (TensorProduct R (Localization.AtPrime p) A)) := by
  intro R A _ _ _ _ _ p _ H q _ hq
  set P : Ideal R := q.comap (algebraMap R (Localization.AtPrime p)) with hPdef
  haveI : P.IsPrime := Ideal.comap_isPrime _ _
  have hP : P.height = 1 := by
    rw [← hq, ← IsLocalization.height_under p.primeCompl q]
  haveI := H P hP
  haveI : IsLocalization.AtPrime (Localization.AtPrime q) P :=
    IsLocalization.isLocalization_atPrime_localization_atPrime p.primeCompl q
  let e : Localization.AtPrime P ≃ₐ[R] Localization.AtPrime q :=
    IsLocalization.algEquiv P.primeCompl _ _
  letI : Algebra (Localization.AtPrime P) (Localization.AtPrime q) := e.toRingHom.toAlgebra
  haveI : IsScalarTower R (Localization.AtPrime P) (Localization.AtPrime q) :=
    IsScalarTower.of_algebraMap_eq (fun r => (e.commutes r).symm)
  haveI : Algebra.Etale (Localization.AtPrime q)
      (TensorProduct (Localization.AtPrime P) (Localization.AtPrime q)
        (TensorProduct R (Localization.AtPrime P) A)) :=
    Algebra.Etale.baseChange _ _ _
  let e1 := Algebra.TensorProduct.cancelBaseChange R (Localization.AtPrime P)
    (Localization.AtPrime q) (Localization.AtPrime q) A
  let e2 := Algebra.TensorProduct.cancelBaseChange R (Localization.AtPrime p)
    (Localization.AtPrime q) (Localization.AtPrime q) A
  exact Algebra.Etale.of_equiv (e1.trans e2.symm)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleOfEtaleHeightOneOfRegularLocalRing

section

@[expose] public section

open IsLocalRing

namespace GlobalTheory.BranchPurity

theorem dim_lt (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (p : Ideal R) [p.IsPrime]
    (hp : p ≠ maximalIdeal R) : ringKrullDim (Localization.AtPrime p) < ringKrullDim R := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p, ← maximalIdeal_height_eq_ringKrullDim]
  exact WithBot.coe_lt_coe.mpr (Ideal.height_strict_mono_of_isPrime_of_isPrime
    (lt_of_le_of_ne (le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)) hp))

theorem regular_localization (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R) (p : Ideal R) [p.IsPrime] :
    ((maximalIdeal (Localization.AtPrime p)).spanFinrank : WithBot ℕ∞) =
      ringKrullDim (Localization.AtPrime p) := by
  haveI : IsRegularLocalRing R := (isRegularLocalRing_iff R).mpr hR
  haveI : IsRegularRing R := GlobalTheory.isRegularRing_of_isRegularLocalRing R
  exact (IsRegularRing.isRegularLocalRing_localization p).spanFinrank_maximalIdeal

theorem integrallyClosed (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R) : IsIntegrallyClosed R := by
  haveI : IsRegularLocalRing R := (isRegularLocalRing_iff R).mpr hR
  exact (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing R).2

theorem not_isField_localization (R : Type) [CommRing R] [IsDomain R] (p : Ideal R) [p.IsPrime]
    (hp : p ≠ ⊥) : ¬ IsField (Localization.AtPrime p) := by
  rw [IsLocalRing.isField_iff_maximalIdeal_eq, ← Localization.AtPrime.map_eq_maximalIdeal]
  intro h
  apply hp
  have hinj : Function.Injective (algebraMap R (Localization.AtPrime p)) :=
    IsLocalization.injective (Localization.AtPrime p) p.primeCompl_le_nonZeroDivisors
  exact (Ideal.map_eq_bot_iff_of_injective hinj).mp h

theorem finiteRing_sq_sub_mul_sq_eq_of_card : ∀ (n : ℕ) (R A : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R] [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra R A] [Module.Finite R A] [FaithfulSMul R A], (maximalIdeal R).spanFinrank = n → (((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R) → ¬ IsField R → (∀ (p : Ideal R) [p.IsPrime], p.height = 1 → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → Algebra.Etale R A := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro R A _ _ _ _ _ _ _ _ _ _ hn hR hF hA
  haveI : IsIntegrallyClosed R := integrallyClosed R hR
  have hfree : Module.Free R A := by
    by_cases h2 : ringKrullDim R ≤ 2
    · exact GlobalTheory.PurFree.free_of_isIntegrallyClosed R A hR h2
    · refine GlobalTheory.T.free_of_etale_on_punctured_spectrum R A hR ?_ ?_
      · rw [not_le] at h2
        have h2' : ((2 : ℕ) : WithBot ℕ∞) < ringKrullDim R := by exact_mod_cast h2
        rw [← hR] at h2' ⊢
        have : 2 < (maximalIdeal R).spanFinrank := by exact_mod_cast h2'
        exact_mod_cast this
      · intro p _ hp
        by_cases hb : p = ⊥
        · subst hb
          exact GlobalTheory.etale_fractionField_of_etale_height_one R A hF hA
        obtain ⟨hdom, hic, hfs⟩ := GlobalTheory.atPrime_tensor_isDomain_isIntegrallyClosed_faithfulSMul R A p
        have hlt := dim_lt R p hp
        have hreg := regular_localization R hR p
        refine IH (maximalIdeal (Localization.AtPrime p)).spanFinrank ?_ (Localization.AtPrime p)
          (TensorProduct R (Localization.AtPrime p) A) rfl hreg (not_isField_localization R p hb)
          (GlobalTheory.etale_localization_atPrime_of_height_one R A p hA)
        rw [← hreg, ← hR, hn] at hlt
        exact_mod_cast hlt
  exact GlobalTheory.PurityDisc.etale_of_etale_height_one R A hF hA

theorem etale_of_etale_height_one : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R] [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra R A] [Module.Finite R A] [FaithfulSMul R A], (((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R) → 1 ≤ ringKrullDim R → ¬ IsField R → (∀ (p : Ideal R) [p.IsPrime], p.height = 1 → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → Algebra.Etale R A := by
  intro R A _ _ _ _ _ _ _ _ _ _ hR _ hF hA
  exact finiteRing_sq_sub_mul_sq_eq_of_card _ R A rfl hR hF hA

end GlobalTheory.BranchPurity
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleOfEtaleHeightOneOfRegularLocalRingStatement

section

@[expose] public section

open IsLocalRing

theorem _root_.GlobalTheory.T.etale_of_etale_height_one_of_regularLocalRing : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R] [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra R A] [Module.Finite R A] [FaithfulSMul R A], (((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R) → 1 ≤ ringKrullDim R → ¬ IsField R → (∀ (p : Ideal R) [p.IsPrime], p.height = 1 → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → Algebra.Etale R A := by
  first | exact @GlobalTheory.BranchPurity.etale_of_etale_height_one | exact GlobalTheory.BranchPurity.etale_of_etale_height_one | (intros; apply GlobalTheory.BranchPurity.etale_of_etale_height_one <;> assumption)
end
end
