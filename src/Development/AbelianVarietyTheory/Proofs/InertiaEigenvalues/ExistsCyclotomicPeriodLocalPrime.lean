module

public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAinfFrobeniusIterateEqXiMulStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinExt
public import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AwayOfInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Acris0TorsionFree
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisFrobeniusFontaineTEqMulStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisLogTeichmullerUniqueGaloisFrobeniusBdRStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLogTeichmullerAcrisEqMuMulUnitStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineTIsUnitBcrisAndUniformizerBdRPlus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPrimitiveTiltedRootOfUnityLocalPeriodRingsDataStatement
import Mathlib.Tactic.Polynomial.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusEigenFilOneIsUnitExactDegreeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFilPIffEvPt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BcrisFrobeniusFixedFilZeroEqQp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPrimitiveTiltedRootOfUnityLocalPeriodRingsData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalPeriodRingsDataUnramifiedLawsStatement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitFrobeniusIterateProductEq

section

@[expose] public section

namespace GlobalTheory.FrobeniusProduct

theorem exists_adic_limit {A : Type} [CommRing A] (I : Ideal A) [IsPrecomplete I A]
    (s : ℕ → A) (hs : ∀ r : ℕ, ∃ N : ℕ, ∀ m ≥ N, s (m + 1) - s m ∈ I ^ r) :
    ∃ L : A, ∀ r : ℕ, ∃ N : ℕ, ∀ m ≥ N, s m - L ∈ I ^ r := by
  have hsm : ∀ J : Ideal A, J • (⊤ : Submodule A A) = J := fun J => by simp
  choose N hN using hs
  have tele : ∀ r a b, (∀ k ≥ a, s (k + 1) - s k ∈ I ^ r) → a ≤ b → s b - s a ∈ I ^ r := by
    intro r a b h hab
    induction b, hab using Nat.le_induction with
    | base => simp
    | succ b hab ih =>
      have := (I ^ r).add_mem (h b hab) ih
      convert this using 1
      ring
  set N' : ℕ → ℕ := fun r => ∑ j ∈ Finset.range (r + 1), N j with hN'
  have hN'ge : ∀ r, N r ≤ N' r := fun r =>
    Finset.single_le_sum (f := N) (fun j _ => Nat.zero_le _) (Finset.self_mem_range_succ r)
  have hN'mono : Monotone N' := fun a b hab =>
    Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_succ hab))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := I) (M := A) inferInstance
    (f := fun r => s (N' r)) (by
      intro m n hmn
      rw [SModEq.sub_mem, hsm]
      have := tele m (N' m) (N' n) (fun k hk => hN m k (le_trans (hN'ge m) hk)) (hN'mono hmn)
      have := (I ^ m).neg_mem this
      simpa using this)
  refine ⟨L, fun r => ⟨N' r, fun m hm => ?_⟩⟩
  have h1 := tele r (N' r) m (fun k hk => hN r k (le_trans (hN'ge r) hk)) hm
  have h2 : s (N' r) - L ∈ I ^ r := by
    have := hL r
    rw [SModEq.sub_mem, hsm] at this
    exact this
  have := (I ^ r).add_mem h1 h2
  convert this using 1
  ring

theorem exists_unit_iterate_mul_eq :
    ∀ (A : Type) [CommRing A] (p : ℕ), IsAdicComplete (Ideal.span {(p : A)}) A →
      ∀ (φ : A →+* A) (u : A), IsUnit u →
        (∀ r : ℕ, ∃ M : ℕ, ∀ m ≥ M, (⇑φ)^[m] u - 1 ∈ Ideal.span {(p : A)} ^ r) →
          ∀ n : ℕ, 0 < n → ∃ c : A, IsUnit c ∧ (⇑φ)^[n] c * (⇑φ)^[n - 1] u = c := by
  intro A _ p hc φ u hu hconv n hn
  haveI := hc
  set I : Ideal A := Ideal.span {(p : A)} with hI
  have hsm : ∀ J : Ideal A, J • (⊤ : Submodule A A) = J := fun J => by simp
  obtain ⟨w, hw⟩ : ∃ w : ℕ → A, w = fun k => (⇑φ)^[n * k + (n - 1)] u := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : ℕ → A, s = fun N => ∏ k ∈ Finset.range N, w k := ⟨_, rfl⟩
  have hwconv : ∀ r, ∃ M, ∀ k ≥ M, w k - 1 ∈ I ^ r := fun r => by
    obtain ⟨M, hM⟩ := hconv r
    exact ⟨M, fun k hk => by rw [hw]; exact hM _ (by nlinarith)⟩
  have hcauchy : ∀ r, ∃ N, ∀ m ≥ N, s (m + 1) - s m ∈ I ^ r := by
    intro r
    obtain ⟨M, hM⟩ := hwconv r
    refine ⟨M, fun m hm => ?_⟩
    have e : s (m + 1) - s m = s m * (w m - 1) := by
      simp only [hs, Finset.prod_range_succ]; ring
    rw [e]
    exact Ideal.mul_mem_left _ _ (hM m hm)
  obtain ⟨c, hc'⟩ := exists_adic_limit I s hcauchy
  have haus : ∀ x : A, (∀ r : ℕ, x ∈ I ^ r) → x = 0 := fun x hx =>
    IsHausdorff.haus (I := I) (M := A) inferInstance x (fun r => by rw [SModEq.zero, hsm]; exact hx r)
  have hmap : ∀ k (x : A) r, x ∈ I ^ r → (⇑φ)^[k] x ∈ I ^ r := by
    intro k x r hx
    have := Ideal.mem_map_of_mem (φ ^ k) hx
    rwa [Ideal.map_pow, hI, Ideal.map_span, Set.image_singleton, map_natCast,
      RingHom.coe_pow] at this
  have hsub : ∀ x y : A, (⇑φ)^[n] (x - y) = (⇑φ)^[n] x - (⇑φ)^[n] y := by
    intro x y; rw [← RingHom.coe_pow]; exact map_sub _ _ _
  have key : ∀ N, (⇑φ)^[n] (s N) * (⇑φ)^[n - 1] u = s (N + 1) := by
    intro N
    simp only [hs, Finset.prod_range_succ']
    rw [← RingHom.coe_pow, map_prod]
    congr 1
    · apply Finset.prod_congr rfl
      intro k _
      simp only [RingHom.coe_pow, hw]
      rw [← Function.iterate_add_apply]
      congr 1
      ring
    · simp [hw]
  have hwunit : ∀ k, IsUnit (w k) := fun k => by
    rw [hw]; show IsUnit ((⇑φ)^[n * k + (n - 1)] u)
    rw [← RingHom.coe_pow]; exact hu.map _
  refine ⟨c, ?_, ?_⟩
  · obtain ⟨N, hN⟩ := hc' 1
    have h1 : s N - c ∈ I := by simpa using hN N le_rfl
    have hsN : IsUnit (s N) := by
      rw [hs]
      exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one
        (fun k _ => hwunit k)
    obtain ⟨v, hv⟩ := hsN
    have hy : -(s N - c) ∈ (⊥ : Ideal A).jacobson :=
      IsAdicComplete.le_jacobson_bot I (I.neg_mem h1)
    have hu' := (Ideal.mem_jacobson_bot.mp hy) (↑v⁻¹ : A)
    have heq : c = (-(s N - c) * (↑v⁻¹ : A) + 1) * ↑v := by
      rw [add_mul, mul_assoc, Units.inv_mul, mul_one, one_mul, hv]; ring
    rw [heq]
    exact hu'.mul v.isUnit
  · refine sub_eq_zero.mp (haus _ fun r => ?_)
    obtain ⟨N, hN⟩ := hc' r
    have e : (⇑φ)^[n] c * (⇑φ)^[n - 1] u - c =
        -((⇑φ)^[n] (s N - c) * (⇑φ)^[n - 1] u) + (s (N + 1) - c) := by
      rw [← key N, hsub]; ring
    rw [e]
    exact (I ^ r).add_mem ((I ^ r).neg_mem (Ideal.mul_mem_right _ _ (hmap n _ r (hN N le_rfl))))
      (hN (N + 1) (by omega))

end GlobalTheory.FrobeniusProduct
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitFrobeniusIterateProductEqStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.exists_unit_frobenius_iterate_product_eq : ∀ (A : Type) [CommRing A] (p : ℕ), IsAdicComplete (Ideal.span {(p : A)}) A → ∀ (φ : A →+* A) (u : A), IsUnit u → (∀ r : ℕ, ∃ M : ℕ, ∀ m ≥ M, (⇑φ)^[m] u - 1 ∈ Ideal.span {(p : A)} ^ r) → ∀ n : ℕ, 0 < n → ∃ c : A, IsUnit c ∧ (⇑φ)^[n] c * (⇑φ)^[n - 1] u = c := by
  first | exact @GlobalTheory.FrobeniusProduct.exists_unit_iterate_mul_eq | exact GlobalTheory.FrobeniusProduct.exists_unit_iterate_mul_eq | (intros; apply GlobalTheory.FrobeniusProduct.exists_unit_iterate_mul_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobXiDivPrimeUnitTendstoOne

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.PhiXiUnit

variable {l : ℕ} [Fact l.Prime]

theorem phiA_alg (x : Per.Ainf l) :
    phiA l (algebraMap (Per.Ainf l) (Per.Acris l) x) =
      algebraMap (Per.Ainf l) (Per.Acris l) (Per.φA l x) :=
  (GlobalTheory.CrisMaps.phiA_extends l).alg x

theorem φA_tm (x : Per.Fl l) : Per.φA l (Per.tm x) = Per.tm x ^ l := by
  rw [← map_pow]
  exact GlobalTheory.RingIface.phiA_teich l x

theorem φA_tm_root (e : Per.Fl l) :
    Per.φA l (Per.tm ((frobeniusEquiv (Per.Fl l) l).symm e)) = Per.tm e := by
  rw [φA_tm, ← map_pow, ← frobenius_def, ← frobeniusEquiv_apply, RingEquiv.apply_symm_apply]

theorem φA_xi (e : Per.Fl l) :
    Per.φA l (xi e) = ∑ i ∈ Finset.range l, Per.tm e ^ i := by

  rw [xi, map_sum]
  simp only [map_pow, φA_tm_root]

theorem φA_mu (e : Per.Fl l) : Per.φA l (mu e) = mu e * Per.φA l (xi e) := by
  rw [φA_xi, mu, map_sub, map_one, φA_tm, mul_comm, geom_sum_mul]

theorem φA_xi_sub (e : Per.Fl l) :
    ∃ s : Per.Ainf l, Per.φA l (xi e) - (l : Per.Ainf l) = mu e * s := by
  refine ⟨∑ i ∈ Finset.range l, ∑ j ∈ Finset.range i, Per.tm e ^ j, ?_⟩
  have h : (l : Per.Ainf l) = ∑ i ∈ Finset.range l, (1 : Per.Ainf l) := by simp
  rw [φA_xi, mu, Finset.mul_sum, h, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm, geom_sum_mul]

theorem cancel_mu (C : Core l) (x y : Per.Acris l)
    (h : algebraMap (Per.Ainf l) (Per.Acris l) (mu C.ε) * x =
      algebraMap (Per.Ainf l) (Per.Acris l) (mu C.ε) * y) : x = y := by
  have he := GlobalTheory.T.isPrimitiveTiltedRootOfUnity_localPeriodRingsData l C
  have hU : IsUnit (algebraMap (Per.Acris l) (Per.Bcris l)
      (algebraMap (Per.Ainf l) (Per.Acris l) (mu C.ε))) :=
    GlobalTheory.MemLoc.TFil.isUnit_mu he
  apply GlobalTheory.MemLoc.AwayT.acris_injective C
  apply hU.mul_left_cancel
  rw [← map_mul, ← map_mul, h]

theorem exists_unit (C : Core l) : ∃ u : Per.Acris l, IsUnit u ∧
    (l : Per.Acris l) * u = algebraMap (Per.Ainf l) (Per.Acris l) (Per.φA l (xi C.ε)) := by
  have he := GlobalTheory.T.isPrimitiveTiltedRootOfUnity_localPeriodRingsData l C
  obtain ⟨t, ρ, ht, hρ, htρ⟩ := GlobalTheory.T.exists_log_teichmuller_acris_eq_mu_mul_unit l C.ε he.1
  have h1 : t = C.t := (GlobalTheory.T.acris_logTeichmuller_unique_galois_frobenius_bdR l C.ε C.t he.1 C.t_log).1 t ht
  have hφt := GlobalTheory.T.acrisFrobenius_fontaine_t_eq_mul l C
  rw [← h1, htρ, map_mul, phiA_alg, φA_mu, map_mul, mul_assoc, mul_left_comm (l : Per.Acris l)] at hφt
  have h2 := cancel_mu C _ _ hφt
  have hφρ : IsUnit (phiA l ρ) := hρ.map _
  refine ⟨ρ * ↑hφρ.unit⁻¹, hρ.mul (Units.isUnit _), ?_⟩
  rw [← mul_assoc, ← h2, mul_assoc, IsUnit.mul_val_inv, mul_one]

theorem iterate_sub_one (C : Core l) (u : Per.Acris l)
    (hu : (l : Per.Acris l) * u = algebraMap (Per.Ainf l) (Per.Acris l) (Per.φA l (xi C.ε))) :
    ∀ r : ℕ, ∃ M : ℕ, ∀ m ≥ M, (⇑(phiA l))^[m] u - 1 ∈ Ideal.span {(l : Per.Acris l)} ^ r := by
  set a := algebraMap (Per.Ainf l) (Per.Acris l) (mu C.ε) with ha_def
  have ha : phiA l a = a * ((l : Per.Acris l) * u) := by
    rw [ha_def, phiA_alg, φA_mu, map_mul, hu]
  have hdvd : ∀ m : ℕ, (l : Per.Acris l) ^ m ∣ (phiA l ^ m) a := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [RingHom.coe_pow, Function.iterate_succ_apply, ha, ← RingHom.coe_pow, map_mul, map_mul,
        map_natCast, pow_succ]
      obtain ⟨c, hc⟩ := ih
      rw [hc]
      exact ⟨c * (phiA l ^ m) u, by ring⟩
  obtain ⟨s, hs⟩ := φA_xi_sub C.ε
  have hls : (l : Per.Acris l) * u - l = a * algebraMap (Per.Ainf l) (Per.Acris l) s := by
    rw [hu, ← map_natCast (algebraMap (Per.Ainf l) (Per.Acris l)) l, ← map_sub, hs, map_mul]
  have key : ∀ m : ℕ, (l : Per.Acris l) * ((phiA l ^ m) u - 1) =
      (phiA l ^ m) a * (phiA l ^ m) (algebraMap (Per.Ainf l) (Per.Acris l) s) := by
    intro m
    rw [← map_mul, ← hls, map_sub, map_mul, map_natCast, mul_sub, mul_one]
  have tf := (GlobalTheory.MemLoc.acris_basic l).2.1
  intro r
  refine ⟨r + 1, fun m hm => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [← RingHom.coe_pow]
  obtain ⟨c, hc⟩ := hdvd (k + 1)
  have h3 : (phiA l ^ (k + 1)) u - 1 =
      (l : Per.Acris l) ^ k * (c * (phiA l ^ (k + 1)) (algebraMap (Per.Ainf l) (Per.Acris l) s)) := by
    rw [← sub_eq_zero]
    apply tf
    rw [mul_sub, key, hc, pow_succ]
    ring
  have h4 : (phiA l ^ (k + 1)) u - 1 ∈ Ideal.span {(l : Per.Acris l)} ^ k := by
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, h3]
    exact dvd_mul_right _ _
  exact Ideal.pow_le_pow_right (by omega) h4

end GlobalTheory.MemLoc.PhiXiUnit

theorem GlobalTheory.MemLoc.phi_xi_unit_tendsto : ∀ (l : ℕ) [Fact l.Prime] (C : GlobalTheory.MemLoc.Core l),
    ∃ u : Per.Acris l, IsUnit u ∧
      (l : Per.Acris l) * u = algebraMap (Per.Ainf l) (Per.Acris l) (Per.φA l (GlobalTheory.MemLoc.xi C.ε)) ∧
      ∀ r : ℕ, ∃ M : ℕ, ∀ m ≥ M,
        (⇑(GlobalTheory.MemLoc.phiA l))^[m] u - 1 ∈ Ideal.span {(l : Per.Acris l)} ^ r := by
  intro l _ C
  obtain ⟨u, hu, hlu⟩ := GlobalTheory.MemLoc.PhiXiUnit.exists_unit C
  exact ⟨u, hu, hlu, GlobalTheory.MemLoc.PhiXiUnit.iterate_sub_one C u hlu⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobXiDivPrimeUnitTendstoOneStatement

section

@[expose] public section

open Formalism
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.frobXi_div_prime_unit_tendsto_one : ∀ (l : ℕ) [Fact l.Prime] (C : GlobalTheory.MemLoc.Core l), ∃ u : Per.Acris l, IsUnit u ∧ (l : Per.Acris l) * u = algebraMap (Per.Ainf l) (Per.Acris l) (Per.φA l (GlobalTheory.MemLoc.xi C.ε)) ∧ ∀ r : ℕ, ∃ M : ℕ, ∀ m ≥ M, (⇑(GlobalTheory.MemLoc.phiA l))^[m] u - 1 ∈ Ideal.span {(l : Per.Acris l)} ^ r := by
  first | exact @GlobalTheory.MemLoc.phi_xi_unit_tendsto | exact GlobalTheory.MemLoc.phi_xi_unit_tendsto | (intros; apply GlobalTheory.MemLoc.phi_xi_unit_tendsto <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicPeriodLocalPrime

section

@[expose] public section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.LTPeriod

variable {l : ℕ} [Fact l.Prime]

theorem iter_φB_alg (k : ℕ) (y : Per.Acris l) :
    (⇑(Per.φB l))^[k] (algebraMap (Per.Acris l) (Per.Bcris l) y) =
      algebraMap (Per.Acris l) (Per.Bcris l) ((⇑(GlobalTheory.MemLoc.phiA l))^[k] y) := by
  induction k generalizing y with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, GlobalTheory.MemLoc.fund_phiB_alg, ih]

theorem phiA_alg (a : Per.Ainf l) :
    GlobalTheory.MemLoc.phiA l (algebraMap (Per.Ainf l) (Per.Acris l) a) =
      algebraMap (Per.Ainf l) (Per.Acris l) (Per.φA l a) :=
  (GlobalTheory.CrisMaps.phiA_extends l).alg a

theorem iter_phiA_alg (k : ℕ) (a : Per.Ainf l) :
    (⇑(GlobalTheory.MemLoc.phiA l))^[k] (algebraMap (Per.Ainf l) (Per.Acris l) a) =
      algebraMap (Per.Ainf l) (Per.Acris l) ((⇑(Per.φA l))^[k] a) := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, phiA_alg, ih]

theorem iter_mul {A : Type} [CommRing A] (f : A →+* A) (k : ℕ) (a b : A) :
    (⇑f)^[k] (a * b) = (⇑f)^[k] a * (⇑f)^[k] b := by
  rw [← RingHom.coe_pow, map_mul]

theorem iter_natCast {A : Type} [CommRing A] (f : A →+* A) (k m : ℕ) :
    (⇑f)^[k] (m : A) = m := by
  rw [← RingHom.coe_pow, map_natCast]

theorem concrete (C : GlobalTheory.MemLoc.Core l) (n : ℕ) (hn : 0 < n) :
    ∃ x : Per.Bcris l, IsUnit x ∧ (⇑(Per.φB l))^[n] x = (l : Per.Bcris l) * x ∧ C.ι x ∈ Per.FilD l 1 ∧
      C.ι x ∉ Per.FilD l 2 ∧ ∀ j : ℕ, 0 < j → j < n →
        C.ι ((⇑(Per.φB l))^[j] x) ∈ Per.FilD l 0 ∧ C.ι ((⇑(Per.φB l))^[j] x) ∉ Per.FilD l 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have he := GlobalTheory.MemLoc.core_isEps l C
  obtain ⟨w, hw0, hw⟩ := GlobalTheory.T.exists_ainf_frobenius_iterate_eq_xi_mul l C.ε he (m + 1) hn
  obtain ⟨u, hu, hlu, hconv⟩ := GlobalTheory.T.frobXi_div_prime_unit_tendsto_one l C
  obtain ⟨c, hc, hcφ⟩ :=
    GlobalTheory.T.exists_unit_frobenius_iterate_product_eq (Per.Acris l) l (GlobalTheory.MemLoc.acris_basic l).1 (GlobalTheory.MemLoc.phiA l) u hu hconv (m + 1) hn
  rw [Nat.add_sub_cancel] at hcφ
  set ξ := GlobalTheory.MemLoc.xi C.ε with hξ
  have h1 : (l : Per.Acris l) * (⇑(GlobalTheory.MemLoc.phiA l))^[m] u =
      algebraMap (Per.Ainf l) (Per.Acris l) ((⇑(Per.φA l))^[m + 1] ξ) := by
    rw [← iter_natCast (GlobalTheory.MemLoc.phiA l) m l, ← iter_mul, hlu, iter_phiA_alg,
      ← Function.iterate_succ_apply]
  have hkey : algebraMap (Per.Ainf l) (Per.Acris l) ((⇑(Per.φA l))^[m + 1] ξ) *
      (⇑(GlobalTheory.MemLoc.phiA l))^[m + 1] c = (l : Per.Acris l) * c := by
    rw [← h1]
    linear_combination (l : Per.Acris l) * hcφ
  set a : Per.Acris l := algebraMap (Per.Ainf l) (Per.Acris l) (ξ * w) * c with ha
  have hA : (⇑(GlobalTheory.MemLoc.phiA l))^[m + 1] a = (l : Per.Acris l) * a := by
    rw [ha, iter_mul, iter_phiA_alg, iter_mul, hw, map_mul, map_mul]
    linear_combination (algebraMap (Per.Ainf l) (Per.Acris l) ξ *
      algebraMap (Per.Ainf l) (Per.Acris l) w) * hkey
  set x : Per.Bcris l := algebraMap (Per.Acris l) (Per.Bcris l) a with hx
  have hxφ : (⇑(Per.φB l))^[m + 1] x = (l : Per.Bcris l) * x := by
    rw [hx, iter_φB_alg, hA, map_mul, map_natCast]
  have hxa : x = Per.aB l (ξ * w) * algebraMap (Per.Acris l) (Per.Bcris l) c := by
    have e : algebraMap (Per.Acris l) (Per.Bcris l) (algebraMap (Per.Ainf l) (Per.Acris l) (ξ * w)) =
        Per.aB l (ξ * w) := by
      apply (GlobalTheory.T.localPeriodRingsData_unramified_laws l C).2.2.2.1
      rw [GlobalTheory.MemLoc.PrimeEx.iota_aB, C.ι_j, GlobalTheory.MemLoc.TFil.j_alg C.j_cris]
    rw [hx, ha, map_mul, e]
  have hx0 : x ≠ 0 := by
    intro h0
    rw [hxa, (hc.map (algebraMap (Per.Acris l) (Per.Bcris l))).mul_left_eq_zero] at h0
    exact hw0 (GlobalTheory.MemLoc.PrimeEx.aB_inj C (h0.trans (map_zero _).symm))
  have hx1 : C.ι x ∈ Per.FilD l 1 := by
    rw [hxa, map_mul, C.ι_j, mul_comm, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ ((GlobalTheory.MemLoc.PrimeEx.fil1 C _).2 ⟨w, rfl⟩)
  have hx0' : ∀ j : ℕ, j < m + 1 → C.ι ((⇑(Per.φB l))^[j] x) ∈ Per.FilD l 0 := by
    intro j _
    rw [hx, iter_φB_alg, C.ι_j]
    exact GlobalTheory.MemLoc.TiedUnif.alg_mem_FilD_zero _
  obtain ⟨hunit, h2, hj⟩ := GlobalTheory.T.frobeniusEigen_fil_one_isUnit_exact_degree l C (m + 1) hn x hxφ hx0 hx1 hx0'
  exact ⟨x, hunit, hxφ, hx1, h2, fun j hj0 hjn => ⟨hx0' j hjn, hj j hj0 hjn⟩⟩

end GlobalTheory.LTPeriod

theorem GlobalTheory.LTPeriod.main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (K : FinExt l) (n : ℕ), 0 < n → ∃ x : P.R.B, IsUnit x ∧ (⇑P.φB)^[n] x = (l : P.R.B) * x ∧
      P.ιB x ∈ (P.PD K).Fil 1 ∧ P.ιB x ∉ (P.PD K).Fil 2 ∧ ∀ j : ℕ, 0 < j → j < n →
        P.ιB ((⇑P.φB)^[j] x) ∈ (P.PD K).Fil 0 ∧ P.ιB ((⇑P.φB)^[j] x) ∉ (P.PD K).Fil 1 := by
  intro l _ P AI T K n hn
  obtain ⟨C, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  obtain ⟨x, hu, hφ, h1, h2, hj⟩ := GlobalTheory.LTPeriod.concrete C n hn
  have hit : ∀ (k : ℕ) (b : P.R.B), T.eB ((⇑P.φB)^[k] b) = (⇑(Per.φB l))^[k] (T.eB b) := by
    intro k
    induction k with
    | zero => intro b; rfl
    | succ k ih =>
      intro b
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', T.frob, ih]
  have hfil : ∀ (a : ℤ) (b : P.R.B), P.ιB b ∈ (P.PD K).Fil a ↔ C.ι (T.eB b) ∈ Per.FilD l a := by
    intro a b
    rw [T.fil, hC.ι]
  refine ⟨T.eB.symm x, hu.map T.eB.symm, T.eB.injective ?_, ?_, ?_, fun j hj0 hjn => ?_⟩
  · rw [hit, RingEquiv.apply_symm_apply, hφ, map_mul, map_natCast, RingEquiv.apply_symm_apply]
  · rw [hfil, RingEquiv.apply_symm_apply]
    exact h1
  · rw [hfil, RingEquiv.apply_symm_apply]
    exact h2
  · rw [hfil, hfil, hit, RingEquiv.apply_symm_apply]
    exact hj j hj0 hjn
end
end
end
