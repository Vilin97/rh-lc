module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FaithfulIntegralClosure
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPderivNotDvd

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.CompanionTheory.TraceJac

open MvPolynomial in
theorem exists_pderiv_not_dvd {K σ : Type*} [Field K] [CharZero K] (π : MvPolynomial σ K)
    (hπ : Prime π) : ∃ j, ¬ π ∣ pderiv j π := by
  classical
  have hT : π.totalDegree ≠ 0 := by
    intro h
    have hC := totalDegree_eq_zero_iff_eq_C.1 h
    by_cases ha : π.coeff 0 = 0
    · rw [ha, map_zero] at hC
      exact hπ.ne_zero hC
    · apply hπ.not_isUnit
      rw [hC]
      exact (IsUnit.mk0 _ ha).map C
  have h1 : ¬ ∀ m ∈ π.support, ∀ x, m x = 0 := by
    rwa [← totalDegree_eq_zero_iff]
  push Not at h1
  obtain ⟨m, hm, j, hj⟩ := h1
  refine ⟨j, fun hd => ?_⟩
  have hm' : (m - Finsupp.single j 1) + Finsupp.single j 1 = m := by
    ext i
    by_cases hi : i = j
    · subst hi
      simp
      omega
    · simp [Ne.symm hi]
  have hne : pderiv j π ≠ 0 := by
    intro h0
    have h2 := coeff_pderiv (i := j) π (m - Finsupp.single j 1)
    rw [h0, hm', AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at h2
    have h3 : (((m - Finsupp.single j 1 : σ →₀ ℕ) j : ℕ) + 1 : K) ≠ 0 := by
      exact Nat.cast_add_one_ne_zero _
    exact mul_ne_zero (mem_support_iff.1 hm) h3 h2.symm
  obtain ⟨q, hq⟩ := hd
  have hq0 : q ≠ 0 := fun h => hne (by rw [hq, h, mul_zero])
  have hdeg : (pderiv j π).totalDegree = π.totalDegree + q.totalDegree := by
    rw [hq]; exact totalDegree_mul_of_isDomain hπ.ne_zero hq0
  have hlt : (pderiv j π).totalDegree < π.totalDegree := by
    have : (pderiv j π).totalDegree + 1 ≤ π.totalDegree := by
      have h4 : ∀ s ∈ (pderiv j π).support, s.sum (fun _ e => e) + 1 ≤ π.totalDegree := by
        intro s hs
        have h5 : s + Finsupp.single j 1 ∈ π.support := by
          rw [mem_support_iff] at hs ⊢
          intro h6
          apply hs
          rw [coeff_pderiv, h6, zero_mul]
        have := le_totalDegree h5
        rwa [Finsupp.sum_add_index' (by simp) (by simp), Finsupp.sum_single_index rfl] at this
      obtain ⟨s, hs, hs'⟩ : ∃ s ∈ (pderiv j π).support, (pderiv j π).totalDegree = s.sum (fun _ e => e) := by
        rw [totalDegree]
        obtain ⟨s, hs, hs'⟩ := Finset.exists_mem_eq_sup _ (support_nonempty.2 hne) (fun s : σ →₀ ℕ => s.sum fun _ e => e)
        exact ⟨s, hs, hs'⟩
      rw [hs']; exact h4 s hs
    omega
  omega

theorem finite_frac {A B F L : Type*} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra A B] [Module.Finite A B] [Field F] [Field L] [Algebra A F] [IsFractionRing A F]
    [Algebra B L] [IsFractionRing B L] [Algebra F L] [Algebra A L] [IsScalarTower A F L]
    [IsScalarTower A B L] : FiniteDimensional F L := by
  classical
  obtain ⟨T, hT⟩ := (Module.Finite.fg_top : (⊤ : Submodule A B).FG)
  let W := IntermediateField.adjoin F ((T.image (algebraMap B L) : Finset L) : Set L)
  have hint : ∀ x ∈ ((T.image (algebraMap B L) : Finset L) : Set L), IsIntegral F x := by
    intro x hx
    simp only [Finset.coe_image, Set.mem_image] at hx
    obtain ⟨t, -, rfl⟩ := hx
    have h1 : IsIntegral A t := IsIntegral.of_finite A t
    exact (h1.algebraMap (B := L)).tower_top
  haveI : FiniteDimensional F W :=
    IntermediateField.finiteDimensional_adjoin hint
  have hB : ∀ x : B, algebraMap B L x ∈ W := by
    intro x
    have hx : x ∈ Submodule.span A (T : Set B) := hT ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem s hs =>
      refine IntermediateField.subset_adjoin _ _ ?_
      simp only [Finset.coe_image]
      exact ⟨s, hs, rfl⟩
    | zero => simp
    | add a b _ _ ha hb => rw [map_add (f := _)]; exact W.add_mem ha hb
    | smul r a _ ha =>
      have h1 : algebraMap B L (r • a) = algebraMap F L (algebraMap A F r) * algebraMap B L a := by
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
          ← IsScalarTower.algebraMap_apply]
      rw [h1]
      exact W.mul_mem (W.algebraMap_mem _) ha
  have hW : W = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨a, s, -, rfl⟩ := IsFractionRing.div_surjective (A := B) x
    exact W.div_mem (hB a) (hB s)
  have key : ∀ W' : IntermediateField F L, FiniteDimensional F W' → W' = ⊤ →
      FiniteDimensional F L := by
    rintro _ h rfl
    exact (IntermediateField.topEquiv (F := F) (E := L)).toLinearEquiv.finiteDimensional
  exact key W inferInstance hW

open Polynomial in
theorem integral_of_range {A R L : Type*} [CommRing A] [CommRing R] [Field L] [Algebra A L]
    [Algebra R L] (hr : ∀ a : A, algebraMap A L a ∈ (algebraMap R L).range) (x : L)
    (h : IsIntegral A x) : IsIntegral R x := by
  obtain ⟨p, hp, h0⟩ := h
  have hl : p.map (algebraMap A L) ∈ Polynomial.lifts (algebraMap R L) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [coeff_map]
    exact hr _
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (hp.map _)
  refine ⟨q, hqm, ?_⟩
  rw [← Polynomial.eval_map, hq, Polynomial.eval_map]
  exact h0

end GlobalTheory.CompanionTheory.TraceJac

namespace GlobalTheory.CompanionTheory.TraceJac

theorem at_prime_abs {P L F R n : Type*} [CommRing P] [IsDomain P] [IsNoetherianRing P] [Field L]
    [Field F] [CommRing R] [Algebra P R] [Algebra P F] [Algebra P L] [Algebra R F]
    [IsScalarTower P R F] [Algebra F L] [Algebra R L] [IsScalarTower R F L] [IsScalarTower P R L]
    [IsFractionRing P F] [FiniteDimensional F L] [Algebra.IsSeparable F L] [Fintype n]
    [DecidableEq n] (π : P) (hπ : Prime π) (p : Ideal P) [p.IsPrime] (hp : p = Ideal.span {π})
    [IsLocalization.AtPrime R p] (E : n → Derivation ℤ L L)
    (hE : ∀ k f, ∃ f', E k (algebraMap P L f) = algebraMap P L f') (j : n) (fj : P)
    (hfj : E j (algebraMap P L π) = algebraMap P L fj) (hj : ¬ π ∣ fj)
    (hnat : ∀ m : ℕ, m ≠ 0 → IsUnit (m : R))
    (c : L) (hc : IsIntegral R c) (b : n → L) (hb : ∀ l, IsIntegral R (b l)) :
    ∃ f s : P, ¬ π ∣ s ∧
      algebraMap P F s * Algebra.trace F L (c * (Matrix.of fun k l => E k (b l)).det) =
        algebraMap P F f := by
  classical
  have hmem : ∀ s, s ∈ p ↔ π ∣ s := fun s => by rw [hp, Ideal.mem_span_singleton]
  have hmemM : ∀ s, s ∈ p.primeCompl ↔ ¬ π ∣ s := fun s => by
    rw [Ideal.mem_primeCompl_iff, hmem]
  haveI : IsDomain R := IsLocalization.isDomain_of_le_nonZeroDivisors R
    p.primeCompl_le_nonZeroDivisors
  haveI : IsNoetherianRing R := IsLocalization.isNoetherianRing p.primeCompl R inferInstance
  haveI : IsLocalRing R := IsLocalization.AtPrime.isLocalRing R p
  haveI : IsFractionRing R F :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.primeCompl R F
  have hmax : IsLocalRing.maximalIdeal R = Ideal.span {algebraMap P R π} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p R, hp, Ideal.map_span, Set.image_singleton]
  have hπR0 : algebraMap P R π ≠ 0 := by
    intro h
    apply hπ.ne_zero
    exact IsLocalization.injective R (M := p.primeCompl) p.primeCompl_le_nonZeroDivisors
      (h.trans (map_zero _).symm)
  have hnf : ¬ IsField R := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, hmax]
    simpa using hπR0
  have hprin : (IsLocalRing.maximalIdeal R).IsPrincipal := ⟨⟨_, hmax⟩⟩
  haveI : IsDiscreteValuationRing R := by
    have h5 := (IsDiscreteValuationRing.TFAE R hnf).out 1 5
    exact h5.2 hprin
  have hirr : Irreducible (algebraMap P R π) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hmax
  have hρP : ∀ f, algebraMap R L (algebraMap P R f) = algebraMap P L f := fun f =>
    (IsScalarTower.algebraMap_apply P R L f).symm
  have hR : ∀ k (r : R), ∃ r' : R, E k (algebraMap R L r) = algebraMap R L r' := by
    intro k r
    obtain ⟨f, s, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl r
    have h1 := IsLocalization.mk'_spec R f s
    obtain ⟨w, hw⟩ := (IsLocalization.map_units R s).exists_right_inv
    obtain ⟨f1, hf1⟩ := hE k f
    obtain ⟨s1, hs1⟩ := hE k (s : P)
    refine ⟨(algebraMap P R f1 - IsLocalization.mk' R f s * algebraMap P R s1) * w, ?_⟩
    set x := algebraMap R L (IsLocalization.mk' R f s) with hx
    have h2 : x * algebraMap P L s = algebraMap P L f := by
      rw [hx, ← hρP, ← hρP, ← map_mul, h1]
    have h3 : algebraMap P L s * algebraMap R L w = 1 := by
      rw [← hρP, ← map_mul, hw, map_one]
    have h4 := congrArg (E k) h2
    rw [Derivation.leibniz, hf1, hs1] at h4
    simp only [smul_eq_mul] at h4
    rw [map_mul, map_sub, map_mul, hρP, hρP, ← hx, ← h4]
    linear_combination (-E k x) * h3
  obtain ⟨u, hu⟩ := IsLocalization.map_units R (⟨fj, (hmemM _).2 hj⟩ : p.primeCompl)
  obtain ⟨r, hr⟩ := trace_jac_dvr (F := F) hnat E hR (algebraMap P R π) hirr j u
    (by rw [hρP, hfj, hu, hρP]) c hc b hb
  obtain ⟨f, s, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl r
  refine ⟨f, s, (hmemM _).1 s.2, ?_⟩
  rw [← hr, IsScalarTower.algebraMap_apply P R F, IsScalarTower.algebraMap_apply P R F f,
    ← map_mul, mul_comm, IsLocalization.mk'_spec]

end GlobalTheory.CompanionTheory.TraceJac
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPrimeDvdNotUnit

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.CompanionTheory.TraceJac

theorem exists_prime_dvd_not_unit {P A : Type*} [CommRing P] [IsDomain P]
    [UniqueFactorizationMonoid P] [CommRing A] (φ : P →+* A) (g : P) (hg : g ≠ 0)
    (h : ¬ IsUnit (φ g)) : ∃ π, Prime π ∧ π ∣ g ∧ ¬ IsUnit (φ π) := by
  revert hg h
  refine UniqueFactorizationMonoid.induction_on_prime g ?_ ?_ ?_
  · intro h0
    exact absurd rfl h0
  · intro x hx _ hxu
    exact absurd (hx.map φ) hxu
  · intro a p ha hp ih _ hpa
    by_cases hpu : IsUnit (φ p)
    · have hau : ¬ IsUnit (φ a) := fun hau => hpa (by rw [map_mul]; exact hpu.mul hau)
      obtain ⟨π, hπ, hπa, hπu⟩ := ih ha hau
      exact ⟨π, hπ, dvd_mul_of_dvd_right hπa p, hπu⟩
    · exact ⟨p, hp, dvd_mul_right p a, hpu⟩

section
variable {P A F L n : Type*} [CommRing P] [IsDomain P] [UniqueFactorizationMonoid P]
  [IsNoetherianRing P] [CommRing A] [IsDomain A] [Algebra P A] [Field F] [Algebra A F]
  [IsFractionRing A F] [Algebra P F] [IsScalarTower P A F] [Field L] [Algebra F L] [Algebra A L]
  [IsScalarTower A F L] [Algebra P L] [IsScalarTower P F L] [FiniteDimensional F L]
  [Algebra.IsSeparable F L] [Fintype n] [DecidableEq n]

theorem main_abs (hinj : Function.Injective (algebraMap P A))
    (hloc : ∀ a : A, ∃ f g : P, IsUnit (algebraMap P A g) ∧ a * algebraMap P A g = algebraMap P A f)
    (E : n → Derivation ℤ L L) (hE : ∀ k f, ∃ f', E k (algebraMap P L f) = algebraMap P L f')
    (hjac : ∀ π : P, Prime π → ∃ j fj, E j (algebraMap P L π) = algebraMap P L fj ∧ ¬ π ∣ fj)
    (hnat : ∀ m : ℕ, m ≠ 0 → IsUnit (m : P))
    (c : L) (hc : IsIntegral A c) (b : n → L) (hb : ∀ l, IsIntegral A (b l)) :
    ∃ a : A, algebraMap A F a = Algebra.trace F L (c * (Matrix.of fun k l => E k (b l)).det) := by
  classical
  have hPF_inj : Function.Injective (algebraMap P F) := by
    rw [IsScalarTower.algebraMap_eq P A F]
    exact (IsFractionRing.injective A F).comp hinj
  have hne : ∀ g : P, IsUnit (algebraMap P A g) → algebraMap P F g ≠ 0 := by
    intro g hg h0
    have hg0 : g ≠ 0 := by
      rintro rfl
      simp at hg
    exact hg0 (hPF_inj (h0.trans (map_zero _).symm))
  have hloc' : ∀ a : A, ∃ f g : P, algebraMap P F g ≠ 0 ∧
      algebraMap A F a * algebraMap P F g = algebraMap P F f := by
    intro a
    obtain ⟨f, g, hg, hfg⟩ := hloc a
    refine ⟨f, g, hne g hg, ?_⟩
    rw [IsScalarTower.algebraMap_apply P A F g, IsScalarTower.algebraMap_apply P A F f, ← map_mul, hfg]
  haveI : IsFractionRing P F := by
    haveI : FaithfulSMul P F := (faithfulSMul_iff_algebraMap_injective P F).2 hPF_inj
    refine IsFractionRing.of_field P F (fun z => ?_)
    obtain ⟨a, a', -, rfl⟩ := IsFractionRing.div_surjective (A := A) z
    obtain ⟨f, g, hg, e1⟩ := hloc' a
    obtain ⟨f', g', hg', e2⟩ := hloc' a'
    refine ⟨f * g', g * f', ?_⟩
    rw [map_mul, map_mul, ← e1, ← e2]
    rw [show algebraMap A F a * algebraMap P F g * algebraMap P F g' /
        (algebraMap P F g * (algebraMap A F a' * algebraMap P F g')) =
        algebraMap A F a * (algebraMap P F g * algebraMap P F g') /
        (algebraMap A F a' * (algebraMap P F g * algebraMap P F g')) by ring]
    rw [mul_div_mul_right _ _ (mul_ne_zero hg hg')]
  have key : ∀ π : P, Prime π → ¬ IsUnit (algebraMap P A π) →
      ∃ f s : P, ¬ π ∣ s ∧ algebraMap P F s *
        Algebra.trace F L (c * (Matrix.of fun k l => E k (b l)).det) = algebraMap P F f := by
    intro π hπ hπu
    obtain ⟨j, fj, hfj, hj⟩ := hjac π hπ
    set p : Ideal P := Ideal.span {π} with hp
    haveI hpp : p.IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).2 hπ
    let R : Subalgebra P F :=
      Localization.subalgebra.ofField F p.primeCompl p.primeCompl_le_nonZeroDivisors
    haveI : IsScalarTower R F L := inferInstance
    haveI : IsScalarTower P R L := inferInstance
    haveI : IsLocalization.AtPrime R p := inferInstance
    have hr : ∀ a : A, algebraMap A L a ∈ (algebraMap R L).range := by
      intro a
      obtain ⟨f, g, hg, hfg⟩ := hloc a
      have hgp : g ∈ p.primeCompl := by
        intro hgmem
        apply hπu
        obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.1 hgmem
        rw [map_mul] at hg
        exact isUnit_of_mul_isUnit_right hg
      refine ⟨IsLocalization.mk' R f ⟨g, hgp⟩, ?_⟩
      have h1 : algebraMap R F (IsLocalization.mk' R f ⟨g, hgp⟩) * algebraMap P F g = algebraMap P F f := by
        rw [IsScalarTower.algebraMap_apply P R F g, IsScalarTower.algebraMap_apply P R F f, ← map_mul,
          IsLocalization.mk'_spec]
      have h2 : algebraMap A F a * algebraMap P F g = algebraMap P F f := by
        rw [IsScalarTower.algebraMap_apply P A F g, IsScalarTower.algebraMap_apply P A F f, ← map_mul, hfg]
      have h3 : algebraMap R F (IsLocalization.mk' R f ⟨g, hgp⟩) = algebraMap A F a :=
        mul_right_cancel₀ (hne g hg) (h1.trans h2.symm)
      show algebraMap F L (algebraMap R F _) = _
      rw [h3, ← IsScalarTower.algebraMap_apply A F L]
    have hcR := integral_of_range hr c hc
    have hbR : ∀ l, IsIntegral R (b l) := fun l => integral_of_range hr (b l) (hb l)
    have hnatR : ∀ m : ℕ, m ≠ 0 → IsUnit (m : R) := fun m hm => by
      simpa using (hnat m hm).map (algebraMap P R)
    exact at_prime_abs (R := R) π hπ p hp E hE j fj hfj hj hnatR c hcR b hbR
  obtain ⟨n0, d0, hrel, hx0⟩ := IsFractionRing.exists_reduced_fraction (A := P)
    (Algebra.trace F L (c * (Matrix.of fun k l => E k (b l)).det))
  have hd0 : (d0 : P) ≠ 0 := nonZeroDivisors.coe_ne_zero d0
  have hxd : Algebra.trace F L (c * (Matrix.of fun k l => E k (b l)).det) * algebraMap P F d0 =
      algebraMap P F n0 := by
    rw [← hx0]
    exact IsLocalization.mk'_spec F n0 d0
  by_cases hu : IsUnit (algebraMap P A d0)
  · obtain ⟨u, hu'⟩ := hu
    refine ⟨algebraMap P A n0 * ((u⁻¹ : Aˣ) : A), ?_⟩
    have hdF : algebraMap A F (algebraMap P A d0) = algebraMap P F d0 :=
      (IsScalarTower.algebraMap_apply P A F d0).symm
    have hnF : algebraMap A F (algebraMap P A n0) = algebraMap P F n0 :=
      (IsScalarTower.algebraMap_apply P A F n0).symm
    have hinv : algebraMap A F ((u⁻¹ : Aˣ) : A) * algebraMap P F d0 = 1 := by
      rw [← hdF, ← hu', ← map_mul, Units.inv_mul, map_one]
    rw [map_mul, hnF, ← hxd, mul_assoc, mul_comm (algebraMap P F _), hinv, mul_one]
  · obtain ⟨π, hπ, hπd, hπu⟩ := exists_prime_dvd_not_unit (algebraMap P A) (d0 : P) hd0 hu
    obtain ⟨f, s, hs, hfs⟩ := key π hπ hπu
    exfalso
    have h1 : algebraMap P F (s * n0) = algebraMap P F (f * d0) := by
      rw [map_mul, map_mul, ← hxd, ← hfs]
      ring
    have h2 := hPF_inj h1
    have hπn : π ∣ n0 := by
      have : π ∣ s * n0 := by
        rw [h2]
        exact dvd_mul_of_dvd_right hπd f
      exact (hπ.dvd_or_dvd this).resolve_left hs
    exact hπ.not_isUnit (hrel hπn hπd)
end

end GlobalTheory.CompanionTheory.TraceJac

namespace GlobalTheory.CompanionTheory.TraceJac

theorem deriv_aeval_mv {K L : Type*} [Field K] [Field L] [Algebra K L] {d : ℕ} (τ : Fin d → L)
    (D : Derivation K L L) (k : Fin d) (hD : ∀ j, D (τ j) = if k = j then 1 else 0)
    (f : MvPolynomial (Fin d) K) :
    D (MvPolynomial.aeval τ f) = MvPolynomial.aeval τ (MvPolynomial.pderiv k f) := by
  induction f using MvPolynomial.induction_on
  next a =>
    simp [MvPolynomial.aeval_C, MvPolynomial.pderiv_C]
  next p q hp hq =>
    simp only [map_add (f := _), hp, hq]
  next p i hp =>
    simp only [map_mul, Derivation.leibniz, hp, MvPolynomial.aeval_X, hD, smul_eq_mul,
      MvPolynomial.pderiv_X, map_add]
    by_cases hki : k = i
    · subst hki
      simp
    · simp [hki, Pi.single_apply, Ne.symm hki]

theorem trace_jacobian_mem : ∀ (K : Type) [Field K] [CharZero K] (d : ℕ) (A : Type) [CommRing A] [IsDomain A] [Algebra K A] (t : Fin d → A), Function.Injective (MvPolynomial.aeval t : MvPolynomial (Fin d) K →ₐ[K] A) → (∀ a : A, ∃ f g : MvPolynomial (Fin d) K, IsUnit (MvPolynomial.aeval t g) ∧ a * MvPolynomial.aeval t g = MvPolynomial.aeval t f) → ∀ (B : Type) [CommRing B] [IsDomain B] [Algebra A B] [Algebra K B] [IsScalarTower K A B] [Module.Finite A B], Function.Injective (algebraMap A B) → ∀ (F L : Type) [Field F] [Field L] [Algebra A F] [IsFractionRing A F] [Algebra B L] [IsFractionRing B L] [Algebra F L] [Algebra A L] [IsScalarTower A F L] [IsScalarTower A B L] [Algebra K L] [IsScalarTower K B L] (D : Fin d → Derivation K L L), (∀ k j, D k (algebraMap A L (t j)) = if k = j then 1 else 0) → ∀ (c : B) (b : Fin d → B), ∃ a : A, algebraMap A F a = Algebra.trace F L (algebraMap B L c * (Matrix.of fun k l => D k (algebraMap B L (b l))).det) := by
  intro K _ _ d A _ _ _ t ht hloc B _ _ _ _ _ _ hAB F L _ _ _ _ _ _ _ _ _ _ _ _ D hD c b
  classical
  letI : Algebra (MvPolynomial (Fin d) K) A := (MvPolynomial.aeval t).toRingHom.toAlgebra
  letI : Algebra (MvPolynomial (Fin d) K) F :=
    ((algebraMap A F).comp (MvPolynomial.aeval t).toRingHom).toAlgebra
  letI : Algebra (MvPolynomial (Fin d) K) L :=
    ((algebraMap A L).comp (MvPolynomial.aeval t).toRingHom).toAlgebra
  haveI : IsScalarTower (MvPolynomial (Fin d) K) A F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower (MvPolynomial (Fin d) K) F L := IsScalarTower.of_algebraMap_eq (fun x => by
    show algebraMap A L _ = algebraMap F L (algebraMap A F _)
    exact IsScalarTower.algebraMap_apply A F L _)
  haveI : IsScalarTower K A L := IsScalarTower.of_algebraMap_eq (fun x => by
    rw [IsScalarTower.algebraMap_apply K B L, IsScalarTower.algebraMap_apply K A B,
      ← IsScalarTower.algebraMap_apply A B L])
  haveI : FiniteDimensional F L := finite_frac (A := A) (B := B)
  haveI : CharZero A := (RingHom.charZero_iff (algebraMap K A).injective).1 inferInstance
  haveI : CharZero F := (RingHom.charZero_iff (IsFractionRing.injective A F)).1 inferInstance
  haveI : Algebra.IsSeparable F L := inferInstance
  have hτ : ∀ f : MvPolynomial (Fin d) K, algebraMap (MvPolynomial (Fin d) K) L f =
      MvPolynomial.aeval (fun i => algebraMap A L (t i)) f := by
    intro f
    show algebraMap A L (MvPolynomial.aeval t f) = _
    rw [← MvPolynomial.aeval_algebraMap_apply]
    rfl
  have hE : ∀ (k : Fin d) (f : MvPolynomial (Fin d) K), ∃ f',
      ((D k).restrictScalars ℤ) (algebraMap (MvPolynomial (Fin d) K) L f) =
        algebraMap (MvPolynomial (Fin d) K) L f' := by
    intro k f
    refine ⟨MvPolynomial.pderiv k f, ?_⟩
    rw [hτ, hτ]
    exact deriv_aeval_mv _ (D k) k (fun j => hD k j) f
  have hjac : ∀ π : MvPolynomial (Fin d) K, Prime π → ∃ j fj,
      ((D j).restrictScalars ℤ) (algebraMap (MvPolynomial (Fin d) K) L π) =
        algebraMap (MvPolynomial (Fin d) K) L fj ∧ ¬ π ∣ fj := by
    intro π hπ
    obtain ⟨j, hj⟩ := exists_pderiv_not_dvd π hπ
    refine ⟨j, MvPolynomial.pderiv j π, ?_, hj⟩
    rw [hτ, hτ]
    exact deriv_aeval_mv _ (D j) j (fun i => hD j i) π
  have hnat : ∀ m : ℕ, m ≠ 0 → IsUnit (m : MvPolynomial (Fin d) K) := by
    intro m hm
    have hmK : IsUnit (m : K) := (Nat.cast_ne_zero.2 hm).isUnit
    simpa using hmK.map (MvPolynomial.C : K →+* MvPolynomial (Fin d) K)
  have hc : IsIntegral A (algebraMap B L c) :=
    (Algebra.IsIntegral.isIntegral (R := A) c).map (IsScalarTower.toAlgHom A B L)
  have hb : ∀ l, IsIntegral A (algebraMap B L (b l)) := fun l =>
    (Algebra.IsIntegral.isIntegral (R := A) (b l)).map (IsScalarTower.toAlgHom A B L)
  obtain ⟨a, ha⟩ := main_abs (P := MvPolynomial (Fin d) K) (A := A) (F := F) (L := L) (n := Fin d)
    ht hloc (fun k => (D k).restrictScalars ℤ) hE hjac hnat (algebraMap B L c) hc
    (fun l => algebraMap B L (b l)) hb
  exact ⟨a, ha⟩

end GlobalTheory.CompanionTheory.TraceJac
end
end
