module

public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbhyankarExistsFractionLocalisationNormalisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbhyankarExistsLocalKummerElement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbhyankarRootMemMaximalIdealNonZeroDivisors
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArtinianRingKummerAdjoinRootQuotientRootStatement
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
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
import Mathlib.RingTheory.Artinian.Instances
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Artinian.Module
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitMulPowOfMaximalIdealEqSpan
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Filtration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformizerEqPowRamificationIdxMulUnitIntegralCl
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Lemma

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerUnitRadicandQuotientRootIsReduced

section

@[expose] public section

open IsLocalRing Polynomial

namespace GlobalTheory

theorem kummerUnit_quotRoot_isReduced : ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (ϖ : A) (u : Aˣ) (m k : ℕ), Irreducible ϖ → IsUnit (m : A) → 0 < k → IsReduced (AdjoinRoot (Polynomial.X ^ k - Polynomial.C (AdjoinRoot.of (Polynomial.X ^ m - Polynomial.C (u : A) : Polynomial A) ϖ * AdjoinRoot.root (Polynomial.X ^ m - Polynomial.C (u : A) : Polynomial A)) : Polynomial (AdjoinRoot (Polynomial.X ^ m - Polynomial.C (u : A) : Polynomial A))) ⧸ Ideal.span {AdjoinRoot.root (Polynomial.X ^ k - Polynomial.C (AdjoinRoot.of (Polynomial.X ^ m - Polynomial.C (u : A) : Polynomial A) ϖ * AdjoinRoot.root (Polynomial.X ^ m - Polynomial.C (u : A) : Polynomial A)) : Polynomial (AdjoinRoot (Polynomial.X ^ m - Polynomial.C (u : A) : Polynomial A)))}) := by
  intro A _ _ _ ϖ u m k hϖ hm hk
  set f : A[X] := X ^ m - C (u : A) with hf
  set c : AdjoinRoot f := AdjoinRoot.of f ϖ * AdjoinRoot.root f with hc
  set g : (AdjoinRoot f)[X] := X ^ k - C c with hg
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
  have hy : IsUnit (AdjoinRoot.root f) := by
    have h0 := AdjoinRoot.eval₂_root f
    have h1 : AdjoinRoot.root f ^ m = AdjoinRoot.of f (u : A) := by
      rw [hf] at h0
      simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at h0
      exact sub_eq_zero.mp h0
    have h2 : IsUnit (AdjoinRoot.root f ^ m) := by
      rw [h1]; exact (u.isUnit.map _)
    exact (isUnit_pow_iff hm0).mp h2
  have hspan : Ideal.span {c} = (Ideal.span {ϖ}).map (AdjoinRoot.of f) := by
    rw [Ideal.map_span, Set.image_singleton, hc]
    exact Ideal.span_singleton_mul_right_unit hy _
  haveI : (Ideal.span {ϖ}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ
  letI : Field (A ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field _
  have hredK : IsReduced ((A ⧸ Ideal.span {ϖ})[X] ⧸ Ideal.span {f.map (Ideal.Quotient.mk (Ideal.span {ϖ}))}) := by
    rw [← Ideal.isRadical_iff_quotient_reduced, ← isRadical_iff_span_singleton]
    apply Squarefree.isRadical
    apply Polynomial.Separable.squarefree
    have hmap : f.map (Ideal.Quotient.mk (Ideal.span {ϖ})) =
        X ^ m - C ((Units.map (Ideal.Quotient.mk (Ideal.span {ϖ})).toMonoidHom u : (A ⧸ Ideal.span {ϖ})ˣ) : A ⧸ Ideal.span {ϖ}) := by
      simp [hf, Polynomial.map_sub]
    rw [hmap]
    apply separable_X_pow_sub_C_unit
    simpa using hm.map (Ideal.Quotient.mk (Ideal.span {ϖ}))
  have hred1 : IsReduced (AdjoinRoot f ⧸ Ideal.span {c}) := by
    have e := (Ideal.quotEquivOfEq hspan).trans (AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot (Ideal.span {ϖ}) f)
    exact isReduced_of_injective e.toRingHom e.injective
  have hgroot : AdjoinRoot.of g c = AdjoinRoot.root g ^ k := by
    have h0 := AdjoinRoot.eval₂_root g
    rw [hg] at h0
    simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at h0
    exact (sub_eq_zero.mp h0).symm
  let φ0 : AdjoinRoot g →+* AdjoinRoot f ⧸ Ideal.span {c} :=
    AdjoinRoot.lift (Ideal.Quotient.mk (Ideal.span {c})) 0 (by
      rw [hg]
      simp only [eval₂_sub, eval₂_X_pow, eval₂_C, zero_pow hk.ne', zero_sub, neg_eq_zero]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self c))
  let φ : AdjoinRoot g ⧸ Ideal.span {AdjoinRoot.root g} →+* AdjoinRoot f ⧸ Ideal.span {c} :=
    Ideal.Quotient.lift _ φ0 (by
      intro a ha
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      simp [φ0])
  let ψ : AdjoinRoot f ⧸ Ideal.span {c} →+* AdjoinRoot g ⧸ Ideal.span {AdjoinRoot.root g} :=
    Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (AdjoinRoot.of g)) (by
      intro a ha
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [RingHom.comp_apply, map_mul, hgroot, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) k hk))
  have hcomp : ψ.comp φ = RingHom.id _ := by
    apply Ideal.Quotient.ringHom_ext
    apply AdjoinRoot.ringHom_ext
    · ext <;> simp [φ, φ0, ψ]
    · simp [φ, φ0, ψ]
  have hinj : Function.Injective φ := by
    intro x y hxy
    have := congrArg ψ hxy
    simpa [← RingHom.comp_apply, hcomp] using this
  exact isReduced_of_injective φ hinj

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIdealLocalizationEqSpanOfReducedArtinianA

section

@[expose] public section

open IsLocalRing

namespace GlobalTheory

theorem exists_not_mem_mul_mem_span_of_reduced_artinian (R : Type) [CommRing R] (T : R)
    (hred : IsReduced (R ⧸ Ideal.span {T})) (hart : IsArtinianRing (R ⧸ Ideal.span {T}))
    (n : Ideal R) [n.IsPrime] (z : R) (hz : z ∈ n) :
    ∃ c : R, c ∉ n ∧ c * z ∈ Ideal.span {T} := by
  set x : R ⧸ Ideal.span {T} := Ideal.Quotient.mk _ z
  obtain ⟨k, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd x (1 : R ⧸ Ideal.span {T})
  simp only [smul_eq_mul, mul_one] at hy
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective y
  have h0 : x * (1 - x * Ideal.Quotient.mk _ w) = 0 := by
    apply IsReduced.eq_zero
    refine ⟨k + 1, ?_⟩
    have : x ^ k * (1 - x * Ideal.Quotient.mk _ w) = 0 := by
      rw [mul_sub, mul_one, ← mul_assoc, ← pow_succ, hy, sub_self]
    calc (x * (1 - x * Ideal.Quotient.mk _ w)) ^ (k + 1)
        = (x ^ k * (1 - x * Ideal.Quotient.mk _ w)) * (x * (1 - x * Ideal.Quotient.mk _ w) ^ k) := by rw [mul_pow, pow_succ, pow_succ]; ring
      _ = 0 := by rw [this, zero_mul]
  refine ⟨1 - z * w, ?_, ?_⟩
  · intro hc
    have : (1 : R) ∈ n := by
      have := n.add_mem hc (n.mul_mem_right w hz)
      simpa using this
    exact (Ideal.IsPrime.ne_top ‹_›) ((Ideal.eq_top_iff_one _).2 this)
  · rw [← Ideal.Quotient.eq_zero_iff_mem]
    simpa [x, mul_comm] using h0

theorem maximalIdeal_localization_eq_span_of_reduced_artinian :
    ∀ (R : Type) [CommRing R] (T : R), IsReduced (R ⧸ Ideal.span {T}) → IsArtinianRing (R ⧸ Ideal.span {T}) → ∀ (n : Ideal R) [n.IsPrime], T ∈ n → IsLocalRing.maximalIdeal (Localization.AtPrime n) = Ideal.span {algebraMap R (Localization.AtPrime n) T} := by
  intro R _ T hred hart n _ hT
  rw [← Localization.AtPrime.map_eq_maximalIdeal]
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro z hz
    obtain ⟨c, hc, hcz⟩ := exists_not_mem_mul_mem_span_of_reduced_artinian R T hred hart n z hz
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hcz
    have hu : IsUnit (algebraMap R (Localization.AtPrime n) c) :=
      IsLocalization.map_units (Localization.AtPrime n) (⟨c, hc⟩ : n.primeCompl)
    rw [Ideal.mem_comap]
    have : algebraMap R (Localization.AtPrime n) z =
        (hu.unit⁻¹ : (Localization.AtPrime n)ˣ) * algebraMap R _ a * algebraMap R _ T := by
      rw [mul_assoc, ← map_mul, ha, map_mul, ← mul_assoc, IsUnit.val_inv_mul, one_mul]
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_map_of_mem _ hT

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIdealSpanImageUniformizer

section

@[expose] public section

open IsLocalRing

namespace GlobalTheory

theorem eq_pow_mul_unit_of_maximalIdeal_eq_span {V : Type} [CommRing V] [IsLocalRing V]
    [IsNoetherianRing V] (T : V) (hm : maximalIdeal V = Ideal.span {T}) (v : V) (hv : v ≠ 0) :
    ∃ (a : ℕ) (c : V), IsUnit c ∧ v = T ^ a * c := by
  apply GlobalTheory.Pat.unit_mul_pow_of_maximalIdeal_eq_span <;> assumption

theorem maximalIdeal_eq_span_map_of_fractions (V W : Type) [CommRing V] [IsLocalRing V]
    [IsNoetherianRing V] [CommRing W] [IsLocalRing W] (φ : V →+* W) (T : V)
    (hm : IsLocalRing.maximalIdeal V = Ideal.span {T})
    (hTm : φ T ∈ IsLocalRing.maximalIdeal W) (hTn : φ T ∈ nonZeroDivisors W)
    (hfrac : ∀ w : W, ∃ x z : V, φ z ∈ nonZeroDivisors W ∧ φ z * w = φ x) :
    IsLocalRing.maximalIdeal W = Ideal.span {φ T} := by
  have cancel : ∀ (n : ℕ) (y : W), φ T ^ n * y = 0 → y = 0 := fun n y h =>
    (mul_left_mem_nonZeroDivisors_eq_zero_iff (pow_mem hTn n)).mp h
  have surj : ∀ w : W, ∃ v : V, φ v = w := by
    intro w
    obtain ⟨x, z, hz, hzw⟩ := hfrac w
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [map_zero] at hz
      have h1 : (1 : W) = 0 :=
        (mul_left_mem_nonZeroDivisors_eq_zero_iff hz).mp (zero_mul 1)
      exact one_ne_zero h1
    by_cases hx : x = 0
    · refine ⟨0, ?_⟩
      rw [hx, map_zero] at hzw
      rw [map_zero, eq_comm]
      exact (mul_left_mem_nonZeroDivisors_eq_zero_iff hz).mp hzw
    obtain ⟨a, α, hα, rfl⟩ := eq_pow_mul_unit_of_maximalIdeal_eq_span T hm x hx
    obtain ⟨c, β, hβ, rfl⟩ := eq_pow_mul_unit_of_maximalIdeal_eq_span T hm z hz0
    obtain ⟨βi, hβi⟩ := hβ.exists_right_inv
    simp only [map_mul, map_pow] at hzw
    rcases le_or_gt c a with h | h
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
      refine ⟨βi * T ^ d * α, ?_⟩
      have h1 : φ β * w = φ T ^ d * φ α := by
        apply sub_eq_zero.mp
        apply cancel c
        linear_combination hzw
      have h2 : φ βi * φ β = 1 := by rw [← map_mul, mul_comm, hβi, map_one]
      calc φ (βi * T ^ d * α) = φ βi * (φ T ^ d * φ α) := by simp only [map_mul, map_pow]; ring
        _ = φ βi * (φ β * w) := by rw [h1]
        _ = w := by rw [← mul_assoc, h2, one_mul]
    · exfalso
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt h
      have h1 : φ T ^ (d + 1) * φ β * w = φ α := by
        apply sub_eq_zero.mp
        apply cancel a
        linear_combination hzw
      have hmem : φ T ^ (d + 1) * φ β * w ∈ maximalIdeal W := by
        rw [mul_assoc]
        exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hTm _ (Nat.succ_pos d))
      rw [h1, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hmem
      exact hmem (hα.map φ)
  ext w
  constructor
  · intro hw
    obtain ⟨v, rfl⟩ := surj w
    have hv : v ∈ maximalIdeal V := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hw
      exact hw (hu.map φ)
    rw [hm] at hv
    obtain ⟨v', rfl⟩ := Ideal.mem_span_singleton'.mp hv
    rw [map_mul, Ideal.mem_span_singleton']
    exact ⟨φ v', rfl⟩
  · intro hw
    obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.mp hw
    exact Ideal.mul_mem_left _ _ hTm

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbhyankarRamificationIdxEqOne

section

@[expose] public section

open IsLocalRing



namespace GlobalTheory

open IsLocalRing in


open Polynomial in
private lemma maximalIdeal_eq_span_of_kummer_tower (A W : Type) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing W] [IsLocalRing W] (Φ : A →+* W) (ϖ : A) (u : Aˣ) (m k : ℕ)
    (hϖ : Irreducible ϖ) (hm : IsUnit (m : A)) (hk : 0 < k) (y τ : W) (hy : y ^ m = Φ u)
    (hτ : τ ^ k = Φ ϖ * y) (hτm : τ ∈ maximalIdeal W) (hτnz : τ ∈ nonZeroDivisors W)
    (hfrac : ∀ w : W, ∃ x z, x ∈ Subring.closure (Set.range Φ ∪ {τ}) ∧
      z ∈ Subring.closure (Set.range Φ ∪ {τ}) ∧ z ∈ nonZeroDivisors W ∧ z * w = x) :
    maximalIdeal W = Ideal.span {τ} := by
  obtain ⟨gB, hgB_of, hgB_root⟩ : ∃ gB : AdjoinRoot (X ^ m - C (u : A)) →+* W,
      (∀ a, gB (AdjoinRoot.of _ a) = Φ a) ∧ gB (AdjoinRoot.root _) = y :=
    ⟨AdjoinRoot.lift Φ y (by simp [hy]), fun a => AdjoinRoot.lift_of _, AdjoinRoot.lift_root _⟩
  obtain ⟨g, hg_of, hg_root⟩ : ∃ g : AdjoinRoot (X ^ k - C (AdjoinRoot.of (X ^ m - C (u : A)) ϖ *
        AdjoinRoot.root (X ^ m - C (u : A)))) →+* W,
      (∀ b, g (AdjoinRoot.of _ b) = gB b) ∧ g (AdjoinRoot.root _) = τ :=
    ⟨AdjoinRoot.lift gB τ (by simp [hgB_of, hgB_root, hτ]), fun b => AdjoinRoot.lift_of _,
      AdjoinRoot.lift_root _⟩
  haveI hn : (Ideal.comap g (maximalIdeal W)).IsPrime := Ideal.comap_isPrime g (maximalIdeal W)
  have hTn : AdjoinRoot.root (X ^ k - C (AdjoinRoot.of (X ^ m - C (u : A)) ϖ *
      AdjoinRoot.root (X ^ m - C (u : A)))) ∈ Ideal.comap g (maximalIdeal W) := by
    rw [Ideal.mem_comap, hg_root]
    exact hτm
  have hmaxV := _root_.GlobalTheory.maximalIdeal_localization_eq_span_of_reduced_artinian _ _ (_root_.GlobalTheory.kummerUnit_quotRoot_isReduced A ϖ u m k hϖ hm hk)
    (_root_.GlobalTheory.T.isArtinianRing_kummerAdjoinRoot_quotient_root A ϖ u m k hϖ hm hk) _ hTn
  haveI : IsNoetherianRing (AdjoinRoot (X ^ k - C (AdjoinRoot.of (X ^ m - C (u : A)) ϖ *
      AdjoinRoot.root (X ^ m - C (u : A))))) := inferInstance
  haveI : IsNoetherianRing (Localization.AtPrime (Ideal.comap g (maximalIdeal W))) :=
    IsLocalization.isNoetherianRing (Ideal.comap g (maximalIdeal W)).primeCompl _ inferInstance
  have hunit : ∀ s : (Ideal.comap g (maximalIdeal W)).primeCompl, IsUnit (g s) := by
    intro s
    by_contra h
    exact s.2 ((IsLocalRing.mem_maximalIdeal _).2 h)
  have hlift := fun r => IsLocalization.lift_eq (M := (Ideal.comap g (maximalIdeal W)).primeCompl)
    (S := Localization.AtPrime (Ideal.comap g (maximalIdeal W))) hunit r
  obtain ⟨φ, hφ⟩ : ∃ φ : Localization.AtPrime (Ideal.comap g (maximalIdeal W)) →+* W,
      ∀ r, φ (algebraMap _ _ r) = g r := ⟨IsLocalization.lift hunit, hlift⟩
  have key := _root_.GlobalTheory.maximalIdeal_eq_span_map_of_fractions (Localization.AtPrime (Ideal.comap g (maximalIdeal W))) W φ _ hmaxV (by rw [hφ, hg_root]; exact hτm)
    (by rw [hφ, hg_root]; exact hτnz) ?_
  · rw [key, hφ, hg_root]
  intro w
  obtain ⟨x, z, hx, hz, hznz, hzw⟩ := hfrac w
  have hle : Subring.closure (Set.range Φ ∪ {τ}) ≤ φ.range := by
    rw [Subring.closure_le]
    refine Set.union_subset ?_ ?_
    · rintro _ ⟨a, rfl⟩
      exact ⟨algebraMap _ _ (AdjoinRoot.of _ (AdjoinRoot.of _ a)), by rw [hφ, hg_of, hgB_of]⟩
    · rintro _ rfl
      exact ⟨algebraMap _ _ (AdjoinRoot.root _), by rw [hφ, hg_root]⟩
  obtain ⟨x', rfl⟩ := hle hx
  obtain ⟨z', rfl⟩ := hle hz
  exact ⟨x', z', hznz, hzw⟩


open IsLocalRing in


theorem _root_.GlobalTheory.abhyankar_ramificationIdx_eq_one : ∀ (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ) (D : Type) [CommRing D] [Algebra S D],
    Nonempty (D ≃ₐ[S] AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) → Irreducible π → IsUnit (e : S) →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → P.ramificationIdx S ∣ e) →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → ∀ [P.LiesOver (maximalIdeal S)],
      Algebra.IsSeparable (S ⧸ maximalIdeal S) (integralClosure S L ⧸ P)) →
    ∀ [IsDomain D] [IsDiscreteValuationRing D] (Q : Ideal (integralClosure D (TensorProduct S D L))) [Q.IsMaximal],
    Q.ramificationIdx D = 1 := by
  intro S K L _ _ _ _ _ _ _ _ _ _ _ _ π e D _ _ ⟨ψ⟩ hπ he hdiv _ _ _ Q _
  haveI : Q.IsPrime := Ideal.IsMaximal.isPrime inferInstance
  haveI : IsDedekindDomain (integralClosure S L) := integralClosure.isDedekindDomain S K L
  have he0 : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h
      simp at he
    · exact h
  obtain ⟨ht, htnz⟩ := _root_.GlobalTheory.AbhyankarRootUnit.root_mem_maximalIdeal_and_mem_nonZeroDivisors S K L π e D ψ hπ he0 Q
  have hte : (ψ.symm (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π))) ^ e = algebraMap S D π := by
    apply ψ.injective
    rw [map_pow, AlgEquiv.apply_symm_apply, AlgEquiv.commutes]
    have h := AdjoinRoot.eval₂_root (Polynomial.X ^ e - Polynomial.C π)
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C] at h
    rw [sub_eq_zero.1 h]
    rfl
  have htQ : algebraMap D (integralClosure D (TensorProduct S D L))
      (ψ.symm (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π))) ∈ Q := by
    rw [IsScalarTower.algebraMap_apply D (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q)] at ht
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime Q) Q _).1 ht
  have hπO : algebraMap S (integralClosure S L) π ≠ 0 := by
    intro h
    have h1 : algebraMap S L π = 0 := by
      rw [IsScalarTower.algebraMap_apply S (integralClosure S L) L, h, map_zero]
    rw [IsScalarTower.algebraMap_apply S K L, map_eq_zero_iff _ (algebraMap K L).injective,
      IsFractionRing.to_map_eq_zero_iff] at h1
    exact hπ.ne_zero h1
  have hπP : algebraMap S (integralClosure S L) π ∈
      Ideal.comap (_root_.GlobalTheory.AbhyankarLocal.toNorm S L D) Q := by
    rw [Ideal.mem_comap]
    have hpow : _root_.GlobalTheory.AbhyankarLocal.toNorm S L D (algebraMap S (integralClosure S L) π) =
        (algebraMap D (integralClosure D (TensorProduct S D L))
          (ψ.symm (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π)))) ^ e := by
      apply Subtype.ext
      rw [_root_.GlobalTheory.AbhyankarLocal.toNorm_coe, ← map_pow, hte]
      change (1 : D) ⊗ₜ[S] (algebraMap S L π) = algebraMap D (TensorProduct S D L) (algebraMap S D π)
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one π,
        Algebra.algebraMap_eq_smul_one π, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
        Algebra.algebraMap_self, RingHom.id_apply]
    rw [hpow]
    exact Ideal.pow_mem_of_mem Q htQ e he0
  haveI hPmax : (Ideal.comap (_root_.GlobalTheory.AbhyankarLocal.toNorm S L D) Q).IsMaximal := by
    refine Ideal.IsPrime.isMaximal inferInstance ?_
    intro h
    rw [h] at hπP
    exact hπO hπP
  obtain ⟨ϖ, hϖ, u, hu⟩ := _root_.GlobalTheory.pi_eq_pow_ramificationIdx_mul_unit S K L π e D
    (Ideal.comap (_root_.GlobalTheory.AbhyankarLocal.toNorm S L D) Q) hπ hπP
  obtain ⟨k, hk⟩ := hdiv _ hPmax
  obtain ⟨y, hym, hyk⟩ := _root_.GlobalTheory.AbhyankarLocal.exists_kummer_element S K L π e D ψ hπ he0 Q _ k ϖ u hk.symm hu
  have hP0 : Ideal.comap (_root_.GlobalTheory.AbhyankarLocal.toNorm S L D) Q ≠ ⊥ := by
    intro h
    rw [h] at hπP
    exact hπO hπP
  haveI : IsDiscreteValuationRing
      (Localization.AtPrime (Ideal.comap (_root_.GlobalTheory.AbhyankarLocal.toNorm S L D) Q)) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (integralClosure S L) hP0 _
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, mul_zero] at hk
      omega
    · exact h
  have hmu : IsUnit (((Ideal.comap (_root_.GlobalTheory.AbhyankarLocal.toNorm S L D) Q).ramificationIdx S : ℕ) :
      Localization.AtPrime (Ideal.comap (_root_.GlobalTheory.AbhyankarLocal.toNorm S L D) Q)) := by
    have h := he.map (algebraMap S
      (Localization.AtPrime (Ideal.comap (_root_.GlobalTheory.AbhyankarLocal.toNorm S L D) Q)))
    rw [map_natCast, hk, Nat.cast_mul] at h
    exact isUnit_of_mul_isUnit_left h
  have hmax := maximalIdeal_eq_span_of_kummer_tower _ (Localization.AtPrime Q)
    (_root_.GlobalTheory.AbhyankarLocal.locHom Q) ϖ u _ k hϖ hmu hk0 y _ hym hyk ht htnz
    (_root_.GlobalTheory.AbhyankarLocal.exists_frac_closure S K L π e D ψ hπ he0 Q)
  have hunder : Ideal.under D Q = maximalIdeal D := by
    refine IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal inferInstance ?_)
    intro h
    have h1 : ψ.symm (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π)) ∈ Ideal.under D Q := htQ
    rw [h, Ideal.mem_bot] at h1
    rw [h1, map_zero] at htnz
    exact zero_notMem_nonZeroDivisors htnz
  have hmapmax : Ideal.map (algebraMap D (Localization.AtPrime Q)) (Ideal.under D Q) =
      maximalIdeal (Localization.AtPrime Q) := by
    refine le_antisymm ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro d hd
      rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply D (integralClosure D (TensorProduct S D L))
        (Localization.AtPrime Q)]
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime Q) Q _).2 hd
    · rw [hmax, Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_map_of_mem _ htQ
  rw [Ideal.ramificationIdx_def, hmapmax,
    Module.length_eq_one_iff.2 (isSimpleModule_iff_isCoatom.2 (IsLocalRing.maximalIdeal.isMaximal _).out)]
  rfl

end GlobalTheory
end
end
