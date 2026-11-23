module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
public import Mathlib.RingTheory.Ideal.Height
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CupPair
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularTopFormPoleOrderHeightOnePrimeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceMemLocalizationIffForallPrimeStatement
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
public import Mathlib.RingTheory.Ideal.UFD

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureHeightEqOneOfLiesOver

section

@[expose] public section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory

theorem integralClosure_height_eq_one_of_liesOver : ∀ (k F K : Type) [Field k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K] (A : Subalgebra k F) [IsFractionRing A F] (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → ∀ (p : Ideal A), p.IsPrime → p.height = 1 → ∀ Q : Ideal B, Q.IsPrime → (∀ a : A, ∀ b : B, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p)) → Q.height = 1 := by
  intro k F K _ _ _ _ _ _ _ _ A _ B hB p hp hp1 Q hQ hlo

  have hmem : ∀ a : A, algebraMap F K (a : F) ∈ B := by
    intro a
    rw [hB, Subalgebra.mem_restrictScalars, mem_integralClosure_iff]
    exact isIntegral_algebraMap (R := A) (A := K) (x := a)
  let f : A →+* B := ((algebraMap F K).comp A.val.toRingHom).codRestrict B hmem
  letI : Algebra A B := f.toAlgebra
  have hf : ∀ a : A, ((algebraMap A B a : B) : K) = algebraMap F K (a : F) := fun _ => rfl

  let φ : B →ₐ[A] K :=
    { toRingHom := B.val.toRingHom
      commutes' := fun a => rfl }
  have hint : Algebra.IsIntegral A B := by
    refine ⟨fun b => ?_⟩
    have key : ∀ x : K, x ∈ B → x ∈ integralClosure A K := by
      intro x hx
      rw [hB, Subalgebra.mem_restrictScalars] at hx
      exact hx
    have hb : (b : K) ∈ integralClosure A K := key b b.2
    rw [← isIntegral_algHom_iff φ Subtype.val_injective]
    exact hb

  have hcomap : Q.comap (algebraMap A B) = p := by
    ext a
    exact hlo a (algebraMap A B a) (hf a)
  haveI := hp
  haveI := hQ
  have hpne : p ≠ ⊥ := Ideal.ne_bot_of_height_eq_one hp1
  apply le_antisymm
  · rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) by rfl, Ideal.height_le_iff]
    intro Q' hQ' hlt
    haveI := hQ'
    by_contra hge
    have hQ'ne : Q' ≠ ⊥ := by
      intro h
      apply hge
      rw [h, Ideal.height_bot]
      norm_num
    have h1 : Q'.comap (algebraMap A B) ≠ ⊥ := Ideal.IsIntegral.comap_ne_bot A hQ'ne
    have h2 : Q'.comap (algebraMap A B) < p := hcomap ▸ Ideal.IsIntegral.comap_lt_comap hlt
    haveI : (Q'.comap (algebraMap A B)).IsPrime := Ideal.comap_isPrime _ _
    have h3 := Ideal.height_add_one_le_of_lt_of_isPrime h2
    have h4 : 1 ≤ (Q'.comap (algebraMap A B)).height := by
      rw [Order.one_le_iff_pos, pos_iff_ne_zero]
      exact fun h => h1 (Ideal.height_eq_zero_iff_eq_bot.mp h)
    rw [hp1] at h3
    have : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add h4 le_rfl).trans h3
    norm_num at this
  · rw [Order.one_le_iff_pos, pos_iff_ne_zero]
    intro h
    rw [Ideal.height_eq_zero_iff_eq_bot] at h
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hpne
    have : algebraMap A B a ∈ Q := by rw [← Ideal.mem_comap, hcomap]; exact ha
    rw [h, Ideal.mem_bot] at this
    apply ha0
    have := congrArg (fun x : B => (x : K)) this
    simp only [hf, ZeroMemClass.coe_zero] at this
    exact Subtype.ext ((algebraMap F K).injective (this.trans (map_zero _).symm))

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureHeightEqOneOfLiesOverStatement

section

@[expose] public section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.height_eq_one_of_liesOver_height_one : ∀ (k F K : Type) [Field k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K] (A : Subalgebra k F) [IsFractionRing A F] (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → ∀ (p : Ideal A), p.IsPrime → p.height = 1 → ∀ Q : Ideal B, Q.IsPrime → (∀ a : A, ∀ b : B, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p)) → Q.height = 1 := by
  first | (exact @GlobalTheory.integralClosure_height_eq_one_of_liesOver) | (exact GlobalTheory.integralClosure_height_eq_one_of_liesOver) | (intros; apply GlobalTheory.integralClosure_height_eq_one_of_liesOver  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureHeightOneUniformizerRamificationA

section

@[expose] public section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory

theorem exists_localUniformizer_and_order {B : Type} [CommRing B] [IsDomain B]
    [IsNoetherianRing B] [IsIntegrallyClosed B] (Q : Ideal B) [Q.IsPrime] (hQ : Q.height = 1)
    (x : B) (hx0 : x ≠ 0) (hxQ : x ∈ Q) :
    ∃ (s : B) (e : ℕ), 1 ≤ e ∧ s ∈ Q ∧ (∀ y ∈ Q, ∃ c r : B, r ∉ Q ∧ r * y = c * s) ∧
      (∃ a r : B, a ∉ Q ∧ r ∉ Q ∧ r * x = a * s ^ e) := by
  let L := Localization.AtPrime Q
  haveI : IsDiscreteValuationRing L := isDiscreteValuationRing_of_height_eq_one Q hQ L
  have hle : Q.primeCompl ≤ nonZeroDivisors B := Q.primeCompl_le_nonZeroDivisors
  have hinj : Function.Injective (algebraMap B L) := IsLocalization.injective L hle
  have hcomap : (IsLocalRing.maximalIdeal L).comap (algebraMap B L) = Q :=
    IsLocalization.AtPrime.under_maximalIdeal L Q
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible L
  obtain ⟨⟨s, r0⟩, hs⟩ := IsLocalization.surj Q.primeCompl ϖ
  simp only at hs
  have hu0 : IsUnit (algebraMap B L r0) := IsLocalization.map_units L r0
  have hsirr : Irreducible (algebraMap B L s) := by
    rw [← hs]; exact (irreducible_mul_isUnit hu0).mpr hϖ
  have hmax := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hsirr
  have hsQ : s ∈ Q := by
    rw [← hcomap, Ideal.mem_comap, hmax]; exact Ideal.subset_span rfl
  refine ⟨s, ?_⟩
  have hxL : algebraMap B L x ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap B L)]; exact fun h => hx0 (hinj h)
  obtain ⟨n, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hxL hsirr
  have hxm : algebraMap B L x ∈ IsLocalRing.maximalIdeal L := by
    rw [← Ideal.mem_comap, hcomap]; exact hxQ
  refine ⟨n, ?_, hsQ, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      rw [h, pow_zero, mul_one] at hw
      exact (IsLocalRing.mem_maximalIdeal _).mp hxm (hw ▸ w.isUnit)
    · exact h
  · intro y hy
    have hym : algebraMap B L y ∈ Ideal.span {algebraMap B L s} := by
      rw [← hmax, ← Ideal.mem_comap, hcomap]; exact hy
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp hym
    obtain ⟨⟨c, r⟩, hcr⟩ := IsLocalization.surj Q.primeCompl z
    simp only at hcr
    refine ⟨c, r, r.2, hinj ?_⟩
    rw [map_mul, map_mul, ← hz, ← hcr]; ring
  · obtain ⟨⟨a, r⟩, har⟩ := IsLocalization.surj Q.primeCompl (w : L)
    simp only at har
    have hau : IsUnit (algebraMap B L a) := by
      rw [← har]; exact w.isUnit.mul (IsLocalization.map_units L r)
    refine ⟨a, r, ?_, r.2, hinj ?_⟩
    · intro haQ
      have : algebraMap B L a ∈ IsLocalRing.maximalIdeal L := by
        rw [← Ideal.mem_comap, hcomap]; exact haQ
      exact (IsLocalRing.mem_maximalIdeal _).mp this hau
    · rw [map_mul, map_mul, map_pow, ← har, hw]; ring

theorem integralClosure_height_one_uniformizer_ramification :
    ∀ (k F K : Type) [Field k] [CharZero k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F) [IsFractionRing A F], A = Algebra.adjoin k (Set.range u) → ∀ (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → ∀ (p : Ideal A), p.IsPrime → ∀ t : A, Irreducible t → p = Ideal.span {t} → ∀ Q : Ideal B, Q.IsPrime → Q.height = 1 → (∀ a : A, ∀ b : B, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p)) → ∃ (s : B) (e : ℕ), 1 ≤ e ∧ s ∈ Q ∧ (∀ y ∈ Q, ∃ c r : B, r ∉ Q ∧ r * y = c * s) ∧ (∃ a r : B, a ∉ Q ∧ r ∉ Q ∧ (r : K) * algebraMap F K t = a * s ^ e) := by
  intro k F K _ _ _ _ _ _ _ _ _ d u hu A _ hA B hB p _ t ht hpt Q _ hQ hlie
  have hN : IsNoetherianRing A := by
    subst hA
    exact isNoetherianRing_of_ringEquiv _ hu.aevalEquiv.toRingEquiv
  have hI : IsIntegrallyClosed A := by
    subst hA
    have : IsIntegrallyClosed (MvPolynomial (Fin d) k) :=
      UniqueFactorizationMonoid.instIsIntegrallyClosed
    exact IsIntegrallyClosed.of_equiv hu.aevalEquiv.toRingEquiv
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap k F).injective
  subst hB
  have hNB : IsNoetherianRing (integralClosure A K) := by
    letI : IsNoetherianRing A := hN
    letI : IsIntegrallyClosed A := hI
    exact integralClosure.isNoetherianRing (A := A) (K := F) (L := K)
  have hIB : IsIntegrallyClosed (integralClosure A K) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension F
  haveI : IsNoetherianRing ((integralClosure A K).restrictScalars k) := hNB
  haveI : IsIntegrallyClosed ((integralClosure A K).restrictScalars k) := hIB
  have hmem : algebraMap F K (t : F) ∈ (integralClosure A K).restrictScalars k := by
    rw [Subalgebra.mem_restrictScalars, mem_integralClosure_iff]
    exact isIntegral_algebraMap (x := t)
  let x : (integralClosure A K).restrictScalars k := ⟨_, hmem⟩
  have hxQ : x ∈ Q := (hlie t x rfl).mpr (hpt ▸ Ideal.subset_span rfl)
  have hx0 : x ≠ 0 := by
    intro h
    have h' : algebraMap F K (t : F) = 0 := congrArg Subtype.val h
    rw [map_eq_zero_iff _ (algebraMap F K).injective, ZeroMemClass.coe_eq_zero] at h'
    exact ht.ne_zero h'
  obtain ⟨s, e, he, hs, hgen, a, r, ha, hr, hrx⟩ := exists_localUniformizer_and_order Q hQ x hx0 hxQ
  refine ⟨s, e, he, hs, hgen, a, r, ha, hr, ?_⟩
  have := congrArg Subtype.val hrx
  simpa using this

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureHeightOneUniformizerRamificationAStatement

section

@[expose] public section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.exists_uniformizer_ramification_of_height_one : ∀ (k F K : Type) [Field k] [CharZero k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F) [IsFractionRing A F], A = Algebra.adjoin k (Set.range u) → ∀ (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → ∀ (p : Ideal A), p.IsPrime → ∀ t : A, Irreducible t → p = Ideal.span {t} → ∀ Q : Ideal B, Q.IsPrime → Q.height = 1 → (∀ a : A, ∀ b : B, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p)) → ∃ (s : B) (e : ℕ), 1 ≤ e ∧ s ∈ Q ∧ (∀ y ∈ Q, ∃ c r : B, r ∉ Q ∧ r * y = c * s) ∧ (∃ a r : B, a ∉ Q ∧ r ∉ Q ∧ (r : K) * algebraMap F K t = a * s ^ e) := by
  first | (exact @GlobalTheory.integralClosure_height_one_uniformizer_ramification) | (exact GlobalTheory.integralClosure_height_one_uniformizer_ramification) | (intros; apply GlobalTheory.integralClosure_height_one_uniformizer_ramification  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTraceDualLocalizationIffForallRegularForm

section

@[expose] public section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory

theorem heightOne_eq_span_irreducible : ∀ (k F : Type) [Field k] [Field F] [Algebra k F] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F), A = Algebra.adjoin k (Set.range u) → ∀ (p : Ideal A), p.IsPrime → p.height = 1 → ∃ t : A, Irreducible t ∧ p = Ideal.span {t} := by
  intro k F _ _ _ d u hu A hA p hp hh
  subst hA
  haveI := hp
  haveI : UniqueFactorizationMonoid (Algebra.adjoin k (Set.range u)) :=
    hu.aevalEquiv.toMulEquiv.uniqueFactorizationMonoid inferInstance
  obtain ⟨g, hg⟩ := (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hh).principal
  refine ⟨g, ?_, hg⟩
  have hne : g ≠ 0 := by
    rintro rfl
    exact p.ne_bot_of_height_eq_one hh (by rw [hg]; simp)
  rw [hg] at hp
  exact ((Ideal.span_singleton_prime hne).mp hp).irreducible

theorem mem_traceDual_localization_iff_forall_regularForm : ∀ (k F K : Type) [Field k] [CharZero k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F) [IsFractionRing A F], A = Algebra.adjoin k (Set.range u) → ∀ (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → Algebra.Smooth k B → ∀ τ : DR k K →ₗ[K] K, τ (ExteriorAlgebra.ιMulti K d fun j => D k K (algebraMap F K (u j))) = 1 → ∀ (p : Ideal A), p.IsPrime → p.height = 1 → ∀ z : K, (∀ b : B, ∃ r c : A, r ∉ p ∧ (r : F) * Algebra.trace F K (z * b) = c) ↔ ∀ Q : Ideal B, Q.IsPrime → (∀ a : A, ∀ b : B, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p)) → (∃ r : B, r ∉ Q ∧ ∃ y ∈ omB k K B d, τ y = r * z) := by
  intro k F K _ _ _ _ _ _ _ _ _ d u hu A _ hA B hB hsm τ hτ p hp hh z
  obtain ⟨t, ht, hpt⟩ := heightOne_eq_span_irreducible k F d u hu A hA p hp hh
  have h2 : ∀ Q : Ideal B, Q.IsPrime → (∀ a : A, ∀ b : B, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p)) → Q.height = 1 :=
    fun Q hQ hov => GlobalTheory.T.height_eq_one_of_liesOver_height_one k F K A B hB p hp hh Q hQ hov
  have h3 := fun Q hQ hov => GlobalTheory.T.exists_uniformizer_ramification_of_height_one k F K d u hu A hA B hB p hp t ht hpt Q hQ (h2 Q hQ hov) hov
  rw [GlobalTheory.T.trace_mem_localization_iff_forall_prime_alt k F K d u hu A hA B hB p hp hh t ht hpt h2 h3 z]
  constructor
  · intro hl Q hQ hov
    obtain ⟨s, e, he, hs, hun, htd⟩ := h3 Q hQ hov
    exact (GlobalTheory.T.regular_topForm_pole_order_height_one_prime k F K d u hu A hA B hB hsm τ hτ Q hQ (h2 Q hQ hov) t s e ht he hs hun htd z).mpr
      (hl Q hQ hov s e he hs hun htd)
  · intro hr Q hQ hov s e he hs hun htd
    exact (GlobalTheory.T.regular_topForm_pole_order_height_one_prime k F K d u hu A hA B hB hsm τ hτ Q hQ (h2 Q hQ hov) t s e ht he hs hun htd z).mp (hr Q hQ hov)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTraceDualLocalizationIffForallRegularFormStatement

section

@[expose] public section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.mem_traceDual_localization_iff_forall_regularForm_alt : ∀ (k F K : Type) [Field k] [CharZero k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F) [IsFractionRing A F], A = Algebra.adjoin k (Set.range u) → ∀ (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → Algebra.Smooth k B → ∀ τ : DR k K →ₗ[K] K, τ (ExteriorAlgebra.ιMulti K d fun j => D k K (algebraMap F K (u j))) = 1 → ∀ (p : Ideal A), p.IsPrime → p.height = 1 → ∀ z : K, (∀ b : B, ∃ r c : A, r ∉ p ∧ (r : F) * Algebra.trace F K (z * b) = c) ↔ ∀ Q : Ideal B, Q.IsPrime → (∀ a : A, ∀ b : B, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p)) → (∃ r : B, r ∉ Q ∧ ∃ y ∈ omB k K B d, τ y = r * z) := by
  first | (exact @GlobalTheory.mem_traceDual_localization_iff_forall_regularForm) | (exact GlobalTheory.mem_traceDual_localization_iff_forall_regularForm) | (intros; apply GlobalTheory.mem_traceDual_localization_iff_forall_regularForm  <;> assumption)
end
end
