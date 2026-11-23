module

public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOfFinOrderFbar
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
public import Formalism.CyclotomicNorms.StatementT
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsRingEquivOfIsTranscendenceBasis
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Finsupp.Encodable
public import Mathlib.RingTheory.Algebraic.Cardinality
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyResidueFieldUnitBallEquiv

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTeichmullerReindexComplexPlace

section

@[expose] public section

open Polynomial

noncomputable section

namespace GlobalTheory.TeichAt

open Formalism.L2.NT GlobalTheory.ParRay

theorem orderOf_coprime {g : ℕ} [hg : Fact g.Prime] {x : Formalism.CyclotomicNorms.Fbar g} (hx : x ≠ 0) : (orderOf x).Coprime g := by
  have hpos := (isOfFinOrder_fbar hx).orderOf_pos
  set n := orderOf x with hn
  refine (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hg.out).2 ?_))
  intro hdvd
  have hm : g ^ n.factorization g * (n / g ^ n.factorization g) = n := Nat.ordProj_mul_ordCompl_eq_self n g
  have h1 : x ^ (g ^ n.factorization g * (n / g ^ n.factorization g)) = 1 := by rw [hm, hn, pow_orderOf_eq_one]
  have h2 : x ^ (n / g ^ n.factorization g) = 1 := pow_eq_one_of_charP g x _ _ h1
  have h3 : n ∣ n / g ^ n.factorization g := orderOf_dvd_of_pow_eq_one h2
  exact Nat.not_dvd_ordCompl hg.out hpos.ne' (hdvd.trans h3)

theorem map_zero_of_inj {Ω : Type} [Field Ω] {g : ℕ} [Fact g.Prime] (t : Formalism.CyclotomicNorms.Fbar g →* Ω)
    (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) : t 0 = 0 := by
  classical
  have h : t 0 * t 0 = t 0 := by rw [← map_mul, mul_zero]
  by_contra h0
  have h1 : t 0 = 1 := (mul_eq_left₀ h0).1 h
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset (Formalism.CyclotomicNorms.Fbar g))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  apply hx.2
  refine ht x 1 hx.1 one_ne_zero ?_
  have : t x = t x * t 0 := by rw [h1, mul_one]
  rw [this, ← map_mul, mul_zero, h1, map_one]

theorem exists_teich_reindex : ∀ (g : ℕ) [Fact g.Prime] (A : ValuationSubring ℂ)
    (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) (t : Formalism.CyclotomicNorms.Fbar g →* ℂ),
    (∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) → ∃ t₀ : Formalism.CyclotomicNorms.Fbar g →* ℂ,
      Formalism.L2.NT.IsTeich A κ t₀ ∧ ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t₀ x = t₀ y → x = y := by
  intro g _ A κ t ht
  set s := redHom A κ t with hs_def
  have hs : ∀ x, s x = redThrough A κ (t x) := fun x => rfl
  have ht0 : t 0 = 0 := map_zero_of_inj t ht
  have hs0 : s 0 = 0 := by
    rw [hs, ht0]; unfold redThrough; rw [dite_eq_left (zero_mem A)]
    have : (⟨0, zero_mem A⟩ : A) = 0 := rfl
    rw [this, map_zero, map_zero]
  have hsne : ∀ x, x ≠ 0 → s x ≠ 0 := by
    intro x hx h0
    have hpos := (isOfFinOrder_fbar hx).orderOf_pos
    have : s x ^ orderOf x = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
    rw [h0, zero_pow hpos.ne'] at this
    exact zero_ne_one this
  have hinj : Function.Injective s := by
    intro x y h
    rcases eq_or_ne x 0 with rfl | hx
    · rcases eq_or_ne y 0 with rfl | hy
      · rfl
      · exact absurd (h.symm.trans hs0) (hsne y hy)
    · rcases eq_or_ne y 0 with rfl | hy
      · exact absurd (h.trans hs0) (hsne x hx)
      · exact redHom_inj A κ t ht x y hx hy (orderOf_coprime hx) (orderOf_coprime hy) h
  have hsurj : Function.Surjective s := by
    intro y
    rcases eq_or_ne y 0 with rfl | hy
    · exact ⟨0, hs0⟩
    have hn := (isOfFinOrder_fbar hy).orderOf_pos
    set n := orderOf y
    have hmem : ∀ z : Formalism.CyclotomicNorms.Fbar g, z ∈ nthRootsFinset n (1 : Formalism.CyclotomicNorms.Fbar g) ↔ z ^ n = 1 :=
      fun z => mem_nthRootsFinset hn 1
    obtain ⟨a, -, ha⟩ := Finset.surj_on_of_inj_on_of_card_le (s := nthRootsFinset n (1 : Formalism.CyclotomicNorms.Fbar g))
      (t := nthRootsFinset n (1 : Formalism.CyclotomicNorms.Fbar g)) (fun a _ => s a)
      (fun a ha => (hmem _).2 (by rw [← map_pow, (hmem a).1 ha, map_one]))
      (fun a₁ a₂ _ _ h => hinj h) le_rfl y ((hmem y).2 (pow_orderOf_eq_one y))
    exact ⟨a, ha.symm⟩
  let e : Formalism.CyclotomicNorms.Fbar g ≃* Formalism.CyclotomicNorms.Fbar g := MulEquiv.ofBijective s ⟨hinj, hsurj⟩
  have he : ∀ x, e x = s x := fun x => rfl
  refine ⟨t.comp e.symm.toMonoidHom, ?_, ?_⟩
  · intro x
    refine ⟨mem_of_monoidHom A t _, ?_⟩
    have h1 : s (e.symm x) = x := by rw [← he, MulEquiv.apply_symm_apply]
    have h2 := hs (e.symm x)
    unfold redThrough at h2
    rw [dite_eq_left (mem_of_monoidHom A t _)] at h2
    exact h2.symm.trans h1
  · intro x y hx hy h
    have hx' : e.symm x ≠ 0 := fun h0 => hx (by rw [← e.apply_symm_apply x, h0, he, hs0])
    have hy' : e.symm y ≠ 0 := fun h0 => hy (by rw [← e.apply_symm_apply y, h0, he, hs0])
    exact e.symm.injective (ht _ _ hx' hy' h)

end GlobalTheory.TeichAt

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTeichmullerReindexComplexPlaceStatement

section

@[expose] public section

open Polynomial

theorem _root_.GlobalTheory.T.exists_teichmuller_reindex_complexPlace : ∀ (g : ℕ) [Fact g.Prime] (A : ValuationSubring ℂ) (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) (t : Formalism.CyclotomicNorms.Fbar g →* ℂ), (∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) → ∃ t₀ : Formalism.CyclotomicNorms.Fbar g →* ℂ, Formalism.L2.NT.IsTeich A κ t₀ ∧ ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t₀ x = t₀ y → x = y := by
  first | exact @GlobalTheory.TeichAt.exists_teich_reindex | exact GlobalTheory.TeichAt.exists_teich_reindex | (intros; apply GlobalTheory.TeichAt.exists_teich_reindex <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FbarExistsComplexAutCompEq

section

@[expose] public section

open Polynomial

noncomputable section

namespace GlobalTheory.TeichGalois

variable {g : ℕ} [Fact g.Prime]

theorem map_zero_eq_zero (t : Formalism.CyclotomicNorms.Fbar g →* ℂ)
    (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) : t 0 = 0 := by
  classical
  have h2 : t 0 * (t 0 - 1) = 0 := by
    rw [mul_sub, mul_one, ← map_mul, mul_zero, sub_self]
  rcases mul_eq_zero.1 h2 with h | h
  · exact h
  · exfalso
    have h1 : t 0 = 1 := sub_eq_zero.1 h
    have hall : ∀ x, t x = 1 := fun x => by
      have : t (x * 0) = t x * t 0 := map_mul t x 0
      rw [mul_zero, h1, mul_one] at this
      exact this.symm
    obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset (Formalism.CyclotomicNorms.Fbar g))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
    exact hy.2 (ht y 1 hy.1 one_ne_zero (by rw [hall, hall]))

theorem exists_coprime_pow_eq_one {x : Formalism.CyclotomicNorms.Fbar g} (hx : x ≠ 0) :
    ∃ m : ℕ, g.Coprime m ∧ x ^ m = 1 := by
  let K := IntermediateField.adjoin (ZMod g) ({x} : Set (Formalism.CyclotomicNorms.Fbar g))
  haveI : FiniteDimensional (ZMod g) K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  haveI : Finite K := Module.finite_of_finite (ZMod g)
  have hxK : (⟨x, IntermediateField.mem_adjoin_simple_self _ x⟩ : K) ≠ 0 := by
    intro h; apply hx; simpa using congrArg Subtype.val h
  let u := Units.mk0 _ hxK
  have hn : x ^ orderOf u = 1 := by
    have h3 : (u : K) ^ orderOf u = 1 := by
      rw [← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]
    have h4 : ((u : K) : Formalism.CyclotomicNorms.Fbar g) ^ orderOf u = 1 := by
      rw [← IntermediateField.coe_pow, h3, IntermediateField.coe_one]
    exact h4
  have hpos : 0 < orderOf u := orderOf_pos u
  obtain ⟨a, m, hm, heq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hpos.ne' g (Fact.out : g.Prime).ne_one
  refine ⟨m, (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hm, ?_⟩
  have h2 : (x ^ m - 1) ^ (g ^ a) = 0 := by
    rw [sub_pow_char_pow, one_pow, ← pow_mul, mul_comm, ← heq, hn, sub_self]
  exact sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero _ (Fact.out : g.Prime).ne_zero) |>.1 h2)

theorem exists_common_exponent (s : Finset (Formalism.CyclotomicNorms.Fbar g)) (hs : ∀ x ∈ s, x ≠ 0) :
    ∃ m : ℕ, g.Coprime m ∧ ∀ x ∈ s, x ^ m = 1 := by
  have h := fun x (hx : x ∈ s) => exists_coprime_pow_eq_one (hs x hx)
  choose! e he using h
  refine ⟨∏ x ∈ s, e x, Nat.Coprime.prod_right fun x hx => (he x hx).1, fun x hx => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem e hx
  rw [hc, pow_mul, (he x hx).2, one_pow]

theorem isPrimitiveRoot_map (t : Formalism.CyclotomicNorms.Fbar g →* ℂ)
    (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) {u : Formalism.CyclotomicNorms.Fbar g} {m : ℕ}
    (hm : 0 < m) (hu : IsPrimitiveRoot u m) : IsPrimitiveRoot (t u) m := by
  have hu0 : u ≠ 0 := hu.ne_zero hm.ne'
  refine ⟨by rw [← map_pow, hu.pow_eq_one, map_one], fun l hl => hu.dvd_of_pow_eq_one l ?_⟩
  exact ht _ _ (pow_ne_zero _ hu0) one_ne_zero (by rw [map_pow, hl, map_one])

theorem lift_apply_eq_sum (t : Formalism.CyclotomicNorms.Fbar g →* ℂ) (f : MonoidAlgebra ℤ (Formalism.CyclotomicNorms.Fbar g)) :
    MonoidAlgebra.lift ℤ ℂ (Formalism.CyclotomicNorms.Fbar g) t f = ∑ x ∈ f.coeff.support, (f.coeff x : ℂ) * t x := by
  rw [MonoidAlgebra.lift_apply, Finsupp.sum]
  simp [zsmul_eq_mul]

theorem lift_eq_zero_of_lift_eq_zero (t t' : Formalism.CyclotomicNorms.Fbar g →* ℂ)
    (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y)
    (ht' : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t' x = t' y → x = y)
    (f : MonoidAlgebra ℤ (Formalism.CyclotomicNorms.Fbar g)) (h : MonoidAlgebra.lift ℤ ℂ (Formalism.CyclotomicNorms.Fbar g) t' f = 0) :
    MonoidAlgebra.lift ℤ ℂ (Formalism.CyclotomicNorms.Fbar g) t f = 0 := by
  classical
  set s := f.coeff.support.filter (· ≠ 0) with hs
  obtain ⟨m, hmc, hpow⟩ := exists_common_exponent s (fun x hx => (Finset.mem_filter.1 hx).2)
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact (Fact.out : g.Prime).ne_one (Nat.coprime_zero_right _ |>.1 hmc)
  have hm : 0 < m := Nat.pos_of_ne_zero hm0
  haveI : NeZero m := ⟨hm0⟩
  haveI : NeZero (m : Formalism.CyclotomicNorms.Fbar g) := ⟨by
    rw [Ne, CharP.cast_eq_zero_iff (Formalism.CyclotomicNorms.Fbar g) g]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).1 hmc⟩
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_root (cyclotomic m (Formalism.CyclotomicNorms.Fbar g))
    (degree_cyclotomic_pos m _ hm).ne'
  have hu : IsPrimitiveRoot u m := isRoot_cyclotomic_iff.1 hu
  have hk : ∀ x ∈ s, ∃ i : ℕ, u ^ i = x := fun x hx => by
    obtain ⟨i, -, hi⟩ := hu.eq_pow_of_pow_eq_one (hpow x hx)
    exact ⟨i, hi⟩
  choose! k hk using hk
  let P : ℤ[X] := ∑ x ∈ s, C (f.coeff x) * X ^ (k x)
  have heval : ∀ τ : Formalism.CyclotomicNorms.Fbar g →* ℂ, τ 0 = 0 →
      MonoidAlgebra.lift ℤ ℂ (Formalism.CyclotomicNorms.Fbar g) τ f = aeval (τ u) P := by
    intro τ hτ
    rw [lift_apply_eq_sum, ← Finset.sum_filter_of_ne (p := (· ≠ 0)) (fun x _ hx h0 => hx (by rw [h0, hτ, mul_zero]))]

    simp only [P, map_sum, map_mul, aeval_C, map_pow, aeval_X, algebraMap_int_eq, eq_intCast, map_intCast]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [← map_pow, hk x hx]
  have hζ := isPrimitiveRoot_map t ht hm hu
  have hζ' := isPrimitiveRoot_map t' ht' hm hu
  have h1 : aeval (t' u) P = 0 := by rw [← heval t' (map_zero_eq_zero t' ht'), h]
  have hdvd : minpoly ℤ (t' u) ∣ P := minpoly.isIntegrallyClosed_dvd (hζ'.isIntegral hm) h1
  rw [← cyclotomic_eq_minpoly hζ' hm, cyclotomic_eq_minpoly hζ hm] at hdvd
  rw [heval t (map_zero_eq_zero t ht)]
  exact aeval_eq_zero_of_dvd_aeval_eq_zero hdvd (minpoly.aeval ℤ (t u))

instance countable_fbar : Countable (Formalism.CyclotomicNorms.Fbar g) :=
  Cardinal.mk_le_aleph0_iff.1 ((Algebra.IsAlgebraic.cardinalMk_le_max (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).trans
    (max_le Cardinal.mk_le_aleph0 le_rfl))

theorem exists_ringEquiv_comp_eq : ∀ (g : ℕ) [Fact g.Prime] (t t' : Formalism.CyclotomicNorms.Fbar g →* ℂ), (∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) → (∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t' x = t' y → x = y) → ∃ σ : ℂ ≃+* ℂ, ∀ x, σ (t' x) = t x := by
  intro g _ t t' ht ht'
  let α : MonoidAlgebra ℤ (Formalism.CyclotomicNorms.Fbar g) →+* ℂ := (MonoidAlgebra.lift ℤ ℂ (Formalism.CyclotomicNorms.Fbar g) t').toRingHom
  let β : MonoidAlgebra ℤ (Formalism.CyclotomicNorms.Fbar g) →+* ℂ := (MonoidAlgebra.lift ℤ ℂ (Formalism.CyclotomicNorms.Fbar g) t).toRingHom
  have hker : RingHom.ker α ≤ RingHom.ker β := fun f hf =>
    lift_eq_zero_of_lift_eq_zero t t' ht ht' f hf
  have hker' : RingHom.ker β ≤ RingHom.ker α := fun f hf =>
    lift_eq_zero_of_lift_eq_zero t' t ht' ht f hf
  haveI : (RingHom.ker α).IsPrime := RingHom.ker_isPrime α
  let Q := MonoidAlgebra ℤ (Formalism.CyclotomicNorms.Fbar g) ⧸ RingHom.ker α
  let α' : Q →+* ℂ := RingHom.kerLift α
  let β' : Q →+* ℂ := Ideal.Quotient.lift (RingHom.ker α) β hker
  have hα' : Function.Injective α' := RingHom.kerLift_injective α
  have hβ' : Function.Injective β' := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective q
    have : β f = 0 := hq
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hker' this)
  haveI : Countable (MonoidAlgebra ℤ (Formalism.CyclotomicNorms.Fbar g)) :=
    Function.Injective.countable (f := MonoidAlgebra.coeff) (fun a b h => by ext x; rw [h])
  haveI : Countable Q := Function.Surjective.countable Ideal.Quotient.mk_surjective
  haveI : Countable (FractionRing Q) :=
    Function.Surjective.countable (IsLocalization.mk'_surjective (nonZeroDivisors Q) (S := FractionRing Q))
  let a : FractionRing Q →+* ℂ := IsFractionRing.lift hα'
  let b : FractionRing Q →+* ℂ := IsFractionRing.lift hβ'
  obtain ⟨σ, hσ⟩ := GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq a b
  refine ⟨σ, fun x => ?_⟩
  have h := hσ (algebraMap Q (FractionRing Q) (Ideal.Quotient.mk _ (MonoidAlgebra.single x 1)))
  have ha : a (algebraMap Q (FractionRing Q) (Ideal.Quotient.mk _ (MonoidAlgebra.single x 1))) = t' x := by
    simp only [a]
    rw [IsFractionRing.lift_algebraMap]
    simp only [α']
    rw [RingHom.kerLift_mk]
    simp [α, MonoidAlgebra.lift_single]
  have hb : b (algebraMap Q (FractionRing Q) (Ideal.Quotient.mk _ (MonoidAlgebra.single x 1))) = t x := by
    simp only [b]
    rw [IsFractionRing.lift_algebraMap]
    show β (MonoidAlgebra.single x 1) = t x
    simp [β, MonoidAlgebra.lift_single]
  rw [ha, hb] at h
  exact h

end GlobalTheory.TeichGalois
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FbarExistsComplexAutCompEqStatement

section

@[expose] public section

open Polynomial

theorem _root_.GlobalTheory.T.fbar_exists_complexAut_comp_eq : ∀ (g : ℕ) [Fact g.Prime] (t t' : Formalism.CyclotomicNorms.Fbar g →* ℂ), (∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) → (∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t' x = t' y → x = y) → ∃ σ : ℂ ≃+* ℂ, ∀ x, σ (t' x) = t x := by
  first | exact @GlobalTheory.TeichGalois.exists_ringEquiv_comp_eq | exact GlobalTheory.TeichGalois.exists_ringEquiv_comp_eq | (intros; apply GlobalTheory.TeichGalois.exists_ringEquiv_comp_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPlaceIsTeichmullerLiftFbar

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC Formalism.L2.NC NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting

noncomputable section
namespace GlobalTheory.TeichPlace

theorem exists_place_isTeich : ∀ (g : ℕ) [Fact g.Prime] (t : Formalism.CyclotomicNorms.Fbar g →* ℂ), (∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) → ∃ (A : ValuationSubring ℂ) (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g), IsTeich A κ t := by
  intro g _ t ht
  obtain ⟨ι⟩ := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex g
  obtain ⟨κ₀⟩ := GlobalTheory.HeightCounting.nonempty_residueField_unitBall_equiv ι
  obtain ⟨t₀, ht₀, hinj₀⟩ := GlobalTheory.T.exists_teichmuller_reindex_complexPlace g (GlobalTheory.HeightCounting.unitBall ι) κ₀ t ht
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.fbar_exists_complexAut_comp_eq g t t₀ ht hinj₀
  let A : ValuationSubring ℂ := (GlobalTheory.HeightCounting.unitBall ι).comap (σ.symm : ℂ →+* ℂ)
  have hmem : ∀ z : ℂ, z ∈ A ↔ σ.symm z ∈ GlobalTheory.HeightCounting.unitBall ι := fun z => ValuationSubring.mem_comap
  let e : A ≃+* GlobalTheory.HeightCounting.unitBall ι :=
    { toFun := fun a => ⟨σ.symm a, (hmem a).1 a.2⟩
      invFun := fun b => ⟨σ b, (hmem _).2 (by simpa using b.2)⟩
      left_inv := fun a => Subtype.ext (by simp)
      right_inv := fun b => Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  refine ⟨A, (IsLocalRing.ResidueField.mapEquiv e).trans κ₀, fun x => ?_⟩
  have hx : σ.symm (t x) = t₀ x := by rw [← hσ x, RingEquiv.symm_apply_apply]
  obtain ⟨h₀, e₀⟩ := ht₀ x
  refine ⟨(hmem _).2 (hx ▸ h₀), ?_⟩
  refine Eq.trans ?_ e₀
  change κ₀ (IsLocalRing.ResidueField.map (e : A →+* GlobalTheory.HeightCounting.unitBall ι) (IsLocalRing.residue A _)) = _
  rw [IsLocalRing.ResidueField.map_residue]
  congr 2
  exact Subtype.ext hx

end GlobalTheory.TeichPlace
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPlaceIsTeichmullerLiftFbarStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC Formalism.L2.NC NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting

theorem _root_.GlobalTheory.T.exists_place_isTeichmuller_lift_Fbar : ∀ (g : ℕ) [Fact g.Prime] (t : Formalism.CyclotomicNorms.Fbar g →* ℂ), (∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) → ∃ (A : ValuationSubring ℂ) (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g), IsTeich A κ t := by
  first | exact @GlobalTheory.TeichPlace.exists_place_isTeich | exact GlobalTheory.TeichPlace.exists_place_isTeich | (intros; apply GlobalTheory.TeichPlace.exists_place_isTeich <;> assumption)
end
end
