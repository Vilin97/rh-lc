module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Support
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthCokerLsmulEqLengthKerAddSumStatement
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
import Mathlib.Tactic.Lemma
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
public import Mathlib.Data.ENat.BigOperators
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.RingTheory.KrullDimension.Zero

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthKerCokerLsmulQuotientSpanSwap

section

@[expose] public section

namespace GlobalTheory.ASwap

variable {A : Type} [CommRing A] [IsDomain A]

noncomputable def mulMap (a b c : A) (hc : a * b = c) :
    (A ⧸ Ideal.span {a}) →ₗ[A] (A ⧸ Ideal.span {c}) :=
  Submodule.mapQ (Ideal.span {a}) (Ideal.span {c}) (LinearMap.lsmul A A b) (by
    intro x hx
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hx
    simp only [Submodule.mem_comap, LinearMap.lsmul_apply, smul_eq_mul]
    exact Submodule.mem_span_singleton.mpr ⟨r, by rw [← hc]; ring⟩)

lemma mulMap_mk (a b c : A) (hc : a * b = c) (x : A) :
    mulMap a b c hc (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (b * x) := rfl

lemma mulMap_injective (a b c : A) (hb : b ≠ 0) (hc : a * b = c) :
    Function.Injective (mulMap a b c hc) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro q hq
  induction q using Submodule.Quotient.induction_on with
  | H x =>
    change mulMap a b c hc (Ideal.Quotient.mk _ x) = 0 at hq
    rw [mulMap_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hq
    obtain ⟨r, hr⟩ := hq
    change Ideal.Quotient.mk _ x = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
    refine ⟨r, ?_⟩
    apply mul_left_cancel₀ hb
    rw [← hr, ← hc]; ring

lemma map_mulMap_ker (a b c : A) (hc : a * b = c) :
    (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)).map (mulMap a b c hc) =
      Submodule.map (Submodule.mkQ (Ideal.span {c})) (Ideal.span {a} ⊓ Ideal.span {b} : Submodule A A) := by
  ext z
  simp only [Submodule.mem_map, LinearMap.mem_ker, LinearMap.lsmul_apply, Submodule.mem_inf]
  constructor
  · rintro ⟨q, hq, rfl⟩
    induction q using Submodule.Quotient.induction_on with
    | H x =>
      refine ⟨b * x, ⟨?_, ?_⟩, rfl⟩
      · have hq' : Ideal.Quotient.mk (Ideal.span {a}) (b * x) = 0 := hq
        exact Ideal.Quotient.eq_zero_iff_mem.mp hq'
      · exact Ideal.mem_span_singleton'.mpr ⟨x, mul_comm _ _⟩
  · rintro ⟨t, ⟨hta, htb⟩, rfl⟩
    obtain ⟨x, rfl⟩ := Ideal.mem_span_singleton'.mp htb
    refine ⟨Ideal.Quotient.mk _ x, ?_, ?_⟩
    · change Ideal.Quotient.mk (Ideal.span {a}) (b * x) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem, mul_comm]; exact hta
    · change Ideal.Quotient.mk _ (b * x) = Ideal.Quotient.mk _ (x * b)
      rw [mul_comm]

noncomputable def kerEquiv (a b : A) (ha : a ≠ 0) (hb : b ≠ 0) :
    LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b) ≃ₗ[A]
      LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {b}) a) :=
  (Submodule.equivMapOfInjective _ (mulMap_injective a b (a * b) hb rfl) _).trans
    ((LinearEquiv.ofEq _ _ (by
        rw [map_mulMap_ker, map_mulMap_ker b a (a * b) (mul_comm b a), inf_comm])).trans
      (Submodule.equivMapOfInjective _ (mulMap_injective b a (a * b) ha (mul_comm b a)) _).symm)

lemma range_lsmul_eq (a b : A) :
    LinearMap.range (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b) =
      Submodule.map (Submodule.mkQ (Ideal.span {a})) (Ideal.span {b} : Submodule A A) := by
  ext z
  simp only [LinearMap.mem_range, LinearMap.lsmul_apply, Submodule.mem_map]
  constructor
  · rintro ⟨q, rfl⟩
    induction q using Submodule.Quotient.induction_on with
    | H x => exact ⟨x * b, Ideal.mem_span_singleton'.mpr ⟨x, rfl⟩, by
        change Ideal.Quotient.mk _ (x * b) = Ideal.Quotient.mk _ (b * x); rw [mul_comm]⟩
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨x, rfl⟩ := Ideal.mem_span_singleton'.mp ht
    exact ⟨Ideal.Quotient.mk _ x, by
        change Ideal.Quotient.mk _ (b * x) = Ideal.Quotient.mk _ (x * b); rw [mul_comm]⟩

noncomputable def cokerEquiv (a b : A) :
    ((A ⧸ Ideal.span {a}) ⧸ LinearMap.range (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) ≃ₗ[A]
      A ⧸ (Ideal.span {a} ⊔ Ideal.span {b} : Submodule A A) :=
  (Submodule.quotEquivOfEq _ _ (range_lsmul_eq a b)).trans
    (Submodule.quotientQuotientEquivQuotientSup _ _)

end GlobalTheory.ASwap

theorem GlobalTheory.kernel_cokernel_length_swap :
    ∀ (A : Type) [CommRing A] [IsDomain A] (a b : A), a ≠ 0 → b ≠ 0 → Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) = Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {b}) a)) ∧ Module.length A ((A ⧸ Ideal.span {a}) ⧸ LinearMap.range (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) = Module.length A ((A ⧸ Ideal.span {b}) ⧸ LinearMap.range (LinearMap.lsmul A (A ⧸ Ideal.span {b}) a)) := by
  intro A _ _ a b ha hb
  refine ⟨(GlobalTheory.ASwap.kerEquiv a b ha hb).length_eq, ?_⟩
  exact ((GlobalTheory.ASwap.cokerEquiv a b).trans ((Submodule.quotEquivOfEq _ _ (sup_comm _ _)).trans
    (GlobalTheory.ASwap.cokerEquiv b a).symm)).length_eq
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthKerCokerLsmulQuotientSpanSwapStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.length_ker_coker_lsmul_quotient_span_swap : ∀ (A : Type) [CommRing A] [IsDomain A] (a b : A), a ≠ 0 → b ≠ 0 → Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) = Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {b}) a)) ∧ Module.length A ((A ⧸ Ideal.span {a}) ⧸ LinearMap.range (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) = Module.length A ((A ⧸ Ideal.span {b}) ⧸ LinearMap.range (LinearMap.lsmul A (A ⧸ Ideal.span {b}) a)) := by
  first | exact @GlobalTheory.kernel_cokernel_length_swap | exact GlobalTheory.kernel_cokernel_length_swap | (intros; apply GlobalTheory.kernel_cokernel_length_swap <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthSumHeightOneDisjointDivisors

section

@[expose] public section

open IsLocalRing

namespace GlobalTheory.IntersectionSymm

theorem height_add_dim_quotient_le {R : Type} [CommRing R] (p : Ideal R) [hp : p.IsPrime] :
    ((p.height : ℕ∞) : WithBot ℕ∞) + ringKrullDim (R ⧸ p) ≤ ringKrullDim R := by
  let P : PrimeSpectrum R := ⟨p, hp⟩
  haveI : Nonempty (PrimeSpectrum R) := ⟨P⟩
  have h1 : PrimeSpectrum.zeroLocus (p : Set R) = Set.Ici P := by
    ext x
    simp only [PrimeSpectrum.mem_zeroLocus, Set.mem_Ici]
    rfl
  have h2 : ringKrullDim (R ⧸ p) = (Order.coheight P : ℕ∞) := by
    rw [ringKrullDim_quotient, h1, Order.coheight_eq_krullDim_Ici]
  have h3 : p.height = Order.height P := PrimeSpectrum.height_eq_orderHeight P
  rw [h2, h3, ← WithBot.coe_add]
  change _ ≤ Order.krullDim (PrimeSpectrum R)
  rw [Order.krullDim_eq_iSup_height_add_coheight_of_nonempty, WithBot.coe_le_coe]
  exact le_iSup (fun x : PrimeSpectrum R => Order.height x + Order.coheight x) P

theorem arith (h : ℕ∞) (d : WithBot ℕ∞) (h1 : (h : WithBot ℕ∞) + d ≤ 2) (h2 : ¬ d ≤ 0) :
    h ≤ 1 ∧ (h = 1 → d = 1) := by
  induction d using WithBot.recBotCoe with
  | bot => exact absurd bot_le h2
  | coe e =>
    have h1' : h + e ≤ 2 := by
      rw [← WithBot.coe_add, ← WithBot.coe_ofNat, WithBot.coe_le_coe] at h1; exact h1
    have h2' : ¬ e ≤ 0 := fun h => h2 (by exact_mod_cast h)
    induction e using ENat.recTopCoe with
    | top => simp at h1'
    | coe n =>
      induction h using ENat.recTopCoe with
      | top => simp at h1'
      | coe m =>
        have a1 : m + n ≤ 2 := by exact_mod_cast h1'
        have a2 : ¬ n ≤ 0 := fun h => h2' (by exact_mod_cast h)
        refine ⟨by exact_mod_cast (show m ≤ 1 by omega), fun hm => ?_⟩
        have : m = 1 := by exact_mod_cast hm
        have : n = 1 := by omega
        subst this; rfl

theorem not_dim_quotient_le_zero {A : Type} [CommRing A] (p : Ideal A) [p.IsPrime]
    (hne : ¬ p.IsMaximal) : ¬ ringKrullDim (A ⧸ p) ≤ 0 := by
  intro h
  haveI : Ring.KrullDimLE 0 (A ⧸ p) := Ring.krullDimLE_iff.2 (by exact_mod_cast h)
  exact hne (Ideal.Quotient.maximal_of_isField _ Ring.KrullDimLE.isField_of_isDomain)

theorem dim_quotient_eq_one {A : Type} [CommRing A] [IsLocalRing A]
    (hA : ringKrullDim A = 2) (p : Ideal A) [p.IsPrime] (hp : p.height = 1) :
    ringKrullDim (A ⧸ p) = 1 := by
  have h1 := height_add_dim_quotient_le p
  rw [hA] at h1
  have hne : ¬ p.IsMaximal := by
    intro hm
    have := maximalIdeal_height_eq_ringKrullDim (R := A)
    rw [← IsLocalRing.eq_maximalIdeal hm, hp, hA] at this
    exact absurd this (by decide)
  exact (arith _ _ h1 (not_dim_quotient_le_zero p hne)).2 hp

theorem height_one_or_eq_max {A : Type} [CommRing A] [IsDomain A] [IsLocalRing A]
    (hA : ringKrullDim A = 2) (p : Ideal A) [hp : p.IsPrime] (h0 : p ≠ ⊥) :
    p.height = 1 ∨ p = maximalIdeal A := by
  by_cases hm : p = maximalIdeal A
  · exact Or.inr hm
  left
  have hne : ¬ p.IsMaximal := fun h => hm (IsLocalRing.eq_maximalIdeal h)
  have h1 := height_add_dim_quotient_le p
  rw [hA] at h1
  have hle := (arith _ _ h1 (not_dim_quotient_le_zero p hne)).1
  have hz : p.height ≠ 0 := by
    intro hz
    rw [Ideal.height_eq_zero_iff] at hz
    exact h0 (le_bot_iff.1 (hz.2 ⟨Ideal.isPrime_bot, bot_le⟩ bot_le))
  exact le_antisymm hle (ENat.one_le_iff_ne_zero.2 hz)

end GlobalTheory.IntersectionSymm

namespace GlobalTheory.IntersectionSymm

theorem length_localized_quotient {A : Type} [CommRing A] (p : Ideal A) [p.IsPrime] (a : A) :
    Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl (A ⧸ Ideal.span {a})) =
      Module.length (Localization.AtPrime p)
        (Localization.AtPrime p ⧸ Ideal.span {algebraMap A (Localization.AtPrime p) a}) := by
  let f := Algebra.linearMap A (Localization.AtPrime p)
  let M' : Submodule A A := Ideal.span {a}
  let g := M'.toLocalizedQuotient' (Localization.AtPrime p) p.primeCompl f
  let e0 := IsLocalizedModule.iso p.primeCompl g
  let e := e0.extendScalarsOfIsLocalization p.primeCompl (Localization.AtPrime p)
  rw [e.length_eq]
  have h : Submodule.localized' (Localization.AtPrime p) p.primeCompl f M' =
      Ideal.span {algebraMap A (Localization.AtPrime p) a} := by
    rw [Ideal.localized'_eq_map, Ideal.map_span, Set.image_singleton]
  rw [h]

theorem length_quotient_sup {A : Type} [CommRing A] (p : Ideal A) (b : A) :
    Module.length A (A ⧸ (p ⊔ Ideal.span {b})) =
      Module.length (A ⧸ p) ((A ⧸ p) ⧸ Ideal.span {Ideal.Quotient.mk p b}) := by
  rw [← (DoubleQuot.quotQuotEquivQuotSupₐ A p (Ideal.span {b})).toLinearEquiv.length_eq,
    Ideal.map_span, Set.image_singleton, Ideal.Quotient.mkₐ_eq_mk]
  exact Module.length_eq_of_surjective (S := A) (R := A ⧸ p) Ideal.Quotient.mk_surjective

theorem length_localized_ne_top {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (p : Ideal A) [p.IsPrime] (hp : p.height = 1) (a : A) (ha : a ≠ 0) :
    Module.length (Localization.AtPrime p)
        (Localization.AtPrime p ⧸ Ideal.span {algebraMap A (Localization.AtPrime p) a}) ≠ ⊤ := by
  haveI : Ring.KrullDimLE 1 (Localization.AtPrime p) := by
    rw [Ring.krullDimLE_iff, IsLocalization.AtPrime.ringKrullDim_eq_height p, hp]
    rfl
  rw [Module.length_ne_top_iff]
  apply isFiniteLength_quotient_span_singleton
  apply mem_nonZeroDivisors_of_ne_zero
  exact IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors _
    (Ideal.primeCompl_le_nonZeroDivisors p) (mem_nonZeroDivisors_of_ne_zero ha)

theorem length_quotient_ne_top {A : Type} [CommRing A] [IsNoetherianRing A]
    (p : Ideal A) [p.IsPrime] (hd : ringKrullDim (A ⧸ p) = 1) (b : A) (hb : b ∉ p) :
    Module.length (A ⧸ p) ((A ⧸ p) ⧸ Ideal.span {Ideal.Quotient.mk p b}) ≠ ⊤ := by
  haveI : Ring.KrullDimLE 1 (A ⧸ p) := by
    rw [Ring.krullDimLE_iff, hd]
    rfl
  rw [Module.length_ne_top_iff]
  apply isFiniteLength_quotient_span_singleton
  apply mem_nonZeroDivisors_of_ne_zero
  rwa [ne_eq, Ideal.Quotient.eq_zero_iff_mem]

end GlobalTheory.IntersectionSymm

namespace GlobalTheory.IntersectionSymm

theorem support_cases {A : Type} [CommRing A] [IsDomain A] [IsLocalRing A]
    (hA : ringKrullDim A = 2) (a : A) (ha : a ≠ 0) (P : Finset (PrimeSpectrum A))
    (hP : ∀ p, p ∈ P ↔ p.asIdeal.height = 1 ∧ a ∈ p.asIdeal) :
    ∀ p ∈ Module.support A (A ⧸ Ideal.span {a}), p ∈ P ∨ p.asIdeal = maximalIdeal A := by
  intro p hp
  rw [Module.mem_support_iff_of_finite, Ideal.annihilator_quotient] at hp
  have hap : a ∈ p.asIdeal := hp (Ideal.subset_span rfl)
  have h0 : p.asIdeal ≠ ⊥ := fun h => ha (by rw [h] at hap; exact (Submodule.mem_bot A).1 hap)
  rcases height_one_or_eq_max hA p.asIdeal h0 with h | h
  · exact Or.inl ((hP p).2 ⟨h, hap⟩)
  · exact Or.inr h

theorem side {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    (hA : ringKrullDim A = 2) (a b : A) (ha : a ≠ 0) (P Q : Finset (PrimeSpectrum A))
    (hP : ∀ p, p ∈ P ↔ p.asIdeal.height = 1 ∧ a ∈ p.asIdeal)
    (hQ : ∀ p, p ∈ Q ↔ p.asIdeal.height = 1 ∧ b ∈ p.asIdeal) (hdis : Disjoint P Q) :
    Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) ≠ ⊤ ∧
    Module.length A ((A ⧸ Ideal.span {a}) ⧸
        LinearMap.range (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) =
      Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) +
      ∑ p ∈ P, Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal ⧸
          Ideal.span {algebraMap A (Localization.AtPrime p.asIdeal) a}) *
        Module.length (A ⧸ p.asIdeal) ((A ⧸ p.asIdeal) ⧸
          Ideal.span {Ideal.Quotient.mk p.asIdeal b}) := by
  have hmem : ∀ p ∈ P, p.asIdeal.height = 1 ∧ a ∈ p.asIdeal ∧ b ∉ p.asIdeal := by
    intro p hp
    obtain ⟨h1, h2⟩ := (hP p).1 hp
    exact ⟨h1, h2, fun hb => Finset.disjoint_left.1 hdis hp ((hQ p).2 ⟨h1, hb⟩)⟩
  have key := GlobalTheory.T.length_coker_lsmul_eq_length_ker_add_sum' A b P
    (fun p hp => ⟨dim_quotient_eq_one hA p.asIdeal (hmem p hp).1, (hmem p hp).2.2⟩)
    (A ⧸ Ideal.span {a}) (support_cases hA a ha P hP)
  refine ⟨key.1, key.2.trans ?_⟩
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [length_localized_quotient, length_quotient_sup]

theorem terms_ne_top {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    (hA : ringKrullDim A = 2) (a b : A) (ha : a ≠ 0) (P Q : Finset (PrimeSpectrum A))
    (hP : ∀ p, p ∈ P ↔ p.asIdeal.height = 1 ∧ a ∈ p.asIdeal)
    (hQ : ∀ p, p ∈ Q ↔ p.asIdeal.height = 1 ∧ b ∈ p.asIdeal) (hdis : Disjoint P Q) :
    ∀ p ∈ P, Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal ⧸
          Ideal.span {algebraMap A (Localization.AtPrime p.asIdeal) a}) *
        Module.length (A ⧸ p.asIdeal) ((A ⧸ p.asIdeal) ⧸
          Ideal.span {Ideal.Quotient.mk p.asIdeal b}) ≠ ⊤ := by
  intro p hp
  obtain ⟨h1, _⟩ := (hP p).1 hp
  have hb : b ∉ p.asIdeal := fun hb => Finset.disjoint_left.1 hdis hp ((hQ p).2 ⟨h1, hb⟩)
  exact WithTop.mul_ne_top (length_localized_ne_top p.asIdeal h1 a ha)
    (length_quotient_ne_top p.asIdeal (dim_quotient_eq_one hA p.asIdeal h1) b hb)

theorem toNat_sum_mul {ι : Type} (S : Finset ι) (f g : ι → ℕ∞) (h : ∀ i ∈ S, f i * g i ≠ ⊤) :
    ∑ i ∈ S, (f i).toNat * (g i).toNat = (∑ i ∈ S, f i * g i).toNat := by
  rw [ENat.toNat_sum h]
  exact Finset.sum_congr rfl fun i _ => (ENat.toNat_mul _ _).symm

theorem intersection_symm : ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A], ringKrullDim A = 2 → ∀ (a b : A), a ≠ 0 → b ≠ 0 → ∀ (P Q : Finset (PrimeSpectrum A)), (∀ p, p ∈ P ↔ p.asIdeal.height = 1 ∧ a ∈ p.asIdeal) → (∀ p, p ∈ Q ↔ p.asIdeal.height = 1 ∧ b ∈ p.asIdeal) → Disjoint P Q → ∑ p ∈ P, (Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal ⧸ Ideal.span {algebraMap A (Localization.AtPrime p.asIdeal) a})).toNat * (Module.length (A ⧸ p.asIdeal) ((A ⧸ p.asIdeal) ⧸ Ideal.span {Ideal.Quotient.mk p.asIdeal b})).toNat = ∑ p ∈ Q, (Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal ⧸ Ideal.span {algebraMap A (Localization.AtPrime p.asIdeal) b})).toNat * (Module.length (A ⧸ p.asIdeal) ((A ⧸ p.asIdeal) ⧸ Ideal.span {Ideal.Quotient.mk p.asIdeal a})).toNat := by
  intro A _ _ _ _ hA a b ha hb P Q hP hQ hdis
  obtain ⟨hK, hC⟩ := side hA a b ha P Q hP hQ hdis
  obtain ⟨_, hC'⟩ := side hA b a hb Q P hQ hP hdis.symm
  obtain ⟨hk, hc⟩ := GlobalTheory.T.length_ker_coker_lsmul_quotient_span_swap A a b ha hb
  have hS := hC.symm.trans (hc.trans hC')
  rw [← hk] at hS
  have hS' := WithTop.add_left_cancel hK hS
  refine (toNat_sum_mul P _ _ (terms_ne_top hA a b ha P Q hP hQ hdis)).trans
    ((congrArg ENat.toNat hS').trans
      (toNat_sum_mul Q _ _ (terms_ne_top hA b a hb Q P hQ hP hdis.symm)).symm)

end GlobalTheory.IntersectionSymm
end
end
