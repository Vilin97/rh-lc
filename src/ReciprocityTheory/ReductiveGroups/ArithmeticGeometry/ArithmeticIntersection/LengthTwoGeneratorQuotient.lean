module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.LocalLengthAdditivityTorsionFree
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.HeightOneIffDimOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.LengthCokerEqKerAddDimOneOrderSum
public import Mathlib.RingTheory.Length
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.LengthEqOfSurjOfKerEq

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.AI

universe u

theorem length_eq_of_surj_of_ker_eq {A C M N : Type*} [CommRing A] [AddCommGroup C] [Module A C]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] (f : C →ₗ[A] M) (g : C →ₗ[A] N)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (h : LinearMap.ker f = LinearMap.ker g) : Module.length A M = Module.length A N := ((f.quotKerEquivOfSurjective hf).symm.trans ((Submodule.quotEquivOfEq _ _ h).trans
      (g.quotKerEquivOfSurjective hg))).length_eq

theorem mem_ker_lsmul_mk {A : Type u} [CommRing A] (a b x : A) :
    Ideal.Quotient.mk (Ideal.span {a}) x ∈
        LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b) ↔ ∃ y, b * x = a * y := by
  rw [LinearMap.mem_ker, LinearMap.lsmul_apply, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
    ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  rfl

theorem length_ker_swap {A : Type u} [CommRing A] [IsDomain A] (a b : A) (ha : a ≠ 0) (hb : b ≠ 0) :
    Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) =
      Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {b}) a)) := by
  set S : Submodule A (A × A) :=
    LinearMap.ker (b • LinearMap.fst A A A - a • LinearMap.snd A A A) with hSdef
  have hS : ∀ p : A × A, p ∈ S ↔ b * p.1 = a * p.2 := by
    intro p
    rw [hSdef, LinearMap.mem_ker]
    simp [sub_eq_zero]
  have hf0 : ∀ p : S, (Ideal.span {a}).mkQ (p : A × A).1 ∈
      LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b) := by
    intro p
    exact (mem_ker_lsmul_mk a b _).mpr ⟨_, (hS _).mp p.2⟩
  have hg0 : ∀ p : S, (Ideal.span {b}).mkQ (p : A × A).2 ∈
      LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {b}) a) := by
    intro p
    exact (mem_ker_lsmul_mk b a _).mpr ⟨(p : A × A).1, ((hS _).mp p.2).symm⟩
  let f := LinearMap.codRestrict _
    ((Ideal.span {a}).mkQ ∘ₗ LinearMap.fst A A A ∘ₗ S.subtype) hf0
  let g := LinearMap.codRestrict _
    ((Ideal.span {b}).mkQ ∘ₗ LinearMap.snd A A A ∘ₗ S.subtype) hg0
  apply length_eq_of_surj_of_ker_eq f g
  · rintro ⟨k, hk⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective k
    obtain ⟨y, hy⟩ := (mem_ker_lsmul_mk a b x).mp hk
    exact ⟨⟨(x, y), (hS _).mpr hy⟩, rfl⟩
  · rintro ⟨k, hk⟩
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective k
    obtain ⟨x, hx⟩ := (mem_ker_lsmul_mk b a y).mp hk
    exact ⟨⟨(x, y), (hS _).mpr hx.symm⟩, rfl⟩
  · ext ⟨⟨x, y⟩, hp⟩
    have hp' := (hS _).mp hp
    rw [LinearMap.mem_ker, LinearMap.mem_ker, ← Submodule.coe_eq_zero, ← Submodule.coe_eq_zero]
    show (Ideal.span {a}).mkQ x = 0 ↔ (Ideal.span {b}).mkQ y = 0
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton, Ideal.mem_span_singleton]
    simp only at hp'
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨z, ?_⟩
      apply mul_left_cancel₀ ha
      rw [← hp']
      ring
    · rintro ⟨w, rfl⟩
      refine ⟨w, ?_⟩
      apply mul_left_cancel₀ hb
      rw [hp']
      ring

theorem length_ne_top_of_killed {A N : Type*} [CommRing A] [AddCommGroup N] [Module A N]
    [Module.Finite A N] (I : Ideal A) (hI : ∀ r ∈ I, ∀ x : N, r • x = 0)
    (hfin : Module.length A (A ⧸ I) ≠ ⊤) : Module.length A N ≠ ⊤ := by
  rw [Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian] at hfin ⊢
  obtain ⟨hN, hA⟩ := hfin
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := N)
  let φ : Fin n → (A ⧸ I) →ₗ[A] N := fun i =>
    Submodule.liftQ I (LinearMap.toSpanSingleton A N (s i)) (by
      intro r hr
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
      exact hI r hr (s i))
  let Φ : (Fin n → A ⧸ I) →ₗ[A] N := ∑ i, (φ i).comp (LinearMap.proj i)
  have hΦ : Function.Surjective Φ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hs, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨Pi.single i (Submodule.Quotient.mk 1), ?_⟩
    simp only [Φ, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    rw [Finset.sum_eq_single i]
    · rw [Pi.single_eq_same]
      simp only [φ, Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, one_smul]
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  exact ⟨isNoetherian_of_surjective Φ (LinearMap.range_eq_top.mpr hΦ),
    isArtinian_of_surjective _ Φ hΦ⟩

theorem length_ker_ne_top {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] (a b : A)
    (ha : a ≠ 0) (hb : b ≠ 0) (hfin : Module.length A (A ⧸ Ideal.span {a, b}) ≠ ⊤) :
    Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) ≠ ⊤ := by
  apply length_ne_top_of_killed (Ideal.span {a, b}) _ hfin
  rintro r hr ⟨k, hk⟩
  apply Subtype.ext
  simp only [Submodule.coe_smul, Submodule.coe_zero]
  obtain ⟨u, v, rfl⟩ := Ideal.mem_span_pair.mp hr
  have hbk : b • k = 0 := by simpa using hk
  have hak : a • k = 0 := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective k
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self a)
  rw [add_smul, mul_smul, mul_smul, hak, hbk, smul_zero, smul_zero, add_zero]

end ReciprocityTheory.ChartRestriction.G.AI
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.LengthTwoGeneratorQuotient

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.AI

open Module

universe u

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]

theorem length_quotient_kernel (a b : A) :
    length (A ⧸ Ideal.span {a}) (LinearMap.ker (LinearMap.lsmul (A ⧸ Ideal.span {a})
        (A ⧸ Ideal.span {a}) (Ideal.Quotient.mk (Ideal.span {a}) b))) =
      length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) := by
  rw [length_quot_restrict a]
  have h : (LinearMap.ker (LinearMap.lsmul (A ⧸ Ideal.span {a})
        (A ⧸ Ideal.span {a}) (Ideal.Quotient.mk (Ideal.span {a}) b))).restrictScalars A =
      LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b) := by
    ext x
    simp [Algebra.smul_def]
  rw [← h]
  rfl

theorem length_quotient_cokernel (a b : A) :
    length (A ⧸ Ideal.span {a}) ((A ⧸ Ideal.span {a}) ⧸ LinearMap.range (LinearMap.lsmul
        (A ⧸ Ideal.span {a}) (A ⧸ Ideal.span {a}) (Ideal.Quotient.mk (Ideal.span {a}) b))) =
      length A (A ⧸ Ideal.span {a, b}) := by
  rw [length_quot_restrict a]
  set N := LinearMap.range (LinearMap.lsmul
        (A ⧸ Ideal.span {a}) (A ⧸ Ideal.span {a}) (Ideal.Quotient.mk (Ideal.span {a}) b)) with hN
  let f : A →ₗ[A] ((A ⧸ Ideal.span {a}) ⧸ N) :=
    (N.mkQ.restrictScalars A) ∘ₗ (Ideal.span {a} : Ideal A).mkQ
  have hf : Function.Surjective f :=
    (Submodule.mkQ_surjective N).comp (Submodule.mkQ_surjective _)
  have hk : LinearMap.ker f = Ideal.span {a, b} := by
    ext x
    have h1 : x ∈ LinearMap.ker f ↔ Ideal.Quotient.mk (Ideal.span {a}) x ∈ N := by
      rw [LinearMap.mem_ker]
      exact Submodule.Quotient.mk_eq_zero N
    rw [h1, Ideal.mem_span_pair, hN, LinearMap.mem_range]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [LinearMap.lsmul_apply, smul_eq_mul, ← map_mul, Ideal.Quotient.eq,
        Ideal.mem_span_singleton'] at hy
      obtain ⟨c, hc⟩ := hy
      exact ⟨-c, y, by linear_combination -hc⟩
    · rintro ⟨c, y, h⟩
      refine ⟨Ideal.Quotient.mk _ y, ?_⟩
      rw [LinearMap.lsmul_apply, smul_eq_mul, ← map_mul, Ideal.Quotient.eq,
        Ideal.mem_span_singleton']
      exact ⟨-c, by linear_combination -h⟩
  exact ((f.quotKerEquivOfSurjective hf).symm.trans
    (Submodule.quotEquivOfEq _ _ hk)).length_eq

theorem dimension_eq_one_of_add_one (d : WithBot ℕ∞) (hd : d + 1 = 2) : d = 1 := by
  induction d using WithBot.recBotCoe with
  | bot => simp at hd
  | coe n =>
    induction n using ENat.recTopCoe with
    | top => exact absurd hd (by decide)
    | coe m =>
      have e : ((((m + 1 : ℕ) : ℕ∞)) : WithBot ℕ∞) = (((2 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
        rw [Nat.cast_add, Nat.cast_one, WithBot.coe_add, WithBot.coe_one]
        exact hd
      have h2 : ((m + 1 : ℕ) : ℕ∞) = ((2 : ℕ) : ℕ∞) := WithBot.coe_inj.mp e
      have h3 : m + 1 = 2 := Nat.cast_injective h2
      have h4 : m = 1 := by omega
      subst h4
      rfl

theorem length_quotient_sum_ord (h2 : ringKrullDim A = 2) {a : A} (ha : a ≠ 0) (b : A) :
    (∑ᶠ (P : PrimeSpectrum (A ⧸ Ideal.span {a}))
        (_ : ringKrullDim ((A ⧸ Ideal.span {a}) ⧸ P.asIdeal) = 1),
        length (Localization.AtPrime P.asIdeal)
          (LocalizedModule P.asIdeal.primeCompl (A ⧸ Ideal.span {a})) *
            ordMod P (Ideal.Quotient.mk (Ideal.span {a}) b)) =
      ∑ᶠ (p : PrimeSpectrum A) (_ : p.asIdeal.height = 1 ∧ a ∈ p.asIdeal),
          ordLoc p a * ordMod p b := by
  have hmem : ∀ P : PrimeSpectrum (A ⧸ Ideal.span {a}),
      a ∈ (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {a})) P).asIdeal := by
    intro P
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self a)]
    exact zero_mem _
  refine finsum_mem_eq_of_bijOn
    (s := {P : PrimeSpectrum (A ⧸ Ideal.span {a}) |
      ringKrullDim ((A ⧸ Ideal.span {a}) ⧸ P.asIdeal) = 1})
    (t := {p : PrimeSpectrum A | p.asIdeal.height = 1 ∧ a ∈ p.asIdeal})
    (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {a}))) ⟨?_, ?_, ?_⟩ ?_
  · intro P hP
    refine ⟨(height_one_iff_dim_one h2 ha _ (hmem P)).2 ?_, hmem P⟩
    rw [← dim_quot_comap]
    exact hP
  · exact (PrimeSpectrum.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective).injOn
  · rintro p ⟨hp, hap⟩
    have : p ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {a}))) := by
      rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
        Ideal.mk_ker, PrimeSpectrum.mem_zeroLocus]
      exact (Ideal.span_singleton_le_iff_mem _).2 hap
    obtain ⟨P, rfl⟩ := this
    refine ⟨P, ?_, rfl⟩
    change ringKrullDim _ = 1
    rw [dim_quot_comap]
    exact (height_one_iff_dim_one h2 ha _ hap).1 hp
  · intro P _
    rw [length_loc_quot, ordMod_quot]

theorem length_quotient_pair_formula (h2 : ringKrullDim A = 2) {a : A} (ha : a ≠ 0) (b : A)
    (hfin : length A (A ⧸ Ideal.span {a, b}) ≠ ⊤) :
    length A (A ⧸ Ideal.span {a, b}) =
      length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) +
        ∑ᶠ (p : PrimeSpectrum A) (_ : p.asIdeal.height = 1 ∧ a ∈ p.asIdeal),
          ordLoc p a * ordMod p b := by
  by_cases hu : IsUnit a
  · have h1 : Subsingleton (A ⧸ Ideal.span {a}) :=
      Ideal.Quotient.subsingleton_iff.2 (Ideal.span_singleton_eq_top.2 hu)
    have h3 : Subsingleton (A ⧸ Ideal.span {a, b}) :=
      Ideal.Quotient.subsingleton_iff.2
        (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (by simp)) hu)
    have h4 : ∀ p : PrimeSpectrum A, a ∉ p.asIdeal := fun p hp =>
      p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hp hu)
    simp [h4]
  · have hm : a ∈ IsLocalRing.maximalIdeal A := hu
    have hnt : Nontrivial (A ⧸ Ideal.span {a}) :=
      Ideal.Quotient.nontrivial_iff.2 (fun h => hu (Ideal.span_singleton_eq_top.1 h))
    have hloc : IsLocalRing (A ⧸ Ideal.span {a}) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    have hd := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero ha) hm
    have hd1 : ringKrullDim (A ⧸ Ideal.span {a}) = 1 := by
      rw [h2] at hd
      exact dimension_eq_one_of_add_one _ hd
    have key := (dimOneFormula (A ⧸ Ideal.span {a}) (A ⧸ Ideal.span {a})
      (Ideal.Quotient.mk (Ideal.span {a}) b) hd1 (by rw [length_quotient_cokernel]; exact hfin)).2
    rw [length_quotient_cokernel, length_quotient_kernel, length_quotient_sum_ord h2 ha] at key
    exact key

end

theorem length_two_generator_quotient : LocalLengthMultiplicativity := by
  intro A _ _ _ _ a b h2 ha hb hfin
  have hfin' : length A (A ⧸ Ideal.span {b, a}) ≠ ⊤ := by rwa [Set.pair_comm]
  have h1 := length_quotient_pair_formula h2 ha b hfin
  have h1' := length_quotient_pair_formula h2 hb a hfin'
  have hs := length_ker_swap a b ha hb
  have ht := length_ker_ne_top a b ha hb hfin
  refine ⟨h1, ⟨hs, ht⟩, ?_⟩
  rw [Set.pair_comm, h1, ← hs] at h1'
  exact ENat.add_right_injective_of_ne_top ht h1'

end ReciprocityTheory.ChartRestriction.G.AI
end
end
