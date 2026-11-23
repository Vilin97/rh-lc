module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntBTmulBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicIntegralTensorBasisIffExistsIntegralMultipleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyAdicIntegralSpanClosedMulStar
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
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
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyAdicIntegralSpanClosedMulStar
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.RingTheory.DedekindDomain.Instances
import Mathlib.RingTheory.SimpleRing.Principal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntBTmulBasis
public import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicTensorExistsRationalAddIntegralMul

section

@[expose] public section

open Matrix NumberField IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.AdicSpan

theorem exists_rat_sub_le (v : HeightOneSpectrum ℤ) (c d : v.adicCompletion ℚ) (hd : d ≠ 0) :
    ∃ q : ℚ, Valued.v (c - algebraMap ℚ (v.adicCompletion ℚ) q) ≤ Valued.v d := by
  have hset : {y : v.adicCompletion ℚ | Valued.v y ≤ Valued.v d} =
      {y | Valued.v.restrict y ≤ Valued.v.restrict d} := by
    ext y; simp only [Set.mem_setOf_eq, Valuation.restrict_le_iff]
  have hball : IsOpen {y : v.adicCompletion ℚ | Valued.v y ≤ Valued.v d} := by
    rw [hset]; exact Valued.isOpen_closedBall _ (by simpa using hd)
  have ho : IsOpen {y : v.adicCompletion ℚ | Valued.v (c - y) ≤ Valued.v d} :=
    hball.preimage (continuous_const.sub continuous_id)
  obtain ⟨q, hq⟩ := (HeightOneSpectrum.denseRange_algebraMap (R := ℤ) (K := ℚ) v).exists_mem_open ho
    ⟨c, by simp⟩
  exact ⟨q, hq⟩

theorem exists_tmul_add_mul_isIntB : ∀ (L : Type) [Field L] [NumberField L] (κ : Type) (ℓ : Module.Basis κ ℚ L)
    (v : HeightOneSpectrum ℤ) (x : v.adicCompletion ℚ ⊗[ℚ] L) (D : ℤ), D ≠ 0 →
    ∃ (y : L) (ρ : v.adicCompletion ℚ ⊗[ℚ] L), IsIntB v ℓ ρ ∧
      x = (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] y + (D : v.adicCompletion ℚ ⊗[ℚ] L) * ρ := by
  intro L _ _ κ ℓ v x D hD
  haveI : Fintype κ := FiniteDimensional.fintypeBasisIndex ℓ
  have hD' : (D : v.adicCompletion ℚ) ≠ 0 := by
    rw [← map_intCast (algebraMap ℚ (v.adicCompletion ℚ)) D]
    exact (map_ne_zero _).2 (Int.cast_ne_zero.2 hD)
  choose q hq using fun i =>
    exists_rat_sub_le v ((Algebra.TensorProduct.basis (v.adicCompletion ℚ) ℓ).repr x i) (D : v.adicCompletion ℚ) hD'
  refine ⟨∑ i, q i • ℓ i, ∑ i, (((Algebra.TensorProduct.basis (v.adicCompletion ℚ) ℓ).repr x i -
    algebraMap ℚ (v.adicCompletion ℚ) (q i)) / D) ⊗ₜ[ℚ] ℓ i, ?_, ?_⟩
  · intro k

    rw [map_sum, Finsupp.finsetSum_apply]
    simp only [repr_tmul_apply ℓ v, ℓ.repr_self, Finsupp.single_apply, apply_ite (algebraMap ℚ (v.adicCompletion ℚ)),
      map_one, map_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀]
    have h0 : (0 : WithZero (Multiplicative ℤ)) < Valued.v (D : v.adicCompletion ℚ) := by
      rw [zero_lt_iff]; exact (map_ne_zero _).2 hD'
    exact (div_le_one₀ h0).2 (hq k)
  · conv_lhs => rw [eq_sum_tmul ℓ v x]
    rw [TensorProduct.tmul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hcast : (D : v.adicCompletion ℚ ⊗[ℚ] L) = (D : v.adicCompletion ℚ) ⊗ₜ[ℚ] (1 : L) := by
      have h := map_intCast (Algebra.TensorProduct.includeLeft : v.adicCompletion ℚ →ₐ[ℚ] v.adicCompletion ℚ ⊗[ℚ] L) D
      rw [Algebra.TensorProduct.includeLeft_apply] at h
      exact h.symm
    rw [hcast, Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      ← TensorProduct.add_tmul, Algebra.smul_def, mul_one, mul_div_cancel₀ _ hD', add_sub_cancel]

end GlobalTheory.AdicSpan
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicTensorExistsRationalAddIntegralMulStatement

section

@[expose] public section

open Matrix NumberField IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.adicTensor_exists_rational_add_integral_mul : ∀ (L : Type) [Field L] [NumberField L] (κ : Type) (ℓ : Module.Basis κ ℚ L)
    (v : HeightOneSpectrum ℤ) (x : v.adicCompletion ℚ ⊗[ℚ] L) (D : ℤ), D ≠ 0 →
    ∃ (y : L) (ρ : v.adicCompletion ℚ ⊗[ℚ] L), IsIntB v ℓ ρ ∧
      x = (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] y + (D : v.adicCompletion ℚ ⊗[ℚ] L) * ρ := by
  first | (exact @GlobalTheory.AdicSpan.exists_tmul_add_mul_isIntB) | (exact GlobalTheory.AdicSpan.exists_tmul_add_mul_isIntB) | (intros; apply GlobalTheory.AdicSpan.exists_tmul_add_mul_isIntB  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorLocalizedIntegersIdealInField

section

@[expose] public section

open Matrix NumberField IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.LocIntPrincipal

variable (L : Type) [Field L] [NumberField L] (v : HeightOneSpectrum ℤ)

abbrev locS : Submonoid (𝓞 L) := Algebra.algebraMapSubmonoid (𝓞 L) v.asIdeal.primeCompl

theorem locS_le : locS L v ≤ nonZeroDivisors (𝓞 L) :=
  algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _ v.asIdeal.primeCompl_le_nonZeroDivisors

abbrev locR : Subalgebra (𝓞 L) L := Localization.subalgebra.ofField L (locS L v) (locS_le L v)

instance : IsDedekindDomain (locR L v) :=
  IsLocalization.isDedekindDomain (𝓞 L) (locS_le L v) _

instance : IsPrincipalIdealRing (locR L v) :=
  IsDedekindDomain.isPrincipalIdealRing_localization_over_prime (𝓞 L) v.asIdeal v.ne_bot

theorem intCast_ne_zero {s : ℤ} (hs : s ∉ v.asIdeal) : (s : L) ≠ 0 := by
  intro h
  apply hs
  rw [show s = 0 by exact_mod_cast h]
  exact zero_mem _

theorem mem_locR_iff (c : L) :
    c ∈ locR L v ↔ ∃ s : ℤ, s ∉ v.asIdeal ∧ IsIntegral ℤ ((s : L) * c) := by
  constructor
  · rintro ⟨a, _, ⟨t, ht, rfl⟩, rfl⟩
    refine ⟨t, ht, ?_⟩
    have h0 := intCast_ne_zero L v ht
    have e : algebraMap (𝓞 L) L (algebraMap ℤ (𝓞 L) t) = (t : L) := by simp
    rw [e, mul_comm, mul_assoc, inv_mul_cancel₀ h0, mul_one]
    exact RingOfIntegers.isIntegral_coe a
  · rintro ⟨s, hs, hi⟩
    have h0 := intCast_ne_zero L v hs
    refine ⟨⟨(s : L) * c, hi⟩, algebraMap ℤ (𝓞 L) s, ⟨s, hs, rfl⟩, ?_⟩
    have e : algebraMap (𝓞 L) L (algebraMap ℤ (𝓞 L) s) = (s : L) := by simp
    rw [e]
    change c = (s : L) * c * (s : L)⁻¹
    field_simp

end GlobalTheory.LocIntPrincipal


open GlobalTheory.LocIntPrincipal in
theorem GlobalTheory.LocIntPrincipal.exists_generator : ∀ (L : Type) [Field L] [NumberField L] (v : HeightOneSpectrum ℤ) (K : Set L), 0 ∈ K →
    (∀ a ∈ K, ∀ b ∈ K, a + b ∈ K) →
    (∀ c : L, (∃ s : ℤ, s ∉ v.asIdeal ∧ IsIntegral ℤ ((s : L) * c)) → ∀ a ∈ K, c * a ∈ K) →
    (∀ a ∈ K, ∃ s : ℤ, s ∉ v.asIdeal ∧ IsIntegral ℤ ((s : L) * a)) →
    ∃ g ∈ K, ∀ a ∈ K, ∃ c : L, (∃ s : ℤ, s ∉ v.asIdeal ∧ IsIntegral ℤ ((s : L) * c)) ∧ a = c * g := by
  intro L _ _ v K h0 hadd hmul hint
  let J : Ideal (locR L v) :=
    { carrier := {a | (a : L) ∈ K}
      zero_mem' := h0
      add_mem' := fun {a b} ha hb => hadd _ ha _ hb
      smul_mem' := fun c a ha => by
        change (c : L) * (a : L) ∈ K
        exact hmul _ ((mem_locR_iff L v c).1 c.2) _ ha }
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal J).principal
  have hgJ : g ∈ J := by rw [hg]; exact Submodule.mem_span_singleton_self g
  refine ⟨g, hgJ, fun a ha => ?_⟩
  have haR : a ∈ locR L v := (mem_locR_iff L v a).2 (hint a ha)
  have hJ : (⟨a, haR⟩ : locR L v) ∈ J := ha
  rw [hg, Submodule.mem_span_singleton] at hJ
  obtain ⟨c, hc⟩ := hJ
  refine ⟨c, (mem_locR_iff L v c).1 c.2, ?_⟩
  have := congrArg Subtype.val hc
  exact this.symm
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorLocalizedIntegersIdealInFieldStatement

section

@[expose] public section

open Matrix NumberField IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.exists_generator_localized_integers_ideal_in_field : ∀ (L : Type) [Field L] [NumberField L] (v : HeightOneSpectrum ℤ) (K : Set L), 0 ∈ K →
    (∀ a ∈ K, ∀ b ∈ K, a + b ∈ K) →
    (∀ c : L, (∃ s : ℤ, s ∉ v.asIdeal ∧ IsIntegral ℤ ((s : L) * c)) → ∀ a ∈ K, c * a ∈ K) →
    (∀ a ∈ K, ∃ s : ℤ, s ∉ v.asIdeal ∧ IsIntegral ℤ ((s : L) * a)) →
    ∃ g ∈ K, ∀ a ∈ K, ∃ c : L, (∃ s : ℤ, s ∉ v.asIdeal ∧ IsIntegral ℤ ((s : L) * c)) ∧ a = c * g := by
  first | (exact @GlobalTheory.LocIntPrincipal.exists_generator) | (exact GlobalTheory.LocIntPrincipal.exists_generator) | (intros; apply GlobalTheory.LocIntPrincipal.exists_generator <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCardQuotientBound

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.AdicSpan

theorem isIntB_lattice_principal_eventually : ∀ (L : Type) [Field L] [NumberField L] (κ : Type) (ℓ : Module.Basis κ ℚ L),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ I : Set (v.adicCompletion ℚ ⊗[ℚ] L), 0 ∈ I →
      (∀ x ∈ I, ∀ y ∈ I, x + y ∈ I) → (∀ ρ, IsIntB v ℓ ρ → ∀ x ∈ I, ρ * x ∈ I) →
      (∃ D : ℤ, D ≠ 0 ∧ (∀ x, IsIntB v ℓ x → (D : v.adicCompletion ℚ ⊗[ℚ] L) * x ∈ I) ∧
        ∀ x ∈ I, IsIntB v ℓ ((D : v.adicCompletion ℚ ⊗[ℚ] L) * x)) →
      ∃ m : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ, ∀ x, x ∈ I ↔ ∃ ρ, IsIntB v ℓ ρ ∧ x = ↑m * ρ := by
  intro L _ _ κ ℓ
  obtain ⟨S₁, hS₁⟩ := isIntB_mul_star_eventually L
    (RingHom.toOpposite (RingHom.id L) fun x y => mul_comm x y) κ ℓ
  obtain ⟨S₂, hS₂⟩ := GlobalTheory.T.adicIntegralTensorBasis_iff_exists_integral_multiple L κ ℓ
  refine ⟨S₁ ∪ S₂, fun v hv I h0 hadd hmul ⟨D, hD0, hDI, hIO⟩ => ?_⟩
  have hv₁ : v ∉ S₁ := fun h => hv (Finset.mem_union_left _ h)
  have hv₂ : v ∉ S₂ := fun h => hv (Finset.mem_union_right _ h)
  have hOmul := (hS₁ v hv₁).1
  have hloc := hS₂ v hv₂
  have hOadd : ∀ y z, IsIntB v ℓ y → IsIntB v ℓ z → IsIntB v ℓ (y + z) := fun y z hy hz i => by
    rw [map_add (f := _), Finsupp.add_apply]; exact add_mem (hy i) (hz i)
  have hone : (1 : ℤ) ∉ v.asIdeal := fun h => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have hloc1 : ∀ c : ℤ, ∃ s : ℤ, s ∉ v.asIdeal ∧ IsIntegral ℤ ((s : L) * (c : L)) := fun c =>
    ⟨1, hone, by rw [Int.cast_one, one_mul, ← eq_intCast (algebraMap ℤ L)]; exact isIntegral_algebraMap⟩
  have hcast : ∀ c : ℤ, ((c : v.adicCompletion ℚ ⊗[ℚ] L)) = (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (c : L) :=
    fun c => by rw [← Algebra.TensorProduct.includeRight_apply, map_intCast]
  have hO : ∀ c : L, (∃ s : ℤ, s ∉ v.asIdeal ∧ IsIntegral ℤ ((s : L) * c)) →
      IsIntB v ℓ ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] c) := fun c hc => (hloc c).2 hc
  have htm : ∀ a b : L, ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] a) * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] b) =
      (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (a * b) := fun a b => by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have hDL : (D : L) ≠ 0 := Int.cast_ne_zero.2 hD0
  let K : Set L := {a | (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (a / D) ∈ I}
  have hK0 : (0 : L) ∈ K := by
    show _ ∈ I; rw [zero_div, TensorProduct.tmul_zero]; exact h0
  have hKadd : ∀ a ∈ K, ∀ b ∈ K, a + b ∈ K := fun a ha b hb => by
    show _ ∈ I; rw [add_div, TensorProduct.tmul_add]; exact hadd _ ha _ hb
  have hKmul : ∀ c : L, (∃ s : ℤ, s ∉ v.asIdeal ∧ IsIntegral ℤ ((s : L) * c)) → ∀ a ∈ K, c * a ∈ K :=
    fun c hc a ha => by
      show _ ∈ I; rw [mul_div_assoc, ← htm]; exact hmul _ (hO c hc) _ ha
  have hKloc : ∀ a ∈ K, ∃ s : ℤ, s ∉ v.asIdeal ∧ IsIntegral ℤ ((s : L) * a) := fun a ha => by
    apply (hloc a).1
    have := hIO _ ha
    rwa [hcast, htm, mul_div_cancel₀ _ hDL] at this
  obtain ⟨g, hgK, hg⟩ := GlobalTheory.T.exists_generator_localized_integers_ideal_in_field L v K hK0 hKadd hKmul hKloc
  have hDK : (D : L) * D ∈ K := by
    show _ ∈ I
    have h1 := hDI _ (hO _ (hloc1 1))
    rwa [Int.cast_one, ← Algebra.TensorProduct.one_def, mul_one, hcast,
      ← mul_div_cancel_right₀ (D : L) hDL] at h1
  obtain ⟨c₀, hc₀, hc₀g⟩ := hg _ hDK
  have hg0 : g ≠ 0 := by
    rintro rfl; rw [mul_zero] at hc₀g; exact hDL (mul_self_eq_zero.1 hc₀g)
  have e1 : g / D * (D / g) = 1 := by field_simp
  have e1' : D / g * (g / D) = 1 := by field_simp
  let m : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ :=
    { val := (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (g / D), inv := (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (D / g),
      val_inv := by rw [htm, e1]; rfl
      inv_val := by rw [htm, e1']; rfl }
  refine ⟨m, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · obtain ⟨y, ρ₁, hρ₁, rfl⟩ := GlobalTheory.T.adicTensor_exists_rational_add_integral_mul L κ ℓ v x D hD0
    have hy : (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] y ∈ I := by
      have h2 : (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] ((-1 : ℤ) : L) * ((D : v.adicCompletion ℚ ⊗[ℚ] L) * ρ₁) ∈ I :=
        hmul _ (hO _ (hloc1 _)) _ (hDI _ hρ₁)
      have := hadd _ hx _ h2
      convert this using 1
      rw [← hcast]; push_cast; ring
    have hyK : (D : L) * y ∈ K := by
      show _ ∈ I; rwa [mul_div_cancel_left₀ _ hDL]
    obtain ⟨c, hc, hcg⟩ := hg _ hyK
    have e2 : g / D * c = y := by
      rw [div_mul_eq_mul_div, mul_comm g c, ← hcg, mul_div_cancel_left₀ _ hDL]
    have e3 : g / D * c₀ = D := by
      rw [div_mul_eq_mul_div, mul_comm g c₀, ← hc₀g, mul_div_cancel_left₀ _ hDL]
    refine ⟨(1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] c + (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] c₀ * ρ₁,
      hOadd _ _ (hO c hc) (hOmul _ _ (hO c₀ hc₀) hρ₁), ?_⟩
    show _ = (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (g / D) * _
    rw [mul_add, htm, ← mul_assoc, htm, e2, e3, hcast]
  · rintro ⟨ρ, hρ, rfl⟩
    rw [mul_comm]
    exact hmul ρ hρ _ hgK

end GlobalTheory.AdicSpan
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionalIdealIntegralLattice

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.fractional_ideal_integral_lattice : ∀ (L : Type) [Field L] [NumberField L] (κ : Type) (ℓ : Module.Basis κ ℚ L),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ I : Set (v.adicCompletion ℚ ⊗[ℚ] L), 0 ∈ I →
      (∀ x ∈ I, ∀ y ∈ I, x + y ∈ I) → (∀ ρ, IsIntB v ℓ ρ → ∀ x ∈ I, ρ * x ∈ I) →
      (∃ D : ℤ, D ≠ 0 ∧ (∀ x, IsIntB v ℓ x → (D : v.adicCompletion ℚ ⊗[ℚ] L) * x ∈ I) ∧
        ∀ x ∈ I, IsIntB v ℓ ((D : v.adicCompletion ℚ ⊗[ℚ] L) * x)) →
      ∃ m : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ, ∀ x, x ∈ I ↔ ∃ ρ, IsIntB v ℓ ρ ∧ x = ↑m * ρ := by
  first | (exact @GlobalTheory.AdicSpan.isIntB_lattice_principal_eventually) | (exact GlobalTheory.AdicSpan.isIntB_lattice_principal_eventually) | (intros; apply GlobalTheory.AdicSpan.isIntB_lattice_principal_eventually  <;> assumption)
end
end
