module

public import Formalism.ConjugateSelfDual.Statement
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.GaloisValuations.GlobalB
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNotMemMulValuationLeOneOfNe

section

@[expose] public section

open IsDedekindDomain NumberField

namespace GlobalTheory

theorem exists_notMem_mul_valuation_le_one_of_ne : ∀ {F : Type} [Field F] [NumberField F]
    (p : HeightOneSpectrum (𝓞 F)) {ι : Type} [Finite ι] (x : ι → F), ∃ s : 𝓞 F, s ∉ p.asIdeal ∧
      ∀ q : HeightOneSpectrum (𝓞 F), q ≠ p → ∀ i, q.valuation F ((s : F) * x i) ≤ 1 := by
  intro F _ _ p ι _ x
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 F)) x
  have hc : (b : 𝓞 F) ≠ 0 := nonZeroDivisors.ne_zero b.2
  have hfin : FiniteMultiplicity p.asIdeal (Ideal.span {(b : 𝓞 F)}) :=
    FiniteMultiplicity.of_not_isUnit (by rw [Ideal.isUnit_iff]; exact p.isPrime.ne_top)
      (by simpa using hc)
  obtain ⟨J, hJ, hnd⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  have hJp : ¬ J ≤ p.asIdeal := fun h => hnd (Ideal.dvd_iff_le.mpr h)
  obtain ⟨s, hsJ, hsp⟩ := SetLike.not_le_iff_exists.mp hJp
  refine ⟨s, hsp, fun q hq i => ?_⟩
  have hpow : ¬ p.asIdeal ^ multiplicity p.asIdeal (Ideal.span {(b : 𝓞 F)}) ≤ q.asIdeal := by
    intro h
    have h1 : p.asIdeal ≤ q.asIdeal := q.isPrime.le_of_pow_le h
    exact hq (HeightOneSpectrum.ext (p.isMaximal.eq_of_le q.isPrime.ne_top h1).symm)
  obtain ⟨t, ht, htq⟩ := SetLike.not_le_iff_exists.mp hpow
  have hts : t * s ∈ Ideal.span {(b : 𝓞 F)} := by
    rw [hJ]; exact Ideal.mul_mem_mul ht hsJ
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton.mp hts
  obtain ⟨a, ha⟩ := hb i
  replace ha : algebraMap (𝓞 F) F a = algebraMap (𝓞 F) F (b : 𝓞 F) * x i := by
    rw [ha]; exact Algebra.smul_def _ _
  have key : algebraMap (𝓞 F) F t * ((s : F) * x i) = algebraMap (𝓞 F) F (u * a) := by
    rw [map_mul, ha, RingOfIntegers.coe_eq_algebraMap, ← mul_assoc, ← map_mul, hu, map_mul]
    ring
  have h1 : q.valuation F (algebraMap (𝓞 F) F t) = 1 :=
    (q.valuation_eq_one_iff_notMem (K := F) (r := t)).2 htq
  have h2 : q.valuation F (algebraMap (𝓞 F) F (u * a)) ≤ 1 := q.valuation_le_one (K := F) _
  rw [← key, map_mul, h1, one_mul] at h2
  exact h2

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DenseNumberFieldOfContinuousCompletionEquiv

section

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory

open IsDedekindDomain.HeightOneSpectrum

theorem valuationSubring_le_one_of_ringOfIntegers {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω']
    [Algebra E' Ω'] (A' : ValuationSubring Ω') (m : 𝓞 E') :
    A'.valuation (algebraMap E' Ω' (m : E')) ≤ 1 :=
  (A'.valuation_le_one_iff _).2
    (mem_of_isIntegral_int A' (map_isIntegral_int (algebraMap E' Ω') (RingOfIntegers.isIntegral_coe m)))

theorem valuationSubring_lt_one_of_placeOver {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω']
    [Algebra E' Ω'] (A' : ValuationSubring Ω') (w' : HeightOneSpectrum (𝓞 E')) (hP : IsPlaceOver A' w')
    (t : E') (ht : w'.valuation E' t < 1) : A'.valuation (algebraMap E' Ω' t) < 1 := by
  obtain ⟨s, hs, hq⟩ := GlobalTheory.exists_notMem_mul_valuation_le_one_of_ne w' (fun _ : Unit => t)
  have hsle : w'.valuation E' (s : E') ≤ 1 := by
    rw [RingOfIntegers.coe_eq_algebraMap]; exact w'.valuation_le_one (K := E') s
  have hw : w'.valuation E' ((s : E') * t) < 1 := by
    rw [map_mul]
    calc w'.valuation E' (s : E') * w'.valuation E' t ≤ 1 * w'.valuation E' t := by gcongr
      _ < 1 := by rwa [one_mul]
  have hall : ∀ q : HeightOneSpectrum (𝓞 E'), q.valuation E' ((s : E') * t) ≤ 1 := by
    intro q
    by_cases hq' : q = w'
    · subst hq'; exact hw.le
    · exact hq q hq' ()
  obtain ⟨m, hm⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one E' _ hall
  have hmw : m ∈ w'.asIdeal := by
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E')]
    show w'.valuation E' (algebraMap (𝓞 E') E' m) < 1
    rw [hm]; exact hw
  have h1 := (hP m).2 hmw
  have h2 : A'.valuation (algebraMap E' Ω' (s : E')) = 1 :=
    le_antisymm (valuationSubring_le_one_of_ringOfIntegers A' s) (not_lt.1 (fun h => hs ((hP s).1 h)))
  have hm' : ((m : 𝓞 E') : E') = (s : E') * t := by rw [← hm]
  rw [hm', map_mul, map_mul, h2, one_mul] at h1
  exact h1

theorem exists_int_valuationSubring_le {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω']
    [Algebra E' Ω'] [Algebra.IsAlgebraic E' Ω'] (A' : ValuationSubring Ω') {δ : Ω'} (hδ : δ ≠ 0) :
    ∃ n : ℤ, n ≠ 0 ∧ A'.valuation (algebraMap E' Ω' (n : E')) ≤ A'.valuation δ := by
  haveI : Algebra.IsAlgebraic ℤ E' :=
    ⟨fun x => (IsFractionRing.isAlgebraic_iff ℤ ℚ E').mpr (Algebra.IsAlgebraic.isAlgebraic x)⟩
  haveI : Algebra.IsAlgebraic ℤ Ω' := Algebra.IsAlgebraic.trans ℤ E' Ω'
  obtain ⟨n, hn, hint⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) δ⁻¹).exists_integral_multiple
  refine ⟨n, hn, ?_⟩
  have hle := (A'.valuation_le_one_iff _).2 (mem_of_isIntegral_int A' hint)
  rw [zsmul_eq_mul, map_mul, map_inv₀] at hle
  have hd : A'.valuation δ ≠ 0 := by simpa using hδ
  rw [map_intCast]
  calc A'.valuation (n : Ω') = A'.valuation (n : Ω') * (A'.valuation δ)⁻¹ * A'.valuation δ := by
        rw [mul_assoc, inv_mul_cancel₀ hd, mul_one]
    _ ≤ 1 * A'.valuation δ := by gcongr
    _ = A'.valuation δ := one_mul _

end GlobalTheory

namespace GlobalTheory

theorem approx_of_completion_equiv : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [Algebra.IsAlgebraic E' Ω'] (A' : ValuationSubring Ω') (w' : HeightOneSpectrum (𝓞 E')), IsPlaceOver A' w' → ∀ (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), Continuous i → (∀ x, i (algebraMap E _ x) = algebraMap E' _ (j x)) → ∀ (y : E') (δ : Ω'), δ ≠ 0 → ∃ x : E, A'.valuation (algebraMap E' Ω' y - algebraMap E' Ω' (j x)) < A'.valuation δ := by
  intro E _ _ w E' Ω' _ _ _ _ _ A' w' hP j i hi hij y δ hδ
  obtain ⟨n, hn, hnδ⟩ := exists_int_valuationSubring_le (E' := E') A' hδ
  set c : E' := (n : E') with hcdef
  have hc : c ≠ 0 := Int.cast_ne_zero.mpr hn
  let U : Set (w'.adicCompletion E') :=
    {z | Valued.v ((z - algebraMap E' _ y) * (algebraMap E' (w'.adicCompletion E') c)⁻¹) < 1}
  have hU : IsOpen U := by
    have h := (Valued.isOpen_ball (w'.adicCompletion E') 1).preimage
      ((continuous_sub_right (algebraMap E' (w'.adicCompletion E') y)).mul
        (continuous_const (y := (algebraMap E' (w'.adicCompletion E') c)⁻¹)))
    convert h using 2 with z
    simp [U, Valuation.restrict_lt_iff_lt_embedding]
  have hdense : DenseRange (i ∘ algebraMap E (w.adicCompletion E)) :=
    i.surjective.denseRange.comp (HeightOneSpectrum.denseRange_algebraMap E w) hi
  obtain ⟨x, hx⟩ := hdense.exists_mem_open hU ⟨algebraMap E' _ y, by simp [U]⟩
  refine ⟨x, ?_⟩
  have hx' : w'.valuation E' ((j x - y) * c⁻¹) < 1 := by
    have e : (i (algebraMap E _ x) - algebraMap E' (w'.adicCompletion E') y) *
        (algebraMap E' (w'.adicCompletion E') c)⁻¹ = algebraMap E' (w'.adicCompletion E') ((j x - y) * c⁻¹) := by
      rw [hij, map_mul, map_sub, map_inv₀]
    have hx2 : (i ∘ algebraMap E (w.adicCompletion E)) x ∈ U := hx
    simp only [Function.comp, U, Set.mem_ofPred_eq] at hx2
    rw [e] at hx2
    have hv : Valued.v (algebraMap E' (w'.adicCompletion E') ((j x - y) * c⁻¹)) = w'.valuation E' ((j x - y) * c⁻¹) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w' _
    rw [hv] at hx2
    exact hx2
  have ht := valuationSubring_lt_one_of_placeOver A' w' hP _ hx'
  have e2 : algebraMap E' Ω' y - algebraMap E' Ω' (j x) = -(algebraMap E' Ω' ((j x - y) * c⁻¹) * algebraMap E' Ω' c) := by
    rw [← map_mul, ← map_sub, ← map_neg]; congr 1; field_simp; ring
  have hcpos : 0 < A'.valuation (algebraMap E' Ω' c) := by
    rw [zero_lt_iff]; simpa using hc
  rw [e2, Valuation.map_neg, map_mul]
  calc _ < A'.valuation (algebraMap E' Ω' c) := mul_lt_of_lt_one_left hcpos ht
    _ ≤ A'.valuation δ := hnδ

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DenseNumberFieldOfContinuousCompletionEquivStatement

section

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.dense_numberField_of_continuous_completion_equiv : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [Algebra.IsAlgebraic E' Ω'] (A' : ValuationSubring Ω') (w' : HeightOneSpectrum (𝓞 E')), IsPlaceOver A' w' → ∀ (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), Continuous i → (∀ x, i (algebraMap E _ x) = algebraMap E' _ (j x)) → ∀ (y : E') (δ : Ω'), δ ≠ 0 → ∃ x : E, A'.valuation (algebraMap E' Ω' y - algebraMap E' Ω' (j x)) < A'.valuation δ := by
  first | exact @GlobalTheory.approx_of_completion_equiv | exact GlobalTheory.approx_of_completion_equiv | (intros; apply GlobalTheory.approx_of_completion_equiv <;> assumption)
end
end
