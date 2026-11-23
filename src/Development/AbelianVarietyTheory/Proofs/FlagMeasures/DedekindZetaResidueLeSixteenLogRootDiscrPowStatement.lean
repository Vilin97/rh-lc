module

public import Formalism.HermitianLattices.StatementMass
public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Units.Regulator
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.ClassGroup.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RegulatorLeSumSmallIdealsInClass
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
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.NumberTheory.ArithmeticFunction.Zeta
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIdealInClassOfNormLeSqrtDiscr
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RootDiscrGeThreeHalvesOfIsTotallyComplexStatement
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.RegulatorLeSumSmallIdealsInClassStatement

section

@[expose] public section

open MeasureTheory NumberField Finset

theorem _root_.GlobalTheory.T.regulator_le_sum_small_ideals_in_class : ∀ (K : Type) [Field K] [NumberField K], IsTotallyComplex K → ∀ (C : ClassGroup (𝓞 K)) (S : Finset (Ideal (𝓞 K))), (∀ I, I ∈ S ↔ ∃ hI : I ∈ nonZeroDivisors (Ideal (𝓞 K)), ClassGroup.mk0 ⟨I, hI⟩ = C ∧ (Ideal.absNorm I : ℝ) ≤ Real.sqrt |(discr K : ℝ)|) → Units.regulator K ≤ ∑ I ∈ S, Real.log (Real.sqrt |(discr K : ℝ)| / Ideal.absNorm I) ^ Units.rank K / ((Units.rank K).factorial : ℝ) := by
  first | exact @GlobalTheory.RegulatorClassBound.regulator_le_sum_class | exact GlobalTheory.RegulatorClassBound.regulator_le_sum_class | (intros; apply GlobalTheory.RegulatorClassBound.regulator_le_sum_class <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumAbsNormRpowNegLeDedekindZetaBound

section

@[expose] public section

open MeasureTheory NumberField Finset
open scoped ArithmeticFunction.zeta

namespace GlobalTheory.IdealZetaSum

theorem sum_Ioc_rpow_neg_le {s : ℝ} (hs : 1 < s) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, (n : ℝ) ^ (-s) ≤ s / (s - 1) := by
  have hs1 : 0 < s - 1 := by linarith
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [Ioc_self, sum_empty]; positivity
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-s)) (Set.Icc ((1 : ℕ) : ℝ) (N : ℝ)) := by
    intro x hx y _ hxy
    have : (1 : ℝ) ≤ x := by simpa using hx.1
    exact Real.rpow_le_rpow_of_nonpos (by linarith) hxy (by linarith)
  have h := AntitoneOn.sum_le_integral_Ico hN hanti
  rw [integral_rpow (Or.inr ⟨by linarith, by
    rw [Set.uIcc_of_le (by simpa using hN1)]; simp⟩)] at h
  have e : ∑ n ∈ Ioc 0 N, (n : ℝ) ^ (-s)
      = 1 + ∑ i ∈ Ico 1 N, (((i + 1 : ℕ) : ℝ)) ^ (-s) := by
    rw [sum_Ico_add' (fun n : ℕ => (n : ℝ) ^ (-s)) 1 N 1]
    have : Ioc 0 N = insert 1 (Ico (1 + 1) (N + 1)) := by
      ext n; simp only [mem_Ioc, mem_insert, mem_Ico]; omega
    rw [this, sum_insert (by simp)]
    simp
  rw [e]
  have hpos : 0 ≤ (N : ℝ) ^ (-s + 1) := by positivity
  have h2 : ((N : ℝ) ^ (-s + 1) - ((1 : ℕ) : ℝ) ^ (-s + 1)) / (-s + 1) ≤ 1 / (s - 1) := by
    rw [Nat.cast_one, Real.one_rpow, show -s + 1 = -(s - 1) by ring, div_neg, ← neg_div]
    rw [show -s + 1 = -(s - 1) by ring] at hpos
    exact div_le_div_of_nonneg_right (by linarith) hs1.le
  have h3 : s / (s - 1) = 1 + 1 / (s - 1) := by field_simp; ring
  linarith

theorem sum_zeta_pow_mul_rpow_le (s : ℝ) (N k : ℕ) :
    ∑ n ∈ Ioc 0 N, (((ζ ^ k : ArithmeticFunction ℕ) n : ℕ) : ℝ) * (n : ℝ) ^ (-s)
      ≤ (∑ n ∈ Ioc 0 N, (n : ℝ) ^ (-s)) ^ k := by
  induction k with
  | zero =>
    simp only [pow_zero, ArithmeticFunction.one_apply, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
      ite_mul, one_mul, zero_mul, sum_ite_eq']
    split_ifs <;> simp
  | succ k ih =>
    rw [pow_succ (∑ n ∈ Ioc 0 N, (n : ℝ) ^ (-s))]
    refine le_trans ?_ (mul_le_mul_of_nonneg_right ih (sum_nonneg fun n _ => by positivity))
    rw [sum_mul_sum, ← sum_product', pow_succ]
    have e : ∀ n ∈ Ioc 0 N, (((ζ ^ k * ζ : ArithmeticFunction ℕ) n : ℕ) : ℝ) * (n : ℝ) ^ (-s)
        = ∑ x ∈ (Ioc 0 N ×ˢ Ioc 0 N).filter (fun x => x.1 * x.2 = n),
          (((ζ ^ k : ArithmeticFunction ℕ) x.1 : ℕ) : ℝ) * (x.1 : ℝ) ^ (-s) * (x.2 : ℝ) ^ (-s) := by
      intro n hn
      rw [mem_Ioc] at hn
      rw [ArithmeticFunction.mul_apply, Nat.cast_sum, sum_mul]
      refine sum_congr ?_ ?_
      · ext x
        simp only [Nat.mem_divisorsAntidiagonal, mem_filter, mem_product, mem_Ioc]
        constructor
        · rintro ⟨h, h0⟩
          have h1 : 0 < x.1 := Nat.pos_of_ne_zero (by rintro h1; rw [h1] at h; omega)
          have h2 : 0 < x.2 := Nat.pos_of_ne_zero (by rintro h1; rw [h1] at h; omega)
          refine ⟨⟨⟨h1, ?_⟩, h2, ?_⟩, h⟩ <;> nlinarith
        · rintro ⟨_, h⟩
          exact ⟨h, by omega⟩
      · intro x hx
        simp only [mem_filter, mem_product, mem_Ioc] at hx
        rw [← hx.2, Nat.cast_mul, Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity),
          ArithmeticFunction.zeta_apply_ne hx.1.2.1.ne']
        simp [mul_assoc]
    rw [sum_congr rfl e, sum_fiberwise_eq_sum_filter]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun x _ _ => by positivity

theorem sum_absNorm_rpow_neg_le : ∀ (K : Type) [Field K] [NumberField K] (s : ℝ), 1 < s →
    ∀ (S : Finset (Ideal (𝓞 K))), (∀ I ∈ S, I ≠ ⊥) →
      ∑ I ∈ S, (Ideal.absNorm I : ℝ) ^ (-s) ≤ (s / (s - 1)) ^ Module.finrank ℚ K := by
  intro K _ _ s hs S hS
  classical
  set N := S.sup (fun I => Ideal.absNorm I) with hN
  refine le_trans ?_ (pow_le_pow_left₀ (sum_nonneg fun n _ => by positivity)
    (sum_Ioc_rpow_neg_le hs N) _)
  refine le_trans ?_ (sum_zeta_pow_mul_rpow_le s N _)
  rw [← sum_fiberwise_of_maps_to (s := S) (t := Ioc 0 N) (g := fun I => Ideal.absNorm I)]
  · refine sum_le_sum fun n hn => ?_
    rw [sum_congr rfl (g := fun _ => (n : ℝ) ^ (-s))
      (fun I hI => by rw [(mem_filter.mp hI).2]), sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [Nat.cast_le]
    refine le_trans ?_ (ncard_ideal_absNorm_eq_le K (mem_Ioc.mp hn).1.ne')
    rw [← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard (fun I hI => (mem_filter.mp (mem_coe.mp hI)).2)
      (Ideal.finite_setOfPred_absNorm_eq n)
  · intro I hI
    rw [mem_Ioc]
    exact ⟨Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hS I hI),
      le_sup (f := fun I => Ideal.absNorm I) hI⟩

end GlobalTheory.IdealZetaSum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumAbsNormRpowNegLeDedekindZetaBoundStatement

section

@[expose] public section

open MeasureTheory NumberField Finset

theorem _root_.GlobalTheory.T.sum_absNorm_rpow_neg_le_dedekindZeta_bound : ∀ (K : Type) [Field K] [NumberField K] (s : ℝ), 1 < s → ∀ (S : Finset (Ideal (𝓞 K))), (∀ I ∈ S, I ≠ ⊥) → ∑ I ∈ S, (Ideal.absNorm I : ℝ) ^ (-s) ≤ (s / (s - 1)) ^ Module.finrank ℚ K := by
  first | exact @GlobalTheory.IdealZetaSum.sum_absNorm_rpow_neg_le | exact GlobalTheory.IdealZetaSum.sum_absNorm_rpow_neg_le | (intros; apply GlobalTheory.IdealZetaSum.sum_absNorm_rpow_neg_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClassNumberMulRegulatorLeSqrtDiscrRpow

section

@[expose] public section

open MeasureTheory NumberField Finset

namespace GlobalTheory

theorem log_pow_div_factorial_le_rpow_of_one_le {u s : ℝ} (hu : 1 ≤ u) (hs : 1 ≤ s) (r : ℕ) :
    Real.log u ^ r / (r.factorial : ℝ) ≤ u ^ s := by
  have h := Real.pow_div_factorial_le_exp (Real.log u) (Real.log_nonneg hu) r
  rw [Real.exp_log (by linarith)] at h
  refine h.trans ?_
  calc u = u ^ (1 : ℝ) := (Real.rpow_one u).symm
    _ ≤ u ^ s := Real.rpow_le_rpow_of_exponent_le hu hs

theorem classNumber_mul_regulator_le_sqrt_discr_rpow :
    ∀ (K : Type) [Field K] [NumberField K], IsTotallyComplex K → ∀ s : ℝ, 1 < s →
      (classNumber K : ℝ) * Units.regulator K ≤
        Real.sqrt |(discr K : ℝ)| ^ s * (s / (s - 1)) ^ Module.finrank ℚ K := by
  intro K _ _ hK s hs
  classical
  set Y : ℝ := Real.sqrt |(discr K : ℝ)| with hY
  have hY0 : 0 ≤ Y := Real.sqrt_nonneg _
  have hfin : {I : Ideal (𝓞 K) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ Y}.Finite := by
    refine (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊Y⌋₊).subset fun I hI => ?_
    exact Nat.le_floor hI.2
  set T := hfin.toFinset with hT
  have hmem : ∀ I, I ∈ T ↔ I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ Y := fun I => by
    rw [hT, Set.Finite.mem_toFinset]; rfl
  let cls : Ideal (𝓞 K) → ClassGroup (𝓞 K) := fun I =>
    if h : I ∈ nonZeroDivisors (Ideal (𝓞 K)) then ClassGroup.mk0 ⟨I, h⟩ else 1
  let g : Ideal (𝓞 K) → ℝ := fun I =>
    Real.log (Y / Ideal.absNorm I) ^ Units.rank K / ((Units.rank K).factorial : ℝ)
  have h1 : ∀ C : ClassGroup (𝓞 K),
      Units.regulator K ≤ ∑ I ∈ T.filter (fun I => cls I = C), g I := by
    intro C
    refine GlobalTheory.T.regulator_le_sum_small_ideals_in_class K hK C _ fun I => ?_
    rw [Finset.mem_filter, hmem]
    constructor
    · rintro ⟨⟨h0, hle⟩, hc⟩
      have hI : I ∈ nonZeroDivisors (Ideal (𝓞 K)) := mem_nonZeroDivisors_of_ne_zero h0
      refine ⟨hI, ?_, hle⟩
      simpa only [cls, dif_pos hI] using hc
    · rintro ⟨hI, hc, hle⟩
      refine ⟨⟨nonZeroDivisors.ne_zero hI, hle⟩, ?_⟩
      simpa only [cls, dif_pos hI] using hc
  have h2 : ∀ I ∈ T, g I ≤ Y ^ s * (Ideal.absNorm I : ℝ) ^ (-s) := by
    intro I hI
    obtain ⟨h0, hle⟩ := (hmem I).1 hI
    have hN : (0 : ℝ) < Ideal.absNorm I := by
      have : Ideal.absNorm I ≠ 0 := fun h => h0 (Ideal.absNorm_eq_zero_iff.1 h)
      exact_mod_cast Nat.pos_of_ne_zero this
    have hu : 1 ≤ Y / Ideal.absNorm I := (one_le_div hN).2 hle
    refine (log_pow_div_factorial_le_rpow_of_one_le hu hs.le _).trans (le_of_eq ?_)
    rw [Real.div_rpow hY0 hN.le, Real.rpow_neg hN.le, div_eq_mul_inv]
  calc (classNumber K : ℝ) * Units.regulator K
      = ∑ _C : ClassGroup (𝓞 K), Units.regulator K := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, classNumber]
    _ ≤ ∑ C : ClassGroup (𝓞 K), ∑ I ∈ T.filter (fun I => cls I = C), g I :=
        Finset.sum_le_sum fun C _ => h1 C
    _ = ∑ I ∈ T, g I := Finset.sum_fiberwise T cls g
    _ ≤ ∑ I ∈ T, Y ^ s * (Ideal.absNorm I : ℝ) ^ (-s) := Finset.sum_le_sum h2
    _ = Y ^ s * ∑ I ∈ T, (Ideal.absNorm I : ℝ) ^ (-s) := (Finset.mul_sum _ _ _).symm
    _ ≤ Y ^ s * (s / (s - 1)) ^ Module.finrank ℚ K :=
        mul_le_mul_of_nonneg_left
          (GlobalTheory.T.sum_absNorm_rpow_neg_le_dedekindZeta_bound K s hs T fun I hI => ((hmem I).1 hI).1) (Real.rpow_nonneg hY0 s)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClassNumberMulRegulatorLeSqrtDiscrRpowStatement

section

@[expose] public section

open MeasureTheory NumberField Finset

theorem _root_.GlobalTheory.T.classNumber_mul_regulator_le_sqrt_discr_rpow' : ∀ (K : Type) [Field K] [NumberField K], IsTotallyComplex K → ∀ s : ℝ, 1 < s → (classNumber K : ℝ) * Units.regulator K ≤ Real.sqrt |(discr K : ℝ)| ^ s * (s / (s - 1)) ^ Module.finrank ℚ K := by
  first | exact @GlobalTheory.classNumber_mul_regulator_le_sqrt_discr_rpow | exact GlobalTheory.classNumber_mul_regulator_le_sqrt_discr_rpow | (intros; apply GlobalTheory.classNumber_mul_regulator_le_sqrt_discr_rpow <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.DedekindZetaResidueLeSixteenLogRootDiscrPow

section

@[expose] public section

open MeasureTheory NumberField Finset

namespace GlobalTheory

theorem residue_rankin_numeric (x : ℝ) (hx : (3 / 2 : ℝ) ≤ x) (f : ℕ) :
    0 < Real.log x ∧
    (2 * Real.pi) ^ f * ((x ^ f) ^ (1 + 1 / Real.log x) *
      ((1 + 1 / Real.log x) / ((1 + 1 / Real.log x) - 1)) ^ (2 * f))
      ≤ (16 * Real.log x) ^ (2 * f) * x ^ f := by
  have hx0 : 0 < x := by linarith
  have hL : (2 / 5 : ℝ) ≤ Real.log x := by
    have h1 := Real.le_log_one_add_of_nonneg (x := (1 / 2 : ℝ)) (by norm_num)
    have h2 : Real.log (1 + 1 / 2) ≤ Real.log x := Real.log_le_log (by norm_num) (by linarith)
    norm_num at h1 h2 ⊢
    linarith
  set L := Real.log x with hLdef
  have hL0 : 0 < L := by linarith
  refine ⟨hL0, ?_⟩
  have e1 : (1 + 1 / L) / ((1 + 1 / L) - 1) = 1 + L := by
    rw [add_sub_cancel_left]; field_simp; ring
  have e2 : (x ^ f) ^ (1 + 1 / L) = x ^ f * Real.exp 1 ^ f := by
    rw [Real.rpow_add (pow_pos hx0 f), Real.rpow_one, Real.rpow_def_of_pos (pow_pos hx0 f),
      Real.log_pow, ← hLdef, ← Real.exp_nat_mul]
    congr 2
    field_simp
  rw [e1, e2, pow_mul, pow_mul]
  have hb : 2 * Real.pi * Real.exp 1 * (1 + L) ^ 2 ≤ (16 * L) ^ 2 := by
    have hpi := Real.pi_lt_d2
    have he := Real.exp_one_lt_d9
    have hp0 := Real.pi_pos
    have he0 := Real.exp_pos 1
    have h3 : 2 * Real.pi * Real.exp 1 ≤ 18 := by nlinarith
    have h4 : (1 + L) ^ 2 ≤ (7 / 2 * L) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    calc 2 * Real.pi * Real.exp 1 * (1 + L) ^ 2 ≤ 18 * (7 / 2 * L) ^ 2 :=
          mul_le_mul h3 h4 (by positivity) (by norm_num)
      _ ≤ (16 * L) ^ 2 := by nlinarith [sq_nonneg L]
  have hc := pow_le_pow_left₀ (by positivity) hb f
  calc (2 * Real.pi) ^ f * (x ^ f * Real.exp 1 ^ f * ((1 + L) ^ 2) ^ f)
      = (2 * Real.pi * Real.exp 1 * (1 + L) ^ 2) ^ f * x ^ f := by
        rw [mul_pow (2 * Real.pi * Real.exp 1), mul_pow (2 * Real.pi)]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)

theorem dedekindZeta_residue_le_log_rootDiscr_pow :
    ∀ (K : Type) [Field K] [NumberField K], IsTotallyComplex K →
      0 < dedekindZeta_residue K ∧ dedekindZeta_residue K ≤
        (16 * Real.log (2 * Formalism.HermitianLatticesTheory.vInv K)) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K) := by
  intro K _ _ hK
  refine ⟨dedekindZeta_residue_pos K, ?_⟩
  obtain ⟨hn, -, hx, hd⟩ := GlobalTheory.T.rootDiscr_ge_three_halves_of_isTotallyComplex K hK
  obtain ⟨hL0, hnum⟩ := residue_rankin_numeric _ hx (Formalism.HermitianLatticesTheory.fDeg K)
  set x := 2 * Formalism.HermitianLatticesTheory.vInv K with hxdef
  have hx0 : 0 < x := by linarith
  have hHR := GlobalTheory.T.classNumber_mul_regulator_le_sqrt_discr_rpow' K hK (1 + 1 / Real.log x) (by
    have : 0 < 1 / Real.log x := by positivity
    linarith)
  have hr : InfinitePlace.nrRealPlaces K = 0 := IsTotallyComplex.nrRealPlaces_eq_zero K
  have hc : InfinitePlace.nrComplexPlaces K = Formalism.HermitianLatticesTheory.fDeg K := by
    have := InfinitePlace.card_add_two_mul_card_eq_rank K
    omega
  have hw : (1 : ℝ) ≤ (Units.torsionOrder K : ℝ) := by
    exact_mod_cast Units.torsionOrder_pos K
  rw [hn, hd] at hHR
  rw [dedekindZeta_residue_def, hr, hc, hd, div_le_iff₀ (by positivity)]
  have hp : 0 < (2 * Real.pi) ^ Formalism.HermitianLatticesTheory.fDeg K := by positivity
  have hq : 0 ≤ (16 * Real.log x) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K) * x ^ Formalism.HermitianLatticesTheory.fDeg K := by positivity
  calc (2 : ℝ) ^ 0 * (2 * Real.pi) ^ Formalism.HermitianLatticesTheory.fDeg K * Units.regulator K * (classNumber K : ℝ)
      = (2 * Real.pi) ^ Formalism.HermitianLatticesTheory.fDeg K * ((classNumber K : ℝ) * Units.regulator K) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hHR hp.le
    _ ≤ _ := hnum
    _ ≤ _ := by nlinarith

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.DedekindZetaResidueLeSixteenLogRootDiscrPowStatement

section

@[expose] public section

open MeasureTheory NumberField Finset

theorem _root_.GlobalTheory.T.dedekindZeta_residue_le_sixteen_log_rootDiscr_pow : ∀ (K : Type) [Field K] [NumberField K], IsTotallyComplex K → 0 < dedekindZeta_residue K ∧ dedekindZeta_residue K ≤ (16 * Real.log (2 * Formalism.HermitianLatticesTheory.vInv K)) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K) := by
  first | exact @GlobalTheory.dedekindZeta_residue_le_log_rootDiscr_pow | exact GlobalTheory.dedekindZeta_residue_le_log_rootDiscr_pow | (intros; apply GlobalTheory.dedekindZeta_residue_le_log_rootDiscr_pow <;> assumption)
end
end
