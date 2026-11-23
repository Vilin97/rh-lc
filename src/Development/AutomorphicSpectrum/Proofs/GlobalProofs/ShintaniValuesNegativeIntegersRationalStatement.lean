module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Formalism.SharpRestriction.GlobalSchurBounds.ShortIntervalPrimes
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConeSeriesRealDerivativeFormulaStatement
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConeSeriesDerivativeGrowthBound

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem one_le_sizeE_of_nonneg {r : ℕ} (x : Fin r → ℝ) (hx : ∀ i, 0 ≤ x i) : 1 ≤ sizeE x := by
  unfold sizeE
  have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hx i)
  linarith

theorem linF_comparable_sizeE {ι : Type} {r : ℕ} (a : ι → Fin r → ℝ) (b : ι → ℝ) (j : ι)
    (ha : ∀ i, 0 < a j i) (hb : 0 < b j) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : Fin r → ℝ, (∀ i, 0 ≤ x i) →
      c * sizeE x ≤ linF a b j x ∧ linF a b j x ≤ C * sizeE x := by
  let f : Option (Fin r) → ℝ := fun o => o.elim (b j) (a j)
  obtain ⟨p, hp⟩ := Finite.exists_min f
  obtain ⟨q, hq⟩ := Finite.exists_max f
  have hpos : ∀ o, 0 < f o := by
    intro o
    cases o with
    | none => exact hb
    | some i => exact ha i
  refine ⟨f p, f q, hpos p, hpos q, fun x hx => ?_⟩
  unfold linF sizeE
  constructor
  · rw [mul_add, mul_one, Finset.mul_sum]
    exact add_le_add (hp none)
      (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hp (some i)) (hx i))
  · rw [mul_add, mul_one, Finset.mul_sum]
    exact add_le_add (hq none)
      (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hq (some i)) (hx i))

theorem rpow_le_of_comparable (c C T : ℝ) (hc : 0 < c) (hC : 0 < C) (hT : 0 ≤ T) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ L E t D : ℝ, 1 ≤ E → c * E ≤ L → L ≤ C * E → |t| ≤ T → t ≤ D →
      L ^ t ≤ K * E ^ D := by
  refine ⟨Real.exp ((|Real.log c| + |Real.log C|) * T), (Real.exp_pos _).le, ?_⟩
  intro L E t D hE h1 h2 ht htD
  have hE0 : 0 < E := by linarith
  have hL : 0 < L := lt_of_lt_of_le (mul_pos hc hE0) h1
  have hu : 0 < L / E := div_pos hL hE0
  have hu1 : c ≤ L / E := (le_div_iff₀ hE0).2 h1
  have hu2 : L / E ≤ C := (div_le_iff₀ hE0).2 h2
  have hlog1 : Real.log c ≤ Real.log (L / E) := Real.log_le_log hc hu1
  have hlog2 : Real.log (L / E) ≤ Real.log C := Real.log_le_log hu hu2
  have habs : |Real.log (L / E)| ≤ |Real.log c| + |Real.log C| := by
    rw [abs_le]
    constructor
    · have := neg_abs_le (Real.log c)
      have := abs_nonneg (Real.log C)
      linarith
    · have := le_abs_self (Real.log C)
      have := abs_nonneg (Real.log c)
      linarith
  have hLE : L = (L / E) * E := by field_simp
  have hfirst : (L / E) ^ t ≤ Real.exp ((|Real.log c| + |Real.log C|) * T) := by
    rw [Real.rpow_def_of_pos hu]
    apply Real.exp_le_exp.2
    calc Real.log (L / E) * t ≤ |Real.log (L / E) * t| := le_abs_self _
      _ = |Real.log (L / E)| * |t| := abs_mul _ _
      _ ≤ (|Real.log c| + |Real.log C|) * T :=
        mul_le_mul habs ht (abs_nonneg _) (by positivity)
  have hsecond : E ^ t ≤ E ^ D := Real.rpow_le_rpow_of_exponent_le hE htD
  calc L ^ t = (L / E) ^ t * E ^ t := by
        rw [← Real.mul_rpow hu.le hE0.le, ← hLE]
    _ ≤ Real.exp ((|Real.log c| + |Real.log C|) * T) * E ^ D :=
        mul_le_mul hfirst hsecond (Real.rpow_nonneg hE0.le _) (Real.exp_pos _).le

theorem prod_zpow_eq_zpow_sum {ι : Type} (E : ℝ) (hE : E ≠ 0) (S : Finset ι) (f : ι → ℤ) :
    ∏ j ∈ S, E ^ f j = E ^ ∑ j ∈ S, f j := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert j S hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, zpow_add₀ hE]

theorem norm_factor_le {ι : Type} (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (j : ι)
    (ha : ∀ i, 0 < a j i) (hb : 0 < b j) (B R β : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℂ, ‖s‖ ≤ R → -(B : ℝ) ≤ s.re → ∀ x : Fin r → ℝ, (∀ i, 0 ≤ x i) →
      ‖((linF a b j x : ℝ) : ℂ) ^ (-s - (β : ℂ))‖ ≤ K * sizeE x ^ ((B : ℤ) - (β : ℤ)) := by
  obtain ⟨c, C, hc, hC, hcmp⟩ := linF_comparable_sizeE a b j ha hb
  obtain ⟨K, hK0, hK⟩ := rpow_le_of_comparable c C ((R : ℝ) + β) hc hC (by positivity)
  refine ⟨K, hK0, fun s hs hs' x hx => ?_⟩
  have hE := one_le_sizeE_of_nonneg x hx
  have hE0 : 0 < sizeE x := by linarith
  obtain ⟨h1, h2⟩ := hcmp x hx
  have hL : 0 < linF a b j x := lt_of_lt_of_le (mul_pos hc hE0) h1
  have hre : (-s - (β : ℂ)).re = -s.re - β := by simp
  have hsr : |s.re| ≤ R := (Complex.abs_re_le_norm s).trans hs
  have hβ : (0 : ℝ) ≤ β := by positivity
  have ht : |-s.re - (β : ℝ)| ≤ (R : ℝ) + β := by
    rw [abs_le] at hsr ⊢
    constructor <;> linarith [hsr.1, hsr.2]
  have htD : -s.re - (β : ℝ) ≤ (((B : ℤ) - (β : ℤ) : ℤ) : ℝ) := by
    push_cast
    linarith
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hL, hre, ← Real.rpow_intCast]
  exact hK _ _ _ _ hE h1 h2 ht htD

theorem baseBound : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ), (∀ j i, 0 < a j i) → (∀ j, 0 < b j) → ∀ (B R : ℕ) (β : ι → ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, ‖s‖ ≤ R → -(B : ℝ) ≤ s.re →
  ∀ x : Fin r → ℝ, (∀ i, 0 ≤ x i) →
    ‖Fr a b s β x‖ ≤ C * sizeE x ^ ((Fintype.card ι : ℤ) * (B : ℤ) - ∑ j, (β j : ℤ)) := by
  intro ι _ r a b ha hb B R β
  have hj := fun j => norm_factor_le r a b j (ha j) (hb j) B R (β j)
  choose K hK0 hK using hj
  refine ⟨∏ j, K j, Finset.prod_nonneg fun j _ => hK0 j, fun s hs hs' x hx => ?_⟩
  have hE0 : sizeE x ≠ 0 := by
    have := one_le_sizeE_of_nonneg x hx
    intro h
    linarith
  unfold Fr
  rw [norm_prod]
  calc ∏ j, ‖((linF a b j x : ℝ) : ℂ) ^ (-s - (β j : ℂ))‖
      ≤ ∏ j, (K j * sizeE x ^ ((B : ℤ) - (β j : ℤ))) :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ => hK j s hs hs' x hx)
    _ = (∏ j, K j) * sizeE x ^ ((Fintype.card ι : ℤ) * (B : ℤ) - ∑ j, (β j : ℤ)) := by
        rw [Finset.prod_mul_distrib, prod_zpow_eq_zpow_sum _ hE0, Finset.sum_sub_distrib]
        simp

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConeSeriesDerivativeGrowthBoundStatement

section

@[expose] public section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem _root_.GlobalTheory.T.cone_series_derivative_growth_bound : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ), (∀ j i, 0 < a j i) → (∀ j, 0 < b j) → ∀ (B R : ℕ) (β : ι → ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, ‖s‖ ≤ R → -(B : ℝ) ≤ s.re →
  ∀ x : Fin r → ℝ, (∀ i, 0 ≤ x i) →
    ‖Fr a b s β x‖ ≤ C * sizeE x ^ ((Fintype.card ι : ℤ) * (B : ℤ) - ∑ j, (β j : ℤ)) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.baseBound | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.baseBound | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.baseBound <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.ShintaniValuesNegativeIntegersRational

section

@[expose] public section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DiffDecay

theorem zpow_le_two_pow_mul {E u : ℝ} (hE : 0 < E) (h1 : E ≤ u) (h2 : u ≤ 2 * E) (z : ℤ) :
    u ^ z ≤ 2 ^ z.natAbs * E ^ z := by
  have hu : 0 < u := lt_of_lt_of_le hE h1
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  · simp only [Int.natAbs_natCast, zpow_natCast]
    calc u ^ n ≤ (2 * E) ^ n := pow_le_pow_left₀ hu.le h2 n
      _ = 2 ^ n * E ^ n := mul_pow _ _ _
  · simp only [Int.natAbs_neg, Int.natAbs_natCast, zpow_neg, zpow_natCast]
    have hEn : 0 < E ^ n := pow_pos hE n
    have a1 : (u ^ n)⁻¹ ≤ (E ^ n)⁻¹ := inv_anti₀ hEn (pow_le_pow_left₀ hE.le h1 n)
    have a2 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    calc (u ^ n)⁻¹ ≤ (E ^ n)⁻¹ := a1
      _ = 1 * (E ^ n)⁻¹ := (one_mul _).symm
      _ ≤ 2 ^ n * (E ^ n)⁻¹ := mul_le_mul_of_nonneg_right a2 (inv_nonneg.2 hEn.le)

theorem one_le_sizeE {r : ℕ} {x : Fin r → ℝ} (hx : ∀ i, 0 ≤ x i) : 1 ≤ sizeE x := by
  have : 0 ≤ ∑ i, x i := Finset.sum_nonneg fun i _ => hx i
  unfold sizeE; linarith

theorem sizeE_add_smul {r : ℕ} (x : Fin r → ℝ) (c : Fin r) (τ : ℝ) :
    sizeE (x + τ • (Pi.single c 1 : Fin r → ℝ)) = sizeE x + τ := by
  simp [sizeE, Finset.sum_add_distrib, Pi.single_apply]
  ring

theorem nonneg_add_smul {r : ℕ} {x : Fin r → ℝ} (hx : ∀ i, 0 ≤ x i) (c : Fin r) {τ : ℝ} (hτ : 0 ≤ τ) (k : Fin r) :
    0 ≤ (x + τ • (Pi.single c 1 : Fin r → ℝ)) k := by
  have : 0 ≤ τ * (Pi.single c 1 : Fin r → ℝ) k := by
    refine mul_nonneg hτ ?_
    by_cases h : k = c
    · subst h; simp
    · simp [Pi.single_apply, h]
  simpa using add_nonneg (hx k) this

theorem sum_add_single {ι : Type} [Fintype ι] [DecidableEq ι] (β : ι → ℕ) (j : ι) :
    ∑ i, (((β + Pi.single j 1 : ι → ℕ) i : ℕ) : ℤ) = ∑ i, (β i : ℤ) + 1 := by
  simp [Finset.sum_add_distrib, Pi.single_apply]

theorem diff_bound (ι : Type) [Fintype ι] [DecidableEq ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (ha : ∀ j i, 0 < a j i) (hb : ∀ j, 0 < b j) (B R : ℕ) (cs : List (Fin r)) (β : ι → ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, ‖s‖ ≤ R → -(B : ℝ) ≤ s.re → ∀ x : Fin r → ℝ, (∀ i, 0 ≤ x i) →
      ‖DLR cs (Fr a b s β) x‖ ≤ C * sizeE x ^ ((Fintype.card ι : ℤ) * (B : ℤ) - ∑ j, (β j : ℤ) - (cs.length : ℤ)) := by
  induction cs generalizing β with
  | nil =>
    obtain ⟨C, hC, h⟩ := GlobalTheory.T.cone_series_derivative_growth_bound ι r a b ha hb B R β
    refine ⟨C, hC, fun s hs hB x hx => ?_⟩
    simpa [DLR] using h s hs hB x hx
  | cons c cs ih =>
    choose C hC0 hC using fun j => ih (β + Pi.single j 1)
    obtain ⟨z, hz⟩ : ∃ z : ℤ, z = (Fintype.card ι : ℤ) * (B : ℤ) - ∑ j, (β j : ℤ) - ((c :: cs).length : ℤ) := ⟨_, rfl⟩
    rw [← hz]
    have hzj : ∀ j, (Fintype.card ι : ℤ) * (B : ℤ) - ∑ i, (((β + Pi.single j 1 : ι → ℕ) i : ℕ) : ℤ) - (cs.length : ℤ) = z := by
      intro j
      rw [sum_add_single, hz, List.length_cons]
      push_cast
      ring
    have hterm : ∀ j, 0 ≤ ((R : ℝ) + β j) * a j c * C j := fun j =>
      mul_nonneg (mul_nonneg (by positivity) (ha j c).le) (hC0 j)
    refine ⟨(∑ j, ((R : ℝ) + β j) * a j c * C j) * 2 ^ z.natAbs,
      mul_nonneg (Finset.sum_nonneg fun j _ => hterm j) (by positivity), fun s hs hB x hx => ?_⟩
    have hE1 : 1 ≤ sizeE x := one_le_sizeE hx
    have hE0 : 0 < sizeE x := by linarith
    have hmv := norm_image_sub_le_of_norm_deriv_le_segment_01'
      (f := fun t : ℝ => DLR cs (Fr a b s β) (x + t • (Pi.single c 1 : Fin r → ℝ)))
      (f' := fun τ => ∑ j, (-s - (β j : ℂ)) * (a j c : ℂ) *
        DLR cs (Fr a b s (β + Pi.single j 1)) (x + τ • (Pi.single c 1 : Fin r → ℝ)))
      (C := (∑ j, ((R : ℝ) + β j) * a j c * C j) * 2 ^ z.natAbs * sizeE x ^ z)
      (fun τ hτ => (GlobalTheory.T.cone_series_real_derivative_formula ι r a b ha hb s β cs c x τ hx hτ.1).hasDerivWithinAt)
      (fun τ hτ => ?_)
    · simpa [DLR, fdR] using hmv
    · have hu1 : sizeE x ≤ sizeE (x + τ • (Pi.single c 1 : Fin r → ℝ)) := by
        rw [sizeE_add_smul]; linarith [hτ.1]
      have hu2 : sizeE (x + τ • (Pi.single c 1 : Fin r → ℝ)) ≤ 2 * sizeE x := by
        rw [sizeE_add_smul]; linarith [hτ.2.le]
      have hpow := zpow_le_two_pow_mul hE0 hu1 hu2 z
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_le_sum fun j _ => ?_
      have hD := hC j s hs hB _ (nonneg_add_smul hx c hτ.1)
      rw [hzj j] at hD
      have hs1 : ‖-s - (β j : ℂ)‖ ≤ (R : ℝ) + β j := by
        refine (norm_sub_le _ _).trans ?_
        simpa using hs
      have ha1 : ‖(a j c : ℂ)‖ = a j c := by
        simp [abs_of_pos (ha j c)]
      rw [norm_mul, norm_mul, ha1]
      calc ‖-s - (β j : ℂ)‖ * a j c * ‖DLR cs (Fr a b s (β + Pi.single j 1)) (x + τ • (Pi.single c 1 : Fin r → ℝ))‖
          ≤ ((R : ℝ) + β j) * a j c * (C j * (2 ^ z.natAbs * sizeE x ^ z)) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_right hs1 (ha j c).le) (hD.trans ?_) (norm_nonneg _)
              (mul_nonneg (by positivity) (ha j c).le)
            exact mul_le_mul_of_nonneg_left hpow (hC0 j)
        _ = ((R : ℝ) + β j) * a j c * C j * 2 ^ z.natAbs * sizeE x ^ z := by ring

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DiffDecay
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.ShintaniValuesNegativeIntegersRationalStatement

section

@[expose] public section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem _root_.GlobalTheory.T.real_difference_cone_bound : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ), (∀ j i, 0 < a j i) → (∀ j, 0 < b j) → ∀ (B R : ℕ) (cs : List (Fin r)) (β : ι → ℕ),
  ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, ‖s‖ ≤ R → -(B : ℝ) ≤ s.re → ∀ x : Fin r → ℝ, (∀ i, 0 ≤ x i) →
    ‖DLR cs (Fr a b s β) x‖ ≤ C * sizeE x ^ ((Fintype.card ι : ℤ) * (B : ℤ) - ∑ j, (β j : ℤ) - (cs.length : ℤ)) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DiffDecay.diff_bound | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DiffDecay.diff_bound | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DiffDecay.diff_bound <;> assumption)
end
end
