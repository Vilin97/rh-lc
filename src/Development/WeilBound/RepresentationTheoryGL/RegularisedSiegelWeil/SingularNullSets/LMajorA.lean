module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.SmoothSeries
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.PSeries
import Mathlib.Tactic.ENatToNat
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist

-- Source module: Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LmajABumpDerivZero

section

@[expose] public section

noncomputable section

namespace PositivityTheory.Rg.Rsw.L.LMajor

open Metric
open scoped ContDiff

def lmajABump : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

lemma lmajABump_bound (m : ℕ) : ∃ C, ∀ t : ℝ, ‖iteratedFDeriv ℝ m lmajABump t‖ ≤ C :=
  ((lmajABump.contDiff (n := ⊤)).continuous_iteratedFDeriv (mod_cast le_top)).bounded_above_of_compact_support
    (lmajABump.hasCompactSupport.iteratedFDeriv m)

lemma lmajABump_deriv_zero (m : ℕ) (t : ℝ) (ht : 2 < |t|) : iteratedFDeriv ℝ m lmajABump t = 0 := by
  by_contra hne
  have h1 : t ∈ tsupport (lmajABump : ℝ → ℝ) := support_iteratedFDeriv_subset m hne
  rw [lmajABump.tsupport_eq, mem_closedBall, dist_zero_right, Real.norm_eq_abs] at h1
  exact absurd h1 (by simp [lmajABump]; linarith)

theorem lmajASeqSchwartz (b : ℕ → ℝ) (hb0 : ∀ n, 0 ≤ b n)
    (hb : ∀ k : ℕ, Summable (fun n : ℕ => b n * ((n : ℝ) + 2) ^ k)) :
    ∃ h : SchwartzMap ℝ ℂ, (∀ t, 0 ≤ (h t).re ∧ (h t).im = 0) ∧
      ∀ (n : ℕ) (t : ℝ), |t - n| ≤ 1 → b n ≤ (h t).re := by
  choose C hC using lmajABump_bound
  set φ : ℕ → ℝ → ℝ := fun n => b n • fun t => lmajABump (t - n) with hφ
  have hφc : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ n) := fun n =>
    ((lmajABump.contDiff).comp (contDiff_id.sub contDiff_const)).const_smul (b n)
  have hD : ∀ m n t, iteratedFDeriv ℝ m (φ n) t = b n • iteratedFDeriv ℝ m lmajABump (t - n) := by
    intro m n t
    have hc : ContDiff ℝ m (fun t : ℝ => lmajABump (t - n)) :=
      (lmajABump.contDiff).comp (contDiff_id.sub contDiff_const)
    rw [hφ]
    simp only
    rw [iteratedFDeriv_const_smul_apply hc.contDiffAt, iteratedFDeriv_comp_sub]
  have hs0 : Summable b := by simpa using hb 0
  have hv : ∀ m : ℕ, ((m : ℕ∞)) ≤ (⊤ : ℕ∞) → Summable (fun n => b n * C m) :=
    fun m _ => hs0.mul_right _
  have hbd : ∀ (m : ℕ) (n : ℕ) (t : ℝ), ((m : ℕ∞)) ≤ (⊤ : ℕ∞) →
      ‖iteratedFDeriv ℝ m (φ n) t‖ ≤ b n * C m := by
    intro m n t _
    rw [hD, norm_smul, Real.norm_of_nonneg (hb0 n)]
    exact mul_le_mul_of_nonneg_left (hC m _) (hb0 n)
  set g : ℝ → ℝ := fun t => ∑' n, φ n t with hg
  have hgc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g := contDiff_tsum hφc hv hbd
  have hφv : ∀ n t, φ n t = b n * lmajABump (t - n) := fun n t => rfl
  have hφs : ∀ t, Summable (fun n => φ n t) := by
    intro t
    refine hs0.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    · rw [hφv]; exact mul_nonneg (hb0 n) (lmajABump.nonneg)
    · rw [hφv]; exact mul_le_of_le_one_right (hb0 n) (lmajABump.le_one)
  have hg0 : ∀ t, 0 ≤ g t := fun t => tsum_nonneg fun n => by
    rw [hφv]; exact mul_nonneg (hb0 n) (lmajABump.nonneg)
  have hdecay : ∀ k m : ℕ, ∀ t : ℝ, ‖t‖ ^ k * ‖iteratedFDeriv ℝ m g t‖ ≤
      ∑' n, b n * ((n : ℝ) + 2) ^ k * C m := by
    intro k m t
    rw [hg, iteratedFDeriv_tsum_apply hφc hv hbd (mod_cast le_top) t]
    have hsn : Summable (fun n => ‖iteratedFDeriv ℝ m (φ n) t‖) :=
      (hv m le_top).of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => hbd m n t le_top)
    calc ‖t‖ ^ k * ‖∑' n, iteratedFDeriv ℝ m (φ n) t‖
        ≤ ‖t‖ ^ k * ∑' n, ‖iteratedFDeriv ℝ m (φ n) t‖ :=
          mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hsn) (by positivity)
      _ = ∑' n, ‖t‖ ^ k * ‖iteratedFDeriv ℝ m (φ n) t‖ := (tsum_mul_left).symm
      _ ≤ ∑' n, b n * ((n : ℝ) + 2) ^ k * C m := by
          refine (hsn.mul_left _).tsum_le_tsum (fun n => ?_) ((hb k).mul_right _)
          rw [hD, norm_smul, Real.norm_of_nonneg (hb0 n)]
          by_cases htn : |t - n| ≤ 2
          · have h1 : ‖t‖ ≤ (n : ℝ) + 2 := by
              rw [Real.norm_eq_abs]
              have := abs_sub_abs_le_abs_sub t n
              rw [Nat.abs_cast] at this
              linarith
            have h2 : ‖t‖ ^ k ≤ ((n : ℝ) + 2) ^ k := pow_le_pow_left₀ (norm_nonneg _) h1 k
            have hCm : 0 ≤ C m := (norm_nonneg _).trans (hC m 0)
            calc ‖t‖ ^ k * (b n * ‖iteratedFDeriv ℝ m (lmajABump : ℝ → ℝ) (t - n)‖)
                ≤ ((n : ℝ) + 2) ^ k * (b n * C m) :=
                  mul_le_mul h2 (mul_le_mul_of_nonneg_left (hC m _) (hb0 n)) (mul_nonneg (hb0 n) (norm_nonneg _))
                    (by positivity)
              _ = b n * ((n : ℝ) + 2) ^ k * C m := by ring
          · rw [lmajABump_deriv_zero m _ (not_le.mp htn), norm_zero, mul_zero, mul_zero]
            have hCm : 0 ≤ C m := (norm_nonneg _).trans (hC m 0)
            exact mul_nonneg (mul_nonneg (hb0 n) (by positivity)) hCm
  refine ⟨⟨Complex.ofRealLI ∘ g, ?_, ?_⟩, ?_, ?_⟩
  · exact Complex.ofRealLI.contDiff.comp hgc
  · intro k m
    refine ⟨∑' n, b n * ((n : ℝ) + 2) ^ k * C m, fun t => ?_⟩
    rw [LinearIsometry.norm_iteratedFDeriv_comp_left _ hgc.contDiffAt (mod_cast le_top)]
    exact hdecay k m t
  · intro t
    show 0 ≤ (Complex.ofRealLI (g t)).re ∧ (Complex.ofRealLI (g t)).im = 0
    simp [hg0 t]
  · intro n t ht
    have h1 : (t - n) ∈ closedBall (0 : ℝ) lmajABump.rIn := by
      rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs]; simpa [lmajABump] using ht
    have h2 : φ n t = b n := by rw [hφv, lmajABump.one_of_mem_closedBall h1, mul_one]
    show b n ≤ (Complex.ofRealLI (g t)).re
    simp only [Complex.ofRealLI_apply, Complex.ofReal_re]
    rw [← h2]
    exact (hφs t).le_tsum n (fun j _ => by rw [hφv]; exact mul_nonneg (hb0 j) (lmajABump.nonneg))

end PositivityTheory.Rg.Rsw.L.LMajor

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LmajASeq

section

@[expose] public section

noncomputable section

namespace PositivityTheory.Rg.Rsw.L.LMajor

theorem lmajASeq {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {k : ℕ}
    (f : Fin k → SchwartzMap V ℂ) (q : V → ℝ) (hq0 : ∀ y, 0 ≤ q y) (A : ℝ) (hA : 0 ≤ A)
    (hqA : ∀ y, q y ≤ A * ‖y‖ ^ 2) :
    ∃ b : ℕ → ℝ, (∀ n, 0 ≤ b n) ∧ (∀ j : ℕ, Summable (fun n : ℕ => b n * ((n : ℝ) + 2) ^ j)) ∧
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ i y, (N : ℝ) ≤ q y → ‖f i y‖ ≤ ε * b ⌊q y⌋₊ := by
  set S : ℕ → ℝ := fun j => ∑ i, (Finset.Iic (2 * j, 0)).sup
      (fun m => SchwartzMap.seminorm ℝ m.1 m.2) (f i) with hS
  set D : ℕ → ℝ := fun j => (1 + A) ^ j * (2 ^ (2 * j) * S j) with hDdef
  have hS0 : ∀ j, 0 ≤ S j := fun j => Finset.sum_nonneg fun i _ => apply_nonneg _ _
  have hD0 : ∀ j, 0 ≤ D j := fun j =>
    mul_nonneg (pow_nonneg (by linarith) _) (mul_nonneg (by positivity) (hS0 j))
  have hD : ∀ j i y, (1 + q y) ^ j * ‖f i y‖ ≤ D j := by
    intro j i y
    have h1 : 1 + q y ≤ (1 + A) * (1 + ‖y‖) ^ 2 := by
      have := hqA y; have hy := norm_nonneg y; nlinarith [mul_nonneg hA hy]
    have h2 : (1 + ‖y‖) ^ (2 * j) * ‖f i y‖ ≤ 2 ^ (2 * j) * S j := by
      have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (2 * j, 0)) (k := 2 * j)
        (n := 0) le_rfl le_rfl (f i) y
      rw [norm_iteratedFDeriv_zero] at this
      refine this.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      exact Finset.single_le_sum (f := fun i => (Finset.Iic (2 * j, 0)).sup
        (fun m => SchwartzMap.seminorm ℝ m.1 m.2) (f i)) (fun i _ => apply_nonneg _ _)
        (Finset.mem_univ i)
    calc (1 + q y) ^ j * ‖f i y‖ ≤ ((1 + A) * (1 + ‖y‖) ^ 2) ^ j * ‖f i y‖ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith [hq0 y]) h1 j) (norm_nonneg _)
      _ = (1 + A) ^ j * ((1 + ‖y‖) ^ (2 * j) * ‖f i y‖) := by rw [mul_pow, ← pow_mul]; ring
      _ ≤ D j := mul_le_mul_of_nonneg_left h2 (pow_nonneg (by linarith) _)
  set m : ℕ → ℝ := fun n => ⨅ j : ℕ, D j / (1 + (n : ℝ)) ^ j with hm
  have hbdd : ∀ n : ℕ, BddBelow (Set.range fun j : ℕ => D j / (1 + (n : ℝ)) ^ j) :=
    fun n => ⟨0, by rintro _ ⟨j, rfl⟩; exact div_nonneg (hD0 j) (by positivity)⟩
  have hm0 : ∀ n, 0 ≤ m n := fun n => le_ciInf fun j => div_nonneg (hD0 j) (by positivity)
  have hmle : ∀ n j, m n ≤ D j / (1 + (n : ℝ)) ^ j := fun n j => ciInf_le (hbdd n) j
  have hfm : ∀ i y, ‖f i y‖ ≤ m ⌊q y⌋₊ := by
    intro i y
    refine le_ciInf fun j => ?_
    rw [le_div_iff₀ (by positivity)]
    have hn : (⌊q y⌋₊ : ℝ) ≤ q y := Nat.floor_le (hq0 y)
    calc ‖f i y‖ * (1 + (⌊q y⌋₊ : ℝ)) ^ j ≤ (1 + q y) ^ j * ‖f i y‖ := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) j)
            (norm_nonneg _)
      _ ≤ D j := hD j i y
  set b : ℕ → ℝ := fun n => Real.sqrt (m n) with hb
  have hbdec : ∀ j n, b n ≤ Real.sqrt (D (2 * j)) / (1 + (n : ℝ)) ^ j := by
    intro j n
    have hpos : 0 < (1 + (n : ℝ)) ^ j := by positivity
    calc b n ≤ Real.sqrt (D (2 * j) / (1 + (n : ℝ)) ^ (2 * j)) := Real.sqrt_le_sqrt (hmle n (2 * j))
      _ = Real.sqrt (D (2 * j)) / (1 + (n : ℝ)) ^ j := by
          rw [Real.sqrt_div (hD0 _), pow_mul', Real.sqrt_sq hpos.le]
  have hsum2 : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    refine ((summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)).congr
      fun n => ?_
    push_cast; ring
  have hbs : ∀ j : ℕ, Summable (fun n : ℕ => b n * ((n : ℝ) + 2) ^ j) := by
    intro j
    refine (hsum2.mul_left (Real.sqrt (D (2 * (j + 2))) * 2 ^ j)).of_nonneg_of_le
      (fun n => mul_nonneg (Real.sqrt_nonneg _) (by positivity)) (fun n => ?_)
    have hpos : 0 < (1 + (n : ℝ)) := by positivity
    have h1 := hbdec (j + 2) n
    have h2 : ((n : ℝ) + 2) ^ j ≤ 2 ^ j * (1 + (n : ℝ)) ^ j := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) j
    calc b n * ((n : ℝ) + 2) ^ j ≤ Real.sqrt (D (2 * (j + 2))) / (1 + (n : ℝ)) ^ (j + 2) *
          (2 ^ j * (1 + (n : ℝ)) ^ j) := mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = Real.sqrt (D (2 * (j + 2))) * 2 ^ j * (1 / ((n : ℝ) + 1) ^ 2) := by
          field_simp; ring
  refine ⟨b, fun n => Real.sqrt_nonneg _, hbs, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.sqrt (D (2 * 1)) / ε)
  refine ⟨N, fun i y hy => ?_⟩
  have hNn : N ≤ ⌊q y⌋₊ := Nat.le_floor hy
  have hbε : b ⌊q y⌋₊ ≤ ε := by
    have h1 := hbdec 1 ⌊q y⌋₊
    rw [pow_one] at h1
    have hNr : (N : ℝ) ≤ (⌊q y⌋₊ : ℝ) := by exact_mod_cast hNn
    have h3 := (div_lt_iff₀ hε).mp hN
    have h4 : Real.sqrt (D (2 * 1)) / (1 + (⌊q y⌋₊ : ℝ)) ≤ ε := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  calc ‖f i y‖ ≤ m ⌊q y⌋₊ := hfm i y
    _ = b ⌊q y⌋₊ * b ⌊q y⌋₊ := (Real.mul_self_sqrt (hm0 _)).symm
    _ ≤ ε * b ⌊q y⌋₊ := mul_le_mul_of_nonneg_right hbε (Real.sqrt_nonneg _)

end PositivityTheory.Rg.Rsw.L.LMajor

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LMajorA

section

@[expose] public section

noncomputable section

namespace PositivityTheory.Rg.Rsw.L.LMajor

open Metric
open scoped ContDiff

theorem schMajor {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {k : ℕ}
    (f : Fin k → SchwartzMap V ℂ) :
    ∃ F₀ : SchwartzMap V ℂ, (∀ y, 0 ≤ (F₀ y).re ∧ (F₀ y).im = 0) ∧
      ∀ ε : ℝ, 0 < ε → ∃ c : V → ℂ, c.HasTemperateGrowth ∧ HasCompactSupport c ∧
        ∀ i y, ‖f i y‖ * ‖1 - c y‖ ≤ ε * (F₀ y).re := by
  classical
  set e : V ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) := toEuclidean with he
  set q : V → ℝ := fun y => ‖e y‖ ^ 2 with hqdef
  have hqy : ∀ y, q y = ‖e y‖ ^ 2 := fun y => rfl
  have hq0 : ∀ y, 0 ≤ q y := fun y => by rw [hqy]; positivity
  have hq : q.HasTemperateGrowth :=
    (Function.hasTemperateGrowth_norm_sq (EuclideanSpace ℝ (Fin (Module.finrank ℝ V)))).comp
      e.hasTemperateGrowth
  have hq_upper : ∃ (k : ℕ) (C : ℝ), ∀ y, ‖y‖ ≤ C * (1 + ‖q y‖) ^ k := by
    refine ⟨1, ‖(e.symm : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) →L[ℝ] V)‖, fun y => ?_⟩
    have h1 : ‖y‖ ≤ ‖(e.symm : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) →L[ℝ] V)‖ * ‖e y‖ := by
      have := (e.symm : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) →L[ℝ] V).le_opNorm (e y)
      simpa using this
    have h2 : ‖e y‖ ≤ 1 + ‖q y‖ := by
      rw [Real.norm_of_nonneg (hq0 y), hqy]
      nlinarith [sq_nonneg (‖e y‖ - 1), norm_nonneg (e y)]
    rw [pow_one]
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
  have hqA : ∀ y, q y ≤ ‖(e : V →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)))‖ ^ 2 * ‖y‖ ^ 2 := by
    intro y
    rw [hqy, ← mul_pow]
    have := (e : V →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V))).le_opNorm y
    exact pow_le_pow_left₀ (norm_nonneg _) (by simpa using this) 2
  obtain ⟨b, hb0, hbs, hbε⟩ := lmajASeq f q hq0 _ (sq_nonneg _) hqA
  obtain ⟨h, hh0, hhb⟩ := lmajASeqSchwartz b hb0 hbs
  set F₀ : SchwartzMap V ℂ := SchwartzMap.compCLM ℝ hq hq_upper h with hF₀
  have hF : ∀ y, F₀ y = h (q y) := fun y => rfl
  refine ⟨F₀, fun y => by rw [hF]; exact hh0 _, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hbε ε hε
  let β : ContDiffBump (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) :=
    ⟨(N : ℝ) + 1, (N : ℝ) + 2, by positivity, by linarith⟩
  set c : V → ℂ := fun y => ((β (e y) : ℝ) : ℂ) with hc
  have hcd : ContDiff ℝ ∞ c := Complex.ofRealCLM.contDiff.comp ((β.contDiff).comp e.contDiff)
  have hcs : HasCompactSupport c :=
    (β.hasCompactSupport.comp_homeomorph e.toHomeomorph).comp_left Complex.ofReal_zero
  refine ⟨c, hcs.hasTemperateGrowth hcd, hcs, fun i y => ?_⟩
  have hF0 : 0 ≤ (F₀ y).re := by rw [hF]; exact (hh0 _).1
  by_cases hy : ‖e y‖ ≤ (N : ℝ) + 1
  · have hβ : β (e y) = 1 :=
      β.one_of_mem_closedBall (by rw [mem_closedBall, dist_zero_right]; exact hy)
    have hc1 : c y = 1 := by simp [hc, hβ]
    rw [hc1, sub_self, norm_zero, mul_zero]
    exact mul_nonneg hε.le hF0
  · push Not at hy
    have hqN : (N : ℝ) ≤ q y := by
      rw [hqy]
      have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      nlinarith
    have h1c : ‖1 - c y‖ ≤ 1 := by
      have : (1 : ℂ) - c y = ((1 - β (e y) : ℝ) : ℂ) := by simp [hc]
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith [β.nonneg (x := e y), β.le_one (x := e y)]
    have hqn : |q y - (⌊q y⌋₊ : ℝ)| ≤ 1 := by
      have h1 := Nat.floor_le (hq0 y)
      have h2 := Nat.lt_floor_add_one (q y)
      rw [abs_le]; constructor <;> linarith
    calc ‖f i y‖ * ‖1 - c y‖ ≤ ‖f i y‖ := mul_le_of_le_one_right (norm_nonneg _) h1c
      _ ≤ ε * b ⌊q y⌋₊ := hN i y hqN
      _ ≤ ε * (F₀ y).re := by rw [hF]; exact mul_le_mul_of_nonneg_left (hhb _ _ hqn) hε.le

end PositivityTheory.Rg.Rsw.L.LMajor

end
end
end
