module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.NumberTheory.LSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlobalPositivityIneqMultiplicativeCoeffStatement
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Formalism.DirichletDensity.DirichletDensityProofs.APLogDensity
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Group.Tannery
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Monotonicity.Lemmas
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Topology.Sheaves.Init
import Mathlib.Algebra.Order.Star.Real

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.NotSummableInvPrimesCongrNegOne

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

theorem sub_one_mul_log_div_rpow_le (n : ℕ) (hn : 1 < n) {x : ℝ} (hx : 1 < x) :
    (x - 1) * (Real.log n / (n : ℝ) ^ x) ≤ 1 / n := by
  have hp : (0 : ℝ) < n := by exact_mod_cast (zero_lt_one.trans hn)
  have e : (n : ℝ) ^ x = (n : ℝ) ^ (x - 1) * n := by
    rw [Real.rpow_sub_one hp.ne' x]; field_simp
  have hq : 0 < (n : ℝ) ^ (x - 1) := Real.rpow_pos_of_pos hp _
  have hl : (x - 1) * Real.log n ≤ (n : ℝ) ^ (x - 1) := by
    rw [Real.rpow_def_of_pos hp]
    have := Real.add_one_le_exp (Real.log n * (x - 1))
    nlinarith [this]
  have hrw : (x - 1) * (Real.log n / (n : ℝ) ^ x) =
      ((x - 1) * Real.log n / (n : ℝ) ^ (x - 1)) * (1 / n) := by
    rw [e]; field_simp
  rw [hrw]
  refine mul_le_of_le_one_left (by positivity) ((div_le_one hq).2 hl)

theorem not_summable_one_div_primes_eq_neg_one :
    ∀ M : ℕ, 0 < M → ¬ Summable fun p : ℕ =>
      if p.Prime ∧ (p : ZMod M) = -1 then (1 : ℝ) / p else 0 := by
  intro M hM hs
  haveI : NeZero M := ⟨hM.ne'⟩
  have hD := Formalism.HF.apLogDensity M (-1 : ZMod M) isUnit_one.neg
  unfold Formalism.HF.LogDensity at hD
  set S := {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (p : ZMod M) = -1}} with hS
  have h0 : Tendsto (fun x : ℝ => ∑' n : ℕ,
      (x - 1) * S.indicator (fun m : ℕ => Real.log m / (m : ℝ) ^ x) n) (𝓝[>] 1)
      (𝓝 (∑' _ : ℕ, (0 : ℝ))) := by
    refine tendsto_tsum_of_dominated_convergence hs (fun n => ?_) ?_
    · by_cases hn : n ∈ S
      · simp only [Set.indicator_of_mem hn]
        have hp : (0 : ℝ) < n := by exact_mod_cast hn.1.pos
        have hc : Continuous fun x : ℝ => (x - 1) * (Real.log n / (n : ℝ) ^ x) := by
          refine (continuous_id.sub continuous_const).mul (continuous_const.div ?_ ?_)
          · exact continuous_const.rpow continuous_id (fun _ => Or.inl hp.ne')
          · intro x; exact (Real.rpow_pos_of_pos hp x).ne'
        have := (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
        simpa using this
      · simp only [Set.indicator_of_notMem hn, mul_zero]
        exact tendsto_const_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx n
      have hx : (1 : ℝ) < x := hx
      by_cases hn : n ∈ S
      · have hc : n.Prime ∧ (n : ZMod M) = -1 := hn
        simp only [Set.indicator_of_mem hn, if_pos hc]
        have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hc.1.one_lt.le)
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith)
          (div_nonneg hlog (Real.rpow_nonneg n.cast_nonneg _)))]
        exact sub_one_mul_log_div_rpow_le n hc.1.one_lt hx
      · have hc : ¬ (n.Prime ∧ (n : ZMod M) = -1) := hn
        simp only [Set.indicator_of_notMem hn, if_neg hc, mul_zero, norm_zero, le_refl]
  simp only [tsum_zero, tsum_mul_left] at h0
  have hu := tendsto_nhds_unique hD h0
  have ht : (0 : ℝ) < M.totient := by exact_mod_cast Nat.totient_pos.2 hM
  rw [one_div] at hu
  exact (inv_pos.2 ht).ne' hu

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.NotSummableInvPrimesCongrNegOneStatement

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.not_summable_inv_primes_congr_neg_one : ∀ M : ℕ, 0 < M → ¬ Summable fun p : ℕ => if p.Prime ∧ (p : ZMod M) = -1 then (1 : ℝ) / p else 0 := by
  first | exact @GlobalTheory.not_summable_one_div_primes_eq_neg_one | exact GlobalTheory.not_summable_one_div_primes_eq_neg_one | (intros; apply GlobalTheory.not_summable_one_div_primes_eq_neg_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.LseriesNeZeroReGeOneOfPositivity

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem not_dvd_of_prime_of_eq_neg_one {M p : ℕ} (hp : p.Prime) (h : (p : ZMod M) = -1) :
    ¬ p ∣ M := by
  intro hpM
  have h1 : ((p + 1 : ℕ) : ZMod M) = 0 := by push_cast; rw [h]; ring
  have h1' : M ∣ p + 1 := (CharP.cast_eq_zero_iff (ZMod M) M (p + 1)).mp h1
  have : p ∣ p + 1 := hpM.trans h1'
  have : p ∣ 1 := (Nat.dvd_add_right (dvd_refl p)).mp this
  exact hp.one_lt.ne' (Nat.dvd_one.mp this)

theorem lseries_ne_zero_edge : ∀ (M : ℕ) (b ω : ℕ → ℂ) (C : ℝ) (Λ : ℂ → ℂ), 0 < M → b 1 = 1 → b 0 = 0 → (∀ m n : ℕ, m.Coprime n → b (m * n) = b m * b n) → (∀ n, ¬ n.Coprime M → b n = 0) → (∀ p r : ℕ, p.Prime → ¬ p ∣ M → ‖ω p‖ = 1 ∧ b (p ^ (r + 2)) = b p * b (p ^ (r + 1)) - ω p * b (p ^ r)) → (∀ n : ℕ, ‖b n‖ ^ 2 ≤ C * n) → (∀ s : ℝ, 0 < s → Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s)) → (∀ s : ℝ, 0 < s → s ≤ 1 → s * ∑' n : ℕ, ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s) ≤ C) → (∀ p : ℕ, p.Prime → ¬ p ∣ M → (p : ZMod M) = -1 → (b p).re = 0) → Differentiable ℂ Λ → (∀ s : ℝ, 0 < s → LSeries b ((1 + s : ℝ) : ℂ) = Λ ((1 + s : ℝ) : ℂ)) → ∀ w : ℝ, 1 ≤ w → Λ w ≠ 0 := by
  intro M b ω C Λ hM hb1 hb0 hmul hcop hrec hC hsum hsC hre hdiff hL w hw
  have G := fun s hs => GlobalTheory.T.global_positivity_ineq_multiplicative_coeff M b ω s C hs hb1 hb0 hmul hcop hrec hC (hsum s hs)
  rcases hw.lt_or_eq with hw | rfl
  · intro h0
    have hs : 0 < w - 1 := by linarith
    have := G (w - 1) hs 0
    have e : ((1 + (w - 1) : ℝ) : ℂ) = (w : ℂ) := by push_cast; ring
    rw [hL _ hs, e, h0] at this
    norm_num at this
  · intro h0
    rw [Complex.ofReal_one] at h0

    have hO := (hdiff 1).isBigO_sub
    have ht : Tendsto (fun s : ℝ => ((1 + s : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      have : Continuous fun s : ℝ => ((1 + s : ℝ) : ℂ) := by fun_prop
      have h := this.tendsto 0
      simp only [add_zero, Complex.ofReal_one] at h
      exact h.mono_left nhdsWithin_le_nhds
    obtain ⟨c, hc, hcw⟩ := (hO.comp_tendsto ht).exists_pos
    have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s ∧ s ≤ 1 ∧ ‖Λ ((1 + s : ℝ) : ℂ)‖ ≤ c * s := by
      have h1 := hcw.bound
      have h2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s := self_mem_nhdsWithin
      have h3 : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ≤ 1 :=
        nhdsWithin_le_nhds (Iic_mem_nhds (by norm_num : (0:ℝ) < 1))
      filter_upwards [h1, h2, h3] with s h1 h2 h3
      refine ⟨h2, h3, ?_⟩
      simp only [Function.comp, h0, sub_zero] at h1
      have : ((1 + s : ℝ) : ℂ) - 1 = (s : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h2] at h1
      exact h1

    have hC0 : 0 ≤ C := by
      have := hsC 1 one_pos le_rfl
      refine le_trans ?_ this
      exact mul_nonneg zero_le_one (tsum_nonneg fun n => div_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    set B : ℝ := 4 * c ^ 2 * C with hB
    let T : ℕ → Finset ℕ := fun X => (Finset.range X).filter (fun p => p.Prime ∧ (p : ZMod M) = -1)

    have key : ∀ X : ℕ, ∀ s : ℝ, 0 < s → s ≤ 1 → ‖Λ ((1 + s : ℝ) : ℂ)‖ ≤ c * s →
        ∑ p ∈ T X, (1 : ℝ) / (p : ℝ) ^ (1 + s) ≤ B := by
      intro X s hs hs1 hΛ
      set S := ∑' n : ℕ, ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s) with hS
      have hS0 : 0 ≤ S := tsum_nonneg fun n => div_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      have g := G s hs X
      rw [hL s hs] at g
      set F := (Finset.range X).filter (fun p => p.Prime ∧ ¬ p ∣ M)
      have hsub : T X ⊆ F := by
        intro p hp
        simp only [T, F, Finset.mem_filter] at hp ⊢
        exact ⟨hp.1, hp.2.1, not_dvd_of_prime_of_eq_neg_one hp.2.1 hp.2.2⟩
      have h1 : ∑ p ∈ T X, (1 : ℝ) / (p : ℝ) ^ (1 + s) ≤ ∑ p ∈ T X, ‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s) := by
        apply Finset.sum_le_sum
        intro p hp
        simp only [T, Finset.mem_filter] at hp
        have hre' := hre p hp.2.1 (not_dvd_of_prime_of_eq_neg_one hp.2.1 hp.2.2) hp.2.2
        have : (1 : ℝ) ≤ ‖1 + b p‖ ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]
          simp only [Complex.add_re, Complex.one_re, hre', Complex.add_im, Complex.one_im]
          nlinarith [sq_nonneg (b p).im]
        exact div_le_div_of_nonneg_right this (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      have h2 : ∑ p ∈ T X, ‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s) ≤ ∑ p ∈ F, ‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => div_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      have h3 := Real.add_one_le_exp (∑ p ∈ F, ‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s))
      have hL2 : ‖Λ ((1 + s : ℝ) : ℂ)‖ ^ 2 ≤ (c * s) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hΛ 2
      have hsS := hsC s hs hs1
      have h4 : 2 * (1 + 1 / s) * ‖Λ ((1 + s : ℝ) : ℂ)‖ ^ 2 * S ≤ B := by
        calc 2 * (1 + 1 / s) * ‖Λ ((1 + s : ℝ) : ℂ)‖ ^ 2 * S
            ≤ 2 * (1 + 1 / s) * (c * s) ^ 2 * S := by gcongr
          _ = 2 * (s + 1) * c ^ 2 * (s * S) := by field_simp
          _ ≤ 2 * (1 + 1) * c ^ 2 * C := by gcongr
          _ = B := by rw [hB]; ring
      linarith

    have hT : ∀ X : ℕ, ∑ p ∈ T X, (1 : ℝ) / (p : ℝ) ≤ B := by
      intro X
      have ht : Tendsto (fun s : ℝ => ∑ p ∈ T X, (1 : ℝ) / (p : ℝ) ^ (1 + s)) (𝓝[>] (0 : ℝ))
          (𝓝 (∑ p ∈ T X, (1 : ℝ) / (p : ℝ) ^ (1 + (0:ℝ)))) := by
        apply Tendsto.mono_left _ nhdsWithin_le_nhds
        apply tendsto_finsetSum
        intro p hp
        simp only [T, Finset.mem_filter] at hp
        have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.2.1.pos
        apply Continuous.tendsto
        exact continuous_const.div (continuous_const.rpow (continuous_const.add continuous_id) (fun _ => Or.inl hp0.ne'))
          (fun _ => (Real.rpow_pos_of_pos hp0 _).ne')
      simp only [add_zero, Real.rpow_one] at ht
      apply le_of_tendsto ht
      filter_upwards [hev] with s hs
      exact key X s hs.1 hs.2.1 hs.2.2
    apply GlobalTheory.T.not_summable_inv_primes_congr_neg_one M hM
    apply summable_of_sum_range_le (c := B)
    · intro n; split_ifs <;> positivity
    · intro X
      rw [← Finset.sum_filter]
      exact hT X

end GlobalTheory.EisM
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.LseriesNeZeroReGeOneOfPositivityStatement

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.lseries_ne_zero_re_ge_one_of_positivity : ∀ (M : ℕ) (b ω : ℕ → ℂ) (C : ℝ) (Λ : ℂ → ℂ), 0 < M → b 1 = 1 → b 0 = 0 → (∀ m n : ℕ, m.Coprime n → b (m * n) = b m * b n) → (∀ n, ¬ n.Coprime M → b n = 0) → (∀ p r : ℕ, p.Prime → ¬ p ∣ M → ‖ω p‖ = 1 ∧ b (p ^ (r + 2)) = b p * b (p ^ (r + 1)) - ω p * b (p ^ r)) → (∀ n : ℕ, ‖b n‖ ^ 2 ≤ C * n) → (∀ s : ℝ, 0 < s → Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s)) → (∀ s : ℝ, 0 < s → s ≤ 1 → s * ∑' n : ℕ, ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s) ≤ C) → (∀ p : ℕ, p.Prime → ¬ p ∣ M → (p : ZMod M) = -1 → (b p).re = 0) → Differentiable ℂ Λ → (∀ s : ℝ, 0 < s → LSeries b ((1 + s : ℝ) : ℂ) = Λ ((1 + s : ℝ) : ℂ)) → ∀ w : ℝ, 1 ≤ w → Λ w ≠ 0 := by
  first | exact @GlobalTheory.EisM.lseries_ne_zero_edge | exact GlobalTheory.EisM.lseries_ne_zero_edge | (intros; apply GlobalTheory.EisM.lseries_ne_zero_edge <;> assumption)
end
end
