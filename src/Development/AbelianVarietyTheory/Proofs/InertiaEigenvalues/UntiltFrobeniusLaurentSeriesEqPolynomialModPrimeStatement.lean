module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusLaurentSeriesHasSumBoundFrobeniusStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Order.Interval.Finset.Box
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltFrobeniusIntegerPowerLawsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUntiltToComplexPAdicBasicLawsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UltrametricNormHasSumSubFinsetSumLeStatement
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.Completion

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoeffHasSumUntiltFrobeniusCombination

section

@[expose] public section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.PSer

theorem emod_toNat_lt (h : ℕ) (hh : 1 ≤ h) (k : ℤ) : (k % (h : ℤ)).toNat < h := by
  have h0 : (0 : ℤ) < h := by exact_mod_cast hh
  have := Int.emod_lt_of_pos k h0
  have := Int.emod_nonneg k h0.ne'
  omega

def reCoef (l : ℕ) [Fact l.Prime] (h : ℕ) (hh : 1 ≤ h) (μ : Fin h → ℂ_[l]) (k : ℤ) : ℂ_[l] :=
  (l : ℂ_[l]) ^ (-(k / (h : ℤ))) * μ ⟨(k % (h : ℤ)).toNat, emod_toNat_lt h hh k⟩

theorem reCoef_add (l : ℕ) [Fact l.Prime] (h : ℕ) (hh : 1 ≤ h) (μ : Fin h → ℂ_[l]) (k : ℤ) :
    reCoef l h hh μ k = (l : ℂ_[l]) * reCoef l h hh μ (k + h) := by
  have hl : (l : ℂ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have h0 : (h : ℤ) ≠ 0 := by exact_mod_cast (by omega : h ≠ 0)
  have e1 : (k + h) / (h : ℤ) = k / h + 1 := by
    have := Int.add_mul_ediv_right k 1 h0; simpa using this
  have e2 : (k + h) % (h : ℤ) = k % h := by simp
  unfold reCoef
  simp only [e1, e2]
  rw [neg_add, zpow_add₀ hl, zpow_neg_one]
  field_simp

theorem reCoef_at (l : ℕ) [Fact l.Prime] (h : ℕ) (hh : 1 ≤ h) (μ : Fin h → ℂ_[l]) (n : ℤ) (i : Fin h) :
    reCoef l h hh μ (n * h + i) = (l : ℂ_[l]) ^ (-n) * μ i := by
  have h0 : (h : ℤ) ≠ 0 := by exact_mod_cast (by omega : h ≠ 0)
  have hi0 : (0 : ℤ) ≤ (i : ℤ) := by positivity
  have hih : (i : ℤ) < h := by exact_mod_cast i.isLt
  have e1 : (n * h + i) / (h : ℤ) = n := by
    rw [add_comm, Int.add_mul_ediv_right _ _ h0, Int.ediv_eq_zero_of_lt hi0 hih, zero_add]
  have e2 : (n * h + i) % (h : ℤ) = i := by
    rw [add_comm, Int.add_mul_emod_self_right, Int.emod_eq_of_lt hi0 hih]
  unfold reCoef
  congr 2
  · rw [e1]
  · ext; simp [e2]

theorem emod_at (h : ℕ) (hh : 1 ≤ h) (n : ℤ) (i : Fin h) :
    (n * h + ((i : ℕ) : ℤ)) % (h : ℤ) = ((i : ℕ) : ℤ) := by
  have hi0 : (0 : ℤ) ≤ ((i : ℕ) : ℤ) := by positivity
  have hih : ((i : ℕ) : ℤ) < h := by exact_mod_cast i.isLt
  rw [add_comm, Int.add_mul_emod_self_right, Int.emod_eq_of_lt hi0 hih]

theorem exists_coef_hasSum_lam : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l]), 1 ≤ h → μ ≠ 0 →
    ∃ m : ℤ → ℂ_[l], (∀ k, m k = (l : ℂ_[l]) * m (k + h)) ∧ (∃ k, m k ≠ 0) ∧
      ∀ x : Fl l, ‖sh x‖ < 1 →
        HasSum (fun k : ℤ => m k * sh (pw k x)) (∑ i : Fin h, μ i * lam h i x) := by
  intro l _ h μ hh hμ
  have h0 : (h : ℤ) ≠ 0 := by exact_mod_cast (by omega : h ≠ 0)
  refine ⟨reCoef l h hh μ, reCoef_add l h hh μ, ?_, ?_⟩
  · obtain ⟨i, hi⟩ : ∃ i, μ i ≠ 0 := by
      by_contra H; push_neg at H; exact hμ (funext H)
    refine ⟨((i : ℕ) : ℤ), ?_⟩
    have := reCoef_at l h hh μ 0 i
    simp only [zero_mul, zero_add, neg_zero, zpow_zero, one_mul] at this
    rw [this]; exact hi
  · intro x hx
    let f : ℤ → ℂ_[l] := fun k => reCoef l h hh μ k * sh (pw k x)
    let F : Fin h → ℤ → ℂ_[l] := fun i k => if k % (h : ℤ) = ((i : ℕ) : ℤ) then f k else 0
    have hF : ∀ k, f k = ∑ i, F i k := by
      intro k
      have hn : 0 ≤ k % (h : ℤ) := Int.emod_nonneg k h0
      rw [Finset.sum_eq_single ⟨(k % (h : ℤ)).toNat, emod_toNat_lt h hh k⟩]
      · simp only [F]; rw [if_pos (by simp [Int.toNat_of_nonneg hn])]
      · intro b _ hb
        simp only [F]
        rw [if_neg]
        intro hbk
        apply hb
        ext
        simp only
        omega
      · intro hc; exact absurd (Finset.mem_univ _) hc
    have hFi : ∀ i : Fin h, HasSum (F i) (μ i * lam h i x) := by
      intro i
      have hg : Function.Injective (fun n : ℤ => n * h + ((i : ℕ) : ℤ)) := by
        intro a b e
        have e' : a * (h : ℤ) = b * h := by simpa using e
        exact mul_right_cancel₀ h0 e'
      rw [← hg.hasSum_iff]
      · have := ((GlobalTheory.T.untiltFrobeniusLaurentSeries_hasSum_bound_frobenius l h i ‖sh x‖ x hh hx le_rfl).1).mul_left (μ i)
        have heq : (F i ∘ fun n : ℤ => n * h + ((i : ℕ) : ℤ)) =
            fun n : ℤ => μ i * ((l : ℂ_[l]) ^ (-n) * sh (pw (n * h + ((i : ℕ) : ℤ)) x)) := by
          funext n
          simp only [Function.comp, F, f]
          rw [if_pos (emod_at h hh n i), reCoef_at]
          ring
        rw [heq]; exact this
      · intro k hk
        simp only [F]
        rw [if_neg]
        intro hki
        apply hk
        refine ⟨k / h, ?_⟩
        have := Int.ediv_mul_add_emod k (h : ℤ)
        simp only
        rw [← hki]
        linarith [mul_comm (k / (h : ℤ)) (h : ℤ)]
    have := hasSum_sum (s := Finset.univ) (fun i _ => hFi i)
    have hf : f = fun k => ∑ i, F i k := funext hF
    show HasSum f _
    rw [hf]; exact this

end GlobalTheory.PSer
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoeffHasSumUntiltFrobeniusCombinationStatement

section

@[expose] public section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_coeff_hasSum_untiltFrobeniusCombination : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l]), 1 ≤ h → μ ≠ 0 → ∃ m : ℤ → ℂ_[l], (∀ k, m k = (l : ℂ_[l]) * m (k + h)) ∧ (∃ k, m k ≠ 0) ∧ ∀ x : Fl l, ‖sh x‖ < 1 → HasSum (fun k : ℤ => m k * sh (pw k x)) (∑ i : Fin h, μ i * lam h i x) := by
  first | exact @GlobalTheory.PSer.exists_coef_hasSum_lam | exact GlobalTheory.PSer.exists_coef_hasSum_lam | (intros; apply GlobalTheory.PSer.exists_coef_hasSum_lam <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WindowAroundLastMaxNullSequence

section

@[expose] public section

open Polynomial

namespace GlobalTheory

theorem window_around_last_max : ∀ (β : ℤ → ℝ) (c : ℝ) (h : ℕ), 0 < c → (∀ k, 0 ≤ β k) → (∃ k, β k ≠ 0) → Filter.Tendsto β Filter.cofinite (nhds 0) → ∃ (D E M : ℕ), h ≤ D ∧ M + h ≤ E ∧ 0 < β ((M + h : ℕ) - D) ∧ (∀ k, β k ≤ β ((M + h : ℕ) - D)) ∧ (∀ k, ((M + h : ℕ) : ℤ) - D < k → β k < β ((M + h : ℕ) - D)) ∧ ∀ k : ℤ, (k < -(D : ℤ) ∨ (E : ℤ) - D < k) → β k ≤ c * β ((M + h : ℕ) - D) := by
  intro β c h hc hβ0 hne hlim
  have hfin : ∀ ε : ℝ, 0 < ε → {k | ε ≤ β k}.Finite := by
    intro ε hε
    have h1 : ∀ᶠ k in Filter.cofinite, β k < ε := hlim.eventually (gt_mem_nhds hε)
    rw [Filter.eventually_cofinite] at h1
    simpa [not_lt] using h1
  obtain ⟨k₀, hk₀⟩ := hne
  have hpos : 0 < β k₀ := lt_of_le_of_ne (hβ0 k₀) (Ne.symm hk₀)
  set T := (hfin _ hpos).toFinset with hT
  have hk₀T : k₀ ∈ T := by simp [T]
  obtain ⟨m, hmT, hm⟩ := T.exists_max_image β ⟨k₀, hk₀T⟩
  have hmax : ∀ k, β k ≤ β m := by
    intro k
    by_cases hk : β k₀ ≤ β k
    · exact hm k (by simp [T, hk])
    · push_neg at hk
      have : β k₀ ≤ β m := hm k₀ hk₀T
      linarith
  set U := T.filter (fun k => β k = β m) with hU
  have hmU : m ∈ U := Finset.mem_filter.2 ⟨hmT, rfl⟩
  set N := U.max' ⟨m, hmU⟩ with hNdef
  have hNU : N ∈ U := U.max'_mem _
  have hN : β N = β m := (Finset.mem_filter.1 hNU).2
  have hk₀m : β k₀ ≤ β m := hm k₀ hk₀T
  have hNlast : ∀ k, N < k → β k < β N := by
    intro k hk
    rcases lt_or_eq_of_le (hmax k) with h1 | h1
    · rw [hN]; exact h1
    · exfalso
      have hkU : k ∈ U := by
        refine Finset.mem_filter.2 ⟨?_, h1⟩
        simp [T]; linarith
      have := U.le_max' k hkU
      omega
  have hc₀ : 0 < β N := by rw [hN]; linarith
  have hcpos : 0 < c * β N := mul_pos hc hc₀
  set F := (hfin _ hcpos).toFinset with hF
  set B : ℕ := (F.image (fun k => k.natAbs)).sup id ⊔ N.natAbs with hB
  have hNB : N.natAbs ≤ B := le_sup_right
  have hFB : ∀ k, c * β N ≤ β k → k.natAbs ≤ B := by
    intro k hk
    have hkF : k ∈ F := by simp [F, hk]
    have : k.natAbs ≤ (F.image (fun k => k.natAbs)).sup id :=
      Finset.le_sup (f := id) (Finset.mem_image_of_mem _ hkF)
    exact le_trans this le_sup_left
  refine ⟨B + h, B + h + B, (N + B).toNat, ?_⟩
  have hx : ((((N + (B : ℤ)).toNat + h : ℕ)) : ℤ) - ((B + h : ℕ) : ℤ) = N := by omega
  rw [hx]
  refine ⟨by omega, by omega, hc₀, fun k => hN ▸ hmax k, fun k hk => hNlast k hk, ?_⟩
  intro k hk
  by_contra hlt
  push_neg at hlt
  have := hFB k hlt.le
  omega

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WindowAroundLastMaxNullSequenceStatement

section

@[expose] public section

open Polynomial

theorem _root_.GlobalTheory.T.window_around_last_max_null_sequence : ∀ (β : ℤ → ℝ) (c : ℝ) (h : ℕ), 0 < c → (∀ k, 0 ≤ β k) → (∃ k, β k ≠ 0) → Filter.Tendsto β Filter.cofinite (nhds 0) → ∃ (D E M : ℕ), h ≤ D ∧ M + h ≤ E ∧ 0 < β ((M + h : ℕ) - D) ∧ (∀ k, β k ≤ β ((M + h : ℕ) - D)) ∧ (∀ k, ((M + h : ℕ) : ℤ) - D < k → β k < β ((M + h : ℕ) - D)) ∧ ∀ k : ℤ, (k < -(D : ℤ) ∨ (E : ℤ) - D < k) → β k ≤ c * β ((M + h : ℕ) - D) := by
  first | exact @GlobalTheory.window_around_last_max | exact GlobalTheory.window_around_last_max | (intros; apply GlobalTheory.window_around_last_max <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusLaurentSeriesEqPolynomialModPrime

section

@[expose] public section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PolyRoot

theorem key_exp (l : ℕ) [Fact l.Prime] (h : ℕ) (P : ℝ) (hP : 0 < P) (k : ℤ) :
    P ^ ((l:ℝ) ^ k) * P ^ (((l:ℝ) ^ h - 1) * (l:ℝ) ^ k) = P ^ ((l:ℝ) ^ (k + h)) := by
  have hl : (l:ℝ) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  rw [← Real.rpow_add hP, zpow_add₀ hl, zpow_natCast]
  congr 1; ring

theorem rho_pow (l : ℕ) [Fact l.Prime] (h D n : ℕ) (P : ℝ) (hP : 0 ≤ P) :
    (P ^ (((l:ℝ) ^ h - 1) / (l:ℝ) ^ D)) ^ (l ^ n) = P ^ (((l:ℝ) ^ h - 1) * (l:ℝ) ^ ((n:ℤ) - D)) := by
  have hl : (l:ℝ) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  rw [← Real.rpow_natCast, ← Real.rpow_mul hP, zpow_sub₀ hl, zpow_natCast, zpow_natCast]
  congr 1; push_cast; ring

theorem poly_root_mod_l : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l]) (σ : Fl l), 1 ≤ h → μ ≠ 0 → sh σ = l → ∃ (t : ℂ_[l]) (D E M : ℕ) (a : ℕ → ℂ_[l]) (ρ : ℝ), t ≠ 0 ∧ M + h ≤ E ∧ (∀ k, k ≤ E → ‖a k‖ ≤ 1) ∧ ‖a (M + h)‖ = 1 ∧ ‖(l : ℂ_[l])‖ ≤ ρ ∧ ρ < 1 ∧ ‖(l : ℂ_[l])‖ * ρ ^ l ^ D = ‖(l : ℂ_[l])‖ ^ l ^ h ∧ ‖a M‖ * ρ ^ l ^ M = ‖(l : ℂ_[l])‖ ∧ (∀ k, M < k → k ≤ E → ‖a k‖ * ρ ^ l ^ k < ‖(l : ℂ_[l])‖) ∧ ∀ u : Fl l, ‖∑ i : Fin h, μ i * lam h i (σ * u ^ l ^ D) - t * ∑ k ∈ Finset.range (E + 1), a k * sh u ^ l ^ k‖ ≤ ‖(l : ℂ_[l])‖ * ‖t‖ := by
  intro l _ h μ σ h1 hμ hσ
  obtain ⟨pwadd, pwmul, pwzero, pwcomp, pwnat, pwpow, pwnorm⟩ := GlobalTheory.T.tiltFrobeniusIntegerPower_laws l
  obtain ⟨sh1, sh0, shmul, shpow, shle, shsurj, shadd, shneg⟩ := GlobalTheory.T.tiltUntiltToComplexPAdic_basic_laws l
  obtain ⟨m, hm, ⟨k0, hk0⟩, hsum⟩ := GlobalTheory.T.exists_coeff_hasSum_untiltFrobeniusCombination l h μ h1 hμ
  obtain ⟨P, hPd⟩ : ∃ P : ℝ, P = ‖(l : ℂ_[l])‖ := ⟨_, rfl⟩
  rw [← hPd]
  have hP0 : 0 < P := hPd ▸ norm_pos_iff.2 GlobalTheory.RingBasics.p_ne_zero
  have hP1 : P < 1 := hPd ▸ GlobalTheory.RingBasics.norm_p_lt
  have hσn : ‖sh σ‖ = P := by rw [hσ, hPd]
  obtain ⟨α, hα⟩ : ∃ α : ℤ → ℂ_[l], ∀ k, α k = m k * sh (pw k σ) := ⟨_, fun _ => rfl⟩
  obtain ⟨β, hβd⟩ : ∃ β : ℤ → ℝ, ∀ k, β k = ‖α k‖ := ⟨_, fun _ => rfl⟩
  have hshσ : ∀ k : ℤ, ‖sh (pw k σ)‖ = P ^ ((l:ℝ) ^ k) := fun k => by rw [pwnorm, hσn]
  have hβ : ∀ k, β k = ‖m k‖ * P ^ ((l:ℝ) ^ k) := fun k => by
    rw [hβd, hα, norm_mul, hshσ]
  have hkey : ∀ k : ℤ, β k * P ^ (((l:ℝ) ^ h - 1) * (l:ℝ) ^ k) = P * β (k + h) := fun k => by
    rw [hβ, hβ, hm k, norm_mul, ← hPd, ← key_exp l h P hP0 k]; ring
  have hσlt : ‖sh σ‖ < 1 := hσn ▸ hP1
  have hαsum : Summable α := by
    have := (hsum σ hσlt).summable
    rwa [show (fun k : ℤ => m k * sh (pw k σ)) = α from funext fun k => (hα k).symm] at this
  have hβt : Filter.Tendsto β Filter.cofinite (nhds 0) := by
    have := (hαsum.tendsto_cofinite_zero).norm
    rw [norm_zero] at this
    rwa [show (fun k => ‖α k‖) = β from funext fun k => (hβd k).symm] at this
  have hβne : ∃ k, β k ≠ 0 := ⟨k0, by
    rw [hβ]; exact mul_ne_zero (norm_ne_zero_iff.2 hk0) (Real.rpow_pos_of_pos hP0 _).ne'⟩
  have hβ0 : ∀ k, 0 ≤ β k := fun k => by rw [hβd]; exact norm_nonneg _
  obtain ⟨D, E, M, hD, hME, hpos, hmax, hstrict, htail⟩ :=
    GlobalTheory.T.window_around_last_max_null_sequence β P h hP0 hβ0 hβne hβt
  obtain ⟨N, hN⟩ : ∃ N : ℤ, N = ((M + h : ℕ) : ℤ) - D := ⟨_, rfl⟩
  rw [← hN] at hpos hmax hstrict htail
  have htn : ‖α N‖ = β N := (hβd N).symm
  have ht0 : α N ≠ 0 := by intro h0; rw [← norm_eq_zero, htn] at h0; linarith
  have hl2 : (2:ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).two_le
  have hlD : (0:ℝ) < (l:ℝ) ^ D := by positivity
  have hnorm_a : ∀ k : ℕ, ‖α ((k:ℤ) - D) / α N‖ = β ((k:ℤ) - D) / β N := fun k => by
    rw [norm_div, htn, ← hβd]
  have hprod : ∀ k : ℕ, ‖α ((k:ℤ) - D) / α N‖ * (P ^ (((l:ℝ) ^ h - 1) / (l:ℝ) ^ D)) ^ (l ^ k)
      = P * β ((k:ℤ) - D + h) / β N := fun k => by
    rw [hnorm_a, rho_pow l h D k P hP0.le, div_mul_eq_mul_div, hkey]
  refine ⟨α N, D, E, M, fun k : ℕ => α ((k:ℤ) - D) / α N, P ^ (((l:ℝ) ^ h - 1) / (l:ℝ) ^ D),
    ht0, hME, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k _
    show ‖α ((k:ℤ) - D) / α N‖ ≤ 1
    rw [hnorm_a, div_le_one hpos]; exact hmax _
  · show ‖α (((M + h : ℕ) : ℤ) - D) / α N‖ = 1
    rw [← hN, div_self ht0, norm_one]
  · have he : ((l:ℝ) ^ h - 1) / (l:ℝ) ^ D ≤ 1 := by
      rw [div_le_one hlD]
      have : (l:ℝ) ^ h ≤ (l:ℝ) ^ D := pow_le_pow_right₀ (by linarith) hD
      linarith
    calc P = P ^ (1:ℝ) := (Real.rpow_one P).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hP0 hP1.le he
  · have hq : (l:ℝ) ≤ (l:ℝ) ^ h := le_self_pow₀ (by linarith) (by omega)
    exact Real.rpow_lt_one hP0.le hP1 (div_pos (by linarith) hlD)
  · rw [rho_pow l h D D P hP0.le, sub_self, zpow_zero, mul_one, ← Real.rpow_natCast P (l ^ h)]
    rw [show P * P ^ ((l:ℝ) ^ h - 1) = P ^ ((1:ℝ) + ((l:ℝ) ^ h - 1)) by
      rw [Real.rpow_add hP0, Real.rpow_one]]
    congr 1; push_cast; ring
  · show ‖α ((M:ℤ) - D) / α N‖ * _ = P
    rw [hprod, show (M:ℤ) - D + h = N by rw [hN]; push_cast; ring, mul_div_assoc,
      div_self hpos.ne', mul_one]
  · intro k hk _
    show ‖α ((k:ℤ) - D) / α N‖ * _ < P
    rw [hprod, div_lt_iff₀ hpos]
    exact mul_lt_mul_of_pos_left (hstrict _ (by omega)) hP0
  · intro u
    have hx : ‖sh (σ * u ^ l ^ D)‖ < 1 := by
      rw [shmul, shpow, norm_mul, norm_pow, hσn]
      calc P * ‖sh u‖ ^ l ^ D ≤ P * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) (shle u)) hP0.le
        _ < 1 := by rw [mul_one]; exact hP1
    have hS := hsum _ hx
    have hf : ∀ k : ℤ, m k * sh (pw k (σ * u ^ l ^ D)) = α k * sh (pw (k + D) u) := fun k => by
      rw [hα, pwmul, ← pwnat D u, ← pwcomp, shmul]; ring
    rw [show (fun k : ℤ => m k * sh (pw k (σ * u ^ l ^ D))) = fun k => α k * sh (pw (k + D) u)
      from funext hf] at hS
    have htr := GlobalTheory.T.ultrametric_norm_hasSum_sub_finset_sum_le ℂ_[l] ℤ (fun k => α k * sh (pw (k + D) u)) _
      ((Finset.range (E + 1)).image (fun k : ℕ => (k:ℤ) - D)) (P * ‖α N‖)
      (mul_nonneg hP0.le (norm_nonneg _)) hS (by
        intro j hj
        have hj' : j < -(D:ℤ) ∨ (E:ℤ) - D < j := by
          by_contra hc
          push_neg at hc
          apply hj
          rw [Finset.mem_image]
          exact ⟨(j + D).toNat, Finset.mem_range.2 (by omega), by omega⟩
        show ‖α j * sh (pw (j + D) u)‖ ≤ P * ‖α N‖
        rw [norm_mul, ← hβd, htn]
        exact (mul_le_of_le_one_right (hβ0 j) (shle _)).trans (htail j hj'))
    have heq : ∑ j ∈ (Finset.range (E + 1)).image (fun k : ℕ => (k:ℤ) - D), α j * sh (pw (j + D) u)
        = α N * ∑ k ∈ Finset.range (E + 1), α ((k:ℤ) - D) / α N * sh u ^ l ^ k := by
      rw [Finset.sum_image (fun x _ y _ hxy => by simpa using hxy), Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [sub_add_cancel, pwnat, shpow]
      field_simp
    rw [heq] at htr
    exact htr

end GlobalTheory.PolyRoot
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusLaurentSeriesEqPolynomialModPrimeStatement

section

@[expose] public section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.untiltFrobeniusLaurentSeries_eq_polynomial_mod_prime : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l]) (σ : Fl l), 1 ≤ h → μ ≠ 0 → sh σ = l → ∃ (t : ℂ_[l]) (D E M : ℕ) (a : ℕ → ℂ_[l]) (ρ : ℝ), t ≠ 0 ∧ M + h ≤ E ∧ (∀ k, k ≤ E → ‖a k‖ ≤ 1) ∧ ‖a (M + h)‖ = 1 ∧ ‖(l : ℂ_[l])‖ ≤ ρ ∧ ρ < 1 ∧ ‖(l : ℂ_[l])‖ * ρ ^ l ^ D = ‖(l : ℂ_[l])‖ ^ l ^ h ∧ ‖a M‖ * ρ ^ l ^ M = ‖(l : ℂ_[l])‖ ∧ (∀ k, M < k → k ≤ E → ‖a k‖ * ρ ^ l ^ k < ‖(l : ℂ_[l])‖) ∧ ∀ u : Fl l, ‖∑ i : Fin h, μ i * lam h i (σ * u ^ l ^ D) - t * ∑ k ∈ Finset.range (E + 1), a k * sh u ^ l ^ k‖ ≤ ‖(l : ℂ_[l])‖ * ‖t‖ := by
  first | exact @GlobalTheory.PolyRoot.poly_root_mod_l | exact GlobalTheory.PolyRoot.poly_root_mod_l | (intros; apply GlobalTheory.PolyRoot.poly_root_mod_l <;> assumption)
end
end
