module

public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CardFilterLeSuccAndSqSumLePow
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CloudNodeProjectionNormLowLevel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CardFilterFinBounds
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitCasimirOffDiagonalNormSqLeOfLevelStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightNearDiagonalOperatorsBounds
import Mathlib.Algebra.Order.Star.Real
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitCasEigenvalueSummand
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGlModuleProjComponentsLevelAddTwoStatement
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.CloudNodeProjectionNormLowLevelStatement

section

@[expose] public section

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.cloudNode_projection_norm_lowLevel : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ) (w : M), IsMod ε E μ → (∀ s, IsMod ε (F s) (μ - Pi.single s 1)) → AlgTens ε E N F io pr → Shape ε kk μ bv → j ≤ 4 * n ^ 2 → Lev ε E μ j w → ∀ c, ∑ d, ‖(∑ s ∈ univ.filter (fun a : Fin n => a.val + 1 < kk), io s (pr s (Pi.single c w))) d‖ ^ 2 ≤ (18 / 13) ^ 2 * ‖w‖ ^ 2 ∧ ∀ s : Fin n, kk ≤ s.val + 1 → ∑ d, ‖io s (pr s (Pi.single c w)) d‖ ^ 2 ≤ (3 * (6 * bv) ^ (n - kk)) ^ 2 * ‖w‖ ^ 2 := by
  first | exact @GlobalTheory.cloud_node_projection_norm | exact GlobalTheory.cloud_node_projection_norm | (intros; apply GlobalTheory.cloud_node_projection_norm <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.InvariantHermitianFormNonnegOfCloudEigen

section

@[expose] public section

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem hhJ_nonneg_of_cloud_eigen : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ) (x : Fin n → M), IsMod ε E μ → Shape ε kk μ bv → j ≤ 4 * n ^ 2 + 2 → (∀ c, Lev ε E μ j (x c)) → ∀ s : Fin n, s.val + 1 < kk → splitCas E x = ((-μ s + (1 - (n : ℝ)) / 2 : ℝ) : ℂ) • x → 0 ≤ (hhJ ε x x).re := by
  intro M _ _ n ε E μ kk j bv x hM hS hj hL s hs hx
  obtain ⟨hb, hω, hζ⟩ := GlobalTheory.shape_position n kk j ε μ bv hS hj
  have hO := GlobalTheory.T.splitCasimir_offDiagonal_norm_sq_le_of_level M n ε E μ kk j bv x hM hS hj hL
  set ζ : ℝ := -μ s + (1 - (n : ℝ)) / 2 with hζdef
  have hζs : ζ ≤ bv / 32 := ((hζ s).1 hs).2
  have hnode : ∀ c : Fin n, kk ≤ c.val + 1 →
      (15 * bv / 16) ^ 2 * ‖x c‖ ^ 2 ≤ ‖∑ a ∈ univ.erase c, E c a (x a)‖ ^ 2 := by
    intro c hc
    have h1 := (GlobalTheory.wtNear_diag_bounds M n ε E (lowK ε μ) (j : ℝ) (x c) hM.2.1 (hL c).2).2.1 c (ζ : ℂ)
      (15 * bv / 16) (by positivity) (by
        intro ω hw
        have h2 := ((hω ω hw c).2 hc).1
        rw [← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs]
        have := neg_abs_le (ζ + ω c)
        linarith)
    have h3 := congrFun hx c
    simp only [splitCas, Pi.smul_apply] at h3
    rw [← Finset.add_sum_erase univ (fun a => E c a (x a)) (mem_univ c)] at h3
    have h4 : (ζ : ℂ) • x c + E c c (x c) = -∑ a ∈ univ.erase c, E c a (x a) := by
      rw [← h3]; abel
    rw [h4, norm_neg] at h1
    exact h1
  have hterm : ∀ c : Fin n, (15 * bv / 16) ^ 2 * ‖x c‖ ^ 2 - 2 * ‖∑ a ∈ univ.erase c, E c a (x a)‖ ^ 2 ≤
      (15 * bv / 16) ^ 2 * ((if ε c then 1 else -1) * ⟪x c, x c⟫_ℂ : ℂ).re := by
    intro c
    have hin : (⟪x c, x c⟫_ℂ : ℂ).re = ‖x c‖ ^ 2 := by
      simpa using inner_self_eq_norm_sq (𝕜 := ℂ) (x c)
    by_cases he : ε c = true
    · rw [if_pos he, one_mul, hin]
      have := sq_nonneg ‖∑ a ∈ univ.erase c, E c a (x a)‖
      linarith
    · have hc : kk ≤ c.val + 1 := by
        by_contra h
        exact he (hS.2.2.2.1 c (not_le.mp h)).1
      rw [if_neg he, neg_one_mul, Complex.neg_re, hin]
      have := hnode c hc
      linarith
  have hsum := Finset.sum_le_sum (fun c (_ : c ∈ (univ : Finset (Fin n))) => hterm c)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Complex.re_sum] at hsum
  have hS0 : 0 ≤ ∑ c, ‖x c‖ ^ 2 := Finset.sum_nonneg fun c _ => sq_nonneg _
  have hpos : 0 < (15 * bv / 16) ^ 2 := by positivity
  have hkey : 0 ≤ (15 * bv / 16) ^ 2 * (hhJ ε x x).re := by
    unfold hhJ
    have : 0 ≤ bv ^ 2 * ∑ c, ‖x c‖ ^ 2 := mul_nonneg (sq_nonneg _) hS0
    nlinarith
  exact (mul_nonneg_iff_of_pos_left hpos).mp hkey

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.InvariantHermitianFormNonnegOfCloudEigenStatement

section

@[expose] public section

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.invariantHermitianForm_nonneg_of_cloud_eigen : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ) (x : Fin n → M), IsMod ε E μ → Shape ε kk μ bv → j ≤ 4 * n ^ 2 + 2 → (∀ c, Lev ε E μ j (x c)) → ∀ s : Fin n, s.val + 1 < kk → splitCas E x = ((-μ s + (1 - (n : ℝ)) / 2 : ℝ) : ℂ) • x → 0 ≤ (hhJ ε x x).re := by
  first | exact @GlobalTheory.hhJ_nonneg_of_cloud_eigen | exact GlobalTheory.hhJ_nonneg_of_cloud_eigen | (intros; apply GlobalTheory.hhJ_nonneg_of_cloud_eigen <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumNormHhJSelfLe

section

@[expose] public section

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

section
variable {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {n : ℕ}

lemma hhJ_self_norm_le_sum_sq (ε : Fin n → Bool) (x : Fin n → M) :
    ‖hhJ ε x x‖ ≤ ∑ c, ‖x c‖ ^ 2 := by
  unfold hhJ
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  rw [norm_mul, inner_self_eq_norm_sq_to_K]
  split_ifs <;> simp

lemma hhJ_self_im_eq_zero (ε : Fin n → Bool) (x : Fin n → M) :
    (hhJ ε x x).im = 0 := by
  unfold hhJ
  rw [Complex.im_sum]
  refine Finset.sum_eq_zero fun c _ => ?_
  have h : (⟪x c, x c⟫_ℂ).im = 0 := inner_self_im (𝕜 := ℂ) (x c)
  split_ifs <;> simp [-inner_self_eq_norm_sq_to_K, h]

lemma hhJ_finsum_finsum {ι : Type} (ε : Fin n → Bool) (y : ι → Fin n → M) (In : Finset ι) :
    hhJ ε (∑ s ∈ In, y s) (∑ s ∈ In, y s) = ∑ s ∈ In, ∑ t ∈ In, hhJ ε (y s) (y t) := by
  unfold hhJ
  simp only [Finset.sum_apply, sum_inner, inner_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_comm]

end

theorem sum_norm_hhJ_self_le : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (y : Fin n → Fin n → M) (In : Finset (Fin n)) (Cc Cs Nn : ℝ), (∀ s t, s ≠ t → hhJ ε (y s) (y t) = 0) → (∀ s ∈ In, 0 ≤ (hhJ ε (y s) (y s)).re) → ∑ c, ‖(∑ s ∈ In, y s) c‖ ^ 2 ≤ Cc ^ 2 * Nn → (∀ s, s ∉ In → ∑ c, ‖y s c‖ ^ 2 ≤ Cs ^ 2 * Nn) → ∑ s, ‖hhJ ε (y s) (y s)‖ ≤ (Cc ^ 2 + (Inᶜ.card : ℝ) * Cs ^ 2) * Nn := by
  intro M _ _ n ε y In Cc Cs Nn horth hpos hIn hout
  rw [← Finset.sum_add_sum_compl In]
  have h1 : hhJ ε (∑ s ∈ In, y s) (∑ s ∈ In, y s) = ∑ s ∈ In, hhJ ε (y s) (y s) := by
    rw [hhJ_finsum_finsum]
    refine Finset.sum_congr rfl fun s hs => ?_
    exact Finset.sum_eq_single_of_mem s hs fun t _ hts => horth s t (Ne.symm hts)
  have h2 : ∑ s ∈ In, ‖hhJ ε (y s) (y s)‖ = (∑ s ∈ In, hhJ ε (y s) (y s)).re := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [← Complex.abs_re_eq_norm.mpr (hhJ_self_im_eq_zero ε (y s)), abs_of_nonneg (hpos s hs)]
  have h3 : ∑ s ∈ In, ‖hhJ ε (y s) (y s)‖ ≤ Cc ^ 2 * Nn := by
    rw [h2, ← h1]
    exact (Complex.re_le_norm _).trans ((hhJ_self_norm_le_sum_sq ε _).trans hIn)
  have h4 : ∑ s ∈ Inᶜ, ‖hhJ ε (y s) (y s)‖ ≤ (Inᶜ.card : ℝ) * (Cs ^ 2 * Nn) := by
    rw [← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun s hs => ?_
    exact (hhJ_self_norm_le_sum_sq ε _).trans (hout s (Finset.mem_compl.mp hs))
  calc _ ≤ Cc ^ 2 * Nn + (Inᶜ.card : ℝ) * (Cs ^ 2 * Nn) := add_le_add h3 h4
    _ = _ := by ring

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumNormHhJSelfLeStatement

section

@[expose] public section

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.sum_norm_hhJ_self_le_of_orthogonal : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (y : Fin n → Fin n → M) (In : Finset (Fin n)) (Cc Cs Nn : ℝ), (∀ s t, s ≠ t → hhJ ε (y s) (y t) = 0) → (∀ s ∈ In, 0 ≤ (hhJ ε (y s) (y s)).re) → ∑ c, ‖(∑ s ∈ In, y s) c‖ ^ 2 ≤ Cc ^ 2 * Nn → (∀ s, s ∉ In → ∑ c, ‖y s c‖ ^ 2 ≤ Cs ^ 2 * Nn) → ∑ s, ‖hhJ ε (y s) (y s)‖ ≤ (Cc ^ 2 + (Inᶜ.card : ℝ) * Cs ^ 2) * Nn := by
  first | exact @GlobalTheory.sum_norm_hhJ_self_le | exact GlobalTheory.sum_norm_hhJ_self_le | (intros; apply GlobalTheory.sum_norm_hhJ_self_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumNormSqProjectionsTensorUnitaryGlLe

section

@[expose] public section

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem sum_normSq_proj_single_le : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ) (w : M), IsMod ε E μ → (∀ s, IsMod ε (F s) (μ - Pi.single s 1)) → AlgTens ε E N F io pr → Shape ε kk μ bv → j ≤ 4 * n ^ 2 → Lev ε E μ j w → ∀ c, ∑ s, ‖pr s (Pi.single c w)‖ ^ 2 ≤ (6 * bv) ^ (2 * (n + 1 - kk)) * ‖w‖ ^ 2 := by
  intro M _ _ n ε E N _ _ F io pr μ kk j bv w hE hF hA hS hj hw c
  have hnorm : ∀ s, ‖pr s (Pi.single c w)‖ ^ 2 =
      ‖hhJ ε (io s (pr s (Pi.single c w))) (io s (pr s (Pi.single c w)))‖ := by
    intro s
    obtain ⟨e, he, hs⟩ := hA.sign s
    rw [hs, norm_mul, inner_self_eq_norm_sq_to_K]
    rcases he with rfl | rfl <;> simp
  have hcomp := GlobalTheory.T.unitary_glModule_proj_components_level_add_two M n ε E N F io pr μ j w hE.2.1 (fun s => (hF s).2.1) hA hw
  have hproj := GlobalTheory.T.cloudNode_projection_norm_lowLevel M n ε E N F io pr μ kk j bv w hE hF hA hS hj hw c
  have hq := GlobalTheory.T.sum_norm_hhJ_self_le_of_orthogonal M n ε (fun s => io s (pr s (Pi.single c w)))
    (univ.filter (fun a : Fin n => a.val + 1 < kk)) (18 / 13) (3 * (6 * bv) ^ (n - kk)) (‖w‖ ^ 2)
    (fun s t hst => hA.orth s t hst _ _)
    (fun s hs => GlobalTheory.T.invariantHermitianForm_nonneg_of_cloud_eigen M n ε E μ kk (j + 2) bv _ hE hS (by omega) (fun d => hcomp s c d) s
      (Finset.mem_filter.1 hs).2 (GlobalTheory.splitCas_eigenvalue_summand M n ε E N F io pr μ hE hF hA s _))
    hproj.1
    (fun s hs => hproj.2 s (by simpa using hs))
  obtain ⟨h1, h2, -, -, -, hb⟩ := hS
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hnb : (n : ℝ) ≤ bv := by
    have h7 : (n : ℝ) ≤ (n : ℝ) ^ 7 := le_self_pow₀ hn1 (by norm_num)
    have : (0 : ℝ) ≤ (n : ℝ) ^ 7 := by positivity
    nlinarith
  obtain ⟨hcard, harith⟩ := GlobalTheory.card_filter_le_succ_and_sq_sum_le_pow n kk bv h1 h2 hnb
  have hcompl : (univ.filter (fun a : Fin n => a.val + 1 < kk))ᶜ =
      univ.filter (fun a : Fin n => kk ≤ a.val + 1) := by
    ext a; simp
  rw [hcompl, hcard] at hq
  rw [Finset.sum_congr rfl (fun s _ => hnorm s)]
  exact hq.trans (mul_le_mul_of_nonneg_right harith (by positivity))

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumNormSqProjectionsTensorUnitaryGlLeStatement

section

@[expose] public section

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.sum_normSq_projections_tensor_unitary_gl_le : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ) (w : M), IsMod ε E μ → (∀ s, IsMod ε (F s) (μ - Pi.single s 1)) → AlgTens ε E N F io pr → Shape ε kk μ bv → j ≤ 4 * n ^ 2 → Lev ε E μ j w → ∀ c, ∑ s, ‖pr s (Pi.single c w)‖ ^ 2 ≤ (6 * bv) ^ (2 * (n + 1 - kk)) * ‖w‖ ^ 2 := by
  first | exact @GlobalTheory.sum_normSq_proj_single_le | exact GlobalTheory.sum_normSq_proj_single_le | (intros; apply GlobalTheory.sum_normSq_proj_single_le <;> assumption)
end
end
