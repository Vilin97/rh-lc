module

public import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SummablePeriodicMulInvSubInvFloorStatement
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.Lemma
public import Mathlib.Analysis.Complex.IntegerCompl
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TendstoSumIccPeriodicMulInvFloorDivStatement
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Order.Interval.Finset.Box

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumPeriodicCotEqQExpansionFourier

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.CotQExp

theorem hasSum_pi_cot (w : ℂ) (hw : 0 < w.im) :
    HasSum (fun m : ℕ => -2 * π * Complex.I * cexp (2 * π * Complex.I * w) ^ (m + 1))
      (π * Complex.cot (π * w) + π * Complex.I) := by
  have h : (π : ℂ) * Complex.cot (π * w) =
      π * Complex.I - 2 * π * Complex.I * ∑' n : ℕ, cexp (2 * π * Complex.I * w) ^ n :=
    pi_mul_cot_pi_q_exp (⟨w, hw⟩ : ℍ)
  have hq : ‖cexp (2 * π * Complex.I * w)‖ < 1 :=
    UpperHalfPlane.norm_exp_two_pi_I_lt_one (⟨w, hw⟩ : ℍ)
  have hs : Summable fun n : ℕ => cexp (2 * π * Complex.I * w) ^ n :=
    summable_geometric_of_norm_lt_one hq
  have hs1 : Summable fun n : ℕ => cexp (2 * π * Complex.I * w) ^ (n + 1) :=
    (summable_nat_add_iff 1).2 hs
  have h2 := hs1.hasSum.mul_left (-2 * π * Complex.I)
  have e : (π : ℂ) * Complex.cot (π * w) + π * Complex.I =
      -2 * π * Complex.I * ∑' n : ℕ, cexp (2 * π * Complex.I * w) ^ (n + 1) := by
    rw [h, hs.tsum_eq_zero_add]
    ring
  rw [e]
  exact h2

theorem sum_cot_eq_qexp : ∀ (L : ℕ) (φ : ZMod L → ℂ) (z : ℂ), 0 < L → 0 < z.im → hat φ 0 = 0 →
    ∑ r ∈ Finset.range L, φ r * (π / L * Complex.cot (π * ((z + r) / L))) =
      -2 * π * Complex.I / L *
        ∑' m : ℕ, hat φ (m + 1 : ℕ) * cexp (2 * π * Complex.I * (m + 1 : ℕ) * z / L) := by
  intro L φ z hL hz h0
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hsum0 : ∑ r ∈ Finset.range L, φ r = 0 := by
    simpa [hat] using h0
  have him : ∀ r : ℕ, 0 < ((z + r) / L : ℂ).im := by
    intro r
    rw [Complex.div_natCast_im]
    simpa using div_pos hz hLr
  have hs := hasSum_sum (s := Finset.range L)
    (fun r _ => (hasSum_pi_cot _ (him r)).mul_left (φ r / L))
  rw [← tsum_mul_left]
  have e1 : ∑ r ∈ Finset.range L, φ r * (π / L * Complex.cot (π * ((z + r) / L))) =
      ∑ r ∈ Finset.range L, φ r / L * (π * Complex.cot (π * ((z + r) / L)) + π * Complex.I) := by
    have : ∑ r ∈ Finset.range L, φ r / L * (π * Complex.cot (π * ((z + r) / L)) + π * Complex.I)
        = ∑ r ∈ Finset.range L, φ r * (π / L * Complex.cot (π * ((z + r) / L)))
          + (∑ r ∈ Finset.range L, φ r) * (π * Complex.I / L) := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      ring
    rw [this, hsum0, zero_mul, add_zero]
  rw [e1, ← hs.tsum_eq]
  refine tsum_congr fun m => ?_
  rw [hat, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← Complex.exp_nat_mul, mul_assoc (φ r), ← Complex.exp_add]
  have e2 : ((m + 1 : ℕ) : ℂ) * (2 * π * Complex.I * ((z + r) / L)) =
      2 * π * Complex.I * (r * (((m + 1 : ℕ) : ℤ) : ℂ)) / L
        + 2 * π * Complex.I * (m + 1 : ℕ) * z / L := by
    push_cast
    ring
  rw [e2]
  ring

end GlobalTheory.CotQExp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumPeriodicCotEqQExpansionFourierStatement

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.sum_periodic_cot_eq_qExpansion_fourier : ∀ (L : ℕ) (φ : ZMod L → ℂ) (z : ℂ), 0 < L → 0 < z.im → hat φ 0 = 0 → ∑ r ∈ Finset.range L, φ r * (π / L * Complex.cot (π * ((z + r) / L))) = -2 * π * Complex.I / L * ∑' m : ℕ, hat φ (m + 1 : ℕ) * cexp (2 * π * Complex.I * (m + 1 : ℕ) * z / L) := by
  first | exact @GlobalTheory.CotQExp.sum_cot_eq_qexp | exact GlobalTheory.CotQExp.sum_cot_eq_qexp | (intros; apply GlobalTheory.CotQExp.sum_cot_eq_qexp <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.TendstoSumIccInvResidueCot

section

@[expose] public section

open Complex Filter Topology
open scoped Real

namespace GlobalTheory

lemma sum_Icc_inv_add_eq_cotTerm (w : ℂ) (N : ℕ) :
    ∑ n ∈ Finset.Icc (-(N:ℤ)) N, (w + n)⁻¹ =
      1 / w + ∑ j ∈ Finset.range N, (1 / (w - (j + 1)) + 1 / (w + (j + 1))) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have h : Finset.Icc (-((N + 1 : ℕ) : ℤ)) ((N + 1 : ℕ) : ℤ) =
        insert (-((N:ℤ) + 1)) (insert ((N:ℤ) + 1) (Finset.Icc (-(N:ℤ)) N)) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      push_cast
      omega
    rw [h, Finset.sum_insert, Finset.sum_insert, ih, Finset.sum_range_succ]
    · push_cast
      simp only [one_div, sub_eq_add_neg]
      ring
    · simp only [Finset.mem_Icc]; omega
    · simp only [Finset.mem_Icc, Finset.mem_insert]; omega

theorem tendsto_sum_Icc_inv_residue_cot :
    ∀ (L : ℕ) (z : ℂ) (r : ℕ), 0 < L → 0 < z.im →
      Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N:ℤ)) N, (z + r + n * L)⁻¹) atTop
        (𝓝 (π / L * Complex.cot (π * ((z + r) / L)))) := by
  intro L z r hL hz
  have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  set w : ℂ := (z + r) / L with hw
  have hwL : z + r = w * L := by rw [hw]; field_simp
  have hmem : w ∈ Complex.integerComplement := by
    rintro ⟨k, hk⟩
    have := congrArg Complex.im hwL
    rw [← hk] at this
    simp at this
    linarith
  have h1 := ((tendsto_logDeriv_euler_cot_sub hmem).const_add (1 / w)).const_mul (L : ℂ)⁻¹
  have hlim : (L : ℂ)⁻¹ * (1 / w + (π * Complex.cot (π * w) - 1 / w)) =
      π / L * Complex.cot (π * w) := by ring
  rw [hlim] at h1
  refine h1.congr fun N => ?_
  have := sum_Icc_inv_add_eq_cotTerm w N
  simp only [cotTerm]
  rw [← this, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [hwL, ← add_mul, mul_inv, mul_comm]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.TendstoSumIccInvResidueCotStatement

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.tendsto_sum_Icc_inv_add_mul_eq_pi_div_mul_cot : ∀ (L : ℕ) (z : ℂ) (r : ℕ), 0 < L → 0 < z.im → Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N:ℤ)) N, (z + r + n * L)⁻¹) atTop (𝓝 (π / L * Complex.cot (π * ((z + r) / L)))) := by
  first | exact @GlobalTheory.tendsto_sum_Icc_inv_residue_cot | exact GlobalTheory.tendsto_sum_Icc_inv_residue_cot | (intros; apply GlobalTheory.tendsto_sum_Icc_inv_residue_cot <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.LipschitzWeightOnePeriodicMeanZero

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM.LipOne

theorem block (L : ℕ) (f : ℤ → ℂ) (N : ℕ) :
    ∑ d ∈ Finset.Ico (-(N * L : ℤ)) ((N + 1) * L), f d =
      ∑ r ∈ Finset.range L, ∑ n ∈ Finset.Icc (-(N:ℤ)) N, f (r + n * L) := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · simp
  rw [← Finset.sum_product']
  have hL' : (0:ℤ) < L := by exact_mod_cast hL
  refine Finset.sum_nbij' (fun d => ((d % L).toNat, d / L)) (fun p => (p.1 : ℤ) + p.2 * L) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    simp only [Finset.mem_coe, Finset.mem_Ico] at hd
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range, Finset.mem_Icc]
    have h1 := Int.emod_nonneg d hL'.ne'
    have h2 := Int.emod_lt_of_pos d hL'
    have h3 := Int.emod_add_mul_ediv d L
    refine ⟨by omega, ?_, ?_⟩
    · by_contra h
      push_neg at h
      have : (L:ℤ) * (d / L) ≤ L * (-(N:ℤ) - 1) := by
        apply mul_le_mul_of_nonneg_left (by omega) hL'.le
      nlinarith
    · by_contra h
      push_neg at h
      have : (L:ℤ) * (N + 1) ≤ L * (d / L) := by
        apply mul_le_mul_of_nonneg_left (by omega) hL'.le
      nlinarith
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range, Finset.mem_Icc] at hp
    simp only [Finset.mem_coe, Finset.mem_Ico]
    obtain ⟨h1, h2, h3⟩ := hp
    have h1' : (p.1 : ℤ) < L := by exact_mod_cast h1
    have h0 : (0:ℤ) ≤ p.1 := by positivity
    constructor <;> nlinarith
  · intro d hd
    simp only
    have h1 := Int.emod_nonneg d hL'.ne'
    rw [Int.toNat_of_nonneg h1]
    have := Int.emod_add_mul_ediv d L
    linarith
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range] at hp
    have h1' : (p.1 : ℤ) < L := by exact_mod_cast hp.1
    ext
    · simp only
      rw [Int.add_mul_emod_self_right, Int.emod_eq_of_lt (by positivity) h1']
      simp
    · simp only
      rw [Int.add_mul_ediv_right _ _ hL'.ne', Int.ediv_eq_zero_of_lt (by positivity) h1']
      simp
  · intro d hd
    simp only
    congr 1
    have h1 := Int.emod_nonneg d hL'.ne'
    rw [Int.toNat_of_nonneg h1]
    have := Int.emod_add_mul_ediv d L
    linarith

theorem lipschitz_one : ∀ (L : ℕ) (φ : ZMod L → ℂ) (z : ℂ), 0 < L → 0 < z.im → hat φ 0 = 0 → Tendsto (fun R : ℕ => ∑ d ∈ Finset.Icc (-(R : ℤ)) R, φ (d : ZMod L) * trm 1 0 (z + d)) atTop (𝓝 (-2 * π * Complex.I / L * ∑' m : ℕ, hat φ (m + 1 : ℕ) * cexp (2 * π * Complex.I * (m + 1 : ℕ) * z / L))) := by
  intro L φ z hL hz h0
  have hLz : (L:ℤ) ≠ 0 := by exact_mod_cast hL.ne'
  have htrm : ∀ w : ℂ, trm 1 0 w = w⁻¹ := by
    intro w
    simp [trm]
  simp only [htrm]
  have hsum0 : ∑ r ∈ Finset.range L, φ r = 0 := by simpa [hat] using h0
  set g : ℤ → ℂ := fun d => φ d * ((z + d)⁻¹ - (z + ((L:ℤ) * (d / L) : ℤ))⁻¹) with hg
  have hs : Summable g := T.summable_periodic_mul_inv_sub_inv_floor' L φ z hL hz
  have hsplit : ∀ s : Finset ℤ, ∑ d ∈ s, φ d * (z + d)⁻¹ =
      ∑ d ∈ s, g d + ∑ d ∈ s, φ d * (z + ((L:ℤ) * (d / L) : ℤ))⁻¹ := by
    intro s
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [hg]
    ring
  have hmonoF : Monotone (fun R : ℕ => Finset.Icc (-(R:ℤ)) R) := by
    intro a b hab
    have : (a:ℤ) ≤ b := by exact_mod_cast hab
    exact Finset.Icc_subset_Icc (by omega) (by omega)
  have hcovF : ∀ d : ℤ, ∃ R : ℕ, d ∈ Finset.Icc (-(R:ℤ)) R := by
    intro d
    exact ⟨d.natAbs, by simp only [Finset.mem_Icc]; omega⟩
  have hmonoG : Monotone (fun N : ℕ => Finset.Ico (-(N * L : ℤ)) ((N + 1) * L)) := by
    intro a b hab
    have : (a:ℤ) ≤ b := by exact_mod_cast hab
    have hL0 : (0:ℤ) ≤ L := by positivity
    exact Finset.Ico_subset_Ico (by nlinarith) (by nlinarith)
  have hcovG : ∀ d : ℤ, ∃ N : ℕ, d ∈ Finset.Ico (-(N * L : ℤ)) ((N + 1) * L) := by
    intro d
    refine ⟨d.natAbs, ?_⟩
    have h1 : (1:ℤ) ≤ L := by exact_mod_cast hL
    have h3 : (d.natAbs : ℤ) = |d| := Int.natCast_natAbs d
    have h4 : (0:ℤ) ≤ |d| := abs_nonneg d
    simp only [Finset.mem_Ico]
    rw [h3]
    constructor
    · nlinarith [neg_abs_le d]
    · nlinarith [le_abs_self d]
  have hF := Filter.Tendsto.comp hs.hasSum (Filter.tendsto_atTop_finset_of_monotone hmonoF hcovF)
  have hG := Filter.Tendsto.comp hs.hasSum (Filter.tendsto_atTop_finset_of_monotone hmonoG hcovG)
  have hzero : ∀ N : ℕ, ∑ d ∈ Finset.Ico (-(N * L : ℤ)) ((N + 1) * L),
      φ d * (z + ((L:ℤ) * (d / L) : ℤ))⁻¹ = 0 := by
    intro N
    rw [block L (fun d : ℤ => φ d * (z + ((L:ℤ) * (d / L) : ℤ))⁻¹) N]
    calc _ = ∑ r ∈ Finset.range L, φ r * ∑ n ∈ Finset.Icc (-(N:ℤ)) N, (z + ((L:ℤ) * n : ℤ))⁻¹ := by
          refine Finset.sum_congr rfl fun r hr => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun n _ => ?_
          have hr' : (r:ℤ) < L := by exact_mod_cast Finset.mem_range.mp hr
          rw [Int.add_mul_ediv_right _ _ hLz, Int.ediv_eq_zero_of_lt (by positivity) hr', zero_add]
          congr 1
          push_cast
          simp [ZMod.natCast_self]
      _ = 0 := by rw [← Finset.sum_mul, hsum0, zero_mul]
  have hb : ∀ N : ℕ, ∑ d ∈ Finset.Ico (-(N * L : ℤ)) ((N + 1) * L), φ d * (z + d)⁻¹ =
      ∑ r ∈ Finset.range L, φ r * ∑ n ∈ Finset.Icc (-(N:ℤ)) N, (z + r + n * L)⁻¹ := by
    intro N
    rw [block L (fun d : ℤ => φ d * (z + d)⁻¹) N]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    push_cast
    simp only [ZMod.natCast_self, mul_zero, add_zero]
    ring_nf
  have hmain := tendsto_finsetSum (Finset.range L)
    fun r (_ : r ∈ Finset.range L) => (T.tendsto_sum_Icc_inv_add_mul_eq_pi_div_mul_cot L z r hL hz).const_mul (φ r)
  rw [T.sum_periodic_cot_eq_qExpansion_fourier L φ z hL hz h0] at hmain
  have hT : ∑' d, g d = -2 * ↑π * Complex.I / ↑L * ∑' (m : ℕ), hat φ ↑(m + 1) *
      cexp (2 * ↑π * Complex.I * ↑(m + 1) * z / ↑L) := by
    refine tendsto_nhds_unique ?_ hmain
    refine hG.congr fun N => ?_
    simp only [Function.comp_apply]
    rw [← hb N, hsplit, hzero N, add_zero]
  have hlim := hF.add (T.tendsto_sum_Icc_periodic_mul_inv_floor_div L φ z hL hz h0)
  rw [add_zero, hT] at hlim
  refine hlim.congr fun R => ?_
  simp only [Function.comp_apply]
  rw [hsplit]

end GlobalTheory.EisM.LipOne
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.LipschitzWeightOnePeriodicMeanZeroStatement

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.lipschitz_weight_one_periodic_mean_zero : ∀ (L : ℕ) (φ : ZMod L → ℂ) (z : ℂ), 0 < L → 0 < z.im → hat φ 0 = 0 → Tendsto (fun R : ℕ => ∑ d ∈ Finset.Icc (-(R : ℤ)) R, φ (d : ZMod L) * trm 1 0 (z + d)) atTop (𝓝 (-2 * π * Complex.I / L * ∑' m : ℕ, hat φ (m + 1 : ℕ) * cexp (2 * π * Complex.I * (m + 1 : ℕ) * z / L))) := by
  first | exact @GlobalTheory.EisM.LipOne.lipschitz_one | exact GlobalTheory.EisM.LipOne.lipschitz_one | (intros; apply GlobalTheory.EisM.LipOne.lipschitz_one <;> assumption)
end
end
