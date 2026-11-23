module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHSt
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHLocalA
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LRight
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LSeries.Nonvanishing
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
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MeanSquareHypWIff
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHLocalA
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LGrowth
import Mathlib.NumberTheory.LSeries.Nonvanishing

-- Source module: Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHLocalB

section

@[expose] public section

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

lemma dhl_geom (t : ℝ) (z : ℂ) (hz : ‖z - ((26 / 25 : ℂ) + t * I)‖ ≤ 12 / 25) :
    1 / 2 ≤ z.re ∧ 1 + ‖z‖ ≤ 2 * (|t| + 2) := by
  have hre : ((26 / 25 : ℂ) + t * I).re = 26 / 25 := by
    simp
  have h1 := abs_re_le_norm (z - ((26 / 25 : ℂ) + t * I))
  rw [sub_re, hre] at h1
  have hn : ‖((26 / 25 : ℂ) + t * I)‖ ≤ 26 / 25 + |t| := by
    calc ‖((26 / 25 : ℂ) + t * I)‖ ≤ ‖(26 / 25 : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
      _ = 26 / 25 + |t| := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
        norm_num
  refine ⟨?_, ?_⟩
  · have := (abs_le.mp (h1.trans hz)).1; linarith
  · have := norm_sub_norm_le z ((26 / 25 : ℂ) + t * I)
    linarith [abs_nonneg t]

lemma dhl_core (hCau : DHCauchy) (f : ℂ → ℂ) (t K X : ℝ) (hK : 1 ≤ K) (hX : 3 ≤ X)
    (hf : Differentiable ℂ f) (hf0 : f ((26 / 25 : ℂ) + t * I) ≠ 0)
    (hB : ∀ z, ‖z - ((26 / 25 : ℂ) + t * I)‖ ≤ 12 / 25 →
      ‖f z‖ ≤ K * X ^ 2 * ‖f ((26 / 25 : ℂ) + t * I)‖) :
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ : ℂ, ρ ∈ Z ↔ (‖ρ - ((26 / 25 : ℂ) + t * I)‖ ≤ 4 / 25 ∧ f ρ = 0)) ∧
      (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
      ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ 150 * (Real.log K + 2) * Real.log X ∧
      ∀ (k : ℕ) (s : ℂ), ‖s - ((26 / 25 : ℂ) + t * I)‖ ≤ 1 / 25 → f s ≠ 0 →
        ‖(-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k (fun z => -(deriv f z / f z)) s
            + ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1)‖ ≤
          150 * (Real.log K + 2) * Real.log X * 25 ^ k := by
  have hB1 : 1 ≤ K * X ^ 2 := by nlinarith
  obtain ⟨Z, m, hZ, hm, hsum, hexp⟩ := hCau f ((26 / 25 : ℂ) + t * I) (12 / 25) (K * X ^ 2)
    (by norm_num) hB1 hf.differentiableOn hf0
    (fun z hz => hB z (by rwa [Metric.mem_closedBall, dist_eq] at hz))
  have hlog := dhl_log K X hK hX
  have hlog0 : 0 ≤ Real.log (K * X ^ 2) := Real.log_nonneg hB1
  refine ⟨Z, m, ?_, hm, ?_, ?_⟩
  · intro ρ
    rw [hZ ρ, Metric.mem_closedBall, dist_eq]
    norm_num
  · refine hsum.trans ?_
    have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  · intro k s hs hfs
    have := hexp k s (by rw [Metric.mem_closedBall, dist_eq]; norm_num; linarith) hfs
    refine this.trans ?_
    have e : (72 * Real.log (K * X ^ 2) / (12 / 25) * (12 / (12 / 25)) ^ k : ℝ)
        = 150 * Real.log (K * X ^ 2) * 25 ^ k := by
      norm_num; ring
    rw [e]
    have : (0 : ℝ) < 25 ^ k := by positivity
    nlinarith

lemma dhl_z0re (t : ℝ) : ((26 / 25 : ℂ) + t * I).re = 26 / 25 := by
  simp

lemma dhl_inv (M : ℕ) [NeZero M] (ψ : DirichletCharacter ℂ M) (t : ℝ) :
    1 ≤ 26 * ‖DirichletCharacter.LFunction ψ ((26 / 25 : ℂ) + t * I)‖ := by
  have h := inverseBound M ψ ((26 / 25 : ℂ) + t * I) (by rw [dhl_z0re]; norm_num)
  rw [dhl_z0re] at h
  have hne : DirichletCharacter.LFunction ψ ((26 / 25 : ℂ) + t * I) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ
      (Or.inr (by intro h; have := congrArg Complex.re h; rw [dhl_z0re] at this; norm_num at this))
      (by rw [dhl_z0re]; norm_num)
  have hpos : 0 < ‖DirichletCharacter.LFunction ψ ((26 / 25 : ℂ) + t * I)‖ := norm_pos_iff.mpr hne
  rw [inv_le_comm₀ hpos (by norm_num)] at h
  norm_num at h
  linarith

def DHLocalAt (C : ℝ) (M : ℕ) [NeZero M] (ψ : DirichletCharacter ℂ M) (t : ℝ) : Prop :=
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ : ℂ, ρ ∈ Z ↔ (‖ρ - ((26 / 25 : ℂ) + t * I)‖ ≤ 4 / 25 ∧ IsLZero ψ ρ)) ∧
      (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
      (∀ ρ ∈ Z, ρ.re < 1) ∧
      ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ C * Real.log ((M : ℝ) * (|t| + 2)) ∧
      ∀ (k : ℕ) (s : ℂ), 1 < s.re → ‖s - ((26 / 25 : ℂ) + t * I)‖ ≤ 1 / 25 →
        ‖(-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k (negLD ψ) s
            - (if ψ = 1 then 1 / (s - 1) ^ (k + 1) else 0)
            + ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1)‖ ≤ C * Real.log ((M : ℝ) * (|t| + 2)) * 25 ^ k

lemma dhl_X (M : ℕ) (t : ℝ) (hM : 3 ≤ M) : 3 ≤ (M : ℝ) * (|t| + 2) := by
  have h3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  nlinarith [abs_nonneg t]

lemma dhl_nontriv (hCau : DHCauchy) (C0 K : ℝ)
    (hC0 : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ s : ℂ, 1 / 2 ≤ s.re →
      ‖DirichletCharacter.LFunction χ s‖ ≤ C0 * q * (1 + ‖s‖))
    (hK1 : 1 ≤ K) (hK : 52 * C0 ≤ K) (M : ℕ) [NeZero M] (ψ : DirichletCharacter ℂ M) (hψ : ψ ≠ 1)
    (t : ℝ) (hM : 3 ≤ M) : DHLocalAt (150 * (Real.log K + 2)) M ψ t := by
  have hX := dhl_X M t hM
  have h3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hinv := dhl_inv M ψ t
  have hf0 : DirichletCharacter.LFunction ψ ((26 / 25 : ℂ) + t * I) ≠ 0 := by
    intro h; rw [h, norm_zero] at hinv; norm_num at hinv
  obtain ⟨Z, m, hZ, hm, hsum, hexp⟩ := dhl_core hCau (DirichletCharacter.LFunction ψ) t K
    ((M : ℝ) * (|t| + 2)) hK1 hX (DirichletCharacter.differentiable_LFunction hψ) hf0 (by
      intro z hz
      obtain ⟨hre, hn⟩ := dhl_geom t z hz
      have h1 := hC0 M ψ hψ z hre
      have hz0 := norm_nonneg z
      have ht := abs_nonneg t
      calc ‖DirichletCharacter.LFunction ψ z‖ ≤ C0 * M * (1 + ‖z‖) := h1
        _ ≤ (K / 52) * M * (1 + ‖z‖) := by
            have : C0 ≤ K / 52 := by linarith
            gcongr
        _ ≤ (K / 52) * M * (2 * (|t| + 2)) := by gcongr
        _ = K * ((M : ℝ) * (|t| + 2)) * (1 / 26) := by ring
        _ ≤ K * ((M : ℝ) * (|t| + 2)) ^ 2 * ‖DirichletCharacter.LFunction ψ ((26 / 25 : ℂ) + t * I)‖ := by
            have hXX : (M : ℝ) * (|t| + 2) ≤ ((M : ℝ) * (|t| + 2)) ^ 2 := by nlinarith
            have : (1 / 26 : ℝ) ≤ ‖DirichletCharacter.LFunction ψ ((26 / 25 : ℂ) + t * I)‖ := by linarith
            gcongr)
  refine ⟨Z, m, ?_, hm, ?_, hsum, ?_⟩
  · intro ρ
    rw [hZ ρ]
    exact and_congr_right (fun _ => ⟨fun h => ⟨Or.inl hψ, h⟩, fun h => h.2⟩)
  · intro ρ hρ
    by_contra hcon
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ (Or.inl hψ) (not_lt.mp hcon)
      ((hZ ρ).mp hρ).2
  · intro k s hs1 hs
    have h := hexp k s hs (DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ (Or.inl hψ) hs1.le)
    rw [if_neg hψ, sub_zero]
    exact h

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end
end

-- Source module: Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHLocal

section

@[expose] public section

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

lemma dhl_ne_one {s : ℂ} (hs : 1 < s.re) : s ≠ 1 := by
  intro h
  rw [h, Complex.one_re] at hs
  exact lt_irrefl _ hs

lemma dhl_triv_ld (M : ℕ) [NeZero M] (z : ℂ) (hz : 1 < z.re) :
    -(deriv (DirichletCharacter.LFunctionTrivChar₁ M) z / DirichletCharacter.LFunctionTrivChar₁ M z)
      = negLD (1 : DirichletCharacter ℂ M) z - 1 / (z - 1) := by
  have hz1 : z ≠ 1 := dhl_ne_one hz
  have hf : ∀ w : ℂ, w ≠ 1 → DirichletCharacter.LFunctionTrivChar₁ M w =
      (w - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) w := by
    intro w hw
    simp [DirichletCharacter.LFunctionTrivChar₁, hw]
  have hev : DirichletCharacter.LFunctionTrivChar₁ M =ᶠ[nhds z]
      fun w => (w - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) w := by
    filter_upwards [eventually_ne_nhds hz1] with w hw
    exact hf w hw
  have hd := DirichletCharacter.differentiableAt_LFunction (1 : DirichletCharacter ℂ M) z (Or.inl hz1)
  have hL0 := DirichletCharacter.LFunction_ne_zero_of_one_le_re (1 : DirichletCharacter ℂ M)
    (Or.inr hz1) hz.le
  have hlin : DifferentiableAt ℂ (fun w : ℂ => w - 1) z := differentiableAt_id.sub_const 1
  have hder : deriv (DirichletCharacter.LFunctionTrivChar₁ M) z =
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) z +
        (z - 1) * deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M)) z := by
    rw [hev.deriv_eq, deriv_fun_mul hlin hd]
    simp
  rw [hder, hf z hz1]
  unfold negLD
  have hz1' : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  field_simp
  ring

lemma dhl_negLD_contDiffAt (M : ℕ) [NeZero M] (s : ℂ) (hs : 1 < s.re) (k : ℕ) :
    ContDiffAt ℂ k (negLD (1 : DirichletCharacter ℂ M)) s := by
  have hU : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hLd : DifferentiableOn ℂ (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M))
      {w : ℂ | 1 < w.re} := by
    intro w hw
    exact (DirichletCharacter.differentiableAt_LFunction _ w
      (Or.inl (dhl_ne_one hw))).differentiableWithinAt
  have hD : DifferentiableOn ℂ (negLD (1 : DirichletCharacter ℂ M)) {w : ℂ | 1 < w.re} := by
    unfold negLD
    refine ((hLd.deriv hU).div hLd ?_).neg
    intro w hw
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re _ (Or.inr (dhl_ne_one hw)) (le_of_lt hw)
  exact (hD.contDiffOn hU).contDiffAt (hU.mem_nhds hs)

lemma dhl_pole_contDiffAt (s : ℂ) (hs : s ≠ 1) (k : ℕ) :
    ContDiffAt ℂ k (fun z : ℂ => 1 / (z - 1)) s := by
  exact contDiffAt_const.div (contDiffAt_id.sub contDiffAt_const) (sub_ne_zero.mpr hs)

lemma dhl_triv_iter (M : ℕ) [NeZero M] (s : ℂ) (hs : 1 < s.re) (k : ℕ) :
    (-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k (fun z =>
      -(deriv (DirichletCharacter.LFunctionTrivChar₁ M) z / DirichletCharacter.LFunctionTrivChar₁ M z)) s
      = (-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k (negLD (1 : DirichletCharacter ℂ M)) s
        - 1 / (s - 1) ^ (k + 1) := by
  have hU : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : (fun z => -(deriv (DirichletCharacter.LFunctionTrivChar₁ M) z /
      DirichletCharacter.LFunctionTrivChar₁ M z)) =ᶠ[nhds s]
      (negLD (1 : DirichletCharacter ℂ M) - fun z : ℂ => 1 / (z - 1)) := by
    filter_upwards [hU.mem_nhds hs] with z hz
    rw [Pi.sub_apply]
    exact dhl_triv_ld M z hz
  rw [hev.iteratedDeriv_eq k, iteratedDeriv_sub (dhl_negLD_contDiffAt M s hs k)
    (dhl_pole_contDiffAt s (dhl_ne_one hs) k), mul_sub, dhl_pole k s (dhl_ne_one hs)]

lemma dhl_triv (hCau : DHCauchy) (K : ℝ) (hK : 10400 ≤ K) (M : ℕ) [NeZero M]
    (t : ℝ) (hM : 3 ≤ M) : DHLocalAt (150 * (Real.log K + 2)) M (1 : DirichletCharacter ℂ M) t := by
  have hX3 : 3 ≤ (M : ℝ) * (|t| + 2) := dhl_X M t hM
  have hK1 : 1 ≤ K := by linarith
  have hf : ∀ w : ℂ, w ≠ 1 → DirichletCharacter.LFunctionTrivChar₁ M w =
      (w - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) w := by
    intro w hw
    simp [DirichletCharacter.LFunctionTrivChar₁, hw]
  have hf1 : DirichletCharacter.LFunctionTrivChar₁ M 1 ≠ 0 := by
    simp only [DirichletCharacter.LFunctionTrivChar₁, Function.update_self]
    rw [Finset.prod_ne_zero_iff]
    intro p hp h
    have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
    have h1 : (p : ℂ)⁻¹ = 1 := (sub_eq_zero.mp h).symm
    have h2 : (p : ℂ) = 1 := inv_eq_one.mp h1
    have h3 : p = 1 := by exact_mod_cast h2
    omega
  have hz0re : ((26 / 25 : ℂ) + ↑t * I).re = 26 / 25 := dhl_z0re t
  have hz0ne : (26 / 25 : ℂ) + ↑t * I ≠ 1 := dhl_ne_one (by rw [hz0re]; norm_num)
  have hLz0 := dhl_inv M (1 : DirichletCharacter ℂ M) t
  have hnz0 : 1 / 650 ≤ ‖DirichletCharacter.LFunctionTrivChar₁ M ((26 / 25 : ℂ) + ↑t * I)‖ := by
    rw [hf _ hz0ne, norm_mul]
    have ha : 1 / 25 ≤ ‖(26 / 25 : ℂ) + ↑t * I - 1‖ := by
      have := Complex.re_le_norm ((26 / 25 : ℂ) + ↑t * I - 1)
      rw [Complex.sub_re, hz0re, Complex.one_re] at this
      linarith
    nlinarith [norm_nonneg (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) ((26 / 25 : ℂ) + ↑t * I))]
  have hfz0 : DirichletCharacter.LFunctionTrivChar₁ M ((26 / 25 : ℂ) + ↑t * I) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnz0
    norm_num at hnz0
  have hgrowth : ∀ z : ℂ, ‖z - ((26 / 25 : ℂ) + ↑t * I)‖ ≤ 12 / 25 →
      ‖DirichletCharacter.LFunctionTrivChar₁ M z‖ ≤
        K * ((M : ℝ) * (|t| + 2)) ^ 2 * ‖DirichletCharacter.LFunctionTrivChar₁ M ((26 / 25 : ℂ) + ↑t * I)‖ := by
    intro z hz
    obtain ⟨hre, hn⟩ := dhl_geom t z hz
    have h1 := dhl_triv_growth M z hre
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (by omega : 1 ≤ M)
    have h2 : ‖DirichletCharacter.LFunctionTrivChar₁ M z‖ ≤ 16 * M * (|t| + 2) ^ 2 := by
      have hsq : (1 + ‖z‖) ^ 2 ≤ (2 * (|t| + 2)) ^ 2 := by
        have : 0 ≤ 1 + ‖z‖ := by positivity
        gcongr
      have := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 4 * M)
      nlinarith
    have h3 : 16 * M * (|t| + 2) ^ 2 ≤ K * ((M : ℝ) * (|t| + 2)) ^ 2 * (1 / 650) := by
      have hKM : 10400 ≤ K * M := by nlinarith
      have hT : 0 ≤ (M : ℝ) * (|t| + 2) ^ 2 := by positivity
      have e : K * ((M : ℝ) * (|t| + 2)) ^ 2 * (1 / 650) = (K * M) * (M * (|t| + 2) ^ 2) / 650 := by ring
      rw [e]
      have := mul_le_mul_of_nonneg_right hKM hT
      linarith
    have h4 : K * ((M : ℝ) * (|t| + 2)) ^ 2 * (1 / 650) ≤
        K * ((M : ℝ) * (|t| + 2)) ^ 2 * ‖DirichletCharacter.LFunctionTrivChar₁ M ((26 / 25 : ℂ) + ↑t * I)‖ := by
      apply mul_le_mul_of_nonneg_left hnz0
      positivity
    linarith
  obtain ⟨Z, m, hZ, hm, hcount, hbd⟩ := dhl_core hCau (DirichletCharacter.LFunctionTrivChar₁ M) t K
    ((M : ℝ) * (|t| + 2)) hK1 hX3 (DirichletCharacter.differentiable_LFunctionTrivChar₁ M) hfz0 hgrowth
  have hzero : ∀ ρ : ℂ, DirichletCharacter.LFunctionTrivChar₁ M ρ = 0 ↔
      IsLZero (1 : DirichletCharacter ℂ M) ρ := by
    intro ρ
    constructor
    · intro h
      have hρ : ρ ≠ 1 := fun e => hf1 (e ▸ h)
      refine ⟨Or.inr hρ, ?_⟩
      rw [hf ρ hρ] at h
      exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hρ)
    · rintro ⟨h1, h2⟩
      have hρ : ρ ≠ 1 := h1.resolve_left (fun h => h rfl)
      rw [hf ρ hρ, h2, mul_zero]
  unfold DHLocalAt
  refine ⟨Z, m, ?_, hm, ?_, hcount, ?_⟩
  · intro ρ
    rw [hZ ρ, hzero ρ]
  · intro ρ hρ
    obtain ⟨_, hfρ⟩ := (hZ ρ).mp hρ
    obtain ⟨h1, h2⟩ := (hzero ρ).mp hfρ
    by_contra hge
    push_neg at hge
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re _ h1 hge h2
  · intro k s hs hsd
    have hs1 : s ≠ 1 := dhl_ne_one hs
    have hfs : DirichletCharacter.LFunctionTrivChar₁ M s ≠ 0 := by
      rw [hf s hs1]
      exact mul_ne_zero (sub_ne_zero.mpr hs1)
        (DirichletCharacter.LFunction_ne_zero_of_one_le_re _ (Or.inr hs1) hs.le)
    have hb := hbd k s hsd hfs
    rw [if_pos rfl, ← dhl_triv_iter M s hs k]
    exact hb

theorem deuring_heilbronn_local : DHLocalOf := by
  unfold DHLocalOf DHLocal
  intro hCau
  obtain ⟨C0, hC0⟩ := lfunction_polynomial_growth
  have hlog : 0 ≤ Real.log (max 10400 (52 * C0)) :=
    Real.log_nonneg (by linarith [le_max_left (10400 : ℝ) (52 * C0)])
  refine ⟨150 * (Real.log (max 10400 (52 * C0)) + 2), by linarith, ?_⟩
  intro M inst ψ t hM
  by_cases hψ : ψ = 1
  · subst hψ
    exact dhl_triv hCau _ (le_max_left _ _) M t hM
  · exact dhl_nontriv hCau C0 _ hC0 (by linarith [le_max_left (10400 : ℝ) (52 * C0)])
      (le_max_right _ _) M ψ hψ t hM

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end
end
