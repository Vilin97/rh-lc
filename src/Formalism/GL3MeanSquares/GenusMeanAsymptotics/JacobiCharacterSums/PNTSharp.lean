module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.DeuringHeilbronnM
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Formalism.LandauZeroFreeBounds.LogDerivRegionChiOf
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTSharpA

section

@[expose] public section

open Finset Complex

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

lemma sharp_cpow_sub_one {ρ : ℂ} (hρ0 : ρ ≠ 0) (hre : ρ.re ≤ 1) {t : ℝ} (ht : 1 ≤ t) :
    ‖(t : ℂ) ^ ρ - 1‖ ≤ ‖ρ‖ * (t - 1) := by
  have hd : ∀ x ∈ Set.Icc (1 : ℝ) t,
      HasDerivWithinAt (fun y : ℝ => (y : ℂ) ^ ρ) (ρ * (x : ℂ) ^ (ρ - 1)) (Set.Icc 1 t) x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := by linarith [hx.1]
    exact ((Complex.hasStrictDerivAt_cpow_const (Complex.ofReal_mem_slitPlane.2 hx0)).hasDerivAt.comp_ofReal).hasDerivWithinAt
  have hb : ∀ x ∈ Set.Ico (1 : ℝ) t, ‖ρ * (x : ℂ) ^ (ρ - 1)‖ ≤ ‖ρ‖ := by
    intro x hx
    have hx0 : (0 : ℝ) < x := by linarith [hx.1]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have h1 : x ^ (ρ - 1).re ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx.1 (by simp; linarith)
    calc ‖ρ‖ * x ^ (ρ - 1).re ≤ ‖ρ‖ * 1 := by gcongr
      _ = ‖ρ‖ := mul_one _
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hd hb t ⟨ht, le_rfl⟩
  simpa using h

lemma differenced_kernel_bound {ρ : ℂ} (hρ0 : ρ ≠ 0) (hρ1 : ρ ≠ 1) (hre : ρ.re ≤ 1) {δ : ℝ} (hδ : 0 < δ) :
    ‖(((1 + δ : ℝ) : ℂ) ^ (ρ - 1) - 1) / (ρ - 1) + (((1 + δ)⁻¹ - 1 : ℝ) : ℂ)‖ ≤ ‖ρ‖ * δ * δ := by
  have hρ1' : ρ - 1 ≠ 0 := sub_ne_zero.2 hρ1
  let f : ℝ → ℂ := fun u => (((u : ℂ) ^ (ρ - 1) - 1) / (ρ - 1)) + (((u⁻¹ - 1 : ℝ)) : ℂ)
  let f' : ℝ → ℂ := fun u => ((u : ℂ) ^ ρ - 1) / (u : ℂ) ^ 2
  have hd : ∀ x ∈ Set.Icc (1 : ℝ) (1 + δ), HasDerivWithinAt f (f' x) (Set.Icc 1 (1 + δ)) x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := by linarith [hx.1]
    have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hx0.ne'
    have h1 := (((Complex.hasStrictDerivAt_cpow_const (c := ρ - 1)
      (Complex.ofReal_mem_slitPlane.2 hx0)).hasDerivAt.comp_ofReal).sub_const 1).div_const (ρ - 1)
    have h2 := ((hasDerivAt_inv hx0.ne').sub_const 1).ofReal_comp
    refine (h1.add h2).hasDerivWithinAt.congr_deriv ?_
    simp only [f']
    have e1 : (x : ℂ) ^ (ρ - 1 - 1) = (x : ℂ) ^ ρ / (x : ℂ) ^ 2 := by
      rw [show ρ - 1 - 1 = ρ - 2 by ring, Complex.cpow_sub _ _ hxc,
        show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
    rw [e1]
    push_cast
    field_simp
    ring
  have hb : ∀ x ∈ Set.Ico (1 : ℝ) (1 + δ), ‖f' x‖ ≤ ‖ρ‖ * δ := by
    intro x hx
    have hx0 : (0 : ℝ) < x := by linarith [hx.1]
    have hk := sharp_cpow_sub_one hρ0 hre hx.1
    simp only [f']
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hx0.le]
    have hx1 : 1 ≤ x ^ 2 := one_le_pow₀ hx.1
    calc ‖(x : ℂ) ^ ρ - 1‖ / x ^ 2 ≤ ‖(x : ℂ) ^ ρ - 1‖ := div_le_self (norm_nonneg _) hx1
      _ ≤ ‖ρ‖ * (x - 1) := hk
      _ ≤ ‖ρ‖ * δ := by gcongr; linarith [hx.2]
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hd hb (1 + δ) ⟨by linarith, le_rfl⟩
  have hf1 : f 1 = 0 := by simp [f]
  rw [hf1, sub_zero, show 1 + δ - 1 = δ by ring] at h
  exact h

lemma sharp_kernel {ρ : ℂ} (hρ0 : ρ ≠ 0) (hρ1 : ρ ≠ 1) (hre : ρ.re ≤ 1) {δ : ℝ} (hδ : 0 < δ)
    (hδ2 : δ ≤ 1 / 2) :
    ‖(((1 + δ) / δ : ℝ) : ℂ) * ((((1 + δ : ℝ) : ℂ) ^ (ρ - 1) - 1) / (ρ - 1)) - 1‖ ≤ 2 * δ * ‖ρ‖ := by
  set g : ℂ := (((1 + δ : ℝ) : ℂ) ^ (ρ - 1) - 1) / (ρ - 1) with hg
  set e : ℂ := g + (((1 + δ)⁻¹ - 1 : ℝ) : ℂ) with he
  have hae := differenced_kernel_bound hρ0 hρ1 hre hδ
  rw [← hg, ← he] at hae
  have hr : (1 + δ) / δ * ((1 + δ)⁻¹ - 1) = -1 := by
    field_simp
    ring
  have hid : (((1 + δ) / δ : ℝ) : ℂ) * g - 1 = (((1 + δ) / δ : ℝ) : ℂ) * e := by
    rw [he, mul_add, ← Complex.ofReal_mul, hr]
    push_cast
    ring
  have hq : 0 < (1 + δ) / δ := by positivity
  rw [hid, norm_mul, Complex.norm_real, Real.norm_of_nonneg hq.le]
  calc (1 + δ) / δ * ‖e‖ ≤ (1 + δ) / δ * (‖ρ‖ * δ * δ) := by gcongr
    _ = (1 + δ) * (δ * ‖ρ‖) := by field_simp
    _ ≤ 2 * (δ * ‖ρ‖) := by gcongr; linarith
    _ = 2 * δ * ‖ρ‖ := by ring

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end
end

-- Source module: Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTSharpB

section

@[expose] public section

open Finset Complex ArithmeticFunction

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.ZeroFreeDirichlet

lemma sharp_split (g : ℕ → ℂ) {a b : ℕ} (hab : a ≤ b) :
    ∑ n ∈ Icc 1 b, g n = ∑ n ∈ Icc 1 a, g n + ∑ n ∈ Ioc a b, g n := by
  have hd : Disjoint (Icc 1 a) (Ioc a b) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_Icc, Finset.mem_Ioc] at hx hx'
    omega
  have hu : Icc 1 b = Icc 1 a ∪ Ioc a b := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ioc, Finset.mem_union]
    omega
  rw [hu, Finset.sum_union hd]

lemma sharp_schi_div {N : ℕ} (χ : DirichletCharacter ℂ N) {v : ℝ} (hv : 0 < v) :
    Formalism.ZeroFreeDirichlet.Schi χ v / (v : ℂ) =
      ∑ n ∈ Icc 1 ⌊v⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod N) * ((1 / n - 1 / v : ℝ) : ℂ) := by
  rw [Formalism.ZeroFreeDirichlet.Schi.eq_1, Finset.sum_div]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hn0 : (n:ℝ) ≠ 0 := by positivity
  have hv0 : v ≠ 0 := hv.ne'
  rw [mul_div_assoc]
  congr 1
  rw [← Complex.ofReal_div]
  congr 1
  field_simp

lemma sharp_identity {N : ℕ} (χ : DirichletCharacter ℂ N) {y u : ℝ} (hy : 1 ≤ y) (hu : y < u) :
    ((y * u / (u - y) : ℝ) : ℂ) * (Formalism.ZeroFreeDirichlet.Schi χ u / (u : ℂ) - Formalism.ZeroFreeDirichlet.Schi χ y / (y : ℂ)) - psiChi χ y =
      ∑ n ∈ Ioc ⌊y⌋₊ ⌊u⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod N) *
        ((y * u / (u - y) * (1 / n - 1 / u) : ℝ) : ℂ) := by
  have hy0 : 0 < y := by linarith
  have hu0 : 0 < u := by linarith
  have huy : u - y ≠ 0 := (sub_pos.mpr hu).ne'
  have hfl : ⌊y⌋₊ ≤ ⌊u⌋₊ := Nat.floor_mono hu.le
  rw [sharp_schi_div χ hu0, sharp_schi_div χ hy0, sharp_split _ hfl, Formalism.ZeroFreeDirichlet.psiChi.eq_1]
  have hc1 : y * u / (u - y) * (1 / y - 1 / u) = 1 := by
    field_simp
  have hAC : (∑ n ∈ Icc 1 ⌊y⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod N) * ((1 / n - 1 / u : ℝ) : ℂ)) -
      ∑ n ∈ Icc 1 ⌊y⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod N) * ((1 / n - 1 / y : ℝ) : ℂ) =
      ((1 / y - 1 / u : ℝ) : ℂ) * ∑ n ∈ Icc 1 ⌊y⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod N) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    push_cast
    ring
  have hE : ∑ n ∈ Ioc ⌊y⌋₊ ⌊u⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod N) *
        ((y * u / (u - y) * (1 / n - 1 / u) : ℝ) : ℂ) =
      ((y * u / (u - y) : ℝ) : ℂ) *
        ∑ n ∈ Ioc ⌊y⌋₊ ⌊u⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod N) * ((1 / n - 1 / u : ℝ) : ℂ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    push_cast
    ring
  have hc1' : ((y * u / (u - y) : ℝ) : ℂ) * ((1 / y - 1 / u : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, hc1, Complex.ofReal_one]
  rw [hE]
  linear_combination ((y * u / (u - y) : ℝ) : ℂ) * hAC +
    (∑ n ∈ Icc 1 ⌊y⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod N)) * hc1'

lemma sharp_term {N : ℕ} (χ : DirichletCharacter ℂ N) {y u : ℝ} (hy : 1 ≤ y) (hu : y < u)
    {n : ℕ} (hn : n ∈ Ioc ⌊y⌋₊ ⌊u⌋₊) :
    ‖((Λ n : ℝ) : ℂ) * χ (n : ZMod N) * ((y * u / (u - y) * (1 / n - 1 / u) : ℝ) : ℂ)‖ ≤
      Real.log u := by
  have hy0 : 0 < y := by linarith
  have hu0 : 0 < u := by linarith
  obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.mp hn
  have hyn : y < n := (Nat.floor_lt hy0.le).mp hn1
  have hnu : (n : ℝ) ≤ u := (Nat.le_floor_iff hu0.le).mp hn2
  have hnpos : (0:ℝ) < n := by linarith
  have huy : 0 < u - y := by linarith
  have hf0 : 0 ≤ y * u / (u - y) * (1 / n - 1 / u) := by
    apply mul_nonneg (div_nonneg (by positivity) huy.le)
    rw [sub_nonneg]
    exact one_div_le_one_div_of_le hnpos hnu
  have hf1 : y * u / (u - y) * (1 / n - 1 / u) ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one huy]
    have h1 : y * u * (1 / n - 1 / u) = y * u / n - y := by
      rw [mul_sub, mul_one_div, mul_one_div, mul_div_cancel_right₀ y hu0.ne']
    rw [h1]
    have h2 : y * u / n ≤ u := by
      rw [div_le_iff₀ hnpos]
      nlinarith
    linarith
  have hΛ0 : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
  have hΛ : Λ n ≤ Real.log u :=
    ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hnpos hnu)
  have hχ : ‖χ (n : ZMod N)‖ ≤ 1 := DirichletCharacter.norm_le_one χ (n : ZMod N)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg hΛ0, ← abs_mul, abs_of_nonneg hf0]
  calc Λ n * ‖χ (n : ZMod N)‖ * (y * u / (u - y) * (1 / n - 1 / u)) ≤ Λ n * 1 * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hχ hΛ0) hf1 hf0 (mul_nonneg hΛ0 zero_le_one)
    _ = Λ n := by ring
    _ ≤ Real.log u := hΛ

theorem sharp_arith {N : ℕ} (χ : DirichletCharacter ℂ N) {y u : ℝ} (hy : 1 ≤ y) (hu : y < u) :
    ‖((y * u / (u - y) : ℝ) : ℂ) * (Formalism.ZeroFreeDirichlet.Schi χ u / (u : ℂ) - Formalism.ZeroFreeDirichlet.Schi χ y / (y : ℂ)) - psiChi χ y‖ ≤
      (u - y + 1) * Real.log u := by
  rw [sharp_identity χ hy hu]
  have hu1 : 1 ≤ u := by linarith
  have hlog : 0 ≤ Real.log u := Real.log_nonneg hu1
  calc _ ≤ ∑ n ∈ Ioc ⌊y⌋₊ ⌊u⌋₊, ‖((Λ n : ℝ) : ℂ) * χ (n : ZMod N) *
          ((y * u / (u - y) * (1 / n - 1 / u) : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Ioc ⌊y⌋₊ ⌊u⌋₊, Real.log u := Finset.sum_le_sum (fun n hn => sharp_term χ hy hu hn)
    _ = ((⌊u⌋₊ - ⌊y⌋₊ : ℕ) : ℝ) * Real.log u := by
        rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
    _ ≤ (u - y + 1) * Real.log u := by
        apply mul_le_mul_of_nonneg_right _ hlog
        have h1 : (⌊u⌋₊ : ℝ) ≤ u := Nat.floor_le (by linarith)
        have h2 : y < ⌊y⌋₊ + 1 := Nat.lt_floor_add_one y
        have h3 : ⌊y⌋₊ ≤ ⌊u⌋₊ := Nat.floor_mono hu.le
        rw [Nat.cast_sub h3]
        linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end
end

-- Source module: Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTSharp

section

@[expose] public section

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

lemma sharp_zero_term {ρ : ℂ} (h1 : 1 / 2 ≤ ρ.re) (h2 : ρ.re < 1) {y δ : ℝ} (hy : 0 < y) (hδ : 0 < δ)
    (hδ2 : δ ≤ 1 / 2) :
    ‖((y * ((1 + δ) / δ) : ℝ) : ℂ) * ((((1 + δ) * y : ℝ) : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1)) -
        (y : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1))) - (y : ℂ) ^ ρ / ρ‖ ≤ 2 * δ * y * y ^ (ρ.re - 1) := by
  have hρ0 : ρ ≠ 0 := by
    intro h; rw [h] at h1; norm_num at h1
  have hρ1 : ρ ≠ 1 := by
    intro h; rw [h] at h2; norm_num at h2
  have hs : ρ - 1 ≠ 0 := sub_ne_zero.2 hρ1
  have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hδc : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
  have hpow : (y : ℂ) ^ ρ = (y : ℂ) * (y : ℂ) ^ (ρ - 1) := by
    rw [Complex.cpow_sub _ _ hyc, Complex.cpow_one]; field_simp
  have e : ((y * ((1 + δ) / δ) : ℝ) : ℂ) * ((((1 + δ) * y : ℝ) : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1)) -
        (y : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1))) - (y : ℂ) ^ ρ / ρ =
      (y : ℂ) ^ ρ / ρ *
        ((((1 + δ) / δ : ℝ) : ℂ) * ((((1 + δ : ℝ) : ℂ) ^ (ρ - 1) - 1) / (ρ - 1)) - 1) := by
    rw [Complex.ofReal_mul (1 + δ) y, Complex.mul_cpow_ofReal_nonneg (by linarith) hy.le, hpow]
    generalize ((1 + δ : ℝ) : ℂ) ^ (ρ - 1) = a
    generalize (y : ℂ) ^ (ρ - 1) = b
    push_cast
    field_simp
  rw [e, norm_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  have hk := sharp_kernel hρ0 hρ1 h2.le hδ hδ2
  have hn : 0 < ‖ρ‖ := norm_pos_iff.2 hρ0
  have hr : y ^ ρ.re = y * y ^ (ρ.re - 1) := by
    rw [Real.rpow_sub_one hy.ne']; field_simp
  calc y ^ ρ.re / ‖ρ‖ * _ ≤ y ^ ρ.re / ‖ρ‖ * (2 * δ * ‖ρ‖) :=
        mul_le_mul_of_nonneg_left hk (by positivity)
    _ = 2 * δ * y * y ^ (ρ.re - 1) := by rw [hr]; field_simp

lemma sharp_log_term {y δ : ℝ} (hy : 0 < y) (hδ : 0 < δ) :
    |y * ((1 + δ) / δ) * ((Real.log ((1 + δ) * y) - 1) - (Real.log y - 1)) - y| ≤ δ * y := by
  have h1 : (0 : ℝ) < 1 + δ := by linarith
  rw [Real.log_mul h1.ne' hy.ne']
  have hup : Real.log (1 + δ) ≤ δ := by
    have := Real.log_le_sub_one_of_pos h1; linarith
  have hlo : δ / (1 + δ) ≤ Real.log (1 + δ) := by
    have := Real.one_sub_inv_le_log_of_pos h1
    have e : 1 - (1 + δ)⁻¹ = δ / (1 + δ) := by field_simp; ring
    linarith
  have e : y * ((1 + δ) / δ) * ((Real.log (1 + δ) + Real.log y - 1) - (Real.log y - 1)) - y =
      y * ((1 + δ) / δ * Real.log (1 + δ) - 1) := by ring
  rw [e, abs_mul, abs_of_pos hy, mul_comm δ y]
  refine mul_le_mul_of_nonneg_left ?_ hy.le
  have hc : 0 < (1 + δ) / δ := by positivity
  rw [abs_le]
  constructor
  · have : (1 + δ) / δ * (δ / (1 + δ)) ≤ (1 + δ) / δ * Real.log (1 + δ) :=
      mul_le_mul_of_nonneg_left hlo hc.le
    have e2 : (1 + δ) / δ * (δ / (1 + δ)) = 1 := by field_simp
    linarith
  · have : (1 + δ) / δ * Real.log (1 + δ) ≤ (1 + δ) / δ * δ := mul_le_mul_of_nonneg_left hup hc.le
    have e2 : (1 + δ) / δ * δ = 1 + δ := by field_simp
    linarith

theorem differenced_explicit_formula : SharpenS := by
  intro M _ χ Z m K E y δ hZ hy hδ hδ2 hE
  have hy0 : 0 < y := by linarith
  have hEu := hE ((1 + δ) * y) (Or.inr rfl)
  have hEy := hE y (Or.inl rfl)
  have hE0 : 0 ≤ E := (norm_nonneg _).trans hEy
  have huy : y < (1 + δ) * y := by nlinarith
  have hR := sharp_arith χ (by linarith : (1 : ℝ) ≤ y) huy
  have hc : y * ((1 + δ) * y) / ((1 + δ) * y - y) = y * ((1 + δ) / δ) := by
    have : (1 + δ) * y - y = δ * y := by ring
    rw [this]; field_simp
  rw [hc] at hR
  set c : ℝ := y * ((1 + δ) / δ) with hcdef
  have hc0 : 0 < c := by positivity
  have hcle : c ≤ 3 / 2 * y / δ := by
    rw [hcdef, show y * ((1 + δ) / δ) = (1 + δ) * y / δ by ring]
    exact div_le_div_of_nonneg_right (by nlinarith) hδ.le
  set T : ℂ → ℂ := fun ρ => (c : ℂ) * ((((1 + δ) * y : ℝ) : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1)) -
        (y : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1))) - (y : ℂ) ^ ρ / ρ with hT
  have hsum : ∑ ρ ∈ Z, (m ρ : ℂ) * T ρ =
      (c : ℂ) * (∑ ρ ∈ Z, (m ρ : ℂ) * (((1 + δ) * y : ℝ) : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1)) -
        ∑ ρ ∈ Z, (m ρ : ℂ) * (y : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1))) -
        ∑ ρ ∈ Z, (m ρ : ℂ) * (y : ℂ) ^ ρ / ρ := by
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    simp only [hT]; ring
  have hTb : ‖∑ ρ ∈ Z, (m ρ : ℂ) * T ρ‖ ≤ 2 * δ * y * ∑ ρ ∈ Z, (m ρ : ℝ) * y ^ (ρ.re - 1) := by
    rw [Finset.mul_sum]
    refine norm_sum_le_of_le _ fun ρ hρ => ?_
    rw [norm_mul, Complex.norm_natCast]
    have := sharp_zero_term (hZ ρ hρ).1 (hZ ρ hρ).2 hy0 hδ hδ2
    calc (m ρ : ℝ) * ‖T ρ‖ ≤ (m ρ : ℝ) * (2 * δ * y * y ^ (ρ.re - 1)) :=
          mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
      _ = 2 * δ * y * ((m ρ : ℝ) * y ^ (ρ.re - 1)) := by ring
  have hS0 : 0 ≤ ∑ ρ ∈ Z, (m ρ : ℝ) * y ^ (ρ.re - 1) :=
    Finset.sum_nonneg fun ρ _ => by positivity
  have hP : ‖(c : ℂ) * ((if χ = 1 then ((Real.log ((1 + δ) * y) - 1 : ℝ) : ℂ) else 0) -
      (if χ = 1 then ((Real.log y - 1 : ℝ) : ℂ) else 0)) - (if χ = 1 then (y : ℂ) else 0)‖ ≤ δ * y := by
    by_cases hχ : χ = 1
    · simp only [hχ, if_true]
      rw [← Complex.ofReal_sub, ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs]
      exact sharp_log_term hy0 hδ
    · simp only [hχ, if_false]
      simp; positivity
  have hlog1 : 1 ≤ Real.log (2 * y) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hlogu : Real.log ((1 + δ) * y) ≤ Real.log (2 * y) :=
    Real.log_le_log (by positivity) (by nlinarith)
  have hD : ‖(c : ℂ) * ((Formalism.ZeroFreeDirichlet.Schi χ ((1 + δ) * y) / (((1 + δ) * y : ℝ) : ℂ) - K -
        (if χ = 1 then ((Real.log ((1 + δ) * y) - 1 : ℝ) : ℂ) else 0) +
          ∑ ρ ∈ Z, (m ρ : ℂ) * (((1 + δ) * y : ℝ) : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1))) -
      (Formalism.ZeroFreeDirichlet.Schi χ y / (y : ℂ) - K - (if χ = 1 then ((Real.log y - 1 : ℝ) : ℂ) else 0) +
                ∑ ρ ∈ Z, (m ρ : ℂ) * (y : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1))))‖ ≤ c * (2 * E) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0]
    refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans ?_) hc0.le
    linarith
  have key : psiChi χ y - (if χ = 1 then (y : ℂ) else 0) + ∑ ρ ∈ Z, (m ρ : ℂ) * (y : ℂ) ^ ρ / ρ =
      (c : ℂ) * ((Formalism.ZeroFreeDirichlet.Schi χ ((1 + δ) * y) / (((1 + δ) * y : ℝ) : ℂ) - K -
        (if χ = 1 then ((Real.log ((1 + δ) * y) - 1 : ℝ) : ℂ) else 0) +
          ∑ ρ ∈ Z, (m ρ : ℂ) * (((1 + δ) * y : ℝ) : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1))) -
      (Formalism.ZeroFreeDirichlet.Schi χ y / (y : ℂ) - K - (if χ = 1 then ((Real.log y - 1 : ℝ) : ℂ) else 0) +
                ∑ ρ ∈ Z, (m ρ : ℂ) * (y : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1))))
      - ((c : ℂ) * (Formalism.ZeroFreeDirichlet.Schi χ ((1 + δ) * y) / (((1 + δ) * y : ℝ) : ℂ) - Formalism.ZeroFreeDirichlet.Schi χ y / (y : ℂ)) - psiChi χ y)
      + ((c : ℂ) * ((if χ = 1 then ((Real.log ((1 + δ) * y) - 1 : ℝ) : ℂ) else 0) -
      (if χ = 1 then ((Real.log y - 1 : ℝ) : ℂ) else 0)) - (if χ = 1 then (y : ℂ) else 0))
      - ∑ ρ ∈ Z, (m ρ : ℂ) * T ρ := by
    rw [hsum]; ring
  rw [key]
  refine (norm_sub_le _ _).trans ?_
  refine (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
    (add_le_add hD hR)) hP)) hTb).trans ?_
  have b1 : c * (2 * E) ≤ 4 * y * E / δ := by
    calc c * (2 * E) ≤ 3 / 2 * y / δ * (2 * E) := mul_le_mul_of_nonneg_right hcle (by positivity)
      _ = 3 * y * E / δ := by ring
      _ ≤ 4 * y * E / δ := div_le_div_of_nonneg_right (by nlinarith [mul_nonneg hy0.le hE0]) hδ.le
  have hdy : 0 < δ * y := by positivity
  have b2 : ((1 + δ) * y - y + 1) * Real.log ((1 + δ) * y) ≤ (δ * y + 1) * Real.log (2 * y) := by
    rw [show (1 + δ) * y - y + 1 = δ * y + 1 by ring]
    exact mul_le_mul_of_nonneg_left hlogu (by positivity)
  have b3 : δ * y ≤ (δ * y + 1) * Real.log (2 * y) := by nlinarith
  have b4 : 2 * δ * y * ∑ ρ ∈ Z, (m ρ : ℝ) * y ^ (ρ.re - 1) ≤
      20 * δ * y * ∑ ρ ∈ Z, (m ρ : ℝ) * y ^ (ρ.re - 1) :=
    mul_le_mul_of_nonneg_right (by nlinarith) hS0
  have b5 : 0 ≤ (δ * y + 1) * Real.log (2 * y) := by positivity
  linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end
end
