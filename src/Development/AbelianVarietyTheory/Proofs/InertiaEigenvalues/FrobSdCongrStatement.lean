module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCastNeZeroPs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CstSApply
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DividedPowerMonomialFrobeniusCongrPowStatement
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DividedPowerSeriesSubringEqGeneratorSet
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCastNeZeroPs

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DividedPowerSeriesGeneratorSetEqSumAddMul

section

@[expose] public section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

theorem sdSet_eq_sum_add_mul (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) :
    ∀ F ∈ SdSet t K e, ∃ (N : ℕ) (v : ℕ → Wq l a), ∃ y ∈ SdSet t K e,
      F = ∑ n ∈ Finset.range N, cstS t K (v n) * dpS a e n + (l : ZMod a → K⟦X⟧) * y := by
  rintro F ⟨w, hw, hF⟩
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hl0 : (l : Wq l a) ≠ 0 := by
    have h := WittVector.p_nonzero l (Fq l a)
    exact h
  have h1 := hw 1
  rw [Nat.cofinite_eq_atTop, Filter.eventually_atTop] at h1
  obtain ⟨N, hN⟩ := h1
  have h2 : ∀ n, ∃ z : Wq l a, (n < N → z = 0) ∧ (¬ n < N → w n = l * z) := by
    intro n
    by_cases h : n < N
    · exact ⟨0, fun _ => rfl, fun h' => absurd h h'⟩
    · obtain ⟨z, hz⟩ := hN n (not_lt.1 h)
      exact ⟨z, fun h' => absurd h' h, fun _ => by rw [hz, pow_one]⟩
  choose z hz0 hz using h2
  have hfac : ∀ n : ℕ, ((n / e).factorial : K) ≠ 0 := fun n => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  refine ⟨N, w, fun τ => PowerSeries.mk fun n => ((n / e).factorial : K)⁻¹ * algebraMap O K (emb t τ (z n)),
    ⟨z, fun r => ?_, fun τ n => ?_⟩, ?_⟩
  · filter_upwards [hw (r + 1)] with n hn
    by_cases h : n < N
    · rw [hz0 n h]; exact dvd_zero _
    · rw [hz n h, pow_succ'] at hn
      exact (mul_dvd_mul_iff_left hl0).1 hn
  · rw [coeff_mk, mul_inv_cancel_left₀ (hfac n)]
  · funext τ
    ext m
    apply mul_left_cancel₀ (hfac m)
    rw [hF]
    have hc : (l : K⟦X⟧) = C (l : K) := (map_natCast (C : K →+* K⟦X⟧) l).symm

    simp only [Pi.add_apply, Finset.sum_apply, Pi.mul_apply, Pi.natCast_apply, map_add (f := _), map_sum, cstS_apply, dpS,
    hc, coeff_C_mul, coeff_monomial, coeff_mk, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_range]
    by_cases h : m < N
    · rw [if_pos h, hz0 m h, map_zero, map_zero]
      field_simp [hfac m]
      ring
    · rw [if_neg h, hz m h, map_mul, map_mul, map_natCast, map_natCast]
      field_simp [hfac m]
      ring

end GlobalTheory.CrysPrism
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DividedPowerSeriesGeneratorSetEqSumAddMulStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per


theorem _root_.GlobalTheory.T.dividedPowerSeriesGeneratorSet_eq_sum_add_mul : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ F ∈ SdSet t K e, ∃ (N : ℕ) (v : ℕ → Wq l a), ∃ y ∈ SdSet t K e, F = ∑ n ∈ Finset.range N, cstS t K (v n) * dpS a e n + (l : ZMod a → K⟦X⟧) * y := by
  first | exact @GlobalTheory.CrysPrism.sdSet_eq_sum_add_mul | exact GlobalTheory.CrysPrism.sdSet_eq_sum_add_mul | (intros; apply GlobalTheory.CrysPrism.sdSet_eq_sum_add_mul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusMapsDividedPowerSeriesGeneratorSet

section

@[expose] public section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

theorem frobTot_mem_SdSet : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O),
    ∀ F ∈ SdSet t K e, frobTot K a l F ∈ SdSet t K e := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t F hF
  obtain ⟨w, hw, hF⟩ := hF
  have hpos : 0 < l := (Fact.out : l.Prime).pos
  refine ⟨fun n => if l ∣ n then
      ((((n / e).factorial / ((n / l) / e).factorial : ℕ) : Wq l a) * sigma l a (w (n / l))) else 0, ?_, ?_⟩
  · intro r
    have h := hw r
    rw [Filter.eventually_cofinite] at h ⊢
    refine (h.image fun m => l * m).subset ?_
    intro n hn
    simp only [Set.mem_setOf_eq] at hn
    split_ifs at hn with hd
    · refine ⟨n / l, ?_, Nat.mul_div_cancel' hd⟩
      intro hr
      apply hn
      obtain ⟨c, hc⟩ := hr
      exact Dvd.dvd.mul_left ⟨sigma l a c, by rw [hc, map_mul, map_pow, map_natCast]⟩ _
    · exact absurd (dvd_zero _) hn
  · intro τ n
    show _ = algebraMap O K (emb t τ (if l ∣ n then _ else 0))
    rw [frobTot_apply, coeff_frob]
    by_cases hd : l ∣ n
    · rw [if_pos hd, if_pos hd]
      obtain ⟨m, rfl⟩ := hd
      rw [Nat.mul_div_cancel_left m hpos]
      have hdiv : (m / e).factorial ∣ (l * m / e).factorial :=
        Nat.factorial_dvd_factorial (Nat.div_le_div_right (Nat.le_mul_of_pos_left m hpos))
      rw [map_mul, map_natCast, emb_sigma, map_mul, map_natCast, ← hF (τ - 1) m, ← mul_assoc, ← Nat.cast_mul,
        Nat.div_mul_cancel hdiv]
    · rw [if_neg hd, if_neg hd]; simp

end GlobalTheory.CrysPrism
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusMapsDividedPowerSeriesGeneratorSetStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per


theorem _root_.GlobalTheory.T.frobenius_maps_dividedPowerSeriesGeneratorSet : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ F ∈ SdSet t K e, frobTot K a l F ∈ SdSet t K e := by
  first | exact @GlobalTheory.CrysPrism.frobTot_mem_SdSet | exact GlobalTheory.CrysPrism.frobTot_mem_SdSet | (intros; apply GlobalTheory.CrysPrism.frobTot_mem_SdSet <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittTiltFrobeniusEqPowAddMul

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.FrobCong

theorem sigma_eq_pow_add (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (w : Wq l a) :
    ∃ x : Wq l a, sigma l a w = w ^ l + (l : Wq l a) * x := by
  have h0 : sigma l a w - w ^ l ∈ Ideal.span {(l : Wq l a)} := by
    rw [← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub, map_pow]
    simp [WittVector.constantCoeff_apply, coeff_sigma]
  obtain ⟨x, hx⟩ := Ideal.mem_span_singleton'.1 h0
  exact ⟨x, by rw [mul_comm, hx]; ring⟩

end GlobalTheory.FrobCong
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittTiltFrobeniusEqPowAddMulStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per


theorem _root_.GlobalTheory.T.wittTiltFrobenius_eq_pow_add_mul : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (w : Wq l a), ∃ x : Wq l a, sigma l a w = w ^ l + (l : Wq l a) * x := by
  first | exact @GlobalTheory.FrobCong.sigma_eq_pow_add | exact GlobalTheory.FrobCong.sigma_eq_pow_add | (intros; apply GlobalTheory.FrobCong.sigma_eq_pow_add <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobSdCongr

section

@[expose] public section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

theorem cstS_mem_frob : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ w : Wq l a, cstS t K w ∈ SdSet t K e ∧ frobTot K a l (cstS t K w) = cstS t K (sigma l a w) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t w
  constructor
  · refine ⟨fun n => if n = 0 then w else 0, fun r => ?_, fun τ n => ?_⟩
    · refine (Set.finite_singleton 0).subset fun n hn => ?_
      by_contra h0
      exact hn (by simp [show n ≠ 0 from h0])
    · rw [cstS_apply, coeff_C]
      by_cases hn : n = 0
      · subst hn; simp
      · simp [hn]
  · funext τ
    change frob K l (cstS t K w (τ - 1)) = cstS t K (sigma l a w) τ
    rw [cstS_apply, cstS_apply, emb_sigma, ← PowerSeries.algebraMap_eq (R := K)]
    exact (frob K l).commutes _

theorem frob_sd_congr : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ F ∈ SdSet t K e, (frobTot K a l) F ∈ SdSet t K e ∧ ∃ B ∈ SdSet t K e, (frobTot K a l) F = F ^ l + (l : ZMod a → K⟦X⟧) * B := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t
  have hclosed : ∀ F ∈ Sd t K e, F ∈ SdSet t K e := sdSet_closed l a e O K t
  have memS : ∀ {F}, F ∈ SdSet t K e → F ∈ Sd t K e := fun h => Subring.subset_closure h
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  let G : (ZMod a → K⟦X⟧) → Prop := fun z => z ∈ Sd t K e ∧
    ∃ B ∈ Sd t K e, frobTot K a l z = z ^ l + (l : ZMod a → K⟦X⟧) * B
  have gadd : ∀ x y, G x → G y → G (x + y) := by
    rintro x y ⟨hx, Bx, hBx, ex⟩ ⟨hy, By, hBy, ey⟩
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq (Fact.out : l.Prime) (⟨x, hx⟩ : Sd t K e) ⟨y, hy⟩
    have hr' := congrArg Subtype.val hr
    push_cast at hr'
    refine ⟨(Sd t K e).add_mem hx hy, Bx + By - x * y * r, ?_, ?_⟩
    · exact (Sd t K e).sub_mem ((Sd t K e).add_mem hBx hBy) ((Sd t K e).mul_mem ((Sd t K e).mul_mem hx hy) r.2)
    · rw [map_add (f := _), ex, ey, hr']; ring
  have gmul : ∀ x y, G x → G y → G (x * y) := by
    rintro x y ⟨hx, Bx, hBx, ex⟩ ⟨hy, By, hBy, ey⟩
    refine ⟨(Sd t K e).mul_mem hx hy, Bx * y ^ l + x ^ l * By + (l : ZMod a → K⟦X⟧) * Bx * By, ?_, ?_⟩
    · have hlS : (l : ZMod a → K⟦X⟧) ∈ Sd t K e := natCast_mem (Sd t K e) l
      exact (Sd t K e).add_mem ((Sd t K e).add_mem ((Sd t K e).mul_mem hBx ((Sd t K e).pow_mem hy l))
        ((Sd t K e).mul_mem ((Sd t K e).pow_mem hx l) hBy)) ((Sd t K e).mul_mem ((Sd t K e).mul_mem hlS hBx) hBy)
    · rw [map_mul, ex, ey]; ring
  have gcst : ∀ w, G (cstS t K w) := by
    intro w
    obtain ⟨hm, hf⟩ := cstS_mem_frob l a e O K t w
    obtain ⟨x, hx⟩ := GlobalTheory.T.wittTiltFrobenius_eq_pow_add_mul l a w
    refine ⟨memS hm, cstS t K x, memS (cstS_mem_frob l a e O K t x).1, ?_⟩
    rw [hf, hx, map_add (f := _), map_pow, map_mul, map_natCast]
  have gdp : ∀ n, G (dpS a e n) := by
    intro n
    obtain ⟨hm, B, hB, eB⟩ := GlobalTheory.T.dividedPowerMonomial_frobenius_congr_pow l a e O K t n
    exact ⟨memS hm, B, memS hB, eB⟩
  have gsum : ∀ (N : ℕ) (v : ℕ → Wq l a), G (∑ n ∈ Finset.range N, cstS t K (v n) * dpS a e n) := by
    intro N v
    refine Finset.sum_induction _ G gadd ⟨(Sd t K e).zero_mem, 0, (Sd t K e).zero_mem, ?_⟩ fun n _ => gmul _ _ (gcst _) (gdp n)
    rw [map_zero, zero_pow hl0, mul_zero, add_zero]
  intro F hF
  refine ⟨GlobalTheory.T.frobenius_maps_dividedPowerSeriesGeneratorSet l a e O K t F hF, ?_⟩
  obtain ⟨N, v, y, hy, hFe⟩ := GlobalTheory.T.dividedPowerSeriesGeneratorSet_eq_sum_add_mul l a e O K t F hF
  obtain ⟨hg, Bg, hBg, eg⟩ := gsum N v
  set g := ∑ n ∈ Finset.range N, cstS t K (v n) * dpS a e n
  set L : ZMod a → K⟦X⟧ := (l : ZMod a → K⟦X⟧)
  set Q := ∑ i ∈ Finset.range l, (g + L * y) ^ i * g ^ (l - 1 - i)
  have hQ : Q ∈ Sd t K e := (Sd t K e).sum_mem fun i _ => (Sd t K e).mul_mem
    ((Sd t K e).pow_mem ((Sd t K e).add_mem hg ((Sd t K e).mul_mem (natCast_mem (Sd t K e) l) (memS hy))) i)
    ((Sd t K e).pow_mem hg _)
  have geo : (g + L * y) ^ l = g ^ l + L * (y * Q) := by
    have h := geom_sum₂_mul (g + L * y) g l
    linear_combination -h
  refine ⟨Bg + frobTot K a l y - y * Q, hclosed _ ((Sd t K e).sub_mem ((Sd t K e).add_mem hBg
    (memS (GlobalTheory.T.frobenius_maps_dividedPowerSeriesGeneratorSet l a e O K t y hy))) ((Sd t K e).mul_mem (memS hy) hQ)), ?_⟩
  rw [hFe, map_add (f := _), map_mul, map_natCast]
  linear_combination eg - geo

end GlobalTheory.CrysPrism
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobSdCongrStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per


theorem _root_.GlobalTheory.T.frobTot_mem_SdSet_and_eq_pow_add_mul : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ F ∈ SdSet t K e, (frobTot K a l) F ∈ SdSet t K e ∧ ∃ B ∈ SdSet t K e, (frobTot K a l) F = F ^ l + (l : ZMod a → K⟦X⟧) * B := by
  first | exact @GlobalTheory.CrysPrism.frob_sd_congr | exact GlobalTheory.CrysPrism.frob_sd_congr | (intros; apply GlobalTheory.CrysPrism.frob_sd_congr <;> assumption)
end
end
