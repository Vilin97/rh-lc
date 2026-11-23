module

public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Mathlib.RingTheory.FormalGroup.Basic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesInChartRingHomLaws
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImagQuadraticMaximalOrderArithmeticAtSplitPrimeStatement
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
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsUnitCoeffMulSeriesLeNormStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormalGroupPadicMulIntegralVanishingOrderStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImagQuadraticMaximalOrderArithmeticAtSplitPrime
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UwEllipticFlow

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsSmallInPrimePow

section

@[expose] public section

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne

theorem thue_normSq (d e : ℕ) (he : d + 1 = 4 * e) (u v : ℤ) :
    Complex.normSq ((u : ℂ) + (v : ℂ) * wK d) = ((u ^ 2 + u * v + e * v ^ 2 : ℤ) : ℝ) := by
  have hs : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt (Nat.cast_nonneg d)
  have he' : (d : ℝ) + 1 = 4 * e := by exact_mod_cast he
  have h1 : ((u : ℂ) + (v : ℂ) * wK d).re = u + v / 2 := by
    simp [wK]; ring
  have h2 : ((u : ℂ) + (v : ℂ) * wK d).im = v * Real.sqrt d / 2 := by
    simp [wK]; ring
  rw [Complex.normSq_apply, h1, h2]
  push_cast
  linear_combination ((v : ℝ) ^ 2 / 4) * hs + ((v : ℝ) ^ 2 / 4) * he'

theorem thue_norm_zc {q : ℕ} [Fact q.Prime] (a : ℤ_[q]) : ‖zc a‖ = ‖a‖ := by
  unfold zc
  rw [norm_algebraMap', PadicInt.padic_norm_e_of_padicInt]

theorem thue_pigeon {q : ℕ} [Fact q.Prime] (a : ℤ_[q]) (k : ℕ) :
    ∃ u v : ℤ, (u ≠ 0 ∨ v ≠ 0) ∧ u ^ 2 ≤ (q : ℤ) ^ k ∧ v ^ 2 ≤ (q : ℤ) ^ k ∧
      ‖(u : ℤ_[q]) + (v : ℤ_[q]) * a‖ ≤ (q : ℝ) ^ (-(k : ℤ)) := by
  have hq : q.Prime := Fact.out
  haveI : NeZero (q ^ k) := ⟨pow_ne_zero _ hq.ne_zero⟩
  set m := Nat.sqrt (q ^ k) with hm
  let f : Fin (m + 1) × Fin (m + 1) → ZMod (q ^ k) := fun p =>
    PadicInt.toZModPow k (((p.1 : ℕ) : ℤ_[q]) + ((p.2 : ℕ) : ℤ_[q]) * a)
  have hcard : Fintype.card (ZMod (q ^ k)) < Fintype.card (Fin (m + 1) × Fin (m + 1)) := by
    rw [ZMod.card, Fintype.card_prod, Fintype.card_fin]
    exact Nat.lt_succ_sqrt _
  obtain ⟨x, y, hxy, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  have hm2 : ((m : ℤ)) ^ 2 ≤ (q : ℤ) ^ k := by
    have := Nat.sqrt_le' (q ^ k)
    exact_mod_cast this
  have hb : ∀ i j : Fin (m + 1), (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) ^ 2 ≤ (q : ℤ) ^ k := by
    intro i j
    have hi := i.2
    have hj := j.2
    refine le_trans ?_ hm2
    apply sq_le_sq' <;> omega
  refine ⟨((x.1 : ℕ) : ℤ) - ((y.1 : ℕ) : ℤ), ((x.2 : ℕ) : ℤ) - ((y.2 : ℕ) : ℤ), ?_, hb _ _, hb _ _, ?_⟩
  · by_contra h
    push_neg at h
    apply hxy
    ext
    · have := h.1; omega
    · have := h.2; omega
  · rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker]
    have : PadicInt.toZModPow k ((((x.1 : ℕ) : ℤ_[q]) + ((x.2 : ℕ) : ℤ_[q]) * a) -
        (((y.1 : ℕ) : ℤ_[q]) + ((y.2 : ℕ) : ℤ_[q]) * a)) = 0 := by
      rw [map_sub, sub_eq_zero]; exact hf
    rw [← this]
    congr 1
    push_cast
    ring

theorem exists_small_in_prime_pow : ∀ (d q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]), d.Prime → d % 16 = 7 → Split d q → ∀ k : ℕ, ∃ (β : ℂ) (N : ℕ), InOK d β ∧ β ≠ 0 ∧ ‖ι β‖ ≤ (q : ℝ) ^ (-(k : ℤ)) ∧ (N : ℂ) = β * conj β ∧ N ≤ (d + 3) * q ^ k := by
  intro d q _ ι hd h16 hs k
  obtain ⟨⟨-, hw, -⟩, h2, -⟩ := GlobalTheory.T.imagQuadraticMaximalOrder_arithmetic_at_split_prime d q ι hd h16 hs
  obtain ⟨⟨a, ha⟩, -⟩ := h2 _ hw
  obtain ⟨u, v, huv, hu, hv, hn⟩ := thue_pigeon a k
  obtain ⟨e, he⟩ : ∃ e : ℕ, d + 1 = 4 * e := ⟨(d + 1) / 4, by omega⟩
  have he1 : (1 : ℤ) ≤ e := by omega
  have hed : (e : ℤ) ≤ d := by omega
  have hpos : 0 < u ^ 2 + u * v + e * v ^ 2 := by
    have h3 : v ^ 2 ≤ e * v ^ 2 := by nlinarith [sq_nonneg v]
    have h4 : 0 < u ^ 2 + v ^ 2 := by
      rcases huv with h | h
      · have := sq_pos_of_ne_zero h; nlinarith [sq_nonneg v]
      · have := sq_pos_of_ne_zero h; nlinarith [sq_nonneg u]
    nlinarith [sq_nonneg (u + v)]
  have hN := thue_normSq d e he u v
  obtain ⟨N, hNe⟩ := Int.eq_ofNat_of_zero_le hpos.le
  refine ⟨(u : ℂ) + (v : ℂ) * wK d, N, ⟨u, v, rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro h
    rw [h, map_zero] at hN
    have : u ^ 2 + u * v + e * v ^ 2 = 0 := by exact_mod_cast hN.symm
    omega
  · have : ι ((u : ℂ) + (v : ℂ) * wK d) = zc ((u : ℤ_[q]) + (v : ℤ_[q]) * a) := by
      rw [map_add (f := _), map_mul, ha]
      simp [zc]
    rw [this, thue_norm_zc]
    exact hn
  · rw [Complex.mul_conj, hN, hNe]
    simp
  · have h5 : (e : ℤ) * v ^ 2 ≤ d * (q : ℤ) ^ k :=
      mul_le_mul hed hv (sq_nonneg v) (by positivity)
    have h6 : (N : ℤ) ≤ (d + 3) * (q : ℤ) ^ k := by
      rw [← hNe]
      nlinarith [sq_nonneg (u - v), sq_nonneg u, sq_nonneg v]
    exact_mod_cast h6

end GlobalTheory.MomOne
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.HeightOneOfSplit

section

@[expose] public section

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne

private theorem norm_zc_eq {q : ℕ} [Fact q.Prime] (a : ℤ_[q]) : ‖zc a‖ = ‖a‖ := by
  unfold zc
  exact (PadicComplex.norm_extends' (p := q) (a : ℚ_[q])).trans (PadicInt.norm_def).symm

private theorem zc_natCast_eq {q : ℕ} [Fact q.Prime] (n : ℕ) : zc (n : ℤ_[q]) = (n : ℂ_[q]) := by
  simp [zc]

theorem height_one_of_split : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (F : FormalGroup 𝓞_ℂ_[q]), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.Ok → MvPowerSeries.subst (![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[q]) (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u)), PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[q]) (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u))] : Fin 2 → MvPowerSeries (Fin 2) ℂ_[q]) (MvPowerSeries.map (algebraMap 𝓞_ℂ_[q] ℂ_[q]) F.toPowerSeries) = PowerSeries.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[q]) (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u)) → ∃ ℓ : ℂ_[q]⟦X⟧, constantCoeff ℓ = 0 ∧ PowerSeries.subst ℓ (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u)) = X ∧ ‖coeff q (PowerSeries.subst (C (q : ℂ_[q]) * ℓ) (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u)))‖ = 1 ∧ ∀ k < q, ‖coeff k (PowerSeries.subst (C (q : ℂ_[q]) * ℓ) (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u)))‖ < 1 := by
  intro d q _ M F hd hd16 hs hOK hM hF
  set U : ℂ_[q]⟦X⟧ := PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u) with hUdef
  have flow := uw_elliptic_flow q M hM
  have hU0 : constantCoeff U = 0 := by
    rw [hUdef, ← coeff_zero_eq_constantCoeff_apply, coeff_map, tay, coeff_mk]
    simp [flow.2.2.2.2.1]

  obtain ⟨ℓ, hchart, hℓX⟩ := Basic.exists_chart M hM
  have hℓ0 : constantCoeff ℓ = 0 := hchart.2.1
  have hUℓ : U.subst ℓ = X := hℓX
  obtain ⟨P1, P2, P3⟩ := GlobalTheory.T.formalGroup_padicMul_integral_vanishingOrder q F U ℓ hU0 hℓ0 hUℓ hF
  refine ⟨ℓ, hℓ0, hUℓ, ?_, ?_⟩
  ·

    have hle : ‖coeff q (U.subst (C (q : ℂ_[q]) * ℓ))‖ ≤ 1 := by
      have := P1 (q : ℤ_[q])
      rw [zc_natCast_eq] at this
      exact this q
    refine le_antisymm hle (not_lt.1 fun hlt => ?_)
    have P3' := P3 hlt
    set k : ℕ := d + 3 with hk
    obtain ⟨β, N, hβ, hβ0, hβn, hN, hNle⟩ := exists_small_in_prime_pow d q M.ι hd hd16 hs k
    have ar := okArith d q M.ι hd hd16 hs
    obtain ⟨a, ha⟩ := (ar.2.1 β hβ).1
    have hanorm : ‖a‖ ≤ (q : ℝ) ^ (-(k : ℤ)) := by
      rw [← norm_zc_eq, ← ha]
      exact hβn
    have hlat : ∀ l ∈ M.L.lattice, β * l ∈ M.L.lattice := by
      intro l hl
      rw [hOK] at hl ⊢
      exact (ar.1.2.2 β l hβ hl).2.1
    have hu0 : AnalyticAt ℂ M.u 0 := (flow.2.2.2.2.2.2.2.2 0 (Or.inl ((hOK 0).2 ⟨0, 0, by simp⟩))).1
    have hhat : hat M.ι ℓ (fun z => M.u (β * z)) = U.subst (C (zc a) * ℓ) := by
      rw [(TaylorRead.hat_laws q M.ι ℓ hℓ0).2.2.2.2.2.1 M.u β hu0, ← ha]
      rfl
    have hbd : Bd 1 (hat M.ι ℓ (fun z => M.u (β * z))) := by
      rw [hhat]
      exact P1 a
    obtain ⟨n, hnN, hn1⟩ := GlobalTheory.T.exists_unit_coeff_mul_series_le_norm q M ℓ β N hchart hβ0 hlat hN hbd
    have hnlt : n < (2 * q) ^ k := by
      have hq : 0 < q ^ k := pow_pos (Fact.out : q.Prime).pos k
      have h2 : d + 3 < 2 ^ k := Nat.lt_two_pow_self
      calc n ≤ N := hnN
        _ ≤ (d + 3) * q ^ k := hNle
        _ < 2 ^ k * q ^ k := Nat.mul_lt_mul_of_pos_right h2 hq
        _ = (2 * q) ^ k := (mul_pow 2 q k).symm
    have := P3' k a hanorm n hnlt
    rw [← hhat, hn1] at this
    exact lt_irrefl _ this
  · intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · have hc : constantCoeff (C (q : ℂ_[q]) * ℓ) = 0 := by simp [hℓ0]
      rw [coeff_zero_eq_constantCoeff_apply, TaylorRead.constantCoeff_subst_of hc, hU0, norm_zero]
      exact one_pos
    · exact P2 k (Nat.not_dvd_of_pos_of_lt hkpos hk)

end GlobalTheory.MomOne
end
end
