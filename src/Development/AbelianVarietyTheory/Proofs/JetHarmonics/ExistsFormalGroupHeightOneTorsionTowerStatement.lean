module

public import Development.AbelianVarietyTheory.Definitions.Jets.PowerSeriesHasSumAt
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormalGroupNatMulSeriesEvalOpenDiscProperties
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesIntegralBoundedClosureStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowerSeriesEvalTsumUnitDiscPropertiesStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PowerSeries.CoeffMulMem
public import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormalGroupNatMulSeriesPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesIntegralBoundedClosureStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowerSeriesEvalTsumUnitDiscPropertiesStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsRootOpenDiscOfWeierstrassDegree

section

@[expose] public section

open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer.DiscRoot

variable {K : Type} [NormedField K] [IsUltrametricDist K]

def ball (K : Type) [NormedField K] [IsUltrametricDist K] : Subring K where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq, norm_mul] at *
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := fun {a b} ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := fun {a} ha => by simpa using ha

theorem mem_span_pow (p x : ball K) (n : ℕ) :
    x ∈ Ideal.span {p} ^ n ↔ ‖(x : K)‖ ≤ ‖(p : K)‖ ^ n := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨a, rfl⟩
    have ha : ‖(a : K)‖ ≤ 1 := a.2
    simp only [Subring.coe_mul, SubmonoidClass.coe_pow, norm_mul, norm_pow]
    exact mul_le_of_le_one_left (by positivity) ha
  · intro h
    by_cases hp : (p : K) ^ n = 0
    · rw [← norm_pow, hp, norm_zero, norm_le_zero_iff] at h
      exact ⟨0, Subtype.ext (by simp [h])⟩
    · refine ⟨⟨x / p ^ n, ?_⟩, Subtype.ext ?_⟩
      · change ‖(x : K) / p ^ n‖ ≤ 1
        rw [norm_div, norm_pow]
        exact div_le_one_of_le₀ h (by positivity)
      · simp only [Subring.coe_mul, SubmonoidClass.coe_pow]
        exact div_mul_cancel₀ _ hp

theorem smod_iff (p x y : ball K) (n : ℕ) :
    x ≡ y [SMOD (Ideal.span {p} ^ n • ⊤ : Submodule (ball K) (ball K))] ↔
      ‖(x : K) - y‖ ≤ ‖(p : K)‖ ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, mem_span_pow]
  rfl

theorem adicComplete [CompleteSpace K] (p : ball K) (hp : ‖(p : K)‖ < 1) :
    IsAdicComplete (Ideal.span {p}) (ball K) := by
  have ht : Filter.Tendsto (fun n : ℕ => ‖(p : K)‖ ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hp
  have hH : IsHausdorff (Ideal.span {p}) (ball K) := ⟨fun x hx => by
    have : ‖(x : K)‖ ≤ 0 := ge_of_tendsto' ht fun n => by
      simpa using (smod_iff p x 0 n).1 (hx n)
    exact Subtype.ext (by simpa using this)⟩
  have hP : IsPrecomplete (Ideal.span {p}) (ball K) := ⟨fun f hf => by
    have hc : CauchySeq fun n => (f n : K) := by
      refine cauchySeq_of_le_tendsto_0' (fun n => ‖(p : K)‖ ^ n) (fun n m hnm => ?_) ht
      rw [dist_eq_norm]
      exact (smod_iff p _ _ n).1 (hf hnm)
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
    have hL1 : ‖L‖ ≤ 1 := le_of_tendsto' hL.norm fun n => (f n).2
    refine ⟨⟨L, hL1⟩, fun n => (smod_iff p _ _ n).2 ?_⟩
    refine le_of_tendsto ((tendsto_const_nhds (x := (f n : K))).sub hL).norm ?_
    filter_upwards [Filter.eventually_ge_atTop n] with m hm
    exact (smod_iff p _ _ n).1 (hf hm)⟩
  exact { toIsHausdorff := hH, toIsPrecomplete := hP }

theorem division [CompleteSpace K] (h : PowerSeries K) (d : ℕ) (hd : 0 < d)
    (hi : ∀ n, ‖PowerSeries.coeff n h‖ ≤ 1) (h1 : ‖PowerSeries.coeff d h‖ = 1)
    (hl : ∀ k < d, ‖PowerSeries.coeff k h‖ < 1) :
    ∃ (q : PowerSeries K) (r : Polynomial K), (∀ n, ‖PowerSeries.coeff n q‖ ≤ 1) ∧
      ‖PowerSeries.coeff 0 q‖ = 1 ∧ r.degree < d ∧ (∀ n, ‖r.coeff n‖ < 1) ∧
      PowerSeries.X ^ d = h * q + (r : PowerSeries K) := by
  obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image (Finset.range d)
    (fun k => ‖PowerSeries.coeff k h‖) ⟨0, Finset.mem_range.2 hd⟩
  let g : PowerSeries (ball K) := PowerSeries.mk fun n => ⟨PowerSeries.coeff n h, hi n⟩
  have hg : ∀ n, ((PowerSeries.coeff n g : ball K) : K) = PowerSeries.coeff n h := fun n => by
    simp [g]
  let p : ball K := PowerSeries.coeff k g
  have hp : ‖(p : K)‖ < 1 := by rw [hg]; exact hl k (Finset.mem_range.1 hk)
  set I : Ideal (ball K) := Ideal.span {p} with hI
  have hmem : ∀ x : ball K, x ∈ I ↔ ‖(x : K)‖ ≤ ‖(p : K)‖ := fun x => by
    simpa using mem_span_pow p x 1
  have hlow : ∀ j < d, PowerSeries.coeff j g ∈ I := fun j hj => by
    rw [hmem, hg, hg]; exact hmax j (Finset.mem_range.2 hj)
  have hord : (g.map (Ideal.Quotient.mk I)).order = d := by
    rw [PowerSeries.order_eq_nat]
    refine ⟨?_, fun i hi => ?_⟩
    · rw [PowerSeries.coeff_map, Ne, Ideal.Quotient.eq_zero_iff_mem, hmem, hg, h1]
      exact not_le.2 hp
    · rw [PowerSeries.coeff_map, Ideal.Quotient.eq_zero_iff_mem]
      exact hlow i hi
  have hord' : (g.map (Ideal.Quotient.mk I)).order.toNat = d := by rw [hord]; rfl
  have H : g.IsWeierstrassDivisorAt I := by
    rw [PowerSeries.IsWeierstrassDivisorAt, hord']
    have h0 : PowerSeries.coeff d h ≠ 0 := by
      intro h0; rw [h0, norm_zero] at h1; exact zero_ne_one h1
    refine IsUnit.of_mul_eq_one ⟨(PowerSeries.coeff d h)⁻¹, ?_⟩ (Subtype.ext ?_)
    · change ‖(PowerSeries.coeff d h)⁻¹‖ ≤ 1
      rw [norm_inv, h1, inv_one]
    · rw [Subring.coe_mul, hg]
      exact mul_inv_cancel₀ h0
  haveI := adicComplete p hp
  have HD := H.isWeierstrassDivisionAt_div_mod (PowerSeries.X ^ d)
  set q := H.div (PowerSeries.X ^ d)
  set r := H.mod (PowerSeries.X ^ d)
  have hdeg : r.degree < d := hord' ▸ HD.degree_lt
  have hgh : g.map (ball K).subtype = h := by
    ext n; simp [hg]
  refine ⟨q.map (ball K).subtype, r.map (ball K).subtype, fun n => ?_, ?_,
    lt_of_le_of_lt (Polynomial.degree_map_le) hdeg, fun n => ?_, ?_⟩
  · rw [PowerSeries.coeff_map]; exact (PowerSeries.coeff n q).2
  · have e := congrArg (PowerSeries.coeff d) HD.eq_mul_add
    rw [g.eq_X_pow_mul_shift_add_trunc d, add_mul, mul_assoc, map_add (f := _), map_add (f := _),
      PowerSeries.coeff_X_pow_self, Polynomial.coeff_coe,
      Polynomial.coeff_eq_zero_of_degree_lt hdeg, add_zero, PowerSeries.coeff_X_pow_mul',
      if_pos le_rfl, Nat.sub_self, PowerSeries.coeff_mul] at e
    rw [Finset.Nat.antidiagonal_zero, Finset.sum_singleton] at e
    have e2 : PowerSeries.coeff d (((g.trunc d : Polynomial (ball K)) : PowerSeries (ball K)) * q) ∈ I := by
      refine PowerSeries.coeff_mul_mem_ideal_of_coeff_left_mem_ideal' (fun i => ?_) d
      rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
      split_ifs with hh
      · exact hlow i hh
      · exact zero_mem _
    have e3 := ((hmem _).1 e2).trans_lt hp
    have e4 := congrArg (fun z : ball K => (z : K)) e
    simp only [PowerSeries.coeff_mk, zero_add, Subring.coe_add, Subring.coe_mul, hg, OneMemClass.coe_one] at e4
    rw [PowerSeries.coeff_map]
    refine le_antisymm (PowerSeries.coeff 0 q).2 (not_lt.1 fun hlt => ?_)
    have e5 := congrArg norm e4
    rw [norm_one] at e5
    refine absurd (e5.le.trans (IsUltrametricDist.norm_add_le_max _ _)) (not_le.2 (max_lt ?_ e3))
    rw [norm_mul, h1, one_mul]
    exact hlt
  · rw [Polynomial.coeff_map]
    by_cases hn : n < d
    · have := HD.coeff_f_sub_r_mem (i := n) (hord'.symm ▸ hn)
      rw [map_sub, PowerSeries.coeff_X_pow, if_neg hn.ne, zero_sub, neg_mem_iff,
        Polynomial.coeff_coe] at this
      exact ((hmem _).1 this).trans_lt hp
    · rw [Polynomial.coeff_eq_zero_of_degree_lt (hdeg.trans_le (by exact_mod_cast not_lt.1 hn))]
      simp
  · have := congrArg (PowerSeries.map (ball K).subtype) HD.eq_mul_add
    rw [map_pow, PowerSeries.map_X, map_add (f := _), map_mul, hgh] at this
    rw [this, Polynomial.polynomial_map_coe]

theorem root_small [IsAlgClosed K] (r : Polynomial K) (d : ℕ) (hd : 0 < d) (hr : r.degree < d)
    (hc : ∀ n, ‖r.coeff n‖ < 1) : ∃ x : K, ‖x‖ < 1 ∧ (Polynomial.X ^ d - r).eval x = 0 := by
  have hdeg : (Polynomial.X ^ d - r).degree = (d : WithBot ℕ) := by
    rw [Polynomial.degree_sub_eq_left_of_degree_lt (by rwa [Polynomial.degree_X_pow]),
      Polynomial.degree_X_pow]
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (Polynomial.X ^ d - r)
    (by rw [hdeg]; exact_mod_cast hd.ne')
  refine ⟨x, not_le.1 fun h1 => ?_, hx⟩
  have e : x ^ d = ∑ i ∈ Finset.range d, r.coeff i * x ^ i := by
    have := hx.eq_zero
    rw [Polynomial.eval_sub, sub_eq_zero, Polynomial.eval_pow, Polynomial.eval_X] at this
    rw [this]
    by_cases h0 : r = 0
    · simp [h0]
    exact Polynomial.eval_eq_sum_range' ((Polynomial.natDegree_lt_iff_degree_lt h0).2 hr) x
  obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty
    (t := Finset.range d) ⟨0, Finset.mem_range.2 hd⟩ (fun i => r.coeff i * x ^ i)
  rw [← e, norm_mul, norm_pow, norm_pow] at hle
  have h2 : ‖x‖ ^ i ≤ ‖x‖ ^ d := pow_le_pow_right₀ h1 (Finset.mem_range.1 hi).le
  have h3 : 0 < ‖x‖ ^ i := by positivity
  have h4 := hc i
  nlinarith

end GlobalTheory.ConvSer.DiscRoot

theorem GlobalTheory.ConvSer.exists_root_of_weierstrassDegree : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [IsAlgClosed K] (h : PowerSeries K) (d : ℕ), 0 < d → Intg h → ‖PowerSeries.coeff d h‖ = 1 → (∀ k < d, ‖PowerSeries.coeff k h‖ < 1) → ∃ x : K, ‖x‖ < 1 ∧ ev1 h x = 0 := by
  intro K _ _ _ _ h d hd hi h1 hl
  obtain ⟨-, -, hA, -, -, -, -, -, -, hB⟩ := GlobalTheory.T.mvPowerSeries_integral_bounded_closure K Unit
  obtain ⟨q, r, hq, hq0, hr, hrc, e⟩ := DiscRoot.division h d hd ((hB h).1.1 hi) h1 hl
  obtain ⟨x, hx, hx0⟩ := DiscRoot.root_small r d hd hr hrc
  refine ⟨x, hx, ?_⟩
  obtain ⟨-, hmul, -, -, hP, -, hI, -⟩ := GlobalTheory.T.powerSeriesEvalTsum_unitDisc_properties_alt K x hx
  have hq' : Intg q := (hB q).1.2 hq
  have e2 : ((Polynomial.X ^ d - r : Polynomial K) : PowerSeries K) = h * q := by
    rw [Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_X, e]; ring
  have e3 := (hP (Polynomial.X ^ d - r)).2
  rw [hx0, e2, (hmul h q ((hA h 0).2.2 hi) ((hA q 0).2.2 hq')).2.2] at e3
  refine (mul_eq_zero.1 e3).resolve_right fun h0 => ?_
  have := (hI q hq').2.1
  rw [h0, zero_sub, norm_neg, hq0] at this
  exact absurd hx (not_lt.2 this)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsRootOpenDiscOfWeierstrassDegreeStatement

section

@[expose] public section

open GlobalTheory.ConvSer

theorem _root_.GlobalTheory.T.exists_root_openDisc_of_weierstrassDegree : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [IsAlgClosed K] (h : PowerSeries K) (d : ℕ), 0 < d → Intg h → ‖PowerSeries.coeff d h‖ = 1 → (∀ k < d, ‖PowerSeries.coeff k h‖ < 1) → ∃ x : K, ‖x‖ < 1 ∧ ev1 h x = 0 := by
  first | exact @GlobalTheory.ConvSer.exists_root_of_weierstrassDegree | exact GlobalTheory.ConvSer.exists_root_of_weierstrassDegree | (intros; apply GlobalTheory.ConvSer.exists_root_of_weierstrassDegree <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFormalGroupHeightOneTorsionTower

section

@[expose] public section

open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer

theorem intg_nMul_of_intg (K : Type) [NormedField K] [IsUltrametricDist K] (F : FormalGroup K)
    (hF : Intg F.toPowerSeries) (n : ℕ) : Intg (nMul F n) := by
  apply GlobalTheory.ConvSer.intg_nMul_for_point <;> assumption

theorem exists_torsion_tower (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [IsAlgClosed K] [CharZero K] (p : ℕ) [Fact p.Prime] (F : FormalGroup K)
    (hF : Intg F.toPowerSeries) (hp : ‖PowerSeries.coeff p (nMul F p)‖ = 1)
    (hlt : ∀ k < p, ‖PowerSeries.coeff k (nMul F p)‖ < 1) :
    ∃ t : ℕ → K, (∀ n, ‖t n‖ < 1) ∧ t 0 = 0 ∧ t 1 ≠ 0 ∧
      ∀ n, ev1 (nMul F p) (t (n + 1)) = t n := by
  classical
  have hpr : p.Prime := Fact.out
  have hI := intg_nMul_of_intg K F hF p
  set h := nMul F p with hh
  obtain ⟨-, -, hpow, -, -, -, -, -, -, hiff⟩ := GlobalTheory.T.mvPowerSeries_integral_bounded_closure K Unit
  have hev := fun (x : K) (hx : ‖x‖ < 1) => GlobalTheory.T.powerSeriesEvalTsum_unitDisc_properties_alt K x hx
  have hbdd : ∀ f : PowerSeries K, Intg f → Bdd f := fun f hf => (hpow f 0).2.2 hf
  have hcoef : ∀ n, ‖PowerSeries.coeff n h‖ ≤ 1 := (hiff h).1.1 hI
  have h0 : PowerSeries.coeff 0 h = 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact ((GlobalTheory.T.formalGroupNatMulSeries_properties K F).1 p).1
  have h0c : PowerSeries.constantCoeff h = 0 := ((GlobalTheory.T.formalGroupNatMulSeries_properties K F).1 p).1
  have h1 : PowerSeries.coeff 1 h = (p : K) := ((GlobalTheory.T.formalGroupNatMulSeries_properties K F).1 p).2
  have hp0 : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hpr.ne_zero
  have hz : ‖(0 : K)‖ < 1 := by simp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hzero⟩ := hev 0 hz

  have hstep : ∀ c : {c : K // ‖c‖ < 1}, ∃ y : {y : K // ‖y‖ < 1}, ev1 h y = c := by
    rintro ⟨c, hc⟩
    have hIc : Intg (h - PowerSeries.C c) := by
      rw [(hiff _).1]
      intro n
      rcases n with _ | n
      · simp [h0c, hc.le]
      · rw [map_sub, PowerSeries.coeff_C, if_neg (Nat.succ_ne_zero n), sub_zero]
        exact hcoef _
    obtain ⟨y, hy, hy0⟩ := GlobalTheory.T.exists_root_openDisc_of_weierstrassDegree K (h - PowerSeries.C c) p hpr.pos hIc (by
        rw [map_sub, PowerSeries.coeff_C, if_neg hpr.ne_zero, sub_zero]
        exact hp) (by
        intro k hk
        rcases k with _ | k
        · simpa [h0, h0c] using hc
        · rw [map_sub, PowerSeries.coeff_C, if_neg (Nat.succ_ne_zero k), sub_zero]
          exact hlt _ hk)
    refine ⟨⟨y, hy⟩, ?_⟩
    obtain ⟨-, hops, hCe, -⟩ := hev y hy
    have hCI : Intg (PowerSeries.C c) := by
      rw [(hiff _).1]
      intro n
      rw [PowerSeries.coeff_C]
      split_ifs
      · exact hc.le
      · simp
    have e := (hops h (PowerSeries.C c) (hbdd h hI) (hbdd _ hCI)).2.1
    rw [hy0, hCe] at e
    simp only
    linear_combination -e

  set g : PowerSeries K := PowerSeries.mk fun k => PowerSeries.coeff (k + 1) h with hg
  have hgI : Intg g := by
    rw [(hiff _).1]
    intro n
    rw [hg, PowerSeries.coeff_mk]
    exact hcoef _
  have hp1 : 0 < p - 1 := by have := hpr.two_le; omega
  obtain ⟨x, hx, hx0⟩ := GlobalTheory.T.exists_root_openDisc_of_weierstrassDegree K g (p - 1) hp1 hgI (by
      rw [hg, PowerSeries.coeff_mk, Nat.sub_add_cancel hpr.one_lt.le]
      exact hp) (by
      intro k hk
      rw [hg, PowerSeries.coeff_mk]
      exact hlt _ (by omega))
  have hxne : x ≠ 0 := by
    rintro rfl
    rw [hzero, hg, PowerSeries.coeff_mk, h1] at hx0
    exact hp0 hx0
  have hXI : Intg (PowerSeries.X : PowerSeries K) := by
    rw [(hiff _).1]
    intro n
    rw [PowerSeries.coeff_X]
    split_ifs <;> simp
  have hXg : h = PowerSeries.X * g := by
    ext n
    rcases n with _ | n
    · simp [h0]
    · rw [PowerSeries.coeff_succ_X_mul, hg, PowerSeries.coeff_mk]
  have hxroot : ev1 h x = 0 := by
    obtain ⟨-, hops, -, hXe, -⟩ := hev x hx
    rw [hXg, ((hops _ _ (hbdd _ hXI) (hbdd _ hgI)).2.2), hXe, hx0, mul_zero]
  choose f hf using hstep
  let x0 : {y : K // ‖y‖ < 1} := ⟨x, hx⟩
  refine ⟨fun n => if n = 0 then 0 else ((f^[n - 1] x0 : {y : K // ‖y‖ < 1}) : K), ?_, ?_, ?_, ?_⟩
  · intro n
    dsimp only
    split_ifs
    · exact hz
    · exact (f^[n - 1] x0).2
  · simp
  · simpa [x0] using hxne
  · intro n
    rcases n with _ | m
    · simpa [x0] using hxroot
    · simp only [Nat.add_sub_cancel, if_neg (Nat.succ_ne_zero _), Function.iterate_succ_apply']
      exact hf _

end GlobalTheory.ConvSer
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFormalGroupHeightOneTorsionTowerStatement

section

@[expose] public section

open GlobalTheory.ConvSer

theorem _root_.GlobalTheory.T.exists_formalGroup_heightOne_torsion_tower : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [IsAlgClosed K] [CharZero K] (p : ℕ) [Fact p.Prime] (F : FormalGroup K), Intg F.toPowerSeries → ‖PowerSeries.coeff p (nMul F p)‖ = 1 → (∀ k < p, ‖PowerSeries.coeff k (nMul F p)‖ < 1) → ∃ t : ℕ → K, (∀ n, ‖t n‖ < 1) ∧ t 0 = 0 ∧ t 1 ≠ 0 ∧ ∀ n, ev1 (nMul F p) (t (n + 1)) = t n := by
  first | exact @GlobalTheory.ConvSer.exists_torsion_tower | exact GlobalTheory.ConvSer.exists_torsion_tower | (intros; apply GlobalTheory.ConvSer.exists_torsion_tower <;> assumption)
end
end
