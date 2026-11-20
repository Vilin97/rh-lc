import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.EllipticFunctions
import GroundTheory.GlobalFields.ComplexMultiplication.EllipticRational
import GroundTheory.GlobalFields.ComplexMultiplication.EllipticDegree
import GroundTheory.GlobalFields.ComplexMultiplication.Uniformization

open Complex Filter Topology Set
open scoped PeriodPair

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

variable {L : PeriodPair}

lemma hasDerivAt_weierstrassP {z : ℂ} (hz : z ∉ L.lattice) : HasDerivAt ℘[L] (℘'[L] z) z := by
  have hd : DifferentiableAt ℂ ℘[L] z := (L.analyticOnNhd_weierstrassP z hz).differentiableAt
  have := hd.hasDerivAt
  rwa [L.deriv_weierstrassP] at this

lemma hasDerivAt_derivWeierstrassP {z : ℂ} (hz : z ∉ L.lattice) :
    HasDerivAt ℘'[L] (deriv ℘'[L] z) z :=
  (L.analyticOnNhd_derivWeierstrassP z hz).differentiableAt.hasDerivAt

theorem deriv_derivWeierstrassP {z : ℂ} (hz : z ∉ L.lattice) :
    deriv ℘'[L] z = 6 * ℘[L] z ^ 2 - L.g₂ / 2 := by
  have hopen : IsOpen (L.lattice : Set ℂ)ᶜ := L.isClosed_lattice.isOpen_compl
  have key : ∀ u ∉ L.lattice,
      ℘'[L] u * (2 * deriv ℘'[L] u - (12 * ℘[L] u ^ 2 - L.g₂)) = 0 := by
    intro u hu
    have h1 : HasDerivAt (℘'[L] ^ 2) (2 * ℘'[L] u * deriv ℘'[L] u) u :=
      ((hasDerivAt_derivWeierstrassP hu).pow 2).congr_deriv (by norm_num)
    have h2 : HasDerivAt (fun v ↦ 4 * ℘[L] v ^ 3 - L.g₂ * ℘[L] v - L.g₃)
        ((12 * ℘[L] u ^ 2 - L.g₂) * ℘'[L] u) u := by
      have hp := hasDerivAt_weierstrassP hu
      exact ((((hp.pow 3).const_mul 4).sub (hp.const_mul L.g₂)).sub_const L.g₃).congr_deriv
        (by norm_num; ring)
    have heq : (℘'[L] ^ 2) =ᶠ[𝓝 u]
        (fun v ↦ 4 * ℘[L] v ^ 3 - L.g₂ * ℘[L] v - L.g₃) := by
      filter_upwards [hopen.mem_nhds hu] with v hv
      exact L.derivWeierstrassP_sq v hv
    have := h1.unique (h2.congr_of_eventuallyEq heq)
    linear_combination this
  by_cases h0 : ℘'[L] z = 0
  · set D : ℂ → ℂ := fun u ↦ deriv ℘'[L] u - (6 * ℘[L] u ^ 2 - L.g₂ / 2) with hD
    have hDc : ContinuousAt D z := by
      have h1 := (L.analyticOnNhd_derivWeierstrassP z hz).deriv.continuousAt
      have h2 := (L.analyticOnNhd_weierstrassP z hz).continuousAt
      exact h1.sub (((h2.pow 2).const_mul 6).sub continuousAt_const)
    have hev : ∀ᶠ u in 𝓝[≠] z, D u = 0 := by
      filter_upwards [eventually_nhdsNE_of_eventually_codiscrete
        (eventually_codiscrete_derivWeierstrassP_ne_zero (L := L)) z,
        nhdsWithin_le_nhds (hopen.mem_nhds hz)] with u hu1 hu2
      rcases mul_eq_zero.1 (key u hu2) with h | h
      · exact absurd h hu1
      · simp only [hD]
        linear_combination h / 2
    have hlim := tendsto_nhds_unique (hDc.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' (hev.mono fun u hu ↦ hu.symm))
    simp only [hD] at hlim
    linear_combination hlim
  · rcases mul_eq_zero.1 (key z hz) with h | h
    · exact absurd h h0
    · linear_combination h / 2

theorem meromorphicOrderAt_nonneg_of_simple_pole {f : ℂ → ℂ} (hf : IsEllipticFunction L f)
    {p : ℂ} (hp : ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f p)
    (ho : ∀ z, z - p ∉ L.lattice → 0 ≤ meromorphicOrderAt f z) (z : ℂ) :
    0 ≤ meromorphicOrderAt f z := by
  have hdeg : degree L f ≤ 1 := by
    rw [degree, finsum_eq_single _ (Torus.mk L p) (fun x hx ↦ ?_)]
    · rw [torusOrder_mk hf]
      generalize meromorphicOrderAt f p = o at hp
      induction o with
      | top => simp
      | coe n =>
        simp only [WithTop.untopD_coe]
        have : (-1 : ℤ) ≤ n := by exact_mod_cast hp
        omega
    · obtain ⟨y, rfl⟩ := Torus.mk_surjective L x
      rw [torusOrder_mk hf]
      exact toNat_neg_untopD_eq_zero_of_nonneg
        (ho y fun h ↦ hx ((Torus.mk_eq_mk_iff L).2 h))
  have h0 : degree L f = 0 := by
    have := degree_ne_one hf
    omega
  have hall := eq_zero_of_finsum_eq_zero_nat (finite_support_toNat_neg_torusOrder hf) h0
    (Torus.mk L z)
  rw [torusOrder_mk hf] at hall
  exact nonneg_of_toNat_neg_untopD_eq_zero hall

lemma eq_of_eventuallyEq_nhdsNE {f g : ℂ → ℂ} {x : ℂ} (hf : ContinuousAt f x)
    (hg : ContinuousAt g x) (h : f =ᶠ[𝓝[≠] x] g) : f x = g x :=
  tendsto_nhds_unique (hf.tendsto.mono_left nhdsWithin_le_nhds)
    ((hg.tendsto.mono_left nhdsWithin_le_nhds).congr' h.symm)

variable (L) in

def chordSlope (z w : ℂ) : ℂ := (℘'[L] z - ℘'[L] w) / (℘[L] z - ℘[L] w)

lemma chordSlope_comm (z w : ℂ) : chordSlope L z w = chordSlope L w z := by
  rw [chordSlope, chordSlope, ← neg_div_neg_eq, neg_sub, neg_sub]

variable (L) in

def addDefect (w z : ℂ) : ℂ :=
  ℘[L] (z + w) + ℘[L] z + ℘[L] w - chordSlope L z w ^ 2 / 4

lemma weierstrassP_eq_except_zero (z : ℂ) : ℘[L] z = ℘[L - (0 : ℂ)] z + 1 / z ^ 2 := by
  have := L.weierstrassPExcept_def ⟨0, L.lattice.zero_mem⟩ z
  change ℘[L - (0 : ℂ)] z = ℘[L] z + (1 / (0 : ℂ) ^ 2 - 1 / (z - 0) ^ 2) at this
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero, zero_sub,
    sub_zero] at this
  rw [this]
  ring

lemma derivWeierstrassP_eq_except_zero (z : ℂ) :
    ℘'[L] z = ℘'[L - (0 : ℂ)] z - 2 / z ^ 3 := by
  have := L.derivWeierstrassPExcept_def ⟨0, L.lattice.zero_mem⟩ z
  change ℘'[L - (0 : ℂ)] z = ℘'[L] z + 2 / (z - 0) ^ 3 at this
  simp only [sub_zero] at this
  rw [this]
  ring

lemma meromorphic_weierstrassP_comp_add (w : ℂ) : Meromorphic fun z ↦ ℘[L] (z + w) := fun x ↦
  (L.meromorphic_weierstrassP (x + w)).comp_analyticAt (g := fun z ↦ z + w) (by fun_prop)

lemma analyticAt_weierstrassP_comp_add {x w : ℂ} (h : x + w ∉ L.lattice) :
    AnalyticAt ℂ (fun z ↦ ℘[L] (z + w)) x :=
  (L.analyticOnNhd_weierstrassP (x + w) h).comp (g := ℘[L]) (f := fun z ↦ z + w) (by fun_prop)

lemma isEllipticFunction_addDefect (w : ℂ) : IsEllipticFunction L (addDefect L w) := by sorry









lemma analyticAt_addDefect {w z : ℂ} (hw : w ∉ L.lattice) (hz : z ∉ L.lattice)
    (hzw : z - w ∉ L.lattice) (hzw' : z + w ∉ L.lattice) : AnalyticAt ℂ (addDefect L w) z := by
  have hne : ℘[L] z - ℘[L] w ≠ 0 := fun h ↦ by
    rcases sub_mem_or_add_mem_of_weierstrassP_eq hz hw (sub_eq_zero.1 h) with h' | h'
    · exact hzw h'
    · exact hzw' h'
  have h1 := analyticAt_weierstrassP_comp_add hzw'
  have h2 := L.analyticOnNhd_weierstrassP z hz
  have h3 := L.analyticOnNhd_derivWeierstrassP z hz
  unfold addDefect chordSlope
  apply AnalyticAt.sub (by fun_prop)
  apply AnalyticAt.div _ analyticAt_const (by norm_num)
  apply AnalyticAt.pow
  exact AnalyticAt.div (by fun_prop) (by fun_prop) hne

lemma addDefect_algebra_zero (u p q x y z : ℂ) (hz : z ≠ 0) (hB : z ^ 2 * (p - x) + 1 ≠ 0) :
    u + (p + 1 / z ^ 2) + x - ((q - 2 / z ^ 3 - y) / (p + 1 / z ^ 2 - x)) ^ 2 / 4 =
      u + x + p + (8 * (p - x) + 4 * z ^ 2 * (p - x) ^ 2 - z ^ 4 * (q - y) ^ 2 + 4 * z * (q - y)) /
        (4 * (z ^ 2 * (p - x) + 1) ^ 2) := by
  have h1 : p + 1 / z ^ 2 - x = (z ^ 2 * (p - x) + 1) / z ^ 2 := by field_simp; ring
  have h2 : q - 2 / z ^ 3 - y = (z ^ 3 * (q - y) - 2) / z ^ 3 := by field_simp; ring
  rw [h1, h2]
  field_simp
  ring

lemma addDefect_algebra_neg (a b c n u z w : ℂ) (ht : z - -w ≠ 0) (hu : u ≠ 0) :
    (z - -w) * (a + 1 / (z + w) ^ 2 + b + c - (n / ((z - -w) * u)) ^ 2 / 4) =
      (z - -w) * a + (z - -w) * (b + c) + (4 * u ^ 2 - n ^ 2) / (z - -w) / (4 * u ^ 2) := by
  rw [sub_neg_eq_add] at ht ⊢
  field_simp
  ring

lemma analyticAt_dslope {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) :
    AnalyticAt ℂ (dslope f a) a := by
  obtain ⟨p, hp⟩ := hf
  exact hp.has_fpower_series_dslope_fslope.analyticAt

lemma exists_analyticAt_addDefect_zero {w : ℂ} (hw : w ∉ L.lattice) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H 0 ∧ H 0 = 0 ∧ addDefect L w =ᶠ[𝓝[≠] 0] H := by sorry























lemma exists_analyticAt_addDefect_self {w : ℂ} (hw : w ∉ L.lattice) (h2w : 2 * w ∉ L.lattice) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H w ∧ addDefect L w =ᶠ[𝓝[≠] w] H := by
  have hpw : AnalyticAt ℂ ℘[L] w := L.analyticOnNhd_weierstrassP w hw
  have hdw : AnalyticAt ℂ ℘'[L] w := L.analyticOnNhd_derivWeierstrassP w hw
  have h1 := analyticAt_dslope hpw
  have h2 := analyticAt_dslope hdw
  have hne : dslope ℘[L] w w ≠ 0 := by
    rw [dslope_same, L.deriv_weierstrassP]
    exact fun h ↦ h2w ((two_mul_mem_lattice_iff_derivWeierstrassP_eq_zero hw).2 h)
  have hW := analyticAt_weierstrassP_comp_add (L := L) (x := w) (w := w) (by rwa [← two_mul])
  refine ⟨fun z ↦ ℘[L] (z + w) + ℘[L] z + ℘[L] w -
    (dslope ℘'[L] w z / dslope ℘[L] w z) ^ 2 / 4, ?_, ?_⟩
  · apply AnalyticAt.sub (by fun_prop)
    exact ((h2.div h1 hne).pow 2).div analyticAt_const (by norm_num)
  · filter_upwards [self_mem_nhdsWithin] with z hz
    simp only [addDefect, chordSlope]
    rw [dslope_of_ne _ hz, dslope_of_ne _ hz, slope_def_field, slope_def_field,
      div_div_div_cancel_right₀ (sub_ne_zero.2 hz)]

lemma neg_one_le_meromorphicOrderAt_addDefect_neg {w : ℂ} (hw : w ∉ L.lattice)
    (h2w : 2 * w ∉ L.lattice) :
    ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (addDefect L w) (-w) := by sorry
























































theorem weierstrassP_add_of_two_mul_notMem {z w : ℂ} (hw : w ∉ L.lattice)
    (h2w : 2 * w ∉ L.lattice) (hz : z ∉ L.lattice) (hzw : z - w ∉ L.lattice)
    (hzw' : z + w ∉ L.lattice) :
    ℘[L] (z + w) = chordSlope L z w ^ 2 / 4 - ℘[L] z - ℘[L] w := by sorry








































lemma add_add_eq_zero_of_roots {g₂ g₃ x₁ x₂ x₃ : ℂ} (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃)
    (h23 : x₂ ≠ x₃) (f1 : 4 * x₁ ^ 3 - g₂ * x₁ - g₃ = 0) (f2 : 4 * x₂ ^ 3 - g₂ * x₂ - g₃ = 0)
    (f3 : 4 * x₃ ^ 3 - g₂ * x₃ - g₃ = 0) : x₁ + x₂ + x₃ = 0 := by
  have s12 : 4 * (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2) = g₂ :=
    mul_left_cancel₀ (sub_ne_zero.2 h12) (by linear_combination f1 - f2)
  have s13 : 4 * (x₁ ^ 2 + x₁ * x₃ + x₃ ^ 2) = g₂ :=
    mul_left_cancel₀ (sub_ne_zero.2 h13) (by linear_combination f1 - f3)
  exact mul_left_cancel₀ (sub_ne_zero.2 h23) (by linear_combination (s12 - s13) / 4)

theorem weierstrassP_add {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (hzw : z - w ∉ L.lattice) (hzw' : z + w ∉ L.lattice) :
    ℘[L] (z + w) = chordSlope L z w ^ 2 / 4 - ℘[L] z - ℘[L] w := by
  by_cases h2w : 2 * w ∈ L.lattice
  · by_cases h2z : 2 * z ∈ L.lattice
    · have d1 := derivWeierstrassP_eq_zero_of_two_mul_mem h2z
      have d2 := derivWeierstrassP_eq_zero_of_two_mul_mem h2w
      have root : ∀ u ∉ L.lattice, 2 * u ∈ L.lattice →
          4 * ℘[L] u ^ 3 - L.g₂ * ℘[L] u - L.g₃ = 0 := fun u hu h2 ↦ by
        rw [← L.derivWeierstrassP_sq u hu, derivWeierstrassP_eq_zero_of_two_mul_mem h2]
        ring
      have hne : ∀ {a b : ℂ}, a ∉ L.lattice → b ∉ L.lattice → a - b ∉ L.lattice →
          a + b ∉ L.lattice → ℘[L] a ≠ ℘[L] b := fun ha hb h1 h2 h ↦
        (sub_mem_or_add_mem_of_weierstrassP_eq ha hb h).elim h1 h2
      have nz : -z ∉ L.lattice := fun h ↦ hz (by simpa using neg_mem h)
      have nw : -w ∉ L.lattice := fun h ↦ hw (by simpa using neg_mem h)
      have a1 : z - (z + w) ∉ L.lattice := by rwa [show z - (z + w) = -w by ring]
      have a2 : z + (z + w) ∉ L.lattice := fun h ↦ hw (by
        have := sub_mem h h2z
        rwa [show z + (z + w) - 2 * z = w by ring] at this)
      have a3 : w - (z + w) ∉ L.lattice := by rwa [show w - (z + w) = -z by ring]
      have a4 : w + (z + w) ∉ L.lattice := fun h ↦ hz (by
        have := sub_mem h h2w
        rwa [show w + (z + w) - 2 * w = z by ring] at this)
      have hs := add_add_eq_zero_of_roots (hne hz hw hzw hzw') (hne hz hzw' a1 a2)
        (hne hw hzw' a3 a4) (root z hz h2z) (root w hw h2w)
        (root _ hzw' (by rw [mul_add]; exact add_mem h2z h2w))
      rw [chordSlope, d1, d2, sub_self, zero_div]
      linear_combination hs
    · have hwz : w - z ∉ L.lattice := fun h ↦ hzw (by simpa using neg_mem h)
      have := weierstrassP_add_of_two_mul_notMem hz h2z hw hwz (by rwa [add_comm])
      rw [add_comm, chordSlope_comm] at this
      linear_combination this
  · exact weierstrassP_add_of_two_mul_notMem hw h2w hz hzw hzw'

lemma derivAdd_algebra (x₁ x₂ y₁ y₂ g₂ g₃ : ℂ) (hD : x₁ - x₂ ≠ 0)
    (E₁ : y₁ ^ 2 = 4 * x₁ ^ 3 - g₂ * x₁ - g₃) (E₂ : y₂ ^ 2 = 4 * x₂ ^ 3 - g₂ * x₂ - g₃) :
    2 * ((y₁ - y₂) / (x₁ - x₂)) *
        (((6 * x₁ ^ 2 - g₂ / 2) * (x₁ - x₂) - (y₁ - y₂) * y₁) / (x₁ - x₂) ^ 2) / 4 - y₁ =
      -((y₁ - y₂) / (x₁ - x₂) * (((y₁ - y₂) / (x₁ - x₂)) ^ 2 / 4 - x₁ - x₂ - x₁) + y₁) := by
  rw [← sub_eq_zero]
  have key : 2 * ((y₁ - y₂) / (x₁ - x₂)) *
        (((6 * x₁ ^ 2 - g₂ / 2) * (x₁ - x₂) - (y₁ - y₂) * y₁) / (x₁ - x₂) ^ 2) / 4 - y₁ -
      -((y₁ - y₂) / (x₁ - x₂) * (((y₁ - y₂) / (x₁ - x₂)) ^ 2 / 4 - x₁ - x₂ - x₁) + y₁) =
      (y₁ - y₂) / (4 * (x₁ - x₂) ^ 3) *
        ((y₂ ^ 2 - (4 * x₂ ^ 3 - g₂ * x₂ - g₃)) - (y₁ ^ 2 - (4 * x₁ ^ 3 - g₂ * x₁ - g₃))) := by
    field_simp
    ring
  rw [key, E₁, E₂]
  ring

theorem derivWeierstrassP_add {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (hzw : z - w ∉ L.lattice) (hzw' : z + w ∉ L.lattice) :
    ℘'[L] (z + w) = -(chordSlope L z w * (℘[L] (z + w) - ℘[L] z) + ℘'[L] z) := by
  have hopen : IsOpen {u : ℂ | u ∉ L.lattice ∧ u - w ∉ L.lattice ∧ u + w ∉ L.lattice} := by
    have h := L.isClosed_lattice.isOpen_compl
    exact h.inter ((h.preimage (continuous_sub_right w)).inter
      (h.preimage (continuous_add_const w)))
  have hne : ℘[L] z - ℘[L] w ≠ 0 := fun h ↦
    (sub_mem_or_add_mem_of_weierstrassP_eq hz hw (sub_eq_zero.1 h)).elim hzw hzw'
  have hL : HasDerivAt (fun u ↦ ℘[L] (u + w)) (℘'[L] (z + w)) z :=
    (hasDerivAt_weierstrassP hzw').comp_add_const z w
  have hp := hasDerivAt_weierstrassP hz
  have hd : HasDerivAt ℘'[L] (6 * ℘[L] z ^ 2 - L.g₂ / 2) z := by
    rw [← deriv_derivWeierstrassP hz]
    exact hasDerivAt_derivWeierstrassP hz
  have hm : HasDerivAt (fun u ↦ chordSlope L u w)
      (((6 * ℘[L] z ^ 2 - L.g₂ / 2) * (℘[L] z - ℘[L] w) - (℘'[L] z - ℘'[L] w) * ℘'[L] z) /
        (℘[L] z - ℘[L] w) ^ 2) z :=
    (hd.sub_const (℘'[L] w)).div (hp.sub_const (℘[L] w)) hne
  have hR : HasDerivAt (fun u ↦ chordSlope L u w ^ 2 / 4 - ℘[L] u - ℘[L] w)
      (2 * chordSlope L z w * (((6 * ℘[L] z ^ 2 - L.g₂ / 2) * (℘[L] z - ℘[L] w) -
        (℘'[L] z - ℘'[L] w) * ℘'[L] z) / (℘[L] z - ℘[L] w) ^ 2) / 4 - ℘'[L] z) z :=
    ((((hm.pow 2).div_const 4).sub hp).sub_const (℘[L] w)).congr_deriv (by norm_num)
  have heq : (fun u ↦ ℘[L] (u + w)) =ᶠ[𝓝 z]
      (fun u ↦ chordSlope L u w ^ 2 / 4 - ℘[L] u - ℘[L] w) := by
    filter_upwards [hopen.mem_nhds ⟨hz, hzw, hzw'⟩] with u hu
    exact weierstrassP_add hu.1 hw hu.2.1 hu.2.2
  rw [hL.unique (hR.congr_of_eventuallyEq heq), weierstrassP_add hz hw hzw hzw']
  simp only [chordSlope]
  exact derivAdd_algebra _ _ _ _ _ _ hne (L.derivWeierstrassP_sq z hz) (L.derivWeierstrassP_sq w hw)

variable (L) in

def tangentSlope (w : ℂ) : ℂ := (6 * ℘[L] w ^ 2 - L.g₂ / 2) / ℘'[L] w

lemma exists_continuousAt_chordSlope {w : ℂ} (hw : w ∉ L.lattice) (h2w : 2 * w ∉ L.lattice) :
    ∃ s : ℂ → ℂ, ContinuousAt s w ∧ s w = tangentSlope L w ∧
      ∀ᶠ z in 𝓝[≠] w, z ∉ L.lattice ∧ z - w ∉ L.lattice ∧ z + w ∉ L.lattice ∧
        chordSlope L z w = s z := by
  have hpw : AnalyticAt ℂ ℘[L] w := L.analyticOnNhd_weierstrassP w hw
  have hdw : AnalyticAt ℂ ℘'[L] w := L.analyticOnNhd_derivWeierstrassP w hw
  have hne : dslope ℘[L] w w ≠ 0 := by
    rw [dslope_same, L.deriv_weierstrassP]
    exact fun h ↦ h2w ((two_mul_mem_lattice_iff_derivWeierstrassP_eq_zero hw).2 h)
  refine ⟨fun z ↦ dslope ℘'[L] w z / dslope ℘[L] w z,
    ((analyticAt_dslope hdw).div (analyticAt_dslope hpw) hne).continuousAt, ?_, ?_⟩
  · simp only [dslope_same, L.deriv_weierstrassP, deriv_derivWeierstrassP hw, tangentSlope]
  · have h0 : (↑L.lattice \ {(0 : ℂ)})ᶜ ∈ 𝓝 (w - w) := by
      rw [sub_self]
      exact L.compl_lattice_sdiff_singleton_mem_nhds 0
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (L.isClosed_lattice.isOpen_compl.mem_nhds hw),
      nhdsWithin_le_nhds ((continuous_sub_right w).continuousAt.preimage_mem_nhds h0),
      nhdsWithin_le_nhds ((L.isClosed_lattice.isOpen_compl.preimage
        (continuous_add_const w)).mem_nhds (show w + w ∉ L.lattice by rwa [← two_mul]))]
      with z hz h1 h2 h3
    have hz' : z - w ≠ 0 := sub_ne_zero.2 hz
    refine ⟨h1, fun h ↦ h2 ⟨h, hz'⟩, h3, ?_⟩
    simp only [chordSlope]
    rw [dslope_of_ne _ hz, dslope_of_ne _ hz, slope_def_field, slope_def_field,
      div_div_div_cancel_right₀ hz']

theorem weierstrassP_two_mul {w : ℂ} (hw : w ∉ L.lattice) (h2w : 2 * w ∉ L.lattice) :
    ℘[L] (2 * w) = tangentSlope L w ^ 2 / 4 - 2 * ℘[L] w := by
  obtain ⟨s, hs, hsw, hev⟩ := exists_continuousAt_chordSlope hw h2w
  have hc : ContinuousAt (fun z ↦ ℘[L] (z + w)) w :=
    (analyticAt_weierstrassP_comp_add (show w + w ∉ L.lattice by rwa [← two_mul])).continuousAt
  have hg : ContinuousAt (fun z ↦ s z ^ 2 / 4 - ℘[L] z - ℘[L] w) w :=
    (((hs.pow 2).div_const 4).sub (L.analyticOnNhd_weierstrassP w hw).continuousAt).sub
      continuousAt_const
  have := eq_of_eventuallyEq_nhdsNE hc hg (hev.mono fun z ⟨h1, h2, h3, h4⟩ ↦ by
    simp only
    rw [weierstrassP_add h1 hw h2 h3, h4])
  simp only [hsw] at this
  rw [two_mul, this]
  ring

theorem derivWeierstrassP_two_mul {w : ℂ} (hw : w ∉ L.lattice) (h2w : 2 * w ∉ L.lattice) :
    ℘'[L] (2 * w) = -(tangentSlope L w * (℘[L] (2 * w) - ℘[L] w) + ℘'[L] w) := by
  obtain ⟨s, hs, hsw, hev⟩ := exists_continuousAt_chordSlope hw h2w
  have hww : w + w ∉ L.lattice := by rwa [← two_mul]
  have hc : ContinuousAt (fun z ↦ ℘'[L] (z + w)) w :=
    ((L.analyticOnNhd_derivWeierstrassP (w + w) hww).comp (g := ℘'[L]) (f := fun z ↦ z + w)
      (by fun_prop)).continuousAt
  have hc' : ContinuousAt (fun z ↦ ℘[L] (z + w)) w :=
    (analyticAt_weierstrassP_comp_add hww).continuousAt
  have hg : ContinuousAt (fun z ↦ -(s z * (℘[L] (z + w) - ℘[L] z) + ℘'[L] z)) w :=
    ((hs.mul (hc'.sub (L.analyticOnNhd_weierstrassP w hw).continuousAt)).add
      (L.analyticOnNhd_derivWeierstrassP w hw).continuousAt).neg
  have := eq_of_eventuallyEq_nhdsNE hc hg (hev.mono fun z ⟨h1, h2, h3, h4⟩ ↦ by
    simp only
    rw [derivWeierstrassP_add h1 hw h2 h3, h4])
  simp only [hsw] at this
  rw [two_mul, this]

end Elliptic
end GroundTheory.Global
