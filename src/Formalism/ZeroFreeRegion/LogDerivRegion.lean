module

public import Formalism.ZeroFreeRegion.SmallHeightLogDeriv
public import Formalism.ZeroFreeRegion.FinalZFR
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.GzPNTOf
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.LogDerivRegionOf
import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.LogDerivRight
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.Perron
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.RectDoublePole
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
public import Mathlib.NumberTheory.LSeries.Nonvanishing
import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZetaGrowth
import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZetaInvBound

-- Source module: Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.LaurentAtOne

section

@[expose] public section

open Complex Set Filter Topology

noncomputable section

namespace Formalism.ZF

def laHfun (y : ℝ) (s : ℂ) : ℂ :=
  (1 - (s - 1) * (deriv riemannZeta₁ s / riemannZeta₁ s)) * ((y : ℂ) ^ s / s)

def laU : Set ℂ := {s | riemannZeta₁ s ≠ 0} ∩ {s | s ≠ 0}

theorem laU_open : IsOpen laU :=
  (isOpen_ne_fun differentiable_riemannZeta₁.continuous continuous_const).inter isOpen_ne

theorem one_mem_laU : (1 : ℂ) ∈ laU := by simp [laU]

theorem laH_diffOn (y : ℝ) (hy : 0 < y) : DifferentiableOn ℂ (laHfun y) laU := by
  intro s hs
  have hZ : riemannZeta₁ s ≠ 0 := hs.1
  have h0 : s ≠ 0 := hs.2
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  apply DifferentiableAt.differentiableWithinAt
  have hd : DifferentiableAt ℂ (deriv riemannZeta₁) s := differentiable_riemannZeta₁.deriv s
  have hz : DifferentiableAt ℂ riemannZeta₁ s := differentiable_riemannZeta₁ s
  have hc : DifferentiableAt ℂ (fun s : ℂ => (y : ℂ) ^ s) s :=
    differentiableAt_id.const_cpow (Or.inl hy0)
  exact ((differentiableAt_const _).sub ((differentiableAt_id.sub_const 1).mul
    (hd.div hz hZ))).mul (hc.div differentiableAt_id h0)

theorem laH_one (y : ℝ) : laHfun y 1 = y := by simp [laHfun]

theorem laH_deriv_one (y : ℝ) (hy : 0 < y) :
    deriv (laHfun y) 1 = (y : ℂ) * Real.log y - (1 + Real.eulerMascheroniConstant) * y := by
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hB : DifferentiableAt ℂ (fun s => deriv riemannZeta₁ s / riemannZeta₁ s) 1 :=
    (differentiable_riemannZeta₁.deriv 1).div (differentiable_riemannZeta₁ 1) (by simp)
  have hk := (((hasDerivAt_id' (1 : ℂ)).sub_const 1).mul hB.hasDerivAt).const_sub 1
  have hc : HasDerivAt (fun s : ℂ => (y : ℂ) ^ s) ((y : ℂ) ^ (1 : ℂ) * Complex.log y) 1 := by
    simpa using (hasStrictDerivAt_const_cpow (x := (y : ℂ)) (y := 1) (Or.inl hy0)).hasDerivAt
  have hg := hc.div (hasDerivAt_id' (1 : ℂ)) one_ne_zero
  have hh := hk.mul hg
  have hh' : HasDerivAt (laHfun y) _ 1 := hh
  rw [hh'.deriv]
  rw [← Complex.ofReal_log hy.le]
  simp
  ring

theorem laurentExpansionAtOne : LaurentAtOne := by
  intro y hy
  set h := laHfun y with hdef
  have hn : laU ∈ 𝓝 (1 : ℂ) := laU_open.mem_nhds one_mem_laU
  refine ⟨dslope (dslope h 1) 1, ?_, ?_⟩
  · have h1 : DifferentiableOn ℂ (dslope (dslope h 1) 1) laU :=
      (differentiableOn_dslope hn).2 ((differentiableOn_dslope hn).2 (laH_diffOn y hy))
    exact h1.differentiableAt hn
  · have hU : ∀ᶠ w in 𝓝[≠] (1 : ℂ), w ∈ laU := nhdsWithin_le_nhds hn
    filter_upwards [log_deriv_riemannZeta_eq_neg_inv_sub_add, hU, self_mem_nhdsWithin]
      with w hw hwU hw1
    have hw1' : w - 1 ≠ 0 := sub_ne_zero.2 hw1
    have hw0 : w ≠ 0 := hwU.2
    have e1 := sub_smul_dslope h 1 w
    have e2 := sub_smul_dslope (dslope h 1) 1 w
    rw [dslope_same] at e2
    simp only [smul_eq_mul] at e1 e2
    rw [hdef, laH_deriv_one y hy] at e2
    rw [hdef, laH_one y] at e1
    have hhw : laHfun y w =
        (1 - (w - 1) * (deriv riemannZeta₁ w / riemannZeta₁ w)) * ((y : ℂ) ^ w / w) := rfl
    unfold Fy
    rw [hw]
    rw [hdef] at *
    generalize deriv riemannZeta₁ w / riemannZeta₁ w = B at hhw ⊢
    generalize (y : ℂ) ^ w = P at hhw ⊢
    generalize dslope (dslope (laHfun y) 1) 1 w = q at e2 ⊢
    generalize dslope (laHfun y) 1 w = D at e1 e2
    generalize laHfun y w = H at e1 hhw
    have key : (1 - (w - 1) * B) * (P / w) =
        y + (w - 1) * (((y : ℂ) * Real.log y - (1 + Real.eulerMascheroniConstant) * y)
          + (w - 1) * q) := by
      rw [← hhw]; linear_combination -e1 - (w - 1) * e2
    have lhs : -(-(w - 1)⁻¹ + B) * P / (w * (w - 1)) =
        (1 - (w - 1) * B) * (P / w) / (w - 1) ^ 2 := by
      field_simp
      ring
    rw [lhs, key]
    field_simp
    ring

end Formalism.ZF
end
end
end

-- Source module: Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.RectShiftOf

section

@[expose] public section

open Complex Filter Topology

noncomputable section

namespace Formalism.ZF

lemma rso_zeta_ne_near_one : ∀ᶠ w in 𝓝 (1 : ℂ), w ≠ 1 → riemannZeta w ≠ 0 := by
  have h := riemannZeta_residue_one.eventually (eventually_ne_nhds (one_ne_zero : (1 : ℂ) ≠ 0))
  rw [eventually_nhdsWithin_iff] at h
  filter_upwards [h] with w hw hw1 hz
  exact hw hw1 (by rw [hz, mul_zero])

lemma rso_deriv_zeta_diff : DifferentiableOn ℂ (deriv riemannZeta) {w : ℂ | w ≠ 1} := by
  have hd : DifferentiableOn ℂ riemannZeta {w : ℂ | w ≠ 1} :=
    fun w hw => (differentiableAt_riemannZeta hw).differentiableWithinAt
  exact hd.deriv isOpen_ne

lemma rso_Fy_diff (y : ℝ) (hy : 0 < y) {w : ℂ} (h0 : w ≠ 0) (h1 : w ≠ 1)
    (hz : riemannZeta w ≠ 0) : DifferentiableAt ℂ (Fy y) w := by
  have hd1 : DifferentiableAt ℂ (deriv riemannZeta) w :=
    rso_deriv_zeta_diff.differentiableAt (isOpen_ne.mem_nhds h1)
  have hd2 : DifferentiableAt ℂ riemannZeta w := differentiableAt_riemannZeta h1
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hd3 : DifferentiableAt ℂ (fun s : ℂ => (y : ℂ) ^ s) w :=
    (differentiableAt_id).const_cpow (Or.inl hy0)
  have hden : w * (w - 1) ≠ 0 := mul_ne_zero h0 (sub_ne_zero.2 h1)
  unfold Fy
  exact (((hd1.div hd2 hz).neg).mul hd3).div (differentiableAt_id.mul (differentiableAt_id.sub_const 1)) hden

theorem rectangleShiftOfResidue : RectShiftOf := by
  intro hRDP hLA y hy σ₁ σ₀ T h1 h2 h3 hT hz
  obtain ⟨A, hA1, hAev⟩ := hLA y hy
  set a : ℂ := (y : ℂ) with ha
  set b : ℂ := (y : ℂ) * Real.log y - (1 + Real.eulerMascheroniConstant) * y with hb
  let H : ℂ → ℂ := fun w => Fy y w - a / (w - 1) ^ 2 - b / (w - 1)
  let G : ℂ → ℂ := fun w => if w = 1 then A 1 else H w
  have hH : ∀ z : ℂ, z ≠ 0 → z ≠ 1 → riemannZeta z ≠ 0 → DifferentiableAt ℂ H z := by
    intro z hz0 hz1 hzz
    have hzm : z - 1 ≠ 0 := sub_ne_zero.2 hz1
    exact ((rso_Fy_diff y hy hz0 hz1 hzz).sub
      ((differentiableAt_const a).div ((differentiableAt_id.sub_const 1).pow 2) (pow_ne_zero 2 hzm))).sub
      ((differentiableAt_const b).div (differentiableAt_id.sub_const 1) hzm)
  have hG : ∀ z : ℂ, z ≠ 0 → z ≠ 1 → riemannZeta z ≠ 0 → DifferentiableAt ℂ G z := by
    intro z hz0 hz1 hzz
    refine (hH z hz0 hz1 hzz).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ne.mem_nhds hz1] with w hw
    simp [G, hw]
  have hev := hAev
  rw [eventually_nhdsWithin_iff] at hev
  have hG1 : DifferentiableAt ℂ G 1 := by
    refine hA1.congr_of_eventuallyEq ?_
    filter_upwards [hev] with w hw
    by_cases hw1 : w = 1
    · subst hw1; simp [G]
    · have hw' := hw hw1
      simp only [G, H, if_neg hw1]
      rw [hw']
      ring
  set U : Set ℂ := {w | ∀ᶠ z in 𝓝 w, DifferentiableAt ℂ G z} with hU
  have hUo : IsOpen U := isOpen_setOf_eventually_nhds
  have hUd : DifferentiableOn ℂ G U := fun w hw => (hw.self_of_nhds).differentiableWithinAt
  have h01 : ∀ᶠ z in 𝓝 (1 : ℂ), z ≠ 0 := eventually_ne_nhds one_ne_zero
  have hsub : (Set.uIcc σ₁ σ₀ ×ℂ Set.uIcc (-T) T) ⊆ U := by
    intro w hw
    rw [Complex.mem_reProdIm, Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)] at hw
    obtain ⟨⟨hr1, hr2⟩, hi1, hi2⟩ := hw
    have hw0 : w ≠ 0 := by
      intro h; rw [h] at hr1; simp at hr1; linarith
    by_cases hw1 : w = 1
    · subst hw1
      show ∀ᶠ z in 𝓝 (1 : ℂ), DifferentiableAt ℂ G z
      filter_upwards [rso_zeta_ne_near_one, h01] with z hz1 hz0
      by_cases hz1' : z = 1
      · subst hz1'; exact hG1
      · exact hG z hz0 hz1' (hz1 hz1')
    · have hzw : riemannZeta w ≠ 0 := hz w hr1 hr2 (abs_le.2 ⟨hi1, hi2⟩) hw1
      have hc : ContinuousAt riemannZeta w := (differentiableAt_riemannZeta hw1).continuousAt
      show ∀ᶠ z in 𝓝 w, DifferentiableAt ℂ G z
      filter_upwards [hc.eventually_ne hzw, isOpen_ne.mem_nhds hw1, isOpen_ne.mem_nhds hw0]
        with z hzz hz1 hz0
      exact hG z hz0 hz1 hzz
  refine hRDP (Fy y) G a b 1 σ₁ σ₀ (-T) T (by simpa using h2) (by simpa using h3)
    (by simp; linarith) (by simpa using hT) ⟨U, hUo, hsub, hUd⟩ ?_
  intro w hw
  simp only [G, H, if_neg hw]
  ring

end Formalism.ZF
end
end
end

-- Source module: Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.SmallHeightLogDeriv

section

@[expose] public section

open Complex Set Filter Topology

noncomputable section

namespace Formalism.ZF

lemma shld_identity {s : ℂ} (hs : s ≠ 1) (h1 : riemannZeta₁ s ≠ 0) :
    deriv riemannZeta s / riemannZeta s + 1 / (s - 1) =
      deriv riemannZeta₁ s / riemannZeta₁ s := by
  have hs' : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  rw [deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hs, riemannZeta_eq_inv_sub_mul hs]
  field_simp
  ring

lemma riemannZeta₁_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : riemannZeta₁ s ≠ 0 := by
  intro h
  by_cases hs1 : s = 1
  · subst hs1
    simp at h
  · have hz := riemannZeta_ne_zero_of_one_le_re hs
    rw [riemannZeta_eq_inv_sub_mul hs1, h, mul_zero] at hz
    exact hz rfl

theorem logDerivBoundedHeight : SmallHeightLogDeriv := by
  intro T
  have hK : IsCompact (Icc (1 : ℝ) 3 ×ℂ Icc (-T) T) := isCompact_Icc.reProdIm isCompact_Icc
  have hU : IsOpen {s : ℂ | riemannZeta₁ s ≠ 0} :=
    isOpen_ne_fun differentiable_riemannZeta₁.continuous continuous_const
  have hKU : Icc (1 : ℝ) 3 ×ℂ Icc (-T) T ⊆ {s : ℂ | riemannZeta₁ s ≠ 0} := fun s hs =>
    riemannZeta₁_ne_zero_of_one_le_re (Complex.mem_reProdIm.mp hs).1.1
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_thickening_subset_open hU hKU
  have hne : ∀ s : ℂ, |s.im| ≤ T → 1 - δ / 2 ≤ s.re → s.re ≤ 3 → riemannZeta₁ s ≠ 0 := by
    intro s him hre hre3
    by_cases h1 : 1 ≤ s.re
    · exact riemannZeta₁_ne_zero_of_one_le_re h1
    · apply hδU
      rw [Metric.mem_thickening_iff]
      refine ⟨1 + s.im * I, ?_, ?_⟩
      · rw [Complex.mem_reProdIm]
        obtain ⟨h3, h4⟩ := abs_le.mp him
        refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp <;> linarith
      · rw [Complex.dist_eq]
        have hd : s - (1 + s.im * I) = ((s.re - 1 : ℝ) : ℂ) := by
          apply Complex.ext <;> simp
        rw [hd, Complex.norm_real, Real.norm_eq_abs, abs_lt]
        constructor <;> linarith
  refine ⟨δ / 2, ?_⟩
  have hKc : IsCompact (Icc (1 - δ / 2) 3 ×ℂ Icc (-T) T) := isCompact_Icc.reProdIm isCompact_Icc
  have hcont : ContinuousOn (fun s => deriv riemannZeta₁ s / riemannZeta₁ s)
      (Icc (1 - δ / 2) 3 ×ℂ Icc (-T) T) := by
    apply ContinuousOn.div
    · exact ((differentiable_riemannZeta₁.differentiableOn.deriv isOpen_univ).continuousOn).mono
        (subset_univ _)
    · exact differentiable_riemannZeta₁.continuous.continuousOn
    · intro s hs
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := Complex.mem_reProdIm.mp hs
      exact hne s (abs_le.mpr ⟨h3, h4⟩) h1 h2
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hcont
  refine ⟨C, half_pos hδ, ?_⟩
  intro s hs him hre hre3
  rw [shld_identity hs (hne s him hre hre3)]
  exact hC s (Complex.mem_reProdIm.mpr ⟨⟨hre, hre3⟩, abs_le.mp him⟩)

end Formalism.ZF
end
end
end

-- Source module: Formalism.ZeroFreeRegion.LogDerivRegion

section

@[expose] public section

noncomputable section

namespace Formalism.ZF

theorem logDerivRegion : LogDerivRegion :=
  logDerivBoundInRegionOfBounds zeroFreeRegion logDerivBoundRightHalfPlane growthBound zetaInvBound_statement
    logDerivBoundedHeight landauLocal

theorem rectShift : RectShift := rectangleShiftOfResidue rectangle_double_pole laurentExpansionAtOne

theorem gzPNT : GzPNT :=
  zetaPrimeSumErrorBoundOfBounds zeroFreeRegion logDerivRegion logDerivBoundRightHalfPlane perron_formula rectShift

end Formalism.ZF
end
end
end
