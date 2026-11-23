module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.cut_GCore_GTConnCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BasePointMemHalfPlane
public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThetaAtBasePointZero
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
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThetaAtBasePointZero
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Tactic.Linter.Style
public import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Algebra.Order.Star.Real
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FderivDecomp

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.ImCircleIntegral

section

@[expose] public section

open Set Filter Topology Complex MeasureTheory intervalIntegral

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann

noncomputable section

variable {TT : ℝ} {α : ℂ → ℂ}

theorem continuousOn_bet (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT)) :
    ContinuousOn (bet α) (Hh TT) := by
  exact (contDiffOn_bet hα).continuousOn

theorem cont_vert (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT)) :
    Continuous fun θ : ℝ => bet α (x0 TT + (θ : ℂ) * I) := by
  exact (continuousOn_bet hα).comp_continuous (by fun_prop) (vert_mem hTT)

theorem im_circleIntegral (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT)) :
    (circleIntegral α 0 (TT + 1)).im = ∫ θ in (0 : ℝ)..2 * Real.pi, (bet α (x0 TT + (θ : ℂ) * I)).re := by
  have hint : IntervalIntegrable (fun θ : ℝ => I * bet α (x0 TT + (θ : ℂ) * I)) MeasureTheory.volume
      0 (2 * Real.pi) :=
    (continuous_const.mul (cont_vert hTT hα)).intervalIntegrable _ _
  rw [circleIntegral_eq hTT, ← Complex.imCLM_apply, ← ContinuousLinearMap.intervalIntegral_comp_comm _ hint]
  congr 1
  funext θ
  simp [Complex.mul_im]

theorem th_top (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT)) :
    th TT α (x0 TT + 2 * Real.pi * I) = 2 * (circleIntegral α 0 (TT + 1)).im := by
  rw [im_circleIntegral hTT hα]
  have hw : x0 TT + 2 * Real.pi * I - x0 TT = ((2 * Real.pi : ℝ) : ℂ) * I := by push_cast; ring
  have harg : ∀ t : ℝ, x0 TT + (t : ℂ) * (((2 * Real.pi : ℝ) : ℂ) * I) =
      x0 TT + ((2 * Real.pi * t : ℝ) : ℂ) * I := by
    intro t; push_cast; ring
  have him : ∀ z : ℂ, (z * (((2 * Real.pi : ℝ) : ℂ) * I)).im = 2 * Real.pi * z.re := by
    intro z
    simp [Complex.mul_im, Complex.mul_re]
    ring
  simp only [th, prim, hw, om_apply, harg, him]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (f := fun θ : ℝ => (bet α (x0 TT + (θ : ℂ) * I)).re)
      (by positivity : (2 * Real.pi) ≠ 0)]
  simp only [mul_zero, mul_one, smul_eq_mul]
  have hpi : (2 * Real.pi) * (2 * Real.pi)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
  rw [← mul_assoc (2 * Real.pi), hpi, one_mul]

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.ThShiftInt

section

@[expose] public section

open Set Filter Topology Complex MeasureTheory intervalIntegral

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann

noncomputable section

variable {TT : ℝ} {α : ℂ → ℂ}

theorem Hh_add_int {w : ℂ} (k : ℤ) : w + (k : ℂ) * (2 * Real.pi * I) ∈ Hh TT ↔ w ∈ Hh TT := by
  simp only [Hh, Set.mem_ofPred_eq, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem Hh_add_one {w : ℂ} (hw : w ∈ Hh TT) : w + 2 * Real.pi * I ∈ Hh TT := by
  have := (Hh_add_int (TT := TT) (w := w) 1).2 hw
  simpa using this

theorem th_shift (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0) {w : ℂ} (hw : w ∈ Hh TT) :
    th TT α (w + 2 * Real.pi * I) = th TT α w + 2 * (circleIntegral α 0 (TT + 1)).im := by
  have hc : ∀ z ∈ Hh TT, HasFDerivAt (fun z => th TT α (z + 2 * Real.pi * I) - th TT α z)
      (0 : ℂ →L[ℝ] ℝ) z := by
    intro z hz
    have h1 : HasFDerivAt (fun z => th TT α (z + 2 * Real.pi * I)) (om α (z + 2 * Real.pi * I)) z := by
      have := (hasFDerivAt_th hTT hα hcurv (Hh_add_one hz)).comp z
        ((hasFDerivAt_id z).add_const (2 * Real.pi * I))
      exact this
    have h2 := hasFDerivAt_th hTT hα hcurv hz
    have hom : om α (z + 2 * Real.pi * I) = om α z := by
      have := bet_periodic α z 1
      simp only [Int.cast_one, one_mul] at this
      simp only [om, this]
    have := h1.sub h2
    rwa [hom, sub_self] at this
  have hconst := (convex_Hh TT).is_const_of_fderivWithin_eq_zero
    (fun z hz => (hc z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hc z hz).hasFDerivWithinAt.fderivWithin ((isOpen_Hh TT).uniqueDiffWithinAt hz))
    (base_point_mem_half_plane hTT) hw
  rw [th_top hTT hα, theta_at_base_point_zero, sub_zero] at hconst
  linarith

theorem th_shift_int (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0) (k : ℤ) :
    ∀ w ∈ Hh TT, th TT α (w + (k : ℂ) * (2 * Real.pi * I)) = th TT α w + k * (2 * (circleIntegral α 0 (TT + 1)).im) := by
  intro w hw
  refine Int.induction_on k ?_ ?_ ?_
  · simp
  · intro n ih
    have hmem : w + ((n : ℤ) : ℂ) * (2 * Real.pi * I) ∈ Hh TT := (Hh_add_int (n : ℤ)).2 hw
    have h1 := th_shift hTT hα hcurv hmem
    push_cast at ih h1 ⊢
    rw [show w + ((n : ℂ) + 1) * (2 * Real.pi * I) = w + (n : ℂ) * (2 * Real.pi * I) + 2 * Real.pi * I by ring,
      h1, ih]
    ring
  · intro n ih
    have hmem : w + ((-(n : ℤ) - 1 : ℤ) : ℂ) * (2 * Real.pi * I) ∈ Hh TT := (Hh_add_int _).2 hw
    have h1 := th_shift hTT hα hcurv hmem
    push_cast at ih h1 ⊢
    rw [show w + (-(n : ℂ) - 1) * (2 * Real.pi * I) + 2 * Real.pi * I = w + -(n : ℂ) * (2 * Real.pi * I) by ring,
      ih] at h1
    linarith

theorem expI_th_eq (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0)
    (hhol : ∃ n : ℤ, (circleIntegral α 0 (TT + 1)).im = Real.pi * n)
    {w w' : ℂ} (hw : w ∈ Hh TT) (hw' : w' ∈ Hh TT) (he : Complex.exp w = Complex.exp w') :
    Complex.exp (I * (th TT α w : ℂ)) = Complex.exp (I * (th TT α w' : ℂ)) := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 he
  obtain ⟨m, hm⟩ := hhol
  have h := th_shift_int hTT hα hcurv n w' hw'
  rw [← hn, hm] at h
  apply Complex.exp_eq_exp_iff_exists_int.2
  refine ⟨n * m, ?_⟩
  rw [h]
  push_cast
  ring

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.NeZeroOfAn

section

@[expose] public section

open Set Filter Topology Complex

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann

noncomputable section

variable {TT : ℝ} {α : ℂ → ℂ}

def uu (TT : ℝ) (α : ℂ → ℂ) (ζ : ℂ) : ℂ := Complex.exp (I * (th TT α (Complex.log ζ) : ℂ))

theorem ne_zero_of_An (hTT : 0 ≤ TT) {ζ : ℂ} (hζ : ζ ∈ An TT) : ζ ≠ 0 := by
  rintro rfl
  simp [An] at hζ
  linarith

def br (s : Bool) (ζ : ℂ) : ℂ := if s then Complex.log ζ else Complex.log (-ζ) + Real.pi * I

def brD (s : Bool) : Set ℂ := if s then Complex.slitPlane else {ζ | -ζ ∈ Complex.slitPlane}

theorem isOpen_brD (s : Bool) : IsOpen (brD s) := by
  cases s
  · simp only [brD, Bool.false_eq_true, ↓reduceIte]
    exact Complex.isOpen_slitPlane.preimage continuous_neg
  · simp only [brD, ↓reduceIte]
    exact Complex.isOpen_slitPlane

theorem exp_br (s : Bool) {ζ : ℂ} (hζ : ζ ≠ 0) : Complex.exp (br s ζ) = ζ := by
  cases s
  · simp only [br, Bool.false_eq_true, ↓reduceIte]
    rw [Complex.exp_add, Complex.exp_log (neg_ne_zero.mpr hζ), Complex.exp_pi_mul_I]
    ring
  · simp only [br, ↓reduceIte]
    exact Complex.exp_log hζ

theorem exists_br {ζ : ℂ} (hζ : ζ ≠ 0) : ∃ s, ζ ∈ brD s := by
  by_cases h : ζ ∈ Complex.slitPlane
  · exact ⟨true, by simpa [brD] using h⟩
  · refine ⟨false, ?_⟩
    simp only [brD, Bool.false_eq_true, ↓reduceIte, Set.mem_setOf_eq]
    rw [Complex.mem_slitPlane_iff] at h ⊢
    push_neg at h
    left
    rcases h with ⟨h1, h2⟩
    have h3 : ζ.re ≠ 0 := fun h0 => hζ (Complex.ext (by simpa using h0) (by simpa using h2))
    have h4 : ζ.re < 0 := lt_of_le_of_ne h1 h3
    simp only [Complex.neg_re]
    linarith

theorem hasDerivAt_br (s : Bool) {ζ : ℂ} (hs : ζ ∈ brD s) : HasDerivAt (br s) ζ⁻¹ ζ := by
  cases s
  · simp only [brD, Bool.false_eq_true, ↓reduceIte, Set.mem_setOf_eq] at hs
    have e1 : br false = fun z : ℂ => Complex.log (-z) + Real.pi * I := by
      funext z
      simp [br]
    have h1 : HasDerivAt (fun z : ℂ => Complex.log (-z)) ((-ζ)⁻¹ * (-1)) ζ :=
      (Complex.hasDerivAt_log hs).comp ζ (hasDerivAt_neg ζ)
    have h2 := h1.add_const ((Real.pi : ℂ) * I)
    have e2 : (-ζ)⁻¹ * (-1) = ζ⁻¹ := by rw [inv_neg, neg_mul_neg, mul_one]
    rw [e2] at h2
    rw [e1]
    exact h2
  · simp only [brD, ↓reduceIte] at hs
    have e1 : br true = Complex.log := by
      funext z
      simp [br]
    rw [e1]
    exact Complex.hasDerivAt_log hs

theorem contDiffAt_br (s : Bool) {ζ : ℂ} (hs : ζ ∈ brD s) : ContDiffAt ℂ ((⊤ : ℕ∞) : WithTop ℕ∞) (br s) ζ := by
  have hd : DifferentiableOn ℂ (br s) (brD s) := fun z hz =>
    (hasDerivAt_br s hz).differentiableAt.differentiableWithinAt
  exact (hd.contDiffOn (isOpen_brD s)).contDiffAt ((isOpen_brD s).mem_nhds hs)

theorem br_mem_Hh (s : Bool) (hTT : 0 ≤ TT) {ζ : ℂ} (hζ : ζ ∈ An TT) : br s ζ ∈ Hh TT := by
  show Complex.exp (br s ζ) ∈ An TT
  rw [exp_br s (ne_zero_of_An hTT hζ)]
  exact hζ

theorem uu_eq_br (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0)
    (hhol : ∃ n : ℤ, (circleIntegral α 0 (TT + 1)).im = Real.pi * n) (s : Bool) {ζ : ℂ} (hζ : ζ ∈ An TT) :
    uu TT α ζ = Complex.exp (I * (th TT α (br s ζ) : ℂ)) := by
  unfold uu
  have h0 := ne_zero_of_An hTT hζ
  exact expI_th_eq hTT hα hcurv hhol (br_mem_Hh true hTT hζ) (br_mem_Hh s hTT hζ)
    (by rw [Complex.exp_log h0, exp_br s h0])

theorem norm_uu (ζ : ℂ) : ‖uu TT α ζ‖ = 1 := by
  rw [uu, mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.HasFDerivAtBrReal

section

@[expose] public section

open Set Filter Topology Complex

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann

noncomputable section

variable {TT : ℝ} {α : ℂ → ℂ}

def ug (TT : ℝ) (α : ℂ → ℂ) (s : Bool) (z : ℂ) : ℂ := Complex.exp (I * (th TT α (br s z) : ℂ))

theorem hasFDerivAt_br_real (s : Bool) {ζ : ℂ} (hs : ζ ∈ brD s) :
    HasFDerivAt (br s) ((ContinuousLinearMap.mul ℝ ℂ) ζ⁻¹) ζ := by
  have h : HasFDerivAt (br s)
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) ζ⁻¹).restrictScalars ℝ) ζ :=
    (hasDerivAt_br s hs).hasFDerivAt.restrictScalars ℝ
  convert h using 1
  refine ContinuousLinearMap.ext fun v => ?_
  simp [mul_comm]

theorem hasFDerivAt_ug (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0) (s : Bool) {ζ : ℂ} (hs : ζ ∈ brD s)
    (hζ : ζ ∈ An TT) :
    HasFDerivAt (ug TT α s)
      (((ContinuousLinearMap.mul ℝ ℂ) (ug TT α s ζ)).comp
        (I • Complex.ofRealCLM.comp ((om α (br s ζ)).comp ((ContinuousLinearMap.mul ℝ ℂ) ζ⁻¹)))) ζ := by
  have h1 : HasFDerivAt (fun z => th TT α (br s z))
      ((om α (br s ζ)).comp ((ContinuousLinearMap.mul ℝ ℂ) ζ⁻¹)) ζ :=
    (hasFDerivAt_th hTT hα hcurv (br_mem_Hh s hTT hζ)).comp ζ (hasFDerivAt_br_real s hs)
  have h2 : HasFDerivAt (fun z => ((th TT α (br s z) : ℝ) : ℂ))
      (Complex.ofRealCLM.comp ((om α (br s ζ)).comp ((ContinuousLinearMap.mul ℝ ℂ) ζ⁻¹))) ζ :=
    Complex.ofRealCLM.hasFDerivAt.comp ζ h1
  have h3 : HasFDerivAt (fun z => I * ((th TT α (br s z) : ℝ) : ℂ))
      (I • Complex.ofRealCLM.comp ((om α (br s ζ)).comp ((ContinuousLinearMap.mul ℝ ℂ) ζ⁻¹))) ζ :=
    h2.const_smul I
  have h4 := h3.cexp
  show HasFDerivAt (fun z => Complex.exp (I * (th TT α (br s z) : ℂ))) _ ζ
  refine h4.congr_fderiv ?_
  ext v
  simp [ug]

theorem fderiv_uu_apply (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0)
    (hhol : ∃ n : ℤ, (circleIntegral α 0 (TT + 1)).im = Real.pi * n) {ζ : ℂ} (hζ : ζ ∈ An TT) (v : ℂ) :
    fderiv ℝ (uu TT α) ζ v = uu TT α ζ * (I * ((2 * (α ζ * v).im : ℝ) : ℂ)) := by
  have hne := ne_zero_of_An hTT hζ
  obtain ⟨s, hs⟩ := exists_br hne
  have hev : uu TT α =ᶠ[𝓝 ζ] ug TT α s := by
    filter_upwards [(isOpen_An TT).mem_nhds hζ] with z hz
    exact uu_eq_br hTT hα hcurv hhol s hz
  have hu : ug TT α s ζ = uu TT α ζ := (uu_eq_br hTT hα hcurv hhol s hζ).symm
  rw [hev.fderiv_eq, (hasFDerivAt_ug hTT hα hcurv s hs hζ).fderiv]
  have hb : α ζ * ζ * (ζ⁻¹ * v) = α ζ * v := by field_simp
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply',
    ContinuousLinearMap.smul_apply, Complex.ofRealCLM_apply, om_apply, bet, exp_br s hne,
    smul_eq_mul, hu, hb]

theorem wZ_uu (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0)
    (hhol : ∃ n : ℤ, (circleIntegral α 0 (TT + 1)).im = Real.pi * n) {ζ : ℂ} (hζ : ζ ∈ An TT) :
    wZ (uu TT α) ζ = uu TT α ζ * α ζ ∧ wZb (uu TT α) ζ = -(uu TT α ζ * (starRingEnd ℂ) (α ζ)) := by
  have h1 := fderiv_uu_apply hTT hα hcurv hhol hζ 1
  have h2 := fderiv_uu_apply hTT hα hcurv hhol hζ I
  have e1 : (1 / 2 : ℂ) * (I * ((2 * (α ζ * 1).im : ℝ) : ℂ) - I * (I * ((2 * (α ζ * I).im : ℝ) : ℂ)))
      = α ζ := by
    apply Complex.ext <;> simp
  have e2 : (1 / 2 : ℂ) * (I * ((2 * (α ζ * 1).im : ℝ) : ℂ) + I * (I * ((2 * (α ζ * I).im : ℝ) : ℂ)))
      = -(starRingEnd ℂ) (α ζ) := by
    apply Complex.ext <;> simp
  refine ⟨?_, ?_⟩
  · rw [wZ, h1, h2]
    linear_combination (uu TT α ζ) * e1
  · rw [wZb, h1, h2]
    linear_combination (uu TT α ζ) * e2

theorem contDiffOn_uu (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0)
    (hhol : ∃ n : ℤ, (circleIntegral α 0 (TT + 1)).im = Real.pi * n) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (uu TT α) (An TT) := by
  intro ζ hζ
  obtain ⟨s, hs⟩ := exists_br (ne_zero_of_An hTT hζ)
  have hev : uu TT α =ᶠ[𝓝 ζ] fun z => Complex.exp (I * (th TT α (br s z) : ℂ)) := by
    filter_upwards [(isOpen_An TT).mem_nhds hζ] with z hz
    exact uu_eq_br hTT hα hcurv hhol s hz
  have hth : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (th TT α) (br s ζ) :=
    (contDiffOn_th hTT hα hcurv).contDiffAt ((isOpen_Hh TT).mem_nhds (br_mem_Hh s hTT hζ))
  have hbr : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (br s) ζ :=
    (contDiffAt_br s hs).restrict_scalars ℝ
  have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => ((th TT α (br s z) : ℝ) : ℂ)) ζ :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp ζ (hth.comp ζ hbr)
  exact ((contDiffAt_const.mul h2).cexp.congr_of_eventuallyEq hev).contDiffWithinAt

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnAnn

section

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Complex

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

theorem annulus_condition_holds : GTCAnnulus := by
  intro TT α hTT hα hcurv hper
  have hhol : ∃ n : ℤ, (circleIntegral α 0 (TT + 1)).im = Real.pi * n :=
    hper (TT + 1) (by linarith) (by nlinarith [sq_nonneg (TT + 1 / 2)])
  have hcurv' : ∀ ζ : ℂ, TT < Complex.normSq ζ → (Ann.wZb α ζ).re = 0 := hcurv
  refine ⟨Ann.uu TT α, Ann.contDiffOn_uu hTT hα hcurv' hhol, fun ζ hζ => ?_⟩
  obtain ⟨h1, h2⟩ := Ann.wZ_uu hTT hα hcurv' hhol (ζ := ζ) hζ
  have hn : ‖Ann.uu TT α ζ‖ = 1 := Ann.norm_uu ζ
  have hs : star (Ann.uu TT α ζ) * Ann.uu TT α ζ = 1 := by
    calc star (Ann.uu TT α ζ) * Ann.uu TT α ζ
        = (starRingEnd ℂ) (Ann.uu TT α ζ) * Ann.uu TT α ζ := rfl
      _ = ((‖Ann.uu TT α ζ‖ : ℝ) : ℂ) ^ 2 := Complex.conj_mul' _
      _ = 1 := by rw [hn]; norm_num
  refine ⟨hn, ?_, ?_⟩
  · show star (Ann.uu TT α ζ) * Ann.wZ (Ann.uu TT α) ζ = α ζ
    rw [h1, ← mul_assoc, hs, one_mul]
  · show star (Ann.uu TT α ζ) * Ann.wZb (Ann.uu TT α) ζ = -star (α ζ)
    rw [h2, mul_neg, ← mul_assoc, hs, one_mul] <;> rfl

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end
end
