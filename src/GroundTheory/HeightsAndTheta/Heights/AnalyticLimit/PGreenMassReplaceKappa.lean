module

public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.UIObjects
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import ReciprocityTheory.AnalyticForms.MaIntEmpty
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
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
import Mathlib.Order.CompletePartialOrder
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
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PKaehlerBound
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.Linter.Style
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
public import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCEqZeroOfEventuallyEqZero
public import ReciprocityTheory.AnalyticForms.PotentialTheory.MaMeasureA
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA

-- Source module: GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PGreenMassReplaceLevi

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology
open ReciprocityTheory.AnForm (levi levi_add_smul levi_re_analytic)

noncomputable section

variable {ι : Type} [Fintype ι]

theorem fderiv2_comp_real {ψ : (ι → ℂ) → ℝ} {G G₁ : ℝ → ℝ} {g₂ : ℝ} {y : ι → ℂ}
    (hψ : ContDiffAt ℝ 2 ψ y) (hG : ∀ᶠ z in 𝓝 y, HasDerivAt G (G₁ (ψ z)) (ψ z))
    (hG₁ : HasDerivAt G₁ g₂ (ψ y)) (v w : ι → ℂ) :
    fderiv ℝ (fderiv ℝ (fun z => G (ψ z))) y v w =
      G₁ (ψ y) * fderiv ℝ (fderiv ℝ ψ) y v w + g₂ * fderiv ℝ ψ y v * fderiv ℝ ψ y w := by
  have hev : fderiv ℝ (fun z => G (ψ z)) =ᶠ[𝓝 y] fun z => G₁ (ψ z) • fderiv ℝ ψ z := by
    filter_upwards [hG, hψ.eventually (by simp)] with z h1 h2
    exact (h1.comp_hasFDerivAt z (h2.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  have hD2 : HasFDerivAt (fderiv ℝ ψ) (fderiv ℝ (fderiv ℝ ψ) y) y :=
    ((hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hc : HasFDerivAt (fun z => G₁ (ψ z)) (g₂ • fderiv ℝ ψ y) y :=
    hG₁.comp_hasFDerivAt y (hψ.differentiableAt (by norm_num)).hasFDerivAt
  have h := ((hc.smul hD2).congr_of_eventuallyEq hev).fderiv
  rw [h]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]

theorem fderiv_comp_real {ψ : (ι → ℂ) → ℝ} {G : ℝ → ℝ} {g₁ : ℝ} {y : ι → ℂ}
    (hψ : DifferentiableAt ℝ ψ y) (hG : HasDerivAt G g₁ (ψ y)) (v : ι → ℂ) :
    fderiv ℝ (fun z => G (ψ z)) y v = g₁ * fderiv ℝ ψ y v := by
  have h := (hG.comp_hasFDerivAt y hψ.hasFDerivAt).fderiv
  rw [show (fun z => G (ψ z)) = G ∘ ψ from rfl, h]
  simp

theorem levi_comp_real {ψ : (ι → ℂ) → ℝ} {G G₁ : ℝ → ℝ} {g₂ : ℝ} {y : ι → ℂ}
    (hψ : ContDiffAt ℝ 2 ψ y) (hG : ∀ᶠ z in 𝓝 y, HasDerivAt G (G₁ (ψ z)) (ψ z))
    (hG₁ : HasDerivAt G₁ g₂ (ψ y)) (w : ι → ℂ) :
    levi (fun z => G (ψ z)) y w = G₁ (ψ y) * levi ψ y w +
      g₂ * ((fderiv ℝ ψ y w) ^ 2 + (fderiv ℝ ψ y (Complex.I • w)) ^ 2) / 4 := by
  unfold levi
  rw [fderiv2_comp_real hψ hG hG₁, fderiv2_comp_real hψ hG hG₁]
  ring

theorem fderiv_re_analytic {S : (ι → ℂ) → ℂ} {y : ι → ℂ} (hS : AnalyticAt ℂ S y) (v : ι → ℂ) :
    fderiv ℝ (fun z => (S z).re) y v = (fderiv ℂ S y v).re := by
  have hS' : HasFDerivAt S ((fderiv ℂ S y).restrictScalars ℝ) y :=
    hS.differentiableAt.hasFDerivAt.restrictScalars ℝ
  have h := (Complex.reCLM.hasFDerivAt.comp y hS').fderiv
  rw [show (fun z => (S z).re) = Complex.reCLM ∘ S from rfl, h]
  simp

theorem im_eq_re_mul (c : ℂ) : c.im = (-Complex.I * c).re := by
  simp [Complex.mul_re]

theorem fderiv_im_analytic {S : (ι → ℂ) → ℂ} {y : ι → ℂ} (hS : AnalyticAt ℂ S y) (v : ι → ℂ) :
    fderiv ℝ (fun z => (S z).im) y v = (fderiv ℂ S y v).im := by
  have hS2 : AnalyticAt ℂ (fun z => -Complex.I * S z) y := analyticAt_const.mul hS
  have h1 : (fun z => (S z).im) = fun z => (-Complex.I * S z).re := funext fun z => im_eq_re_mul _
  rw [h1, fderiv_re_analytic hS2, fderiv_const_mul hS.differentiableAt]
  simp [Complex.mul_re]

theorem levi_im_analytic {S : (ι → ℂ) → ℂ} {y : ι → ℂ} (hS : AnalyticAt ℂ S y) (w : ι → ℂ) :
    levi (fun z => (S z).im) y w = 0 := by
  have hS2 : AnalyticAt ℂ (fun z => -Complex.I * S z) y := analyticAt_const.mul hS
  have h1 : (fun z => (S z).im) = fun z => (-Complex.I * S z).re := funext fun z => im_eq_re_mul _
  rw [h1]
  exact levi_re_analytic hS2 w

theorem contDiffAt_re_analytic {S : (ι → ℂ) → ℂ} {y : ι → ℂ} (hS : AnalyticAt ℂ S y) :
    ContDiffAt ℝ 2 (fun z => (S z).re) y :=
  (Complex.reCLM.contDiff (n := 2)).contDiffAt.comp y (hS.restrictScalars (𝕜 := ℝ)).contDiffAt

theorem contDiffAt_im_analytic {S : (ι → ℂ) → ℂ} {y : ι → ℂ} (hS : AnalyticAt ℂ S y) :
    ContDiffAt ℝ 2 (fun z => (S z).im) y :=
  (Complex.imCLM.contDiff (n := 2)).contDiffAt.comp y (hS.restrictScalars (𝕜 := ℝ)).contDiffAt

theorem sq_norm_eq_re_im (c : ℂ) : ‖c‖ ^ 2 = c.re ^ 2 + 1 * c.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem hasDerivAt_sq' (x : ℝ) : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by
  simpa using hasDerivAt_pow 2 x

theorem levi_normSq_analytic {S : (ι → ℂ) → ℂ} {y : ι → ℂ} (hS : AnalyticAt ℂ S y) (w : ι → ℂ) :
    levi (fun z => ‖S z‖ ^ 2) y w = ‖fderiv ℂ S y w‖ ^ 2 := by
  have hre := contDiffAt_re_analytic hS
  have him := contDiffAt_im_analytic hS
  have e : (fun z => ‖S z‖ ^ 2) = fun z => (S z).re ^ 2 + 1 * (S z).im ^ 2 :=
    funext fun z => sq_norm_eq_re_im _
  have hG : ∀ (ψ : (ι → ℂ) → ℝ), ∀ᶠ z in 𝓝 y, HasDerivAt (fun x : ℝ => x ^ 2) (2 * ψ z) (ψ z) :=
    fun ψ => Eventually.of_forall fun z => hasDerivAt_sq' _
  have hG₁ : ∀ x : ℝ, HasDerivAt (fun x : ℝ => 2 * x) 2 x := fun x => by
    simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
  have l1 := levi_comp_real (G₁ := fun x => 2 * x) hre (hG _) (hG₁ _) w
  have l2 := levi_comp_real (G₁ := fun x => 2 * x) him (hG _) (hG₁ _) w
  have hsq : ∀ (ψ : (ι → ℂ) → ℝ), ContDiffAt ℝ 2 ψ y → ContDiffAt ℝ 2 (fun z => ψ z ^ 2) y :=
    fun ψ h => h.pow 2
  rw [e, levi_add_smul 1 (hsq _ hre) (hsq _ him), l1, l2, levi_re_analytic hS,
    levi_im_analytic hS, fderiv_re_analytic hS, fderiv_re_analytic hS, fderiv_im_analytic hS,
    fderiv_im_analytic hS, map_smul, sq_norm_eq_re_im]
  simp only [smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  ring

theorem fderiv_normSq_analytic {S : (ι → ℂ) → ℂ} {y : ι → ℂ} (hS : AnalyticAt ℂ S y) (v : ι → ℂ) :
    fderiv ℝ (fun z => ‖S z‖ ^ 2) y v =
      2 * ((S y).re * (fderiv ℂ S y v).re + (S y).im * (fderiv ℂ S y v).im) := by
  have hre := contDiffAt_re_analytic hS
  have him := contDiffAt_im_analytic hS
  have e : (fun z => ‖S z‖ ^ 2) = fun z => (S z).re ^ 2 + (S z).im ^ 2 :=
    funext fun z => by rw [sq_norm_eq_re_im, one_mul]
  have d1 : DifferentiableAt ℝ (fun z => (S z).re ^ 2) y :=
    (hre.differentiableAt (by norm_num)).pow 2
  have d2 : DifferentiableAt ℝ (fun z => (S z).im ^ 2) y :=
    (him.differentiableAt (by norm_num)).pow 2
  rw [e, fderiv_fun_add d1 d2, ContinuousLinearMap.add_apply,
    fderiv_comp_real (G := fun x : ℝ => x ^ 2) (hre.differentiableAt (by norm_num))
      (hasDerivAt_sq' _),
    fderiv_comp_real (G := fun x : ℝ => x ^ 2) (him.differentiableAt (by norm_num))
      (hasDerivAt_sq' _), fderiv_re_analytic hS, fderiv_im_analytic hS]
  ring

theorem levi_log_normSq_add_exp {S : (ι → ℂ) → ℂ} {Φ : (ι → ℂ) → ℝ} {y : ι → ℂ} {ε : ℝ}
    (hS : AnalyticAt ℂ S y) (hΦ : ContDiffAt ℝ 2 Φ y) (hε : 0 < ε) (w : ι → ℂ) :
    2 * (ε * Real.exp (2 * Φ y)) / (‖S y‖ ^ 2 + ε * Real.exp (2 * Φ y)) * levi Φ y w ≤
      levi (fun z => Real.log (‖S z‖ ^ 2 + ε * Real.exp (2 * Φ z))) y w := by
  set h : (ι → ℂ) → ℝ := fun z => ‖S z‖ ^ 2 + ε * Real.exp (2 * Φ z) with hh
  have hpos : ∀ z, 0 < h z := fun z => by
    have := Real.exp_pos (2 * Φ z)
    positivity
  have hSc : ContDiffAt ℝ 2 S y := (hS.restrictScalars (𝕜 := ℝ)).contDiffAt
  have hQ : ContDiffAt ℝ 2 (fun z => ‖S z‖ ^ 2) y := (contDiff_norm_sq ℝ).contDiffAt.comp y hSc
  have h2Φ : ContDiffAt ℝ 2 (fun z => 2 * Φ z) y := contDiffAt_const.mul hΦ
  have hE : ContDiffAt ℝ 2 (fun z => Real.exp (2 * Φ z)) y := h2Φ.exp
  have hhc : ContDiffAt ℝ 2 h y := hQ.add (contDiffAt_const.mul hE)
  have l2Φ := levi_comp_real (G := fun x : ℝ => 2 * x) (G₁ := fun _ => 2) (g₂ := 0) hΦ
    (Eventually.of_forall fun z => by simpa using (hasDerivAt_id (Φ z)).const_mul (2 : ℝ))
    (hasDerivAt_const _ _) w
  have lE := levi_comp_real (G := Real.exp) (G₁ := Real.exp) (g₂ := Real.exp (2 * Φ y)) h2Φ
    (Eventually.of_forall fun z => Real.hasDerivAt_exp _) (Real.hasDerivAt_exp _) w
  have d2Φ : ∀ v, fderiv ℝ (fun z => 2 * Φ z) y v = 2 * fderiv ℝ Φ y v := fun v =>
    fderiv_comp_real (G := fun x : ℝ => 2 * x) (hΦ.differentiableAt (by norm_num))
      (by simpa using (hasDerivAt_id (Φ y)).const_mul (2 : ℝ)) v
  have dE : ∀ v, fderiv ℝ (fun z => Real.exp (2 * Φ z)) y v =
      Real.exp (2 * Φ y) * (2 * fderiv ℝ Φ y v) := fun v => by
    rw [fderiv_comp_real (G := Real.exp) (h2Φ.differentiableAt (by norm_num))
      (Real.hasDerivAt_exp _), d2Φ]
  have dh : ∀ v, fderiv ℝ h y v = 2 * ((S y).re * (fderiv ℂ S y v).re +
      (S y).im * (fderiv ℂ S y v).im) + ε * (Real.exp (2 * Φ y) * (2 * fderiv ℝ Φ y v)) := by
    intro v
    have d1 : DifferentiableAt ℝ (fun z => ‖S z‖ ^ 2) y := hQ.differentiableAt (by norm_num)
    have d2 : DifferentiableAt ℝ (fun z => ε * Real.exp (2 * Φ z)) y :=
      (contDiffAt_const.mul hE).differentiableAt (by norm_num)
    rw [hh, fderiv_fun_add d1 d2, ContinuousLinearMap.add_apply, fderiv_normSq_analytic hS,
      fderiv_const_mul (hE.differentiableAt (by norm_num)), ContinuousLinearMap.smul_apply,
      dE, smul_eq_mul]
  have lh : levi h y w = ‖fderiv ℂ S y w‖ ^ 2 + ε * (Real.exp (2 * Φ y) * (2 * levi Φ y w) +
      Real.exp (2 * Φ y) * ((2 * fderiv ℝ Φ y w) ^ 2 +
        (2 * fderiv ℝ Φ y (Complex.I • w)) ^ 2) / 4) := by
    rw [hh, levi_add_smul ε hQ hE, levi_normSq_analytic hS, lE, l2Φ, d2Φ, d2Φ]
    ring
  have lK := levi_comp_real (G := Real.log) (G₁ := fun x => x⁻¹) (g₂ := -(h y ^ 2)⁻¹) hhc
    (Eventually.of_forall fun z => Real.hasDerivAt_log (hpos z).ne')
    (hasDerivAt_inv (hpos y).ne') w
  change _ ≤ levi (fun z => Real.log (h z)) y w
  rw [lK, lh, dh, dh, (fderiv ℂ S y).map_smul Complex.I w, sq_norm_eq_re_im (fderiv ℂ S y w)]
  simp only [smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  set E := ε * Real.exp (2 * Φ y) with hEdef
  have hEpos : 0 < E := mul_pos hε (Real.exp_pos _)
  have hy : h y = ‖S y‖ ^ 2 + E := rfl
  rw [sq_norm_eq_re_im (S y)] at hy
  set σr := (S y).re
  set σi := (S y).im
  set ar := (fderiv ℂ S y w).re
  set ai := (fderiv ℂ S y w).im
  set b₁ := fderiv ℝ Φ y w
  set b₂ := fderiv ℝ Φ y (Complex.I • w)
  set L := levi Φ y w
  have hhy : 0 < h y := hpos y
  rw [show ‖S y‖ ^ 2 + E = h y from rfl]
  have key : (h y)⁻¹ * (ar ^ 2 + 1 * ai ^ 2 + ε * (Real.exp (2 * Φ y) * (2 * L) +
      Real.exp (2 * Φ y) * ((2 * b₁) ^ 2 + (2 * b₂) ^ 2) / 4)) +
      -(h y ^ 2)⁻¹ * ((2 * (σr * ar + σi * ai) + ε * (Real.exp (2 * Φ y) * (2 * b₁))) ^ 2 +
        (2 * (σr * (0 * ar - 1 * ai) + σi * (0 * ai + 1 * ar)) +
          ε * (Real.exp (2 * Φ y) * (2 * b₂))) ^ 2) / 4 - 2 * E / h y * L =
      E * ((ar - (σr * b₁ + σi * b₂)) ^ 2 + (ai - (σi * b₁ - σr * b₂)) ^ 2) / h y ^ 2 := by
    rw [hy]
    field_simp
    rw [hEdef]
    ring
  have hnn : 0 ≤ E * ((ar - (σr * b₁ + σi * b₂)) ^ 2 + (ai - (σi * b₁ - σr * b₂)) ^ 2) / h y ^ 2 :=
    by positivity
  linarith

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PGreenMassReplaceKappa

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology MeasureTheory
open scoped ContDiff
open ReciprocityTheory.AnForm (levi levi_congr levi_add_smul)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection IsSNC logNormSec)

noncomputable section

namespace GreenMassReplace

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem secNorm_eq_local {A : FinHolAtlas e X} {L : LocPot X} {s : X → X → ℂ}
    (hS : IsSection A L s) {x y : X} (hy : y ∈ L.U x) :
    secNorm L s y = ‖s x y‖ * Real.exp (-L.φ x y) :=
  hS.2 y x y ⟨L.mem_U y, hy⟩

def logNormSqAdd (L : LocPot X) (s : X → X → ℂ) (ε : ℝ) (y : X) : ℝ :=
  Real.log (secNorm L s y ^ 2 + ε)

theorem logNormSqAdd_eq_local {A : FinHolAtlas e X} {L : LocPot X} {s : X → X → ℂ}
    (hS : IsSection A L s) {x y : X} (hy : y ∈ L.U x) {ε : ℝ} (hε : 0 < ε) :
    logNormSqAdd L s ε y =
      Real.log (‖s x y‖ ^ 2 + ε * Real.exp (2 * L.φ x y)) - 2 * L.φ x y := by
  unfold logNormSqAdd
  rw [secNorm_eq_local hS hy]
  have hP : 0 < ‖s x y‖ ^ 2 + ε * Real.exp (2 * L.φ x y) := by positivity
  have h1 : Real.exp (-L.φ x y) ^ 2 = Real.exp (-(2 * L.φ x y)) := by
    rw [sq, ← Real.exp_add]
    ring_nf
  have h2 : Real.exp (2 * L.φ x y) * Real.exp (-(2 * L.φ x y)) = 1 := by
    rw [← Real.exp_add]
    simp
  have h3 : (‖s x y‖ * Real.exp (-L.φ x y)) ^ 2 + ε =
      (‖s x y‖ ^ 2 + ε * Real.exp (2 * L.φ x y)) * Real.exp (-(2 * L.φ x y)) := by
    rw [mul_pow, h1, add_mul, mul_assoc ε, h2, mul_one]
  rw [h3, Real.log_mul hP.ne' (Real.exp_pos _).ne', Real.log_exp]
  ring

theorem kappaEp_φ_eq_local {A : FinHolAtlas e X} {L : LocPot X} {s : X → X → ℂ}
    (hS : IsSection A L s) {x y : X} (hy : y ∈ L.U x) {ε : ℝ} (hε : 0 < ε) :
    (kappaEp L s ε).φ x y = Real.log (‖s x y‖ ^ 2 + ε * Real.exp (2 * L.φ x y)) := by
  have h := logNormSqAdd_eq_local hS hy hε
  unfold logNormSqAdd at h
  show 2 * L.φ x y + Real.log (secNorm L s y ^ 2 + ε) = _
  rw [h]
  ring

theorem smooth_logNormSqAdd {A : FinHolAtlas e X} {L : LocPot X} {s : X → X → ℂ}
    (hL : IsPotential A L) (hS : IsSection A L s) {ε : ℝ} (hε : 0 < ε) :
    A.Smooth (logNormSqAdd L s ε) := by
  intro j y hy
  refine ContDiffAt.contDiffWithinAt ?_
  have hyt : y ∈ (A.chart j).target := hy.1
  set q := (A.chart j).symm y with hq
  have hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' L.U q) :=
    (A.chart j).isOpen_inter_preimage_symm (L.isOpen_U q)
  have hyO : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' L.U q := ⟨hyt, L.mem_U q⟩
  have heq : (logNormSqAdd L s ε ∘ (A.chart j).symm) =ᶠ[𝓝 y] fun z =>
      Real.log (‖(s q ∘ (A.chart j).symm) z‖ ^ 2 +
        ε * Real.exp (2 * (L.φ q ∘ (A.chart j).symm) z)) - 2 * (L.φ q ∘ (A.chart j).symm) z := by
    filter_upwards [hO.mem_nhds hyO] with z hz
    exact logNormSqAdd_eq_local hS hz.2 hε
  refine ContDiffAt.congr_of_eventuallyEq ?_ heq
  have hSc : ContDiffAt ℝ ∞ (s q ∘ (A.chart j).symm) y :=
    ((hS.1 q j y hyO).restrictScalars (𝕜 := ℝ)).contDiffAt
  have hΦ : ContDiffAt ℝ ∞ (L.φ q ∘ (A.chart j).symm) y :=
    ReciprocityTheory.AnForm.M.contDiffAt_of_isPotential A L hL q j hyO
  refine ((((contDiff_norm_sq ℝ).contDiffAt.comp y hSc).add
    (contDiffAt_const.mul (contDiffAt_const.mul hΦ).exp)).log ?_).sub (contDiffAt_const.mul hΦ)
  exact (by positivity : (0 : ℝ) < ‖(s q ∘ (A.chart j).symm) y‖ ^ 2 +
    ε * Real.exp (2 * (L.φ q ∘ (A.chart j).symm) y)).ne'

theorem isPotential_kappaEp {A : FinHolAtlas e X} {L : LocPot X} {s : X → X → ℂ}
    (hL : IsPotential A L) (hS : IsSection A L s) {ε : ℝ} (hε : 0 < ε) :
    IsPotential A (kappaEp L s ε) :=
  ReciprocityTheory.AnForm.M.isPotentialAdd A _ _ (ReciprocityTheory.AnForm.M.isPotentialRsmul A 2 L hL)
    (ReciprocityTheory.AnForm.M.isPotential_ofFun A _ (smooth_logNormSqAdd hL hS hε))

theorem kappaEp_formNonneg [CompactSpace X] {A : FinHolAtlas e X} (Om : KaehlerForm A)
    {L : LocPot X} {s : X → X → ℂ} (hL : IsPotential A L) (hS : IsSection A L s) :
    ∃ Cκ : ℝ, 0 ≤ Cκ ∧ ∀ ε, 0 < ε → FormNonneg A Set.univ (kappaEp L s ε + Om.pot.rsmul Cκ) := by
  obtain ⟨M, hM0, hM⟩ := levi_abs_le_global A isCompact_univ L Om.pot hL Om.isPot Om.pos
  refine ⟨2 * M, by positivity, fun ε hε x k y hy w => ?_⟩
  have hyt : y ∈ (A.chart k).target := hy.1
  have hyL : (A.chart k).symm y ∈ L.U x := hy.2.2.1.1
  have hyΩ : (A.chart k).symm y ∈ Om.pot.U x := hy.2.2.2
  set S := s x ∘ (A.chart k).symm with hSdef
  set Φ := L.φ x ∘ (A.chart k).symm with hΦdef
  set Ψ := Om.pot.φ x ∘ (A.chart k).symm with hΨdef
  have hO : IsOpen ((A.chart k).target ∩ (A.chart k).symm ⁻¹' L.U x) :=
    (A.chart k).isOpen_inter_preimage_symm (L.isOpen_U x)
  have hSa : AnalyticAt ℂ S y := hS.1 x k y ⟨hyt, hyL⟩
  have hΦ2 : ContDiffAt ℝ 2 Φ y := ReciprocityTheory.AnForm.M.pot_contDiffAt_two hL x k hyt hyL
  have hΨ2 : ContDiffAt ℝ 2 Ψ y := ReciprocityTheory.AnForm.M.pot_contDiffAt_two Om.isPot x k hyt hyΩ
  have heq : (kappaEp L s ε).φ x ∘ (A.chart k).symm =ᶠ[𝓝 y]
      fun z => Real.log (‖S z‖ ^ 2 + ε * Real.exp (2 * Φ z)) := by
    filter_upwards [hO.mem_nhds ⟨hyt, hyL⟩] with z hz
    exact kappaEp_φ_eq_local hS hz.2 hε
  have hK2 : ContDiffAt ℝ 2 (fun z => Real.log (‖S z‖ ^ 2 + ε * Real.exp (2 * Φ z))) y := by
    have hSc : ContDiffAt ℝ 2 S y := (hSa.restrictScalars (𝕜 := ℝ)).contDiffAt
    refine (((contDiff_norm_sq ℝ).contDiffAt.comp y hSc).add
      (contDiffAt_const.mul (contDiffAt_const.mul hΦ2).exp)).log ?_
    exact (by positivity : (0 : ℝ) < ‖S y‖ ^ 2 + ε * Real.exp (2 * Φ y)).ne'
  have hκ2 := hK2.congr_of_eventuallyEq heq
  have hsum : (kappaEp L s ε + Om.pot.rsmul (2 * M)).φ x ∘ (A.chart k).symm =
      fun z => ((kappaEp L s ε).φ x ∘ (A.chart k).symm) z + (2 * M) * Ψ z := rfl
  rw [hsum, levi_add_smul (2 * M) hκ2 hΨ2 w, levi_congr heq w]
  have hA := levi_log_normSq_add_exp hSa hΦ2 hε w
  have hB := hM x k y ⟨hyt, hyL, hyΩ⟩ w
  have hΨnn : 0 ≤ levi Ψ y w := by
    rcases eq_or_ne w 0 with h0 | h0
    · rw [h0, ReciprocityTheory.AnForm.levi_zero]
    · exact (Om.pos x k y ⟨hyt, hyΩ⟩ w h0).le
  set E := ε * Real.exp (2 * Φ y) with hE
  have hE0 : 0 < E := mul_pos hε (Real.exp_pos _)
  have hh : 0 < ‖S y‖ ^ 2 + E := by positivity
  set c := 2 * E / (‖S y‖ ^ 2 + E) with hc
  have hc0 : 0 ≤ c := by positivity
  have hc2 : c ≤ 2 := by
    rw [hc, div_le_iff₀ hh]
    nlinarith [sq_nonneg ‖S y‖]
  have hl := (abs_le.mp hB).1
  have hMΨ : 0 ≤ M * levi Ψ y w := mul_nonneg hM0 hΨnn
  nlinarith

def zeroSet (s : X → X → ℂ) : Set X := {y | s y y = 0}

theorem zero_iff_local {A : FinHolAtlas e X} {L : LocPot X} {s : X → X → ℂ}
    (hS : IsSection A L s) {x y : X} (hy : y ∈ L.U x) : s y y = 0 ↔ s x y = 0 := by
  have h := hS.2 y x y ⟨L.mem_U y, hy⟩
  constructor
  · intro h0
    rw [h0, norm_zero, zero_mul] at h
    exact norm_eq_zero.mp ((mul_eq_zero.mp h.symm).resolve_right (Real.exp_pos _).ne')
  · intro h0
    rw [h0, norm_zero, zero_mul] at h
    exact norm_eq_zero.mp ((mul_eq_zero.mp h).resolve_right (Real.exp_pos _).ne')

theorem zeroSet_analytic {A : FinHolAtlas e X} {L : LocPot X} {s : X → X → ℂ}
    (hS : IsSection A L s) : A.IsAnalyticSubset (zeroSet s) := by
  intro x
  refine ⟨L.U x, L.isOpen_U x, L.mem_U x, 1, fun _ => s x, fun _ => hS.1 x, ?_⟩
  ext y
  simp only [zeroSet, Set.mem_inter_iff, Set.mem_ofPred_eq, forall_const]
  constructor
  · rintro ⟨h0, hy⟩
    exact ⟨hy, (zero_iff_local hS hy).1 h0⟩
  · rintro ⟨hy, h0⟩
    exact ⟨(zero_iff_local hS hy).2 h0, hy⟩

theorem interior_zeroSet {A : FinHolAtlas e X} {L : LocPot X} {s : X → X → ℂ}
    (hS : IsSection A L s) {r : ℕ} {m : Fin r → ℕ} {W : Fin r → Set X}
    (hsnc : IsSNC A L s m W) : interior (zeroSet s) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨ψ, -, hxψ, hψL, σ, -, -, u, -, hu0, hprod⟩ := hsnc x
  have hOimg : IsOpen (ψ '' (ψ.source ∩ interior (zeroSet s))) :=
    ψ.isOpen_image_source_inter isOpen_interior
  have hne : (ψ '' (ψ.source ∩ interior (zeroSet s))).Nonempty := ⟨ψ x, x, ⟨hxψ, hx⟩, rfl⟩
  have hsub : ψ '' (ψ.source ∩ interior (zeroSet s)) ⊆ ⋃ i, {z : Fin e → ℂ | z i = 0} := by
    rintro _ ⟨y, ⟨hyψ, hyZ⟩, rfl⟩
    have hz : y ∈ zeroSet s := interior_subset hyZ
    have h0 : s x y = 0 := (zero_iff_local hS (hψL hyψ)).1 hz
    rw [hprod y hyψ] at h0
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h (hu0 y hyψ)
    · obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.1 h
      revert hk
      cases hσ : σ k with
      | none => intro hk; exact absurd hk one_ne_zero
      | some i => intro hk; exact Set.mem_iUnion.2 ⟨i, eq_zero_of_pow_eq_zero hk⟩
  have hpos := hOimg.measure_pos volume hne
  have hnull : volume (⋃ i, {z : Fin e → ℂ | z i = 0}) = 0 :=
    measure_iUnion_null fun i => ReciprocityTheory.AnForm.M.PLAux.volume_coord_eq_zero i
  exact hpos.ne' (measure_mono_null hsub hnull)

theorem greenEp_eq_off (L : LocPot X) (s : X → X → ℂ) {ε : ℝ} (hε : 0 < ε) {y : X}
    (hy : y ∉ zeroSet s) :
    greenEp L s ε y = -2 * logNormSec L s y + logNormSqAdd L s ε y := by
  have hn : 0 < secNorm L s y := mul_pos (norm_pos_iff.2 hy) (Real.exp_pos _)
  have h1 : 1 + ε / secNorm L s y ^ 2 = (secNorm L s y ^ 2 + ε) / secNorm L s y ^ 2 := by
    field_simp
  unfold greenEp logNormSqAdd
  rw [h1, Real.log_div (by positivity) (by positivity), Real.log_pow]
  show _ = -2 * Real.log (secNorm L s y) + _
  push_cast
  ring

theorem greenEp_nonneg (L : LocPot X) (s : X → X → ℂ) {ε : ℝ} (hε : 0 < ε) (y : X) :
    0 ≤ greenEp L s ε y :=
  Real.log_nonneg (le_add_of_nonneg_right (div_nonneg hε.le (sq_nonneg _)))

end GreenMassReplace

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end
end
