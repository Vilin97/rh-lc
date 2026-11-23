module

public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Polynomial.Basic
public import ReciprocityTheory.L2DbarEstimates.LeviForms.EventuallyDifferentiableAtOfContDiffAt
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatCalcA
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxE

-- Source module: ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.RegMaxA

section

@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

variable {n : ℕ}

lemma rm_wdb_ofReal_eventually (F : V n → ℝ) (y : V n) (hF : ContDiffAt ℝ 2 F y) (k : Fin n) :
    wdb n k (fun x => (F x : ℂ)) =ᶠ[𝓝 y] fun x =>
      (((fderiv ℝ F x (bas n k) : ℝ) : ℂ) +
        Complex.I * ((fderiv ℝ F x (Complex.I • bas n k) : ℝ) : ℂ)) / 2 := by
  filter_upwards [hF.eventually (by simp)] with x hx
  have hd : HasFDerivAt (fun x => (F x : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ F x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x (hx.differentiableAt (by norm_num)).hasFDerivAt
  unfold wdb
  rw [hd.fderiv]
  simp

lemma rm_hasFDerivAt_fderiv_apply_ofReal (F : V n → ℝ) (y : V n) (hF : ContDiffAt ℝ 2 F y)
    (w : V n) :
    HasFDerivAt (fun x => ((fderiv ℝ F x w : ℝ) : ℂ))
      (Complex.ofRealCLM.comp ((fderiv ℝ (fderiv ℝ F) y).flip w)) y := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ F) y := hF.fderiv_right (by norm_num)
  have h2 : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) y) y :=
    (h1.differentiableAt (by norm_num)).hasFDerivAt
  have h3 : HasFDerivAt (fun x => fderiv ℝ F x w) ((fderiv ℝ (fderiv ℝ F) y).flip w) y := by
    have := h2.clm_apply (hasFDerivAt_const w y)
    rw [ContinuousLinearMap.comp_zero, zero_add] at this
    exact this
  exact Complex.ofRealCLM.hasFDerivAt.comp y h3

lemma rm_wd_wdb_ofReal (F : V n → ℝ) (y : V n) (hF : ContDiffAt ℝ 2 F y) (j k : Fin n) :
    wd n j (wdb n k (fun x => (F x : ℂ))) y =
      (((fderiv ℝ (fderiv ℝ F) y (bas n j) (bas n k) : ℝ) : ℂ)
        + Complex.I * ((fderiv ℝ (fderiv ℝ F) y (bas n j) (Complex.I • bas n k) : ℝ) : ℂ)
        - Complex.I * ((fderiv ℝ (fderiv ℝ F) y (Complex.I • bas n j) (bas n k) : ℝ) : ℂ)
        + ((fderiv ℝ (fderiv ℝ F) y (Complex.I • bas n j) (Complex.I • bas n k) : ℝ) : ℂ)) / 4 := by
  have hS := (rm_hasFDerivAt_fderiv_apply_ofReal F y hF (bas n k)).add
    ((rm_hasFDerivAt_fderiv_apply_ofReal F y hF (Complex.I • bas n k)).const_mul Complex.I)
  have hG := HasFDerivAt.const_mul (𝔸 := ℂ) hS ((2 : ℂ)⁻¹)
  have hfd := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) (rm_wdb_ofReal_eventually F y hF k)
  have hfun : (fun x => (((fderiv ℝ F x (bas n k) : ℝ) : ℂ) +
      Complex.I * ((fderiv ℝ F x (Complex.I • bas n k) : ℝ) : ℂ)) / 2) =
      fun x => (2 : ℂ)⁻¹ * (((fun x => ((fderiv ℝ F x (bas n k) : ℝ) : ℂ)) +
        fun y => Complex.I * ((fderiv ℝ F y (Complex.I • bas n k) : ℝ) : ℂ)) x) := by
    funext x
    simp only [Pi.add_apply]
    ring
  unfold wd
  rw [hfd, hfun, hG.fderiv]
  simp
  ring_nf
  rw [Complex.I_sq]
  ring

def rmVec (ξ : Fin n → ℂ) : V n := ∑ j, ξ j • bas n j

lemma rm_cplx_smul_eq (z : ℂ) (x : V n) : z • x = z.re • x + z.im • (Complex.I • x) := by
  conv_lhs => rw [← Complex.re_add_im z]
  rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]

lemma rm_bil_expand (B : V n →L[ℝ] V n →L[ℝ] ℝ) (z w : ℂ) (a b : V n) :
    B (z • a) (w • b) = z.re * w.re * B a b + z.re * w.im * B a (Complex.I • b)
      + z.im * w.re * B (Complex.I • a) b + z.im * w.im * B (Complex.I • a) (Complex.I • b) := by
  rw [rm_cplx_smul_eq z a, rm_cplx_smul_eq w b]
  simp only [map_add (f := _), map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

lemma rm_bil_sum (B : V n →L[ℝ] V n →L[ℝ] ℝ) (c : Fin n → ℂ) :
    B (∑ j, c j • bas n j) (∑ k, c k • bas n k) = ∑ j, ∑ k, B (c j • bas n j) (c k • bas n k) := by

  simp only [map_sum, ContinuousLinearMap.sum_apply]
  exact Finset.sum_comm

lemma rm_I_smul_vec (ξ : Fin n → ℂ) : Complex.I • rmVec ξ = ∑ j, (Complex.I * ξ j) • bas n j := by
  unfold rmVec
  rw [Finset.smul_sum]
  simp_rw [smul_smul]

theorem rm_levi_re_ofReal (F : V n → ℝ) (y : V n) (hF : ContDiffAt ℝ 2 F y) (ξ : Fin n → ℂ) :
    4 * (leviV n (fun x => (F x : ℂ)) y ξ).re =
      fderiv ℝ (fderiv ℝ F) y (rmVec ξ) (rmVec ξ) +
        fderiv ℝ (fderiv ℝ F) y (Complex.I • rmVec ξ) (Complex.I • rmVec ξ) := by
  rw [rm_I_smul_vec]
  unfold rmVec
  rw [rm_bil_sum, rm_bil_sum, ← Finset.sum_add_distrib]
  unfold leviV
  rw [Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [rm_wd_wdb_ofReal F y hF j k, rm_bil_expand (fderiv ℝ (fderiv ℝ F) y) (ξ j) (ξ k),
    rm_bil_expand (fderiv ℝ (fderiv ℝ F) y) (Complex.I * ξ j) (Complex.I * ξ k)]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  simp [Complex.mul_re, Complex.mul_im]
  ring

end

end ReciprocityTheory.L2DbarEstimates.Y
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHoloQuadraticAddLeviIsLittleO

section

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.TaylorLevi

theorem taylor_two {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (φ : E → ℝ) (p : E)
    (hφ : ContDiffAt ℝ 2 φ p) :
    (fun v => φ v - φ p - fderiv ℝ φ p (v - p) - fderiv ℝ (fderiv ℝ φ) p (v - p) (v - p) / 2)
      =o[𝓝 p] (fun v => ‖v - p‖ ^ 2) := by
  set D := fderiv ℝ φ p
  set B := fderiv ℝ (fderiv ℝ φ) p
  have hB : HasFDerivAt (fderiv ℝ φ) B p :=
    ((hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
  have hsymm : ∀ u w, B u w = B w u := fun u w =>
    (hφ.isSymmSndFDerivAt (by simp)) u w
  have hdiff := eventually_differentiableAt_of_contDiffAt hφ
  have hlo := hB.isLittleO
  set g : E → ℝ := fun w => φ w - D (w - p) - 1 / 2 * B (w - p) (w - p)
  have hg : ∀ w, DifferentiableAt ℝ φ w → HasFDerivAt g (fderiv ℝ φ w - D - B (w - p)) w := by
    intro w hw
    have h1 : HasFDerivAt (fun x : E => x - p) (ContinuousLinearMap.id ℝ E) w :=
      (hasFDerivAt_id w).sub_const p
    have h2 : HasFDerivAt (fun y => B (y - p) (y - p)) _ w := B.hasFDerivAt_of_bilinear h1 h1
    have h3 := (hw.hasFDerivAt.sub (D.hasFDerivAt.comp w h1)).sub (HasFDerivAt.const_mul h2 (1 / 2 : ℝ))
    refine h3.congr_fderiv ?_
    ext u
    simp
    rw [hsymm u w, hsymm u p]
    ring
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have h4 := (Asymptotics.isLittleO_iff.1 hlo) hc
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 (h4.and hdiff)
  filter_upwards [Metric.ball_mem_nhds p hδ] with v hv
  have hsub : closedBall p ‖v - p‖ ⊆ ball p δ := by
    apply closedBall_subset_ball
    rw [← dist_eq_norm]; exact mem_ball.1 hv
  have hmvt := (convex_closedBall p ‖v - p‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := g) (C := c * ‖v - p‖)
    (fun w hw => (hg w (hball w (hsub hw)).2).hasFDerivWithinAt)
    (fun w hw => by
      have hw' := hball w (hsub hw)
      have e1 : ‖fderiv ℝ φ w - D - B (w - p)‖ ≤ c * ‖w - p‖ := by
        simpa using hw'.1
      have e2 : ‖w - p‖ ≤ ‖v - p‖ := by rw [← dist_eq_norm]; exact mem_closedBall.1 hw
      exact e1.trans (mul_le_mul_of_nonneg_left e2 hc.le))
    (mem_closedBall_self (norm_nonneg _)) (by rw [mem_closedBall, dist_eq_norm])
  have : g v - g p = φ v - φ p - D (v - p) - B (v - p) (v - p) / 2 := by
    simp only [g]; rw [sub_self]; simp; ring
  rw [this] at hmvt
  rw [norm_pow, norm_norm]
  calc _ ≤ c * ‖v - p‖ * ‖v - p‖ := hmvt
    _ = c * ‖v - p‖ ^ 2 := by ring

end GlobalTheory.TaylorLevi

namespace GlobalTheory.TaylorLevi

variable {n : ℕ}

noncomputable section

theorem rmVec_coord (h : V n) : rmVec (fun j => h j) = h := by
  ext i
  simp [rmVec, bas, PiLp.single_apply, Pi.single_apply]

def linCoef (D : V n →L[ℝ] ℝ) (j : Fin n) : ℂ :=
  (D (bas n j) : ℂ) - Complex.I * (D (Complex.I • bas n j) : ℂ)

def quadCoef (B : V n →L[ℝ] V n →L[ℝ] ℝ) (j k : Fin n) : ℂ :=
  ((B (bas n j) (bas n k) - B (Complex.I • bas n j) (Complex.I • bas n k) : ℝ) : ℂ)
    - Complex.I * ((B (Complex.I • bas n j) (bas n k) + B (bas n j) (Complex.I • bas n k) : ℝ) : ℂ)

theorem lin_re (D : V n →L[ℝ] ℝ) (ξ : Fin n → ℂ) :
    (∑ j, linCoef D j * ξ j).re = D (rmVec ξ) := by

  simp only [rmVec, map_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [rm_cplx_smul_eq]
  simp [linCoef, Complex.mul_re]
  ring

theorem quad_re (B : V n →L[ℝ] V n →L[ℝ] ℝ) (ξ : Fin n → ℂ) :
    (∑ j, ∑ k, quadCoef B j k * ξ j * ξ k).re =
      B (rmVec ξ) (rmVec ξ) - B (Complex.I • rmVec ξ) (Complex.I • rmVec ξ) := by
  rw [rm_I_smul_vec, rmVec, rm_bil_sum, rm_bil_sum, Complex.re_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.re_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [rm_bil_expand B (ξ j) (ξ k), rm_bil_expand B (Complex.I * ξ j) (Complex.I * ξ k)]
  simp [quadCoef, Complex.mul_re, Complex.mul_im]
  ring

end

end GlobalTheory.TaylorLevi

namespace GlobalTheory.TaylorLevi

theorem exists_holo_quadratic_add_levi : ∀ (n : ℕ) (φ : V n → ℝ) (p : V n), ContDiffAt ℝ 2 φ p →
    ∃ q : V n → ℂ, Differentiable ℂ q ∧
      (fun v : V n => φ v - 2 * (q v).re
        - (leviV n (fun w => ((φ w : ℝ) : ℂ)) p (fun j => (v - p) j)).re)
        =o[𝓝 p] (fun v : V n => ‖v - p‖ ^ 2) := by
  intro n φ p hφ
  set D := fderiv ℝ φ p
  set B := fderiv ℝ (fderiv ℝ φ) p
  refine ⟨fun v => (φ p : ℂ) / 2 + (∑ j, linCoef D j * (v - p) j) / 2
      + (∑ j, ∑ k, quadCoef B j k * (v - p) j * (v - p) k) / 8, ?_, ?_⟩
  · have hc : ∀ j, Differentiable ℂ (fun v : V n => (v - p) j) := fun j =>
      (EuclideanSpace.proj j : V n →L[ℂ] ℂ).differentiable.comp (differentiable_id.sub_const p)
    fun_prop
  · refine (taylor_two φ p hφ).congr' ?_ (EventuallyEq.refl _ _)
    filter_upwards with v
    have hL := rm_levi_re_ofReal φ p hφ (fun j => (v - p) j)
    have hA := lin_re D (fun j => (v - p) j)
    have hQ := quad_re B (fun j => (v - p) j)
    rw [rmVec_coord] at hL hA hQ
    have hq : ((φ p : ℂ) / 2 + (∑ j, linCoef D j * (v - p) j) / 2
        + (∑ j, ∑ k, quadCoef B j k * (v - p) j * (v - p) k) / 8).re
        = φ p / 2 + (∑ j, linCoef D j * (v - p) j).re / 2
          + (∑ j, ∑ k, quadCoef B j k * (v - p) j * (v - p) k).re / 8 := by
      simp only [Complex.add_re, Complex.div_ofNat_re, Complex.ofReal_re]
    rw [hq, hA, hQ]
    linarith

end GlobalTheory.TaylorLevi
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHoloQuadraticAddLeviIsLittleOStatement

section

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.exists_holo_quadratic_add_levi_isLittleO : ∀ (n : ℕ) (φ : V n → ℝ) (p : V n), ContDiffAt ℝ 2 φ p → ∃ q : V n → ℂ, Differentiable ℂ q ∧ (fun v : V n => φ v - 2 * (q v).re - (leviV n (fun w => ((φ w : ℝ) : ℂ)) p (fun j => (v - p) j)).re) =o[𝓝 p] (fun v : V n => ‖v - p‖ ^ 2) := by
  first | exact @GlobalTheory.TaylorLevi.exists_holo_quadratic_add_levi | exact GlobalTheory.TaylorLevi.exists_holo_quadratic_add_levi | (intros; apply GlobalTheory.TaylorLevi.exists_holo_quadratic_add_levi <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PshNormalFrameQuadraticComparison

section

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem leviV_re_le_sum_norm {n : ℕ} (g : V n → ℂ) (p ζ : V n) :
    (leviV n g p ζ.ofLp).re ≤
      (∑ j, ∑ k, ‖wd n j (wdb n k g) p‖) * ‖ζ‖ ^ 2 := by
  calc (leviV n g p ζ.ofLp).re ≤ ‖leviV n g p ζ.ofLp‖ := Complex.re_le_norm _
    _ ≤ ∑ j, ‖∑ k, wd n j (wdb n k g) p * ζ.ofLp j * (starRingEnd ℂ) (ζ.ofLp k)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ j, ∑ k, ‖wd n j (wdb n k g) p‖ * ‖ζ‖ ^ 2 := by
        gcongr with j _
        refine (norm_sum_le _ _).trans ?_
        gcongr with k _
        rw [norm_mul, norm_mul, Complex.norm_conj, sq, ← mul_assoc]
        have hj : ‖ζ.ofLp j‖ ≤ ‖ζ‖ := PiLp.norm_apply_le ζ j
        have hk : ‖ζ.ofLp k‖ ≤ ‖ζ‖ := PiLp.norm_apply_le ζ k
        gcongr
    _ = (∑ j, ∑ k, ‖wd n j (wdb n k g) p‖) * ‖ζ‖ ^ 2 := by
        simp only [Finset.sum_mul]

theorem psh_normal_frame : ∀ (n : ℕ) (O : Set (V n)) (φ : V n → ℝ) (p : V n), IsOpen O → p ∈ O → ContDiffOn ℝ ∞ φ O → (∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < (leviV n (fun w => ((φ w : ℝ) : ℂ)) p ξ).re) → ∃ (q : V n → ℂ) (c C ρ : ℝ), Differentiable ℂ q ∧ 0 < c ∧ 0 < C ∧ 0 < ρ ∧ closedBall p ρ ⊆ O ∧ ∀ v ∈ closedBall p ρ, c * ‖v - p‖ ^ 2 ≤ φ v - 2 * (q v).re ∧ φ v - 2 * (q v).re ≤ C * ‖v - p‖ ^ 2 := by
  intro n O φ p hO hp hφ hlevi
  set g : V n → ℂ := fun w => ((φ w : ℝ) : ℂ) with hg
  have hgs : ContDiffOn ℝ ∞ g O := Complex.ofRealCLM.contDiff.comp_contDiffOn hφ
  obtain ⟨m, hm, hmb⟩ := levi_pos_compact (g := g) hO hgs (K0 := {p}) isCompact_singleton
    (Set.singleton_subset_iff.2 hp) (fun u hu ζ hζ => by
      rw [Set.mem_singleton_iff.1 hu]
      refine hlevi _ ?_
      intro h0; apply hζ
      exact (WithLp.ofLp_eq_zero 2).1 h0)
  have hφ2 : ContDiffAt ℝ 2 φ p :=
    ((hφ.contDiffAt (hO.mem_nhds hp)).of_le (by norm_cast))
  obtain ⟨q, hq, ho⟩ := GlobalTheory.T.exists_holo_quadratic_add_levi_isLittleO n φ p hφ2
  set A : ℝ := ∑ j, ∑ k, ‖wd n j (wdb n k g) p‖ with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => norm_nonneg _
  have hev := ho.def (half_pos hm)
  obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff.1 hev
  obtain ⟨ε2, hε2, hε2O⟩ := Metric.isOpen_iff.1 hO p hp
  refine ⟨q, m / 2, A + m / 2, min ε ε2 / 2, hq, half_pos hm, by positivity,
    by positivity, ?_, ?_⟩
  · intro v hv
    apply hε2O
    rw [mem_closedBall] at hv
    rw [mem_ball]
    have : min ε ε2 / 2 < ε2 := by
      have := min_le_right ε ε2; linarith [lt_min hε hε2]
    linarith
  · intro v hv
    rw [mem_closedBall] at hv
    have hvε : dist v p < ε := by
      have := min_le_left ε ε2; linarith [lt_min hε hε2]
    have hR := hεb hvε
    rw [Real.norm_eq_abs, norm_pow, norm_norm] at hR
    have hlo := hmb p rfl (v - p)
    have hup := leviV_re_le_sum_norm g p (v - p)
    have habs := abs_le.1 hR
    change m * ‖v - p‖ ^ 2 ≤ (leviV n g p (fun j => (v - p) j)).re at hlo
    change (leviV n g p (fun j => (v - p) j)).re ≤ A * ‖v - p‖ ^ 2 at hup
    constructor <;> nlinarith [habs.1, habs.2, sq_nonneg ‖v - p‖]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PshNormalFrameQuadraticComparisonStatement

section

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.psh_normal_frame_quadratic_comparison : ∀ (n : ℕ) (O : Set (V n)) (φ : V n → ℝ) (p : V n), IsOpen O → p ∈ O → ContDiffOn ℝ ∞ φ O → (∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < (leviV n (fun w => ((φ w : ℝ) : ℂ)) p ξ).re) → ∃ (q : V n → ℂ) (c C ρ : ℝ), Differentiable ℂ q ∧ 0 < c ∧ 0 < C ∧ 0 < ρ ∧ closedBall p ρ ⊆ O ∧ ∀ v ∈ closedBall p ρ, c * ‖v - p‖ ^ 2 ≤ φ v - 2 * (q v).re ∧ φ v - 2 * (q v).re ≤ C * ‖v - p‖ ^ 2 := by
  first | exact @GlobalTheory.psh_normal_frame | exact GlobalTheory.psh_normal_frame | (intros; apply GlobalTheory.psh_normal_frame <;> assumption)
end
end
