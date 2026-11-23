module

public import Formalism.SharpRestriction.CuspSpanNormBounds.SGauge
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SGaugeDensB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SGaugeDensG
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SGaugeDensL
import Mathlib.Tactic.Linter.Style
import Mathlib.Topology.Algebra.Group.Units

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SGaugeDensD

section

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace Formalism.MainNotions.S.Gauge

variable {n : ℕ}

theorem tendsto_ratioAt_of_ball {ε : Fin n → Bool} {c s : ℝ} (hc : 0 < c) (hs : 0 < s)
    (hb : ∀ ρ : ℝ, 0 < ρ → ρ ≤ s →
      Formalism.REAL.muG ε (expSet ε (Metric.ball (0 : gLie ε) ρ)) = ENNReal.ofReal c * ∫⁻ t in Metric.ball (0 : EL ε) ρ, jd ε t) :
    Tendsto (ratioAt ε) (𝓝[>] (0 : ℝ)) (𝓝 c) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro e he
  set δ : ℝ := min (1 / 2) (e / (2 * c)) with hδ
  have hδpos : 0 < δ := lt_min (by norm_num) (div_pos he (by linarith))
  have hδ1 : δ ≤ 1 / 2 := min_le_left _ _
  have hδe : c * δ < e := by
    have : δ ≤ e / (2 * c) := min_le_right _ _
    calc c * δ ≤ c * (e / (2 * c)) := mul_le_mul_of_nonneg_left this hc.le
      _ = e / 2 := by field_simp
      _ < e := by linarith
  have hJc := (continuous_chartJac_thetaExp ε).continuousAt (x := 0)
  obtain ⟨η, hη, hcont⟩ := Metric.continuousAt_iff.1 hJc δ hδpos
  refine ⟨min η s, lt_min hη hs, fun ρ hρpos hρd => ?_⟩
  have hρ0 : 0 < ρ := hρpos
  have hρd' : ρ < min η s := by
    have : dist ρ 0 < min η s := hρd
    rwa [Real.dist_eq, sub_zero, abs_of_pos hρ0] at this
  have hρη : ρ ≤ η := (lt_of_lt_of_le hρd' (min_le_left _ _)).le
  have hρr : ρ ≤ s := (lt_of_lt_of_le hρd' (min_le_right _ _)).le
  have hbound : ∀ t ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin (dimL ε))) ρ, |chartJac (thetaExp ε) t - 1| < δ := by
    intro t ht
    have := hcont (lt_of_lt_of_le ht hρη)
    rw [chartJac_thetaExp_zero, Real.dist_eq] at this
    exact this
  set V := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (dimL ε))) ρ) with hV
  have hVpos : 0 < V := Metric.measure_ball_pos volume 0 hρ0
  have hVfin : V ≠ ⊤ := measure_ball_lt_top.ne
  set I := ∫⁻ t in Metric.ball (0 : EuclideanSpace ℝ (Fin (dimL ε))) ρ, ENNReal.ofReal (chartJac (thetaExp ε) t) with hI
  have hup : I ≤ ENNReal.ofReal (1 + δ) * V := by
    calc I ≤ ∫⁻ _ in Metric.ball (0 : EuclideanSpace ℝ (Fin (dimL ε))) ρ, ENNReal.ofReal (1 + δ) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
          exact ENNReal.ofReal_le_ofReal (by linarith [(abs_lt.1 (hbound x hx)).2])
      _ = ENNReal.ofReal (1 + δ) * V := setLIntegral_const _ _
  have hlo : ENNReal.ofReal (1 - δ) * V ≤ I := by
    calc ENNReal.ofReal (1 - δ) * V = ∫⁻ _ in Metric.ball (0 : EuclideanSpace ℝ (Fin (dimL ε))) ρ, ENNReal.ofReal (1 - δ) :=
          (setLIntegral_const _ _).symm
      _ ≤ I := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
          exact ENNReal.ofReal_le_ofReal (by linarith [(abs_lt.1 (hbound x hx)).1])
  have hIfin : I ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVfin) hup
  have hVr : 0 < V.toReal := ENNReal.toReal_pos hVpos.ne' hVfin
  have hupR : I.toReal ≤ (1 + δ) * V.toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVfin) hup
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)] at this
  have hloR : (1 - δ) * V.toReal ≤ I.toReal := by
    have := ENNReal.toReal_mono hIfin hlo
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)] at this
  have hratio : ratioAt ε ρ = c * I.toReal / V.toReal := by
    unfold ratioAt
    rw [hb ρ hρ0 hρr, volume_ball_gLie, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le]
    rfl
  rw [Real.dist_eq, hratio]
  have key : |c * I.toReal / V.toReal - c| ≤ c * δ := by
    rw [abs_le]
    constructor
    · have : c * ((1 - δ) * V.toReal) ≤ c * I.toReal := mul_le_mul_of_nonneg_left hloR hc.le
      rw [le_sub_iff_add_le, le_div_iff₀ hVr]
      nlinarith
    · have : c * I.toReal ≤ c * ((1 + δ) * V.toReal) := mul_le_mul_of_nonneg_left hupR hc.le
      rw [sub_le_iff_le_add, div_le_iff₀ hVr]
      nlinarith
  exact lt_of_le_of_lt key hδe

theorem densOfBall (ε : Fin n → Bool) : DensOfBall ε := by
  rintro ⟨c, hc, s, hs, hb⟩
  have ht := tendsto_ratioAt_of_ball hc hs hb
  have he := gaugeU_eq ht
  exact ⟨he ▸ ht, he ▸ hc⟩

end Formalism.MainNotions.S.Gauge
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SGaugeDensJ

section

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace Formalism.MainNotions.S.Gauge

variable {n : ℕ}

section JacInvSec

variable {N : ℕ}

def lmulP (Z : Matrix (Fin n) (Fin n) ℂ) : MP n →L[ℝ] MP n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => Matrix.of.symm (Z * Matrix.of X)
      map_add' := fun X Y => by
        funext i j
        simp [Matrix.mul_apply, Finset.sum_add_distrib, mul_add]
      map_smul' := fun c X => by
        funext i j
        simp [Matrix.mul_apply, Finset.smul_sum, mul_left_comm] }

theorem lmulP_apply (Z : Matrix (Fin n) (Fin n) ℂ) (X : MP n) : lmulP Z X = Matrix.of.symm (Z * Matrix.of X) := rfl

theorem of_sum_smul (c : Fin N → ℝ) (X : Fin N → MP n) :
    Matrix.of (∑ k, c k • X k) = ∑ k, c k • Matrix.of (X k) := by
  ext i j
  simp [Matrix.sum_apply, Finset.sum_apply]

theorem sum_single (v : EuclideanSpace ℝ (Fin N)) : v = ∑ k, v k • EuclideanSpace.single k (1 : ℝ) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin N) ℝ).sum_repr v]
  simp [EuclideanSpace.basisFun_apply]

theorem mul_dPart {Θ : EuclideanSpace ℝ (Fin N) → MP n} {U : Set (EuclideanSpace ℝ (Fin N))}
    {φ : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)} {Z : Matrix (Fin n) (Fin n) ℂ}
    (hΘ : Differentiable ℝ Θ) (hU : IsOpen U) (hφ : DifferentiableOn ℝ φ U)
    (h : ∀ t ∈ U, Matrix.of (Θ (φ t)) = Z * Matrix.of (Θ t)) {t : EuclideanSpace ℝ (Fin N)} (ht : t ∈ U) (i : Fin N) :
    Z * Matrix.of (dPart Θ t i) =
      ∑ k, (fderiv ℝ φ t (EuclideanSpace.single i 1) k) • Matrix.of (dPart Θ (φ t) k) := by
  have hφt : DifferentiableAt ℝ φ t := hφ.differentiableAt (hU.mem_nhds ht)
  have heq : (Θ ∘ φ) =ᶠ[𝓝 t] (lmulP Z ∘ Θ) := by
    filter_upwards [hU.mem_nhds ht] with s hs
    simp only [Function.comp_apply, lmulP_apply, ← h s hs, Equiv.symm_apply_apply]
  have h1 : fderiv ℝ (Θ ∘ φ) t = (fderiv ℝ Θ (φ t)).comp (fderiv ℝ φ t) := fderiv_comp t (hΘ _) hφt
  have h2 : fderiv ℝ (lmulP Z ∘ Θ) t = (lmulP Z).comp (fderiv ℝ Θ t) := by
    rw [fderiv_comp t (lmulP Z).differentiableAt (hΘ t), ContinuousLinearMap.fderiv]
  have h3 := heq.fderiv_eq (𝕜 := ℝ)
  rw [h1, h2] at h3
  have h4 := congrArg (fun L => L (EuclideanSpace.single i 1)) h3
  simp only [ContinuousLinearMap.comp_apply, lmulP_apply] at h4

  rw [sum_single (fderiv ℝ φ t (EuclideanSpace.single i 1)), map_sum] at h4
  simp only [map_smul] at h4
  have h5 := congrArg Matrix.of h4
  rw [Equiv.apply_symm_apply] at h5
  simp only [dPart]
  exact h5.symm.trans (of_sum_smul _ _)

theorem chartJac_mul_det {Θ : EuclideanSpace ℝ (Fin N) → MP n} {U : Set (EuclideanSpace ℝ (Fin N))}
    {φ : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)} {Z : Matrix (Fin n) (Fin n) ℂ}
    (hΘ : Differentiable ℝ Θ) (hinv : ∀ s, IsUnit (Matrix.of (Θ s)).det) (hU : IsOpen U) (hφ : DifferentiableOn ℝ φ U)
    (h : ∀ t ∈ U, Matrix.of (Θ (φ t)) = Z * Matrix.of (Θ t)) {t : EuclideanSpace ℝ (Fin N)} (ht : t ∈ U) :
    chartJac Θ (φ t) * |(fderiv ℝ φ t).det| = chartJac Θ t := by
  set D : Matrix (Fin N) (Fin N) ℝ := Matrix.of fun k i => fderiv ℝ φ t (EuclideanSpace.single i 1) k with hDdef
  set M := Matrix.of (Θ t)
  set M' := Matrix.of (Θ (φ t))
  have hM' : M' = Z * M := h t ht
  have hZ : IsUnit Z.det := by
    have := hinv (φ t)
    change IsUnit M'.det at this
    rw [hM', Matrix.det_mul] at this
    exact isUnit_of_mul_isUnit_left this
  have hMinv : M⁻¹ = M'⁻¹ * Z := by
    rw [hM', Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hZ, Matrix.mul_one]
  set w : EuclideanSpace ℝ (Fin N) → Fin N → EuclideanSpace ℝ (Fin n × Fin n × Bool) :=
    fun s i => realV ((Matrix.of (Θ s))⁻¹ * Matrix.of (dPart Θ s i)) with hwdef
  have hw : ∀ i, w t i = ∑ k, D k i • w (φ t) k := by
    intro i
    have e1 : w t i = realV (M'⁻¹ * (Z * Matrix.of (dPart Θ t i))) := by
      simp only [hwdef]
      change realV (M⁻¹ * _) = _
      rw [hMinv, Matrix.mul_assoc]
    rw [e1, mul_dPart hΘ hU hφ h ht i, Matrix.mul_sum]
    simp only [Matrix.mul_smul]
    change realL n (∑ k, _) = _

    rw [map_sum]
    simp only [map_smul]
    rfl
  have hG : (Matrix.of fun i j : Fin N => @inner ℝ _ _ (w t i) (w t j)) =
      D.transpose * (Matrix.of fun k l : Fin N => @inner ℝ _ _ (w (φ t) k) (w (φ t) l)) * D := by
    ext i j
    rw [Matrix.of_apply, hw i, hw j]
    simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.of_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have hdet : (fderiv ℝ φ t).det = D.det := by
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin N) ℝ).toBasis]
    congr 1
  have hJ : chartJac Θ t = Real.sqrt (Matrix.det (Matrix.of fun i j : Fin N => @inner ℝ _ _ (w t i) (w t j))) := rfl
  have hJ' : chartJac Θ (φ t) =
      Real.sqrt (Matrix.det (Matrix.of fun i j : Fin N => @inner ℝ _ _ (w (φ t) i) (w (φ t) j))) := rfl
  rw [hJ, hJ', hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdet,
    show D.det * Matrix.det (Matrix.of fun k l : Fin N => @inner ℝ _ _ (w (φ t) k) (w (φ t) l)) * D.det =
      (D.det * D.det) * Matrix.det (Matrix.of fun k l : Fin N => @inner ℝ _ _ (w (φ t) k) (w (φ t) l)) by ring,
    Real.sqrt_mul (mul_self_nonneg _), Real.sqrt_mul_self_eq_abs, mul_comm]

end JacInvSec

theorem jacInv (ε : Fin n → Bool) : JacInv ε := by
  intro U φ Z hU hφ h t ht
  refine chartJac_mul_det ((contDiff_thetaExp ε).differentiable (by simp)) (fun s => ?_) hU hφ h ht
  rw [of_thetaExp]
  exact (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp _)

end Formalism.MainNotions.S.Gauge
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SGaugeDensV

section

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace Formalism.MainNotions.S.Gauge

variable {n : ℕ}

theorem continuous_expC (ε : Fin n → Bool) : Continuous (expC ε) :=
  (continuous_expG ε).comp (obG ε).repr.symm.continuous

theorem expC_injOn (ε : Fin n → Bool) : ∃ ρ₀ > 0, Set.InjOn (expC ε) (Metric.ball 0 ρ₀) := by
  obtain ⟨ρ₀, hρ, hinj⟩ := injOn_thetaExp ε
  refine ⟨ρ₀, hρ, fun a ha b hb e => hinj ha hb ?_⟩
  have e2 := congrArg uMat e
  rw [uMat_expC, uMat_expC] at e2
  exact Matrix.of.injective e2

theorem lamM_apply (ε : Fin n → Bool) (s : ℝ) {B : Set (Formalism.REAL.UJ ε)} (hB : MeasurableSet B) :
    lamM ε s B = ∫⁻ t in expC ε ⁻¹' B ∩ Metric.ball 0 s, jd ε t := by
  have hm : MeasurableSet (expC ε ⁻¹' B) := (continuous_expC ε).measurable hB
  rw [lamM, Measure.map_apply (continuous_expC ε).measurable hB, withDensity_apply _ hm,
    Measure.restrict_restrict hm]

theorem locInvOf (ε : Fin n → Bool) : LocInvOf ε := by
  intro hT hJ
  obtain ⟨s₁, hs₁, hTs⟩ := hT
  obtain ⟨ρ₀, hρ₀, hinj⟩ := expC_injOn ε
  refine ⟨min s₁ ρ₀, lt_min hs₁ hρ₀, fun s hs hss z A hA hAs hzA => ?_⟩
  have hinjs : Set.InjOn (expC ε) (Metric.ball 0 s) :=
    hinj.mono (Metric.ball_subset_ball (hss.trans (min_le_right _ _)))
  obtain ⟨U, hU, φ, hφ, hΘ, hsub⟩ := hTs s hs (hss.trans (min_le_left _ _)) z
  have hexp : ∀ t ∈ U, expC ε (φ t) = z * expC ε t := by
    intro t ht
    apply uMat_inj
    show _ = uMat z * uMat (expC ε t)
    simp only [uMat_expC]
    exact hΘ t ht
  set T := expC ε ⁻¹' A ∩ Metric.ball 0 s with hTdef
  have hTU : ∀ t ∈ T, t ∈ U ∧ φ t ∈ Metric.ball (0 : EL ε) s := fun t ht =>
    hsub t ht.2 (hzA ⟨expC ε t, ht.1, rfl⟩)
  have himage : φ '' T = expC ε ⁻¹' ((fun g => z * g) '' A) ∩ Metric.ball 0 s := by
    ext t'
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨?_, (hTU t ht).2⟩
      show expC ε (φ t) ∈ (fun g => z * g) '' A
      rw [hexp t (hTU t ht).1]
      exact ⟨expC ε t, ht.1, rfl⟩
    · rintro ⟨⟨a, ha, hza⟩, ht'⟩
      obtain ⟨t, htb, rfl⟩ := hAs ha
      have htT : t ∈ T := ⟨ha, htb⟩
      refine ⟨t, htT, hinjs (hTU t htT).2 ht' ?_⟩
      rw [hexp t (hTU t htT).1]
      exact hza
  have hinjT : Set.InjOn φ T := by
    intro a ha b hb e
    apply hinjs ha.2 hb.2
    have e2 := congrArg (expC ε) e
    rw [hexp a (hTU a ha).1, hexp b (hTU b hb).1] at e2
    exact mul_left_cancel e2
  have hzAm : MeasurableSet ((fun g => z * g) '' A) := by
    have : (fun g => z * g) '' A = (fun g => z⁻¹ * g) ⁻¹' A := by
      ext g
      constructor
      · rintro ⟨a, ha, rfl⟩
        simpa using ha
      · intro hg
        exact ⟨z⁻¹ * g, hg, by simp⟩
    rw [this]
    exact (continuous_const_mul z⁻¹).measurable hA
  have hTm : MeasurableSet T := ((continuous_expC ε).measurable hA).inter measurableSet_ball
  rw [lamM_apply ε s hzAm, lamM_apply ε s hA, ← himage,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hTm
      (fun t ht => ((hφ.differentiableAt (hU.mem_nhds (hTU t ht).1)).hasFDerivAt).hasFDerivWithinAt) hinjT]
  refine setLIntegral_congr_fun hTm (fun t ht => ?_)
  simp only [jd]
  rw [← ENNReal.ofReal_mul (abs_nonneg _), mul_comm, hJ U φ (uMat z) hU hφ hΘ t (hTU t ht).1]

end Formalism.MainNotions.S.Gauge
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SGaugeDensPf

section

@[expose] public section

namespace Formalism.MainNotions.S.Gauge

theorem gauge_density_exists : ∀ (n : ℕ) (ε : Fin n → Bool), GaugeDens ε := fun _ ε =>
  gaugeDens_of_parts ε (chartNhd ε) (transC ε) (jacInv ε) (locInvOf ε) (ballFormOf ε) (densOfBall ε)

end Formalism.MainNotions.S.Gauge
end
end
