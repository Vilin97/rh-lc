module

public import GroundTheory.AutomorphicForms.HarishChandraRegularity.ContDiffCompCoordEquiv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpHaar
public import GroundTheory.AutomorphicForms.HarishChandraRegularity.TupleOp
public import GroundTheory.AutomorphicForms.GKModules.Casimir
public import GroundTheory.AutomorphicForms.HarishChandraRegularity.CartanBasis
public import GroundTheory.AutomorphicForms.PartialDifferential.AnalyticHypoelliptic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.Separation.CompletelyRegular

-- Source module: GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpChart

section

@[expose] public section

namespace GroundTheory.Automorphic

open NormedSpace Set Filter Topology
open scoped ContDiff

set_option linter.unusedSectionVars false

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]

theorem analyticAt_expPartialHomeomorph_symm {y : 𝔸}
    (hy : y ∈ (expPartialHomeomorph ℝ 𝔸).target) :
    AnalyticAt ℝ (expPartialHomeomorph ℝ 𝔸).symm y := by
  set e := expPartialHomeomorph ℝ 𝔸 with he
  have hs : e.symm y ∈ e.source := e.map_target hy
  have hu : IsUnit (fderiv ℝ (exp : 𝔸 → 𝔸) (e.symm y)) :=
    expPartialHomeomorph_source_subset ℝ 𝔸 hs
  obtain ⟨p, hp⟩ := exp_analytic (𝕂 := ℝ) (e.symm y)
  have hp' : HasFPowerSeriesAt e p (e.symm y) := by
    rw [he, coe_expPartialHomeomorph]; exact hp
  have h1 : p 1 = (continuousMultilinearCurryFin1 ℝ 𝔸 𝔸).symm
      ((ContinuousLinearEquiv.unitsEquiv ℝ 𝔸 hu.unit : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸) := by
    have h2 := hp.fderiv_eq
    have h3 : ((ContinuousLinearEquiv.unitsEquiv ℝ 𝔸 hu.unit : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸) =
        fderiv ℝ (exp : 𝔸 → 𝔸) (e.symm y) := by
      ext x; simp
    rw [h3, h2, LinearIsometryEquiv.symm_apply_apply]
  have := e.hasFPowerSeriesAt_symm hs hp' h1
  rw [e.right_inv hy] at this
  exact this.analyticAt

variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

noncomputable def expChartProd {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (X : 𝔤)
    (p : EuclideanSpace ℝ (Fin d) × ℝ) : 𝔸 :=
  exp ((coordEquiv b p.1 : 𝔤) : 𝔸) * exp (p.2 • (X : 𝔸))

noncomputable def expChartFlow {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (X : 𝔤)
    (p : EuclideanSpace ℝ (Fin d) × ℝ) : EuclideanSpace ℝ (Fin d) :=
  (coordEquiv b).symm (subspaceProj 𝔤 ((expPartialHomeomorph ℝ 𝔸).symm (expChartProd b X p)))

noncomputable def expChartCoeff {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (X : 𝔤)
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  fderiv ℝ (expChartFlow b X) (x, 0) (0, 1)

theorem continuous_expChartProd {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (X : 𝔤) :
    Continuous (expChartProd b X) := by
  unfold expChartProd
  refine Continuous.mul ?_ ?_
  · exact (contDiff_exp ℝ 𝔸 (n := 0)).continuous.comp
      (continuous_subtype_val.comp ((coordEquiv b).continuous.comp continuous_fst))
  · exact (contDiff_exp ℝ 𝔸 (n := 0)).continuous.comp (continuous_snd.smul continuous_const)

theorem analyticAt_expChartProd {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (X : 𝔤)
    (p : EuclideanSpace ℝ (Fin d) × ℝ) : AnalyticAt ℝ (expChartProd b X) p := by
  have h1 : AnalyticAt ℝ (fun q : EuclideanSpace ℝ (Fin d) × ℝ => ((coordEquiv b q.1 : 𝔤) : 𝔸)) p :=
    (𝔤.subtypeL.comp ((coordEquiv b : EuclideanSpace ℝ (Fin d) →L[ℝ] 𝔤).comp
      (ContinuousLinearMap.fst ℝ _ ℝ))).analyticAt p
  have h2 : AnalyticAt ℝ (fun q : EuclideanSpace ℝ (Fin d) × ℝ => q.2 • (X : 𝔸)) p :=
    ((ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin d)) ℝ).smulRight (X : 𝔸)).analyticAt p
  have h1' := (exp_analytic (𝕂 := ℝ) _).comp h1
  have h2' := (exp_analytic (𝕂 := ℝ) _).comp h2
  exact h1'.mul h2'

theorem analyticAt_expChartFlow {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (X : 𝔤)
    {p : EuclideanSpace ℝ (Fin d) × ℝ}
    (hp : expChartProd b X p ∈ (expPartialHomeomorph ℝ 𝔸).target) :
    AnalyticAt ℝ (expChartFlow b X) p := by
  have hL : AnalyticAt ℝ (fun w : 𝔸 => (coordEquiv b).symm (subspaceProj 𝔤 w))
      ((expPartialHomeomorph ℝ 𝔸).symm (expChartProd b X p)) :=
    (((coordEquiv b).symm : 𝔤 →L[ℝ] EuclideanSpace ℝ (Fin d)).comp (subspaceProj 𝔤)).analyticAt _
  have h2 : AnalyticAt ℝ ((expPartialHomeomorph ℝ 𝔸).symm ∘ expChartProd b X) p :=
    (analyticAt_expPartialHomeomorph_symm hp).comp (analyticAt_expChartProd b X p)
  exact AnalyticAt.comp (f := (expPartialHomeomorph ℝ 𝔸).symm ∘ expChartProd b X)
    (g := fun w : 𝔸 => (coordEquiv b).symm (subspaceProj 𝔤 w)) hL h2

theorem analyticOnNhd_expChartFlow {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (X : 𝔤) :
    AnalyticOnNhd ℝ (expChartFlow b X) (expChartProd b X ⁻¹' (expPartialHomeomorph ℝ 𝔸).target) :=
  fun _ hp => analyticAt_expChartFlow b X hp

namespace IsExpLieAlgebra

variable (h : IsExpLieAlgebra G 𝔤)

theorem exists_ball_coordEquiv_mem_nhd {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    ∃ r > 0, ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r,
      ((coordEquiv b x : 𝔤) : 𝔸) ∈ h.nhd := by
  have hc : Continuous (fun x : EuclideanSpace ℝ (Fin d) => ((coordEquiv b x : 𝔤) : 𝔸)) :=
    continuous_subtype_val.comp (coordEquiv b).continuous
  have h0 : h.nhd ∈ 𝓝 ((fun x : EuclideanSpace ℝ (Fin d) => ((coordEquiv b x : 𝔤) : 𝔸)) 0) := by
    simp only [map_zero, ZeroMemClass.coe_zero]
    exact h.isOpen_nhd.mem_nhds h.zero_mem_nhd
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (hc.continuousAt.preimage_mem_nhds h0)
  exact ⟨r, hr, fun x hx => hball hx⟩

theorem val_expG_mul_expG {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (X : 𝔤)
    (p : EuclideanSpace ℝ (Fin d) × ℝ) :
    (((h.expG (coordEquiv b p.1) * h.expG (p.2 • X) : G) : 𝔸ˣ) : 𝔸) = expChartProd b X p := by
  simp [expChartProd]

theorem expG_expChartFlow {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (X : 𝔤)
    {p : EuclideanSpace ℝ (Fin d) × ℝ} (hp : expChartProd b X p ∈ h.nhdOne) :
    h.expG (coordEquiv b (expChartFlow b X p)) = h.expG (coordEquiv b p.1) * h.expG (p.2 • X) := by
  set w : G := h.expG (coordEquiv b p.1) * h.expG (p.2 • X) with hw
  have hwv : ((w : 𝔸ˣ) : 𝔸) = expChartProd b X p := h.val_expG_mul_expG b X p
  have hwN : ((w : 𝔸ˣ) : 𝔸) ∈ h.nhdOne := hwv ▸ hp
  have hmem := h.symm_mem_lie hwN
  have e1 : coordEquiv b (expChartFlow b X p) =
      subspaceProj 𝔤 ((expPartialHomeomorph ℝ 𝔸).symm ((w : 𝔸ˣ) : 𝔸)) := by
    rw [hwv]; exact (coordEquiv b).apply_symm_apply _
  apply Subtype.ext; apply Units.ext
  rw [coe_expG, e1, subspaceProj_of_mem hmem, h.exp_symm hwN]

theorem expChartFlow_zero {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (X : 𝔤)
    {x : EuclideanSpace ℝ (Fin d)} (hx : ((coordEquiv b x : 𝔤) : 𝔸) ∈ h.nhd) :
    expChartFlow b X (x, 0) = x := by
  simp only [expChartFlow, expChartProd, zero_smul, exp_zero, mul_one]
  rw [h.symm_exp hx, subspaceProj_coe, ContinuousLinearEquiv.symm_apply_apply]

theorem expChartProd_zero_mem_nhdOne {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (X : 𝔤)
    {x : EuclideanSpace ℝ (Fin d)} (hx : ((coordEquiv b x : 𝔤) : 𝔸) ∈ h.nhd) :
    expChartProd b X (x, 0) ∈ h.nhdOne := by
  simp only [expChartProd, zero_smul, exp_zero, mul_one]
  exact h.exp_mem_nhdOne hx

theorem hasDerivAt_expChartFlow {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (X : 𝔤)
    {x : EuclideanSpace ℝ (Fin d)} (hx : ((coordEquiv b x : 𝔤) : 𝔸) ∈ h.nhd) :
    HasDerivAt (fun t : ℝ => expChartFlow b X (x, t)) (expChartCoeff b X x) 0 := by
  have hA : AnalyticAt ℝ (expChartFlow b X) (x, 0) :=
    analyticAt_expChartFlow b X (h.nhdOne_subset_target (h.expChartProd_zero_mem_nhdOne b X hx))
  have hl : HasDerivAt (fun t : ℝ => (x, t)) ((0 : EuclideanSpace ℝ (Fin d)), (1 : ℝ)) 0 :=
    (hasDerivAt_const (0 : ℝ) x).prodMk (hasDerivAt_id 0)
  exact hA.differentiableAt.hasFDerivAt.comp_hasDerivAt (x := (0 : ℝ)) hl

theorem exists_expChart_coeff {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    ∃ r > 0, ∃ c : 𝔤 → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
      (∀ X, AnalyticOnNhd ℝ (c X) (Metric.ball 0 r)) ∧
      (∀ X, c X 0 = (coordEquiv b).symm X) ∧
      ∀ (X : 𝔤) (f : G → ℂ), h.IsSmoothFun f → ∀ (g : G),
        ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r,
          h.rightDeriv X f (g * h.expG (coordEquiv b x)) =
            fderiv ℝ (fun y => f (g * h.expG (coordEquiv b y))) x (c X x) := by
  obtain ⟨r, hr, hball⟩ := h.exists_ball_coordEquiv_mem_nhd b
  refine ⟨r, hr, expChartCoeff b, ?_, ?_, ?_⟩
  ·
    intro X x hx
    have hS : (x, (0 : ℝ)) ∈ expChartProd b X ⁻¹' (expPartialHomeomorph ℝ 𝔸).target :=
      h.nhdOne_subset_target (h.expChartProd_zero_mem_nhdOne b X (hball x hx))
    have hD := (analyticOnNhd_expChartFlow b X).fderiv (𝕜 := ℝ) _ hS
    have hinl : AnalyticAt ℝ (fun y : EuclideanSpace ℝ (Fin d) => (y, (0 : ℝ))) x :=
      (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin d)) ℝ).analyticAt x
    have hD' : AnalyticAt ℝ (fun y : EuclideanSpace ℝ (Fin d) =>
        fderiv ℝ (expChartFlow b X) (y, 0)) x :=
      AnalyticAt.comp (g := fderiv ℝ (expChartFlow b X))
        (f := fun y : EuclideanSpace ℝ (Fin d) => (y, (0 : ℝ))) hD hinl
    have hap := (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin d))
      ((0 : EuclideanSpace ℝ (Fin d)), (1 : ℝ))).analyticAt (fderiv ℝ (expChartFlow b X) (x, 0))
    exact AnalyticAt.comp (f := fun y : EuclideanSpace ℝ (Fin d) => fderiv ℝ (expChartFlow b X) (y, 0))
      hap hD'
  ·
    intro X
    have h0 : ((coordEquiv b (0 : EuclideanSpace ℝ (Fin d)) : 𝔤) : 𝔸) ∈ h.nhd := by
      simp only [map_zero, ZeroMemClass.coe_zero]; exact h.zero_mem_nhd
    have hd := h.hasDerivAt_expChartFlow b X h0
    have hev : (fun t : ℝ => expChartFlow b X (0, t)) =ᶠ[𝓝 0]
        fun t : ℝ => t • (coordEquiv b).symm X := by
      have hc : Continuous (fun t : ℝ => t • (X : 𝔸)) := continuous_id.smul continuous_const
      have : ∀ᶠ t in 𝓝 (0 : ℝ), t • (X : 𝔸) ∈ h.nhd := by
        have h1 := hc.continuousAt (x := 0)
        rw [ContinuousAt, zero_smul] at h1
        exact h1 (h.isOpen_nhd.mem_nhds h.zero_mem_nhd)
      filter_upwards [this] with t ht
      simp only [expChartFlow, expChartProd, map_zero, ZeroMemClass.coe_zero, exp_zero, one_mul]
      rw [h.symm_exp ht, show t • (X : 𝔸) = ((t • X : 𝔤) : 𝔸) from rfl, subspaceProj_coe, map_smul]
    have hd2 : HasDerivAt (fun t : ℝ => t • (coordEquiv b).symm X) ((coordEquiv b).symm X) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const ((coordEquiv b).symm X)
    exact hd.unique (hd2.congr_of_eventuallyEq hev)
  ·
    intro X f hf g x hx
    have hxN := hball x hx
    set u : EuclideanSpace ℝ (Fin d) → ℂ := fun y => f (g * h.expG (coordEquiv b y)) with hu
    have hud : Differentiable ℝ u := (h.contDiff_comp_coordEquiv hf g b).differentiable (by simp)
    have hφ := h.hasDerivAt_expChartFlow b X hxN
    have h1 : HasDerivAt (fun t : ℝ => u (expChartFlow b X (x, t)))
        (fderiv ℝ u x (expChartCoeff b X x)) 0 := by
      have := (hud (expChartFlow b X (x, 0))).hasFDerivAt.comp_hasDerivAt (x := (0 : ℝ)) hφ
      rw [h.expChartFlow_zero b X hxN] at this
      exact this
    have h2 := h.hasDerivAt_rightDeriv hf X (g * h.expG (coordEquiv b x))
    have hev : (fun t : ℝ => f (g * h.expG (coordEquiv b x) * h.expG (t • X))) =ᶠ[𝓝 0]
        fun t : ℝ => u (expChartFlow b X (x, t)) := by
      have hc : Continuous (fun t : ℝ => expChartProd b X (x, t)) :=
        (continuous_expChartProd b X).comp (continuous_const.prodMk continuous_id)
      have : ∀ᶠ t in 𝓝 (0 : ℝ), expChartProd b X (x, t) ∈ h.nhdOne :=
        hc.continuousAt.preimage_mem_nhds
          (h.isOpen_nhdOne.mem_nhds (h.expChartProd_zero_mem_nhdOne b X hxN))
      filter_upwards [this] with t ht
      simp only [hu]
      rw [h.expG_expChartFlow b X ht, mul_assoc]
    exact h2.unique (h1.congr_of_eventuallyEq hev)

end IsExpLieAlgebra

end GroundTheory.Automorphic
end
end

-- Source module: GroundTheory.AutomorphicForms.HarishChandraRegularity

section

@[expose] public section

namespace GroundTheory.Automorphic

open Sobolev Set Filter Topology MeasureTheory
open scoped ContDiff Manifold

set_option linter.unusedSectionVars false

namespace Sobolev

variable {n : ℕ}

def sqSymbol {ι : Type*} [Fintype ι] (c : ι → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x ξ : EuclideanSpace ℝ (Fin n)) : ℂ :=
  ∑ i, (∑ j, ((c i x j : ℝ) : ℂ) * ((ξ j : ℝ) : ℂ)) ^ 2

theorem sqSymbol_eq {ι : Type*} [Fintype ι] (c : ι → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x ξ : EuclideanSpace ℝ (Fin n)) :
    sqSymbol c x ξ = ((∑ i, (inner ℝ (c i x) ξ) ^ 2 : ℝ) : ℂ) := by
  simp only [sqSymbol, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem exists_ball_sqSymbol_ne_zero {ι : Type*} [Fintype ι]
    {c : ι → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} (hc : ∀ i, ContinuousAt (c i) 0)
    (hspan : ∀ ξ : EuclideanSpace ℝ (Fin n), (∀ i, inner ℝ (c i 0) ξ = 0) → ξ = 0) :
    ∃ δ > 0, ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ, ∀ ξ, ξ ≠ 0 → sqSymbol c x ξ ≠ 0 := by
  classical
  let Q : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) := fun x => ∑ i, (innerSL ℝ (c i x)).smulRight (c i x)
  have hQ : ∀ x ξ, Q x ξ = ∑ i, inner ℝ (c i x) ξ • c i x := by
    intro x ξ; simp [Q]
  have hquad : ∀ x ξ, inner ℝ (Q x ξ) ξ = ∑ i, (inner ℝ (c i x) ξ) ^ 2 := by
    intro x ξ
    rw [hQ, sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_smul_left, sq]
  have hzero : ∀ x ξ, ∑ i, (inner ℝ (c i x) ξ) ^ 2 = 0 → Q x ξ = 0 := by
    intro x ξ h0
    have hall := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (inner ℝ (c i x) ξ)).1 h0
    rw [hQ]
    exact Finset.sum_eq_zero fun i hi => by
      rw [pow_eq_zero_iff two_ne_zero |>.1 (hall i hi), zero_smul]
  have hinj : Function.Injective (Q 0) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro ξ hξ
    apply hspan
    have h0 : ∑ i, (inner ℝ (c i 0) ξ) ^ 2 = 0 := by rw [← hquad, hξ, inner_zero_left]
    intro i
    exact pow_eq_zero_iff two_ne_zero |>.1
      ((Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (inner ℝ (c i 0) ξ)).1 h0 i
        (Finset.mem_univ _))
  have hsurj : Function.Surjective (Q 0) :=
    LinearMap.injective_iff_surjective (f := ((Q 0 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
      EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))).1 hinj
  let e := ContinuousLinearEquiv.ofBijective (Q 0) (LinearMap.ker_eq_bot.2 hinj)
    (LinearMap.range_eq_top.2 hsurj)
  have hU : IsUnit (Q 0) :=
    ⟨(ContinuousLinearEquiv.unitsEquiv ℝ (EuclideanSpace ℝ (Fin n))).symm e, ContinuousLinearMap.ext fun _ => rfl⟩
  have hQc : ContinuousAt Q 0 := by
    rw [continuousAt_clm_apply]
    intro ξ
    simp only [hQ]
    exact tendsto_finsetSum _ fun i _ =>
      (Filter.Tendsto.inner (hc i) tendsto_const_nhds).smul (hc i)
  set_option synthInstance.maxHeartbeats 200000 in
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 (hQc.preimage_mem_nhds (Units.isOpen.mem_nhds hU))
  refine ⟨δ, hδ, fun x hx ξ hξ hs => hξ ?_⟩
  obtain ⟨u, hu⟩ := hball hx
  rw [sqSymbol_eq, Complex.ofReal_eq_zero] at hs
  have h1 := hzero x ξ hs
  rw [← hu] at h1
  have h2 := congrArg (fun v => ((↑u⁻¹ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) v) h1
  have h3 : ((↑u⁻¹ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) *
      (↑u : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) ξ = 0 := by
    change (↑u⁻¹ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
      ((↑u : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ξ) = 0
    rw [h1, map_zero]
  rw [Units.inv_mul] at h3
  simpa using h3

theorem integral_euclideanSpace_of_eq_zero {d : ℕ} (hd : d = 0) (F : EuclideanSpace ℝ (Fin d) → ℂ) :
    ∫ x, F x = F 0 := by
  subst hd
  rw [volume_euclideanSpace_eq_dirac, integral_dirac]

end Sobolev

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

namespace IsExpLieAlgebra

variable (h : IsExpLieAlgebra G 𝔤)

def lieEquiv : h.lieSubalgebra ≃ₗ[ℝ] 𝔤 where
  toFun := h.ofLie
  invFun := h.toLie
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem lieEquiv_apply (X : h.lieSubalgebra) : h.lieEquiv X = h.ofLie X := rfl

theorem span_coord_of_basis {ι : Type*} [Fintype ι] (bL : Module.Basis ι ℝ h.lieSubalgebra) {d : ℕ}
    (b : Module.Basis (Fin d) ℝ 𝔤) (ξ : EuclideanSpace ℝ (Fin d))
    (hξ : ∀ i, inner ℝ ((coordEquiv b).symm (h.ofLie (bL i))) ξ = 0) : ξ = 0 := by
  have hall : ∀ v : h.lieSubalgebra, inner ℝ ((coordEquiv b).symm (h.lieEquiv v)) ξ = 0 := by
    intro v

    rw [← bL.sum_repr v, map_sum, map_sum, sum_inner]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_smul, map_smul, real_inner_smul_left, lieEquiv_apply, hξ i, mul_zero]
  have := hall (h.lieEquiv.symm (coordEquiv b ξ))
  rw [LinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply] at this
  exact inner_self_eq_zero.1 this

theorem laplacian_apply_coe {ι : Type*} [Fintype ι] (bL : Module.Basis ι ℝ h.lieSubalgebra)
    (w : h.smoothFuns (F := ℂ)) :
    ((h.laplacian bL w : h.smoothFuns (F := ℂ)) : G → ℂ) =
      ∑ i, h.rightDeriv (h.ofLie (bL i)) (h.rightDeriv (h.ofLie (bL i)) (w : G → ℂ)) := by
  simp [laplacian, LinearMap.sum_apply, Module.End.mul_apply]

theorem exists_tupleOp_laplacian_pow {ι : Type*} [Fintype ι] (bL : Module.Basis ι ℝ h.lieSubalgebra)
    {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    (c : ι → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hc : ∀ i, AnalyticOnNhd ℝ (c i) Ω)
    (hR : ∀ i (F : G → ℂ), h.IsSmoothFun F → ∀ g : G, ∀ x ∈ Ω,
      h.rightDeriv (h.ofLie (bL i)) F (g * h.expG (coordEquiv b x)) =
        vfOp (c i) (fun y => F (g * h.expG (coordEquiv b y))) x)
    (k : ℕ) : ∃ a : (k : ℕ) → (Fin k → Fin d) → EuclideanSpace ℝ (Fin d) → ℂ,
      (∀ k' J, AnalyticOnNhd ℝ (a k' J) Ω) ∧
      (∀ x ∈ Ω, ∀ ξ, tupleSymbol (2 * k) a x ξ = sqSymbol c x ξ ^ k) ∧
      ∀ (F : h.smoothFuns (F := ℂ)) (g : G), ∀ x ∈ Ω,
        ((((h.laplacian bL) ^ k) F : h.smoothFuns (F := ℂ)) : G → ℂ) (g * h.expG (coordEquiv b x)) =
          tupleOp (2 * k) a (fun y => (F : G → ℂ) (g * h.expG (coordEquiv b y))) x := by
  induction k with
  | zero =>
    refine ⟨idCoeff, fun k J => analyticOnNhd_idCoeff k J Ω,
      fun x _ ξ => by simpa using tupleSymbol_idCoeff x ξ, fun F g x _ => ?_⟩
    simp [tupleOp_idCoeff]
  | succ k ih =>
    obtain ⟨a, ha, hs, hop⟩ := ih
    have s1 := fun i => exists_vfOp_tupleOp (hc i) (m := 2 * k) ha
    choose a1 ha1 hs1 hop1 using s1
    have s2 := fun i => exists_vfOp_tupleOp (hc i) (m := 2 * k + 1) (ha1 i)
    choose a2 ha2 hs2 hop2 using s2
    have e2 : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
    refine ⟨∑ i, a2 i, fun k' J => ?_, fun x hx ξ => ?_, fun F g x hx => ?_⟩
    · have : (∑ i, a2 i) k' J = ∑ i, a2 i k' J := by ext y; simp [Finset.sum_apply]
      rw [this]; exact Finset.analyticOnNhd_sum _ fun i _ => ha2 i k' J
    · rw [e2, tupleSymbol_sum]
      simp only [hs2 _ x, hs1 _ x, hs x hx]
      rw [pow_succ', sqSymbol, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    · set u := fun y => (F : G → ℂ) (g * h.expG (coordEquiv b y)) with hu_def
      have hu : ContDiff ℝ ∞ u := h.contDiff_comp_coordEquiv F.2 g b
      rw [pow_succ', Module.End.mul_apply, laplacian_apply_coe, Finset.sum_apply, e2, tupleOp_sum]
      set w := ((h.laplacian bL) ^ k) F
      have hw : h.IsSmoothFun (w : G → ℂ) := w.2
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hR i _ (h.isSmoothFun_rightDeriv hw _) g x hx]
      have E1 : EqOn (fun y => h.rightDeriv (h.ofLie (bL i)) (w : G → ℂ) (g * h.expG (coordEquiv b y)))
          (vfOp (c i) (fun y => (w : G → ℂ) (g * h.expG (coordEquiv b y)))) Ω :=
        fun y hy => hR i _ hw g y hy
      have E2 : EqOn (fun y => (w : G → ℂ) (g * h.expG (coordEquiv b y))) (tupleOp (2 * k) a u) Ω :=
        fun y hy => hop F g y hy
      have E3 : EqOn (vfOp (c i) (fun y => (w : G → ℂ) (g * h.expG (coordEquiv b y))))
          (tupleOp (2 * k + 1) (a1 i) u) Ω :=
        fun y hy => (vfOp_congr_of_eqOn hΩ E2 (c i) hy).trans (hop1 i u hu y hy)
      rw [vfOp_congr_of_eqOn hΩ (E1.trans E3) (c i) hx, hop2 i u hu x hx]

theorem exists_tupleOp_aeval_laplacian {ι : Type*} [Fintype ι] (bL : Module.Basis ι ℝ h.lieSubalgebra)
    {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    (c : ι → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hc : ∀ i, AnalyticOnNhd ℝ (c i) Ω)
    (hR : ∀ i (F : G → ℂ), h.IsSmoothFun F → ∀ g : G, ∀ x ∈ Ω,
      h.rightDeriv (h.ofLie (bL i)) F (g * h.expG (coordEquiv b x)) =
        vfOp (c i) (fun y => F (g * h.expG (coordEquiv b y))) x)
    (P : Polynomial ℂ) (hP : P.Monic) :
    ∃ a : (k : ℕ) → (Fin k → Fin d) → EuclideanSpace ℝ (Fin d) → ℂ,
      (∀ k J, AnalyticOnNhd ℝ (a k J) Ω) ∧
      (∀ x ∈ Ω, ∀ ξ, tupleSymbol (2 * P.natDegree) a x ξ = sqSymbol c x ξ ^ P.natDegree) ∧
      ∀ (F : h.smoothFuns (F := ℂ)) (g : G), ∀ x ∈ Ω,
        ((Polynomial.aeval (h.laplacian bL) P F : h.smoothFuns (F := ℂ)) : G → ℂ)
            (g * h.expG (coordEquiv b x)) =
          tupleOp (2 * P.natDegree) a (fun y => (F : G → ℂ) (g * h.expG (coordEquiv b y))) x := by
  classical
  set N := P.natDegree with hN
  have s := fun i => h.exists_tupleOp_laplacian_pow bL b hΩ c hc hR i
  choose a ha hs hop using s
  let a' : ℕ → (k : ℕ) → (Fin k → Fin d) → EuclideanSpace ℝ (Fin d) → ℂ :=
    fun i => P.coeff i • raiseCoeff (2 * i) (a i)
  refine ⟨∑ i ∈ Finset.range (N + 1), a' i, fun k J => ?_, fun x hx ξ => ?_, fun F g x hx => ?_⟩
  · exact analyticOnNhd_sum_coeff _
      (fun i _ => analyticOnNhd_smul_coeff _ (analyticOnNhd_raiseCoeff _ (ha i))) k J
  · rw [tupleSymbol_sum, Finset.sum_range_succ, Finset.sum_eq_zero, zero_add]
    · simp only [a']
      rw [tupleSymbol_smul, tupleSymbol_raiseCoeff, hs N x hx, show P.coeff N = 1 from hP.coeff_natDegree,
        one_mul]
    · intro i hi
      simp only [a']
      rw [tupleSymbol_smul, tupleSymbol_raiseCoeff_of_lt (by simp at hi; omega), mul_zero]
  · rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply,
      tupleOp_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [a']
    rw [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, hop i F g x hx,
      tupleOp_smul, tupleOp_raiseCoeff (by simp at hi; omega)]

theorem exists_elliptic_aeval_laplacian {ι : Type*} [Fintype ι] (bL : Module.Basis ι ℝ h.lieSubalgebra)
    {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (P : Polynomial ℂ) (hP : P.Monic) :
    ∃ δ > 0, ∃ (A : Finset (Fin d → ℕ)) (a : (Fin d → ℕ) → EuclideanSpace ℝ (Fin d) → ℂ),
      (∀ α ∈ A, mabs α ≤ 2 * P.natDegree) ∧
      (∀ α ∈ A, AnalyticOn ℝ (a α) (Metric.ball 0 δ)) ∧
      (∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) δ, ∀ ξ, ξ ≠ 0 →
        prinSymbol A a (2 * P.natDegree) x ξ ≠ 0) ∧
      ∀ (F : h.smoothFuns (F := ℂ)) (g : G), ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) δ,
        diffOp A a (fun y => (F : G → ℂ) (g * h.expG (coordEquiv b y))) x =
          ((Polynomial.aeval (h.laplacian bL) P F : h.smoothFuns (F := ℂ)) : G → ℂ)
            (g * h.expG (coordEquiv b x)) := by
  obtain ⟨r, hr, cX, hcan, hc0, hchart⟩ := h.exists_expChart_coeff b
  set c : ι → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun i => cX (h.ofLie (bL i))
  have hcont : ∀ i, ContinuousAt (c i) 0 := fun i =>
    (hcan _ 0 (Metric.mem_ball_self hr)).continuousAt
  have hspan : ∀ ξ : EuclideanSpace ℝ (Fin d), (∀ i, inner ℝ (c i 0) ξ = 0) → ξ = 0 := by
    intro ξ hξ
    exact h.span_coord_of_basis bL b ξ fun i => by rw [← hc0]; exact hξ i
  obtain ⟨δ₀, hδ₀, hell⟩ := exists_ball_sqSymbol_ne_zero hcont hspan
  set δ := min r δ₀
  have hδ : 0 < δ := lt_min hr hδ₀
  have hΩr : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) δ ⊆ Metric.ball 0 r :=
    Metric.ball_subset_ball (min_le_left _ _)
  have hΩδ : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) δ ⊆ Metric.ball 0 δ₀ :=
    Metric.ball_subset_ball (min_le_right _ _)
  have hR : ∀ i (F : G → ℂ), h.IsSmoothFun F → ∀ g : G, ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) δ,
      h.rightDeriv (h.ofLie (bL i)) F (g * h.expG (coordEquiv b x)) =
        vfOp (c i) (fun y => F (g * h.expG (coordEquiv b y))) x := fun i F hF g x hx =>
    hchart _ F hF g x (hΩr hx)
  obtain ⟨a, ha, hs, hop⟩ := h.exists_tupleOp_aeval_laplacian bL b Metric.isOpen_ball c
    (fun i => (hcan _).mono hΩr) hR P hP
  obtain ⟨A, a', hA, ha', hsym, hconv⟩ := exists_diffOp_eq_tupleOp _ a ha
  refine ⟨δ, hδ, A, a', hA, fun α hα => (ha' α hα).analyticOn, fun x hx ξ hξ => ?_,
    fun F g x hx => ?_⟩
  · rw [hsym x ξ, hs x hx]
    exact pow_ne_zero _ (hell x (hΩδ hx) ξ hξ)
  · rw [hconv _ (h.contDiff_comp_coordEquiv F.2 g b), hop F g x hx]

theorem analyticAt_of_aeval_laplacian_eq_zero {ι : Type*} [Fintype ι]
    (bL : Module.Basis ι ℝ h.lieSubalgebra) (P : Polynomial ℂ) (hP : P.Monic)
    (f : h.smoothFuns (F := ℂ)) (hf : Polynomial.aeval (h.laplacian bL) P f = 0) (g : G) :
    AnalyticAt ℝ (fun Y : 𝔤 => (f : G → ℂ) (g * h.expG Y)) 0 := by
  set b := Module.finBasis ℝ 𝔤
  obtain ⟨δ, hδ, A, a, hA, ha, hell, hop⟩ := h.exists_elliptic_aeval_laplacian bL b P hP
  set u := fun y => (f : G → ℂ) (g * h.expG (coordEquiv b y))
  have hu : ContDiff ℝ ∞ u := h.contDiff_comp_coordEquiv f.2 g b
  have han : AnalyticOn ℝ u (Metric.ball 0 δ) :=
    analyticOn_of_elliptic Metric.isOpen_ball hA ha hell hu.contDiffOn fun x hx => by
      rw [hop f g x hx, hf]; rfl
  have hu0 : AnalyticAt ℝ u 0 :=
    (Metric.isOpen_ball.analyticOn_iff_analyticOnNhd.1 han) 0 (Metric.mem_ball_self hδ)
  have e : (fun Y : 𝔤 => (f : G → ℂ) (g * h.expG Y)) = u ∘ (coordEquiv b).symm := by
    funext Y; simp [u]
  rw [e]
  refine AnalyticAt.comp (by simpa using hu0) ?_
  exact (coordEquiv b).symm.toContinuousLinearMap.analyticAt _

end IsExpLieAlgebra

section Groups

open Matrix
open scoped Matrix.Norms.L2Operator

namespace IsExpLieAlgebra

end IsExpLieAlgebra

end Groups

end GroundTheory.Automorphic
end
end
