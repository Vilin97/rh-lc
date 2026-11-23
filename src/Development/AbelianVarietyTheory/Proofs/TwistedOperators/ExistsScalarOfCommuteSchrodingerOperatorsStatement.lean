module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import GroundTheory.GlobalFields.TateThesis.GaussianSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivedActionIntertwinesOfGroupStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzTranslate
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfOrthogonalSchrodingerGaussian

section

@[expose] public section

open GlobalTheory.RealWeil MeasureTheory
open scoped SchwartzMap

open scoped FourierTransform RealInnerProductSpace Real

namespace GlobalTheory.RealWeil

theorem eq_zero_of_inner_rhoSch_gaussian : ∀ (l : Type) [Fintype l] (k : Sch l),
    (∀ w : l ⊕ l → ℝ, inner ℂ ((rhoSch w (GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l))).toLp 2 volume)
      (k.toLp 2 volume) = 0) → k = 0 := by
  intro l _ k h
  set G := GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l) with hG
  let m : EuclideanSpace ℝ l → ℂ := fun x => G x * k x
  have hGn : ∀ x, ‖G x‖ ≤ 1 := fun x => by
    rw [hG, GroundTheory.Global.gaussianSchwartz_apply, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    have := Real.pi_pos
    nlinarith [sq_nonneg ‖x‖]
  have hm_cont : Continuous m := G.continuous.mul k.continuous
  have hm_int : Integrable m := k.integrable.norm.mono' hm_cont.aestronglyMeasurable
    (ae_of_all _ fun x => by
      simp only [m, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hGn x))
  have hF : 𝓕 m = 0 := by
    funext q
    have hq := h (Sum.elim 0 (fun i => q i))
    have hp : pPart (Sum.elim 0 (fun i => q i) : l ⊕ l → ℝ) = 0 := by
      ext i; simp [pPart]
    have hqq : qPart (Sum.elim 0 (fun i => q i) : l ⊕ l → ℝ) = q := by
      ext i; simp [qPart]
    rw [SchwartzMap.inner_toL2_toL2_eq _ _ volume] at hq
    rw [Real.fourier_eq', Pi.zero_apply, ← hq]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [m, coe_rhoSch, rhoFun, phase, hp, hqq, add_zero, inner_zero_left, mul_zero, RCLike.inner_apply,
      map_mul, smul_eq_mul]
    rw [← Complex.exp_conj]
    have hGc : (starRingEnd ℂ) (G x) = G x := by
      rw [hG, GroundTheory.Global.gaussianSchwartz_apply, Complex.conj_ofReal]
    rw [hGc]
    have : (starRingEnd ℂ) (((2 * π * ⟪q, x⟫ : ℝ) : ℂ) * Complex.I) =
        ((-2 * π * ⟪x, q⟫ : ℝ) : ℂ) * Complex.I := by
      rw [map_mul, Complex.conj_ofReal, Complex.conj_I, real_inner_comm]
      push_cast
      ring
    rw [this]
    ring
  have hm0 : m = 0 := by
    have hi : Integrable (𝓕 m) := by rw [hF]; exact integrable_zero _ _ _
    rw [← hm_cont.fourierInv_fourier_eq hm_int hi, hF]
    funext v
    simp [Real.fourierInv_eq]
  ext x
  have hx := congrFun hm0 x
  simp only [m, Pi.zero_apply, mul_eq_zero] at hx
  rcases hx with hx | hx
  · exfalso
    rw [hG, GroundTheory.Global.gaussianSchwartz_apply, Complex.ofReal_eq_zero] at hx
    exact (Real.exp_pos _).ne' hx
  · simpa using hx

end GlobalTheory.RealWeil
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfOrthogonalSchrodingerGaussianStatement

section

@[expose] public section

open GlobalTheory.RealWeil MeasureTheory
open scoped SchwartzMap

theorem _root_.GlobalTheory.T.eq_zero_of_orthogonal_schrodinger_gaussian : ∀ (l : Type) [Fintype l] (k : Sch l), (∀ w : l ⊕ l → ℝ, inner ℂ ((rhoSch w (GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l))).toLp 2 volume) (k.toLp 2 volume) = 0) → k = 0 := by
  first | exact @GlobalTheory.RealWeil.eq_zero_of_inner_rhoSch_gaussian | exact GlobalTheory.RealWeil.eq_zero_of_inner_rhoSch_gaussian | (intros; apply GlobalTheory.RealWeil.eq_zero_of_inner_rhoSch_gaussian <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzEqGaussianOfFderivAddEqZero

section

@[expose] public section

open scoped SchwartzMap

namespace GlobalTheory

theorem schwartz_eq_gaussian_of_fderiv_add_eq_zero
    (l : Type) [Fintype l] [DecidableEq l] (h : 𝓢(EuclideanSpace ℝ l, ℂ))
    (H : ∀ (j : l) (x : EuclideanSpace ℝ l),
      fderiv ℝ (⇑h) x (EuclideanSpace.single j 1) + 2 * Real.pi * (x j : ℂ) * h x = 0)
    (x : EuclideanSpace ℝ l) :
    h x = h 0 * ((Real.exp (-Real.pi * ‖x‖ ^ 2) : ℝ) : ℂ) := by
  have hE : ∀ y : EuclideanSpace ℝ l,
      HasFDerivAt (fun y : EuclideanSpace ℝ l => Real.exp (Real.pi * ‖y‖ ^ 2))
        (Real.exp (Real.pi * ‖y‖ ^ 2) • (Real.pi • (2 • innerSL ℝ y))) y := by
    intro y
    exact ((hasStrictFDerivAt_norm_sq y).hasFDerivAt.const_mul Real.pi).exp
  have hu : ∀ y : EuclideanSpace ℝ l,
      HasFDerivAt (fun y : EuclideanSpace ℝ l => Real.exp (Real.pi * ‖y‖ ^ 2) • h y)
        (0 : EuclideanSpace ℝ l →L[ℝ] ℂ) y := by
    intro y
    have h1 := (hE y).smul (h.differentiableAt (x := y)).hasFDerivAt
    refine h1.congr_fderiv ?_
    apply ContinuousLinearMap.coe_injective
    apply (EuclideanSpace.basisFun l ℝ).toBasis.ext
    intro j
    have h2 := H j y
    have h3 : fderiv ℝ (⇑h) y (EuclideanSpace.single j 1) = -(2 * Real.pi * (y j : ℂ) * h y) :=
      eq_neg_of_add_eq_zero_left h2
    simp [h3, EuclideanSpace.inner_single_right]
    ring
  have hc := is_const_of_fderiv_eq_zero (𝕜 := ℝ)
    (f := fun y : EuclideanSpace ℝ l => Real.exp (Real.pi * ‖y‖ ^ 2) • h y)
    (fun y => (hu y).differentiableAt) (fun y => (hu y).fderiv) x 0
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    Real.exp_zero, one_smul] at hc
  rw [← hc, Complex.real_smul, mul_right_comm, ← Complex.ofReal_mul, ← Real.exp_add]
  simp

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzEqGaussianOfFderivAddEqZeroStatement

section

@[expose] public section

open scoped SchwartzMap

theorem _root_.GlobalTheory.T.schwartz_eq_gaussian_of_fderiv_add_eq_zero' : ∀ (l : Type) [Fintype l] [DecidableEq l] (h : 𝓢(EuclideanSpace ℝ l, ℂ)), (∀ (j : l) (x : EuclideanSpace ℝ l), fderiv ℝ (⇑h) x (EuclideanSpace.single j 1) + 2 * Real.pi * (x j : ℂ) * h x = 0) → ∀ x, h x = h 0 * ((Real.exp (-Real.pi * ‖x‖ ^ 2) : ℝ) : ℂ) := by
  first | exact @GlobalTheory.schwartz_eq_gaussian_of_fderiv_add_eq_zero | exact GlobalTheory.schwartz_eq_gaussian_of_fderiv_add_eq_zero | (intros; apply GlobalTheory.schwartz_eq_gaussian_of_fderiv_add_eq_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsScalarOfCommuteSchrodingerOperators

section

@[expose] public section

noncomputable section

open MeasureTheory Complex
open scoped SchwartzMap Matrix Real RealInnerProductSpace

namespace GlobalTheory.RealWeil

theorem fderiv_gaussianSchwartz_single_add {l : Type} [Fintype l] [DecidableEq l] (j : l) (x : EuclideanSpace ℝ l) :
    fderiv ℝ (⇑(GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l))) x (EuclideanSpace.single j 1) +
      2 * Real.pi * (x j : ℂ) * GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l) x = 0 := by
  have h1 : HasFDerivAt (fun y : EuclideanSpace ℝ l => -Real.pi * ‖y‖ ^ 2)
      (-Real.pi • (2 • (innerSL ℝ) x ∘L ContinuousLinearMap.id ℝ _)) x :=
    ((hasFDerivAt_id x).norm_sq).const_mul (-Real.pi)
  have h2 := (ofRealCLM.hasFDerivAt (x := Real.exp (-Real.pi * ‖x‖ ^ 2))).comp x h1.exp
  have e : ⇑(GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l)) =
      (ofRealCLM : ℝ →L[ℝ] ℂ) ∘ fun y : EuclideanSpace ℝ l => Real.exp (-Real.pi * ‖y‖ ^ 2) := by
    funext y; simp
  rw [e, h2.fderiv]
  simp [EuclideanSpace.inner_single_right]
  ring

theorem inner_toLp_map_of_integral_norm_sq : ∀ (l : Type) [Fintype l] (S : Sch l →ₗ[ℂ] Sch l),
    (∀ f, ∫ x, ‖S f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) →
    ∀ f g, inner ℂ ((S f).toLp 2 volume) ((S g).toLp 2 volume) = inner ℂ (f.toLp 2 volume) (g.toLp 2 volume) := by
  intro l _ S hiso f g
  set U := SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (EuclideanSpace ℝ l)) with hU
  have hn : ∀ h : Sch l, ‖U (S h)‖ = ‖U h‖ := by
    intro h
    simp only [hU, SchwartzMap.toLpCLM_apply]
    rw [SchwartzMap.norm_toLp' (by norm_num) (by norm_num), SchwartzMap.norm_toLp' (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    rw [hiso]
  have e1 : (S f).toLp 2 volume = U (S f) := rfl
  have e2 : (S g).toLp 2 volume = U (S g) := rfl
  have e3 : f.toLp 2 volume = U f := rfl
  have e4 : g.toLp 2 volume = U g := rfl
  rw [e1, e2, e3, e4, inner_eq_sum_norm_sq_div_four, inner_eq_sum_norm_sq_div_four]
  simp only [← map_add (f := _), ← map_sub, ← map_smul, hn]

theorem exists_eq_smul_of_commute_rhoFun : ∀ (l : Type) [Fintype l] (S : Sch l →ₗ[ℂ] Sch l),
    (∀ f, ∫ x, ‖S f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) →
    (∀ w (f f₁ : Sch l), ⇑f₁ = rhoFun w ⇑f → ⇑(S f₁) = rhoFun w ⇑(S f)) → ∃ c : ℂ, ∀ f, S f = c • f := by
  intro l _ S hiso hcomm
  classical
  have hl : ∀ g : Sch l, ∫⁻ x, ‖g x‖ₑ ^ 2 = ENNReal.ofReal (∫ x, ‖g x‖ ^ 2) := by
    intro g
    rw [ofReal_integral_eq_lintegral_ofReal ((g.memLp (2 : ℕ) volume).integrable_norm_pow (by norm_num))
      (.of_forall fun x => by positivity)]
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  have hbound : ∀ f, ∫⁻ x, ‖S f x‖ₑ ^ 2 ≤ 1 * ∫⁻ x, ‖f x‖ₑ ^ 2 := by
    intro f
    rw [one_mul, hl, hl, hiso]
  have hd := GlobalTheory.T.derived_action_intertwines_of_group l LinearMap.id S 1 ENNReal.one_ne_top hbound (by simpa using hcomm)
  set G : Sch l := GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l) with hG
  have hN : ∀ (j : l) (h : Sch l) x, (dRho (Pi.single (Sum.inl j) 1) h - I • dRho (Pi.single (Sum.inr j) 1) h) x =
      fderiv ℝ (⇑h) x (EuclideanSpace.single j 1) + 2 * Real.pi * (x j : ℂ) * h x := by
    intro j h x
    rw [SchwartzMap.sub_apply, SchwartzMap.smul_apply, dRho_single_inl, dRho_single_inr,
      SchwartzMap.lineDerivOp_apply_eq_fderiv, smul_eq_mul]
    ring_nf
    rw [I_sq]
    ring
  have hSG : ∀ j (x : EuclideanSpace ℝ l), fderiv ℝ (⇑(S G)) x (EuclideanSpace.single j 1) +
      2 * Real.pi * (x j : ℂ) * S G x = 0 := by
    intro j x
    have h0 : dRho (Pi.single (Sum.inl j) 1) G - I • dRho (Pi.single (Sum.inr j) 1) G = 0 := by
      ext y
      rw [hN, hG, fderiv_gaussianSchwartz_single_add]
      rfl
    have := congrArg S h0
    rw [map_sub, map_smul, hd, hd, map_zero] at this
    rw [← hN, LinearMap.id_apply, LinearMap.id_apply] at *
    rw [this]
    rfl
  set c : ℂ := S G 0 with hc
  have hSGc : S G = c • G := by
    ext x
    rw [GlobalTheory.T.schwartz_eq_gaussian_of_fderiv_add_eq_zero' l (S G) hSG x, SchwartzMap.smul_apply, smul_eq_mul, hG, GroundTheory.Global.gaussianSchwartz_apply]
  have hrho : ∀ w, S (rhoSch w G) = c • rhoSch w G := by
    intro w
    ext x
    rw [hcomm w G (rhoSch w G) (coe_rhoSch w G), hSGc, SchwartzMap.smul_apply, coe_rhoSch]
    simp only [rhoFun, SchwartzMap.smul_apply, smul_eq_mul]
    ring
  have key : ∀ f : Sch l, (starRingEnd ℂ c) • S f = f := by
    intro f
    rw [← sub_eq_zero]
    apply GlobalTheory.T.eq_zero_of_orthogonal_schrodinger_gaussian l
    intro w
    have hsm : ∀ (a : ℂ) (g : Sch l), (a • g).toLp 2 volume = a • g.toLp 2 volume := fun a g =>
      (SchwartzMap.toLpCLM ℂ ℂ 2 volume).map_smul a g
    have hsub : ∀ (g g' : Sch l), (g - g').toLp 2 volume = g.toLp 2 volume - g'.toLp 2 volume := fun g g' =>
      (SchwartzMap.toLpCLM ℂ ℂ 2 volume).map_sub g g'
    have hp := inner_toLp_map_of_integral_norm_sq l S hiso (rhoSch w G) f
    rw [hrho, hsm, inner_smul_left] at hp
    rw [hsub, hsm, inner_sub_right, inner_smul_right, hp, sub_self]
  have hc0 : starRingEnd ℂ c ≠ 0 := by
    intro h0
    have := congrArg (fun g : Sch l => g 0) (key G)
    simp [h0, hG] at this
  exact ⟨(starRingEnd ℂ c)⁻¹, fun f => by rw [← key f, smul_smul, inv_mul_cancel₀ hc0, one_smul, key]⟩

end GlobalTheory.RealWeil
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsScalarOfCommuteSchrodingerOperatorsStatement

section

@[expose] public section

open GlobalTheory.RealWeil MeasureTheory
open scoped SchwartzMap Matrix

theorem _root_.GlobalTheory.T.exists_scalar_of_commute_schrodingerOperators : ∀ (l : Type) [Fintype l] (S : Sch l →ₗ[ℂ] Sch l), (∀ f, ∫ x, ‖S f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) → (∀ w (f f₁ : Sch l), ⇑f₁ = rhoFun w ⇑f → ⇑(S f₁) = rhoFun w ⇑(S f)) → ∃ c : ℂ, ∀ f, S f = c • f := by
  first | exact @GlobalTheory.RealWeil.exists_eq_smul_of_commute_rhoFun | exact GlobalTheory.RealWeil.exists_eq_smul_of_commute_rhoFun | (intros; apply GlobalTheory.RealWeil.exists_eq_smul_of_commute_rhoFun <;> assumption)
end
end
