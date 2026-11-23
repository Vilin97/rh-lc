module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ContDiffAtFrameEntry
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsHolomorphicNormalFrameStatement
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.TripleDeriv
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Order
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.Linter.Style
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
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.InFlagDomainOne
import Mathlib.Analysis.SpecialFunctions.Bernstein

-- Source module: Development.WeilBound.CoreStatements.PluriharmonicCharts.ProjectiveLineNormalFrame

section

@[expose] public section

open Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

namespace PositivityTheory.Xgp.ProjectiveLineNormal

theorem holo_part {E M : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup M] [Module ℂ M]
    (H : E →ₗ[ℝ] M) : ∃ L : E →ₗ[ℂ] M, ∀ v, L v = (1 / 2 : ℂ) • (H v - Complex.I • H (Complex.I • v)) := by
  refine ⟨⟨⟨fun v => (1 / 2 : ℂ) • (H v - Complex.I • H (Complex.I • v)), ?_⟩, ?_⟩, fun v => rfl⟩
  · intro v w
    simp only [smul_add, map_add (f := _)]
    module
  · intro c v
    have e1 : c • v = c.re • v + c.im • (Complex.I • v) := by
      rw [← Complex.coe_smul, ← Complex.coe_smul, smul_smul, ← add_smul, Complex.re_add_im]
    have e2 : Complex.I • c • v = c.re • (Complex.I • v) - c.im • v := by
      rw [← Complex.coe_smul, ← Complex.coe_smul, smul_smul, smul_smul, ← sub_smul]
      congr 1
      apply Complex.ext <;> simp
    simp only [RingHom.id_apply]
    rw [e2, e1, map_add (f := _), map_sub, H.map_smul, H.map_smul, H.map_smul, H.map_smul]
    generalize H v = A
    generalize H (Complex.I • v) = B
    simp only [← Complex.coe_smul]
    match_scalars
    · apply Complex.ext <;> simp [mul_comm]
    · apply Complex.ext <;> simp [mul_comm]

end PositivityTheory.Xgp.ProjectiveLineNormal

theorem PositivityTheory.Xgp.projective_line_normal_frame : ∀ (d : ℕ) (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (y₀ : Fin d → ℂ), (G y₀).PosDef → (∀ y, (G y).IsHermitian) → (∀ p q, ContDiffAt ℝ 2 (fun y => G y p q) y₀) → ∃ g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ, (∀ p q, Differentiable ℂ fun y => g y p q) ∧ IsUnit (g y₀).det ∧ (g y₀)ᴴ * G y₀ * g y₀ = 1 ∧ ∀ p q, fderiv ℝ (fun y => ((g y)ᴴ * G y * g y) p q) y₀ = 0 := by
  intro d G y₀ hpos hherm hC
  have hG : ∀ p q, DifferentiableAt ℝ (fun y => G y p q) y₀ := fun p q =>
    (hC p q).differentiableAt (by norm_num)
  obtain ⟨g0, hg0u, hg0⟩ : ∃ g0 : Matrix (Fin 2) (Fin 2) ℂ, IsUnit g0.det ∧ g0ᴴ * G y₀ * g0 = 1 := by
    open scoped MatrixOrder in
    obtain ⟨y, hy⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hpos.posSemidef.nonneg
    have hdet := hpos.det_pos.ne'
    have hyu : IsUnit y.det := by
      rw [hy, det_mul] at hdet
      exact isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul hdet)
    refine ⟨y⁻¹, isUnit_nonsing_inv_det y hyu, ?_⟩
    rw [hy, star_eq_conjTranspose, ← Matrix.mul_assoc, ← conjTranspose_mul, Matrix.mul_assoc,
      mul_nonsing_inv y hyu]
    simp
  let Dm : (Fin d → ℂ) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
    { toFun := fun v => Matrix.of fun p q => fderiv ℝ (fun y => G y p q) y₀ v
      map_add' := fun v w => by ext p q; simp
      map_smul' := fun c v => by ext p q; simp }
  have hDm : ∀ v, (Dm v)ᴴ = Dm v := by
    intro v
    ext p q
    have h1 := (PositivityTheory.Xgp.gram_grad.line_deriv _ y₀ (hG q p) v).star
    have h2 := PositivityTheory.Xgp.gram_grad.line_deriv _ y₀ (hG p q) v
    have e : (fun s : ℝ => star (G (y₀ + s • v) q p)) = fun s : ℝ => G (y₀ + s • v) p q := by
      funext s
      exact (hherm _).apply p q
    rw [e] at h1
    exact h1.unique h2
  let H : (Fin d → ℂ) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
    { toFun := fun v => g0ᴴ * Dm v * g0
      map_add' := fun v w => by rw [map_add (f := _), Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c v => by rw [map_smul, Matrix.mul_smul, Matrix.smul_mul]; rfl }
  have hH : ∀ v, (H v)ᴴ = H v := by
    intro v
    show (g0ᴴ * Dm v * g0)ᴴ = g0ᴴ * Dm v * g0
    rw [conjTranspose_mul, conjTranspose_mul, hDm, conjTranspose_conjTranspose, Matrix.mul_assoc]
  obtain ⟨L, hL⟩ := PositivityTheory.Xgp.ProjectiveLineNormal.holo_part H
  have hLL : ∀ v, (L v)ᴴ + L v = H v := by
    intro v
    rw [hL, conjTranspose_smul, conjTranspose_sub, conjTranspose_smul, hH, hH]
    simp only [Complex.star_def, Complex.conj_I, map_div₀, map_one, map_ofNat]
    module
  let Λ : Fin 2 → Fin 2 → (Fin d → ℂ) →L[ℂ] ℂ := fun p q => LinearMap.toContinuousLinearMap
    { toFun := fun v => (g0 * L v) p q
      map_add' := fun v w => by rw [map_add (f := _), Matrix.mul_add]; rfl
      map_smul' := fun c v => by rw [map_smul, Matrix.mul_smul]; rfl }
  refine ⟨fun y => g0 - g0 * L (y - y₀), fun p q => ?_, by simpa using hg0u, by simpa using hg0, fun p q => ?_⟩
  · show Differentiable ℂ fun y => g0 p q - Λ p q (y - y₀)
    fun_prop
  · by_cases hd : DifferentiableAt ℝ
        (fun y => ((g0 - g0 * L (y - y₀))ᴴ * G y * (g0 - g0 * L (y - y₀))) p q) y₀
    swap
    · exact fderiv_zero_of_not_differentiableAt hd
    ext1 v
    have hV : ∀ p q, HasDerivAt (fun s : ℝ => (g0 - g0 * L (y₀ + s • v - y₀)) p q) ((-(g0 * L v)) p q) 0 := by
      intro p q
      have e : (fun s : ℝ => (g0 - g0 * L (y₀ + s • v - y₀)) p q) =
          fun s : ℝ => g0 p q - s • (g0 * L v) p q := by
        funext s
        rw [add_sub_cancel_left, L.map_smul_of_tower, Matrix.mul_smul]
        rfl
      rw [e]
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const ((g0 * L v) p q)).const_sub (g0 p q)
    have h1 := PositivityTheory.Xgp.gram_grad.triple_deriv (fun s : ℝ => G (y₀ + s • v))
      (fun s : ℝ => g0 - g0 * L (y₀ + s • v - y₀)) (Dm v) (-(g0 * L v)) 0
      (fun p q => PositivityTheory.Xgp.gram_grad.line_deriv _ y₀ (hG p q) v) hV p q
    have h3 := (PositivityTheory.Xgp.gram_grad.line_deriv _ y₀ hd v).unique h1
    rw [h3]
    simp only [zero_smul, add_zero, sub_self, map_zero, Matrix.mul_zero, sub_zero]
    have e1 : (-(g0 * L v))ᴴ * G y₀ * g0 = -(L v)ᴴ := by
      rw [conjTranspose_neg, conjTranspose_mul, Matrix.neg_mul, Matrix.neg_mul, Matrix.mul_assoc (L v)ᴴ,
        Matrix.mul_assoc (L v)ᴴ, hg0, Matrix.mul_one]
    have e2 : g0ᴴ * G y₀ * -(g0 * L v) = -L v := by
      rw [Matrix.mul_neg, ← Matrix.mul_assoc, hg0, Matrix.one_mul]
    have e3 : g0ᴴ * Dm v * g0 = (L v)ᴴ + L v := (hLL v).symm
    rw [e1, e2, e3]
    simp
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.WeightedPolynomialHomogeneousCoeffBound

section

@[expose] public section

open Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem normal_holomorphic_frame : ∀ (d : ℕ) (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (y₀ : Fin d → ℂ), (G y₀).PosDef → (∀ y, (G y).IsHermitian) → (∀ p q, ContDiffAt ℝ 2 (fun y => G y p q) y₀) → ∃ g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ, (∀ p q, Differentiable ℂ fun y => g y p q) ∧ IsUnit (g y₀).det ∧ (g y₀)ᴴ * G y₀ * g y₀ = 1 ∧ ∀ p q, fderiv ℝ (fun y => ((g y)ᴴ * G y * g y) p q) y₀ = 0 :=
  PositivityTheory.Xgp.projective_line_normal_frame

end GlobalTheory.CompanionTheory.Ar.PB
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.WeightedPolynomialHomogeneousCoeffBoundStatement

section

@[expose] public section

open Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.exists_holomorphic_normal_frame : ∀ (d : ℕ) (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (y₀ : Fin d → ℂ), (G y₀).PosDef → (∀ y, (G y).IsHermitian) → (∀ p q, ContDiffAt ℝ 2 (fun y => G y p q) y₀) → ∃ g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ, (∀ p q, Differentiable ℂ fun y => g y p q) ∧ IsUnit (g y₀).det ∧ (g y₀)ᴴ * G y₀ * g y₀ = 1 ∧ ∀ p q, fderiv ℝ (fun y => ((g y)ᴴ * G y * g y) p q) y₀ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.normal_holomorphic_frame | exact GlobalTheory.CompanionTheory.Ar.PB.normal_holomorphic_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.normal_holomorphic_frame <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalUnitaryNormalFrame2x2

section

@[expose] public section

open MeasureTheory Filter Topology Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

theorem GlobalTheory.CompanionTheory.Ar.PB.FibPt.exists_frame_normal_near :
    ∀ (d : ℕ) (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (y : Fin d → ℂ), (∀ᶠ y' in 𝓝 y, (G y').PosDef) →
      (∀ p q, ContDiffAt ℝ 2 (fun y' => G y' p q) y) →
      ∃ g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ, (∀ p q, Differentiable ℂ fun y' => g y' p q) ∧
        IsUnit (g y).det ∧ (∀ᶠ y' in 𝓝 y, ((g y')ᴴ * G y' * g y').PosDef) ∧
        (∀ p q, ContDiffAt ℝ 2 (fun y' => ((g y')ᴴ * G y' * g y') p q) y) ∧
        (g y)ᴴ * G y * g y = 1 ∧ ∀ p q, fderiv ℝ (fun y' => ((g y')ᴴ * G y' * g y') p q) y = 0 := by
  intro d G y hpd hC
  let Gh : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ := fun y' => (1 / 2 : ℂ) • (G y' + (G y')ᴴ)
  have hent : ∀ y' p q, Gh y' p q = (1 / 2 : ℂ) * (G y' p q + (starRingEnd ℂ) (G y' q p)) := by
    intro y' p q
    simp [Gh, Matrix.smul_apply, Matrix.add_apply, Matrix.conjTranspose_apply]
    ring
  have hherm : ∀ y', (Gh y').IsHermitian := by
    intro y'
    ext p q
    rw [Matrix.conjTranspose_apply, hent, hent]
    have hhalf : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
      apply Complex.ext <;> simp
    simp only [RCLike.star_def, map_mul, map_add (f := _), Complex.conj_conj, hhalf]
    ring
  have hEq : ∀ᶠ y' in 𝓝 y, Gh y' = G y' := by
    filter_upwards [hpd] with y' h
    have e : (G y')ᴴ = G y' := h.isHermitian.eq
    ext p q
    simp only [Gh, e, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    ring
  have hy : Gh y = G y := hEq.self_of_nhds
  have hpdy : (Gh y).PosDef := by
    rw [hy]
    exact hpd.self_of_nhds
  have hCh : ∀ p q, ContDiffAt ℝ 2 (fun y' => Gh y' p q) y := by
    intro p q
    have h1 := hC p q
    have h2 : ContDiffAt ℝ 2 (fun y' => (starRingEnd ℂ) (G y' q p)) y :=
      Complex.conjCLE.contDiff.contDiffAt.comp y (hC q p)
    have e : (fun y' => Gh y' p q) = fun y' => (1 / 2 : ℂ) * (G y' p q + (starRingEnd ℂ) (G y' q p)) :=
      funext fun y' => hent y' p q
    rw [e]
    exact contDiffAt_const.mul (h1.add h2)
  obtain ⟨g, hg, hu, h1, hd⟩ := GlobalTheory.T.exists_holomorphic_normal_frame d Gh y hpdy hherm hCh
  refine ⟨g, hg, hu, ?_, GlobalTheory.CompanionTheory.Ar.PB.FibPt.contDiffAt_frame_entry G g y hC hg, ?_, ?_⟩
  · have hc : ∀ p q, ContinuousAt (fun y' => g y' p q) y := fun p q => (hg p q).continuous.continuousAt
    have hdetc : ContinuousAt (fun y' => (g y').det) y := by
      simp only [Matrix.det_fin_two]
      exact ((hc 0 0).mul (hc 1 1)).sub ((hc 0 1).mul (hc 1 0))
    have hne : ∀ᶠ y' in 𝓝 y, (g y').det ≠ 0 := hdetc.eventually_ne hu.ne_zero
    filter_upwards [hpd, hne] with y' ha hb
    exact (GlobalTheory.T.log_sine_mobius_transform (G y') (g y') ha (isUnit_iff_ne_zero.mpr hb)).1
  · rw [← hy]
    exact h1
  · intro p q
    have hev : (fun y' => ((g y')ᴴ * G y' * g y') p q) =ᶠ[𝓝 y] fun y' => ((g y')ᴴ * Gh y' * g y') p q := by
      filter_upwards [hEq] with y' h
      rw [h]
    rw [hev.fderiv_eq]
    exact hd p q
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalUnitaryNormalFrame2x2Statement

section

@[expose] public section

open MeasureTheory Filter Topology Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.local_unitary_normal_frame_2x2 : ∀ (d : ℕ) (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (y : Fin d → ℂ), (∀ᶠ y' in 𝓝 y, (G y').PosDef) → (∀ p q, ContDiffAt ℝ 2 (fun y' => G y' p q) y) → ∃ g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ, (∀ p q, Differentiable ℂ fun y' => g y' p q) ∧ IsUnit (g y).det ∧ (∀ᶠ y' in 𝓝 y, ((g y')ᴴ * G y' * g y').PosDef) ∧ (∀ p q, ContDiffAt ℝ 2 (fun y' => ((g y')ᴴ * G y' * g y') p q) y) ∧ (g y)ᴴ * G y * g y = 1 ∧ ∀ p q, fderiv ℝ (fun y' => ((g y')ᴴ * G y' * g y') p q) y = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FibPt.exists_frame_normal_near | exact GlobalTheory.CompanionTheory.Ar.PB.FibPt.exists_frame_normal_near | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FibPt.exists_frame_normal_near <;> assumption)
end
end
