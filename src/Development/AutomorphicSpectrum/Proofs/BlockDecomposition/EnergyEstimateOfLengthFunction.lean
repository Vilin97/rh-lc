module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Rr
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivIntegralCompactSupportStatement
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Normed
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Rr
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.DiscreteSeriesTopClasses.IsInvOne
import Mathlib.Analysis.Matrix.Normed
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothTimeRightDerivativesCommuteStatement
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EnergyDensityTimeDerivativeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothTimeRightDerivativesCommuteStatement
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EnergyDensityPointwiseEstimate

section

@[expose] public section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveSpd

theorem pointwise_energy_ineq : ∀ {W ι : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [Fintype ι] (w v : W) (Y : ι → W) (L : ι → ℝ) (A : W →L[ℝ] W) (C₁ C c φ : ℝ), 0 ≤ C₁ → C₁ * (1 + Fintype.card ι) ≤ C → c ≤ 0 → 0 ≤ φ → (∀ p, |L p| ≤ C₁) → c * C * (‖w‖ ^ 2 + (1 / 4) * ∑ p, ‖Y p‖ ^ 2 + ‖v‖ ^ 2) + φ * (2 * ⟪A v, w⟫_ℝ + 2 * ⟪w, v⟫_ℝ) - (1 / 2) * ∑ p, c * L p * ⟪Y p, w⟫_ℝ ≤ (‖A‖ + 1) * (φ * (‖w‖ ^ 2 + (1 / 4) * ∑ p, ‖Y p‖ ^ 2 + ‖v‖ ^ 2)) := by
  intro W ι _ _ _ w v Y L A C₁ C c φ hC₁ hC hc hφ hL
  have hS0 : 0 ≤ ∑ p, ‖Y p‖ ^ 2 := Finset.sum_nonneg fun p _ => by positivity
  obtain ⟨S, hS⟩ : ∃ S, S = ∑ p, ‖Y p‖ ^ 2 := ⟨_, rfl⟩
  rw [← hS] at hS0 ⊢
  obtain ⟨D, hD⟩ : ∃ D, D = ‖w‖ ^ 2 + (1 / 4) * S + ‖v‖ ^ 2 := ⟨_, rfl⟩
  rw [← hD]
  have hw2 : 0 ≤ ‖w‖ ^ 2 := by positivity
  have hv2 : 0 ≤ ‖v‖ ^ 2 := by positivity
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hwD : ‖w‖ ^ 2 ≤ D := by rw [hD]; linarith
  have hSD : (1 / 4) * S ≤ D := by rw [hD]; linarith

  have hterm : ∀ p, -(c * L p * ⟪Y p, w⟫_ℝ) ≤ (-c) * C₁ * ((1 / 2) * (‖Y p‖ ^ 2 + ‖w‖ ^ 2)) := by
    intro p
    have hin : |⟪Y p, w⟫_ℝ| ≤ ‖Y p‖ * ‖w‖ := abs_real_inner_le_norm _ _
    have hmul : |L p * ⟪Y p, w⟫_ℝ| ≤ C₁ * ((1 / 2) * (‖Y p‖ ^ 2 + ‖w‖ ^ 2)) := by
      rw [abs_mul]
      have h2 : ‖Y p‖ * ‖w‖ ≤ (1 / 2) * (‖Y p‖ ^ 2 + ‖w‖ ^ 2) := by
        nlinarith [sq_nonneg (‖Y p‖ - ‖w‖)]
      exact mul_le_mul (hL p) (hin.trans h2) (abs_nonneg _) hC₁
    have hle : L p * ⟪Y p, w⟫_ℝ ≤ C₁ * ((1 / 2) * (‖Y p‖ ^ 2 + ‖w‖ ^ 2)) :=
      (le_abs_self _).trans hmul
    have := mul_le_mul_of_nonneg_left hle (neg_nonneg.2 hc)
    calc -(c * L p * ⟪Y p, w⟫_ℝ) = (-c) * (L p * ⟪Y p, w⟫_ℝ) := by ring
      _ ≤ (-c) * (C₁ * ((1 / 2) * (‖Y p‖ ^ 2 + ‖w‖ ^ 2))) := this
      _ = (-c) * C₁ * ((1 / 2) * (‖Y p‖ ^ 2 + ‖w‖ ^ 2)) := by ring
  have hsum : -(1 / 2) * ∑ p, c * L p * ⟪Y p, w⟫_ℝ
      ≤ (-c) * C₁ * ((1 / 4) * S + (1 / 4) * (Fintype.card ι : ℝ) * ‖w‖ ^ 2) := by
    have h1 : ∑ p, -(c * L p * ⟪Y p, w⟫_ℝ)
        ≤ ∑ p, (-c) * C₁ * ((1 / 2) * (‖Y p‖ ^ 2 + ‖w‖ ^ 2)) :=
      Finset.sum_le_sum fun p _ => hterm p
    have h2 : ∑ p, (-c) * C₁ * ((1 / 2) * (‖Y p‖ ^ 2 + ‖w‖ ^ 2))
        = (-c) * C₁ * ((1 / 2) * (S + (Fintype.card ι : ℝ) * ‖w‖ ^ 2)) := by
      rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib, ← hS]
      simp [Finset.card_univ]
    rw [Finset.sum_neg_distrib, h2] at h1
    linarith
  have hN0 : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hbr : (1 / 4) * S + (1 / 4) * (Fintype.card ι : ℝ) * ‖w‖ ^ 2
      ≤ (1 + (Fintype.card ι : ℝ)) * D := by
    nlinarith [mul_le_mul_of_nonneg_left hwD hN0, mul_nonneg hN0 hw2]
  have hcC : (-c) * C₁ * ((1 / 4) * S + (1 / 4) * (Fintype.card ι : ℝ) * ‖w‖ ^ 2)
      ≤ (-c) * C * D := by
    have hnc : 0 ≤ -c := neg_nonneg.2 hc
    calc (-c) * C₁ * ((1 / 4) * S + (1 / 4) * (Fintype.card ι : ℝ) * ‖w‖ ^ 2)
        ≤ (-c) * C₁ * ((1 + (Fintype.card ι : ℝ)) * D) :=
          mul_le_mul_of_nonneg_left hbr (mul_nonneg hnc hC₁)
      _ = (-c) * (C₁ * (1 + (Fintype.card ι : ℝ))) * D := by ring
      _ ≤ (-c) * C * D :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC hnc) hD0

  have hAv : ⟪A v, w⟫_ℝ ≤ ‖A‖ * ‖v‖ * ‖w‖ :=
    (real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (A.le_opNorm v) (norm_nonneg _))
  have hwv : ⟪w, v⟫_ℝ ≤ ‖w‖ * ‖v‖ := real_inner_le_norm _ _
  have hvw : 2 * (‖v‖ * ‖w‖) ≤ ‖v‖ ^ 2 + ‖w‖ ^ 2 := by
    nlinarith [sq_nonneg (‖v‖ - ‖w‖)]
  have hvwD : 2 * (‖v‖ * ‖w‖) ≤ D := by rw [hD] at *; linarith
  have hA0 : 0 ≤ ‖A‖ := norm_nonneg _
  have hbrack : 2 * ⟪A v, w⟫_ℝ + 2 * ⟪w, v⟫_ℝ ≤ (‖A‖ + 1) * D := by
    have h3 : ‖A‖ * (2 * (‖v‖ * ‖w‖)) ≤ ‖A‖ * D := mul_le_mul_of_nonneg_left hvwD hA0
    nlinarith
  have hφ' := mul_le_mul_of_nonneg_left hbrack hφ
  have hrew : (1 / 2) * ∑ p, c * L p * ⟪Y p, w⟫_ℝ
      = -(-(1 / 2) * ∑ p, c * L p * ⟪Y p, w⟫_ℝ) := by ring
  rw [hrew]
  nlinarith

end GlobalTheory.CompanionTheory.WaveSpd
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EnergyDensityPointwiseEstimateStatement

section

@[expose] public section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.energy_density_pointwise_estimate : ∀ {W ι : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [Fintype ι] (w v : W) (Y : ι → W) (L : ι → ℝ) (A : W →L[ℝ] W) (C₁ C c φ : ℝ), 0 ≤ C₁ → C₁ * (1 + Fintype.card ι) ≤ C → c ≤ 0 → 0 ≤ φ → (∀ p, |L p| ≤ C₁) → c * C * (‖w‖ ^ 2 + (1 / 4) * ∑ p, ‖Y p‖ ^ 2 + ‖v‖ ^ 2) + φ * (2 * ⟪A v, w⟫_ℝ + 2 * ⟪w, v⟫_ℝ) - (1 / 2) * ∑ p, c * L p * ⟪Y p, w⟫_ℝ ≤ (‖A‖ + 1) * (φ * (‖w‖ ^ 2 + (1 / 4) * ∑ p, ‖Y p‖ ^ 2 + ‖v‖ ^ 2)) := by
  first | exact @GlobalTheory.CompanionTheory.WaveSpd.pointwise_energy_ineq | exact GlobalTheory.CompanionTheory.WaveSpd.pointwise_energy_ineq | (intros; apply GlobalTheory.CompanionTheory.WaveSpd.pointwise_energy_ineq <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EnergyDensitySmooth

section

@[expose] public section

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

namespace GlobalTheory.CompanionTheory.WaveSpd

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Sm.normSq {n : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {u : ℝ → Mat n → W} (hu : Sm u) : Sm fun s y => (‖u s y‖ ^ 2 : ℝ) := by
  have h := ContDiffOn.norm_sq ℝ (show ContDiffOn ℝ ∞ (Function.uncurry u) _ from hu)
  exact h.congr fun z _ => rfl

theorem Sm.inner {n : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {u v : ℝ → Mat n → W} (hu : Sm u) (hv : Sm v) : Sm fun s y => ⟪u s y, v s y⟫_ℝ := by
  have h := ContDiffOn.inner ℝ (show ContDiffOn ℝ ∞ (Function.uncurry u) _ from hu)
    (show ContDiffOn ℝ ∞ (Function.uncurry v) _ from hv)
  exact h.congr fun z _ => rfl

theorem Sm.add {n : ℕ} {f g : ℝ → Mat n → ℝ} (hf : Sm f) (hg : Sm g) :
    Sm fun s y => f s y + g s y := by
  have h := ContDiffOn.add (show ContDiffOn ℝ ∞ (Function.uncurry f) _ from hf)
    (show ContDiffOn ℝ ∞ (Function.uncurry g) _ from hg)
  exact h.congr fun z _ => rfl

theorem Sm.const_mul {n : ℕ} (c : ℝ) {f : ℝ → Mat n → ℝ} (hf : Sm f) :
    Sm fun s y => c * f s y := by
  have h := ContDiffOn.mul (contDiffOn_const (c := c))
    (show ContDiffOn ℝ ∞ (Function.uncurry f) _ from hf)
  exact h.congr fun z _ => rfl

theorem Sm.sum {n : ℕ} {ι : Type} (t : Finset ι) {f : ι → ℝ → Mat n → ℝ}
    (hf : ∀ i ∈ t, Sm (f i)) : Sm fun s y => ∑ i ∈ t, f i s y := by
  have h := ContDiffOn.sum (s := t) (f := fun i => Function.uncurry (f i))
    (fun i hi => show ContDiffOn ℝ ∞ (Function.uncurry (f i)) _ from hf i hi)
  exact h.congr fun z _ => by simp [Function.uncurry]

theorem sm_dens_inner {n : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (u : ℝ → Mat n → W) (hu : Sm u) :
    Sm (dens u) ∧ ∀ (X : Mat n) (v : ℝ → Mat n → W), Sm v →
      Sm fun s y => ⟪Rt X u s y, v s y⟫_ℝ := by
  obtain ⟨hdt, hRt, -⟩ := GlobalTheory.T.smooth_time_right_derivatives_commute u hu
  refine ⟨?_, fun X v hv => (hRt X).inner hv⟩
  exact (hdt.normSq.add (Sm.const_mul _ (Sm.sum _ fun p _ => (hRt (hm p)).normSq))).add hu.normSq

end GlobalTheory.CompanionTheory.WaveSpd
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EnergyDensitySmoothStatement

section

@[expose] public section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.energy_density_smooth : ∀ {n : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] (u : ℝ → Mat n → W), Sm u → Sm (dens u) ∧ ∀ (X : Mat n) (v : ℝ → Mat n → W), Sm v → Sm fun s y => ⟪Rt X u s y, v s y⟫_ℝ := by
  first | exact @GlobalTheory.CompanionTheory.WaveSpd.sm_dens_inner | exact GlobalTheory.CompanionTheory.WaveSpd.sm_dens_inner | (intros; apply GlobalTheory.CompanionTheory.WaveSpd.sm_dens_inner <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EnergyEstimateOfLengthFunction

section

@[expose] public section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.WaveSpd.LocEnergy

variable {n : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

def cw (ℓ : Mat n → ℝ) (χ : ℝ → ℝ) (C r s : ℝ) (y : Mat n) : ℝ := χ (ℓ y + C * s - r)

theorem sm_cw {ℓ : Mat n → ℝ} {χ : ℝ → ℝ} (C r : ℝ) (hℓ : ContDiffOn ℝ ∞ ℓ (GLs n))
    (hχ : ContDiff ℝ ∞ χ) : Sm (cw ℓ χ C r) := by
  have h1 : ContDiffOn ℝ ∞ (fun q : ℝ × Mat n => ℓ q.2 + C * q.1 - r) (Set.univ ×ˢ GLs n) := by
    have h2 : ContDiffOn ℝ ∞ (fun q : ℝ × Mat n => ℓ q.2) (Set.univ ×ˢ GLs n) :=
      hℓ.comp contDiff_snd.contDiffOn (fun q hq => hq.2)
    have h3 : ContDiffOn ℝ ∞ (fun q : ℝ × Mat n => C * q.1) (Set.univ ×ˢ GLs n) :=
      (contDiff_const.mul contDiff_fst).contDiffOn
    exact (h2.add h3).sub contDiffOn_const
  exact hχ.comp_contDiffOn h1

theorem sm_mul {f g : ℝ → Mat n → ℝ} (hf : Sm f) (hg : Sm g) : Sm fun s y => f s y * g s y :=
  ContDiffOn.mul hf hg

theorem hasDerivAt_chi {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (a : ℝ) : HasDerivAt χ (deriv χ a) a :=
  ((hχ.differentiable (by simp)) a).hasDerivAt

theorem hasDerivAt_cw {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (ℓ : Mat n → ℝ) (C r s : ℝ) (y : Mat n) :
    HasDerivAt (fun s' => cw ℓ χ C r s' y) (deriv χ (ℓ y + C * s - r) * C) s := by
  have h1 : HasDerivAt (fun s' : ℝ => ℓ y + C * s' - r) C s := by
    simpa using (((hasDerivAt_id s).const_mul C).const_add (ℓ y)).sub_const r
  exact (hasDerivAt_chi hχ _).comp s h1

theorem dt_rho {ℓ : Mat n → ℝ} {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {u : ℝ → Mat n → W} (hu : Sm u)
    (C r s : ℝ) {y : Mat n} (hy : y ∈ GLs n) :
    dt (fun s y => cw ℓ χ C r s y * dens u s y) s y =
      deriv χ (ℓ y + C * s - r) * C * dens u s y + cw ℓ χ C r s y *
        (2 * ⟪dt (dt u) s y, dt u s y⟫_ℝ
          + (1 / 2) * ∑ p : Ix n, ⟪Rr (hm p) (dt u s) y, Rt (hm p) u s y⟫_ℝ
          + 2 * ⟪dt u s y, u s y⟫_ℝ) :=
  ((hasDerivAt_cw hχ ℓ C r s y).mul (GlobalTheory.T.energy_density_time_derivative u hu s y hy)).deriv

theorem rr_cw_inner {ℓ : Mat n → ℝ} {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (C r s : ℝ)
    {f g : Mat n → W} {y : Mat n} (hℓ : DifferentiableAt ℝ ℓ y) (hf : DifferentiableAt ℝ f y)
    (hg : DifferentiableAt ℝ g y) (X : Mat n) :
    Rr X (fun y' => cw ℓ χ C r s y' * ⟪f y', g y'⟫_ℝ) y =
      deriv χ (ℓ y + C * s - r) * fderiv ℝ ℓ y (y * X) * ⟪f y, g y⟫_ℝ +
        cw ℓ χ C r s y * (⟪Rr X f y, g y⟫_ℝ + ⟪f y, Rr X g y⟫_ℝ) := by
  have h1 : HasFDerivAt (fun y' => cw ℓ χ C r s y')
      (deriv χ (ℓ y + C * s - r) • fderiv ℝ ℓ y) y :=
    (hasDerivAt_chi hχ _).comp_hasFDerivAt y ((hℓ.hasFDerivAt.add_const (C * s)).sub_const r)
  have h2 : HasFDerivAt (fun t => ⟪f t, g t⟫_ℝ) (fderiv ℝ (fun t => ⟪f t, g t⟫_ℝ) y) y :=
    (hf.inner ℝ hg).hasFDerivAt
  have h3 : HasFDerivAt (fun y' => cw ℓ χ C r s y' * ⟪f y', g y'⟫_ℝ) _ y := h1.mul h2
  have h4 : fderiv ℝ (fun t => ⟪f t, g t⟫_ℝ) y (y * X) =
      ⟪f y, Rr X g y⟫_ℝ + ⟪Rr X f y, g y⟫_ℝ := fderiv_inner_apply ℝ hf hg (y * X)
  have h5 : fderiv ℝ (fun y' => cw ℓ χ C r s y' * ⟪f y', g y'⟫_ℝ) y (y * X) =
      cw ℓ χ C r s y * fderiv ℝ (fun t => ⟪f t, g t⟫_ℝ) y (y * X) +
        ⟪f y, g y⟫_ℝ * (deriv χ (ℓ y + C * s - r) * fderiv ℝ ℓ y (y * X)) := by
    rw [h3.fderiv]
    rfl
  show fderiv ℝ (fun y' => cw ℓ χ C r s y' * ⟪f y', g y'⟫_ℝ) y (y * X) = _
  rw [h5, h4]
  ring

theorem diffAt_of_sm {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) {y : Mat n} (hy : y ∈ GLs n) : DifferentiableAt ℝ f y :=
  (hf.contDiffAt (isOpen_GLs.mem_nhds hy)).differentiableAt (by simp)

theorem pt_bound {ℓ : Mat n → ℝ} (hℓ : ContDiffOn ℝ ∞ ℓ (GLs n)) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχ' : ∀ x, deriv χ x ≤ 0) (hχ0 : ∀ x, 0 ≤ χ x)
    {u : ℝ → Mat n → W} (hu : Sm u) (A : W →L[ℝ] W)
    (hwave : ∀ s, ∀ y ∈ GLs n, dt (dt u) s y =
      (1 / 4 : ℝ) • ∑ p : Ix n, Rr (hm p) (Rt (hm p) u s) y + A (u s y))
    {C₁ C : ℝ} (r : ℝ) (hC₁ : 0 ≤ C₁) (hC : C₁ * (1 + Fintype.card (Ix n)) ≤ C)
    (hL : ∀ y ∈ GLs n, ∀ p : Ix n, |fderiv ℝ ℓ y (y * hm p)| ≤ C₁)
    (s : ℝ) {y : Mat n} (hy : y ∈ GLs n) :
    dt (fun s y => cw ℓ χ C r s y * dens u s y) s y -
        (1 / 2) * ∑ p : Ix n,
          Rr (hm p) (fun y' => cw ℓ χ C r s y' * ⟪Rt (hm p) u s y', dt u s y'⟫_ℝ) y ≤
      (‖A‖ + 1) * (cw ℓ χ C r s y * dens u s y) := by
  have hdu := (GlobalTheory.T.smooth_time_right_derivatives_commute u hu).1
  have hRt := (GlobalTheory.T.smooth_time_right_derivatives_commute u hu).2.1
  have hℓd := diffAt_of_sm hℓ hy
  have hw : DifferentiableAt ℝ (dt u s) y := diffAt_of_sm ((GlobalTheory.T.smooth_time_right_derivatives_commute _ hdu).2.2.1 s) hy
  have hY : ∀ p : Ix n, DifferentiableAt ℝ (Rt (hm p) u s) y :=
    fun p => diffAt_of_sm ((GlobalTheory.T.smooth_time_right_derivatives_commute _ (hRt _)).2.2.1 s) hy
  have hpt := GlobalTheory.T.energy_density_pointwise_estimate (dt u s y) (u s y) (fun p : Ix n => Rt (hm p) u s y)
    (fun p => fderiv ℝ ℓ y (y * hm p)) A C₁ C (deriv χ (ℓ y + C * s - r)) (cw ℓ χ C r s y)
    hC₁ hC (hχ' _) (hχ0 _) (fun p => hL y hy p)
  have hD : ‖dt u s y‖ ^ 2 + (1 / 4) * ∑ p : Ix n, ‖Rt (hm p) u s y‖ ^ 2 + ‖u s y‖ ^ 2
      = dens u s y := rfl
  rw [hD] at hpt
  have e1 : ⟪(1 / 4 : ℝ) • ∑ p : Ix n, Rr (hm p) (Rt (hm p) u s) y + A (u s y), dt u s y⟫_ℝ
      = (1 / 4) * ∑ p : Ix n, ⟪Rr (hm p) (Rt (hm p) u s) y, dt u s y⟫_ℝ
        + ⟪A (u s y), dt u s y⟫_ℝ := by
    rw [inner_add_left, real_inner_smul_left, sum_inner]
  have e2 : ∑ p : Ix n,
      Rr (hm p) (fun y' => cw ℓ χ C r s y' * ⟪Rt (hm p) u s y', dt u s y'⟫_ℝ) y =
      ∑ p : Ix n, deriv χ (ℓ y + C * s - r) * fderiv ℝ ℓ y (y * hm p) *
          ⟪Rt (hm p) u s y, dt u s y⟫_ℝ +
        cw ℓ χ C r s y * (∑ p : Ix n, ⟪Rr (hm p) (Rt (hm p) u s) y, dt u s y⟫_ℝ +
          ∑ p : Ix n, ⟪Rr (hm p) (dt u s) y, Rt (hm p) u s y⟫_ℝ) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [rr_cw_inner hχ C r s hℓd (hY p) hw (hm p), real_inner_comm (Rt (hm p) u s y)]
  rw [dt_rho hχ hu C r s hy, hwave s y hy, e1, e2]
  refine le_trans (le_of_eq ?_) hpt
  ring

theorem integrable_of_val [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))
    [μ.IsHaarMeasure] {f : Mat n → ℝ} (hf : ContinuousOn f (GLs n)) {K : Set (G n)}
    (hK : IsCompact K) (h : ∀ y : G n, y ∉ K → f y.val = 0) :
    Integrable (fun y : G n => f y.val) μ :=
  (hf.comp_continuous Units.continuous_val val_mem_GLs).integrable_of_hasCompactSupport
    (HasCompactSupport.intro hK h)

theorem energy_diff_ineq : ∀ {n : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (ℓ : Mat n → ℝ), ContDiffOn ℝ ∞ ℓ (GLs n) → (∀ R : ℝ, IsCompact {y : G n | ℓ y.val ≤ R}) → ∀ (C₁ : ℝ), 0 ≤ C₁ → (∀ y ∈ GLs n, ∀ p : Ix n, |fderiv ℝ ℓ y (y * hm p)| ≤ C₁) → (∀ Ψ : Mat n → ℝ, ContDiffOn ℝ ∞ Ψ (GLs n) → (∃ R : ℝ, ∀ y ∈ GLs n, R < ℓ y → Ψ y = 0) → ∀ X : Mat n, ∫ y : G n, Rr X Ψ y.val ∂μ = 0) → ∀ (χ : ℝ → ℝ), ContDiff ℝ ∞ χ → (∀ x, deriv χ x ≤ 0) → (∀ x, 0 ≤ χ x) → (∀ x, 1 ≤ x → χ x = 0) → ∀ (u : ℝ → Mat n → W), Sm u → ∀ (A : W →L[ℝ] W), (∀ s, ∀ y ∈ GLs n, dt (dt u) s y = (1 / 4 : ℝ) • ∑ p : Ix n, Rr (hm p) (Rt (hm p) u s) y + A (u s y)) → ∀ (C : ℝ), C₁ * (1 + Fintype.card (Ix n)) ≤ C → ∀ (r : ℝ), ∃ K : ℝ, ∀ s, ∃ e' : ℝ, HasDerivAt (fun s' => ∫ y : G n, χ (ℓ y.val + C * s' - r) * dens u s' y.val ∂μ) e' s ∧ e' ≤ K * ∫ y : G n, χ (ℓ y.val + C * s - r) * dens u s y.val ∂μ := by
  intro n W _ _ _ _ μ _ ℓ hℓ hcpt C₁ hC₁ hL hIBP χ hχ hχ' hχ0 hχ1 u hu A hwave C hC r
  refine ⟨‖A‖ + 1, fun s => ?_⟩
  have hC0 : 0 ≤ C := le_trans (mul_nonneg hC₁ (by positivity)) hC
  have hdu := (GlobalTheory.T.smooth_time_right_derivatives_commute u hu).1
  have hcw := sm_cw C r hℓ hχ
  let ρ : ℝ → Mat n → ℝ := fun s y => cw ℓ χ C r s y * dens u s y
  have hρ : Sm ρ := sm_mul hcw (GlobalTheory.T.energy_density_smooth u hu).1
  let Ψ : Ix n → ℝ → Mat n → ℝ :=
    fun p s y => cw ℓ χ C r s y * ⟪Rt (hm p) u s y, dt u s y⟫_ℝ
  have hΨ : ∀ p, Sm (Ψ p) := fun p => sm_mul hcw ((GlobalTheory.T.energy_density_smooth u hu).2 _ _ hdu)
  obtain ⟨R, hR⟩ : ∃ R, R = r + 1 + C * (|s| + 1) := ⟨_, rfl⟩
  have hK : IsCompact {y : G n | ℓ y.val ≤ R} := hcpt R
  have hvan : ∀ s' ∈ Metric.ball s 1, ∀ y : G n, y ∉ {y : G n | ℓ y.val ≤ R} →
      ρ s' y.val = 0 := by
    intro s' hs' y hy
    have hy' : R < ℓ y.val := not_le.1 hy
    have h0 : 0 ≤ |s| + 1 + s' := by
      have h1 := neg_abs_le s
      have h2 := (abs_lt.1 (Real.dist_eq s' s ▸ Metric.mem_ball.1 hs')).1
      linarith
    have h3 := mul_nonneg hC0 h0
    have h4 : 1 ≤ ℓ y.val + C * s' - r := by rw [hR] at hy'; nlinarith
    simp only [ρ, cw, hχ1 _ h4, zero_mul]
  have hder := GlobalTheory.T.deriv_integral_compact_support μ ρ hρ _ hK s 1 one_pos hvan
  refine ⟨_, hder, ?_⟩
  have hdtvan : ∀ y : G n, y ∉ {y : G n | ℓ y.val ≤ R} → dt ρ s y.val = 0 := by
    intro y hy
    have h1 : (fun r' => ρ r' y.val) =ᶠ[nhds s] fun _ => 0 := by
      filter_upwards [Metric.ball_mem_nhds s one_pos] with s' hs' using hvan s' hs' y hy
    show deriv (fun r' => ρ r' y.val) s = 0
    rw [h1.deriv_eq]; simp
  have I_dt := integrable_of_val μ
    ((GlobalTheory.T.smooth_time_right_derivatives_commute _ (GlobalTheory.T.smooth_time_right_derivatives_commute _ hρ).1).2.2.1 s).continuousOn hK hdtvan
  have I_ρ := integrable_of_val μ ((GlobalTheory.T.smooth_time_right_derivatives_commute _ hρ).2.2.1 s).continuousOn hK
    (hvan s (Metric.mem_ball_self one_pos))
  have hRs : r + 1 - C * s ≤ R := by
    have h1 := neg_abs_le s
    have h2 : 0 ≤ C * (|s| + 1 + s) := mul_nonneg hC0 (by linarith)
    rw [hR]; nlinarith
  have hrrvan : ∀ (p : Ix n) (y : G n), y ∉ {y : G n | ℓ y.val ≤ R} →
      Rr (hm p) (Ψ p s) y.val = 0 := by
    intro p y hy
    have hy' : R < ℓ y.val := not_le.1 hy
    have hcont : ContinuousAt ℓ y.val := (diffAt_of_sm hℓ (val_mem_GLs y)).continuousAt
    have h1 : Ψ p s =ᶠ[nhds y.val] fun _ => 0 := by
      filter_upwards [hcont.eventually (lt_mem_nhds hy')] with z hz
      have h4 : 1 ≤ ℓ z + C * s - r := by linarith
      simp only [Ψ, cw, hχ1 _ h4, zero_mul]
    show fderiv ℝ (Ψ p s) y.val _ = 0
    rw [h1.fderiv_eq]; simp
  have I_rr : ∀ p : Ix n, Integrable (fun y : G n => Rr (hm p) (Ψ p s) y.val) μ := fun p =>
    integrable_of_val μ
      ((GlobalTheory.T.smooth_time_right_derivatives_commute _ ((GlobalTheory.T.smooth_time_right_derivatives_commute _ (hΨ p)).2.1 (hm p))).2.2.1 s).continuousOn hK
      (hrrvan p)
  have hZ : ∀ p : Ix n, ∫ y : G n, Rr (hm p) (Ψ p s) y.val ∂μ = 0 := fun p =>
    hIBP (Ψ p s) ((GlobalTheory.T.smooth_time_right_derivatives_commute _ (hΨ p)).2.2.1 s)
      ⟨r + 1 - C * s, fun y _ hy => by
        have h4 : 1 ≤ ℓ y + C * s - r := by linarith
        simp only [Ψ, cw, hχ1 _ h4, zero_mul]⟩ (hm p)
  have I_sum : Integrable (fun y : G n => (1 / 2 : ℝ) * ∑ p : Ix n, Rr (hm p) (Ψ p s) y.val) μ :=
    (integrable_finsetSum _ fun p _ => I_rr p).const_mul _
  calc ∫ y : G n, dt ρ s y.val ∂μ
      = ∫ y : G n, (dt ρ s y.val - (1 / 2 : ℝ) * ∑ p : Ix n, Rr (hm p) (Ψ p s) y.val) ∂μ := by
        rw [integral_sub I_dt I_sum, integral_const_mul,
          integral_finsetSum _ fun p _ => I_rr p]
        simp [hZ]
    _ ≤ ∫ y : G n, (‖A‖ + 1) * ρ s y.val ∂μ :=
        integral_mono (I_dt.sub I_sum) (I_ρ.const_mul _) fun y =>
          pt_bound hℓ hχ hχ' hχ0 hu A hwave r hC₁ hC hL s (val_mem_GLs y)
    _ = (‖A‖ + 1) * ∫ y : G n, ρ s y.val ∂μ := integral_const_mul _ _

end GlobalTheory.CompanionTheory.WaveSpd.LocEnergy
end
end
end
