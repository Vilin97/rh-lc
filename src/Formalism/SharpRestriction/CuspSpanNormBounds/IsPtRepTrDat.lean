module

public import Formalism.SharpRestriction.CuspSpanNormBounds.BlockExponentKappaIdentity
public import Formalism.SharpRestriction.CuspSpanNormBounds.ContinuousCjIT
public import Formalism.SharpRestriction.CuspSpanNormBounds.StarVecMulDM
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceEstimates
public import Formalism.SharpRestriction.CuspSpanNormBounds.SpanMemOfImage
public import Formalism.SharpRestriction.CuspSpanNormBounds.ContinuousRootCoords
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Linter.Style

-- Source module: Formalism.SharpRestriction.CuspSpanNormBounds.BcWeightEqZeroOf

section

@[expose] public section

open MeasureTheory Matrix Finset
open scoped ContDiff

noncomputable section

set_option linter.unusedVariables false

namespace Formalism.MainNotions.FrameBoundFromBesselTorus

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates

def sBig (r : ℕ) (κ τ : ℝ) (p : (Fin r → ℂ) × ℂ) : (Fin r → ℂ) × ℂ :=
  (fun a => ((tF r κ τ a.val ^ 2 : ℝ) : ℂ) * p.1 a, ((τ ^ 2 : ℝ) : ℂ) * p.2)

def sBigL (r : ℕ) (κ τ : ℝ) : ((Fin r → ℂ) × ℂ) →ₗ[ℝ] ((Fin r → ℂ) × ℂ) :=
  LinearMap.prodMap (LinearMap.pi fun a => ((tF r κ τ a.val ^ 2) • LinearMap.id) ∘ₗ LinearMap.proj a)
    ((τ ^ 2) • LinearMap.id)

theorem sBigL_apply (r : ℕ) (κ τ : ℝ) (p : (Fin r → ℂ) × ℂ) : sBigL r κ τ p = sBig r κ τ p := by
  ext a <;> simp [sBigL, sBig, Complex.real_smul]

def jacBig (r : ℕ) (κ τ : ℝ) : ℝ := (∏ a : Fin r, tF r κ τ a.val ^ 4) * τ ^ 4

def wBig (k r : ℕ) (κ τ : ℝ) : ℝ :=
  (∏ a : Fin r, (tF r κ τ a.val ^ 2) ^ (2 * (Mdim k r a - 2))) * (τ ^ 4) ^ (k - 1)

section Norm

variable {k r : ℕ} {κ τ : ℝ}

theorem det_sBigL : LinearMap.det (sBigL r κ τ) = jacBig r κ τ := by
  rw [sBigL, LinearMap.det_prodMap, LinearMap.det_pi]
  simp only [LinearMap.det_smul, LinearMap.det_id, Complex.finrank_real_complex, mul_one, jacBig]
  congr 1
  · refine Finset.prod_congr rfl fun a _ => ?_; ring
  · ring

theorem jacBig_pos (hκ : 0 < κ) (hτ : 0 < τ) : 0 < jacBig r κ τ :=
  mul_pos (Finset.prod_pos fun a _ => pow_pos (tF_pos hκ hτ _) 4) (pow_pos hτ 4)

theorem wBig_pos (hκ : 0 < κ) (hτ : 0 < τ) : 0 < wBig k r κ τ :=
  mul_pos (Finset.prod_pos fun a _ => pow_pos (pow_pos (tF_pos hκ hτ _) 2) _) (pow_pos (pow_pos hτ 4) _)

theorem lintegral_sBig (hκ : 0 < κ) (hτ : 0 < τ) (G : (Fin r → ℂ) × ℂ → ENNReal) :
    ∫⁻ p, G p = ENNReal.ofReal (jacBig r κ τ) * ∫⁻ p, G (sBig r κ τ p) := by
  have hdet : LinearMap.det (sBigL r κ τ) ≠ 0 := by rw [det_sBigL]; exact (jacBig_pos hκ hτ).ne'
  let e : ((Fin r → ℂ) × ℂ) ≃ₗ[ℝ] ((Fin r → ℂ) × ℂ) := LinearMap.equivOfDetNeZero (sBigL r κ τ) hdet
  let eM : ((Fin r → ℂ) × ℂ) ≃ᵐ ((Fin r → ℂ) × ℂ) := e.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have : (volume : Measure ((Fin r → ℂ) × ℂ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; exact Measure.prod.instIsAddHaarMeasure _ _
  have hmap : Measure.map eM (volume : Measure ((Fin r → ℂ) × ℂ)) =
      ENNReal.ofReal |(LinearMap.det (sBigL r κ τ))⁻¹| • volume := by
    rw [← Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet]
    rfl
  have h1 : ∫⁻ p, G (sBig r κ τ p) = ENNReal.ofReal |(jacBig r κ τ)⁻¹| * ∫⁻ p, G p := by
    have : (fun p => G (sBig r κ τ p)) = fun p => G (eM p) := by
      funext p; rw [← sBigL_apply]; rfl
    rw [this, ← lintegral_map_equiv, hmap, lintegral_smul_measure, det_sBigL, smul_eq_mul]
  rw [h1, ← mul_assoc, ← ENNReal.ofReal_mul (jacBig_pos hκ hτ).le, abs_inv,
    abs_of_pos (jacBig_pos hκ hτ), mul_inv_cancel₀ (jacBig_pos hκ hτ).ne', ENNReal.ofReal_one, one_mul]

theorem bcWeight_sBig (hκ : 0 < κ) (hτ : 0 < τ) (T T' : ℝ) (p : (Fin r → ℂ) × ℂ) :
    bcWeight k r (τ ^ 2 * T) (τ ^ 2 * T') (sBig r κ τ p) = wBig k r κ τ * bcWeight k r T T' p := by
  have hn : Complex.normSq (((τ ^ 2 : ℝ) : ℂ) * p.2) = τ ^ 4 * Complex.normSq p.2 := by
    rw [Complex.normSq_mul, Complex.normSq_ofReal]; ring
  have h4 : 0 < τ ^ 4 := pow_pos hτ 4
  unfold bcWeight sBig
  simp only
  rw [hn]
  by_cases hc : T * T' ≤ Complex.normSq p.2
  · rw [if_pos (by nlinarith), if_pos hc]
    have hprod : ∏ a : Fin r, ‖((tF r κ τ a.val ^ 2 : ℝ) : ℂ) * p.1 a‖ ^ (2 * (Mdim k r a - 2)) =
        (∏ a : Fin r, (tF r κ τ a.val ^ 2) ^ (2 * (Mdim k r a - 2))) *
          ∏ a : Fin r, ‖p.1 a‖ ^ (2 * (Mdim k r a - 2)) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun a _ => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (pow_pos (tF_pos hκ hτ _) 2), mul_pow]
    rw [hprod, show τ ^ 4 * Complex.normSq p.2 - τ ^ 2 * T * (τ ^ 2 * T') =
      τ ^ 4 * (Complex.normSq p.2 - T * T') by ring, mul_pow, wBig]
    ring
  · rw [if_neg (by intro h; apply hc; nlinarith), if_neg hc, mul_zero]

theorem hsNormSq_eq_sum {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A : Wq →L[ℂ] Wp) :
    hsNormSq A = ∑ i, ‖A (stdOrthonormalBasis ℂ Wq i)‖ ^ 2 := by
  unfold hsNormSq hsInner
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_self_eq_norm_sq_to_K]; norm_cast

theorem hsNormSq_nonneg {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A : Wq →L[ℂ] Wp) : 0 ≤ hsNormSq A := by
  rw [hsNormSq_eq_sum]; positivity

theorem hsNormSq_smul {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (C : ℂ) (A : Wq →L[ℂ] Wp) :
    hsNormSq (C • A) = ‖C‖ ^ 2 * hsNormSq A := by
  rw [hsNormSq_eq_sum, hsNormSq_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [FunLike.coe_smul, Pi.smul_apply, norm_smul, mul_pow]

theorem bcWeight_eq_zero_of {T T' : ℝ} (hk : 2 ≤ k) (p : (Fin r → ℂ) × ℂ)
    (h : ¬ ((∀ a, p.1 a ≠ 0) ∧ T * T' < Complex.normSq p.2)) : bcWeight k r T T' p = 0 := by
  unfold bcWeight
  split_ifs with hc
  · rcases not_and_or.mp h with h1 | h1
    · push Not at h1
      obtain ⟨a, ha⟩ := h1
      have hpos : 2 * (Mdim k r a - 2) ≠ 0 := by unfold Mdim; omega
      rw [Finset.prod_eq_zero (Finset.mem_univ a) (by rw [ha, norm_zero, zero_pow hpos]), zero_mul]
    · have : Complex.normSq p.2 = T * T' := le_antisymm (not_lt.mp h1) hc
      rw [this, sub_self, zero_pow (by omega), mul_zero]
  · rfl

theorem jNorm2_tr (hκ : 0 < κ) (hτ : 0 < τ) (L L₁ : LocBessel k r)
    (e1 : Tz k r L₁.z = τ ^ 2 * Tz k r L.z) (e2 : Tz k r L₁.z' = τ ^ 2 * Tz k r L.z')
    (f : Mx k r → (L.Wq →L[ℂ] L.Wp)) (f₁ : Mx k r → (L₁.Wq →L[ℂ] L₁.Wp))
    (μsec μsec₁ : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (C : ℂ)
    (hk : 2 ≤ k)
    (hJ : ∀ p : (Fin r → ℂ) × ℂ, (∀ a, p.1 a ≠ 0) → Tz k r L.z * Tz k r L.z' < Complex.normSq p.2 →
      hsNormSq (L₁.J f₁ (bigCell k r (sBig r κ τ p).1 (μsec₁ (sBig r κ τ p).2))) =
        ‖C‖ ^ 2 * hsNormSq (L.J f (bigCell k r p.1 (μsec p.2)))) :
    jNorm2 L₁ f₁ μsec₁ = ENNReal.ofReal (jacBig r κ τ * wBig k r κ τ * ‖C‖ ^ 2) * jNorm2 L f μsec := by
  unfold jNorm2 jNormSq
  rw [e1, e2, lintegral_sBig hκ hτ]
  have hw := wBig_pos (k := k) (r := r) hκ hτ
  have hpt : ∀ p : (Fin r → ℂ) × ℂ,
      ENNReal.ofReal (bcWeight k r (τ ^ 2 * Tz k r L.z) (τ ^ 2 * Tz k r L.z') (sBig r κ τ p) *
        ‖Real.sqrt (hsNormSq (L₁.J f₁ (bigCell k r (sBig r κ τ p).1 (μsec₁ (sBig r κ τ p).2))))‖ ^ 2) =
      ENNReal.ofReal (wBig k r κ τ * ‖C‖ ^ 2) *
        ENNReal.ofReal (bcWeight k r (Tz k r L.z) (Tz k r L.z') p *
          ‖Real.sqrt (hsNormSq (L.J f (bigCell k r p.1 (μsec p.2))))‖ ^ 2) := by
    intro p
    by_cases hD : (∀ a, p.1 a ≠ 0) ∧ Tz k r L.z * Tz k r L.z' < Complex.normSq p.2
    swap
    · have h0 := bcWeight_eq_zero_of (T := Tz k r L.z) (T' := Tz k r L.z') hk p (by tauto)
      rw [bcWeight_sBig hκ hτ, h0]; simp
    rw [← ENNReal.ofReal_mul (by positivity), hJ p hD.1 hD.2, bcWeight_sBig hκ hτ,
      Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs,
      Real.sq_sqrt (mul_nonneg (sq_nonneg _) (hsNormSq_nonneg _)), Real.sq_sqrt (hsNormSq_nonneg _)]
    congr 1; ring
  beta_reduce
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc, ← ENNReal.ofReal_mul (jacBig_pos hκ hτ).le,
    mul_assoc (jacBig r κ τ)]

theorem wbPart_smul (z : Fin (2 * r + k + 1) → ℂ) (t : ℂ) : wbPart k r (t • z) = t • wbPart k r z := by
  funext j; rfl

def secTr (τ : ℝ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  fun ζ => μsec (ζ / ((τ ^ 2 : ℝ) : ℂ))

theorem secTr_sBig (hτ : 0 < τ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (p : (Fin r → ℂ) × ℂ) :
    secTr τ μsec (sBig r κ τ p).2 = μsec p.2 := by
  unfold secTr sBig
  have : ((τ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos hτ 2).ne'
  simp only
  rw [mul_div_cancel_left₀ _ this]

theorem isSection_tr (hτ : 0 < τ) {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (h : IsSection k r z z' μsec) : IsSection k r ((τ : ℂ) • z) ((τ : ℂ) • z') (secTr τ μsec) := by
  have h2 : ((τ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos hτ 2).ne'
  have h4 : 0 < τ ^ 4 := pow_pos hτ 4
  have hns : ∀ ζ : ℂ, Complex.normSq (ζ / ((τ ^ 2 : ℝ) : ℂ)) = Complex.normSq ζ / τ ^ 4 := by
    intro ζ; rw [Complex.normSq_div, Complex.normSq_ofReal]; ring
  have hreg : ∀ ζ : ℂ, Tz k r ((τ : ℂ) • z) * Tz k r ((τ : ℂ) • z') < Complex.normSq ζ →
      Tz k r z * Tz k r z' < Complex.normSq (ζ / ((τ ^ 2 : ℝ) : ℂ)) := by
    intro ζ hζ
    rw [Tz_smul, Tz_smul] at hζ
    rw [hns, lt_div_iff₀ h4]; nlinarith
  refine ⟨fun i j => ?_, fun ζ hζ => ?_⟩
  · have hc : ContDiff ℝ ∞ (fun ζ : ℂ => ζ / ((τ ^ 2 : ℝ) : ℂ)) := by
      have : (fun ζ : ℂ => ζ / ((τ ^ 2 : ℝ) : ℂ)) = fun ζ => ((τ ^ 2)⁻¹ : ℝ) • ζ := by
        funext ζ; rw [Complex.real_smul, div_eq_inv_mul]; push_cast; ring
      rw [this]; exact contDiff_const_smul _
    exact (h.1 i j).comp hc.contDiffOn fun ζ hζ => hreg ζ hζ
  · obtain ⟨hu, hv⟩ := h.2 _ (hreg ζ hζ)
    refine ⟨hu, ?_⟩
    unfold secTr
    rw [wbPart_smul, wbPart_smul]
    unfold herm at hv ⊢
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct, hv]
    simp only [Complex.star_def, Complex.conj_ofReal, smul_eq_mul]
    field_simp
    push_cast; ring

end Norm

end Formalism.MainNotions.FrameBoundFromBesselTorus
end
end
end

-- Source module: Formalism.SharpRestriction.CuspSpanNormBounds.IsPtRepTrDat

section

@[expose] public section

open MeasureTheory Matrix Finset

noncomputable section

namespace Formalism.MainNotions.FrameBoundFromBesselTorus

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates

def OneBesselTor (D : D7) (Cgf : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)) (κ₀ κ τ : ℝ),
    0 < κ₀ → 0 < κ → 0 < τ → L.c = cOfDpsi (κ₀ : ℂ) → 0 < L.κN → L.κN ≠ ⊤ → L.ε = epsSH D.R →
    GapAtLeast L.ε L.lam (Cgf * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
      (((3 * (D.R.rS + 1) : ℕ) : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 2 + ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 3)) →
    IsKFinCoefH L.σ f →
    ∃ (f₁ : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)) (C : ℂ), C ≠ 0 ∧ IsKFinCoefH L.σ f₁ ∧
      (∀ (c : Fin D.R.rS → ℂ) (μ : Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ), (∀ a, c a ≠ 0) →
        μᴴ * Hb D.R.k * μ = Hb D.R.k →
        L.J (fun x => f₁ (cj D.R.k D.R.rS κ τ x)) (bigCell D.R.k D.R.rS c μ) =
          C • L.J f (bigCell D.R.k D.R.rS c μ)) ∧
      (∀ (γ : Point ℂ (D.R.rS + 1)) (g : Mx D.R.k D.R.rS) (μR : Measure (Mt D.R.k D.R.rS))
        (ν : Measure (PairSp D.R.k D.R.rS)),
        Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ ≠ 0 → IsPtRep L γ g → IsRelStab L g →
        IsRootMeas L γ g μR → IsOrbQuot L g μR ν →
        OrbInt L (fun x => f₁ (cj D.R.k D.R.rS κ τ x)) g ν = C • OrbInt L f g ν)

section Dat

variable {k r : ℕ} {κ τ : ℝ}

theorem hzTr (L : LocBessel k r) (hτ : 0 < τ) : inWb k r ((τ : ℂ) • L.z) ∧ 0 < Tz k r ((τ : ℂ) • L.z) := by
  obtain ⟨h1, h2⟩ := L.hz
  unfold inWb Tz at *
  refine ⟨fun i hi => by simp [h1 i hi], ?_⟩
  unfold herm at *
  have e : star ((τ : ℂ) • L.z) ⬝ᵥ Hpk k r *ᵥ ((τ : ℂ) • L.z) =
      ((τ : ℂ) * τ) * (star L.z ⬝ᵥ Hpk k r *ᵥ L.z) := by
    rw [star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
    simp only [Complex.star_def, Complex.conj_ofReal]
    ring
  rw [e, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
  have hp : 0 < τ * τ := mul_pos hτ hτ
  nlinarith

theorem hzTr' (L : LocBessel k r) (hτ : 0 < τ) : inWb k r ((τ : ℂ) • L.z') ∧ 0 < Tz k r ((τ : ℂ) • L.z') := by
  obtain ⟨h1, h2⟩ := L.hz'
  unfold inWb Tz at *
  refine ⟨fun i hi => by simp [h1 i hi], ?_⟩
  unfold herm at *
  have e : star ((τ : ℂ) • L.z') ⬝ᵥ Hpk k r *ᵥ ((τ : ℂ) • L.z') =
      ((τ : ℂ) * τ) * (star L.z' ⬝ᵥ Hpk k r *ᵥ L.z') := by
    rw [star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
    simp only [Complex.star_def, Complex.conj_ofReal]
    ring
  rw [e, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
  have hp : 0 < τ * τ := mul_pos hτ hτ
  nlinarith

abbrev trDat (L : LocBessel k r) (κ τ : ℝ) (hκ : 0 < κ) (hτ : 0 < τ) : LocBessel k r :=
  trD L κ τ (L.κN * ENNReal.ofReal (deltaN k r κ τ)) (hzTr L hτ) (hzTr' L hτ)
    (isHCTypeW_cjI hκ hτ L.hz.1 L.hπ) (isHCTypeW_cjI hκ hτ L.hz'.1 L.hπ')
    ⟨isHaarOn_map_cjT hκ hτ L.hz.1 L.hμW.1, by rw [map_cjT_univ]; exact L.hμW.2⟩
    ⟨isHaarOn_map_cjT hκ hτ L.hz'.1 L.hμW'.1, by rw [map_cjT_univ]; exact L.hμW'.2⟩

theorem alphaPt_pos (hκ : 0 < κ) (hτ : 0 < τ) (γ : Point ℂ (r + 1)) : 0 < alphaPt κ τ γ := by
  unfold alphaPt tF
  positivity

theorem isPtRep_trDat (hκ : 0 < κ) (hτ : 0 < τ) (L : LocBessel k r) (γ : Point ℂ (r + 1)) (g : Mx k r) :
    IsPtRep (trDat L κ τ hκ hτ) (ptTr κ τ hκ hτ γ) (cj k r κ τ g) ↔ IsPtRep L γ g := by
  unfold IsPtRep
  apply and_congr (cj_mem_UH_iff hκ hτ g)
  show Zhat k r ((τ : ℂ) • L.z) ((τ : ℂ) • L.z') (cj k r κ τ g) = ptMat (ptTr κ τ hκ hτ γ) ↔
    Zhat k r L.z L.z' g = ptMat γ
  constructor
  · intro h
    ext a b
    have h1 : Zhat k r ((τ : ℂ) • L.z) ((τ : ℂ) • L.z') (cj k r κ τ g) a b = ptMat (ptTr κ τ hκ hτ γ) a b := by
      rw [h]
    rw [Zhat_cj hκ hτ L.hz.1 L.hz'.1, ptMat_ptTr hκ hτ] at h1
    have hne : ((tF r κ τ a * tF r κ τ b : ℝ) : ℂ) ≠ 0 := by
      have hp : 0 < tF r κ τ a * tF r κ τ b := by
        unfold tF
        positivity
      exact_mod_cast hp.ne'
    exact mul_left_cancel₀ hne h1
  · intro h
    ext a b
    rw [Zhat_cj hκ hτ L.hz.1 L.hz'.1, ptMat_ptTr hκ hτ, h]

theorem orbSq_trDat (hκ : 0 < κ) (hτ : 0 < τ) (L : LocBessel k r) (F F₁ : Mx k r → (L.Wq →L[ℂ] L.Wp))
    (γ : Point ℂ (r + 1)) (C : ℂ)
    (hO : ∀ (g : Mx k r) (μR : Measure (Mt k r)) (ν : Measure (PairSp k r)), IsPtRep L γ g → IsRelStab L g →
      IsRootMeas L γ g μR → IsOrbQuot L g μR ν →
      OrbInt L (fun x => F₁ (cj k r κ τ x)) g ν = C • OrbInt L F g ν) :
    orbSq (trDat L κ τ hκ hτ) F₁ (ptTr κ τ hκ hτ γ) =
      ENNReal.ofReal ((alphaPt κ τ γ)⁻¹ ^ 2 * ‖C‖ ^ 2) * orbSq L F γ := by
  have hα := alphaPt_pos hκ hτ γ
  set α := alphaPt κ τ γ with hαdef
  have hpat : rootPat (ptTr κ τ hκ hτ γ) = rootPat γ := rootPat_ptTr hκ hτ γ
  have hrel : ∀ g, IsRelStab (trDat L κ τ hκ hτ) (cj k r κ τ g) ↔ IsRelStab L g := fun g =>
    isRelStab_iff hκ hτ L (trDat L κ τ hκ hτ) L.hz.1 L.hz'.1 rfl rfl rfl g
  have hroot : ∀ g μR, IsRootMeas (trDat L κ τ hκ hτ) (ptTr κ τ hκ hτ γ) (cj k r κ τ g)
      (ENNReal.ofReal α • Measure.map (cjT k r κ τ) μR) ↔ IsRootMeas L γ g μR := fun g μR =>
    IsRootMeas_trD_iff hκ hτ L _ _ _ _ _ _ _ hpat g μR
  have hquot : ∀ g μR ν, IsOrbQuot (trDat L κ τ hκ hτ) (cj k r κ τ g)
      (ENNReal.ofReal α • Measure.map (cjT k r κ τ) μR) ((ENNReal.ofReal α)⁻¹ • Measure.map (phiP k r κ τ) ν) ↔
      IsOrbQuot L g μR ν := fun g μR ν => IsOrbQuot_trD_iff hκ hτ L _ _ _ _ _ _ g μR ν hα
  have key : ∀ g μR ν, IsPtRep L γ g → IsRelStab L g → IsRootMeas L γ g μR → IsOrbQuot L g μR ν →
      ENNReal.ofReal (hsNormSq (OrbInt (trDat L κ τ hκ hτ) F₁ (cj k r κ τ g)
        ((ENNReal.ofReal α)⁻¹ • Measure.map (phiP k r κ τ) ν))) =
      ENNReal.ofReal (α⁻¹ ^ 2 * ‖C‖ ^ 2) * ENNReal.ofReal (hsNormSq (OrbInt L F g ν)) := by
    intro g μR ν h1 h2 h3 h4
    show ENNReal.ofReal (@hsNormSq L.Wp L.Wq _ _ _ _ _ (OrbInt (trDat L κ τ hκ hτ) F₁ (cj k r κ τ g)
      ((ENNReal.ofReal α)⁻¹ • Measure.map (phiP k r κ τ) ν))) = _
    rw [OrbInt_trD hκ hτ L _ _ _ _ _ _ _ F₁ g _ ν, hO g μR ν h1 h2 h3 h4, smul_smul, hsNormSq_smul,
      ENNReal.toReal_inv, ENNReal.toReal_ofReal hα.le, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hα, mul_pow]
  unfold orbSq
  apply le_antisymm
  · refine iSup_le fun g₁ => iSup_le fun μR₁ => iSup_le fun ν₁ => iSup_le fun h => ?_
    obtain ⟨g, rfl⟩ : ∃ g, g₁ = cj k r κ τ g := ⟨cjI k r κ τ g₁, (cj_cjI hκ hτ g₁).symm⟩
    obtain ⟨μR, rfl⟩ : ∃ μR, μR₁ = ENNReal.ofReal α • Measure.map (cjT k r κ τ) μR :=
      ⟨_, (map_cjT_cjIT_smul hκ hτ hα μR₁).symm⟩
    obtain ⟨ν, rfl⟩ : ∃ ν, ν₁ = (ENNReal.ofReal α)⁻¹ • Measure.map (phiP k r κ τ) ν :=
      ⟨_, (use₉ hκ hτ hα ν₁).symm⟩
    obtain ⟨h1, h2, h3, h4⟩ := h
    have h1' := (isPtRep_trDat hκ hτ L γ g).mp h1
    have h2' := (hrel g).mp h2
    have h3' := (hroot g μR).mp h3
    have h4' := (hquot g μR ν).mp h4
    rw [key g μR ν h1' h2' h3' h4']
    gcongr
    exact le_iSup_of_le g (le_iSup_of_le μR (le_iSup_of_le ν (le_iSup_of_le ⟨h1', h2', h3', h4'⟩ le_rfl)))
  · simp_rw [ENNReal.mul_iSup]
    refine iSup_le fun g => iSup_le fun μR => iSup_le fun ν => iSup_le fun h => ?_
    obtain ⟨h1, h2, h3, h4⟩ := h
    rw [← key g μR ν h1 h2 h3 h4]
    exact le_iSup_of_le (cj k r κ τ g) (le_iSup_of_le (ENNReal.ofReal α • Measure.map (cjT k r κ τ) μR)
      (le_iSup_of_le ((ENNReal.ofReal α)⁻¹ • Measure.map (phiP k r κ τ) ν)
        (le_iSup_of_le ⟨(isPtRep_trDat hκ hτ L γ g).mpr h1, (hrel g).mpr h2, (hroot g μR).mpr h3,
          (hquot g μR ν).mpr h4⟩ le_rfl)))

theorem jacBig_eq (r : ℕ) (κ τ : ℝ) : jacBig r κ τ = τ ^ (4 * (r + 1)) * κ ^ (2 * r * (r + 1)) := by
  unfold jacBig tF
  have key : ∀ n : ℕ, 2 * ∑ i ∈ Finset.range n, (n - i) = n * (n + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have h2 : ∑ i ∈ Finset.range n, (n + 1 - i) = ∑ i ∈ Finset.range n, ((n - i) + 1) :=
        Finset.sum_congr rfl fun i hi => by
          have := Finset.mem_range.mp hi
          omega
      rw [h2, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
      have h3 : n + 1 - n = 1 := by omega
      rw [h3]
      nlinarith [ih]
  have hsum : ∑ a : Fin r, 4 * (r - (a : ℕ)) = 2 * r * (r + 1) := by
    rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun i => r - i) r]
    have := key r
    nlinarith [this]
  calc (∏ a : Fin r, (τ * κ ^ (r - (a : ℕ))) ^ 4) * τ ^ 4
      = (∏ a : Fin r, (τ ^ 4 * κ ^ (4 * (r - (a : ℕ))))) * τ ^ 4 := by
        congr 1
        refine Finset.prod_congr rfl fun a _ => ?_
        rw [mul_pow, ← pow_mul, mul_comm (r - (a : ℕ)) 4]
    _ = τ ^ (4 * r) * κ ^ (∑ a : Fin r, 4 * (r - (a : ℕ))) * τ ^ 4 := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul,
          Finset.prod_pow_eq_pow_sum]
    _ = τ ^ (4 * (r + 1)) * κ ^ (2 * r * (r + 1)) := by
        rw [hsum]
        ring

theorem wBig_eq_Wbig (hk : 1 ≤ k) (r : ℕ) (κ τ : ℝ) : wBig k r κ τ = Wbig k r κ τ := by
  unfold wBig Wbig Mdim
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl fun a _ => ?_
    rw [Fin.coe_castSucc, ← pow_mul]
    congr 1
    omega
  · simp only [Fin.val_last, tF, Nat.sub_self, pow_zero, mul_one, Nat.mul_zero, zero_add]
    rw [← pow_mul]

end Dat

end Formalism.MainNotions.FrameBoundFromBesselTorus
end
end
end
