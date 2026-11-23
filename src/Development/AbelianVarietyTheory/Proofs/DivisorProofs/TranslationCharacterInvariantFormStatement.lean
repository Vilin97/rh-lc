module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFamilyPhaseBoundStatement
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
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
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzIntegralSuperpositionStatement
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFourierRepresentation

section

@[expose] public section

open MeasureTheory

namespace GlobalTheory


open Real in
theorem schwartz_eq_fourier_synthesis :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (m : SchwartzMap V ℂ),
    ∃ (d : ℕ) (A : EuclideanSpace ℝ (Fin d) →L[ℝ] V →L[ℝ] ℝ) (h : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ),
    ∀ x, m x = ∫ ξ, h ξ * Complex.exp (Complex.I * (A ξ x : ℂ)) := by
  intro V _ _ _ m
  let e : V ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) := toEuclidean
  let m' : SchwartzMap (EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm m
  let A : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) →L[ℝ] V →L[ℝ] ℝ :=
    (2 * π) • (((ContinuousLinearMap.compL ℝ V _ ℝ).flip (e : V →L[ℝ] _)).comp (innerSL ℝ))
  have hA : ∀ ξ x, A ξ x = 2 * π * inner ℝ ξ (e x) := by
    intro ξ x
    simp [A]
  refine ⟨Module.finrank ℝ V, A, (FourierTransform.fourier m' : SchwartzMap (EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) ℂ), fun x => ?_⟩
  have h1 : m x = m' (e x) := by
    simp [m']
  have h2 := congrArg (fun f : SchwartzMap _ ℂ => f (e x)) (FourierTransform.fourierInv_fourier_eq (F := SchwartzMap (EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) ℂ) m')
  rw [h1, ← h2, SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
  congr 1
  ext ξ
  rw [hA, smul_eq_mul, mul_comm]
  congr 2
  push_cast
  ring

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFourierRepresentationStatement

section

@[expose] public section

open MeasureTheory

theorem _root_.GlobalTheory.T.schwartz_fourier_representation : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (m : SchwartzMap V ℂ),
    ∃ (d : ℕ) (A : EuclideanSpace ℝ (Fin d) →L[ℝ] V →L[ℝ] ℝ) (h : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ),
    ∀ x, m x = ∫ ξ, h ξ * Complex.exp (Complex.I * (A ξ x : ℂ)) := by
  first | exact @GlobalTheory.schwartz_eq_fourier_synthesis | exact GlobalTheory.schwartz_eq_fourier_synthesis | (intros; apply GlobalTheory.schwartz_eq_fourier_synthesis <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzInnerProductContinuous

section

@[expose] public section

open MeasureTheory

namespace GlobalTheory

theorem schwartz_pairing_conj_clm : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (μ : @MeasureTheory.Measure V (borel V)), @MeasureTheory.Measure.IsAddHaarMeasure V _ _ (borel V) μ →
    ∀ (w : SchwartzMap V ℂ), ∃ Λ : SchwartzMap V ℂ →L[ℂ] ℂ, ∀ u : SchwartzMap V ℂ,
      Λ u = @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => u x * starRingEnd ℂ (w x)) := by
  intro V _ _ _ μ hμ w
  letI : MeasurableSpace V := borel V
  haveI : BorelSpace V := ⟨rfl⟩
  haveI : μ.IsAddHaarMeasure := hμ
  have hg : Function.HasTemperateGrowth (fun x => starRingEnd ℂ (w x)) :=
    (Complex.conjCLE.toContinuousLinearMap : ℂ →L[ℝ] ℂ).hasTemperateGrowth.comp w.hasTemperateGrowth
  refine ⟨(SchwartzMap.integralCLM ℂ μ).comp (SchwartzMap.smulLeftCLM ℂ (fun x => starRingEnd ℂ (w x))), ?_⟩
  intro u
  rw [ContinuousLinearMap.comp_apply, SchwartzMap.integralCLM_apply]
  congr 1
  funext x
  rw [SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul, mul_comm]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzInnerProductContinuousStatement

section

@[expose] public section

open MeasureTheory

theorem _root_.GlobalTheory.T.schwartz_inner_product_continuous : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (μ : @MeasureTheory.Measure V (borel V)), @MeasureTheory.Measure.IsAddHaarMeasure V _ _ (borel V) μ →
    ∀ (w : SchwartzMap V ℂ), ∃ Λ : SchwartzMap V ℂ →L[ℂ] ℂ, ∀ u : SchwartzMap V ℂ,
      Λ u = @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => u x * starRingEnd ℂ (w x)) := by
  first | exact @GlobalTheory.schwartz_pairing_conj_clm | exact GlobalTheory.schwartz_pairing_conj_clm | (intros; apply GlobalTheory.schwartz_pairing_conj_clm <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationCharacterInvariantForm

section

@[expose] public section

open MeasureTheory

namespace GlobalTheory.CharMult

theorem multiplier_symm : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (μ : @MeasureTheory.Measure V (borel V)), @MeasureTheory.Measure.IsAddHaarMeasure V _ _ (borel V) μ →
    ∀ (T : SchwartzMap V ℂ →L[ℂ] SchwartzMap V ℂ),
    (∀ (L : V →L[ℝ] ℝ) (f f' g g' : SchwartzMap V ℂ),
      (∀ x, f' x = Complex.exp (Complex.I * (L x : ℂ)) * f x) →
      (∀ x, g' x = Complex.exp (Complex.I * (L x : ℂ)) * g x) →
      @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f' x * starRingEnd ℂ (T g' x)) =
        @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f x * starRingEnd ℂ (T g x))) →
    ∀ (m f f' g g' : SchwartzMap V ℂ), (∀ x, f' x = m x * f x) → (∀ x, g' x = starRingEnd ℂ (m x) * g x) →
      @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f' x * starRingEnd ℂ (T g x)) =
        @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f x * starRingEnd ℂ (T g' x)) := by
  intro V _ _ _ μ hμ T hT m f f' g g' hf' hg'
  letI : MeasurableSpace V := borel V
  haveI : BorelSpace V := ⟨rfl⟩
  obtain ⟨d, A, h, hm⟩ := GlobalTheory.T.schwartz_fourier_representation V m
  obtain ⟨Φf, hΦf, cΦf, bΦf⟩ := GlobalTheory.T.schwartz_family_phase_bound V _ A f
  obtain ⟨Φg, hΦg, cΦg, bΦg⟩ := GlobalTheory.T.schwartz_family_phase_bound V _ (-A) g
  obtain ⟨Λ1, hΛ1⟩ := GlobalTheory.T.schwartz_inner_product_continuous V μ hμ (T g)
  obtain ⟨Λ2, hΛ2⟩ := GlobalTheory.T.schwartz_inner_product_continuous V μ hμ (T f)
  have hint : ∀ (Φ : EuclideanSpace ℝ (Fin d) → SchwartzMap V ℂ), Continuous Φ →
      (∀ k n : ℕ, ∃ C : ℝ, ∀ ξ, SchwartzMap.seminorm ℂ k n (Φ ξ) ≤ C * (1 + ‖ξ‖ ^ n)) →
      ∀ (c : EuclideanSpace ℝ (Fin d) → ℂ), (∀ ξ, ‖c ξ‖ = ‖h ξ‖) →
      ∀ k n : ℕ, Integrable (fun ξ => ‖c ξ‖ * SchwartzMap.seminorm ℂ k n (Φ ξ)) := by
    intro Φ hΦ hb c hc k n
    obtain ⟨C, hC⟩ := hb k n
    have hcont : Continuous (fun ξ => SchwartzMap.seminorm ℂ k n (Φ ξ)) :=
      ((schwartz_withSeminorms ℂ V ℂ).continuous_seminorm (k, n)).comp hΦ
    have i1 : Integrable (fun ξ => ‖h ξ‖) := h.integrable.norm
    have i2 : Integrable (fun ξ => ‖ξ‖ ^ n * ‖h ξ‖) := h.integrable_pow_mul volume n
    refine Integrable.mono' ((i1.add i2).const_mul C) ?_ ?_
    · simp_rw [hc]
      exact (h.continuous.norm.mul hcont).aestronglyMeasurable
    · filter_upwards with ξ
      rw [hc, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (apply_nonneg _ _))]
      calc ‖h ξ‖ * SchwartzMap.seminorm ℂ k n (Φ ξ) ≤ ‖h ξ‖ * (C * (1 + ‖ξ‖ ^ n)) :=
            mul_le_mul_of_nonneg_left (hC ξ) (norm_nonneg _)
        _ = C * (‖h ξ‖ + ‖ξ‖ ^ n * ‖h ξ‖) := by ring

  have hkey : ∀ ξ, Λ1 (T (Φf ξ)) = ∫ x, T f x * starRingEnd ℂ (T (Φg ξ) x) ∂μ := by
    intro ξ
    rw [hΛ1]
    refine hT (A ξ) f (Φf ξ) (Φg ξ) g (hΦf ξ) (fun x => ?_)
    rw [hΦg, ← mul_assoc, ← Complex.exp_add]
    simp [ContinuousLinearMap.neg_apply]
  have lhs : ∫ x, T f' x * starRingEnd ℂ (T g x) ∂μ = ∫ ξ, h ξ * ∫ x, T f x * starRingEnd ℂ (T (Φg ξ) x) ∂μ := by
    rw [← hΛ1]
    have := GlobalTheory.T.schwartz_integral_superposition V (EuclideanSpace ℝ (Fin d)) volume Φf cΦf h h.continuous.aestronglyMeasurable
      (hint Φf cΦf bΦf h (fun _ => rfl)) f' (fun x => by
        rw [hf', hm, ← integral_mul_const]
        congr 1; funext ξ; rw [hΦf]; ring) (Λ1.comp T)
    simp only [ContinuousLinearMap.comp_apply] at this
    rw [this]; simp_rw [hkey]
  have rhs : ∫ x, T f x * starRingEnd ℂ (T g' x) ∂μ = ∫ ξ, h ξ * ∫ x, T f x * starRingEnd ℂ (T (Φg ξ) x) ∂μ := by
    have e1 : ∫ x, T f x * starRingEnd ℂ (T g' x) ∂μ = starRingEnd ℂ (Λ2 (T g')) := by
      rw [hΛ2, ← integral_conj]; congr 1; funext x; simp [mul_comm]
    have := GlobalTheory.T.schwartz_integral_superposition V (EuclideanSpace ℝ (Fin d)) volume Φg cΦg (fun ξ => starRingEnd ℂ (h ξ))
      (Complex.continuous_conj.comp h.continuous).aestronglyMeasurable
      (hint Φg cΦg bΦg _ (fun _ => Complex.norm_conj _)) g' (fun x => by
        rw [hg', hm, ← integral_conj, ← integral_mul_const]
        congr 1; funext ξ; rw [hΦg]
        simp only [map_mul, ContinuousLinearMap.neg_apply, ← Complex.exp_conj]
        simp [Complex.ofReal_neg]; ring) (Λ2.comp T)
    simp only [ContinuousLinearMap.comp_apply] at this
    rw [e1, this, ← integral_conj]
    congr 1; funext ξ
    rw [map_mul, Complex.conj_conj, hΛ2, ← integral_conj]
    congr 2; funext x; simp [mul_comm]
  rw [lhs, rhs]

end GlobalTheory.CharMult
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationCharacterInvariantFormStatement

section

@[expose] public section

open MeasureTheory

theorem _root_.GlobalTheory.T.translation_character_invariant_form : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (μ : @MeasureTheory.Measure V (borel V)), @MeasureTheory.Measure.IsAddHaarMeasure V _ _ (borel V) μ →
    ∀ (T : SchwartzMap V ℂ →L[ℂ] SchwartzMap V ℂ),
    (∀ (L : V →L[ℝ] ℝ) (f f' g g' : SchwartzMap V ℂ),
      (∀ x, f' x = Complex.exp (Complex.I * (L x : ℂ)) * f x) →
      (∀ x, g' x = Complex.exp (Complex.I * (L x : ℂ)) * g x) →
      @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f' x * starRingEnd ℂ (T g' x)) =
        @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f x * starRingEnd ℂ (T g x))) →
    ∀ (m f f' g g' : SchwartzMap V ℂ), (∀ x, f' x = m x * f x) → (∀ x, g' x = starRingEnd ℂ (m x) * g x) →
      @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f' x * starRingEnd ℂ (T g x)) =
        @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f x * starRingEnd ℂ (T g' x)) := by
  first | exact @GlobalTheory.CharMult.multiplier_symm | exact GlobalTheory.CharMult.multiplier_symm | (intros; apply GlobalTheory.CharMult.multiplier_symm <;> assumption)
end
end
