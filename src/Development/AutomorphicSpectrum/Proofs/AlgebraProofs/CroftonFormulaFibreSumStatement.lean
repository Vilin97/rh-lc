module

public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsScaleStable
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ConeBall
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AeFibrePointsCardEqDegreeStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.BallAverageFibreCountStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HausdorffConeBallMeasure
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsSigmaCompactConeInter
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Assembly
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowDegreePos
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.RandomSetSumExpectationStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MeasurableFibreCountOverStatement

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HausdorffConeBallMeasureStatement

section

@[expose] public section

set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal


theorem _root_.GlobalTheory.T.hausdorff_cone_ball_measure : ∀ n m : ℕ, 0 < m → m ≤ n → ∃ K : ℝ≥0∞, 0 < K ∧ K < ⊤ ∧
  ∀ (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)), IsProjPrime J → (∀ᵐ π : Fin m → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w ≠ ⊤) →
  ∀ A : Set (EuclideanSpace ℂ (Fin n)), MeasurableSet A → (∀ y ∈ A, ∀ t : ℝ, 0 < t → t • y ∈ A) →
    (Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h J ∩ A} < ⊤ →
    ∫⁻ π : Fin m → Fin n → ℂ, matGauss π * ∫⁻ w in (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1), cntOver (coneSet h J ∩ A) π w =
      K * (Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h J ∩ A} := by
  first | exact @GlobalTheory.CompanionTheory.Relay.hausdorff_cone_ball_measure | exact GlobalTheory.CompanionTheory.Relay.hausdorff_cone_ball_measure | (intros; apply GlobalTheory.CompanionTheory.Relay.hausdorff_cone_ball_measure <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CroftonFormulaOpenCone

section

@[expose] public section

set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton

theorem setCrofton : ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
  (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ), IsProjPrime W → IsChowForm W (e + 1) f → IsMultiHomog δ f →
  ∀ A : Set (EuclideanSpace ℂ (Fin n)), IsOpen A → IsScaleStable A →
    planeMass n e * ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π *
        cntOver (coneSet h W ∩ A) π (firstCoordVec (e + 1)) =
      gaussM (e + 1) n Set.univ *
        (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h W ∩ A} := by
  intro n e δ h W f hW hf hδ A hA hAs
  have hle : e + 1 ≤ n := chowGroups_le hW hf hδ
  have hδpos : 1 ≤ δ := ChowDegreePos.proof n (e + 1) δ W f (Nat.succ_pos e) hW hf hδ
  have hfib := ConeFibreDegree.full n e δ h W f hW hf hδ
  have hfin : ∀ᵐ π : Fin (e + 1) → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin (e + 1)),
      fibreCount h W π w ≠ ⊤ := by
    filter_upwards [hfib] with π hπ
    filter_upwards [hπ] with w hw
    rw [hw]
    exact ENat.natCast_ne_top δ
  obtain ⟨K, hK0, hKtop, hK⟩ := GlobalTheory.T.hausdorff_cone_ball_measure n (e + 1) (Nat.succ_pos e) hle
  have hball : Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (coneBall h W) < ⊤ :=
    ConeBallFinite.full n e h W f hW hf
  have hmass : ∀ B : Set (EuclideanSpace ℂ (Fin n)),
      Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
        {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h W ∩ B} < ⊤ := fun B =>
    lt_of_le_of_lt (measure_mono (show _ ⊆ coneBall h W from fun y hy => And.intro hy.1 hy.2.1)) hball

  have key : ∀ B : Set (EuclideanSpace ℂ (Fin n)), IsOpen B → IsScaleStable B →
      volume (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1) *
        ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π *
          cntOver (coneSet h W ∩ B) π (firstCoordVec (e + 1)) =
      K * (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ))
        {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h W ∩ B} := by
    intro B hB hBs
    have h1 := hK h W hW hfin B hB.measurableSet
      (fun y hy t ht => by
        have := hBs y hy (t : ℂ) (by exact_mod_cast ht.ne')
        simpa using this) (hmass B)
    have h2 := GlobalTheory.T.ball_average_fibre_count n e (coneSet h W ∩ B)
      ((isScaleStable_coneSet h hW).inter hBs) (isSigmaCompact_cone_inter h W hB) id measurable_id
    simp only [id] at h2
    rw [← h2, h1]
  have hΓ : gaussM (e + 1) n Set.univ = ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π := by
    rw [gaussM, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hcnt : ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π *
      cntOver (coneSet h W ∩ Set.univ) π (firstCoordVec (e + 1)) =
      gaussM (e + 1) n Set.univ * (δ : ℝ≥0∞) := by
    rw [hΓ, ← lintegral_mul_const' _ _ (ENNReal.natCast_ne_top δ)]
    refine lintegral_congr_ae ?_
    filter_upwards [GlobalTheory.T.ae_fibre_points_card_eq_degree n e δ h W f hW hf hδ] with π hπ
    have : cntOver (coneSet h W ∩ Set.univ) π (firstCoordVec (e + 1)) = (δ : ℝ≥0∞) := by
      rw [Set.inter_univ, cntOver]
      have : (ptsOver (coneSet h W) π (firstCoordVec (e + 1))).encard = δ := hπ
      rw [this]
      simp
    rw [this]
  have hcb : {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h W ∩ Set.univ} = coneBall h W := by
    ext y
    simp [coneBall, coneSet]
  have hmf : Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (coneBall h W) =
      (δ : ℝ≥0∞) * planeMass n e :=
    ConeMassOfFibre.full n (e + 1) δ h W hW hfib
  have hV0 : volume (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1) ≠ 0 :=
    (Metric.measure_ball_pos _ _ one_pos).ne'
  have hVtop : volume (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1) ≠ ⊤ :=
    measure_ball_lt_top.ne
  have hδ0 : (δ : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : δ ≠ 0)
  have hδtop : (δ : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top δ

  have hVΓ : volume (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1) * gaussM (e + 1) n Set.univ =
      K * planeMass n e := by
    have h0 := key Set.univ isOpen_univ (fun _ _ _ _ => Set.mem_univ _)
    rw [hcnt, hcb, hmf] at h0
    refine (ENNReal.mul_left_inj hδ0 hδtop).1 ?_
    rw [mul_assoc, h0]
    ring
  have hA1 := key A hA hAs
  refine (ENNReal.mul_right_inj hV0 hVtop).1 ?_
  calc volume (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1) * (planeMass n e * ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π *
        cntOver (coneSet h W ∩ A) π (firstCoordVec (e + 1)))
      = planeMass n e * (volume (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1) * ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π *
        cntOver (coneSet h W ∩ A) π (firstCoordVec (e + 1))) := by ring
    _ = planeMass n e * (K * (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ))
        {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h W ∩ A}) := by rw [hA1]
    _ = (K * planeMass n e) * (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ))
        {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h W ∩ A} := by ring
    _ = _ := by rw [← hVΓ]; ring

end GlobalTheory.CompanionTheory.Ar.Short.Crofton
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CroftonFormulaOpenConeStatement

section

@[expose] public section

set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal


theorem _root_.GlobalTheory.T.crofton_formula_open_cone : ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
  (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ), IsProjPrime W → IsChowForm W (e + 1) f → IsMultiHomog δ f →
  ∀ A : Set (EuclideanSpace ℂ (Fin n)), IsOpen A → IsScaleStable A →
    planeMass n e * ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π *
        cntOver (coneSet h W ∩ A) π (firstCoordVec (e + 1)) =
      gaussM (e + 1) n Set.univ *
        (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h W ∩ A} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Short.Crofton.setCrofton | exact GlobalTheory.CompanionTheory.Ar.Short.Crofton.setCrofton | (intros; apply GlobalTheory.CompanionTheory.Ar.Short.Crofton.setCrofton <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.CommonZeroEvaluation.CroftonFormulaFibreSum

section

@[expose] public section

set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

namespace ModelDimension.FnCrofton

theorem measurable_matrix_gaussian (m n : ℕ) :
    Measurable (matGauss : (Fin m → Fin n → ℂ) → ℝ≥0∞) := by
  unfold matGauss
  fun_prop

theorem measurable_cntOver_first {n e : ℕ} {S : Set (EuclideanSpace ℂ (Fin n))} (hS : IsSigmaCompact S) :
    Measurable fun π : Fin (e + 1) → Fin n → ℂ => cntOver S π (firstCoordVec (e + 1)) := by
  have H := GlobalTheory.T.measurable_fibre_count_over n (e + 1) S hS
  have H2 := H.comp (measurable_id.prodMk (measurable_const (a := firstCoordVec (e + 1))))
  exact H2

theorem encard_fibrePts_inter {n e : ℕ} (S A : Set (EuclideanSpace ℂ (Fin n))) (π : Fin (e + 1) → Fin n → ℂ) :
    (((fibrePts S π ∩ A).encard : ℕ∞) : ℝ≥0∞) = cntOver (S ∩ A) π (firstCoordVec (e + 1)) := by
  unfold cntOver
  congr 2
  ext y
  simp only [fibrePts, ptsOver, Set.mem_inter_iff, Set.mem_setOf_eq]
  tauto

end ModelDimension.FnCrofton
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CroftonFormulaFibreSum

section

@[expose] public section

set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal


theorem _root_.GlobalTheory.CompanionTheory.Relay.crofton_formula_fibre_sum : ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
  (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ), IsProjPrime W → IsChowForm W (e + 1) f → IsMultiHomog δ f →
  ∀ φ : EuclideanSpace ℂ (Fin n) → ℝ≥0∞, Measurable φ →
    (∀ s : ℝ≥0∞, IsOpen {y | s < φ y} ∧ IsScaleStable {y | s < φ y}) →
    Measurable (fun π : Fin (e + 1) → Fin n → ℂ => ∑' y : fibrePts (coneSet h W) π, φ y) ∧
      planeMass n e * ∫⁻ π, ∑' y : fibrePts (coneSet h W) π, φ y ∂(gaussM (e + 1) n) =
        gaussM (e + 1) n Set.univ * ∫⁻ y in coneBall h W, φ y ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) := by
  intro n e δ h W f hW hf hδ φ hφ hlev
  have hcnt : ∀ s : ℝ≥0∞, Measurable fun π : Fin (e + 1) → Fin n → ℂ =>
      cntOver (coneSet h W ∩ {y | s < φ y}) π (firstCoordVec (e + 1)) := fun s =>
    ModelDimension.FnCrofton.measurable_cntOver_first (isSigmaCompact_cone_inter h W (hlev s).1)
  obtain ⟨hm, hi⟩ := GlobalTheory.T.random_set_sum_expectation (planeMass n e • gaussM (e + 1) n)
    ((Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)).restrict (coneBall h W))
    (fun π => fibrePts (coneSet h W) π) φ (gaussM (e + 1) n Set.univ) hφ
    (fun s => by
      simp only [ModelDimension.FnCrofton.encard_fibrePts_inter]
      exact hcnt s)
    (fun s => by
      have hA := (hlev s).1
      have T := GlobalTheory.T.crofton_formula_open_cone n e δ h W f hW hf hδ {y | s < φ y} hA (hlev s).2
      simp only [ModelDimension.FnCrofton.encard_fibrePts_inter]
      rw [lintegral_smul_measure, smul_eq_mul, Measure.restrict_apply hA.measurableSet, gaussM,
        lintegral_withDensity_eq_lintegral_mul _ (ModelDimension.FnCrofton.measurable_matrix_gaussian _ _) (hcnt s)]
      have hset : {y | s < φ y} ∩ coneBall h W =
          {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h W ∩ {y | s < φ y}} := by
        ext y
        constructor
        · rintro ⟨h1, h2, h3⟩
          exact ⟨h2, h3, h1⟩
        · rintro ⟨h1, h2, h3⟩
          exact ⟨h3, h1, h2⟩
      rw [hset]
      simpa only [Pi.mul_apply, gaussM] using T)
  refine ⟨hm, ?_⟩
  rw [lintegral_smul_measure, smul_eq_mul] at hi
  exact hi
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CroftonFormulaFibreSumStatement

section

@[expose] public section

set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal


theorem _root_.GlobalTheory.T.crofton_formula_fibre_sum : ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
  (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ), IsProjPrime W → IsChowForm W (e + 1) f → IsMultiHomog δ f →
  ∀ φ : EuclideanSpace ℂ (Fin n) → ℝ≥0∞, Measurable φ →
    (∀ s : ℝ≥0∞, IsOpen {y | s < φ y} ∧ IsScaleStable {y | s < φ y}) →
    Measurable (fun π : Fin (e + 1) → Fin n → ℂ => ∑' y : fibrePts (coneSet h W) π, φ y) ∧
      planeMass n e * ∫⁻ π, ∑' y : fibrePts (coneSet h W) π, φ y ∂(gaussM (e + 1) n) =
        gaussM (e + 1) n Set.univ * ∫⁻ y in coneBall h W, φ y ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.crofton_formula_fibre_sum | exact GlobalTheory.CompanionTheory.Relay.crofton_formula_fibre_sum | (intros; apply GlobalTheory.CompanionTheory.Relay.crofton_formula_fibre_sum <;> assumption)
end
end
