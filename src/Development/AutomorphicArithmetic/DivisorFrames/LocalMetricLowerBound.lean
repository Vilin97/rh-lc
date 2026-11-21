module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WirtConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshBasic
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAlgAtlasAtlasOf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousAndSmul
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenMetricOnSet
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.DifferentiableAtChart
public import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernIntegralEqDegree
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformizedFamilyChartIndex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodFamilyChartDomain
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramedComplexPointOfEigenFrameOffBoundaryStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramSmoothOfHolomorphicFrames
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsExponentialModelFiberOfUniformisationExp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpCoordinatesTangentFieldHolomorphicPeriodMapStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPoint
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousOnFrameDirectionsInverse
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosDefUniformBoundsNearPointStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalEquationComplexPoints
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsHolomorphicLieFrame
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivLift
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstantPeriodMarkingUniversalCover
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrPtPtFOfEigFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentialKernelsIsHolomorphicLatticeFamily
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackAnalytic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PunctPolydiscUniversalCoverOpenConvexExpAnalytic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermFormPeriodsAlternatingNondegRankEqTwoMul
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLagrangianDualPairInCoisotropic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicDualFamilyLinearIndependentRankEqTwoMul
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetNeZeroOfRealIndependentIsotropicHermitian
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannRelationsPeriodMatrixHermitian
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodMatrixPolynomialGrowthPuncturedPolydisc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialGrowthUpperHalfLog

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open CategoryTheory AlgebraicGeometry GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo
open GlobalTheory.MatDeriv GlobalTheory.GradedNorm Matrix
open scoped ComplexOrder
open GlobalTheory.ShFam.Hor GlobalTheory.HermFrame GlobalTheory.Toroidal

private theorem norm_mulVec_le_of_entry {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ i k, ‖M i k‖ ≤ b) (v : Fin m → ℂ) : ‖M *ᵥ v‖ ≤ m * b * ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  calc ‖(M *ᵥ v) i‖ = ‖∑ k, M i k * v k‖ := rfl
    _ ≤ ∑ k, ‖M i k * v k‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin m, b * ‖v‖ := Finset.sum_le_sum fun k _ => by
        rw [norm_mul]
        exact mul_le_mul (h i k) (norm_le_pi_norm v k) (norm_nonneg _) hb
    _ = m * b * ‖v‖ := by simp [mul_assoc]

private theorem local_bounds {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ}
    (H : E → Matrix (Fin m) (Fin m) ℂ) (w₀ : E) (h1 : ∀ a b, ContDiffAt ℝ 1 (fun w => H w a b) w₀)
    (hp : (H w₀).PosDef) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ᶠ w in nhds w₀, (∀ a b, DifferentiableAt ℝ (fun w => H w a b) w) ∧
      ∀ v : Fin m → ℂ, c * ‖v‖ ^ 2 ≤ (star v ⬝ᵥ H w *ᵥ v).re ∧ (star v ⬝ᵥ H w *ᵥ v).re ≤ C * ‖v‖ ^ 2 ∧
        ∀ ξ : E, ‖((H w)⁻¹ * wirt H w ξ) *ᵥ v‖ ≤ C * ‖ξ‖ * ‖v‖ := by
  have hc : ContinuousAt H w₀ := continuousAt_pi.2 fun a => continuousAt_pi.2 fun b => (h1 a b).continuousAt
  obtain ⟨c, C, hc0, hC0, hq⟩ := GlobalTheory.T.posDef_uniform_bounds_near_point E (Fin m) H w₀ hc hp
  have hu : IsUnit (H w₀).det := (isUnit_iff_isUnit_det _).1 hp.isUnit
  have hinv : ContinuousAt (fun w => (H w)⁻¹) w₀ := by
    refine ContinuousAt.comp (f := H) (g := fun A : Matrix (Fin m) (Fin m) ℂ => A⁻¹) ?_ hc
    refine continuousAt_matrix_inv _ ?_
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hu.ne_zero
  let f : E → (Fin m → Fin m → ℂ × (E →L[ℝ] ℂ)) := fun z i k =>
    ((H z)⁻¹ i k, fderiv ℝ (fun x => H x i k) z)
  have hf : ContinuousAt f w₀ := continuousAt_pi.2 fun i => continuousAt_pi.2 fun k =>
    (continuousAt_pi.1 (continuousAt_pi.1 hinv i) k).prodMk
      ((h1 i k).fderiv_right (m := 0) (by norm_num)).continuousAt
  set B := ‖f w₀‖ + 1 with hBdef
  have hB : 0 ≤ B := by positivity
  refine ⟨c, max C (m * B * (m * B)), hc0, le_max_of_le_left hC0, ?_⟩
  filter_upwards [hf.norm.eventually_lt continuousAt_const (lt_add_one ‖f w₀‖), hq,
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun k => (h1 i k).eventually (by simp)] with z hz hqz ha
  have hik : ∀ i k, ‖f z i k‖ ≤ B := fun i k =>
    (norm_le_pi_norm (f z i) k).trans ((norm_le_pi_norm (f z) i).trans hz.le)
  refine ⟨fun a b => (ha a b).differentiableAt (by norm_num), fun v => ⟨(hqz v).1,
    (hqz v).2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)), fun ξ => ?_⟩⟩
  have hd : ∀ (η : E) i k, ‖dMat H z η i k‖ ≤ B * ‖η‖ := fun η i k =>
    (fderiv ℝ (fun x => H x i k) z).le_of_opNorm_le ((norm_snd_le (f z i k)).trans (hik i k)) η
  have hw : ∀ i k, ‖wirt H z ξ i k‖ ≤ B * ‖ξ‖ := fun i k => by
    have e : wirt H z ξ i k = (1 / 2 : ℂ) * (dMat H z ξ i k - Complex.I * dMat H z (Complex.I • ξ) i k) := rfl
    have a1 := hd ξ i k
    have a2 := hd (Complex.I • ξ) i k
    rw [norm_smul, Complex.norm_I, one_mul] at a2
    have a3 := norm_sub_le (dMat H z ξ i k) (Complex.I * dMat H z (Complex.I • ξ) i k)
    rw [norm_mul, Complex.norm_I, one_mul] at a3
    rw [e, norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by simp]
    linarith
  rw [← mulVec_mulVec]
  have b1 := norm_mulVec_le_of_entry (H z)⁻¹ hB (fun i k => (norm_fst_le (f z i k)).trans (hik i k)) (wirt H z ξ *ᵥ v)
  have b2 := norm_mulVec_le_of_entry (wirt H z ξ) (by positivity) hw v
  calc _ ≤ m * B * (m * (B * ‖ξ‖) * ‖v‖) := b1.trans (mul_le_mul_of_nonneg_left b2 (by positivity))
    _ = m * B * (m * B) * ‖ξ‖ * ‖v‖ := by ring
    _ ≤ _ := by gcongr; exact le_max_right _ _
