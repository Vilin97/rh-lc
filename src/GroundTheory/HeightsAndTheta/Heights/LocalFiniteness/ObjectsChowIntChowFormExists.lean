module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StChartSectionLength
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SphereMeanVol
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PBallVolume
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.UniformIntegrabilityProportionalityHolds
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StChartConeComponent
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartDivisorComponents
import Mathlib.Tactic.Linter.Style
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StChartConeLength
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LengthLocalizedModuleQuotient
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LocalMultRadical
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PFundCycleBaseChange
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PComplexMinimalPrimesContract
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPrimeComplexRadical
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp

-- Source module: GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PBallAverageLinear

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Measure Matrix

noncomputable section

namespace BallAverageLinear

def matEquiv {n : ℕ} (h : HermNorm n) : (Fin n → ℂ) ≃L[ℝ] (Fin n → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    (LinearEquiv.ofLinearMap (f := (Matrix.mulVecLin h.mat).restrictScalars ℝ)
      (g := (Matrix.mulVecLin h.mat⁻¹).restrictScalars ℝ)
      (LinearMap.ext fun v => by
        simp [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ h.isUnit_det])
      (LinearMap.ext fun v => by
        simp [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h.isUnit_det]))

theorem matEquiv_apply {n : ℕ} (h : HermNorm n) (v : Fin n → ℂ) : matEquiv h v = h.mat *ᵥ v := rfl

theorem ballH_eq_preimage {n : ℕ} (h : HermNorm n) :
    ballH h = matEquiv h ⁻¹' ballH (HermNorm.std n) := by
  ext v
  simp [ballH, HermNorm.norm, HermNorm.std, matEquiv_apply]

end BallAverageLinear

open BallAverageLinear in
theorem BallAverageLinear.proof : BallAverageLinear.Statement := by
  intro n h φ
  set L := matEquiv h
  have hb := ballH_eq_preimage h
  have hpre : ∀ s : Set (Fin n → ℂ), IntegrableOn (fun v => φ (h.mat *ᵥ v)) (L ⁻¹' s) ↔
      IntegrableOn φ s := by
    intro s
    have he : MeasurableEmbedding L := L.toHomeomorph.measurableEmbedding
    have hmap : (map L volume).IsAddHaarMeasure := L.isAddHaarMeasure_map volume
    have h2 : map L (volume : Measure (Fin n → ℂ)) =
        addHaarScalarFactor (map L volume) volume • volume := isAddLeftInvariant_eq_smul _ _
    have hpos := addHaarScalarFactor_pos_of_isAddHaarMeasure (map L (volume : Measure (Fin n → ℂ))) volume
    rw [show (fun v => φ (h.mat *ᵥ v)) = φ ∘ L from rfl, ← he.integrableOn_map_iff, h2,
      show (addHaarScalarFactor (map L volume) volume • (volume : Measure (Fin n → ℂ))) =
        ((addHaarScalarFactor (map L volume) volume : ENNReal) • volume) from rfl,
      IntegrableOn, IntegrableOn, Measure.restrict_smul,
      integrable_smul_measure (by simpa using hpos.ne') ENNReal.coe_ne_top]
  refine ⟨by rw [hb]; exact hpre _, ?_⟩
  rw [hb]
  exact SphereMean.setAverage_comp_linearEquiv volume volume L _ φ

end

end GroundTheory.Heights₂.Heights
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PFsLogAverage

section

@[expose] public section

set_option maxSynthPendingDepth 1

open MeasureTheory Matrix

namespace GroundTheory.Heights₂.Heights

theorem FsLogAverage.proof (h1 : BallAverageLinear.Statement) (h2 : FsLogPointOf.Statement)
    (h3 : SphereMeanLinearBall.Statement) (h4 : BallVolume.Statement) : FsLogAverage.Statement := by
  intro n h y hy
  set y' : Fin n → ℂ := fun i => y i with hy'def
  have hy' : y' ≠ 0 := by
    intro hz
    apply hy
    ext i
    exact congrFun hz i
  set φ : (Fin n → ℂ) → ℝ := fun w => fsLog (HermNorm.std n) (nrmv (HermNorm.std n) w) y' with hφ
  have hrw : (fun v => fsLog h (nrmv h v) (h.pointOf y)) = fun v => φ (h.mat *ᵥ v) := by
    funext v
    exact h2 n h v y
  obtain ⟨hint, hle, hmean⟩ := h3 n y' hy'
  have habs : (fun w => |φ w|) = fun w => -φ w := by
    funext w
    exact abs_of_nonpos (hle w)
  have hmeanAbs : ⨍ v in ballH h, |φ (h.mat *ᵥ v)| = (harmonic (n - 1) : ℝ) / 2 := by
    rw [(h1 n h (fun w => |φ w|)).2, habs]
    change (⨍ w in ballH (HermNorm.std n), (-φ) w) = _
    rw [average_neg, hmean]
    ring
  obtain ⟨_, hfin⟩ := h4 n h
  refine ⟨?_, ?_, ?_⟩
  · rw [hrw]
    exact (h1 n h φ).1.mpr hint
  · simp only [show ∀ v, fsLog h (nrmv h v) (h.pointOf y) = φ (h.mat *ᵥ v) from fun v => h2 n h v y]
    rw [← measure_smul_setAverage _ hfin.ne, hmeanAbs, smul_eq_mul, measureReal_def]
    ring
  · rw [hrw, (h1 n h φ).2]
    exact hmean

end GroundTheory.Heights₂.Heights
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PFsLogPointOf

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

theorem FsLogPointOf.proof : FsLogPointOf.Statement := by
  intro n h v y
  have hdet : IsUnit (h.matᵀ).det := by rw [Matrix.det_transpose]; exact h.isUnit_det
  have hd : h.dualNorm (h.pointOf y) = (HermNorm.std n).dualNorm (fun i => y i) := by
    simp only [HermNorm.dualNorm, HermNorm.pointOf, HermNorm.std, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec, Matrix.transpose_one, inv_one]
  have hn : (HermNorm.std n).norm (h.mat *ᵥ v) = h.norm v := by
    simp only [HermNorm.norm, HermNorm.std, Matrix.one_mulVec]
  have hs : ∑ j, v j * h.pointOf y j = ∑ i, (h.mat *ᵥ v) i * y i := by
    have := Matrix.dotProduct_mulVec v h.matᵀ (fun i => y i)
    rw [Matrix.vecMul_transpose] at this
    simpa [dotProduct, HermNorm.pointOf] using this
  unfold fsLog nrmv
  rw [hd, hn]
  simp only [mul_assoc, ← Finset.mul_sum, hs]

end GroundTheory.Heights₂.Heights
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartConeComponent

section

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiProjPrime)
open GroundTheory.Heights₂.Heights (segreChartComponents mem_segreChartComponents)

theorem ChartConeComponent.proof : ChartConeComponent.Statement := by
  intro K _ _ ι _ W m σ i hW W' hW'
  have hmin := mem_segreChartComponents.1 hW'
  have : W'.IsPrime := hmin.1.1
  let φ : MvPolynomial (Σ k, ι k) ℂ →+* MvPolynomial (Fin m) ℂ := chartSubst σ i
  have : (W'.comap φ).IsPrime := Ideal.comap_isPrime φ W'
  have hle : W.map (MvPolynomial.map (Int.castRingHom ℂ)) ≤ W'.comap φ := by
    rw [Ideal.map_le_iff_le_comap]
    intro f hf
    show φ (MvPolynomial.map (Int.castRingHom ℂ) f) ∈ W'
    have h := ChartDivisorComponents.chartSection_mem hW.2.1 σ i hf
    rw [chartSection_eq_chartSubst] at h
    exact hmin.1.2 h
  obtain ⟨W'', hW'', hW''le⟩ := Ideal.exists_minimalPrimes_le hle
  exact ⟨W'', hW'', Ideal.map_le_iff_le_comap.2 hW''le⟩

end GroundTheory.Heights₂.Heights.Targets
end
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartSectionLength

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing multAt divSuppArith)
open GroundTheory.Heights₂.Heights (localMult localMult_map_of_flat map_eq_maximalIdeal_of_isRadical)

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem localMult_map_intCast_complex {τ : Type} [Fintype τ] (J W : Ideal (MvPolynomial τ ℤ)) [W.IsPrime]
    (W'' : Ideal (MvPolynomial τ ℂ)) (hW'' : W'' ∈ (W.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes) :
    localMult (J.map (MvPolynomial.map (Int.castRingHom ℂ))) W'' = localMult J W := by
  have := HilbertSamuel.mvPolynomial_int_complex_flat τ
  have hAlg := HilbertSamuel.algebraMap_mvPolynomial_int_complex τ
  have : W''.IsPrime := hW''.1.1
  have hc : W''.comap (MvPolynomial.map (Int.castRingHom ℂ)) = W :=
    HilbertSamuel.ComplexMinimalPrimesContract.proof τ W ‹_› W'' hW''
  have : W''.LiesOver W := ⟨by rw [Ideal.under, hAlg, hc]⟩
  have hrad := HilbertSamuel.PrimeComplexRadical.proof τ W ‹_›
  have key := localMult_map_of_flat J W W''
    (by rw [hAlg]; exact map_eq_maximalIdeal_of_isRadical hrad hW'')
  rwa [hAlg] at key

theorem multAt_eq_localMult {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (J W : Ideal (MRing ι))
    [W.IsPrime] : multAt J W = localMult J W := by
  unfold multAt localMult
  rw [dite_eq_left ‹_›, dite_eq_left ‹_›, ObjectsChow.VerticalPartMultiplicity.length_localizedModule_quotient]

theorem ChartSectionLength.proof (hComp : ChartConeComponent.Statement) (hLen : ChartConeLength.Statement) :
    ChartSectionLength.Statement := by
  intro K _ _ ι _ P n m σ i A s hP hs W hW hWh W' hW'
  have hWa := (divSuppArith K ι P (n + 1) A s W hP hs hW).1 hWh
  have : W.IsPrime := hW.1.1.1
  obtain ⟨W'', hW'', hle⟩ := hComp K ι W m σ i hWa.2.1 W' hW'
  rw [hLen K ι P n m σ i A s hP hs W hW hWh W' hW' W'' hW'' hle, multAt_eq_localMult,
    localMult_map_intCast_complex _ W W'' hW'']

end GroundTheory.Heights₂.Heights.Targets
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.ObjectsChowIntChowFormExists

section

@[expose] public section

set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.Targets_ChartSectionLength : GroundTheory.Heights₂.Heights.Targets.ChartSectionLength.Statement :=
  @GroundTheory.Heights₂.Heights.Targets.ChartSectionLength.proof GroundTheory.Heights₂.Heights.Targets.ChartConeComponent.proof GroundTheory.Heights₂.Heights.AutoClose.Targets_ChartConeLength

theorem GroundTheory.Heights₂.Heights.AutoClose.FsLogAverage : GroundTheory.Heights₂.Heights.FsLogAverage.Statement :=
  @GroundTheory.Heights₂.Heights.FsLogAverage.proof GroundTheory.Heights₂.Heights.BallAverageLinear.proof GroundTheory.Heights₂.Heights.FsLogPointOf.proof GroundTheory.Heights₂.Heights.AutoClose.SphereMeanLinearBall GroundTheory.Heights₂.Heights.BallVolume.proof
end
end
