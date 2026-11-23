module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StChartConeLength
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StChartDivisorComponents
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StLelongWeightDiff
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.OfLeaves
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PAdmissibleAE
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PAdmissibleAENrm
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PBallVolume
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.MeasureTheory.Measure.RegularityCompacts
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PEvalSpecFirst
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PMahlerIntegrand
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PSphereMeanFubini
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PSphereMeanLinearBall
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartConeLength
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StChartDehomIdeal
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartZeroSet
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartDivisorComponents
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartSectionNotMem
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PConeRingLaurent
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLelongWeightDiff

-- Source module: GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeFubini

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

noncomputable section

theorem ConeFubini.proof (h1 : BallVolume.Statement) : ConeFubini.Statement := by
  intro n h μ _ F c M hF hy
  obtain ⟨hpos, hfin⟩ := h1 n h
  have : IsFiniteMeasure (volume.restrict (ballH h)) := isFiniteMeasure_restrict.2 hfin.ne
  have hsm : StronglyMeasurable (Function.uncurry F) := hF.stronglyMeasurable

  have hint : Integrable (Function.uncurry F) ((volume.restrict (ballH h)).prod μ) := by
    rw [integrable_prod_iff' hsm.aestronglyMeasurable]
    refine ⟨hy.mono fun y hy => hy.1, ?_⟩
    refine Integrable.of_bound ?_ M ?_
    · exact (hsm.norm.integral_prod_left' (μ := volume.restrict (ballH h))).aestronglyMeasurable
    · filter_upwards [hy] with y hy
      have e : ∀ x, ‖Function.uncurry F (x, y)‖ = |F x y| := fun x => Real.norm_eq_abs _
      simp only [e]
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)]
      exact hy.2.1
  refine ⟨hint.integral_prod_left, ?_⟩
  have hvol : (volume (ballH h)).toReal ≠ 0 := (ENNReal.toReal_pos hpos.ne' hfin.ne).ne'
  have hreal : volume.real (ballH h) = (volume (ballH h)).toReal := rfl

  have hin : ∀ᵐ y ∂μ, ∫ v in ballH h, F v y = c * (volume (ballH h)).toReal := by
    filter_upwards [hy] with y hy
    have e := hy.2.2
    rw [setAverage_eq, hreal, smul_eq_mul] at e
    field_simp at e ⊢
    linarith
  have hswap := integral_integral_swap hint
  rw [setAverage_eq, hreal, smul_eq_mul, hswap, integral_congr_ae hin, integral_const, smul_eq_mul]
  simp only [measureReal_def]
  field_simp
end
end Heights
end Heights₂
end GroundTheory
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PMahlerAverageSplit

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

theorem mahler_specFirst_eq (h3 : EvalSpecFirst.Statement) {n e : ℕ} (h : HermNorm n)
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (v : Fin n → ℂ) :
    mahler h e (specFirst f v) =
      sphereMean h e (fun w => Real.log ‖eval (consGroup v w) f‖) := by
  unfold mahler
  congr 1
  funext w
  rw [h3]

theorem MahlerAverageSplit.proof (h1 : MahlerIntegrand.Statement) (h2 : SphereMeanFubini.Statement)
    (h3 : EvalSpecFirst.Statement) : MahlerAverageSplit.Statement := by
  intro n e δ h f hf hhom
  have hint := h1 n (e + 1) δ h f hf hhom
  obtain ⟨hI, hM⟩ := h2 n e h (fun u => Real.log ‖eval u f‖) hint
  have key : (fun v => mahler h e (specFirst f (nrmv h v))) =
      fun v => sphereMean h e (fun w => Real.log ‖eval (consGroup (nrmv h v) w) f‖) := by
    funext v
    exact mahler_specFirst_eq h3 h f (nrmv h v)
  rw [key]
  exact ⟨hI, hM⟩

end

end GroundTheory.Heights₂.Heights
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartDehomIdeal

section

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomogIdeal mcPts segre)
open GroundTheory.Heights₂.Heights (segreChartIdeal segreChartSet chartLift segre_chartLift chartLift_segre_apply)

theorem ChartDehomIdeal.proof : ChartDehomIdeal.Statement := by
  intro K _ _ ι _ P m σ i hP
  classical
  set Q : Ideal (MvPolynomial (Σ k, ι k) ℂ) := P.map (MvPolynomial.map (Int.castRingHom ℂ)) with hQ
  set J : Ideal (MvPolynomial (Σ k, ι k) ℂ) := Q ⊔ dehomIdeal i with hJ
  set G : Fin m → MvPolynomial (Σ k, ι k) ℂ := fun a => ∏ k, X ⟨k, σ a k⟩ with hG

  have hseg : ∀ f, segreDehom σ i f = dehom i (aeval G f) := by
    intro f
    rw [← AlgHom.comp_apply, comp_aeval]
    rfl

  have hcomap : ((Q.map (dehom i)).radical).comap (dehom i) = J.radical := by
    have hd : (dehom i : MvPolynomial (Σ k, ι k) ℂ →+* DehomRing i) = Ideal.Quotient.mk (dehomIdeal i) := rfl
    rw [← Ideal.comap_coe (dehom i), ← Ideal.map_coe (dehom i), Ideal.comap_radical, hd,
      Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]

  have hval : ∀ (y : (Σ k, ι k) → ℂ) (f : MvPolynomial (Fin m) ℂ),
      aeval (R := ℂ) y (aeval G f) = aeval (R := ℂ) (fun a => segre y (σ a)) f := by
    intro y f
    rw [← AlgHom.comp_apply, comp_aeval]
    congr 2
    funext a
    simp [hG, segre]

  have hzero : ∀ y : (Σ k, ι k) → ℂ, y ∈ zeroLocus ℂ J ↔ y ∈ mcPts P ∧ ∀ k, y ⟨k, i k⟩ = 1 := by
    intro y
    constructor
    · intro hy
      have h1 : ∀ k, y ⟨k, i k⟩ = 1 := fun k => by
        have := hy _ (Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩))
        simpa [sub_eq_zero] using this
      refine ⟨⟨fun k => ⟨i k, by simp [h1 k]⟩, fun f hf => ?_⟩, h1⟩
      have := hy _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf))
      exact this
    · rintro ⟨hy, h1⟩
      have hle : J ≤ RingHom.ker (aeval (R := ℂ) y : MvPolynomial (Σ k, ι k) ℂ →+* ℂ) := by
        refine sup_le ?_ ?_
        · rw [hQ, Ideal.map_le_iff_le_comap]
          intro f hf
          exact hy.2 f hf
        · rw [dehomIdeal, Ideal.span_le]
          rintro _ ⟨k, rfl⟩
          simp [RingHom.mem_ker, h1 k]
      exact fun p hp => hle hp
  ext f
  rw [Ideal.mem_comap, hseg, ← Ideal.mem_comap, hcomap, ← vanishingIdeal_zeroLocus_eq_radical (K := ℂ),
    segreChartIdeal, mem_vanishingIdeal_iff, mem_vanishingIdeal_iff]
  constructor
  · intro hf y hy
    rw [hval]
    obtain ⟨hym, h1⟩ := (hzero y).1 hy
    refine hf _ ⟨y, hym, ?_, rfl⟩
    simp [segre, h1]
  · rintro hf x ⟨z, hz, hzi, rfl⟩
    have hne : ∀ k, z ⟨k, i k⟩ ≠ 0 := fun k h0 => by
      have h := Finset.prod_eq_zero (f := fun k => z ⟨k, i k⟩) (Finset.mem_univ k) h0
      exact one_ne_zero ((show segre z i = 1 from hzi).symm.trans h)
    set y := chartLift σ i (fun a => segre z (σ a)) with hy
    have hyz : y = fun p => (z ⟨p.1, i p.1⟩)⁻¹ * z p := by
      funext p
      rw [hy, chartLift_segre_apply σ i z hzi p.1 p.2, mul_comm]
    have hym : y ∈ mcPts P := by
      rw [hyz]
      exact SegreChartZeroSet.scaleAll_mem P hP (fun k => (z ⟨k, i k⟩)⁻¹) (fun k => inv_ne_zero (hne k)) hz
    have h1 : ∀ k, y ⟨k, i k⟩ = 1 := fun k => by
      rw [hyz]
      exact inv_mul_cancel₀ (hne k)
    have := hf y ((hzero y).2 ⟨hym, h1⟩)
    rwa [hval, hy, segre_chartLift σ i z hzi] at this

end GroundTheory.Heights₂.Heights.Targets
end
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.UniformIntegrabilityProportionalityHolds

section

@[expose] public section

set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.Targets_ChartDivisorComponents : GroundTheory.Heights₂.Heights.Targets.ChartDivisorComponents.Statement :=
  @GroundTheory.Heights₂.Heights.Targets.ChartDivisorComponents.proof GroundTheory.Heights₂.Heights.Targets.ChartSectionNotMem.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.Targets_LelongWeightDiff : GroundTheory.Heights₂.Heights.Targets.LelongWeightDiff.Statement :=
  @GroundTheory.Heights₂.Heights.Targets.LelongWeightDiff.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.ChartMassCompact

theorem GroundTheory.Heights₂.Heights.AutoClose.Targets_ChartConeLength : GroundTheory.Heights₂.Heights.Targets.ChartConeLength.Statement :=
  @GroundTheory.Heights₂.Heights.Targets.ChartConeLength.proof GroundTheory.Heights₂.Heights.Targets.ConeRingLaurent.proof GroundTheory.Heights₂.Heights.Targets.ChartDehomIdeal.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.MahlerAverageSplit : GroundTheory.Heights₂.Heights.MahlerAverageSplit.Statement :=
  @GroundTheory.Heights₂.Heights.MahlerAverageSplit.proof GroundTheory.Heights₂.Heights.MahlerIntegrand.proof GroundTheory.Heights₂.Heights.SphereMeanFubini.proof GroundTheory.Heights₂.Heights.EvalSpecFirst.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.ConeFubini : GroundTheory.Heights₂.Heights.ConeFubini.Statement :=
  @GroundTheory.Heights₂.Heights.ConeFubini.proof GroundTheory.Heights₂.Heights.BallVolume.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.SphereMeanLinearBall : GroundTheory.Heights₂.Heights.SphereMeanLinearBall.Statement :=
  @GroundTheory.Heights₂.Heights.SphereMeanLinearBall.proof GroundTheory.Heights₂.Heights.SphereMeanLinear.full

theorem GroundTheory.Heights₂.Heights.AutoClose.AdmissibleAENrm : GroundTheory.Heights₂.Heights.AdmissibleAENrm.Statement :=
  @GroundTheory.Heights₂.Heights.AdmissibleAENrm.proof GroundTheory.Heights₂.Heights.AdmissibleAE.proof
end
end
