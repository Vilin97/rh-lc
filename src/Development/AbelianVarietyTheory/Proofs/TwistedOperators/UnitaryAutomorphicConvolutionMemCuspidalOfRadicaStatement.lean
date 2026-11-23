module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousSetIntegralConstTermOn
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv
import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralMulEqZeroOfCosetIntegralEqZeroStatement
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemLpLiftL2DiscreteQuotientOnCompact
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SetIntegralNormRmulLe
import Mathlib.Topology.Compactness.Paracompact
import Development.AbelianVarietyTheory.Definitions.Foundations.WittIndexEqZeroIff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstantTermLocallyIntegrable

section

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Cusp GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed

namespace GlobalTheory.ConstantTermL2

theorem main : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (W : Submodule D.host.E V.V) (hW : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.IsIsotropic V W) (F : DividedPowerChartLift V μ), LocallyIntegrable (constTerm (.single hW) (lift (GQ V) F)) μ ∧ (∀ u ∈ NA (.single hW), (fun g => constTerm (.single hW) (lift (GQ V) F) (u * g)) =ᵐ[μ] constTerm (.single hW) (lift (GQ V) F)) ∧ ∀ f : GA D V → ℂ, Continuous f → HasCompactSupport f → ∀ x, constTerm (.single hW) (fun x => ∫ y, f (x⁻¹ * y) * lift (GQ V) F y ∂μ) x = ∫ y, f (x⁻¹ * y) * constTerm (.single hW) (lift (GQ V) F) y ∂μ := by
  intro D V μ _ _ W hW F
  have hc := cocompact_single hW
  have hl := leftInv_lift (Γ := GQ V) F
  have hm : StronglyMeasurable (lift (GQ V) F) := (Lp.stronglyMeasurable F).comp_measurable measurable_mk
  have hi := GlobalTheory.CuspAE.locallyIntegrable_lift (Γ := GQ V) (μ := μ) F
  refine ⟨GlobalTheory.CuspAE.locallyIntegrable_constTermOn hc hl hm hi, fun u hu => .of_forall fun g =>
    hc.constTermOn_mul_left hl hu g, fun f hf hs x => ?_⟩
  have e1 : (fun x => ∫ y, f (x⁻¹ * y) * lift (GQ V) F y ∂μ) = convR μ f (lift (GQ V) F) :=
    funext fun x => (convR_eq (μ := μ) f _ x).symm
  rw [e1, ← convR_eq (μ := μ)]
  exact GlobalTheory.CuspAE.constTermOn_convR hc hl hm hi hf hs x

end GlobalTheory.ConstantTermL2
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstantTermLocallyIntegrableStatement

section

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Cusp GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed

theorem _root_.GlobalTheory.T.constant_term_locally_integrable : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (W : Submodule D.host.E V.V) (hW : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.IsIsotropic V W) (F : DividedPowerChartLift V μ), LocallyIntegrable (constTerm (.single hW) (lift (GQ V) F)) μ ∧ (∀ u ∈ NA (.single hW), (fun g => constTerm (.single hW) (lift (GQ V) F) (u * g)) =ᵐ[μ] constTerm (.single hW) (lift (GQ V) F)) ∧ ∀ f : GA D V → ℂ, Continuous f → HasCompactSupport f → ∀ x, constTerm (.single hW) (fun x => ∫ y, f (x⁻¹ * y) * lift (GQ V) F y ∂μ) x = ∫ y, f (x⁻¹ * y) * constTerm (.single hW) (lift (GQ V) F) y ∂μ := by
  first | exact @GlobalTheory.ConstantTermL2.main | exact GlobalTheory.ConstantTermL2.main | (intros; apply GlobalTheory.ConstantTermL2.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RightRegularOperatorRepresentedContinuous

section

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Cusp GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed
open scoped Pointwise

namespace GlobalTheory.RopRep

theorem rop_rep : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], ∀ f ∈ CcGA V, ∀ F : DividedPowerChartLift V μ, (∀ x, Integrable (fun y => f (x⁻¹ * y) * lift (GQ V) F y) μ) ∧ Continuous (fun x => ∫ y, f (x⁻¹ * y) * lift (GQ V) F y ∂μ) ∧ LeftInv (GQ V) (fun x => ∫ y, f (x⁻¹ * y) * lift (GQ V) F y ∂μ) ∧ lift (GQ V) (RopG V μ f F) =ᵐ[μ] fun x => ∫ y, f (x⁻¹ * y) * lift (GQ V) F y ∂μ := by
  intro D V μ _ _ f hf F
  obtain ⟨hfc, hfs⟩ := GlobalTheory.Orb.continuous_of_mem_ccAd hf
  have hloc : LocallyIntegrable (lift (GQ V) F) μ :=
    (locallyIntegrable_iff).2 fun C hC => (GlobalTheory.AutomorphicL2Local.memLp_restrict_compact _ (GQ V) μ F C hC).2
  have hint : ∀ x, Integrable (fun y => f (x⁻¹ * y) * lift (GQ V) F y) μ := fun x =>
    hloc.integrable_smul_left_of_hasCompactSupport (hfc.comp (continuous_const_mul _))
      (hfs.comp_homeomorph (Homeomorph.mulLeft x⁻¹))
  have hconv : (fun x => ∫ y, f (x⁻¹ * y) * lift (GQ V) F y ∂μ) = convR μ f (lift (GQ V) F) :=
    funext fun x => (convR_eq f _ x).symm
  refine ⟨hint, ?_, ?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun x₀ => ?_
    obtain ⟨K, hK, hKx⟩ := exists_compact_mem_nhds x₀
    obtain ⟨M, hM⟩ := hfc.bounded_above_of_compact_support hfs
    have hC : IsCompact (K * tsupport f) := hK.mul hfs
    have hCi : IntegrableOn (lift (GQ V) F) (K * tsupport f) μ :=
      (GlobalTheory.AutomorphicL2Local.memLp_restrict_compact _ (GQ V) μ F _ hC).2
    refine continuousAt_of_dominated
      (bound := (K * tsupport f).indicator fun y => M * ‖lift (GQ V) F y‖)
      (.of_forall fun x => (hint x).1) ?_ ?_ (.of_forall fun y => ?_)
    · filter_upwards [hKx] with x hx
      refine .of_forall fun y => ?_
      by_cases hy : f (x⁻¹ * y) = 0
      · rw [hy, zero_mul, norm_zero]
        exact Set.indicator_nonneg (fun _ _ => mul_nonneg ((norm_nonneg _).trans (hM 1)) (norm_nonneg _)) _
      · have hmem : y ∈ K * tsupport f :=
          ⟨x, hx, x⁻¹ * y, subset_tsupport f hy, by simp⟩
        rw [Set.indicator_of_mem hmem, norm_mul]
        exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
    · exact (integrable_indicator_iff hC.isClosed.measurableSet).2 (hCi.norm.const_mul M)
    · exact ((hfc.comp (continuous_inv.mul continuous_const)).mul continuous_const).continuousAt
  · rw [hconv]
    exact (leftInv_lift _).convR f
  · rw [hconv]
    exact (GlobalTheory.AutomorphicL2Pointwise.lift_Rop_eq_convR _ (GQ V) μ f
      (hfc.integrable_of_hasCompactSupport hfs) F).2

end GlobalTheory.RopRep
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RightRegularOperatorRepresentedContinuousStatement

section

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Cusp GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed

theorem _root_.GlobalTheory.T.rightRegularOperator_represented_continuous : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], ∀ f ∈ CcGA V, ∀ F : DividedPowerChartLift V μ, (∀ x, Integrable (fun y => f (x⁻¹ * y) * lift (GQ V) F y) μ) ∧ Continuous (fun x => ∫ y, f (x⁻¹ * y) * lift (GQ V) F y ∂μ) ∧ LeftInv (GQ V) (fun x => ∫ y, f (x⁻¹ * y) * lift (GQ V) F y ∂μ) ∧ lift (GQ V) (RopG V μ f F) =ᵐ[μ] fun x => ∫ y, f (x⁻¹ * y) * lift (GQ V) F y ∂μ := by
  first | exact @GlobalTheory.RopRep.rop_rep | exact GlobalTheory.RopRep.rop_rep | (intros; apply GlobalTheory.RopRep.rop_rep <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAutomorphicConvolutionMemCuspidalOfRadica

section

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Cusp GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed

namespace GlobalTheory.RopCusp

theorem ropG_mem_L2cusp : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant],
    ∀ f ∈ CcGA V, RadicalIntegralsVanish V f → ∀ F : DividedPowerChartLift V μ, RopG V μ f F ∈ L2cusp V μ := by
  intro D V μ _ _ f hf hR F
  obtain ⟨hfc, hfs⟩ := GlobalTheory.Orb.continuous_of_mem_ccAd hf
  obtain ⟨-, hc, hl, he⟩ := GlobalTheory.T.rightRegularOperator_represented_continuous D V μ f hf F
  refine mem_L2cusp_of_ae_eq ⟨hc, hl, (isCuspFun_iff hl).2 fun W hW => funext fun x => ?_⟩ he
  obtain ⟨hw1, hw2, hw3⟩ := GlobalTheory.T.constant_term_locally_integrable D V μ W hW F
  rw [hw3 f hfc hfs x, Pi.zero_apply]
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
  have hcl : IsClosed ((NA (.single hW) : Subgroup (GA D V)) : Set (GA D V)) :=
    IsoFlag.isClosed_unip (IsoFlag.single hW) D.sp.cm _
  exact GlobalTheory.T.integral_mul_eq_zero_of_coset_integral_eq_zero_alt (GA D V) (NA (.single hW)) hcl (Measure.haar) μ (fun y => f (x⁻¹ * y)) _
    (hfc.comp (continuous_const_mul x⁻¹)) (hfs.comp_homeomorph (Homeomorph.mulLeft x⁻¹)) hw1 hw2
    fun g => by simpa only [mul_assoc] using hR _ (IsoFlag.proper_single hW) Measure.haar inferInstance x⁻¹ g

end GlobalTheory.RopCusp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAutomorphicConvolutionMemCuspidalOfRadicaStatement

section

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Cusp GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed

theorem _root_.GlobalTheory.T.unitaryAutomorphicConvolution_mem_cuspidal_of_radical_zero : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], ∀ f ∈ CcGA V, RadicalIntegralsVanish V f → ∀ F : DividedPowerChartLift V μ, RopG V μ f F ∈ L2cusp V μ := by
  first | exact @GlobalTheory.RopCusp.ropG_mem_L2cusp | exact GlobalTheory.RopCusp.ropG_mem_L2cusp | (intros; apply GlobalTheory.RopCusp.ropG_mem_L2cusp <;> assumption)
end
end
