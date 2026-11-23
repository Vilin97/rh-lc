module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StParamChartInt
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceBranchInt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BranchProperAtPointHoldsStatement
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PChartIntCountAdd
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PParamChartInt
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StParamCritNull
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.HolomorphicZerosNotIsolated
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFibreBound
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PInjectiveHolomorphicInverse
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRankDeficientFibreInfinite
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.NullZero
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StParamDensIntegrable
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.OsgoodSeparate
public import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.CompletelyRegular
public import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StParamOffRegularZero
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.RingTheory.Complex
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Mathlib.RingTheory.Norm.Transitivity
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PParamPieceInt
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegularInjectivePieces
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceBranchInt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase

-- Source module: GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PParamCritNull

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Metric Matrix ComplexSets

theorem ParamCritNull.proof : ParamCritNull.Statement := by
  intro n d W A σ r N hW hdim hA hσ hinj hN hZ
  have hg : DifferentiableOn ℂ (fun v => A *ᵥ σ v) (ball (0 : Fin d → ℂ) r) := by
    have hL : Differentiable ℂ (fun x : Fin n → ℂ => A *ᵥ x) :=
      (LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)).differentiable
    exact hL.comp_differentiableOn hσ
  set Ω : Set (Fin d → ℂ) := ball (0 : Fin d → ℂ) r ∩ σ ⁻¹' N with hΩdef
  have hΩ : IsOpen Ω := hσ.continuousOn.isOpen_inter_preimage isOpen_ball hN
  rcases Set.eq_empty_or_nonempty Ω with hemp | hne
  · have hsub : {w | w ∈ ball (0 : Fin d → ℂ) r ∧ σ w ∈ N ∧
        LinearMap.det (fderiv ℂ (fun v => A *ᵥ σ v) w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) = 0} ⊆ Ω :=
      fun w hw => ⟨hw.1, hw.2.1⟩
    rw [hemp] at hsub
    rw [Set.subset_empty_iff.mp hsub, measure_empty]

  have hsome : ∃ w ∈ ball (0 : Fin d → ℂ) r,
      LinearMap.det (fderiv ℂ (fun v => A *ᵥ σ v) w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hrank : ∀ v ∈ Ω, ¬ Function.Injective (fderiv ℂ (fun v => A *ᵥ σ v) v) := by
      intro v hv hinjv
      have h0 := hcon v hv.1
      rw [LinearMap.det_eq_zero_iff_ker_ne_bot] at h0
      exact h0 (LinearMap.ker_eq_bot.mpr hinjv)
    obtain ⟨y, hy⟩ := IndefiniteRowSideFullHecke.ComplexSets.RankDeficientFibreInfinite.proof d d Ω (fun v => A *ᵥ σ v) hΩ hne
      (hg.mono Set.inter_subset_left) hrank
    have himg : (σ '' {t | t ∈ Ω ∧ A *ᵥ σ t = y}).Infinite :=
      hy.image (hinj.mono fun t ht => ht.1.1)
    have hfin := (ComplexSets.FibreBound.proof n d W A hW hdim hA y).2.1
    refine himg (hfin.subset ?_)
    rintro x ⟨t, ⟨⟨htb, htN⟩, hty⟩, rfl⟩
    exact ⟨hZ t htb htN, hty⟩

  have han : AnalyticOnNhd ℂ (fun w =>
      LinearMap.det (fderiv ℂ (fun v => A *ᵥ σ v) w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ))
      (ball (0 : Fin d → ℂ) r) := fun w hw =>
    IndefiniteRowSideFullHecke.ComplexSets.analyticAt_det_fderiv
      (IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicInverse.analyticAt_of_differentiableOn isOpen_ball hg hw)
  refine measure_mono_null ?_ (ReciprocityTheory.AnForm.volume_zero_set_of_analyticOnNhd isOpen_ball
    (convex_ball (0 : Fin d → ℂ) r).isPreconnected han hsome)
  exact fun w hw => ⟨hw.1, hw.2.2⟩

end GroundTheory.Heights₂.Heights
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PParamDensIntegrable

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology ComplexSets
open scoped ContDiff

noncomputable section

theorem ParamDensIntegrable.analyticOnNhd_of_differentiableOn {k m : ℕ} {U : Set (Fin k → ℂ)}
    {f : (Fin k → ℂ) → Fin m → ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) : AnalyticOnNhd ℂ f U := by
  refine analyticOnNhd_pi_iff.2 fun j => ?_
  have hj : DifferentiableOn ℂ (fun t => f t j) U := differentiableOn_pi.1 hf j
  refine IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_continuousOn_of_separately hU hj.continuousOn fun w hw i => ?_
  have hw : DifferentiableAt ℂ (fun t => f t j) (Function.update w i (w i)) := by
    rw [Function.update_eq_self]
    exact (hj w hw).differentiableAt (hU.mem_nhds hw)
  exact hw.comp (w i) (hasFDerivAt_update w (w i)).differentiableAt

theorem ParamDensIntegrable.proof : ParamDensIntegrable.Statement := by
  intro n d W σ r r' N hσ hrr' hN f φ hf hfN hφ
  set B := Metric.ball (0 : Fin d → ℂ) r with hB
  choose U hUo hZU hφU using hφ
  set V : Set (Fin d → ℂ) := B ∩ σ ⁻¹' (⋂ k, U k) with hV
  have hσc : ContinuousOn σ B := hσ.continuousOn
  have hVo : IsOpen V := hσc.isOpen_inter_preimage Metric.isOpen_ball (isOpen_iInter_of_finite hUo)
  have hσ2 : ContDiffOn ℝ 2 σ B :=
    ((ParamDensIntegrable.analyticOnNhd_of_differentiableOn Metric.isOpen_ball hσ).contDiffOn_of_completeSpace).restrict_scalars ℝ
  have hc2 : ∀ k, ContDiffOn ℝ 2 (φ k ∘ σ) V := by
    intro k
    exact ((hφU k).of_le (WithTop.coe_le_coe.2 le_top)).comp (hσ2.mono Set.inter_subset_left)
      fun w hw => Set.mem_iInter.1 hw.2 k
  have hmaV : ContinuousOn (ReciprocityTheory.AnForm.maDens fun k => φ k ∘ σ) V :=
    ReciprocityTheory.AnForm.M.maDens_continuousOn _ _ hVo hc2
  have hcont : ContinuousOn (fun w => f (σ w) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ σ) w) B := by
    refine continuousOn_of_forall_continuousAt fun w hw => ?_
    by_cases hs : σ w ∈ tsupport f
    · have hwV : w ∈ V := ⟨hw, Set.mem_iInter.2 fun k => hZU k (hN w hw (hfN hs)).1⟩
      exact ((hf.continuousAt).comp (hσc.continuousAt (Metric.isOpen_ball.mem_nhds hw))).mul
        (hmaV.continuousAt (hVo.mem_nhds hwV))
    · have hO : IsOpen (B ∩ σ ⁻¹' (tsupport f)ᶜ) :=
        hσc.isOpen_inter_preimage Metric.isOpen_ball (isClosed_tsupport f).isOpen_compl
      refine (continuousAt_const (y := (0 : ℝ))).congr ?_
      filter_upwards [hO.mem_nhds ⟨hw, hs⟩] with w' hw'
      simp [image_eq_zero_of_notMem_tsupport hw'.2]
  have hK : IsCompact (Metric.closedBall (0 : Fin d → ℂ) r') := isCompact_closedBall 0 r'
  have hKB : Metric.closedBall (0 : Fin d → ℂ) r' ⊆ B := Metric.closedBall_subset_ball hrr'
  refine ((hcont.mono hKB).integrableOn_compact hK).of_forall_sdiff_eq_zero Metric.isOpen_ball.measurableSet ?_
  rintro w ⟨hwB, hwK⟩
  have hf0 : f (σ w) = 0 := by
    by_contra h
    exact hwK (Metric.mem_closedBall.2 (by
      simpa using (hN w hwB (hfN (subset_tsupport f h))).2))
  simp [hf0]

end

end GroundTheory.Heights₂.Heights
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PParamOffRegularZero

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

theorem ParamOffRegularZero.proof : ParamOffRegularZero.Statement := by
  intro n d W A σ r N hσ hZN f φ hfN
  set g : (Fin d → ℂ) → Fin d → ℂ := fun v => A *ᵥ σ v with hg
  set C : Set (Fin d → ℂ) := {w | w ∈ Metric.ball (0 : Fin d → ℂ) r ∧ σ w ∈ N ∧
      LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) = 0} with hC
  set R : Set (Fin d → ℂ) := {w | w ∈ Metric.ball (0 : Fin d → ℂ) r ∧ σ w ∈ N ∧
      LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0} with hR
  have hgd : ∀ w ∈ Metric.ball (0 : Fin d → ℂ) r, DifferentiableAt ℂ g w := by
    intro w hw
    have hσw : DifferentiableAt ℂ σ w := (hσ w hw).differentiableAt (Metric.isOpen_ball.mem_nhds hw)
    exact (LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)).differentiableAt.comp w hσw
  have hnull : volume (g '' C) = 0 := by
    refine addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (f' := fun w => (fderiv ℂ g w).restrictScalars ℝ) ?_ ?_
    · intro w hw
      exact ((hgd w hw.1).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
    · intro w hw
      rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars,
        LinearMap.det_restrictScalars, hw.2.2, Algebra.norm_complex_apply, map_zero]
  have hz : ∀ y ∉ g '' C, chartDens W A ((σ '' R)ᶜ.indicator f) φ y = 0 := by
    intro y hy
    unfold chartDens sheetSum
    apply finsum_eq_zero_of_forall_eq_zero
    intro x
    classical
    rw [finsum_eq_if]
    split_ifs with hx hs
    · by_cases hxR : x ∈ σ '' R
      · simp [hxR]
      by_cases hf : f x = 0
      · simp [hxR, hf]
      exfalso
      have hxN : x ∈ N := hfN (subset_tsupport f (Function.mem_support.mpr hf))
      obtain ⟨w, hw, rfl⟩ := hZN ⟨hx.1, hxN⟩
      have hdet : LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) = 0 := by
        by_contra hne
        exact hxR ⟨w, ⟨hw, hxN, hne⟩, rfl⟩
      exact hy ⟨w, ⟨hw, hxN, hdet⟩, hx.2⟩
    · rfl
    · rfl
  unfold chartInt
  apply integral_eq_zero_of_ae
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null (fun y hy => ?_) hnull
  by_contra h
  exact hy (by simpa using hz y h)

end

end GroundTheory.Heights₂.Heights
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegularInjectivePieces

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter Topology

noncomputable section

namespace RegularInjectivePieces

theorem analyticOnNhd_of_differentiableOn {k m : ℕ} {U : Set (Fin k → ℂ)} {f : (Fin k → ℂ) → Fin m → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) : AnalyticOnNhd ℂ f U := by
  refine analyticOnNhd_pi_iff.2 fun j => ?_
  have hj : DifferentiableOn ℂ (fun t => f t j) U := differentiableOn_pi.1 hf j
  refine IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_continuousOn_of_separately hU hj.continuousOn fun w hw i => ?_
  have hw : DifferentiableAt ℂ (fun t => f t j) (Function.update w i (w i)) := by
    rw [Function.update_eq_self]
    exact (hj w hw).differentiableAt (hU.mem_nhds hw)
  exact hw.comp (w i) (hasFDerivAt_update w (w i)).differentiableAt

theorem local_injective {d : ℕ} {U : Set (Fin d → ℂ)} {g : (Fin d → ℂ) → Fin d → ℂ} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) :
    IsOpen {w | w ∈ U ∧ LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0} ∧
    ∀ w ∈ {w | w ∈ U ∧ LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0},
      ∃ V : Set (Fin d → ℂ), IsOpen V ∧ w ∈ V ∧
        V ⊆ {w | w ∈ U ∧ LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0} ∧ Set.InjOn g V := by
  have hA : AnalyticOnNhd ℂ g U := analyticOnNhd_of_differentiableOn hU hg
  have hRopen : IsOpen {w | w ∈ U ∧ LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0} := by
    have hc : ContinuousOn (fun w => (fderiv ℂ g w).det) U :=
      ContinuousLinearMap.continuous_det.comp_continuousOn hA.fderiv.continuousOn
    exact hc.isOpen_inter_preimage hU isOpen_compl_singleton
  refine ⟨hRopen, fun w hw => ?_⟩
  have hs : HasStrictFDerivAt g
      (((fderiv ℂ g w).toContinuousLinearEquivOfDetNeZero hw.2 : (Fin d → ℂ) ≃L[ℂ] (Fin d → ℂ)) :
        (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) w := by
    rw [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
    exact (hA w hw.1).hasStrictFDerivAt
  refine ⟨(hs.toOpenPartialHomeomorph g).source ∩ _, (hs.toOpenPartialHomeomorph g).open_source.inter hRopen,
    ⟨hs.mem_toOpenPartialHomeomorph_source, hw⟩, Set.inter_subset_right, ?_⟩
  have hinj := (hs.toOpenPartialHomeomorph g).injOn
  rw [HasStrictFDerivAt.toOpenPartialHomeomorph_coe] at hinj
  exact hinj.mono Set.inter_subset_left

end RegularInjectivePieces


open RegularInjectivePieces in
theorem RegularInjectivePieces.proof : RegularInjectivePieces.Statement := by
  intro d U g hU hg
  obtain ⟨hRopen, key⟩ := local_injective hU hg
  set R := {w | w ∈ U ∧ LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0} with hR
  choose! V hVo hVm hVR hVi using key
  obtain ⟨T, hTc, hTU⟩ :=
    TopologicalSpace.isOpen_iUnion_countable (fun w : R => V w) (fun w => hVo w w.2)
  have hUnion : ⋃ w : R, V w = R := by
    ext x
    simp only [Set.mem_iUnion]
    exact ⟨fun ⟨w, hx⟩ => hVR w w.2 hx, fun hx => ⟨⟨x, hx⟩, hVm x hx⟩⟩
  rcases T.eq_empty_or_nonempty with hT0 | hTne
  · refine ⟨fun _ => ∅, fun _ => MeasurableSet.empty, fun i j _ => disjoint_bot_left, ?_,
      fun _ => Set.injOn_empty _⟩
    rw [← hUnion, ← hTU, hT0]
    simp
  · obtain ⟨f, hf⟩ := hTc.exists_eq_range hTne
    refine ⟨disjointed (fun n => V (f n)),
      MeasurableSet.disjointed (fun n => (hVo _ (f n).2).measurableSet), disjoint_disjointed _, ?_,
      fun n => (hVi _ (f n).2).mono (disjointed_subset _ n)⟩
    rw [iUnion_disjointed]
    calc ⋃ n, V (f n) = ⋃ i ∈ Set.range f, V i :=
        (Set.biUnion_range (f := f) (g := fun i : R => V (i : Fin d → ℂ))).symm
      _ = ⋃ i ∈ T, V i := by rw [hf]
      _ = R := hTU.trans hUnion

end

end GroundTheory.Heights₂.Heights
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SliceBranchInt

section

@[expose] public section

namespace GlobalTheory.CompanionTheory.Ar.SliceBranch

theorem paramChartInt : GroundTheory.Heights₂.Heights.ParamChartInt.Statement :=
  GroundTheory.Heights₂.Heights.ParamChartInt.proof
    (GroundTheory.Heights₂.Heights.ChartIntCountAdd.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.ChartMassCompact)
    GroundTheory.Heights₂.Heights.ParamPieceInt.proof GroundTheory.Heights₂.Heights.ParamCritNull.proof
    GroundTheory.Heights₂.Heights.ParamOffRegularZero.proof GroundTheory.Heights₂.Heights.RegularInjectivePieces.proof
    GroundTheory.Heights₂.Heights.ParamDensIntegrable.proof

theorem sliceBranchInt : GroundTheory.Heights₂.Heights.SliceBranchInt.Statement :=
  GroundTheory.Heights₂.Heights.SliceBranchInt.proof GlobalTheory.T.branch_proper_at_point_holds paramChartInt

end GlobalTheory.CompanionTheory.Ar.SliceBranch
end
end
