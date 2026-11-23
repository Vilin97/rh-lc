module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLelongLimitAtBranches
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchIntDecompose
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BranchProperAtPointHoldsStatement
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchProperAtPoint
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchChartInt
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StChartIntSumOffHyperplane
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeAvoidsExists
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeAvoidsFinite
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeAvoidsOpen
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteProjHomInjective
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteProjectionsContainOpen
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGenericProjectionFinite
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHomogDimZeroPow
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLeadIdealDim
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLinearFormCut
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PUnitaryZariskiDense
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PBranchChartIntX
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.ParametrisationSheetsConnectedHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BranchProperAtPointHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SliceBranchInt
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceBranchInt
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPolydiscLelongLimit
import Mathlib.Order.CompletePartialOrder
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.UniformSpace.Uniformizable
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.ContDiffOfContDiffOnZeroOff
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.HessCRestrictThm
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.ProjectiveLineZeroFormHolds
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchIntDecompose

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

theorem BranchIntDecompose.proof (hPr : IndefiniteRowSideFullHecke.ComplexSets.BranchProperAtPoint.Statement)
    (hGen : ComplexSets.GenericProjectionFinite.Statement) (hSum : ChartIntSumOffHyperplane.Statement)
    (hBr : BranchChartInt.Statement) : BranchIntDecompose.Statement := by
  intro n d J u q m γ ord hJ hdim hu hcov hdisj _
  obtain ⟨N₀, hN₀, hcovN⟩ := hcov
  have hpr : ∀ b, ∃ e > 0, ∀ τ ∈ Metric.ball 0 (γ b).radius, (γ b).toFun τ ∈ Metric.ball q e →
      τ ∈ Metric.ball 0 ((γ b).radius / 2) := fun b =>
    hPr n (d + 1) J u q q m γ hJ hdim hu ⟨N₀, hN₀, hcovN⟩ hdisj b 0
      (Metric.mem_ball_self (γ b).radius_pos) (γ b).map_zero _
      (Metric.ball_mem_nhds _ (half_pos (γ b).radius_pos))
  choose e he hpe using hpr
  refine ⟨N₀ ∩ ⋂ b, Metric.ball q (e b),
    inter_mem hN₀ (iInter_mem.2 fun b => Metric.ball_mem_nhds q (he b)),
    fun f ψ hf _ hfN hψ => ?_⟩
  have hex : ∃ A : Matrix (Fin (d + 1)) (Fin n) ℂ, IsFiniteProjection J A :=
    (hGen n (d + 1) J hJ hdim).2.1
  have hAf : IsFiniteProjection J hex.choose := hex.choose_spec
  have hvar : varInt J (d + 1) f ψ = chartInt J hex.choose f ψ := by
    rw [varInt, dite_eq_left hex]
  have hbr : ∀ b, Integrable (chartDens J hex.choose ((γ b).image.indicator f) ψ) ∧
      chartInt J hex.choose ((γ b).image.indicator f) ψ =
        ReciprocityTheory.AnForm.maInt (fun k => ψ k ∘ (γ b).toFun) (f ∘ (γ b).toFun)
          (Metric.ball 0 (γ b).radius) := by
    intro b
    refine hBr n (d + 1) J hex.choose q (γ b) f ψ hJ hdim hAf hf.continuous hψ
      ⟨Metric.closedBall 0 ((γ b).radius / 2), isCompact_closedBall _ _,
        Metric.closedBall_subset_ball (half_lt_self (γ b).radius_pos), fun t ht htK => ?_⟩
    by_contra hne
    have hx := hfN (subset_tsupport f hne)
    exact htK (Metric.ball_subset_closedBall (hpe b t ht (Set.mem_iInter.1 hx.2 b)))
  have hpt : ∀ x ∈ zeroSet J, linEval u x ≠ 0 → f x = ∑ b, (γ b).image.indicator f x := by
    intro x hxZ hux
    by_cases hfx : f x = 0
    · rw [hfx]
      exact (Finset.sum_eq_zero fun b _ => by by_cases hb : x ∈ (γ b).image <;> simp [hb, hfx]).symm
    · have hxN := hfN (subset_tsupport f hfx)
      obtain ⟨b₀, hb₀⟩ := Set.mem_iUnion.1 (hcovN ⟨hxZ, hxN.1⟩)
      rw [Finset.sum_eq_single b₀
        (fun b _ hb => Set.indicator_of_notMem (fun hxb => hux (hdisj b b₀ hb ⟨hxb, hb₀⟩)) _)
        (fun h => absurd (Finset.mem_univ b₀) h), Set.indicator_of_mem hb₀]
  rw [hvar, hSum n (d + 1) J hex.choose u m f (fun b => (γ b).image.indicator f) ψ hJ hdim hAf hu hpt
    (fun b => (hbr b).1)]
  exact Finset.sum_congr rfl fun b _ => (hbr b).2

end

end GroundTheory.Heights₂.Heights
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BranchIntDecompose

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar

theorem branchIntDecompose : GroundTheory.Heights₂.Heights.BranchIntDecompose.Statement :=
  GroundTheory.Heights₂.Heights.BranchIntDecompose.proof GlobalTheory.T.branch_proper_at_point_holds
    (GroundTheory.Heights₂.Heights.ComplexSets.GenericProjectionFinite.proof
      (GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjectionsContainOpen.proof
        GroundTheory.Heights₂.Heights.ComplexSets.ConeAvoidsFinite.proof
        GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjHomInjective.proof
        GroundTheory.Heights₂.Heights.ComplexSets.ConeAvoidsOpen.proof
        (GroundTheory.Heights₂.Heights.ComplexSets.ConeAvoidsExists.proof
          GroundTheory.Heights₂.Heights.ComplexSets.LeadIdealDim.proof
          GroundTheory.Heights₂.Heights.ComplexSets.LinearFormCut.proof
          GroundTheory.Heights₂.Heights.ComplexSets.HomogDimZeroPow.proof))
      GroundTheory.Heights₂.Heights.ComplexSets.UnitaryZariskiDense.proof)
    GroundTheory.Heights₂.Heights.AutoClose.ChartIntSumOffHyperplane
    GroundTheory.Heights₂.Heights.Swarm.BranchChartInt.proof

end GlobalTheory.CompanionTheory.Ar
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongLimitAtBranches

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

theorem LelongLimitAtBranches.proof (hDec : BranchIntDecompose.Statement) (hSl : SliceBranchInt.Statement)
    (hLim : PolydiscLelongLimit.Statement) (hPr : IndefiniteRowSideFullHecke.ComplexSets.BranchProperAtPoint.Statement) :
    LelongLimitAtBranches.Statement := by
  intro n d J W u q m γ ord π φ hJ hdim hu hW hq hφ hzW hcov hsl hdisj hord _
  obtain ⟨NA, hNA, hA⟩ := hDec n d J u q m γ ord hJ hdim hu hcov hdisj hord
  obtain ⟨NB, hNB, hB⟩ := hSl n d J W u q m γ ord hJ hdim hu hW hq hzW hcov hsl hdisj hord
  have hpr : ∀ b, ∃ e > 0, ∀ τ ∈ Metric.ball 0 (γ b).radius, (γ b).toFun τ ∈ Metric.ball q e →
      τ ∈ Metric.ball 0 ((γ b).radius / 2) := fun b =>
    hPr n (d + 1) J u q q m γ hJ hdim hu hcov hdisj b 0 (Metric.mem_ball_self (γ b).radius_pos)
      (γ b).map_zero _ (Metric.ball_mem_nhds _ (half_pos (γ b).radius_pos))
  choose e he hpe using hpr
  refine ⟨NA ∩ NB ∩ ⋂ b, Metric.ball q (e b), inter_mem (inter_mem hNA hNB)
    (iInter_mem.2 fun b => Metric.ball_mem_nhds q (he b)), fun f hf hfc hfN => ?_⟩
  have hcons : ∀ (g : (Fin n → ℂ) → ℝ) (b : Fin m), (fun k => vecCons g φ k ∘ (γ b).toFun) =
      vecCons (g ∘ (γ b).toFun) fun k => φ k ∘ (γ b).toFun := fun g b => by
    funext k; refine Fin.cases ?_ (fun j => ?_) k <;> simp
  have hsum : (fun ε => ∑ b, ReciprocityTheory.AnForm.maInt
      (vecCons (fun τ => Real.log (‖linEval u ((γ b).toFun τ)‖ ^ 2 + ε) / 2) fun k => φ k ∘ (γ b).toFun)
      (f ∘ (γ b).toFun) (Metric.ball 0 (γ b).radius)) =ᶠ[𝓝[>] 0]
      fun ε => varInt J (d + 1) f (vecCons (logReg u ε) φ) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [hA f _ hf hfc (hfN.trans (Set.inter_subset_left.trans Set.inter_subset_left))
      (fun i => Fin.cases ⟨Set.univ, isOpen_univ, Set.subset_univ _, (contDiff_logReg u hε).contDiffOn⟩
        (fun j => hφ j) i)]
    exact Finset.sum_congr rfl fun b _ => by rw [hcons]; rfl
  refine Tendsto.congr' hsum ?_
  have hlim : ∀ b, Tendsto (fun ε => ReciprocityTheory.AnForm.maInt
      (vecCons (fun τ => Real.log (‖linEval u ((γ b).toFun τ)‖ ^ 2 + ε) / 2) fun k => φ k ∘ (γ b).toFun)
      (f ∘ (γ b).toFun) (Metric.ball 0 (γ b).radius)) (𝓝[>] 0) (𝓝 ((ord b : ℝ) * varInt W d f φ)) := by
    intro b
    have han : AnalyticOnNhd ℂ (γ b).toFun (Metric.ball 0 (γ b).radius) := fun w hw =>
      AnalyticAt.pi fun i => ReciprocityTheory.AnForm.Osgood.osgood (d + 1) _ (fun z => (γ b).toFun z i)
        Metric.isOpen_ball (differentiableOn_pi.1 (γ b).differentiableOn i) w hw
    have hγ : ContDiffOn ℝ ∞ (γ b).toFun (Metric.ball 0 (γ b).radius) :=
      (han.contDiffOn_of_completeSpace (n := ∞)).restrict_scalars ℝ
    rw [hB b f φ hf hfc (hfN.trans (Set.inter_subset_left.trans Set.inter_subset_right)) hφ]
    refine hLim d (ord b) (γ b).radius ((γ b).radius / 2) _ (f ∘ (γ b).toFun) _
      (half_lt_self (γ b).radius_pos) (hord b) (hf.comp_contDiffOn hγ) (fun τ hτ hne => hpe b τ hτ ?_)
      (fun k => ?_)
    · exact Set.mem_iInter.1 (Set.inter_subset_right (hfN (subset_tsupport f hne))) b
    · obtain ⟨U, hU, hsub, hφU⟩ := hφ k
      exact hφU.comp hγ fun τ hτ => hsub ((γ b).mapsTo hτ)
  have := tendsto_finsetSum Finset.univ fun b _ => hlim b
  convert this using 2
  push_cast
  rw [Finset.sum_mul]

end GroundTheory.Heights₂.Heights
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPolydiscLelongLimit

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open scoped ContDiff

noncomputable section

namespace PolydiscLelongLimit

theorem hypIncl_mem_ball {d : ℕ} {r : ℝ} (w : Fin d → ℂ) :
    hypIncl w ∈ Metric.ball (0 : Fin (d + 1) → ℂ) r ↔ w ∈ Metric.ball 0 r := by
  rcases le_or_gt r 0 with hr | hr
  · simp [Metric.ball_eq_empty.2 hr]
  · simp only [mem_ball_zero_iff, pi_norm_lt_iff hr, Fin.forall_fin_succ, hypIncl, Fin.cons_zero,
      Fin.cons_succ, norm_zero, hr, true_and]

theorem extend_by_zero {D : ℕ} {r ρ : ℝ} {χ : (Fin D → ℂ) → ℝ} (hρ : ρ < r)
    (hχ : ContDiffOn ℝ ∞ χ (Metric.ball 0 r))
    (hsupp : ∀ τ ∈ Metric.ball (0 : Fin D → ℂ) r, χ τ ≠ 0 → τ ∈ Metric.ball 0 ρ) :
    ContDiff ℝ ∞ ((Metric.ball (0 : Fin D → ℂ) r).indicator χ) ∧
      HasCompactSupport ((Metric.ball (0 : Fin D → ℂ) r).indicator χ) ∧
      tsupport ((Metric.ball (0 : Fin D → ℂ) r).indicator χ) ⊆ Metric.closedBall 0 ρ ∧
      Set.EqOn ((Metric.ball (0 : Fin D → ℂ) r).indicator χ) χ (Metric.ball 0 r) := by
  have h0 : ∀ τ ∉ Metric.closedBall (0 : Fin D → ℂ) ρ,
      (Metric.ball (0 : Fin D → ℂ) r).indicator χ τ = 0 := by
    intro τ hτ
    by_cases hU : τ ∈ Metric.ball (0 : Fin D → ℂ) r
    · rw [Set.indicator_of_mem hU]
      by_contra h
      exact hτ (Metric.ball_subset_closedBall (hsupp τ hU h))
    · exact Set.indicator_of_notMem hU _
  have heq : Set.EqOn ((Metric.ball (0 : Fin D → ℂ) r).indicator χ) χ (Metric.ball 0 r) :=
    fun τ hτ => Set.indicator_of_mem hτ _
  exact ⟨contDiff_of_contDiffOn_zero_off Metric.isOpen_ball Metric.isClosed_closedBall
    (Metric.closedBall_subset_ball hρ) (hχ.congr heq) h0,
    HasCompactSupport.intro (isCompact_closedBall 0 ρ) h0,
    closure_minimal (fun τ hτ => by_contra fun h => (Function.mem_support.1 hτ) (h0 τ h))
      Metric.isClosed_closedBall, heq⟩

theorem logReg_contDiffOn {D : ℕ} {U : Set (Fin D → ℂ)} (hU : IsOpen U) {F : (Fin D → ℂ) → ℂ}
    (hF : DifferentiableOn ℂ F U) {ε : ℝ} (hε : 0 < ε) :
    ContDiffOn ℝ ∞ (fun τ => Real.log (‖F τ‖ ^ 2 + ε) / 2) U := by
  intro z hz
  have h1 : ContDiffAt ℝ ∞ F z :=
    ((ReciprocityTheory.AnForm.Osgood.osgood D U F hU hF z hz).contDiffAt (n := ∞)).restrict_scalars ℝ
  have h2 : ContDiffAt ℝ ∞ (fun τ => ‖F τ‖ ^ 2 + ε) z := (h1.norm_sq ℝ).add contDiffAt_const
  exact ((h2.log (by positivity)).div_const 2).contDiffWithinAt

end PolydiscLelongLimit


open PolydiscLelongLimit in
theorem PolydiscLelongLimit.proof : PolydiscLelongLimit.Statement := by
  intro d m r ρ F χ ψ hρ hF hχ hsupp hψ
  obtain ⟨H, hHd, hH0, hFH⟩ := hF
  have h3 : (3 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.2 le_top
  obtain ⟨hv, hvc, hvt, hvχ⟩ := extend_by_zero hρ hχ hsupp
  set U : Set (Fin (d + 1) → ℂ) := Metric.ball 0 r with hUdef
  set v := U.indicator χ with hvdef
  have hU : IsOpen U := Metric.isOpen_ball
  have hvU : tsupport v ⊆ U := hvt.trans (Metric.closedBall_subset_ball hρ)
  have hFd : DifferentiableOn ℂ F U :=
    (((differentiable_apply 0).pow m).differentiableOn.mul hHd).congr fun t ht => hFH t ht
  have hFne : ∀ τ ∈ U, τ 0 ≠ 0 → F τ ≠ 0 := fun τ hτ h0 => by
    rw [hFH τ hτ]; exact mul_ne_zero (pow_ne_zero _ h0) (hH0 τ hτ)
  have hdens0 : ∀ τ, τ ∉ tsupport v → densV v ψ τ = 0 := fun τ hτ => maDens_cons_eq_zero ψ hτ
  have hIon : ∀ f : (Fin (d + 1) → ℂ) → ℝ, IntegrableOn (fun z => f z * densV v ψ z) U →
      Integrable (fun z => f z * densV v ψ z) := fun f h =>
    (integrableOn_iff_integrable_of_support_subset fun z hz => by_contra fun h' =>
      (Function.mem_support.1 hz) (mul_eq_zero_of_right _ (hdens0 z fun h'' => h' (hvU h'')))).1 h

  have hgood : ∀ ε : ℝ, 0 < ε →
      Integrable (fun τ => Real.log (‖F τ‖ ^ 2 + ε) / 2 * densV v ψ τ) ∧
      maInt (Matrix.vecCons (fun τ => Real.log (‖F τ‖ ^ 2 + ε) / 2) ψ) χ U =
        ∫ τ, Real.log (‖F τ‖ ^ 2 + ε) / 2 * densV v ψ τ := by
    intro ε hε
    have hP := parts_thm d ψ v (fun τ => Real.log (‖F τ‖ ^ 2 + ε) / 2) U
      ⟨hU, (hv.of_le h3).contDiffOn, hvc, hvU, (logReg_contDiffOn hU hFd hε).of_le h3,
        fun k => (hψ k).of_le h3⟩
    refine ⟨hIon _ hP.2.1, ?_⟩
    calc maInt (Matrix.vecCons (fun τ => Real.log (‖F τ‖ ^ 2 + ε) / 2) ψ) χ U
        = maInt (Fin.cons (fun τ => Real.log (‖F τ‖ ^ 2 + ε) / 2) ψ) v U := by
          unfold maInt
          exact setIntegral_congr_fun hU.measurableSet fun τ hτ => by
            simp only [hvχ hτ]; try rfl
      _ = maInt (Fin.cons v ψ) (fun τ => Real.log (‖F τ‖ ^ 2 + ε) / 2) U := hP.2.2.2.2.symm
      _ = ∫ τ, Real.log (‖F τ‖ ^ 2 + ε) / 2 * densV v ψ τ := by
          unfold maInt
          exact setIntegral_eq_integral_of_forall_compl_eq_zero fun τ hτ =>
            mul_eq_zero_of_right _ (hdens0 τ fun h => hτ (hvU h))

  have hL0 := log_norm_integral_formula_unit d (m : ℤ) U v ψ H ⟨hU, hv.of_le h3, hvc, hvU, hψ⟩ hHd hH0
  have hlogF : (fun z => Real.log ‖F z‖ * densV v ψ z) =
      fun z => Real.log ‖z 0 ^ (m : ℤ) * H z‖ * densV v ψ z := by
    funext z
    by_cases hz : z ∈ U
    · rw [hFH z hz, zpow_natCast]
    · rw [hdens0 z fun h => hz (hvU h), mul_zero, mul_zero]
  have hint : Integrable (fun τ => Real.log ‖F τ‖ * densV v ψ τ) := by rw [hlogF]; exact hL0.1
  have hdensI : Integrable (densV v ψ) := by
    have hP1 := parts_thm d ψ v (fun _ => (1 : ℝ)) U
      ⟨hU, (hv.of_le h3).contDiffOn, hvc, hvU, contDiffOn_const, fun k => (hψ k).of_le h3⟩
    exact (hIon (fun _ => 1) hP1.2.1).congr (Eventually.of_forall fun z => one_mul _)
  obtain ⟨C, hC⟩ : ∃ C, ∀ τ ∈ tsupport v, ‖(1 / 2 : ℝ) * Real.log (‖F τ‖ ^ 2 + 1)‖ ≤ C :=
    hvc.isCompact.exists_bound_of_continuousOn fun τ hτ =>
      (continuousAt_const.mul ((((hFd.continuousOn.continuousAt (hU.mem_nhds (hvU hτ))).norm.pow 2).add
        continuousAt_const).log (by positivity : ‖F τ‖ ^ 2 + 1 ≠ 0))).continuousWithinAt

  have hlim : Tendsto (fun ε : ℝ => ∫ τ, Real.log (‖F τ‖ ^ 2 + ε) / 2 * densV v ψ τ) (𝓝[>] 0)
      (𝓝 (∫ τ, Real.log ‖F τ‖ * densV v ψ τ)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun τ => |Real.log ‖F τ‖ * densV v ψ τ| + C * |densV v ψ τ|)
      (eventually_mem_nhdsWithin.mono fun ε hε => (hgood ε hε).1.aestronglyMeasurable) ?_
      (hint.abs.add (hdensI.abs.const_mul C)) ?_
    · filter_upwards [Ioc_mem_nhdsGT (one_pos : (0 : ℝ) < 1)] with ε hε
      filter_upwards [ae_coord_ne_zero (0 : Fin (d + 1))] with τ hτ0
      by_cases hτ : τ ∈ tsupport v
      · have h1 := gReg_abs_le hε.1 hε.2 (hFne τ (hvU hτ) hτ0)
        have h2 := hC τ hτ
        rw [Real.norm_eq_abs] at h2
        have e : Real.log (‖F τ‖ ^ 2 + ε) / 2 = gReg ε (F τ) := by unfold gReg; ring
        have h4 : |gReg ε (F τ)| ≤ |Real.log ‖F τ‖| + C :=
          h1.trans (by linarith [le_abs_self ((1 / 2 : ℝ) * Real.log (‖F τ‖ ^ 2 + 1))])
        rw [Real.norm_eq_abs, abs_mul, abs_mul, e]
        calc |gReg ε (F τ)| * |densV v ψ τ| ≤ (|Real.log ‖F τ‖| + C) * |densV v ψ τ| :=
              mul_le_mul_of_nonneg_right h4 (abs_nonneg _)
          _ = _ := by ring
      · rw [hdens0 τ hτ]; simp
    · filter_upwards [ae_coord_ne_zero (0 : Fin (d + 1))] with τ hτ0
      by_cases hτ : τ ∈ U
      · have hpos : 0 < ‖F τ‖ ^ 2 := pow_pos (norm_pos_iff.2 (hFne τ hτ hτ0)) 2
        have hc : Tendsto (fun ε : ℝ => ‖F τ‖ ^ 2 + ε) (𝓝[>] 0) (𝓝 (‖F τ‖ ^ 2 + 0)) :=
          (tendsto_const_nhds.add tendsto_id).mono_left nhdsWithin_le_nhds
        rw [add_zero] at hc
        have e : Real.log ‖F τ‖ = Real.log (‖F τ‖ ^ 2) / 2 := by rw [Real.log_pow]; push_cast; ring
        rw [e]
        exact (((Real.continuousAt_log hpos.ne').tendsto.comp hc).div_const 2).mul_const _
      · rw [hdens0 τ fun h => hτ (hvU h)]
        simp only [mul_zero]
        exact tendsto_const_nhds

  have hR : ∫ w in Metric.ball (0 : Fin d → ℂ) r, χ (hypIncl w) * densHyp ψ w =
      ∫ w, v (hypIncl w) * densHyp ψ w := by
    rw [setIntegral_congr_fun (g := fun w => v (hypIncl w) * densHyp ψ w)
      Metric.isOpen_ball.measurableSet fun w hw => by
      simp only [hvχ ((hypIncl_mem_ball w).2 hw)]]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero fun w hw =>
      mul_eq_zero_of_left (Set.indicator_of_notMem (mt (hypIncl_mem_ball w).1 hw) _) _
  have hlimF : ∫ τ, Real.log ‖F τ‖ * densV v ψ τ = (m : ℝ) * ∫ w, v (hypIncl w) * densHyp ψ w := by
    rw [hlogF, hL0.2, Int.cast_natCast]
  rw [hR, ← hlimF]
  exact hlim.congr' (eventually_mem_nhdsWithin.mono fun ε hε => (hgood ε hε).2.symm)

end

end GroundTheory.Heights₂.Heights
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LelongLimitAtBranches

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Lelong

open GroundTheory.Heights₂.Heights

theorem lelongLimitAtBranches : LelongLimitAtBranches.Statement :=
  LelongLimitAtBranches.proof GlobalTheory.CompanionTheory.Ar.branchIntDecompose GlobalTheory.CompanionTheory.Ar.SliceBranch.sliceBranchInt
    PolydiscLelongLimit.proof GlobalTheory.CompanionTheory.Ar.Branch.branchProperAtPoint

end GlobalTheory.CompanionTheory.Ar.Lelong
end
end
