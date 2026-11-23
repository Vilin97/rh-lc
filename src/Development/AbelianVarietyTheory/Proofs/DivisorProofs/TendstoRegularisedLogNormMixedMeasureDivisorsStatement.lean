module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightEqOneIffClosureDimProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjFsBasisOfUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogNormSectionIntegrableMixedChernProjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormFiniteIntegrablePointClosureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureComplOpenGenericPStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernMeasureFiniteIntegrableProjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothWeightedLineBundleLogSectionNormPropertiesStatement
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtArith
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.Tactic.Basify
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoIntegralLogAddInv

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem tendsto_integral_log_add_inv : ∀ (T : Type) [MeasurableSpace T] (μ : Measure T) [IsFiniteMeasure μ] (w : T → ℝ) (C : ℝ), Measurable w → (∀ x, 0 ≤ w x ∧ w x ≤ C) → (∀ᵐ x ∂μ, 0 < w x) → Integrable (fun x => Real.log (w x) / 2) μ → Tendsto (fun n : ℕ => ∫ x, Real.log (w x + 1 / ((n : ℝ) + 1)) ∂μ) atTop (𝓝 (2 * ∫ x, Real.log (w x) / 2 ∂μ)) := by
  intro T _ μ _ w C hw hwC hpos hint
  have hint' : Integrable (fun x => Real.log (w x)) μ := by
    refine (hint.const_mul 2).congr (Eventually.of_forall fun x => ?_)
    simp only; ring
  have hlim : 2 * ∫ x, Real.log (w x) / 2 ∂μ = ∫ x, Real.log (w x) ∂μ := by
    rw [← integral_const_mul]; congr 1; ext x; ring
  rw [hlim]
  refine tendsto_integral_of_dominated_convergence (fun x => |Real.log (w x)| + |Real.log (C + 1)|) ?_ ?_ ?_ ?_
  · intro n
    exact (Real.measurable_log.comp (hw.add_const _)).aestronglyMeasurable
  · exact hint'.abs.add (integrable_const _)
  · intro n
    filter_upwards [hpos] with x hx
    have hd : 0 < 1 / ((n:ℝ) + 1) := by positivity
    have hd1 : 1 / ((n:ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]
    have h1 : Real.log (w x) ≤ Real.log (w x + 1 / ((n:ℝ)+1)) := Real.log_le_log hx (by linarith)
    have h2 : Real.log (w x + 1 / ((n:ℝ)+1)) ≤ Real.log (C + 1) :=
      Real.log_le_log (by linarith) (by linarith [(hwC x).2])
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · linarith [neg_abs_le (Real.log (w x)), abs_nonneg (Real.log (C+1))]
    · linarith [le_abs_self (Real.log (C+1)), abs_nonneg (Real.log (w x))]
  · filter_upwards [hpos] with x hx
    have h : Tendsto (fun n : ℕ => w x + 1 / ((n:ℝ) + 1)) atTop (𝓝 (w x + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
    rw [add_zero] at h
    exact (Real.continuousAt_log hx.ne').tendsto.comp h

end GlobalTheory.Mix
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoIntegralLogAddInvStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.tendsto_integral_log_add_inv_succ : ∀ (T : Type) [MeasurableSpace T] (μ : Measure T) [IsFiniteMeasure μ] (w : T → ℝ) (C : ℝ), Measurable w → (∀ x, 0 ≤ w x ∧ w x ≤ C) → (∀ᵐ x ∂μ, 0 < w x) → Integrable (fun x => Real.log (w x) / 2) μ → Tendsto (fun n : ℕ => ∫ x, Real.log (w x + 1 / ((n : ℝ) + 1)) ∂μ) atTop (𝓝 (2 * ∫ x, Real.log (w x) / 2 ∂μ)) := by
  first | exact @GlobalTheory.Mix.tendsto_integral_log_add_inv | exact GlobalTheory.Mix.tendsto_integral_log_add_inv | (intros; apply GlobalTheory.Mix.tendsto_integral_log_add_inv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoRegularisedLogNormMixedMeasureDivisors

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mix.LogLim

theorem compactSpace_of_proj {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsProjOver f) : CompactSpace X := by
  obtain ⟨m, i, hi, rfl⟩ := h
  have := isProper_str R m
  have : IsProper (i ≫ PSpace.str R m) := inferInstance
  exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str R m)

theorem nsq_nonneg {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
    (N : MLine p σ) (t : N.B.Sec) (y : CxPts p σ) : 0 ≤ N.φ.nsq (secVal p σ t) y := by
  unfold Weight.nsq; positivity

theorem continuous_nsq {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
    (N : MLine p σ) (t : N.B.Sec) : Continuous (N.φ.nsq (secVal p σ t)) :=
  continuous_iff_continuousAt.2 fun y => ((GlobalTheory.T.smoothWeightedLineBundle_logSectionNorm_properties k X p σ N t).2.2.1 y).continuousAt

theorem exists_nsq_le {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
    (hp : IsProjOver p) (N : MLine p σ) (t : N.B.Sec) : ∃ C : ℝ, ∀ y, N.φ.nsq (secVal p σ t) y ≤ C := by
  haveI : CompactSpace (CxPts p σ) := CxPts.compactSpace σ hp
  obtain ⟨C, hC⟩ := (isCompact_univ.image (continuous_nsq N t)).bddAbove
  exact ⟨C, fun y => hC ⟨y, Set.mem_univ _, rfl⟩⟩

end GlobalTheory.Mix.LogLim


open GlobalTheory.Mix.LogLim in
theorem GlobalTheory.Mix.tendsto_logReg : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (N : MLine p σ) (t : N.B.Sec), (genericPoint X ∈ nonzeroLocus t → ∀ L : Fin (e + 1) → MLine p σ, Tendsto (fun n : ℕ => Mix.int L fun y => Real.log (N.φ.nsq (secVal p σ t) y + 1 / ((n : ℝ) + 1))) atTop (𝓝 (2 * Mix.int L (N.logSec t)))) ∧ ∀ (L : Fin e → MLine p σ) (Δ : CartierDiv X), (∀ z, Δ.mult z ≠ 0 → z ∈ nonzeroLocus t) → Tendsto (fun n : ℕ => ∑ᶠ z, (Δ.mult z : ℝ) * cycInt L (fun y => Real.log (N.φ.nsq (secVal p σ t) y + 1 / ((n : ℝ) + 1))) z) atTop (𝓝 (2 * ∑ᶠ z, (Δ.mult z : ℝ) * cycInt L (N.logSec t) z)) := by
  intro hP F _ X _ _ p σ e hp hdim N t
  set w := N.φ.nsq (secVal p σ t) with hw_def
  have hbasic := GlobalTheory.T.smoothWeightedLineBundle_logSectionNorm_properties F X p σ N t
  have hcont : Continuous w := continuous_nsq N t
  obtain ⟨C, hC⟩ := exists_nsq_le hp N t
  have hwC : ∀ y, 0 ≤ w y ∧ w y ≤ C := fun y => ⟨nsq_nonneg N t y, hC y⟩
  refine ⟨fun hgen L => ?_, fun L Δ hΔ => ?_⟩
  · have hfin := (GlobalTheory.T.mixedChernMeasure_finite_integrable_projective hP F X p σ (e + 1) hp hdim L).1
    have hint := GlobalTheory.T.log_norm_section_integrable_mixedChern_projective hP F X p σ (e + 1) hp hdim L N t hgen
    have one (ε : ℤˣ) (hi : Integrable (N.logSec t) (part L ε)) :
        Tendsto (fun n : ℕ => ∫ y, Real.log (w y + 1 / ((n : ℝ) + 1)) ∂part L ε) atTop
          (𝓝 (2 * ∫ y, Real.log (w y) / 2 ∂part L ε)) := by
      haveI := hfin ε
      have hnull := GlobalTheory.T.mixedChernFormSignedPartMeasure_compl_open_genericPoint_eq_zero F X p σ σ.injective hp (e + 1) L ε (nonzeroLocus t) hgen
      refine GlobalTheory.T.tendsto_integral_log_add_inv_succ _ (part L ε) w C hcont.measurable hwC ?_ hi
      refine ae_iff.2 (measure_mono_null (fun y hy => ?_) hnull)
      exact fun h => hy ((hbasic.2.1 y).2 h)
    have h1 := one 1 hint.1
    have h2 := one (-1) hint.2
    simp only [Mix.int, MLine.logSec, mul_sub]
    exact h1.sub h2
  · haveI : CompactSpace X := compactSpace_of_proj hp
    have hS := Δ.finite_support_mult
    have hsub (f : X → ℝ) : Function.support (fun z => (Δ.mult z : ℝ) * f z) ⊆ ↑hS.toFinset := by
      intro z hz
      simp only [Set.Finite.coe_toFinset, Function.mem_support]
      intro h0; apply hz; simp [h0]
    have hrw : (fun n : ℕ => ∑ᶠ z, (Δ.mult z : ℝ) * cycInt L (fun y => Real.log (w y + 1 / ((n : ℝ) + 1))) z) =
        fun n : ℕ => ∑ z ∈ hS.toFinset, (Δ.mult z : ℝ) * cycInt L (fun y => Real.log (w y + 1 / ((n : ℝ) + 1))) z :=
      funext fun n => finsum_eq_sum_of_support_subset _ (hsub _)
    rw [hrw, finsum_eq_sum_of_support_subset _ (hsub _), Finset.mul_sum]
    refine tendsto_finsetSum _ fun z hz => ?_
    have hz0 : Δ.mult z ≠ 0 := by simpa using hz
    have hcoh := CartierDiv.coheight_eq_one_of_mult_ne_zero hz0
    have hdz := (GlobalTheory.T.coheight_eq_one_iff_closure_dim_projective F X p e hp hdim z).1 hcoh
    obtain ⟨hfin, -, hnull, hlog⟩ := GlobalTheory.T.mixedChernForm_finite_integrable_pointClosure hP F X p σ hp e L z hdz
    have hzt := hΔ z hz0
    have hint := hlog N t hzt
    set π := ptMap (closι z) rfl σ with hπ
    have hπc : Continuous π := continuous_of_comp (f := closι z) fun _ => rfl
    have one (ε : ℤˣ) (hi : Integrable (fun y => N.logSec t (π y)) (part (fun i => (L i).pull (closι z) rfl) ε)) :
        Tendsto (fun n : ℕ => ∫ y, Real.log (w (π y) + 1 / ((n : ℝ) + 1)) ∂part (fun i => (L i).pull (closι z) rfl) ε)
          atTop (𝓝 (2 * ∫ y, Real.log (w (π y)) / 2 ∂part (fun i => (L i).pull (closι z) rfl) ε)) := by
      haveI := hfin ε
      refine GlobalTheory.T.tendsto_integral_log_add_inv_succ _ _ (fun y => w (π y)) C (hcont.comp hπc).measurable (fun y => hwC (π y)) ?_ hi
      refine ae_iff.2 (measure_mono_null (fun y hy => ?_) (hnull (nonzeroLocus t) hzt ε))
      exact fun h => hy ((hbasic.2.1 (π y)).2 h)
    have h1 := one 1 hint.1
    have h2 := one (-1) hint.2
    have := (h1.sub h2).const_mul (Δ.mult z : ℝ)
    simp only [cycInt, Mix.int, MLine.logSec] at this ⊢
    convert this using 2
    ring
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoRegularisedLogNormMixedMeasureDivisorsStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.tendsto_regularisedLogNorm_mixedMeasure_divisors : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (N : MLine p σ) (t : N.B.Sec), (genericPoint X ∈ nonzeroLocus t → ∀ L : Fin (e + 1) → MLine p σ, Tendsto (fun n : ℕ => Mix.int L fun y => Real.log (N.φ.nsq (secVal p σ t) y + 1 / ((n : ℝ) + 1))) atTop (𝓝 (2 * Mix.int L (N.logSec t)))) ∧ ∀ (L : Fin e → MLine p σ) (Δ : CartierDiv X), (∀ z, Δ.mult z ≠ 0 → z ∈ nonzeroLocus t) → Tendsto (fun n : ℕ => ∑ᶠ z, (Δ.mult z : ℝ) * cycInt L (fun y => Real.log (N.φ.nsq (secVal p σ t) y + 1 / ((n : ℝ) + 1))) z) atTop (𝓝 (2 * ∑ᶠ z, (Δ.mult z : ℝ) * cycInt L (N.logSec t) z)) := by
  first | exact @GlobalTheory.Mix.tendsto_logReg | exact GlobalTheory.Mix.tendsto_logReg | (intros; apply GlobalTheory.Mix.tendsto_logReg <;> assumption)
end
end
