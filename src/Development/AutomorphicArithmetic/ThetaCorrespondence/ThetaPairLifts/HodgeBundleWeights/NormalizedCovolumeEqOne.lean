module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OneMeasureSizes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogLowestKTypeWeylDimensionLeOfSizeBoundsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneLeDimAt
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
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasAtOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CovolumeRatioEqIndex
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.HaarMeasureFundamentalDomainNeZeroOfCocompact
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.LevelSubgroupIndexBounded
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.PlugPairs
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.VolumeFundamentalDomainNeTopOfFiniteCovolume
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.PlugPairs
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.VolumeFundamentalDomainNeTopOfFiniteCovolume

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneLeDimAtStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta

theorem _root_.GlobalTheory.T.one_le_dimAt' : ∀ (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau), 1 ≤ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ := by
  first | exact @GlobalTheory.DimAtOne.one_le_dimAt | exact GlobalTheory.DimAtOne.one_le_dimAt | (intros; apply GlobalTheory.DimAtOne.one_le_dimAt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogMeasureRatioLe

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta

namespace GlobalTheory.OneMeasureRatio

theorem log_r_add_three_le (D : D7) (L : ℝ) (hL : GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.Sizes D L) :
    Real.log ((D.R.r : ℝ) + 3) ≤ L := by
  have hr : 6 ≤ D.R.r := by
    unfold Ranks.r; have := D.R.two_le_m; have := D.R.m_add_three_le_k; omega
  have hf : 2 ≤ D.R.f := by
    unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) D.R.ord_pos; omega
  have hn : D.R.r ≤ D.R.nV := by unfold Ranks.nV; omega
  have hr' : (6 : ℝ) ≤ D.R.r := by exact_mod_cast hr
  have hf' : (2 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have hn' : (D.R.r : ℝ) ≤ D.R.nV := by exact_mod_cast hn
  have h1 := hL.1
  rw [← Real.log_exp L]
  refine Real.log_le_log (by positivity) ?_
  have a1 : 2 * (D.R.r : ℝ) ≤ (D.R.f : ℝ) * D.R.r := mul_le_mul_of_nonneg_right hf' (by positivity)
  have a2 : 2 * (D.R.r : ℝ) * D.R.r ≤ (D.R.f : ℝ) * D.R.r * D.R.nV :=
    mul_le_mul a1 hn' (by positivity) (by positivity)
  have : (D.R.r : ℝ) + 3 ≤ (D.R.f : ℝ) * D.R.r * D.R.nV := by nlinarith
  linarith

end GlobalTheory.OneMeasureRatio
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.LogMeasureRatioBounded

section

@[expose] public section

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta
namespace GlobalTheory.OneMeasureRatio
theorem log_covolume_ratio_le : ∀ (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ) (μ : MeasureTheory.Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i))) (hF : IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i P) μ 𝓕) (L : ℝ) (hL : GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.Sizes D L), Real.log (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.ratio D i μ 𝓕) ≤ 122 * (D.R.f * (D.R.r : ℝ) ^ 2 * L) := by
  intro hP D Tu C t0 hC i P μ 𝓕 hF L hL
  have h0 := _root_.GlobalTheory.T.fundamentalDomain_volume_ne_zero hP D Tu C t0 hC i P μ 𝓕 hF
  have ht := _root_.GlobalTheory.T.quotient_measure_lt_top_of_finite_covolume hP D Tu C t0 hC i P μ 𝓕 hF
  have hv := _root_.MainStatements.Tam.Plug.tamagawa_pairs_compatible hP D Tu C t0 hC i P μ 𝓕 hF L hL
  have hd : ∀ τ, Real.log (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ) ≤ 3 / 2 * (D.R.r : ℝ) ^ 2 * L :=
    GlobalTheory.T.log_lowestKTypeWeylDimension_le_of_sizeBounds D i L hL
  have hd1 : ∀ τ, 1 ≤ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ := GlobalTheory.DimAtOne.one_le_dimAt D i
  have hvpos : 0 < (μ 𝓕).toReal := ENNReal.toReal_pos h0 ht
  have hdpos : ∀ τ, 0 < GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ := fun τ => zero_lt_one.trans_le (hd1 τ)
  unfold GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.ratio
  rw [Real.log_mul hvpos.ne' (Finset.prod_pos fun τ _ => hdpos τ).ne',
    Real.log_prod (fun τ _ => (hdpos τ).ne')]
  have hsum : ∑ τ, Real.log (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ) ≤ ∑ _τ : D.what₂.Tau, 3 / 2 * (D.R.r : ℝ) ^ 2 * L :=
    Finset.sum_le_sum fun τ _ => hd τ
  rw [Finset.sum_const, Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul] at hsum
  have hlog := log_r_add_three_le D L hL
  have hL0 : 0 ≤ L := le_trans (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) D.R.r; linarith)) hlog
  have hfr : 0 ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 := by positivity
  have h3 := mul_le_mul_of_nonneg_left hlog hfr
  have h4 : 0 ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * L := mul_nonneg hfr hL0
  nlinarith
end GlobalTheory.OneMeasureRatio
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta

theorem _root_.GlobalTheory.T.log_measure_ratio_bounded : ∀ (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ) (μ : MeasureTheory.Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i))) (hF : IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i P) μ 𝓕) (L : ℝ) (hL : GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.Sizes D L), Real.log (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.ratio D i μ 𝓕) ≤ 122 * (D.R.f * (D.R.r : ℝ) ^ 2 * L) := by
  first | exact @_root_.GlobalTheory.OneMeasureRatio.log_covolume_ratio_le | exact _root_.GlobalTheory.OneMeasureRatio.log_covolume_ratio_le | (intros; apply _root_.GlobalTheory.OneMeasureRatio.log_covolume_ratio_le <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.NormalizedCovolumeEqOne

section

@[expose] public section

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta
namespace GlobalTheory.OneMeasureAll
theorem covolume_measure_eq_one : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.OneMeasure D := by
  intro hP D Tu C t0 hC i P
  refine ⟨_root_.GlobalTheory.T.level_subgroup_index_bounded hP D Tu C t0 hC i P, fun τ => GlobalTheory.T.one_le_dimAt' D i τ, fun μ 𝓕 hF =>
    ⟨_root_.GlobalTheory.T.fundamentalDomain_volume_ne_zero hP D Tu C t0 hC i P μ 𝓕 hF, _root_.GlobalTheory.T.quotient_measure_lt_top_of_finite_covolume hP D Tu C t0 hC i P μ 𝓕 hF,
      _root_.GlobalTheory.T.covolume_ratio_eq_index hP D Tu C t0 hC i P μ 𝓕 hF, fun L hL =>
        ⟨fun τ => GlobalTheory.T.log_lowestKTypeWeylDimension_le_of_sizeBounds D i L hL τ, _root_.MainStatements.Tam.Plug.tamagawa_pairs_compatible hP D Tu C t0 hC i P μ 𝓕 hF L hL,
          _root_.GlobalTheory.T.log_measure_ratio_bounded hP D Tu C t0 hC i P μ 𝓕 hF L hL⟩⟩⟩
end GlobalTheory.OneMeasureAll
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions

theorem _root_.GlobalTheory.T.normalized_covolume_eq_one : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.OneMeasure D := by
  first | exact @_root_.GlobalTheory.OneMeasureAll.covolume_measure_eq_one | exact _root_.GlobalTheory.OneMeasureAll.covolume_measure_eq_one | (intros; apply _root_.GlobalTheory.OneMeasureAll.covolume_measure_eq_one <;> assumption)
end
end
end
