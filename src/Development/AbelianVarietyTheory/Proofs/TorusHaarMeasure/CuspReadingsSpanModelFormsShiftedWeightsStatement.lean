module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CuspFormFamiliesComplexCombinationOfReadings
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
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FinrankHost
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GamAtOfLawsCore
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.WeightsBelow
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.HarmonicGermValueChartIndependentStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArithmeticCMKnownTheoremsProofStatement
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.CarchAt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmFamilyFunctionalsDetectLowCoefficients
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.VanishingLowCoefficientReadingsSpanModelsStatement
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Basify
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CuspFormFamiliesComplexCombinationOfReadingsStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

theorem _root_.GlobalTheory.T.cuspForm_families_complex_combination_of_readings : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) , LawsSh T → GamAt T.toCore → 0 < badN D → (∀ j, InR D j → ∀ k k', ((T.U j T.σ₀).X k).Gm = ((T.U j T.σ₀).X k').Gm ∧ ((T.U j T.σ₀).X k).ξ0 = ((T.U j T.σ₀).X k').ξ0) → ∀ u : WeightFamilies.Wt D j, 8 * D.R.f * D.R.r + 4 ≤ u.n → LastPos (T.Q.Dw j) (wtA u) → RdOnto h j u := by
  first | exact @GlobalTheory.Shares.rdOnto_rec | exact GlobalTheory.Shares.rdOnto_rec | (intros; apply GlobalTheory.Shares.rdOnto_rec <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmFamilyFunctionalsDetectLowCoefficientsStatement

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.BasicNotions Formalism.L2.LamCM GlobalTheory.ArcCM

theorem _root_.GlobalTheory.T.cmFamilyFunctionals_detect_lowCoefficients : Known → ∀ (D : D7) (T : Core D) (h : LawsCore T) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ), GlobalTheory.RunIn.GamAt T → InR D j → j < D.R.m → 3 ≤ D.R.r → 0 < Tt → 0 < cc → DetectQ h j ka CR Tt cc := by
  first | exact @GlobalTheory.ArcCM.detectQ_of_known | exact GlobalTheory.ArcCM.detectQ_of_known | (intros; apply GlobalTheory.ArcCM.detectQ_of_known <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.CuspReadingsSpanModelFormsShiftedWeights

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

namespace GlobalTheory.RunJoin




theorem onto_of_page : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (EX : ErrX D) (p : ℕ), ParOK T EX p j → PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → (∀ k : ℕ, GlobalTheory.Shares.RdOnto h j (addL wF wL k)) ∧ GlobalTheory.Shares.MggOnto h j 7 Tn (cc D large₂ C2 A2 7 wL) ka := by
  intro D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 EX p hPar hPage
  have hG : GlobalTheory.RunIn.GamAt T.toCore := GlobalTheory.RunIn.gamAt_of_lawsCore D T.toCore h.toLawsCore
  obtain ⟨hA, hB, -, -⟩ := GlobalTheory.RunWeights.weights_below D _ _ j (recPJ h j hj) large₂ H C2 A2 7 CT ka wL wF Tn nP nW h0
    hj.1 hPage.hyp
  have key : ∀ u : WeightFamilies.Wt D j, 8 * D.R.f * D.R.r + 4 ≤ u.n → u.LastPos → GlobalTheory.Shares.RdOnto h j u := fun u hn hl =>
    GlobalTheory.T.cuspForm_families_complex_combination_of_readings GlobalTheory.T.harmonic_germ_value_chart_independent D T h j hj hPar.sh hG hPar.bad hPar.same u hn
      (ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.lastPos_wtA h hj u hl)
  refine ⟨fun k => key _ ?_ ?_, ?_⟩
  · have h1 := hB wF (by simp)
    have e : (addL wF wL k).n = wF.n + k * wL.n := rfl
    omega
  · intro τ i hi
    have h1 := (hA wF (by simp)).2.2.2 τ i hi
    have e : (addL wF wL k).aP τ i = wF.aP τ i + k * wL.aP τ i := rfl
    omega
  · refine GlobalTheory.T.vanishing_low_coefficient_readings_span_models D T h j hj ka 7 Tn _ ?_
      (key ka (hB ka (by simp)) (hA ka (by simp)).2.2.2)
    intro hlt
    obtain ⟨t1, t2, t3, t4, t5, t6⟩ := hPage.tie
    have ht : TieC ⟨1, 2, 1, 2, 1, 2, 1, 4, 7⟩ H 1 4 0 11 C2 A2 7 :=
      ⟨t1, t2, t3, t4, t5, rfl, rfl, t6, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩
    obtain ⟨hc, -, -, -, -, h2, h11⟩ := GlobalTheory.ExtraWeight.numbers D _ _ j (recPJ h j hj) _ _ _ _ _ large₂ H C2 A2 7 CT ka wL wF
      Tn nP nW h0 hPage.hyp ht hPage.page hlt hj.1 (le_trans (by norm_num) hPage.df)
    have hT : 0 < Tn := by nlinarith
    exact GlobalTheory.T.cmFamilyFunctionals_detect_lowCoefficients
      GlobalTheory.T.arithmeticCMKnownTheorems_proof D T.toCore h.toLawsCore j ka 7 Tn _ hG hj hlt
      (le_trans (by norm_num) hPage.r8) (by exact_mod_cast hT) hc

end GlobalTheory.RunJoin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.CuspReadingsSpanModelFormsShiftedWeightsStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

theorem _root_.GlobalTheory.T.cuspReadings_span_model_forms_shifted_weights : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (EX : ErrX D) (p : ℕ), ParOK T EX p j → PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → (∀ k : ℕ, GlobalTheory.Shares.RdOnto h j (addL wF wL k)) ∧ GlobalTheory.Shares.MggOnto h j 7 Tn (cc D large₂ C2 A2 7 wL) ka := by
  first | exact @GlobalTheory.RunJoin.onto_of_page | exact GlobalTheory.RunJoin.onto_of_page | (intros; apply GlobalTheory.RunJoin.onto_of_page <;> assumption)
end
end
