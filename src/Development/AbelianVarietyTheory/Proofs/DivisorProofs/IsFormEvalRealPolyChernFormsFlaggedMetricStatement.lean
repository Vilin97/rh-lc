module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormFieldDbarCohomologousTwoConnectionsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedFrameEventuallyFrameNearComplexPointStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlaggedBundleMetricSmoothUnitEtaleChartStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHolomorphicUnitMatrixAtRationalMatrixValuesStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothFormsCalculusHolomorphicAtlas
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGramConnectionPairOfTwoFlaggedMetrics

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem isGramPair_of_isMetricFr : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m k : ι → ℕ) (E : Fr (ratOf X) m k) (H H' : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → IsMetricFr E H' → ∀ τ, IsGramPair (atlas X σ) (gramAt E H τ) (gramAt E H' τ) := by
  intro F _ σ X ι _ m k E H H' hH hH' τ
  have hA (y : CxPts X.str σ) := (E.nonempty (under y)).choose_spec
  refine ⟨fun y => ⟨(GlobalTheory.T.flaggedBundleMetric_smoothUnit_etaleChart F σ X ι m k E H hH y _ (hA y) τ).1,
    (GlobalTheory.T.flaggedBundleMetric_smoothUnit_etaleChart F σ X ι m k E H' hH' y _ (hA y) τ).1⟩, fun y => ?_⟩
  filter_upwards [GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ X ι m k E y _ (hA y)] with z hz
  have hP := (Fr.mem_iff hz).1 (hA z) τ
  have hT := GlobalTheory.T.isHolomorphicUnitMatrixAt_rational_matrix_values F σ X (m τ) _ z (fun i j => mem_O_ratOf.1 (hP.1 i j)) hP.2.1 (mem_O_ratOf.1 hP.2.2.1)
  refine ⟨_, _, _, hT, hT, hT, ?_⟩
  filter_upwards [GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ X ι m k E z _ hz, GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ X ι m k E z _ (hA z)] with w h1 h2
  exact ⟨hH.trans w _ h1 _ h2 τ, hH'.trans w _ h1 _ h2 τ⟩

end GlobalTheory.ChernCalc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGramConnectionPairOfTwoFlaggedMetricsStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

theorem _root_.GlobalTheory.T.isGramConnectionPair_of_two_flagged_metrics : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m k : ι → ℕ) (E : Fr (ratOf X) m k) (H H' : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → IsMetricFr E H' → ∀ τ, IsGramPair (atlas X σ) (gramAt E H τ) (gramAt E H' τ) := by
  first | exact @GlobalTheory.ChernCalc.isGramPair_of_isMetricFr | exact GlobalTheory.ChernCalc.isGramPair_of_isMetricFr | (intros; apply GlobalTheory.ChernCalc.isGramPair_of_isMetricFr <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothFormsCalculusHolomorphicAtlasStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.LineForm
open scoped Classical

theorem _root_.GlobalTheory.T.smoothForms_calculus_holomorphicAtlas : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n),
    A.IsForm 1 ∧ (∀ (c : ℂ) (α β : A.Fld), A.IsForm α → A.IsForm β → A.IsForm (α + β) ∧ A.IsForm (α * β) ∧ A.IsForm (c • α) ∧
      A.IsForm (A.del α) ∧ A.IsForm (A.dbar α) ∧ A.del (α + β) = A.del α + A.del β ∧ A.dbar (α + β) = A.dbar α + A.dbar β ∧
      A.del (c • α) = c • A.del α ∧ A.dbar (c • α) = c • A.dbar α) ∧
    (∀ (w : A.Pt → Ev n) (β : A.Fld), A.IsForm (fld A w) → A.IsForm β →
      A.del (fld A w * β) = A.del (fld A w) * β + fld A w * A.del β ∧ A.dbar (fld A w * β) = A.dbar (fld A w) * β + fld A w * A.dbar β) ∧
    (∀ (ι : Type) (w : ι → A.Pt → Ev n) (P : MvPolynomial ι ℝ), (∀ i, A.IsForm (fld A (w i))) → A.IsForm (evalF A w P) ∧
      ((∀ i, A.del (fld A (w i)) = 0) → A.del (evalF A w P) = 0) ∧ ((∀ i, A.dbar (fld A (w i)) = 0) → A.dbar (evalF A w P) = 0)) ∧
    ∀ (M' : Type) [TopologicalSpace M'] (n' : ℕ) (A' : HolAtlas M' n') (f : M' → M), A.IsHolo A' f →
      A.pullback A' f 1 = 1 ∧ ∀ (c : ℂ) (α β : A.Fld), A.pullback A' f (α + β) = A.pullback A' f α + A.pullback A' f β ∧
        A.pullback A' f (α * β) = A.pullback A' f α * A.pullback A' f β ∧ A.pullback A' f (c • α) = c • A.pullback A' f α ∧
        (A.IsForm α → A'.IsForm (A.pullback A' f α) ∧ A'.del (A.pullback A' f α) = A.pullback A' f (A.del α) ∧
          A'.dbar (A.pullback A' f α) = A.pullback A' f (A.dbar α)) := by
  first | exact @GlobalTheory.formCalculus | exact GlobalTheory.formCalculus | (intros; apply GlobalTheory.formCalculus <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormEvalRealPolyChernFormsFlaggedMetric

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem isForm_evalF_chernF : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m k : ι → ℕ)
    (E : Fr (ratOf X) m k) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H →
    ∀ R : MvPolynomial (ι × ℕ) ℝ, (atlas X σ).IsForm (evalF (atlas X σ) (chernF E H) R) := by
  intro F _ σ X ι _ m k E H h R
  exact ((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ _ (atlas X σ)).2.2.2.1 _ (chernF E H) R fun x =>
    (GlobalTheory.T.chernFormField_dbarCohomologous_two_connections _ _ (atlas X σ) _ _ _ (GlobalTheory.T.isGramConnectionPair_of_two_flagged_metrics F σ X ι m k E H H h h x.1) x.2).1).1

end GlobalTheory.ChernCalc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormEvalRealPolyChernFormsFlaggedMetricStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

theorem _root_.GlobalTheory.T.isForm_evalRealPoly_chernForms_flaggedMetric : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m k : ι → ℕ) (E : Fr (ratOf X) m k) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ R : MvPolynomial (ι × ℕ) ℝ, (atlas X σ).IsForm (evalF (atlas X σ) (chernF E H) R) := by
  first | exact @GlobalTheory.ChernCalc.isForm_evalF_chernF | exact GlobalTheory.ChernCalc.isForm_evalF_chernF | (intros; apply GlobalTheory.ChernCalc.isForm_evalF_chernF <;> assumption)
end
end
