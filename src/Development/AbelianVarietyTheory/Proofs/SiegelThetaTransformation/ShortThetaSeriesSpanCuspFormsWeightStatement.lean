module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
public import Formalism.LocalToGlobal.ProjectiveLattices.RecPJThAllNeBot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SpanSteps
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CuspFormFrameReadingsLinearIndependent
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
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HolomorphicCuspFormsFramesLeSpanShortThetaReadinStatement
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.TypeStar

-- Source module: Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CuspFormFrameReadingsLinearIndependentStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

theorem _root_.GlobalTheory.T.cuspForm_frame_readings_linearIndependent : ∀ (D : D7) (T : Top D), LawsM T.toCore → ∀ j, InR D j → ∀ a n, JInjRd T j a n := by
  first | exact @GlobalTheory.Dict.readings_independent | exact GlobalTheory.Dict.readings_independent | (intros; apply GlobalTheory.Dict.readings_independent <;> assumption)
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SpanInst

section

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra

theorem indepToC_comp {K : Type*} [Field K] {σ : K →+* ℂ} {C C' : Type*} [AddCommGroup C] [Module K C]
    [AddCommGroup C'] [Module K C'] {W : Type*} [AddCommGroup W] [Module ℂ W] (J : C →ₛₗ[σ] W)
    (hJ : IndepToC J) (ι : C' →ₗ[K] C) (hι : Function.Injective ι) : IndepToC (J.comp ι) := by
  intro n b hb
  exact hJ n (fun i => ι (b i)) (hb.map' ι (LinearMap.ker_eq_bot.mpr hι))

variable {D : D7} {T : Top D}

set_option synthInstance.maxHeartbeats 400000 in
def jRec (j : ℕ) (ka : WeightFamilies.Wt D j) :
    cutR T.C j ka →ₛₗ[T.σ₀] FDSec (T.U j T.σ₀).X :=
  (rdC (T.U j) T.σ₀ (wtA ka) ka.n).comp (Submodule.inclusion (cutR_le T.C j ka))

set_option synthInstance.maxHeartbeats 400000 in
theorem spanAt_rec (h : LawsP T) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (ka : WeightFamilies.Wt D j)
    (hJ : JInjRd T j (wtA ka) ka.n) (A : Set (FDSec (T.U j T.σ₀).X))
    (hG : holSub0 (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA ka) ka.n) ≤ Submodule.span ℂ A)
    (hA : A ⊆ Submodule.span ℂ (jRec (T := T) j ka ''
      (((recX h) j h1 h2).shortTh ka : Set ((recB h.toLawsCore).Cusp j ka)))) :
    SpanAt ((recX h) j h1 h2) ka :=
  spanAt_of_chain ((recX h) j h1 h2) ka (jRec (T := T) j ka)
    (indepToC_comp _ hJ _ (Submodule.inclusion_injective _))
    (holSub0 (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA ka) ka.n)) A
    (fun _ => rdC_mem_holSub0 T.good_σ₀ (wtA ka) ka.n _) hG hA

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ShortThetaSeriesSpanCuspFormsWeight

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.Dict



theorem spanAt_record : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T), LawsSh T → GamAt T.toCore → 0 < badN D → (∀ j, InR D j → ∀ k k', ((T.U j T.σ₀).X k).Gm = ((T.U j T.σ₀).X k').Gm ∧ ((T.U j T.σ₀).X k).ξ0 = ((T.U j T.σ₀).X k').ξ0) → ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (ka : WeightFamilies.Wt D j), LastPos (T.Q.Dw j) (wtA ka) → 8 * D.R.f * D.R.r + 4 ≤ ka.n → SpanAt ((recX h) j h1 h2) ka := by
  intro hC D T h hSh hG hb hU j h1 h2 ka hL hn
  have hj : InR D j := ⟨h1, h2⟩
  have hM : LawsM T.toCore := h.toLawsCore.toLawsM
  refine ReciprocityTheory.ChartRestriction.G.PullbackSections.spanAt_rec h j h1 h2 ka (GlobalTheory.T.cuspForm_frame_readings_linearIndependent D T hM j hj _ _) _
    (GlobalTheory.T.holomorphicCuspForms_frames_le_span_shortThetaReadings hC D T hM hSh hG hb hU j hj ka hn) ?_
  rintro _ ⟨x, hx, rfl⟩

  have hxC : x ∈ T.C j ka :=
    hSh.shCusp j hj (wtA ka) ka.n (dom_wtA ka) hL (dom_wtA ka) hL hx
  have hxR : x ∈ cutR T.C j ka := by
    show x ∈ T.C j ka ⊓ ⨅ (_ : ¬InR D j), ⊥
    exact Submodule.mem_inf.2 ⟨hxC, Submodule.mem_iInf _ |>.2 fun hn' => absurd hj hn'⟩
  apply Submodule.subset_span
  refine ⟨⟨x, hxR⟩, ?_, rfl⟩
  exact (Submodule.subset_span hx : x ∈ Submodule.span (𝓞 T.Q.c.F) (T.sh j ka))

end GlobalTheory.Dict
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ShortThetaSeriesSpanCuspFormsWeightStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

theorem _root_.GlobalTheory.T.shortThetaSeries_span_cuspForms_weight : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T), LawsSh T → GamAt T.toCore → 0 < badN D → (∀ j, InR D j → ∀ k k', ((T.U j T.σ₀).X k).Gm = ((T.U j T.σ₀).X k').Gm ∧ ((T.U j T.σ₀).X k).ξ0 = ((T.U j T.σ₀).X k').ξ0) → ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (ka : WeightFamilies.Wt D j), LastPos (T.Q.Dw j) (wtA ka) → 8 * D.R.f * D.R.r + 4 ≤ ka.n → SpanAt ((recX h) j h1 h2) ka := by
  first | exact @GlobalTheory.Dict.spanAt_record | exact GlobalTheory.Dict.spanAt_record | (intros; apply GlobalTheory.Dict.spanAt_record <;> assumption)
end
end
