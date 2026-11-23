module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
public import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementS
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CuspFormValueLeSupNormAtOrthonormalFrame
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsMetricConjugateFramedPoint
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Formalism.LocalToGlobal.ProjectiveLattices.AxHSupA
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsMetricDataCmPointComplexEmbeddingStatement
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FramePolynomialEquivariantAndNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MetricChangeOfFrameStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFrameChangeByMatrices

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CuspFormValueLeSupNormAtOrthonormalFrameStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT


theorem _root_.GlobalTheory.T.cuspForm_value_le_supNorm_at_orthonormal_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = ξ) → 1 ≤ Dw.p + Dw.q → ∀ a n, Dom a n → ∀ F ∈ cusp Xo c U a n, ∀ σ, GoodEmb c σ → ∀ (y : FrPt Xo c (CAt σ)) (N : ℝ), IsMetric y N (fun _ => 1) → cabs (evR Xo c F y) ≤ Real.sqrt N ^ n * supC Xo c U ξ σ a n F := by
  first | exact @GlobalTheory.LamT.OrthoBound.cabs_evR_le_supC | exact GlobalTheory.LamT.OrthoBound.cabs_evR_le_supC | (intros; apply GlobalTheory.LamT.OrthoBound.cabs_evR_le_supC <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsMetricConjugateFramedPointStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT


theorem _root_.GlobalTheory.T.isMetric_conjugate_framedPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (y : FrPt Xo c (CAt σ)) (y' : FrPt Xo c (CAt ((starRingEnd ℂ).comp σ))) (N : ℝ) (Gr : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ)), 1 ≤ Dw.p + Dw.q → FrMap (FrameNorm.conjAlg σ) y y' → IsMetric y N Gr → IsMetric y' N (fun b => (Gr b).map (starRingEnd ℂ)) := by
  first | exact @GlobalTheory.LamT.isMetric_conj | exact GlobalTheory.LamT.isMetric_conj | (intros; apply GlobalTheory.LamT.isMetric_conj <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CuspFormBoundedBySupNormAtGoodEmbeddingAllEmbedd

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT

theorem cusp_bound_allEmb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = ξ) → 1 ≤ Dw.p + Dw.q → ∀ a n, Dom a n → ∀ F ∈ cusp Xo c U a n, ∀ (σ : c.F →+* ℂ) (y : FrPt Xo c (CAt σ)) (N : ℝ), IsMetric y N (fun _ => 1) → cabs (evR Xo c F y) ≤ Real.sqrt N ^ n * supC Xo c U ξ (goodOf c σ) a n F := by
  intro E _ _ _ H Dw l Xo c r U ξ hU hξ hpq a n hd F hF σ y N hm
  by_cases hσ : GoodEmb c σ
  · have e : goodOf c σ = σ := if_pos hσ
    rw [e]
    exact GlobalTheory.T.cuspForm_value_le_supNorm_at_orthonormal_frame E H Dw l Xo c r U ξ hU hξ hpq a n hd F hF σ hσ y N hm
  · have e : goodOf c σ = (starRingEnd ℂ).comp σ := if_neg hσ
    have hg : GoodEmb c ((starRingEnd ℂ).comp σ) := e ▸ goodEmb_goodOf c σ
    rw [e]
    have hB : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
    obtain ⟨y', hy'⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c (CAt σ)
      (CAt ((starRingEnd ℂ).comp σ)) (FrameNorm.conjAlg σ) y
    have hm' := GlobalTheory.T.isMetric_conjugate_framedPoint E H Dw l Xo c σ y y' N (fun _ => 1) hpq hy' hm
    have h1 : (fun b : E →+* ℂ => ((1 : Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ)).map (starRingEnd ℂ)) =
        fun _ => 1 := funext fun b => Matrix.map_one _ (map_zero _) (map_one _)
    rw [h1] at hm'
    have hb := GlobalTheory.T.cuspForm_value_le_supNorm_at_orthonormal_frame E H Dw l Xo c r U ξ hU hξ hpq a n hd F hF _ hg y' N hm'
    haveI : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
    have hev := evR_frMap (GlobalTheory.Frames.algebraic_laws hB E H Dw l Xo c).2.2.1 F (cusp_le_sec Xo c U a n hF).1
      (FrameNorm.conjAlg σ) y (GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw l Xo c (CAt σ) y) y' hy'
    rw [hev] at hb
    refine le_trans (le_of_eq ?_) hb
    exact (Complex.norm_conj _).symm

end GlobalTheory.LamT
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CuspFormBoundedBySupNormAtGoodEmbeddingAllEmbeddStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT


theorem _root_.GlobalTheory.T.cuspForm_bounded_by_supNorm_at_good_embedding_all_embeddings : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = ξ) → 1 ≤ Dw.p + Dw.q → ∀ a n, Dom a n → ∀ F ∈ cusp Xo c U a n, ∀ (σ : c.F →+* ℂ) (y : FrPt Xo c (CAt σ)) (N : ℝ), IsMetric y N (fun _ => 1) → cabs (evR Xo c F y) ≤ Real.sqrt N ^ n * supC Xo c U ξ (goodOf c σ) a n F := by
  first | exact @GlobalTheory.LamT.cusp_bound_allEmb | exact GlobalTheory.LamT.cusp_bound_allEmb | (intros; apply GlobalTheory.LamT.cusp_bound_allEmb <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ArchimedeanHypothesisLowerBoundCmPoint

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT



theorem step5Arch_cm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] [DecidableEq (E →+* ℂ)] (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = ξ) → 1 ≤ Dw.p + Dw.q → ∀ (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La → ∀ a n, Dom a n → ∀ F ∈ cusp Xo c U a n, ∀ G : MvPolynomial (FrVar Dw.mult) z.K, IsFrPoly F z.y G → ∀ σ : z.K →+* ℂ, Step5Arch z.e z.Tl.dual z.LamL z.ℓ z.U G (fun b i => a (b, i)) n La (supC Xo c U ξ (goodOf c (σ.comp (algebraMap c.F z.K))) a n F) σ := by
  intro E _ _ _ H Dw l Xo c _ _ r U ξ hU hξ hpq z f La hz a n hD F hF G hG σ
  obtain ⟨yσ, hy⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c z.K
    (CAt (σ.comp (algebraMap c.F z.K))) (embAlg σ) z.y
  obtain ⟨Hm, hpd, hLam, hU', hmet⟩ := GlobalTheory.T.exists_metricData_cmPoint_complexEmbedding E H Dw l Xo c z f La hz σ yσ hy
  have hsec : F ∈ sec Xo c a n := Formalism.L2.Pj.cusp_le_sec Xo c U a n hF
  refine ⟨Hm, hpd, hLam, hU', (GlobalTheory.T.framePolynomial_equivariant_and_ne_zero E H Dw l Xo c z.K z.y a n F hsec G hG).1 σ, ?_⟩
  intro Y hY
  have hdet : ∀ b, IsUnit (Y b).det := by
    intro b
    have h := congrArg Matrix.det (hY b)
    rw [Matrix.det_mul, Matrix.det_one] at h
    exact IsUnit.of_mul_eq_one_right _ h
  obtain ⟨y', hy', -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c (CAt (σ.comp (algebraMap c.F z.K))) yσ
    (fun b => (Y b).transpose) 1 (fun b => by
      have := hdet b
      rwa [← Matrix.det_transpose] at this)
  have hm' := GlobalTheory.T.metric_change_of_frame E H Dw l Xo c _ yσ y' _ _ Y 1 one_ne_zero hy' hmet
  have e1 : (fun b => (Y b).conjTranspose * gramBlock z.e z.U Hm σ b * Y b) = fun _ => 1 := funext hY
  rw [e1, norm_one, one_pow, _root_.one_mul] at hm'
  have hb := GlobalTheory.T.cuspForm_bounded_by_supNorm_at_good_embedding_all_embeddings E H Dw l Xo c r U ξ hU hξ hpq a n hD F hF _ y' _ hm'
  have hev := hG _ (embAlg σ) yσ y' Y hdet hy hy'
  have hT : 0 < z.Tl.n σ := by
    obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hT, -⟩, -⟩ := hz
    exact hT.2 σ
  rw [Real.sqrt_sq hT.le, hev] at hb
  have hb' : ‖evalFr (MvPolynomial.map σ G) Y‖ ≤
      z.Tl.n σ ^ n * supC Xo c U ξ (goodOf c (σ.comp (algebraMap c.F z.K))) a n F := hb
  have hd : z.Tl.dual.n σ = (z.Tl.n σ)⁻¹ := rfl
  rw [hd, inv_pow, ← div_eq_mul_inv, div_le_iff₀ (pow_pos hT n), _root_.mul_comm]
  exact hb'

end GlobalTheory.LamT
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ArchimedeanHypothesisLowerBoundCmPointStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT


theorem _root_.GlobalTheory.T.archimedeanHypothesis_lowerBound_cmPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] [DecidableEq (E →+* ℂ)] (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = ξ) → 1 ≤ Dw.p + Dw.q → ∀ (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La → ∀ a n, Dom a n → ∀ F ∈ cusp Xo c U a n, ∀ G : MvPolynomial (FrVar Dw.mult) z.K, IsFrPoly F z.y G → ∀ σ : z.K →+* ℂ, Step5Arch z.e z.Tl.dual z.LamL z.ℓ z.U G (fun b i => a (b, i)) n La (supC Xo c U ξ (goodOf c (σ.comp (algebraMap c.F z.K))) a n F) σ := by
  first | exact @GlobalTheory.LamT.step5Arch_cm | exact GlobalTheory.LamT.step5Arch_cm | (intros; apply GlobalTheory.LamT.step5Arch_cm <;> assumption)
end
end
