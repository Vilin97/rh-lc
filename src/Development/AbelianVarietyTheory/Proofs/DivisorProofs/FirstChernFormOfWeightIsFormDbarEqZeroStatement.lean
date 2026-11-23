module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormsFrameIndependentClosedStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
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
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernRealClosed

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.LineForm
open scoped Classical

set_option autoImplicit false

namespace GlobalTheory.LineForm.FirstChern

open Filter Topology GlobalTheory.HermFrame GlobalTheory.Points
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder ComplexConjugate

theorem chernAt_exp_neg {n : ℕ} {u : V n → ℝ} {v : V n} (hu : ContDiffAt ℝ 2 u v) :
    chernAt (fun x => (Matrix.of fun _ _ : Unit => ((Real.exp (-u x) : ℝ) : ℂ))) v 1 = ofValues (ddc u v) := by
  have h1 (G : V n → Matrix Unit Unit ℂ) : chernAt G v 1 = ofValues (chernOne G v) := by
    unfold chernAt ofValues GlobalTheory.GoodMetric.chernPoly chernOne
    rw [Matrix.coeff_charpolyRev_eq_neg_trace, Matrix.trace_neg, neg_neg, pow_one]

    simp only [Matrix.trace, Matrix.diag, GlobalTheory.GoodMetric.curvPoly, Matrix.of_apply, map_sum, map_mul,
    MvPolynomial.aeval_C, MvPolynomial.aeval_X, ← Algebra.smul_def, mul_smul, ← Finset.smul_sum, Finset.sum_smul]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
  rw [h1]
  congr 1
  funext ξ η
  rw [chernOne_line (f := fun x => Real.exp (-u x)) (Real.contDiff_exp.contDiffAt.comp v hu.neg) (Real.exp_ne_zero _)
    (Eventually.of_forall fun _ => rfl)]
  simp only [Real.log_exp, ddc, leviForm_neg]
  simp

end GlobalTheory.LineForm.FirstChern
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernFormOfWeightIsFormDbarEqZero

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

namespace GlobalTheory.ChernCalc.FirstChernW

open GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.LineForm.FirstChern

theorem smoothOn_atlas {F : Type} [Field F] {X : Var F} {σ : F →+* ℂ} {m : Type} {U : Set (CxPts X.str σ)}
    {G : CxPts X.str σ → Matrix m m ℂ} (H : ∀ y ∈ U, MInfAt G y) (i j : m) :
    (atlas X σ).SmoothOn U fun y => G y i j := fun c v hv => by
  have := (H _ hv.2 i j).contDiffAt_chart c (c.e.map_target hv.1)
  erw [c.e.right_inv hv.1] at this
  exact this.contDiffWithinAt

theorem c1W_isForm_and_dbar_eq_zero : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (L : LB X.X) (ψ : Weight X.str σ L),
    ψ.IsCInf → (atlas X σ).IsForm (fld (atlas X σ) (c1W ψ)) ∧ (atlas X σ).dbar (fld (atlas X σ) (c1W ψ)) = 0 := by
  intro F _ σ X L ψ hψ
  have hφ : ∀ a (x : (atlas X σ).Pt), x.pt ∈ ptsIn X.str σ (L.U a) →
      ContDiffAt ℝ 2 (fun v => ψ.φ a (x.ch.symm v)) x.crd := by
    intro a x hx
    exact ((vInfAt_iff_cInfAt.2 (hψ a _ hx)).contDiffAt_chart x.1.1 x.2).of_le (by norm_cast)
  obtain ⟨hfr, hP⟩ := GlobalTheory.T.chernForms_frame_independent_closed (atlas X σ) (ι := Unit) (fun a => ptsIn X.str σ (L.U a)) (fun _ => isOpen_ptsIn _)
    (fun y => ⟨_, mem_pick ψ.isLB y⟩) (fun a b y => Matrix.of fun _ _ => gv X.str σ L a b y)
    (fun a b _ _ c => (AlgChart.holo c _ _).mono fun _ hv => ⟨hv.1, mem_ptsIn_inf.2 ⟨hv.2.1, hv.2.2⟩⟩)
    (fun a y => Matrix.of fun _ _ => ((Real.exp (-ψ.φ a y) : ℝ) : ℂ))
    (fun a => smoothOn_atlas fun y hy _ _ => (vInfAt_iff_cInfAt.2 (hψ a y hy)).comp_contDiff
      (Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp contDiff_neg)))
    (fun a y _ => by
      have : (Matrix.of fun _ _ : Unit => ((Real.exp (-ψ.φ a y) : ℝ) : ℂ)) =
          Matrix.diagonal fun _ => ((Real.exp (-ψ.φ a y) : ℝ) : ℂ) := by
        ext; simp
      rw [this, Matrix.posDef_diagonal_iff]
      exact fun _ => Complex.zero_lt_real.2 (Real.exp_pos _))
    (fun a b y hy => by
      ext
      have h0 : 0 < ‖gv X.str σ L a b y‖ ^ 2 := by have := gv_ne_zero hy.1 hy.2; positivity
      rw [ψ.trans a b y hy.1 hy.2, neg_sub, sub_eq_add_neg, Real.exp_add, Real.exp_log h0]
      simp only [chg, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply,
        Fintype.sum_unique, Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.mul_conj', Complex.star_def]
      ring) 1
  obtain ⟨h1, -, h3⟩ := hP (fld _ (c1W ψ)) fun a x hx => by
    rw [hfr a _ x hx (mem_pick ψ.isLB x.pt)]
    exact congrArg Subtype.val (chernAt_exp_neg (hφ _ x (mem_pick _ _))).symm
  exact ⟨h1, h3⟩

end GlobalTheory.ChernCalc.FirstChernW
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernFormOfWeightIsFormDbarEqZeroStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

theorem _root_.GlobalTheory.T.firstChernFormOfWeight_isForm_dbar_eq_zero : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (L : LB X.X) (ψ : Weight X.str σ L), ψ.IsCInf → (atlas X σ).IsForm (fld (atlas X σ) (c1W ψ)) ∧ (atlas X σ).dbar (fld (atlas X σ) (c1W ψ)) = 0 := by
  first | exact @GlobalTheory.ChernCalc.FirstChernW.c1W_isForm_and_dbar_eq_zero | exact GlobalTheory.ChernCalc.FirstChernW.c1W_isForm_and_dbar_eq_zero | (intros; apply GlobalTheory.ChernCalc.FirstChernW.c1W_isForm_and_dbar_eq_zero <;> assumption)
end
end
