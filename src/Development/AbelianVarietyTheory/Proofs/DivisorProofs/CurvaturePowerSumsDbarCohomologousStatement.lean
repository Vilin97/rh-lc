module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvaturePowerPullbackHolomorphicStatement
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvaturePowerPullbackHolomorphicStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvaturePowerSumTransgressionSmoothDbarClosedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramConnectionPairChernFieldsLocalFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvaturePowerSumTransgressionSmoothDbarClosedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarChernTransgressionFormEqPowerSumDiffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarOperatorLocalCalculusComplexFormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramConnectionPairChernFieldsLocalFrameStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernTransgressionFormHolomorphicPullback

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

noncomputable section
namespace GlobalTheory.ChernCalc

theorem eq_sum_ofLp_smul_complexCoordinateVector {n : ℕ} (w : V n) : w = ∑ a, w a • coordVec a := by
  ext i
  simp [coordVec, Pi.single_apply]

theorem trace_mul_constMatrix_mul_evenForms_sum {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (P Q : Matrix r r (Ev n)) (C : Matrix r r ℂ) :
    (((P * C.map (algebraMap ℂ (Ev n)) * Q).trace : Ev n) : Alt n) = ∑ p, ∑ q, C p q • (((Q * P) q p : Ev n) : Alt n) := by
  rw [Matrix.trace_mul_cycle, Matrix.trace]
  simp only [Matrix.diag, Matrix.mul_apply (M := Q * P), Matrix.map_apply, AddSubmonoidClass.coe_finsetSum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [mul_comm, ← Algebra.smul_def, Subalgebra.coe_smul]

def connectionMatrixDifferenceLinearMap {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (G G' : V n → Matrix r r ℂ) (v : V n) :
    V n →ₗ[ℂ] Matrix r r ℂ where
  toFun ξ := conn G v ξ - conn G' v ξ
  map_add' ξ ξ' := by rw [conn_add_vec, conn_add_vec]; abel
  map_smul' c ξ := by rw [conn_smul_vec, conn_smul_vec, smul_sub]; rfl

theorem transAt_comp_holo : ∀ (n n' : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G G' : V n → Matrix r r ℂ) (φ : V n' → V n) (w : V n'), ContDiffAt ℂ 2 φ w → MContDiffAt ∞ G (φ w) → IsUnit (G (φ w)).det → MContDiffAt ∞ G' (φ w) → IsUnit (G' (φ w)).det → ∀ k, transAt (fun x => G (φ x)) (fun x => G' (φ x)) w k = pull (fderiv ℂ φ w) (transAt G G' (φ w) k) := by
  intro n n' r _ _ G G' φ w hφ hG hGu hG' hG'u k
  have hI := (GlobalTheory.T.curvature_power_pullback_holomorphic n n' r G' φ w hφ hG' hG'u).1
  have hφ1 : DifferentiableAt ℂ φ w := hφ.differentiableAt two_ne_zero
  have h1 : MContDiffAt 1 G (φ w) := hG.of_le (by exact_mod_cast le_top)
  have h1' : MContDiffAt 1 G' (φ w) := hG'.of_le (by exact_mod_cast le_top)
  have hc : ∀ ξ, conn (fun x => G (φ x)) w ξ - conn (fun x => G' (φ x)) w ξ =
      ∑ b, fderiv ℂ φ w ξ b • connectionMatrixDifferenceLinearMap G G' (φ w) (coordVec b) := by
    intro ξ
    rw [conn_comp_holo h1 hφ1, conn_comp_holo h1' hφ1]
    show connectionMatrixDifferenceLinearMap G G' (φ w) (fderiv ℂ φ w ξ) = _
    conv_lhs => rw [eq_sum_ofLp_smul_complexCoordinateVector (fderiv ℂ φ w ξ)]

    rw [map_sum]
    simp only [map_smul]
  have hd : ∀ b, conn G (φ w) (coordVec b) - conn G' (φ w) (coordVec b) = connectionMatrixDifferenceLinearMap G G' (φ w) (coordVec b) :=
    fun _ => rfl

  simp only [transAt, hc, hd, map_sum, map_mul, (pull_dz _ _).1, trace_mul_constMatrix_mul_evenForms_sum, AlgHom.map_smul_of_tower]
  simp only [hI _ _ _ _ G hG hGu, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_smul, Finset.sum_mul,
    Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul, Finset.smul_sum]
  conv_lhs => enter [2, a, 2, i, 2, p]; rw [Finset.sum_comm]
  conv_lhs => enter [2, a, 2, i]; rw [Finset.sum_comm]
  conv_lhs => enter [2, a]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => enter [2, b]; rw [Finset.sum_comm]

end GlobalTheory.ChernCalc
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernTransgressionFormHolomorphicPullbackStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

theorem _root_.GlobalTheory.T.chernTransgressionForm_holomorphic_pullback : ∀ (n n' : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G G' : V n → Matrix r r ℂ) (φ : V n' → V n) (w : V n'), ContDiffAt ℂ 2 φ w → MContDiffAt ∞ G (φ w) → IsUnit (G (φ w)).det → MContDiffAt ∞ G' (φ w) → IsUnit (G' (φ w)).det → ∀ k, transAt (fun x => G (φ x)) (fun x => G' (φ x)) w k = pull (fderiv ℂ φ w) (transAt G G' (φ w) k) := by
  first | exact @GlobalTheory.ChernCalc.transAt_comp_holo | exact GlobalTheory.ChernCalc.transAt_comp_holo | (intros; apply GlobalTheory.ChernCalc.transAt_comp_holo <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvaturePowerSumTransgressionIsForm

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernCalc.PairForm

section Point

variable {n : ℕ} {r : Type} [Fintype r] [DecidableEq r]

theorem powAt_congr {G G₁ : V n → Matrix r r ℂ} {v : V n} (h : G =ᶠ[𝓝 v] G₁) (k : ℕ) :
    powAt G v k = powAt G₁ v k := by
  simp only [powAt, curvEv, curvPoly, curv_congr h]

theorem transAt_congr {G G₁ G' G₁' : V n → Matrix r r ℂ} {v : V n} (h : G =ᶠ[𝓝 v] G₁)
    (h' : G' =ᶠ[𝓝 v] G₁') (k : ℕ) : transAt G G' v k = transAt G₁ G₁' v k := by
  simp only [transAt, curvEv, curvPoly, curv_congr h, curv_congr h', conn_congr h, conn_congr h']

end Point

section Manifold

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) {r : Type} [Fintype r] [DecidableEq r]

theorem contDiffAt_change (x x' : A.Pt) (h : x.pt = x'.pt) : ContDiffAt ℂ 2 (x'.ch ∘ x.ch.symm) x.crd := by
  have hs : IsOpen (x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source) :=
    x.ch.isOpen_inter_preimage_symm x'.ch.open_source
  have hm : x.crd ∈ x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source := by
    refine ⟨x.ch.map_source x.2, ?_⟩
    show x.ch.symm ((x.ch) x.pt) ∈ x'.ch.source
    rw [x.ch.left_inv x.2]
    exact (congrArg (fun y => y ∈ x'.ch.source) h).mpr x'.2
  exact GlobalTheory.SCV.contDiffAt_of_differentiableOn (A.holo x.1.1 x'.1.1) (hs.mem_nhds hm) 2

theorem change_crd (x x' : A.Pt) (h : x.pt = x'.pt) : (x'.ch ∘ x.ch.symm) x.crd = x'.crd := by
  show (x'.ch) (x.ch.symm ((x.ch) x.pt)) = (x'.ch) x'.pt
  rw [x.ch.left_inv x.2]
  exact congrArg x'.ch h

theorem germ_change (G : M → M → Matrix r r ℂ) (x x' : A.Pt) (h : x.pt = x'.pt) :
    (fun u => G x.pt (x.ch.symm u)) =ᶠ[𝓝 x.crd] fun u => G x'.pt (x'.ch.symm ((x'.ch ∘ x.ch.symm) u)) := by
  have hc : ContinuousAt x.ch.symm x.crd := x.ch.continuousAt_symm (x.ch.map_source x.2)
  have hmem : x'.ch.source ∈ 𝓝 (x.ch.symm x.crd) := by
    show x'.ch.source ∈ 𝓝 (x.ch.symm ((x.ch) x.pt))
    rw [x.ch.left_inv x.2]
    exact (congrArg (fun y => x'.ch.source ∈ 𝓝 y) h).mpr (x'.ch.open_source.mem_nhds x'.2)
  filter_upwards [hc hmem] with u hu
  show G x.pt (x.ch.symm u) = G x'.pt (x'.ch.symm ((x'.ch) (x.ch.symm u)))
  rw [x'.ch.left_inv hu]
  exact congrArg (fun y => G y (x.ch.symm u)) h

theorem smooth_crd (G : M → M → Matrix r r ℂ) (hG : ∀ y, SmoothUnitAt A (G y) y) (x : A.Pt) :
    MContDiffAt ∞ (fun u => G x.pt (x.ch.symm u)) x.crd ∧ IsUnit (G x.pt (x.ch.symm x.crd)).det := by
  refine ⟨((hG x.pt).2 x.1.1 x.2).self_of_nhds, ?_⟩
  show IsUnit (G x.pt (x.ch.symm ((x.ch) x.pt))).det
  rw [x.ch.left_inv x.2]
  exact (hG x.pt).1

theorem smooth_change (G : M → M → Matrix r r ℂ) (hG : ∀ y, SmoothUnitAt A (G y) y) (x x' : A.Pt) (h : x.pt = x'.pt) :
    MContDiffAt ∞ (fun u => G x'.pt (x'.ch.symm u)) ((x'.ch ∘ x.ch.symm) x.crd) ∧
      IsUnit (G x'.pt (x'.ch.symm ((x'.ch ∘ x.ch.symm) x.crd))).det := by
  rw [change_crd A x x' h]
  exact smooth_crd A G hG x'

end Manifold

theorem isForm_pow_trans : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (r : Type) [Fintype r]
    [DecidableEq r] (G G' : M → M → Matrix r r ℂ), IsGramPair A G G' →
      ∀ k, A.IsForm (fld A (powFld A G k)) ∧ A.IsForm (transFld A G G' k) := by
  intro M _ n A r _ _ G G' hG k
  have sG : ∀ y, SmoothUnitAt A (G y) y := fun y => (hG.smooth y).1
  have sG' : ∀ y, SmoothUnitAt A (G' y) y := fun y => (hG.smooth y).2
  have near := GlobalTheory.T.gramConnectionPair_chernFields_local_frame M n A r G G' hG
  constructor
  · refine ⟨fun i S => ?_, fun x x' h => ?_⟩
    · intro v hv
      let x : A.Pt := ⟨(i, (A.e i).symm v), (A.e i).map_target hv⟩
      have hx : x.crd = v := (A.e i).right_inv hv
      obtain ⟨h1, h2⟩ := smooth_crd A G sG x
      have hs := (GlobalTheory.T.curvature_power_sum_transgression_smooth_dbar_closed n r _ _ x.crd h1 h2 h1 h2 k).1 S
      have key : ContDiffAt ℝ ∞ (fun v => (bas n).repr (A.loc (fld A (powFld A G k)) i v) S) x.crd :=
        hs.congr_of_eventuallyEq ((near x k).mono fun u hu => congrArg (fun a => (bas n).repr a S) hu.1)
      rw [hx] at key
      exact key.contDiffWithinAt
    · obtain ⟨h1, h2⟩ := smooth_change A G sG x x' h
      have hc := ((GlobalTheory.T.curvature_power_pullback_holomorphic n n r _ (x'.ch ∘ x.ch.symm) x.crd (contDiffAt_change A x x' h) h1 h2).2 k).1
      show (powAt (fun v => G x.pt (x.ch.symm v)) x.crd k : Alt n) =
        pull (fderiv ℂ (x'.ch ∘ x.ch.symm) x.crd) (powAt (fun v => G x'.pt (x'.ch.symm v)) x'.crd k : Alt n)
      rw [powAt_congr (germ_change A G x x' h), hc, change_crd A x x' h]
  · refine ⟨fun i S => ?_, fun x x' h => ?_⟩
    · intro v hv
      let x : A.Pt := ⟨(i, (A.e i).symm v), (A.e i).map_target hv⟩
      have hx : x.crd = v := (A.e i).right_inv hv
      obtain ⟨h1, h2⟩ := smooth_crd A G sG x
      obtain ⟨h1', h2'⟩ := smooth_crd A G' sG' x
      have hs := (GlobalTheory.T.curvature_power_sum_transgression_smooth_dbar_closed n r _ _ x.crd h1 h2 h1' h2' k).2.2 S
      have key : ContDiffAt ℝ ∞ (fun v => (bas n).repr (A.loc (transFld A G G' k) i v) S) x.crd :=
        hs.congr_of_eventuallyEq ((near x k).mono fun u hu => congrArg (fun a => (bas n).repr a S) hu.2.2)
      rw [hx] at key
      exact key.contDiffWithinAt
    · obtain ⟨h1, h2⟩ := smooth_change A G sG x x' h
      obtain ⟨h1', h2'⟩ := smooth_change A G' sG' x x' h
      have hc := GlobalTheory.T.chernTransgressionForm_holomorphic_pullback n n r _ _ (x'.ch ∘ x.ch.symm) x.crd (contDiffAt_change A x x' h) h1 h2 h1' h2' k
      show transAt (fun v => G x.pt (x.ch.symm v)) (fun v => G' x.pt (x.ch.symm v)) x.crd k =
        pull (fderiv ℂ (x'.ch ∘ x.ch.symm) x.crd)
          (transAt (fun v => G x'.pt (x'.ch.symm v)) (fun v => G' x'.pt (x'.ch.symm v)) x'.crd k)
      rw [transAt_congr (germ_change A G x x' h) (germ_change A G' x x' h), hc, change_crd A x x' h]

end GlobalTheory.ChernCalc.PairForm
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvaturePowerSumTransgressionIsFormStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

theorem _root_.GlobalTheory.T.curvaturePowerSum_transgression_isForm : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (r : Type) [Fintype r] [DecidableEq r] (G G' : M → M → Matrix r r ℂ), IsGramPair A G G' → ∀ k, A.IsForm (fld A (powFld A G k)) ∧ A.IsForm (transFld A G G' k) := by
  first | exact @GlobalTheory.ChernCalc.PairForm.isForm_pow_trans | exact GlobalTheory.ChernCalc.PairForm.isForm_pow_trans | (intros; apply GlobalTheory.ChernCalc.PairForm.isForm_pow_trans <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvaturePowerSumsDbarCohomologous

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc.PowCoh

variable {M : Type} [TopologicalSpace M] {n : ℕ} {A : HolAtlas M n} {r : Type} [Fintype r] [DecidableEq r]
  {G G' : M → M → Matrix r r ℂ}

theorem pair_symm (h : IsGramPair A G G') : IsGramPair A G' G :=
  ⟨fun y => (h.smooth y).symm, fun y => (h.trans y).mono fun _ ⟨T, K, K', hT, hK, hK', e⟩ =>
    ⟨T, K', K, hT, hK', hK, e.mono fun _ hw => hw.symm⟩⟩

theorem smooth_crd (h : IsGramPair A G G') (x : A.Pt) :
    MContDiffAt ∞ (fun u => G x.pt (x.ch.symm u)) x.crd ∧ IsUnit (G x.pt (x.ch.symm x.crd)).det := by
  refine ⟨((h.smooth x.pt).1.2 x.1.1 x.2).self_of_nhds, ?_⟩
  rw [x.ch.left_inv x.2]
  exact (h.smooth x.pt).1.1

theorem dbar_powFld (h : IsGramPair A G G') (k : ℕ) : A.dbar (fld A (powFld A G k)) = 0 := by
  funext x
  have h₁ := smooth_crd h x
  refine ((GlobalTheory.T.dbar_operator_local_calculus_complex_forms n x.crd).1 _ _ ((GlobalTheory.T.gramConnectionPair_chernFields_local_frame M n A r G G' h x k).mono fun _ hv => hv.1)).trans ?_
  exact (GlobalTheory.T.curvature_power_sum_transgression_smooth_dbar_closed n r _ _ x.crd h₁.1 h₁.2 h₁.1 h₁.2 k).2.1

theorem dbar_transFld (h : IsGramPair A G G') (k : ℕ) :
    fld A (powFld A G k) - fld A (powFld A G' k) = A.dbar (transFld A G G' k) := by
  funext x
  have h₁ := smooth_crd h x
  have h₂ := smooth_crd (pair_symm h) x
  symm
  refine ((GlobalTheory.T.dbar_operator_local_calculus_complex_forms n x.crd).1 _ _ ((GlobalTheory.T.gramConnectionPair_chernFields_local_frame M n A r G G' h x k).mono fun _ hv => hv.2.2)).trans ?_
  exact GlobalTheory.T.dbar_chernTransgressionForm_eq_power_sum_diff n r _ _ x.crd h₁.1 h₁.2 h₂.1 h₂.2 k

theorem dbarCoh_powFld : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (r : Type) [Fintype r]
    [DecidableEq r] (G G' : M → M → Matrix r r ℂ), IsGramPair A G G' → ∀ k,
    DbarCoh A (powFld A G k) (powFld A G' k) := fun M _ n A r _ _ G G' h k =>
  ⟨(GlobalTheory.T.curvaturePowerSum_transgression_isForm M n A r G G' h k).1, (GlobalTheory.T.curvaturePowerSum_transgression_isForm M n A r G' G (pair_symm h) k).1, dbar_powFld h k,
    dbar_powFld (pair_symm h) k, _, (GlobalTheory.T.curvaturePowerSum_transgression_isForm M n A r G G' h k).2, dbar_transFld h k⟩

end GlobalTheory.ChernCalc.PowCoh
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvaturePowerSumsDbarCohomologousStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

theorem _root_.GlobalTheory.T.curvaturePowerSums_dbarCohomologous : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (r : Type) [Fintype r] [DecidableEq r] (G G' : M → M → Matrix r r ℂ), IsGramPair A G G' → ∀ k, DbarCoh A (powFld A G k) (powFld A G' k) := by
  first | exact @GlobalTheory.ChernCalc.PowCoh.dbarCoh_powFld | exact GlobalTheory.ChernCalc.PowCoh.dbarCoh_powFld | (intros; apply GlobalTheory.ChernCalc.PowCoh.dbarCoh_powFld <;> assumption)
end
end
