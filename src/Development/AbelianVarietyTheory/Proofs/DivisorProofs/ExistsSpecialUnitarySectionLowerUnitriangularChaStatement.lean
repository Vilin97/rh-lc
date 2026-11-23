module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhaseFrame
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IsOrth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemDomOfOrth
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.DetSubUpper
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhaseFrame
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjSkewMemProductSpecialUnitaryLieAlgebraStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnGramSchmidtUpperTriangularFactorStatement
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryChartSectionFderivBelowDiagonalStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryChartSectionFrameEntriesFDerivDiagImStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryChartSectionFrameEntriesFDerivSkewStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryChartSectionFrameEntriesHasStrictFDerivAtStatement
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexHermitianFormUnitaryChartSection

section

@[expose] public section

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff

noncomputable section

namespace GlobalTheory.SUChartSection

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem hermC_eq_dot (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u v : Fin r → ℂ) :
    hermC τ G u v = u ⬝ᵥ (G.map τ *ᵥ fun l => conj (v l)) := by
  simp only [hermC, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, mul_assoc]

theorem hermC_mulVec (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (M : Matrix (Fin r) (Fin r) ℂ)
    (u v : Fin r → ℂ) :
    hermC τ G (M *ᵥ u) (M *ᵥ v) = u ⬝ᵥ (gram τ G M *ᵥ fun l => conj (v l)) := by
  have hc : (fun l => conj ((M *ᵥ v) l)) = M.map (starRingEnd ℂ) *ᵥ fun l => conj (v l) := by
    funext l

    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
  rw [hermC_eq_dot, hc, FrameDegreeData.gram_eq, Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem gram_secM (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) {w : V (nd X)}
    (hw : cpt X x w ∈ X.dom) (τ : X.Ψ) :
    gram τ.1 X.Gm (secM X x w τ) = gram τ.1 X.Gm 1 := by
  have hu : IsUnit (mat x τ).det := isUnit_iff_ne_zero.2 (det_ne_of_orth X hx τ)
  have hgx : secM X x w τ * mat x τ = mat (rmul (cpt X x w) (FrameDegreeData.bOf X (cpt X x w))) τ := by
    rw [secM, Matrix.nonsing_inv_mul_cancel_right _ _ hu, bOf_cpt X hx, yM, ← Matrix.mul_assoc]
    rfl
  have key : (mat x τ)ᵀ * gram τ.1 X.Gm (secM X x w τ) * (mat x τ).map (starRingEnd ℂ) =
      (mat x τ)ᵀ * gram τ.1 X.Gm 1 * (mat x τ).map (starRingEnd ℂ) := by
    rw [← FrameDegreeData.gram_mul, hgx, FrameDegreeData.ortho_bOf X hw τ, ← hx τ, ← FrameDegreeData.gram_mul, Matrix.one_mul]
  have huT : IsUnit (mat x τ)ᵀ.det := by rwa [Matrix.det_transpose]
  have huC : IsUnit ((mat x τ).map (starRingEnd ℂ)).det := by
    rw [show (mat x τ).map (starRingEnd ℂ) = (starRingEnd ℂ).mapMatrix (mat x τ) from rfl, ← RingHom.map_det, isUnit_iff_ne_zero, map_ne_zero]
    exact det_ne_of_orth X hx τ
  have h2 := congrArg (fun M => ((mat x τ)ᵀ)⁻¹ * M * ((mat x τ).map (starRingEnd ℂ))⁻¹) key
  simp only [Matrix.mul_assoc] at h2
  simpa only [Matrix.nonsing_inv_mul_cancel_left _ _ huT, Matrix.mul_nonsing_inv_cancel_right _ _ huC,
    ← Matrix.mul_assoc] using h2

theorem hermC_secM (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) {w : V (nd X)}
    (hw : cpt X x w ∈ X.dom) (τ : X.Ψ) (u v : Fin r → ℂ) :
    hermC τ.1 X.Gm (secM X x w τ *ᵥ u) (secM X x w τ *ᵥ v) = hermC τ.1 X.Gm u v := by
  rw [hermC_mulVec, gram_secM X hx hw τ, ← hermC_mulVec, Matrix.one_mulVec, Matrix.one_mulVec]

end GlobalTheory.SUChartSection
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexHermitianFormUnitaryChartSectionStatement

section

@[expose] public section

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff

theorem _root_.GlobalTheory.T.complexHermitianForm_unitaryChartSection : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {x : Frame X.Ψ r}, IsOrth X x → ∀ {w : V (nd X)}, cpt X x w ∈ X.dom → ∀ (τ : X.Ψ) (u v : Fin r → ℂ), hermC τ.1 X.Gm (secM X x w τ *ᵥ u) (secM X x w τ *ᵥ v) = hermC τ.1 X.Gm u v := by
  first | exact @GlobalTheory.SUChartSection.hermC_secM | exact GlobalTheory.SUChartSection.hermC_secM | (intros; apply GlobalTheory.SUChartSection.hermC_secM <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetUnitaryChartSectionConjugatedMatrix

section

@[expose] public section

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff

namespace GlobalTheory.SUChartSection

theorem det_secM_eq_one : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {x : Frame X.Ψ r}, IsOrth X x → ∀ {w : V (nd X)}, cpt X x w ∈ X.dom → ∀ τ : X.Ψ, (secM X x w τ).det = 1 := by
  intro E _ _ _ r X x hx w hw τ
  have hG := FrameDegreeData.ortho_bOf X hw τ
  rw [bOf_cpt X hx w] at hG
  have hm : mat (rmul (cpt X x w) (fun τ => gsB X w τ)) τ = mat x τ * yM X w τ := by
    show mat x τ * mat (nmat X w) τ * gsB X w τ = _
    rw [yM, Matrix.mul_assoc]
  rw [hm, FrameDegreeData.gram_mul, hx τ] at hG
  have hd := congrArg Matrix.det hG
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hd
  have hc : ((yM X w τ).map (starRingEnd ℂ)).det = starRingEnd ℂ (yM X w τ).det :=
    (RingHom.map_det (starRingEnd ℂ) (yM X w τ)).symm
  rw [hc] at hd
  have hJ : (Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun a _ => by exact_mod_cast PoinPf.sgn_ne _ _
  have hY : (yM X w τ).det = ((∏ k, gsS X w τ k : ℝ) : ℂ) := by
    rw [yM, Matrix.det_mul, gsB, Matrix.det_mul, Matrix.det_diagonal]
    rw [Matrix.det_of_lowerTriangular _ (fun a b hab => ?_)]
    · rw [gsU, Matrix.det_of_upperTriangular (FrameDegreeData.uMat_upper _)]
      simp only [FrameDegreeData.uMat_diag, Finset.prod_const_one, one_mul]
      have : ∀ i, mat (nmat X w) τ i i = 1 := fun i => by
        simp [mat, nmat]
      simp only [this, Finset.prod_const_one, one_mul]
      push_cast; rfl
    · show nmat X w τ a b = 0
      simp only [nmat]
      have hab' : a < b := hab
      have h1 : ¬ b < a := not_lt.2 (le_of_lt hab')
      rw [dite_eq_right h1, if_neg (ne_of_lt hab')]
  set t : ℝ := ∏ k, gsS X w τ k with ht
  have hpos : 0 ≤ t := Finset.prod_nonneg fun k _ => inv_nonneg.2 (Real.sqrt_nonneg _)
  rw [hY, Complex.conj_ofReal] at hd
  have htt : ((t * t : ℝ) : ℂ) = 1 := by
    have h2 : (t : ℂ) * (Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)).det * (t : ℂ) =
      1 * (Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)).det := by rw [hd, one_mul]
    push_cast
    have h3 : ((t : ℂ) * t) * (Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)).det =
      1 * (Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)).det := by rw [← h2]; ring
    exact mul_right_cancel₀ hJ h3
  have htt' : t * t = 1 := by exact_mod_cast htt
  have ht1 : t = 1 := by nlinarith
  rw [secM, Matrix.det_conj ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (det_ne_of_orth X hx τ))) (yM X w τ), hY, ht1, Complex.ofReal_one]

end GlobalTheory.SUChartSection
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetUnitaryChartSectionConjugatedMatrixStatement

section

@[expose] public section

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff

theorem _root_.GlobalTheory.T.det_unitaryChartSectionConjugatedMatrix : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {x : Frame X.Ψ r}, IsOrth X x → ∀ {w : V (nd X)}, cpt X x w ∈ X.dom → ∀ τ : X.Ψ, (secM X x w τ).det = 1 := by
  first | exact @GlobalTheory.SUChartSection.det_secM_eq_one | exact GlobalTheory.SUChartSection.det_secM_eq_one | (intros; apply GlobalTheory.SUChartSection.det_secM_eq_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpecialUnitarySectionLowerUnitriangularCha

section

@[expose] public section

noncomputable section

namespace GlobalTheory.SUChartSection
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal ComplexConjugate ContDiff

theorem exists_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r), IsOrth X x → ∃ (σ : V (nd X) → realSU X.Ψ X.Gm) (ρ : ℝ) (D₁ : V (nd X) →L[ℝ] (X.Ψ → Fin r → Fin r → ℂ)), 0 < ρ ∧ σ 0 = 1 ∧ ContinuousOn σ (Metric.ball 0 ρ) ∧ (∀ z ∈ Metric.ball (0 : V (nd X)) ρ, ∃ b ∈ Bor X.Ψ r, X.lmulC (fun τ => ((((σ z : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul (cpt X x z) b) ∧ HasStrictFDerivAt (fun z => (fun τ a b => ((((σ z : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) a b)) D₁ 0 ∧ ∀ z, D₁ z ∈ realLie X.Ψ X.Gm ∧ (∀ τ a b, b < a → inFrame x (D₁ z) τ a b = nmat X z τ a b) ∧ ∀ τ a, inFrame x (D₁ z) τ a a = 0 := by
  intro E _ _ _ r X x hx
  classical
  obtain ⟨R, hR, hball⟩ := exists_ball X hx
  have hdet1 : ∀ w, cpt X x w ∈ X.dom → ∀ τ, (secM X x w τ).det ≠ 0 := fun w hw τ => by
    rw [GlobalTheory.T.det_unitaryChartSectionConjugatedMatrix X hx hw τ]; exact one_ne_zero
  let secU : ∀ w, cpt X x w ∈ X.dom → realSU X.Ψ X.Gm := fun w hw =>
    ⟨fun τ => Matrix.GeneralLinearGroup.mkOfDetNeZero (secM X x w τ) (hdet1 w hw τ),
      fun τ => ⟨GlobalTheory.T.det_unitaryChartSectionConjugatedMatrix X hx hw τ, GlobalTheory.T.complexHermitianForm_unitaryChartSection X hx hw τ⟩⟩
  have hsecU : ∀ w (hw : cpt X x w ∈ X.dom) τ,
      ((((secU w hw : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
        secM X x w τ := fun _ _ _ => rfl
  let σ : V (nd X) → realSU X.Ψ X.Gm := fun w => if h : w ∈ Metric.ball (0 : V (nd X)) R then secU w (hball w h) else 1
  have hσ : ∀ w (h : w ∈ Metric.ball (0 : V (nd X)) R) τ,
      ((((σ w : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
        secM X x w τ := fun w h τ => by
    simp only [σ, dif_pos h]; rfl
  have hx0 : ∀ τ, IsUnit (mat x τ).det := fun τ => isUnit_iff_ne_zero.2 (det_ne_of_orth X hx τ)
  have h0 : (0 : V (nd X)) ∈ Metric.ball (0 : V (nd X)) R := Metric.mem_ball_self hR
  let Cx : (X.Ψ → Fin r → Fin r → ℂ) →ₗ[ℝ] (X.Ψ → Fin r → Fin r → ℂ) :=
    { toFun := fun Y τ => (mat x τ * Matrix.of (Y τ) * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ)
      map_add' := fun Y Z => by
        funext τ
        have e : Matrix.of ((Y + Z) τ) = Matrix.of (Y τ) + Matrix.of (Z τ) := rfl
        simp only [e, Matrix.mul_add, Matrix.add_mul]; rfl
      map_smul' := fun c Y => by
        funext τ
        have e : Matrix.of ((c • Y) τ) = c • Matrix.of (Y τ) := rfl
        simp only [e, Matrix.mul_smul, Matrix.smul_mul]; rfl }
  let C := LinearMap.toContinuousLinearMap Cx
  have hC : ∀ Y τ, C Y τ = (mat x τ * Matrix.of (Y τ) * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) := fun _ _ => rfl
  refine ⟨σ, R, C.comp (dY X), hR, ?_, ?_, ?_, ?_, ?_⟩
  · refine Subtype.ext (funext fun τ => Units.ext ?_)
    rw [hσ 0 h0 τ, secM_zero X hx τ]; rfl
  · rw [continuousOn_iff_continuous_restrict]
    have hg : ∀ τ, Continuous fun w : Metric.ball (0 : V (nd X)) R => gsB X w τ := fun τ => by
      refine continuous_pi fun a => continuous_pi fun b => ?_
      exact ((GlobalTheory.T.contDiffOn_gramSchmidtUpperTriangularFactor X hx τ a b).continuousOn.mono (fun w hw => hball w hw)).restrict
    have hM : ∀ τ, Continuous fun w : Metric.ball (0 : V (nd X)) R => secM X x w τ := fun τ => by
      refine (continuous_const.matrix_mul ?_).matrix_mul continuous_const
      exact ((PoinPf.cont_nmatm X τ).comp continuous_subtype_val).matrix_mul (hg τ)
    refine continuous_induced_rng.2 (continuous_pi fun τ => Units.continuous_iff.2 ⟨?_, ?_⟩)
    · refine (hM τ).congr fun w => ?_
      simp only [Function.comp_apply, Set.restrict_apply]
      exact (hσ w w.2 τ).symm
    · refine ((hM τ).matrix_adjugate).congr fun w => ?_
      simp only [Function.comp_apply, Set.restrict_apply]
      rw [Matrix.coe_units_inv, hσ w w.2 τ, Matrix.inv_def, GlobalTheory.T.det_unitaryChartSectionConjugatedMatrix X hx (hball w w.2) τ, Ring.inverse_one, one_smul]
  · intro z hz
    refine ⟨FrameDegreeData.bOf X (cpt X x z), FrameDegreeData.bOf_mem X (hball z hz), ?_⟩
    funext τ
    show (((((σ z : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ :
      Matrix (Fin r) (Fin r) ℂ) = (mat (cpt X x z) τ * mat (FrameDegreeData.bOf X (cpt X x z)) τ : Matrix (Fin r) (Fin r) ℂ)
    rw [hσ z hz τ, bOf_cpt X hx z]
    show mat x τ * yM X z τ * (mat x τ)⁻¹ * mat x τ = mat x τ * mat (nmat X z) τ * gsB X z τ
    rw [Matrix.mul_assoc _ (mat x τ)⁻¹, Matrix.nonsing_inv_mul _ (hx0 τ), Matrix.mul_one, yM, Matrix.mul_assoc]
  · have h1 : HasStrictFDerivAt (fun z => C (yF X z)) (C.comp (dY X)) 0 :=
      C.hasStrictFDerivAt.comp 0 (GlobalTheory.T.unitaryChartSectionFrameEntries_hasStrictFDerivAt X hx)
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds (0 : V (nd X)) hR] with z hz
    funext τ a b
    rw [hσ z hz τ, hC]
    rfl
  · intro z
    have hdiag : ∀ τ a, dY X z τ a a = 0 := fun τ a => by
      have h6 := congrArg Complex.re (GlobalTheory.T.unitaryChartSectionFrameEntriesFDeriv_skew X hx z τ a a)
      have h7 := GlobalTheory.T.unitaryChartSectionFrameEntriesFDeriv_diag_im X hx z τ a
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
        Complex.conj_im, h7, Complex.zero_re, mul_zero, sub_zero, zero_mul, neg_zero] at h6
      have hs := PoinPf.sgn_ne X.p0 (a : ℕ)
      have hre : (dY X z τ a a).re = 0 := by
        have : 2 * sgn X.p0 (a : ℕ) * (dY X z τ a a).re = 0 := by linarith
        rcases mul_eq_zero.1 this with h | h
        · exact absurd (by linarith : sgn X.p0 (a : ℕ) = 0) hs
        · exact h
      exact Complex.ext hre h7
    have hIF : ∀ τ, inFrame x (C.comp (dY X) z) τ = Matrix.of (dY X z τ) := fun τ => by
      show (mat x τ)⁻¹ * Matrix.of (C (dY X z) τ) * mat x τ = _
      rw [hC]
      show (mat x τ)⁻¹ * (mat x τ * Matrix.of (dY X z τ) * (mat x τ)⁻¹) * mat x τ = _
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hx0 τ), Matrix.one_mul,
        Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hx0 τ), Matrix.mul_one]
    refine ⟨?_, fun τ a b h => ?_, fun τ a => ?_⟩
    · exact GlobalTheory.T.conj_skew_mem_productSpecialUnitaryLieAlgebra X hx (fun τ => Matrix.of (dY X z τ)) (fun τ a b => GlobalTheory.T.unitaryChartSectionFrameEntriesFDeriv_skew X hx z τ a b) hdiag
    · rw [hIF]; exact GlobalTheory.T.unitaryChartSection_fderiv_below_diagonal X hx z τ a b h
    · rw [hIF]; exact hdiag τ a
end GlobalTheory.SUChartSection
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpecialUnitarySectionLowerUnitriangularChaStatement

section

@[expose] public section

open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal

theorem _root_.GlobalTheory.T.exists_specialUnitary_section_lowerUnitriangular_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r), IsOrth X x → ∃ (σ : V (nd X) → realSU X.Ψ X.Gm) (ρ : ℝ) (D₁ : V (nd X) →L[ℝ] (X.Ψ → Fin r → Fin r → ℂ)), 0 < ρ ∧ σ 0 = 1 ∧ ContinuousOn σ (Metric.ball 0 ρ) ∧ (∀ z ∈ Metric.ball (0 : V (nd X)) ρ, ∃ b ∈ Bor X.Ψ r, X.lmulC (fun τ => ((((σ z : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul (cpt X x z) b) ∧ HasStrictFDerivAt (fun z => (fun τ a b => ((((σ z : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) a b)) D₁ 0 ∧ ∀ z, D₁ z ∈ realLie X.Ψ X.Gm ∧ (∀ τ a b, b < a → inFrame x (D₁ z) τ a b = nmat X z τ a b) ∧ ∀ τ a, inFrame x (D₁ z) τ a a = 0 := by
  first | exact @GlobalTheory.SUChartSection.exists_section | exact GlobalTheory.SUChartSection.exists_section | (intros; apply GlobalTheory.SUChartSection.exists_section <;> assumption)
end
end
