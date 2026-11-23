module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformizationLawsOfGoodDeepCover
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Counterexamples.UpperHalfSurvey.ExistsFundSetOrth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicProbabilityEqNormalisedFundamentalSets
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramePointsOverComponentOpenSet
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.BddSecCuspCongr
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProbabilityMeasureAutQuotientNormalized
public import Formalism.LocalToGlobal.ProjectiveLattices.NormLaws
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalFlagTranslateHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormPeakAtInjectiveChartFrameStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameExponentialVolumeSmall
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DividedWeightStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HostN
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtNZ
public import Formalism.LocalToGlobal.ProjectiveLattices.ModelAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormLowerBoundBergmanFunctionOnComponent

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

namespace GlobalTheory.BergLower

open MeasureTheory ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

theorem le_div_of_mean {β a I v S m J N : ℝ≥0∞} (ha0 : a ≠ 0) (hat : a ≠ ⊤) (hS0 : S ≠ 0) (hv : v ≠ ⊤)
    (hI : v = 0 → I = 0) (hβ : β * I ≤ a * v) (hJ : J * S = I) (hm : v ≤ m * S) (hN : N ≤ m⁻¹ * J) :
    β ≤ a / N := by
  rw [ENNReal.le_div_iff_mul_le (Or.inr ha0) (Or.inr hat)]
  by_cases h0 : v = 0
  · have hJ0 : J = 0 := by
      rw [hI h0] at hJ
      exact (mul_eq_zero.1 hJ).resolve_right hS0
    rw [hJ0, mul_zero, nonpos_iff_eq_zero] at hN
    simp [hN]
  · have h1 : N * v ≤ I := by
      calc N * v ≤ (m⁻¹ * J) * (m * S) := by gcongr
        _ = (m⁻¹ * m) * (J * S) := by ring
        _ ≤ 1 * I := by
          rw [hJ]
          gcongr
          exact ENNReal.inv_mul_le_one m
        _ = I := one_mul _
    have h2 : β * N * v ≤ a * v := by
      rw [mul_assoc]
      exact le_trans (by gcongr) hβ
    exact (ENNReal.mul_le_mul_iff_left h0 hv).1 h2

theorem pnorm_pos {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (la : Wt X.Ψ r)
    {P : Frame X.Ψ r → ℂ} {x : Frame X.Ψ r} (hx : x ∈ X.dom) (hP : P x ≠ 0) : 0 < X.pnorm la P x := by
  have hd : ∀ τ i, dmin X.Gm x τ i ≠ 0 := fun τ i h => by
    have := (hx τ).2 i
    rw [h] at this
    simp at this
  unfold Data.pnorm
  exact mul_pos (norm_pos_iff.2 hP) (Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ =>
    Real.rpow_pos_of_pos (norm_pos_iff.2 (div_ne_zero (hd _ _) (hd _ _))) _)

theorem le_bergOn : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), GlobalTheory.LevGeo.Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∀ (G : WTZ D.host.E) (Z : Comp Xo c) (y : FPt (U σ).X), (⟨y.1, y.2.1⟩ : Σ k, Frame ((U σ).X k).Ψ D.R.r) ∈ framesOn (U σ) Z → ∀ β : ENNReal, (∀ (x0 : Frame ((U σ).X y.1).Ψ D.R.r) (FF : Set (ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd ((U σ).X y.1)))), ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth ((U σ).X y.1) x0 → ReciprocityTheory.ChartRestriction.G.AR.Up.IsFundSet ((U σ).X y.1) x0 FF → ∃ P ∈ ((U σ).X y.1).SS (modelWt (U σ) G y.1), P y.2.1 ≠ 0 ∧ β * ∫⁻ z in FF, ENNReal.ofReal (((U σ).X y.1).pnorm (modelWt (U σ) G y.1) P (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt ((U σ).X y.1) x0 z) ^ 2) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF ((U σ).X y.1) x0) ≤ ENNReal.ofReal (((U σ).X y.1).pnorm (modelWt (U σ) G y.1) P y.2.1 ^ 2) * ReciprocityTheory.ChartRestriction.G.AR.Up.muF ((U σ).X y.1) x0 FF) → β ≤ bergOn (U σ) (D.sp.W j) (dict σ) Z G y := by
  intro D j H Dw l Xo c U dict hL σ hσ G Z y hy β hβ
  classical
  have hU : IsUnf (U σ) := hL.unf σ hσ
  obtain ⟨Kf, th, hr, -, -, hDU, -⟩ := hL.dictU σ hσ
  have hdom : ∀ g, (dict σ g).2 ∈ ((U σ).X (dict σ g).1).dom := Formalism.L2.Pj.dict_dom_of hDU
  have hex : ∀ (X : Data D.host.E D.R.r), ∃ x0, IsOrth X x0 ∧ ∃ FF, IsFundSet X x0 FF := fun X => by
    choose P _ hG using X.signature
    exact ⟨fun τ => P τ, fun τ => hG τ, GlobalTheory.MetricWeightTest.exists_fundSet_orth X (fun τ => hG τ)⟩
  choose x0 hx0 FF hFF using fun k => hex ((U σ).X k)
  obtain ⟨P, hP, hPy, hle⟩ := hβ (x0 y.1) (FF y.1) (hx0 _) (hFF _)
  set la := modelWt (U σ) G with hla
  obtain ⟨hS0, hST, hI⟩ := GlobalTheory.LevGeo.adelicProb_mul_volFund D j H Dw l Xo c U dict hL σ hσ x0 FF
    (fun k => ⟨hx0 k, hFF k⟩)
  set Q : Frame ((U σ).X y.1).Ψ D.R.r → ℂ := ((U σ).X y.1).dom.indicator P with hQ
  have hQP : ∀ x ∈ ((U σ).X y.1).dom, ((U σ).X y.1).pnorm (la y.1) Q x = ((U σ).X y.1).pnorm (la y.1) P x :=
    fun x hx => by unfold Data.pnorm; rw [hQ, Set.indicator_of_mem hx]
  have hQS : Q ∈ ((U σ).X y.1).SS (la y.1) :=
    (GlobalTheory.DomCongr.bddSec_cusp_congr D.host.E D.R.r _ _ P Q (fun x hx => (Set.indicator_of_mem hx _).symm)).2 hP
  set P' : Formalism.L2.Pj.FDSec (U σ).X := Function.update (fun _ => 0) y.1 Q with hP'
  have hP'y : P' y.1 = Q := Function.update_self _ _ _
  have hP'n : ∀ k, k ≠ y.1 → P' k = 0 := fun k hk => Function.update_of_ne hk _ _
  have hP'S : ∀ k, P' k ∈ ((U σ).X k).SS (la k) := fun k => by
    by_cases hk : k = y.1
    · subst hk; rw [hP'y]; exact hQS
    · rw [hP'n k hk]
      exact (ReciprocityTheory.ChartRestriction.G.FD.siegelSpaceAlgebra_holds (E := D.host.E) D.R.r ((U σ).X k) (la k) (la k) 0).1.1
  have hP'0 : ∀ k, ∀ x ∉ ((U σ).X k).dom, P' k x = 0 := fun k x hx => by
    by_cases hk : k = y.1
    · subst hk; rw [hP'y]; exact Set.indicator_of_notMem hx _
    · rw [hP'n k hk]; rfl
  have hP'm : P' ∈ Formalism.L2.Pj.holSub (U σ).X la := Formalism.L2.Pj.holCusp_mem_holSub _ _ hP'S
  have hsf : ∀ k, ((U σ).X k).IsSec (la k) (P' k) := fun k => (hP'S k).1.1
  have hJ := hI (fun k x => ENNReal.ofReal (((U σ).X k).pnorm (la k) (P' k) x ^ 2))
    (fun k => ENNReal.measurable_ofReal.comp ((GlobalTheory.PeterssonCompare.measurable_pnorm _ _
      (hsf k).1.continuousOn (hP'0 k)).pow_const 2))
    (fun k γ hγ x hx => by simp only [GlobalTheory.PeterssonCompare.pnorm_lact _ (hsf k) hγ hx])
    (fun k b hb x hx => by simp only [FrameDegreeData.pnorm_rmul _ _ _ (hsf k).2.1 x hx b hb])
  rw [Finset.sum_eq_single y.1 (f := fun k => ∫⁻ z in FF k, ENNReal.ofReal (((U σ).X k).pnorm (la k) (P' k)
      (cpt ((U σ).X k) (x0 k) z) ^ 2) ∂(muF ((U σ).X k) (x0 k)))
      (fun k _ hk => by simp [hP'n k hk, Formalism.L2.Pj.pnorm_zero])
    (fun h => absurd (Finset.mem_univ _) h), hP'y,
    setLIntegral_congr_fun (hFF y.1).1 (g := fun z => ENNReal.ofReal (((U σ).X y.1).pnorm (la y.1) P
      (cpt ((U σ).X y.1) (x0 y.1) z) ^ 2)) (fun z hz => by simp only [hQP _ ((hFF y.1).2.1 hz)])] at hJ
  have hM := hI (fun k _ => if k = y.1 then 1 else 0) (fun _ => measurable_const) (fun _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ => rfl)
  rw [Finset.sum_eq_single y.1 (f := fun k => ∫⁻ z in FF k, (if k = y.1 then (1 : ℝ≥0∞) else 0)
      ∂(muF ((U σ).X k) (x0 k))) (fun k _ hk => by simp [hk]) (fun h => absurd (Finset.mem_univ _) h),
    if_pos rfl, setLIntegral_one] at hM
  set Cl := classesOver (D.sp.W j) (dict σ) (framesOn (U σ) Z) with hCl
  have hm : ∫⁻ q : AutQ (D.sp.W j), (if (dict σ q.out).1 = y.1 then (1 : ℝ≥0∞) else 0) ∂(muQ1 (D.sp.W j)) ≤
      muQ1 (D.sp.W j) Cl := by
    refine le_trans (lintegral_mono fun q => ?_) (lintegral_indicator_one_le Cl)
    split_ifs with hq
    · have : q ∈ Cl := by
        have h1 := hdom q.out
        show dict σ q.out ∈ framesOn (U σ) Z
        generalize dict σ q.out = z at hq h1
        obtain ⟨k, x⟩ := z
        obtain rfl : k = y.1 := hq
        exact GlobalTheory.FramesUnion.framesOn_of_mem D.host.E H Dw l Xo c D.R.r U σ hU Z _ _ x h1 hy
      simp [this]
    · exact zero_le
  have hN : petE (D.sp.W j) (dict σ) (muOn (U σ) (D.sp.W j) (dict σ) Z) la P' ^ 2 ≤ (muQ1 (D.sp.W j) Cl)⁻¹ *
      ∫⁻ q : AutQ (D.sp.W j), ENNReal.ofReal (((U σ).X (dict σ q.out).1).pnorm (la (dict σ q.out).1)
        (P' (dict σ q.out).1) (dict σ q.out).2 ^ 2) ∂(muQ1 (D.sp.W j)) := by
    have e : petE (D.sp.W j) (dict σ) (muOn (U σ) (D.sp.W j) (dict σ) Z) la P' ^ 2 =
        ∫⁻ q : AutQ (D.sp.W j), ‖ptN la P' (dict σ q.out)‖ₑ ^ 2 ∂(muOn (U σ) (D.sp.W j) (dict σ) Z) := by
      have := lintegral_rpow_eNorm_eq_rpow_eLpNorm' (μ := muOn (U σ) (D.sp.W j) (dict σ) Z)
        (f := fun q : AutQ (D.sp.W j) => ptN la P' (dict σ q.out)) (q := 2) (by norm_num)
      simpa [petE, ENNReal.rpow_natCast] using this.symm
    rw [e]
    show ∫⁻ q, _ ∂((muQ1 (D.sp.W j) Cl)⁻¹ • (muQ1 (D.sp.W j)).restrict Cl) ≤ _
    rw [lintegral_smul_measure, smul_eq_mul]
    refine mul_le_mul_right
      (le_trans (lintegral_mono' Measure.restrict_le_self le_rfl) (le_of_eq (lintegral_congr fun q => ?_))) _
    rw [Real.enorm_eq_ofReal (ptN_nonneg _ _ _), ← ENNReal.ofReal_pow (ptN_nonneg _ _ _)]
    rfl
  have hpos := pnorm_pos ((U σ).X y.1) (la y.1) y.2.2 hPy
  have hpt : ENNReal.ofReal (ptN la P' ⟨y.1, y.2.1⟩) ^ 2 =
      ENNReal.ofReal (((U σ).X y.1).pnorm (la y.1) P y.2.1 ^ 2) := by
    rw [ENNReal.ofReal_pow hpos.le]
    show ENNReal.ofReal (((U σ).X y.1).pnorm (la y.1) (P' y.1) y.2.1) ^ 2 = _
    rw [hP'y, hQP _ y.2.2]
  refine le_trans ?_ (le_iSup₂_of_le (f := fun P (_ : P ∈ Formalism.L2.Pj.holSub (U σ).X la) =>
    ENNReal.ofReal (ptN la P ⟨y.1, y.2.1⟩) ^ 2 /
      petE (D.sp.W j) (dict σ) (muOn (U σ) (D.sp.W j) (dict σ) Z) la P ^ 2) P' hP'm le_rfl)
  rw [hpt]
  refine le_div_of_mean (ENNReal.ofReal_pos.2 (pow_pos hpos 2)).ne' ENNReal.ofReal_ne_top hS0
    (ne_top_of_le_ne_top hST (Finset.single_le_sum (f := fun k => muF ((U σ).X k) (x0 k) (FF k))
      (fun _ _ => zero_le) (Finset.mem_univ y.1)))
    (fun h => setLIntegral_measure_zero _ _ h) hle hJ ?_ hN
  rw [← hM]
  gcongr

end GlobalTheory.BergLower
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormLowerBoundBergmanFunctionOnComponentStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

theorem _root_.GlobalTheory.T.cuspForm_lower_bound_bergmanFunction_on_component : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), GlobalTheory.LevGeo.Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∀ (G : WTZ D.host.E) (Z : Comp Xo c) (y : FPt (U σ).X), (⟨y.1, y.2.1⟩ : Σ k, Frame ((U σ).X k).Ψ D.R.r) ∈ framesOn (U σ) Z → ∀ β : ENNReal, (∀ (x0 : Frame ((U σ).X y.1).Ψ D.R.r) (FF : Set (ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd ((U σ).X y.1)))), ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth ((U σ).X y.1) x0 → ReciprocityTheory.ChartRestriction.G.AR.Up.IsFundSet ((U σ).X y.1) x0 FF → ∃ P ∈ ((U σ).X y.1).SS (modelWt (U σ) G y.1), P y.2.1 ≠ 0 ∧ β * ∫⁻ z in FF, ENNReal.ofReal (((U σ).X y.1).pnorm (modelWt (U σ) G y.1) P (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt ((U σ).X y.1) x0 z) ^ 2) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF ((U σ).X y.1) x0) ≤ ENNReal.ofReal (((U σ).X y.1).pnorm (modelWt (U σ) G y.1) P y.2.1 ^ 2) * ReciprocityTheory.ChartRestriction.G.AR.Up.muF ((U σ).X y.1) x0 FF) → β ≤ bergOn (U σ) (D.sp.W j) (dict σ) Z G y := by
  first | exact @GlobalTheory.BergLower.le_bergOn | exact GlobalTheory.BergLower.le_bergOn | (intros; apply GlobalTheory.BergLower.le_bergOn <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BergmanKernelThickPartEstimate

section

@[expose] public section



section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
namespace GlobalTheory.ThickBerg
open ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst MeasureTheory

theorem exp_neg_B_le_bergOn_of_mem_framesOn : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → HypothesesH → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP C => ∀ u1, Quo p i PP u1 → ∃ B : ℝ, 0 ≤ B ∧ lenT p i PP * B ≤ C * unitE p ∧ ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (σ : Y.d.c₂.F →+* ℂ), GoodEmb Y.d.c₂ σ → ∀ y : FPt (Y.U σ).X, (⟨y.1, y.2.1⟩ : Σ k, Frame ((Y.U σ).X k).Ψ (Fm.D x ι).R.r) ∈ framesOn (Y.U σ) Z → (Fm.L x ι).sc.b ≤ (Y.d.l₂.M : ℝ) * ((Y.U σ).X y.1).firstMinimumSq y.2.1 → ENNReal.ofReal (Real.exp (-B)) ≤ bergOn (Y.U σ) ((Fm.D x ι).sp.W ((i : ℕ) + 1)) (Y.dict σ) Z (wtOf (dat p i) u1 0) y := by
  intro _ _ _ hS _
  obtain ⟨C0, hC0, hpeak⟩ := GlobalTheory.T.exists_cusp_form_peak_at_injective_chart_frame
  have hnum := _root_.GlobalTheory.T.torus_length_lower_bound_quotient' hS
  refine (((hnum.and (_root_.GlobalTheory.CovTop.Sizes.hostN_alt (max 10 C0))).and _root_.GlobalTheory.CovTop.WtShape.wtN_z).and hS).imp
    fun Fm CH _ h => ?_
  obtain ⟨⟨⟨⟨C2, hC2, hN⟩, ⟨A, -, hH⟩⟩, ⟨C3, -, hW⟩⟩, ⟨C4, -, hSz⟩⟩ := h
  refine ⟨C0 * (C2 + 1), by positivity, ?_⟩
  obtain ⟨x0, hall⟩ := ((hN.and hH).and hW).and hSz
  refine ⟨x0, fun x hx hle ι p hp i hi Y hY u1 hu1 => ?_⟩
  obtain ⟨⟨⟨hN, hH⟩, hW⟩, hSz⟩ := hall x hx hle ι p hp
  obtain ⟨hZ24, hu⟩ := hN i hi
  obtain ⟨hTl1, hgap⟩ := hu u1 hu1
  have hHi := hH i
  have hWi := hW i
  have hSi := hSz i
  have hsig := hWi.sig
  have hm3 := (Fm.D x ι).R.m_add_three_le_k
  simp only [Ranks.sigW] at hsig
  have hp1 : 1 ≤ (dat p i).p := by omega
  have hq1 : 1 ≤ (dat p i).q := by omega
  have hf1 : (1 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast (by have := hHi.f8; omega : 1 ≤ (Fm.D x ι).R.f)
  have hr1 : (1 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast (by omega : 1 ≤ (Fm.D x ι).R.r)
  have hD1 : (1 : ℝ) ≤ (dimFlag (dat p i) : ℝ) := by
    rw [hWi.dim]
    have h2 : 1 ≤ (Fm.D x ι).R.r.choose 2 := Nat.choose_pos (by omega)
    have h8 := hHi.f8
    exact_mod_cast (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)))
  have hzb : zBase (Fm.L x ι) = ((Fm.D x ι).R.f * (Fm.D x ι).R.r) * (Fm.L x ι).sc.L := rfl
  obtain ⟨hA8, hC08, h100⟩ := nums ((Fm.D x ι).R.f * (Fm.D x ι).R.r) (Fm.L x ι).sc.L C0 _ _ _ _ _
    (one_le_mul_of_one_le_of_one_le hf1 hr1) hHi.big.2.1 ((le_max_right _ _).trans hHi.big.1)
    (hzb ▸ hHi.ppLow) (hzb ▸ hZ24) hD1 hWi.what₂.2 hSi.2.1
  have hl10 : 0 ≤ l1 u1 := by unfold l1; positivity
  refine ⟨C0 * (l1 u1 + ((Fm.D x ι).R.f * (Fm.D x ι).R.r) ^ 8), by positivity, ?_, fun Z σ hσ y hy hb => ?_⟩
  · have e : (lenT p i (Fm.parT x hx ι).PP : ℝ) * (C0 * (l1 u1 + ((Fm.D x ι).R.f * (Fm.D x ι).R.r) ^ 8)) =
        C0 * ((lenT p i (Fm.parT x hx ι).PP : ℝ) * l1 u1 + (lenT p i (Fm.parT x hx ι).PP : ℝ) * ((Fm.D x ι).R.f * (Fm.D x ι).R.r) ^ 8) := by ring
    rw [e, mul_add C0 C2 1, mul_one]
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add hTl1 hA8) hC0]
  · have hL := GlobalTheory.LawsDeep.levLaws _ p.T _ Y _ _ p.fw.laws ⟨Nat.le_add_left _ _, i.2⟩ hY.1
    have hg0 : ∀ q : ℕ, q.Prime → p.T.Q.l.GoodAt q :=
      Formalism.L2.Pj.goodAt_of_two_primes p.fw.laws.pins.2.1.1 ((Fm.D x ι).host.g_prime 0) ((Fm.D x ι).host.g_prime 1)
        (Fm.D x ι).host.g_ne
    have hg : ∀ q : ℕ, q.Prime → Y.d.l₂.GoodAt q := GlobalTheory.LawsDeep.goodAt_of_mul _ _ _ hY.1.lev.1.2.1 hg0
    have hU := hL.unf σ hσ
    have hM' : Y.d.l₂.M' = Y.d.l₂.M := by rw [Level.M', hY.1.lev.2, Nat.lcm_one_right]
    refine GlobalTheory.T.cuspForm_lower_bound_bergmanFunction_on_component (Fm.D x ι) ((i : ℕ) + 1) _ _ _ Y.d.Xo₂ Y.d.c₂ Y.U Y.dict hL σ hσ _ Z y hy _
      (fun x0 FF hx0 hFF => ?_)
    obtain ⟨x1, hx1, hla, htr⟩ := orth_transfer _ _ ((Y.U σ).X y.1)
      (modelWt (Y.U σ) (wtOf (dat p i) u1 0) y.1) y.2.1 y.2.2
    obtain ⟨hg1, hg2, hl1, hcard⟩ := modelWt_shape _ _ _ _ _ _ σ _ (Y.U σ) hσ hU hp1 hq1 u1
      (lenT p i (Fm.parT x hx ι).PP) (fun τ a b hab => by exact_mod_cast hgap τ a b hab) y.1
    have hcf : (((Y.U σ).X y.1).Ψ.card : ℝ) = (Fm.D x ι).R.f := by
      rw [hcard]; exact_mod_cast hWi.card
    have hball := ball_injects _ _ _ _ _ _ σ _ (Y.U σ) hσ hU hg hp1 hq1 y.1 x1 hx1 (by
      rw [hcf, hM', hla]; exact h100.trans hb)
    have hp0 := (hU.2.1 y.1).1
    have hr := hU.1
    obtain ⟨P, hP, hPx, hle⟩ := hpeak _ _ ((Y.U σ).X y.1) (modelWt (Y.U σ) (wtOf (dat p i) u1 0) y.1) x1
      (by rw [hp0]; exact hq1) (by rw [hp0, hr]; exact Nat.lt_add_of_pos_left hp1) hx1
      (fun τ a b hab hb0 => by rw [hcf]; exact hC08.trans (hg1 τ a b hab hb0))
      (fun τ a b ha hb' => by rw [hcf]; exact hC08.trans (hg2 τ a b ha hb')) hball x0 FF hx0 hFF
    obtain ⟨hPy, hpn⟩ := htr P hP hPx
    refine ⟨P, hP, hPy, ?_⟩
    rw [hpn]
    rw [hl1, hcf] at hle
    exact hle
end GlobalTheory.ThickBerg
end
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

theorem _root_.GlobalTheory.T.exp_neg_B_le_bergOn_of_la1sq_bound : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → HypothesesH → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP C => ∀ u1, Quo p i PP u1 → ∃ B : ℝ, 0 ≤ B ∧ lenT p i PP * B ≤ C * unitE p ∧ ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (σ : Y.d.c₂.F →+* ℂ), GoodEmb Y.d.c₂ σ → ∀ y : FPt (Y.U σ).X, (⟨y.1, y.2.1⟩ : Σ k, Frame ((Y.U σ).X k).Ψ (Fm.D x ι).R.r) ∈ framesOn (Y.U σ) Z → (Fm.L x ι).sc.b ≤ (Y.d.l₂.M : ℝ) * ((Y.U σ).X y.1).firstMinimumSq y.2.1 → ENNReal.ofReal (Real.exp (-B)) ≤ bergOn (Y.U σ) ((Fm.D x ι).sp.W ((i : ℕ) + 1)) (Y.dict σ) Z (wtOf (dat p i) u1 0) y := by
  first | exact @_root_.GlobalTheory.ThickBerg.exp_neg_B_le_bergOn_of_mem_framesOn | exact _root_.GlobalTheory.ThickBerg.exp_neg_B_le_bergOn_of_mem_framesOn | (intros; apply _root_.GlobalTheory.ThickBerg.exp_neg_B_le_bergOn_of_mem_framesOn <;> assumption)
end
end
end
end
