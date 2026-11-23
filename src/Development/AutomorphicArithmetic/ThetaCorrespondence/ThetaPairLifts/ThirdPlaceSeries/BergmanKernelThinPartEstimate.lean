module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CardMulSuccLeTwoMulNcolCopy
public import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformizationLawsOfGoodDeepCoverStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspOnRestrict
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeySectionInverseRootTwistingSectionSpreadStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulInvPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwSecOfConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasUnramifiedIntegralFramedPointsOfGoodPlacesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNumberFieldPoint
public import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FlatValStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QuoShape
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadingStatement
import Formalism.LocalToGlobal.ProjectiveLattices.NormLaws

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameExponentialVolumeLarge

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

namespace GlobalTheory.ThinBerg

open MeasureTheory
open scoped ENNReal

theorem pnorm_pos' {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (la : Wt X.Ψ r)
    {P : Frame X.Ψ r → ℂ} {x : Frame X.Ψ r} (hx : x ∈ X.dom) (hP : P x ≠ 0) : 0 < X.pnorm la P x := by
  have hd : ∀ τ i, dmin X.Gm x τ i ≠ 0 := fun τ i h => by
    have := (hx τ).2 i
    rw [h] at this
    simp at this
  unfold Data.pnorm
  exact mul_pos (norm_pos_iff.2 hP) (Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ =>
    Real.rpow_pos_of_pos (norm_pos_iff.2 (div_ne_zero (hd _ _) (hd _ _))) _)

theorem le_bergOn_of_ratio {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {σ : c.F →+* ℂ} (U : Unf Xo c σ r)
    {D : D7} (V : HSp D) (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (hd : ∀ g, (dict g).2 ∈ (U.X (dict g).1).dom)
    (Z : Comp Xo c) (G : WTZ E) (y : FPt U.X) (P : FDSec U.X) (hP : P ∈ holSub U.X (modelWt U G)) {e : ℝ}
    (he : 0 < e) (hy : 0 < ptN (modelWt U G) P ⟨y.1, y.2.1⟩)
    (hb : ∀ z : FPt U.X, e * ptN (modelWt U G) P ⟨z.1, z.2.1⟩ ≤ ptN (modelWt U G) P ⟨y.1, y.2.1⟩) :
    ENNReal.ofReal (e ^ 2) ≤ bergOn U V dict Z G y := by
  set A : ℝ≥0∞ := ENNReal.ofReal (ptN (modelWt U G) P ⟨y.1, y.2.1⟩) with hA
  have hA0 : A ≠ 0 := by rw [hA]; exact (ENNReal.ofReal_pos.2 hy).ne'
  have hsup : supE U.X (modelWt U G) P ≤ ENNReal.ofReal e⁻¹ * A := by
    unfold supE
    refine iSup_le fun z => ?_
    rw [hA, ← ENNReal.ofReal_mul (inv_nonneg.2 he.le)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h := hb z
    rw [le_inv_mul_iff₀ he]
    exact h
  have hpet : petE V dict (muOn U V dict Z) (modelWt U G) P ≤ ENNReal.ofReal e⁻¹ * A :=
    (petE_le_supE V dict _ (muPart_univ_le V dict _) hd _ P).trans hsup
  unfold bergOn bergE
  refine le_trans ?_ (le_iSup₂_of_le P hP le_rfl)
  rw [ENNReal.le_div_iff_mul_le (Or.inr (pow_ne_zero 2 hA0)) (Or.inr (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))]
  calc ENNReal.ofReal (e ^ 2) * petE V dict (muOn U V dict Z) (modelWt U G) P ^ 2
      ≤ ENNReal.ofReal (e ^ 2) * (ENNReal.ofReal e⁻¹ * A) ^ 2 := by gcongr
    _ = ENNReal.ofReal (e ^ 2 * e⁻¹ ^ 2) * A ^ 2 := by
        rw [mul_pow, ← mul_assoc, ENNReal.ofReal_mul (sq_nonneg e), ENNReal.ofReal_pow (inv_nonneg.2 he.le)]
    _ = A ^ 2 := by
        rw [← mul_pow, mul_inv_cancel₀ he.ne', one_pow, ENNReal.ofReal_one, one_mul]

end GlobalTheory.ThinBerg

namespace GlobalTheory.ThinBerg

open MeasureTheory

end GlobalTheory.ThinBerg
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsConstantTwistOfThinDivisor

section

@[expose] public section

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt


noncomputable section
namespace GlobalTheory.ThinTwist
open GlobalTheory.FlatTw GlobalTheory.FlatLine in
theorem exists_constant_twist_of_thin_divisor (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) {D : D7} (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ)
    (hT : LawsJ T) (hj : InR D j) (hY : Y.Good e o) (hF : FlatExists Y.U (xiR D))
    (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)) (w₀ : Psi T.Q.H → ℤ) (m : ℕ) (Z : Comp Y.d.Xo₂ Y.d.c₂)
    (σ : Y.d.c₂.F →+* ℂ) (hσ : GoodEmb Y.d.c₂ σ) {f : Rul Y.d.Xo₂ Y.d.c₂}
    (hf : f ∈ cuspW Y.d.Xo₂ Y.d.c₂ Y.U (wtOf (T.Q.Dw j) (u + parWt (T.Q.Dw j) w₀) m)) :
    ∃ g ∈ cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0), ∃ K : ℝ, 0 < K ∧
      ∀ z ∈ framesOn (Y.U σ) Z, ptN (modelWt (Y.U σ) (wtOf (T.Q.Dw j) u 0)) (rdU (Y.U σ) g) z =
        K * ptN (modelWt (Y.U σ) (wtOf (T.Q.Dw j) (u + parWt (T.Q.Dw j) w₀) m)) (rdU (Y.U σ) f) z := by
  have hL := GlobalTheory.T.complexUniformizationLaws_of_goodDeepCover D T j Y e o hT hj hY
  have hN := GlobalTheory.T.hasUnramifiedIntegralFramedPoints_of_goodPlaces hP.q18 hP.q1 hP.p5 _ _ _ Y.d.l₂ Y.d.Xo₂ Y.d.c₂ hL.pos
  obtain ⟨hK, ht⟩ := GlobalTheory.T.exists_keySection_inverseRoot_twistingSection_spread _ _ _ _ _ _ _ Y.U hL.unf (xiR D) hL.xi hL.geo hL.pos hL.good hN
  obtain ⟨t, ht1, ht2⟩ := ht Z
  obtain ⟨s, -, -, -, hs1, hs2⟩ := (GlobalTheory.FlatTwisting.twSec_of_flat _ _ _ _ _ _ _ Y.U (xiR D) _ hK hL.unf hL.pos hN).1 Z (-w₀) _
      (FlatSec.shift (hasPts Y.U hL.pos hL.good hL.unf Z) (fun τ => (hF.nonempty Z τ).some) (-w₀))
      ((Set.finite_iUnion fun τ => finite_flDefect_vw (Dw := T.Q.Dw j) (c := Y.d.c₂) τ).subset fun w hw => by
        by_contra hn
        simp only [Set.mem_iUnion, Function.mem_support, not_exists, not_not] at hn
        exact hw (by simp [Finset.sum_apply, hn]))
  obtain ⟨tw, -, -⟩ := GlobalTheory.CombTw.exists_twSec_comb _ _ _ _ _ _ _ Y.U hL.unf (xiR D) _ Z u w₀ m _ s t hs1 hs2 ht1 ht2
  set G := wtOf (T.Q.Dw j) (u + parWt (T.Q.Dw j) w₀) m with hGdef
  have hB : Even G.2 := GlobalTheory.AllWt.even_wtOf _ _
  have hGG : G + (wtOf (T.Q.Dw j) u 0 - G) = wtOf (T.Q.Dw j) u 0 := add_sub_cancel _ _
  have hfZ : idem Z * f ∈ cuspOn Y.U Z G :=
    ⟨GlobalTheory.CompRestr.idem_mul_mem_cuspW hL.unf Z hf, by rw [mul_comm]; exact mul_mem_suppOn _ (idem_mem_suppOn Z)⟩
  have hmem : f * tw.sig ∈ cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0) := by
    have h := tw.cusp_sig G hB _ hfZ
    rwa [hGG, mul_comm (idem Z) f, mul_assoc, tw.idem_sig] at h
  have key : ∀ z ∈ framesOn (Y.U (goodOf Y.d.c₂ σ)) Z,
      homN (Y.U (goodOf Y.d.c₂ σ)) (xiR D) (G + (wtOf (T.Q.Dw j) u 0 - G)) (f * tw.sig) z =
        homN (Y.U (goodOf Y.d.c₂ σ)) (xiR D) G f z * tw.cInf σ := fun z hz => tw.homN_mul_sig hB f hz
  have e : goodOf Y.d.c₂ σ = σ := if_pos hσ
  rw [e, hGG] at key
  have hl := lieFacZ_pos (Dw := T.Q.Dw j) (xiR D) (wtOf (T.Q.Dw j) u 0)
  refine ⟨f * tw.sig, hmem, lieFacZ (T.Q.Dw j) (xiR D) G * tw.cInf σ / lieFacZ (T.Q.Dw j) (xiR D) (wtOf (T.Q.Dw j) u 0),
    div_pos (mul_pos (lieFacZ_pos _ _) (tw.cInf_pos σ)) hl, fun z hz => ?_⟩
  have h1 := key z hz
  unfold homN at h1
  rw [div_mul_eq_mul_div, eq_div_iff hl.ne']
  linear_combination h1
end GlobalTheory.ThinTwist
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspFormBoundedOnFrames

section

@[expose] public section



section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt


noncomputable section
namespace GlobalTheory.ThinTwist
theorem twist_thin_alt_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → HypothesesH → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ u1, Quo p i PP u1 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (σ : Y.d.c₂.F →+* ℂ), GoodEmb Y.d.c₂ σ → ∀ y : FPt (Y.U σ).X, (⟨y.1, y.2.1⟩ : Σ k, Frame ((Y.U σ).X k).Ψ (Fm.D x ι).R.r) ∈ framesOn (Y.U σ) Z → ∀ f ∈ cuspW Y.d.Xo₂ Y.d.c₂ Y.U (GlobalTheory.RefSum.GOf p i u1), ∃ g ∈ cuspOn Y.U Z (wtOf (dat p i) u1 0), ∃ K : ℝ, 0 < K ∧ ∀ z : Σ k, Frame ((Y.U σ).X k).Ψ (Fm.D x ι).R.r, z ∈ framesOn (Y.U σ) Z → ptN (modelWt (Y.U σ) (wtOf (dat p i) u1 0)) (rdU (Y.U σ) g) z = K * ptN (modelWt (Y.U σ) (GlobalTheory.RefSum.GOf p i u1)) (rdU (Y.U σ) f) z := by
  intro hP _ _ hS hFD
  have R := _root_.GlobalTheory.T.weight_conditions_at_index'
  have F := _root_.GlobalTheory.T.abs_flat_c1_add_logOm_le_and_logSum_badPrimes_le hFD
  have Q := _root_.GlobalTheory.RefSum.QuoShape.quo_shape_dom_lastPos_weight_eq hS
  unfold _root_.GlobalTheory.CovTop.CoversCondition _root_.GlobalTheory.CovTop.LiftsCondition at *
  refine (R.and (F.and Q)).imp fun Fm CH _ h => ?_
  obtain ⟨⟨C1, h1, e1⟩, ⟨C2, h2, e2⟩, ⟨C3, h3, e3⟩⟩ := h
  refine ⟨C1, h1, ?_⟩
  obtain ⟨x0, hx0⟩ := e1.and (e2.and e3)
  refine ⟨x0, fun x hx hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨hA, hB, hC⟩ := hx0 x hx hle ι p hp
  obtain ⟨hL, -, -, -, hj, -⟩ := hA i hi
  have hFl := (hB i hi Y hY).2.2.1
  intro u1 hq Z σ hσ _ _ f hf
  obtain ⟨-, -, -, -, -, -, -, -, hG⟩ := hC i hi u1 hq
  rw [hG] at hf ⊢
  exact _root_.GlobalTheory.ThinTwist.exists_constant_twist_of_thin_divisor hP p.T _ Y _ _ hL hj hY.1 hFl u1 _ _ Z σ hσ hf
end GlobalTheory.ThinTwist
theorem _root_.GlobalTheory.T.cusp_form_bounded_on_frames_alt_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → HypothesesH → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ u1, Quo p i PP u1 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (σ : Y.d.c₂.F →+* ℂ), GoodEmb Y.d.c₂ σ → ∀ y : FPt (Y.U σ).X, (⟨y.1, y.2.1⟩ : Σ k, Frame ((Y.U σ).X k).Ψ (Fm.D x ι).R.r) ∈ framesOn (Y.U σ) Z → ∀ f ∈ cuspW Y.d.Xo₂ Y.d.c₂ Y.U (GlobalTheory.RefSum.GOf p i u1), ∃ g ∈ cuspOn Y.U Z (wtOf (dat p i) u1 0), ∃ K : ℝ, 0 < K ∧ ∀ z : Σ k, Frame ((Y.U σ).X k).Ψ (Fm.D x ι).R.r, z ∈ framesOn (Y.U σ) Z → ptN (modelWt (Y.U σ) (wtOf (dat p i) u1 0)) (rdU (Y.U σ) g) z = K * ptN (modelWt (Y.U σ) (GlobalTheory.RefSum.GOf p i u1)) (rdU (Y.U σ) f) z := _root_.GlobalTheory.ThinTwist.twist_thin_alt_alt
end
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BergmanKernelThinPartEstimate

section

@[expose] public section



section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
namespace GlobalTheory.ThinBerg
open MeasureTheory
open scoped ENNReal
end GlobalTheory.ThinBerg
namespace GlobalTheory.ThinBerg
open MeasureTheory
theorem bergman_kernel_bound_thin_part_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → HypothesesH → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ u1, Quo p i PP u1 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (σ : Y.d.c₂.F →+* ℂ), GoodEmb Y.d.c₂ σ → ∀ y : FPt (Y.U σ).X, (⟨y.1, y.2.1⟩ : Σ k, Frame ((Y.U σ).X k).Ψ (Fm.D x ι).R.r) ∈ framesOn (Y.U σ) Z → (Y.d.l₂.M : ℝ) * ((Y.U σ).X y.1).firstMinimumSq y.2.1 < (Fm.L x ι).sc.b → ENNReal.ofReal (Real.exp (-(2 * (ReciprocityTheory.ChartRestriction.G.I2.PT.f (Fm.D x ι).host.E : ℝ) / (ReciprocityTheory.ChartRestriction.G.I2.PT.rd (Fm.D x ι).host.E ^ 2 * ((Y.U σ).X y.1).la1 y.2.1 ^ 2) / 625))) ≤ bergOn (Y.U σ) ((Fm.D x ι).sp.W ((i : ℕ) + 1)) (Y.dict σ) Z (wtOf (dat p i) u1 0) y := by
  intro h1 h2 h3 h4 h5
  have hT := _root_.GlobalTheory.T.thin_divisor_pivot_bound_alt h1 h2 h3 h4 h5
  have hW := _root_.GlobalTheory.T.cusp_form_bounded_on_frames_alt_alt h1 h2 h3 h4 h5
  unfold _root_.GlobalTheory.CovTop.CoversCondition _root_.GlobalTheory.CovTop.LiftsCondition at hT hW ⊢
  refine Closed.imp (Closed.and hT hW) ?_
  rintro eps Fm CH - ⟨⟨C1, hC1, a1, H1⟩, ⟨C2, hC2, a2, H2⟩⟩
  refine ⟨C1, hC1, max a1 a2, fun x hx hle ι p hp i hi Y hY u1 hu Z σ hσ y hyZ hth => ?_⟩
  obtain ⟨f, hf, hfy, hfb⟩ := H1 x hx ((le_max_left _ _).trans hle) ι p hp i hi Y hY u1 hu Z σ hσ y hyZ hth
  obtain ⟨g, hg, K, hK, hgK⟩ := H2 x hx ((le_max_right _ _).trans hle) ι p hp i hi Y hY u1 hu Z σ hσ y hyZ f hf
  obtain ⟨th, hr, -, hDU⟩ := hY.1.dictU σ hσ
  have hd := Formalism.L2.Pj.dict_dom_of hDU
  clear H1 H2
  have he : ∀ φ : ℝ, Real.exp (-(φ / 625)) = Real.exp (-(φ / 1250)) ^ 2 := fun φ => by
    rw [sq, ← Real.exp_add]; congr 1; ring
  rw [he]
  have hgW : g ∈ cuspW Y.d.Xo₂ Y.d.c₂ Y.U (wtOf (dat p i) u1 0) := cuspOn_le _ _ _ hg
  have hgS : g ∈ suppOn Z := (Submodule.mem_inf.1 hg).2
  have hP := (mem_cuspW.1 hgW).2 σ hσ
  have hfy' : 0 < ptN (modelWt (Y.U σ) (GlobalTheory.RefSum.GOf p i u1)) (rdU (Y.U σ) f) ⟨y.1, y.2.1⟩ :=
    pnorm_pos' _ _ y.2.2 hfy
  have hgy : ptN (modelWt (Y.U σ) (wtOf (dat p i) u1 0)) (rdU (Y.U σ) g) ⟨y.1, y.2.1⟩ =
      K * ptN (modelWt (Y.U σ) (GlobalTheory.RefSum.GOf p i u1)) (rdU (Y.U σ) f) ⟨y.1, y.2.1⟩ := hgK _ hyZ
  refine le_bergOn_of_ratio (Y.U σ) _ (Y.dict σ) hd Z _ y _ hP (Real.exp_pos _) ?_ ?_
  · rw [hgy]; exact mul_pos hK hfy'
  · intro z
    by_cases hz : (⟨z.1, z.2.1⟩ : Σ k, Frame ((Y.U σ).X k).Ψ (Fm.D x ι).R.r) ∈ framesOn (Y.U σ) Z
    · rw [hgK _ hz, hgy]
      have := hfb z hz
      nlinarith
    · have h0 : rdU (Y.U σ) g z.1 z.2.1 = 0 := rdU_eq_zero (Y.U σ) hgS hz
      have hz0 : ptN (modelWt (Y.U σ) (wtOf (dat p i) u1 0)) (rdU (Y.U σ) g) ⟨z.1, z.2.1⟩ = 0 := by
        simp only [ptN, Data.pnorm, h0, norm_zero, zero_mul]
      rw [hz0, mul_zero]
      exact ptN_nonneg _ _ _
end GlobalTheory.ThinBerg
end
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

theorem _root_.GlobalTheory.T.bergman_kernel_thin_part_estimate_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → HypothesesH → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ u1, Quo p i PP u1 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (σ : Y.d.c₂.F →+* ℂ), GoodEmb Y.d.c₂ σ → ∀ y : FPt (Y.U σ).X, (⟨y.1, y.2.1⟩ : Σ k, Frame ((Y.U σ).X k).Ψ (Fm.D x ι).R.r) ∈ framesOn (Y.U σ) Z → (Y.d.l₂.M : ℝ) * ((Y.U σ).X y.1).firstMinimumSq y.2.1 < (Fm.L x ι).sc.b → ENNReal.ofReal (Real.exp (-(2 * (ReciprocityTheory.ChartRestriction.G.I2.PT.f (Fm.D x ι).host.E : ℝ) / (ReciprocityTheory.ChartRestriction.G.I2.PT.rd (Fm.D x ι).host.E ^ 2 * ((Y.U σ).X y.1).la1 y.2.1 ^ 2) / 625))) ≤ bergOn (Y.U σ) ((Fm.D x ι).sp.W ((i : ℕ) + 1)) (Y.dict σ) Z (wtOf (dat p i) u1 0) y := by
  first | exact @_root_.GlobalTheory.ThinBerg.bergman_kernel_bound_thin_part_alt | exact _root_.GlobalTheory.ThinBerg.bergman_kernel_bound_thin_part_alt | (intros; apply _root_.GlobalTheory.ThinBerg.bergman_kernel_bound_thin_part_alt <;> assumption)
end
end
end
end
