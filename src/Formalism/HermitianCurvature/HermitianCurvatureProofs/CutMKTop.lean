module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutMK2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CornerBlockActionInvariant
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXMTA
public import Formalism.DoubleCosetMeasures.Statement
public import Formalism.HermitianCurvature.StatementG
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsHaarStabilizer
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXMTB
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormRankZeroApply
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LowerParabolicCoordinates
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.CategoryTheory.Countable
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXMkCpt
public import Formalism.HermitianCurvature.StatementU
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CornerBlockActionInvariant
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormRankZeroApply
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftFubiniNormalizedTower
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ReproducingFormulaReduction
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Tactic.TypeStar

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXMkTopCut

section

@[expose] public section

noncomputable section

open Matrix MeasureTheory
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutEXMT

open Formalism.FourierDecayAlt

def MkTopCut : Prop :=
  ∀ r : ℕ, ∃ β : (Fin r → Fin r → ℂ) → ℝ,
    ContDiffOn ℝ ∞ β {Z | (Matrix.of Z).det ≠ 0} ∧
    (∀ Z : Fin r → Fin r → ℂ, (Matrix.of Z).det ≠ 0 →
      Integrable (fun v : G.UT r → ℂ => β (Matrix.of.symm (Matrix.of Z * G.upper v))) ∧
        ∫ v : G.UT r → ℂ, β (Matrix.of.symm (Matrix.of Z * G.upper v)) = 1) ∧
    ∀ (X : Type) [TopologicalSpace X] (K : Set ((Fin r → Fin r → ℂ) × X)), IsCompact K →
      (∀ q ∈ K, (Matrix.of q.1).det ≠ 0) →
      ∃ K' : Set ((Fin r → Fin r → ℂ) × X), IsCompact K' ∧
        (∀ q ∈ K', (Matrix.of q.1).det ≠ 0 ∧ ∃ q₀ ∈ K, q.2 = q₀.2) ∧
        ∀ q : (Fin r → Fin r → ℂ) × X, (Matrix.of q.1).det ≠ 0 → β q.1 ≠ 0 →
          (∃ u : Matrix (Fin r) (Fin r) ℂ, Formalism.DoubleCosetMeasures.IsUpUni u ∧ (Matrix.of.symm (Matrix.of q.1 * u), q.2) ∈ K) →
          q ∈ K'

end Formalism.FourierDecayAlt.P.CutEXMT
end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXMTC

section

@[expose] public section

noncomputable section

open Matrix MeasureTheory
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutEXMT

open Formalism.FourierDecayAlt

variable {n : ℕ}

theorem upper_utc {M : Matrix (Fin n) (Fin n) ℂ} (hM : M ∈ C2.UTset n) : G.upper (StabilizerDisintegration.utc M) = M := by
  ext i j
  simp only [G.upper, G.strictUpper, StabilizerDisintegration.utc, Matrix.add_apply, Matrix.one_apply, Matrix.of_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · rw [dite_eq_left h, if_neg (ne_of_lt h), zero_add]
  · rw [dite_eq_right (lt_irrefl _), if_pos rfl, hM.2, add_zero]
  · rw [dite_eq_right (not_lt.2 h.le), if_neg (ne_of_gt h), hM.1 i j h, add_zero]

theorem upper_ut (v : G.UT n → ℂ) : G.upper v ∈ C2.UTset n := by
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · simp [G.upper, G.strictUpper, not_lt.2 h.le, ne_of_gt h]
  · simp [G.upper, G.strictUpper]

section gam

variable {r : ℕ} {X : Type}

def Gam (p : ((Fin r → Fin r → ℂ) × X) × (G.UT r → ℂ)) : (Fin r → Fin r → ℂ) × X :=
  (Matrix.of.symm (Matrix.of p.1.1 * Wm (Matrix.of p.1.1) * G.upper p.2), p.1.2)

theorem Gam_det (p : ((Fin r → Fin r → ℂ) × X) × (G.UT r → ℂ)) :
    (Matrix.of (Gam p).1).det = (Matrix.of p.1.1).det := by
  simp only [Gam, Equiv.apply_symm_apply]
  rw [Matrix.det_mul, Matrix.det_mul, C2x2.ut_det (Wm_ut _), C2x2.ut_det (upper_ut p.2), mul_one, mul_one]

theorem Gam_eq (q : (Fin r → Fin r → ℂ) × X) (u : Matrix (Fin r) (Fin r) ℂ) (hdet : (Matrix.of q.1).det ≠ 0)
    (hu : u ∈ C2.UTset r) : Gam ((Matrix.of.symm (Matrix.of q.1 * u), q.2), StabilizerDisintegration.utc (Sm (Matrix.of q.1))) = q := by
  simp only [Gam, Equiv.apply_symm_apply]
  rw [Wm_mul hdet hu, upper_utc (Sm_ut _), Matrix.mul_assoc (Matrix.of q.1) u,
    Matrix.mul_nonsing_inv_cancel_left _ _ (C2x2.ut_unit hu), Matrix.mul_assoc, Wm_mul_Sm, Matrix.mul_one]
  rfl

theorem Gam_cont [TopologicalSpace X] (S : Set (((Fin r → Fin r → ℂ) × X) × (G.UT r → ℂ)))
    (hS : ∀ p ∈ S, (Matrix.of p.1.1).det ≠ 0) : ContinuousOn Gam S := by
  have hW : ∀ a b : Fin r, ContinuousOn (fun p : ((Fin r → Fin r → ℂ) × X) × (G.UT r → ℂ) => Wm (Matrix.of p.1.1) a b) S :=
    fun a b => (cd_Wm a b).continuousOn.comp (continuous_fst.comp continuous_fst).continuousOn fun p hp => hS p hp
  refine ContinuousOn.prodMk (continuousOn_pi.2 fun a => continuousOn_pi.2 fun b => ?_)
    (continuous_snd.comp continuous_fst).continuousOn
  have e : ∀ p : ((Fin r → Fin r → ℂ) × X) × (G.UT r → ℂ),
      (Gam p).1 a b = ∑ c : Fin r, (∑ d : Fin r, p.1.1 a d * Wm (Matrix.of p.1.1) d c) * G.upper p.2 c b := by
    intro p
    simp only [Gam]
    rfl
  have key : ContinuousOn (fun p : ((Fin r → Fin r → ℂ) × X) × (G.UT r → ℂ) =>
      ∑ c : Fin r, (∑ d : Fin r, p.1.1 a d * Wm (Matrix.of p.1.1) d c) * G.upper p.2 c b) S := by
    refine continuousOn_finsetSum _ fun c _ => ContinuousOn.mul (continuousOn_finsetSum _ fun d _ => ?_) ?_
    · exact (((continuous_apply_apply a d).comp (continuous_fst.comp continuous_fst)).continuousOn).mul (hW d c)
    · exact ((continuous_apply_apply c b).comp (Formalism.FourierDecayAlt.P.Dx2.SL.cont_upper.comp continuous_snd)).continuousOn
  exact key.congr fun p _ => e p

end gam

theorem top_truncation_construction : MkTopCut := by
  intro r
  let φ : ContDiffBump (0 : G.UT r → ℂ) := ⟨1, 2, one_pos, one_lt_two⟩
  set β₀ : (G.UT r → ℂ) → ℝ := φ.normed volume with hβ₀
  have hcont : Continuous β₀ := φ.continuous_normed
  refine ⟨fun Z => β₀ (StabilizerDisintegration.utc (Sm (Matrix.of Z))), ?_, ?_, ?_⟩
  · have hS : ContDiffOn ℝ ∞ (fun Z : Fin r → Fin r → ℂ => StabilizerDisintegration.utc (Sm (Matrix.of Z)))
        {Z | (Matrix.of Z).det ≠ 0} :=
      contDiffOn_pi.2 fun q => cd_Sm q.1.1 q.1.2
    exact (φ.contDiff_normed (n := ⊤)).comp_contDiffOn hS
  · intro Z hZ
    have hmp := Formalism.FourierDecayAlt.P.StabilizerDisintegration.HC.mp_UTleft (Sm_ut (Matrix.of Z))
    have hfun : (fun v : G.UT r → ℂ => β₀ (StabilizerDisintegration.utc (Sm (Matrix.of (Matrix.of.symm (Matrix.of Z * G.upper v)))))) =
        fun v => β₀ (StabilizerDisintegration.utc (Sm (Matrix.of Z) * G.upper v)) := by
      funext v
      simp only [Equiv.apply_symm_apply]
      rw [Sm_mul hZ (upper_ut v)]
    show Integrable (fun v : G.UT r → ℂ => β₀ (StabilizerDisintegration.utc (Sm (Matrix.of (Matrix.of.symm (Matrix.of Z * G.upper v)))))) ∧
      ∫ v : G.UT r → ℂ, β₀ (StabilizerDisintegration.utc (Sm (Matrix.of (Matrix.of.symm (Matrix.of Z * G.upper v))))) = 1
    rw [hfun]
    constructor
    · have hi := (integrable_map_measure hcont.aestronglyMeasurable hmp.measurable.aemeasurable).1
        (by rw [hmp.map_eq]; exact φ.integrable_normed)
      exact hi
    · rw [← integral_map hmp.measurable.aemeasurable hcont.aestronglyMeasurable, hmp.map_eq]
      exact φ.integral_normed
  · intro X _ K hK hKdet
    have hC₀ : IsCompact (tsupport β₀) := φ.hasCompactSupport_normed
    refine ⟨Gam '' (K ×ˢ tsupport β₀), (hK.prod hC₀).image_of_continuousOn (Gam_cont _ fun p hp => hKdet _ hp.1), ?_, ?_⟩
    · rintro q ⟨⟨q', c⟩, ⟨hq', -⟩, rfl⟩
      exact ⟨by rw [Gam_det]; exact hKdet q' hq', q', hq', rfl⟩
    · rintro q hdet hβ ⟨u, hu, hK'⟩
      have huT : u ∈ C2.UTset r := ⟨fun i j h => hu.1 h, hu.2⟩
      exact ⟨((Matrix.of.symm (Matrix.of q.1 * u), q.2), StabilizerDisintegration.utc (Sm (Matrix.of q.1))),
        ⟨hK', subset_tsupport _ hβ⟩, Gam_eq q u hdet huT⟩

end Formalism.FourierDecayAlt.P.CutEXMT
end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXMkTopBump

section

@[expose] public section

noncomputable section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutEX.MkTopBump

theorem bump_two {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    (f g : E → ℂ) (hf : Continuous f) (hg : Continuous g) (hf0 : f 0 = 1) (hg0 : g 0 = 1) :
    ∃ b : E → ℝ, ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧ (∫ x, (b x : ℂ) * f x ∂μ) ≠ 0 ∧
      (∫ x, (b x : ℂ) * g x ∂μ) ≠ 0 := by
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuousAt_iff.1 hf.continuousAt (1 / 2 : ℝ) (by norm_num)
  obtain ⟨δ', hδ', hδg⟩ := Metric.continuousAt_iff.1 hg.continuousAt (1 / 2 : ℝ) (by norm_num)
  have hm : 0 < min δ δ' := lt_min hδ hδ'
  let B : ContDiffBump (0 : E) := ⟨min δ δ' / 4, min δ δ' / 2, by positivity, by linarith⟩
  set b : E → ℝ := fun x => B x with hbdef
  have hbd : ContDiff ℝ ∞ b := B.contDiff
  have hbc : HasCompactSupport b := B.hasCompactSupport
  have hbnn : ∀ x, 0 ≤ b x := fun x => B.nonneg
  have hbcont : Continuous b := B.continuous
  have hbint : 0 < ∫ x, b x ∂μ := B.integral_pos
  have hbs : tsupport b ⊆ Metric.ball (0 : E) (min δ δ') := by
    rw [show tsupport b = Metric.closedBall (0 : E) (min δ δ' / 2) from B.tsupport_eq]
    exact Metric.closedBall_subset_ball (by linarith)
  have aux : ∀ h : E → ℂ, Continuous h →
      (∀ x, dist x 0 < min δ δ' → ‖h x - 1‖ < 1 / 2) → (∫ x, (b x : ℂ) * h x ∂μ) ≠ 0 := by
    intro h hh hs
    have hbC : Continuous (fun x => (b x : ℂ)) := Complex.continuous_ofReal.comp hbcont
    have hbcC : HasCompactSupport (fun x => (b x : ℂ)) := hbc.comp_left Complex.ofReal_zero
    have hi1 : Integrable (fun x => (b x : ℂ)) μ := hbC.integrable_of_hasCompactSupport hbcC
    have hi2 : Integrable (fun x => (b x : ℂ) * (h x - 1)) μ :=
      (hbC.mul (hh.sub continuous_const)).integrable_of_hasCompactSupport (hbcC.mul_right)
    have hi3 : Integrable (fun x => b x * (1 / 2 : ℝ)) μ :=
      (hbcont.integrable_of_hasCompactSupport hbc).mul_const _
    have split : (∫ x, (b x : ℂ) * h x ∂μ) = (∫ x, (b x : ℂ) ∂μ) + ∫ x, (b x : ℂ) * (h x - 1) ∂μ := by
      rw [← integral_add hi1 hi2]
      congr 1
      funext x
      ring
    have hbound : ‖∫ x, (b x : ℂ) * (h x - 1) ∂μ‖ ≤ ∫ x, b x * (1 / 2 : ℝ) ∂μ := by
      refine norm_integral_le_of_norm_le hi3 (Filter.Eventually.of_forall fun x => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hbnn x)]
      by_cases hbx : b x = 0
      · rw [hbx]; simp
      · have hx : x ∈ Metric.ball (0 : E) (min δ δ') := hbs (subset_tsupport _ hbx)
        exact mul_le_mul_of_nonneg_left (hs x hx).le (hbnn x)
    have hreal : (∫ x, (b x : ℂ) ∂μ) = ((∫ x, b x ∂μ : ℝ) : ℂ) := integral_ofReal
    rw [integral_mul_const] at hbound
    intro h0
    rw [split, hreal] at h0
    have e1 : ((∫ x, b x ∂μ : ℝ) : ℂ) = -∫ x, (b x : ℂ) * (h x - 1) ∂μ := eq_neg_of_add_eq_zero_left h0
    have e2 : ‖((∫ x, b x ∂μ : ℝ) : ℂ)‖ = ‖∫ x, (b x : ℂ) * (h x - 1) ∂μ‖ := by rw [e1, norm_neg]
    rw [Complex.norm_real, Real.norm_of_nonneg hbint.le] at e2
    linarith
  refine ⟨b, hbd, hbc, aux f hf fun x hx => ?_, aux g hg fun x hx => ?_⟩
  · have := hδf (lt_of_lt_of_le hx (min_le_left _ _))
    rwa [hf0, dist_eq_norm] at this
  · have := hδg (lt_of_lt_of_le hx (min_le_right _ _))
    rwa [hg0, dist_eq_norm] at this

local instance bsS {p : ℕ} : BorelSpace ((G.UT p → ℂ) × (Fin p → ℝ)) := Prod.borelSpace
local instance bsRC {k p ρ : ℕ} : BorelSpace (U.RC k p ρ) := Prod.borelSpace

theorem piHaar {n p : ℕ} : (volume : Measure (Fin n → Fin p → ℂ)).IsAddHaarMeasure :=
  Measure.pi.isAddHaarMeasure (fun _ => volume)

theorem rcHaar {k p ρ : ℕ} : (volume : Measure (U.RC k p ρ)).IsAddHaarMeasure := by
  have := @piHaar (2 * ρ + k + 1) p
  rw [Measure.volume_eq_prod]
  exact Measure.prod.instIsAddHaarMeasure _ _

theorem bump_exists {k p ρ : ℕ} (z z' : Fin (2 * ρ + k + 1) → ℂ) (hz : inWb k ρ z) (hz' : inWb k ρ z') :
    ∃ b : U.RC k p ρ → ℝ, ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧
      (∫ x, (b x : ℂ) * psi k (p + ρ) (liftVec k p ρ z) cStd (U.Rn k p ρ x) ∂(U.muRC k p ρ)) ≠ 0 ∧
      (∫ x, (b x : ℂ) * star (psi k (p + ρ) (liftVec k p ρ z') cStd (U.Rn k p ρ x)) ∂(U.muRC k p ρ)) ≠ 0 := by
  have hc : Continuous (fun x : U.RC k p ρ => psi k (p + ρ) (liftVec k p ρ z) cStd (U.Rn k p ρ x)) :=
    (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.psi_cont _ _).comp (Formalism.FourierDecayAlt.P.Dx2.SplitF.rn_cont p ρ)
  have hc' : Continuous (fun x : U.RC k p ρ => star (psi k (p + ρ) (liftVec k p ρ z') cStd (U.Rn k p ρ x))) :=
    ((Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.psi_cont _ _).comp (Formalism.FourierDecayAlt.P.Dx2.SplitF.rn_cont p ρ)).star
  have h0 : psi k (p + ρ) (liftVec k p ρ z) cStd (U.Rn k p ρ 0) = 1 := by
    rw [Formalism.FourierDecayAlt.P.LeftFubiniLemmas.rn_zero]
    exact Formalism.FourierDecayAlt.P.Qx5.psi_one (Formalism.FourierDecayAlt.P.LeftFubiniLemmas.inWb_liftVec hz) _
  have h0' : star (psi k (p + ρ) (liftVec k p ρ z') cStd (U.Rn k p ρ 0)) = 1 := by
    rw [Formalism.FourierDecayAlt.P.LeftFubiniLemmas.rn_zero, Formalism.FourierDecayAlt.P.Qx5.psi_one (Formalism.FourierDecayAlt.P.LeftFubiniLemmas.inWb_liftVec hz') _, star_one]
  have := @rcHaar k p ρ
  unfold U.muRC
  exact bump_two volume _ _ hc hc' h0 h0'

end Formalism.FourierDecayAlt.P.CutEX.MkTopBump
end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutMKTop

section

@[expose] public section

noncomputable section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMK

theorem psi_cast {k a b : ℕ} (e : a = b) (v : Fin (2 * a + k + 1) → ℂ) (c : ℂ) (g : B.Mat k a) :
    psi k b (D.castV e v) c (D.castM e g) = psi k a v c g := by
  subst e
  rw [Formalism.FourierDecayAlt.P.Dx2.Tower.castV_rfl, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]

theorem top_construction : TopMk := by
  intro hC Wp Wq _ _ _ _ _ _ P p
  have hT := p.hT
  have hr : P.r ≤ P.r := le_rfl
  have e0 : P.r + (P.r - P.r) = P.r := by omega
  have hρ : P.r - P.r = 0 := Nat.sub_self _
  obtain ⟨b, hbs, hbc, hκL, hκR⟩ := Formalism.FourierDecayAlt.P.CutEX.MkTopBump.bump_exists (k := P.k) (p := P.r) (ρ := P.r - P.r)
    (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).z_mem (p.T.bs P.r).z'_mem
  obtain ⟨β, hβs, hβi, hβK⟩ := Formalism.FourierDecayAlt.P.CutEXMT.top_truncation_construction P.r
  refine ⟨b, b, β, kapL (p.T.bs P.r).z b * kapR (p.T.bs P.r).z' b, hbs, hbc, hbs, hbc, mul_ne_zero hκL hκR, hβs,
    ?_, ?_⟩
  · intro K hK hKU
    obtain ⟨K', hK', hK'1, hK'2⟩ := hβK (Mt P.k (P.r - P.r)) K hK (fun q hq => (hKU hq).1)
    refine ⟨K', hK', fun q hq => ?_, hK'2⟩
    obtain ⟨hd, q₀, hq₀, he⟩ := hK'1 q hq
    exact ⟨hd, he ▸ (hKU hq₀).2⟩
  · intro Φ hΦL hΦU Z y hZ hy
    have hyG : (Matrix.of y : B.Mat P.k (P.r - P.r)) ∈ B.GV P.k (P.r - P.r) :=
      (Formalism.FourierDecayAlt.P.CutEX.MkCptPf.glev_last_iff hρ _).1 hy
    have hz : p.T.base.z' = D.castV e0 (liftVec P.k P.r (P.r - P.r) (p.T.bs P.r).z') := (p.T.z'_lev P.r hr).symm
    have hpsi : ∀ u : G.UT P.r → ℂ, CutEX.psiU p (G.upper u) =
        psi P.k (P.r + (P.r - P.r)) (liftVec P.k P.r (P.r - P.r) (p.T.bs P.r).z') cStd
          (U.muP P.k P.r (P.r - P.r) (G.upper u)) := by
      intro u
      unfold CutEX.psiU
      rw [hz]
      exact psi_cast e0 _ _ _
    have key := hC P.k P.r (P.r - P.r) P.r Wp Wq e0 hρ (p.T.bs P.r) p.T.base (p.T.z'_lev P.r hr)
      (p.T.π'_lev P.r hr) (hT P.r hr).1 (hT P.r hr).2.1 (Formalism.FourierDecayAlt.P.PBM.tower_haarW' p.T hT P.r hr e0)
      (hT P.r hr).2.2 (hT 0 (Nat.zero_le _)).2.2 b b β Φ hbs.continuous hbc hbs.continuous hbc Z hZ
      (hβi Z hZ).1 (hβi Z hZ).2 y hyG (fun h1 hh1 h2 hh2 => hΦL Z y hy h1 hh1 h2 hh2)
      (fun u y' hy' => by
        rw [hΦU Z y' (G.upper u) hZ ((Formalism.FourierDecayAlt.P.CutEX.MkCptPf.glev_last_iff hρ _).2 hy')
          (Formalism.FourierDecayAlt.P.LeftFubiniLemmas.upper_isUpUni u), hpsi u])
    exact key

theorem mkTop_of_avgs (hR : RightAvg) (hL : LeftAvg) : CutEX.MkTop := mkTop_of_leaves hR hL top_construction

end Formalism.FourierDecayAlt.P.CutMK
end
end
end
