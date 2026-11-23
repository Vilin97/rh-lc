module

public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselLine
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.FSStatements
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.OpNormLeOneOfIso
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.DecayZeroRight.NormDec
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.ConvPi
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.ConvPsi
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.ConvSig
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.FSFInt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.FSFdeg
public import Formalism.HermitianCurvature.StatementB
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.SmoothStep
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.UnitNorm.UnrealifyRealify
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselLine
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.SchurDecayBounds.NormIdGen
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.SchurDecayBounds.NormIdSm
public import Formalism.SharpRestriction.CuspSpanNormBounds.KfinOfMemLowKSub
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.ConvGrp

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.SchurDecayBounds.NormIdDec

section

@[expose] public section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace PI.WBL.NIS

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine PI.WBL PI.WBL.FSW Formalism.MainNotions.InverseNormDecayBounds

variable {k r : ℕ}

theorem gN_shift {s y : Mx k r} (hs : s ∈ UH (Hpk k r)) (hy : y ∈ UH (Hpk k r)) {a : ℝ} (ha : 0 ≤ a) :
    Formalism.FourierDecayAlt.B.gN (s * y) ^ (-a) ≤ Formalism.FourierDecayAlt.B.gN y ^ a * Formalism.FourierDecayAlt.B.gN s ^ (-a) := by
  have hN := Formalism.MainNotions.InverseNormDecayBounds.normInvP k r
  have hy1 : 1 ≤ Formalism.FourierDecayAlt.B.gN y := (hN.1 y hy).2
  have hs1 : 1 ≤ Formalism.FourierDecayAlt.B.gN s := (hN.1 s hs).2
  have hyinv : Formalism.FourierDecayAlt.B.gN y⁻¹ = Formalism.FourierDecayAlt.B.gN y := (hN.1 y hy).1
  have hdet : IsUnit y.det := by
    have h1 : yᴴ * Hpk k r * y = Hpk k r := hy
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, Matrix.det_mul] at h2
    have hH : IsUnit (Hpk k r).det := Formalism.MainNotions.BesselShellMomentBounds.Hpk_det_unit k r
    have h3 : (yᴴ).det * y.det = 1 := by
      apply hH.mul_left_cancel
      calc (Hpk k r).det * ((yᴴ).det * y.det) = (yᴴ).det * (Hpk k r).det * y.det := by ring
        _ = (Hpk k r).det := h2
        _ = (Hpk k r).det * 1 := (mul_one _).symm
    exact IsUnit.of_mul_eq_one ((yᴴ).det) (by rw [mul_comm]; exact h3)
  have hsy : s = s * y * y⁻¹ := by rw [Matrix.mul_nonsing_inv_cancel_right _ _ hdet]
  have hle : Formalism.FourierDecayAlt.B.gN s ≤ Formalism.FourierDecayAlt.B.gN (s * y) * Formalism.FourierDecayAlt.B.gN y := by
    calc Formalism.FourierDecayAlt.B.gN s = Formalism.FourierDecayAlt.B.gN (s * y * y⁻¹) := by rw [← hsy]
      _ ≤ Formalism.FourierDecayAlt.B.gN (s * y) * Formalism.FourierDecayAlt.B.gN y⁻¹ := hN.2 _ _
      _ = Formalism.FourierDecayAlt.B.gN (s * y) * Formalism.FourierDecayAlt.B.gN y := by rw [hyinv]
  have hypos : 0 < Formalism.FourierDecayAlt.B.gN y := by linarith
  have hspos : 0 < Formalism.FourierDecayAlt.B.gN s := by linarith
  have hq : Formalism.FourierDecayAlt.B.gN s / Formalism.FourierDecayAlt.B.gN y ≤ Formalism.FourierDecayAlt.B.gN (s * y) := by
    rw [div_le_iff₀ hypos]; exact hle
  have hqpos : 0 < Formalism.FourierDecayAlt.B.gN s / Formalism.FourierDecayAlt.B.gN y := div_pos hspos hypos
  calc Formalism.FourierDecayAlt.B.gN (s * y) ^ (-a) ≤ (Formalism.FourierDecayAlt.B.gN s / Formalism.FourierDecayAlt.B.gN y) ^ (-a) :=
        Real.rpow_le_rpow_of_nonpos hqpos hq (by linarith)
    _ = Formalism.FourierDecayAlt.B.gN y ^ a * Formalism.FourierDecayAlt.B.gN s ^ (-a) := by
        rw [Real.div_rpow hspos.le hypos.le, Real.rpow_neg hypos.le, div_eq_mul_inv, inv_inv, mul_comm]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]

theorem measurableSet_S (z : Fin (2 * r + k + 1) → ℂ) :
    MeasurableSet {p : Mt k r × Mt k r | Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r} := by
  have h2 : IsClosed {p : Mt k r × Mt k r | Matrix.of p.1 ∈ UWset k r z} :=
    (PI.WUN.isClosed_UW z).preimage continuous_fst
  have h3 : IsClosed {p : Mt k r × Mt k r | Matrix.of p.2 ∈ Nset k r} :=
    (PI.WUN.isClosed_N k r).preimage continuous_snd
  exact (h2.inter h3).measurableSet

theorem coefS_aesm {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mx k r → (H →L[ℂ] H)}
    (hds : IsDSHpk k r ε lam σ) {z : Fin (2 * r + k + 1) → ℂ} (hGr : Cv.GrpF k r z)
    {μW μN : Measure (Mt k r)}
    (hM1 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r) (w v : H) :
    AEStronglyMeasurable (fun p : Mt k r × Mt k r => ⟪v, σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ) (μW.prod μN) := by
  have hm : Continuous (fun p : Mt k r × Mt k r => (Matrix.of p.1 : Mx k r) * Matrix.of p.2) :=
    (continuous_fst : Continuous (fun p : Mt k r × Mt k r => p.1)).matrix_mul continuous_snd
  have h := (ds_rep hds).2.2.2 w
  have hc : ContinuousOn (fun p : Mt k r × Mt k r => ⟪v, σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ)
      {p : Mt k r × Mt k r | Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r} := by
    refine continuousOn_const.inner (h.comp hm.continuousOn ?_)
    intro p hp
    exact hGr.1 _ hp.1.1 _ hp.2.1
  have hc' := hc.aestronglyMeasurable (μ := μW.prod μN) (measurableSet_S z)
  rwa [Measure.restrict_eq_self_of_ae_mem
    (s := {p : Mt k r × Mt k r | Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r}) hM1] at hc'

theorem int_beF_of_bd {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Mx k r → (H →L[ℂ] H)} (hds : IsDSHpk k r ε lam σ) {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ}
    {π : Mx k r → (Wp →L[ℂ] Wp)} (hGr : Cv.GrpF k r z) (hPi : Cv.PiU z π)
    {μW μN : Measure (Mt k r)} [SFinite μN] (hM : Cv.MeasF z π μW μN) {w v : H} {b C : ℝ} (hb : 0 ≤ b)
    (hbd : ∀ y ∈ UH (Hpk k r), ‖⟪v, σ y w⟫_ℂ‖ ≤ C * Formalism.FourierDecayAlt.B.gN y ^ (-b))
    (hS : Integrable (fun p : Mt k r × Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-(b / 2)))
      (μW.prod μN)) :
    Integrable (beF z c π σ w v) (μW.prod μN) := by
  refine Integrable.mono' (hS.const_mul |C|)
    (Cv.beF_aesm z c π μW μN σ w v hM.2.2.2 (coefS_aesm hds hGr hM.1 w v)) ?_
  filter_upwards [hM.1] with p hp
  have hs : Matrix.of p.1 * Matrix.of p.2 ∈ UH (Hpk k r) := hGr.1 _ hp.1.1 _ hp.2.1
  have g1 := ((normInvP k r).1 _ hs).2
  calc ‖beF z c π σ w v p‖ ≤ ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ‖ :=
        Cv.norm_beF_le z c π σ w v hGr hPi p hp.1
    _ ≤ C * Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-b) := hbd _ hs
    _ ≤ |C| * Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-b) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (by linarith) _)
    _ ≤ |C| * Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-(b / 2)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le g1 (by linarith)) (abs_nonneg C)

theorem bd_shift {σ : Mx k r → (H →L[ℂ] H)} (hSg : Cv.SigU σ) {w v : H} {b C : ℝ} (hb : 0 ≤ b)
    (hbd : ∀ y ∈ UH (Hpk k r), ‖⟪v, σ y w⟫_ℂ‖ ≤ C * Formalism.FourierDecayAlt.B.gN y ^ (-b))
    {x : Mx k r} (hx : x ∈ UH (Hpk k r)) :
    ∀ y ∈ UH (Hpk k r), ‖⟪v, σ y (σ x w)⟫_ℂ‖ ≤ (|C| * Formalism.FourierDecayAlt.B.gN x ^ b) * Formalism.FourierDecayAlt.B.gN y ^ (-b) := by
  intro y hy
  have hyx : y * x ∈ UH (Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hy hx
  have e : σ y (σ x w) = σ (y * x) w := by rw [hSg.2.1 _ hy _ hx]; rfl
  have g1 := ((normInvP k r).1 _ hyx).2
  rw [e]
  calc ‖⟪v, σ (y * x) w⟫_ℂ‖ ≤ C * Formalism.FourierDecayAlt.B.gN (y * x) ^ (-b) := hbd _ hyx
    _ ≤ |C| * Formalism.FourierDecayAlt.B.gN (y * x) ^ (-b) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (by linarith) _)
    _ ≤ |C| * (Formalism.FourierDecayAlt.B.gN x ^ b * Formalism.FourierDecayAlt.B.gN y ^ (-b)) :=
        mul_le_mul_of_nonneg_left (gN_shift hy hx hb) (abs_nonneg C)
    _ = _ := by ring

theorem dInt_of_bd {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Mx k r → (H →L[ℂ] H)} (hds : IsDSHpk k r ε lam σ) {z : Fin (2 * r + k + 1) → ℂ}
    (hGr : Cv.GrpF k r z) {μW μN μG : Measure (Mt k r)} [SFinite μW] [SFinite μN] [SFinite μG]
    (hHaar : IsHaarOn (UH (Hpk k r)) μG)
    (hM1 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r)
    {u v : H} {b C : ℝ} (hb : 0 ≤ b)
    (hbd : ∀ y ∈ UH (Hpk k r), ‖⟪v, σ y u⟫_ℂ‖ ≤ C * Formalism.FourierDecayAlt.B.gN y ^ (-b))
    (hGg : Integrable (fun x : Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (-(b / 2))) μG)
    (hS : Integrable (fun p : Mt k r × Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-(b / 2)))
      (μW.prod μN)) :
    Integrable (fun q : Mt k r × (Mt k r × Mt k r) =>
      ‖⟪v, σ (Matrix.of q.1) u⟫_ℂ‖ * ‖⟪v, σ (sM q.2 * Matrix.of q.1) u⟫_ℂ‖) (μG.prod (μW.prod μN)) := by
  have hprod : Integrable (fun q : Mt k r × (Mt k r × Mt k r) =>
      Formalism.FourierDecayAlt.B.gN (Matrix.of q.1) ^ (-(b / 2)) * Formalism.FourierDecayAlt.B.gN (Matrix.of q.2.1 * Matrix.of q.2.2) ^ (-(b / 2)))
      (μG.prod (μW.prod μN)) := by
    exact hGg.mul_prod hS
  refine Integrable.mono' (hprod.const_mul (|C| * |C|)) ?_ ?_
  · exact ((coef_aesm hds hHaar u v).comp_fst.norm).mul (matrix_coefficient_ae_strongly_measurable hds hGr hHaar hM1 u v).norm
  · filter_upwards [joint_ae hHaar hM1] with q hq
    have hy : Matrix.of q.1 ∈ UH (Hpk k r) := hq.1
    have hs : sM q.2 ∈ UH (Hpk k r) := hGr.1 _ hq.2.1.1 _ hq.2.2.1
    have hsy : sM q.2 * Matrix.of q.1 ∈ UH (Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hs hy
    have gy := ((normInvP k r).1 _ hy).2
    have gsy := ((normInvP k r).1 _ hsy).2
    have hb2 : 0 ≤ b / 2 := by linarith
    have a1 : ‖⟪v, σ (Matrix.of q.1) u⟫_ℂ‖ ≤ |C| * Formalism.FourierDecayAlt.B.gN (Matrix.of q.1) ^ (-b) :=
      (hbd _ hy).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (by linarith) _))
    have a2 : ‖⟪v, σ (sM q.2 * Matrix.of q.1) u⟫_ℂ‖ ≤
        |C| * (Formalism.FourierDecayAlt.B.gN (Matrix.of q.1) ^ (b / 2) * Formalism.FourierDecayAlt.B.gN (sM q.2) ^ (-(b / 2))) := by
      calc ‖⟪v, σ (sM q.2 * Matrix.of q.1) u⟫_ℂ‖ ≤ C * Formalism.FourierDecayAlt.B.gN (sM q.2 * Matrix.of q.1) ^ (-b) :=
            hbd _ hsy
        _ ≤ |C| * Formalism.FourierDecayAlt.B.gN (sM q.2 * Matrix.of q.1) ^ (-b) :=
            mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (by linarith) _)
        _ ≤ |C| * Formalism.FourierDecayAlt.B.gN (sM q.2 * Matrix.of q.1) ^ (-(b / 2)) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le gsy (by linarith)) (abs_nonneg C)
        _ ≤ _ := mul_le_mul_of_nonneg_left (gN_shift hs hy hb2) (abs_nonneg C)
    have ey : Formalism.FourierDecayAlt.B.gN (Matrix.of q.1) ^ (-b) * Formalism.FourierDecayAlt.B.gN (Matrix.of q.1) ^ (b / 2) =
        Formalism.FourierDecayAlt.B.gN (Matrix.of q.1) ^ (-(b / 2)) := by
      rw [← Real.rpow_add (by linarith)]
      congr 1
      ring
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ‖⟪v, σ (Matrix.of q.1) u⟫_ℂ‖ * ‖⟪v, σ (sM q.2 * Matrix.of q.1) u⟫_ℂ‖
        ≤ (|C| * Formalism.FourierDecayAlt.B.gN (Matrix.of q.1) ^ (-b)) *
            (|C| * (Formalism.FourierDecayAlt.B.gN (Matrix.of q.1) ^ (b / 2) * Formalism.FourierDecayAlt.B.gN (sM q.2) ^ (-(b / 2)))) :=
          mul_le_mul a1 a2 (norm_nonneg _) (by positivity)
      _ = (|C| * |C|) * ((Formalism.FourierDecayAlt.B.gN (Matrix.of q.1) ^ (-b) * Formalism.FourierDecayAlt.B.gN (Matrix.of q.1) ^ (b / 2)) *
            Formalism.FourierDecayAlt.B.gN (sM q.2) ^ (-(b / 2))) := by ring
      _ = _ := by rw [ey]; rfl

end PI.WBL.NIS
end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.SchurDecayBounds.NormIdFix

section

@[expose] public section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace PI.WBL.NIS

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine PI.WBL PI.WBL.FSW Formalism.MainNotions.InverseNormDecayBounds Formalism.MainNotions.BridgeLemma₄

def MeasSideP : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ) (Wp : Type) [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN : Measure (Mt k r)),
    inWb k r z → 0 < Tz k r z → PI.UpqRep.IsHCTypeW k r z u π →
    PI.BesselPeriodGGP.IsHaarOn (UWset k r z) μW → PI.BesselPeriodGGP.IsHaarOn (Nset k r) μN →
    Cv.MeasF z π μW μN

theorem thresholds {k r : ℕ} {a : ℝ}
    (ha : 2 * Formalism.FourierDecayAlt.ThreeDimData.Mexp r * (Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r) + Formalism.FourierDecayAlt.ThreeDimData.AG k r + 3 ≤ a) :
    1 ≤ a ∧ Formalism.FourierDecayAlt.ThreeDimData.AG k r < (a - 1) / 2 ∧ Formalism.FourierDecayAlt.ThreeDimData.AS k r < (a - 1) / 2 := by
  have hAG : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AG k r := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.AG
    positivity
  have hdN : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.dN k r := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.dN
    nlinarith [sq_nonneg (r : ℝ), (Nat.cast_nonneg r : (0 : ℝ) ≤ r), (Nat.cast_nonneg k : (0 : ℝ) ≤ k),
      mul_nonneg (Nat.cast_nonneg r : (0 : ℝ) ≤ r) (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hAS : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AS k r := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.AS
    exact mul_nonneg (Nat.cast_nonneg _) hdN
  have hM : 2 ≤ Formalism.FourierDecayAlt.ThreeDimData.Mexp r := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.Mexp
    nlinarith [sq_nonneg (r : ℝ), (Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
  have hMS : 2 * (Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r) ≤
      Formalism.FourierDecayAlt.ThreeDimData.Mexp r * (Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r) :=
    mul_le_mul_of_nonneg_right hM (by linarith)
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]

def DecInfU (σ : Mx k r → (H →L[ℂ] H)) (a : ℝ) : Prop :=
  ∀ v0 : H, IsKFinHpk (k := k) (r := r) σ v0 → ∃ (C : ℝ) (Ws : List (List (Mx k r))),
    (∀ W ∈ Ws, ∀ X ∈ W, PI.UpqRep.InLieHpk k r X) ∧
    ∀ w ∈ smoothVecs (k := k) (r := r) σ, ∀ x ∈ UH (Hpk k r),
      ‖⟪v0, σ x w⟫_ℂ‖ ≤ C * (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) σ W w‖).sum *
        Formalism.FourierDecayAlt.B.gN x ^ (1 - a)

theorem decBd_of_decInfU {σ : Mx k r → (H →L[ℂ] H)} {a : ℝ} (hI : DecInfU σ a) {v0 w : H}
    (hv0 : IsKFinHpk (k := k) (r := r) σ v0) (hw : w ∈ smoothVecs (k := k) (r := r) σ) :
    DecBd σ (a - 1) v0 w := by
  obtain ⟨C, Ws, -, hC⟩ := hI v0 hv0
  refine ⟨C * (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) σ W w‖).sum, fun x hx => ?_⟩
  have h1 := hC w hw x hx
  rwa [show (1 - a) = -(a - 1) by ring] at h1

theorem normId_gen_bd {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {μW μN μG ν : Measure (Mt k r)} [SFinite μW] [SFinite μN] {σ : Mx k r → (H →L[ℂ] H)}
    {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} (hds : IsDSHpk k r ε lam σ)
    (hHaar : IsHaarOn (UH (Hpk k r)) μG) (hq : IsQuotMeas μG (muSof μW μN) ν)
    (hGr : Cv.GrpF k r z) (hSg : Cv.SigU σ) (hPi : Cv.PiU z π) (hPs : Cv.PsiF k r z c) (hM : Cv.MeasF z π μW μN)
    (hS : SchurOn μG σ) {u v : H} (hu : u ≠ 0) {b : ℝ} (hb : 0 ≤ b)
    (huv : DecBd σ b v u) (hvv : DecBd σ b v v)
    (hGg : Integrable (fun x : Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (-(b / 2))) μG)
    (hSS : Integrable (fun p : Mt k r × Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-(b / 2)))
      (μW.prod μN))
    (ξ : Wp) :
    Integrable (fun x : Mt k r => ‖be z c π μW μN σ (σ (Matrix.of x) u) v ξ‖ ^ 2) ν ∧
    ∫ x, ‖be z c π μW μN σ (σ (Matrix.of x) u) v ξ‖ ^ 2 ∂ν =
      ‖u‖ ^ 2 * (⟪be z c π μW μN σ v v ξ, ξ⟫_ℂ).re / fdegH μG σ u ∧
    (⟪ξ, be z c π μW μN σ v v ξ⟫_ℂ).im = 0 := by
  have : SFinite μG := sfinite_haar hHaar
  obtain ⟨C, hC⟩ := huv
  obtain ⟨C', hC'⟩ := hvv
  have hI : ∀ x ∈ UH (Hpk k r), Integrable (beF z c π σ (σ x u) v) (μW.prod μN) :=
    fun x hx => int_beF_of_bd hds hGr hPi hM hb (bd_shift hSg hb hC hx) hSS
  have hIv : Integrable (beF z c π σ v v) (μW.prod μN) := int_beF_of_bd hds hGr hPi hM hb hC' hSS
  have hD := dInt_of_bd hds hGr hHaar hM.1 hb hC hGg hSS
  exact normId_gen hds hHaar hq hGr hSg hPi hPs hM hS hu hI hIv hD ξ

theorem re_inner_swap (B : Wp →L[ℂ] Wp) (ξ : Wp) : (⟪B ξ, ξ⟫_ℂ).re = (⟪ξ, B ξ⟫_ℂ).re := by
  rw [← inner_conj_symm, Complex.conj_re]

theorem normIdSm_of (hGS : Formalism.FourierDecayAlt.ThreeDimData.GrowthS) (hGG : Formalism.FourierDecayAlt.ThreeDimData.GrowthG) (hMS : MeasSideP) :
    Formalism.FourierDecayAlt.ThreeDimData.NormIdSm := by
  intro hIn hSch k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hSide x hx v hv ξ
  obtain ⟨hDL, hDI, hKS, -⟩ := hIn
  obtain ⟨hlam, hds, hgap, hOK, hw0, hz, hT, hc, hπ, hμW, hμN, hμG, hq⟩ := hSide
  have : SigmaFinite μW := hμW.1
  have : SigmaFinite μN := hμN.1
  have hds' : IsDSHpk k r ε lam σ := hds
  have hHaar : IsHaarOn (UH (Hpk k r)) μG := hμG
  have hq' : IsQuotMeas μG (muSof μW μN) νq := hq
  have hGr := Cv.grpAll k r z
  have hSg := Cv.sigAll k r ε lam H σ hds'
  have hPi := Cv.piAll k r z u Wp π hz hT hπ
  have hPs := Cv.psiAll k r z c hz
  have hM := hMS k r z u Wp π μW μN hz hT hπ hμW hμN
  obtain ⟨d, hd, hSd⟩ := hSch k r ε lam H σ μG hlam hds hμG
  have hS : SchurOn μG σ := ⟨d, hd, hSd⟩
  set a := Formalism.FourierDecayAlt.ThreeDimData.aOf r h with ha_def
  obtain ⟨ha1, hAG, hAS⟩ := thresholds hOK.2.2.1
  have hb : 0 ≤ a - 1 := by linarith
  have hGg : Integrable (fun x : Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (-((a - 1) / 2))) μG :=
    hGG k r μG _ hμG hAG
  have hSS : Integrable (fun p : Mt k r × Mt k r =>
      Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-((a - 1) / 2))) (μW.prod μN) :=
    hGS k r z μW μN μG νq _ hz hT hμW hμN hμG hq hAG
  obtain ⟨P, hP, hn1, hmem⟩ := hw0
  have hw0' : IsLowUnitH k r ε lam σ w0 := ⟨P, hP, hn1, hmem⟩
  have hw0ne : w0 ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hn1
    exact zero_ne_one hn1
  have hK0 : IsKFinHpk (k := k) (r := r) σ w0 := Formalism.MainNotions.DoubleDerivativeSmoothness.kfinHpk_of_lowUnitH hw0'
  have hsm0 : w0 ∈ smoothVecs (k := k) (r := r) σ := hKS k r ε lam H σ hlam hds w0 hK0
  have hD : DiagonalMatrixCoefficientPowerDecay σ w0 a := hDL k r hOK.1 ε lam h H σ hlam hds hgap hOK.2.1 P hP w0 w0 hmem hmem
  have hI : DecInfU σ a := hDI k r ε lam h H σ hlam hds hgap hOK

  have hB : (∀ y ∈ smoothVecs (k := k) (r := r) σ, DecBd σ (a - 1) v y) ∧ DecBd σ (a - 1) v v := by
    rcases hv with hvD | hvK
    · exact ⟨fun y hy => decBd_DD_left hds' hSg hb (decBd_of_decInfU hI hK0 hy) v hvD,
        decBd_mono (by linarith) (decDD hds' (by linarith) hD v hvD v hvD)⟩
    · have hvs : v ∈ smoothVecs (k := k) (r := r) σ := hKS k r ε lam H σ hlam hds v hvK
      exact ⟨fun y hy => decBd_of_decInfU hI hvK hy, decBd_of_decInfU hI hvK hvs⟩
  have hfd : ∀ y : H, y ≠ 0 → fdegH μG σ y = d := fun y hy => fdegH_eq ⟨hd, hSd⟩ hy

  obtain ⟨-, heq0, him⟩ := normId_gen_bd hds' hHaar hq' hGr hSg hPi hPs hM hS hw0ne hb (hB.1 w0 hsm0) hB.2
    hGg hSS ξ
  have hre : 0 ≤ (⟪ξ, PI.WBL.be z c π μW μN σ v v ξ⟫_ℂ).re := by
    have h0 : 0 ≤ ∫ y, ‖PI.WBL.be z c π μW μN σ (σ (Matrix.of y) w0) v ξ‖ ^ 2 ∂νq :=
      integral_nonneg fun _ => by positivity
    rw [heq0, hfd w0 hw0ne, hn1, re_inner_swap] at h0
    have : 0 ≤ (⟪ξ, PI.WBL.be z c π μW μN σ v v ξ⟫_ℂ).re / d := by simpa using h0
    exact (div_nonneg_iff.mp this).elim (fun h => h.1) (fun h => absurd h.2 (not_le.mpr hd))
  refine ⟨?_, him, hre⟩
  have hfd0 : PI.BesselPeriodGGP.fdegH μG σ w0 = d := hfd w0 hw0ne
  rw [hfd0]
  by_cases hx0 : x = 0
  · subst hx0
    have e0 : Formalism.FourierDecayAlt.ThreeDimData.be z c π σ μW μN 0 v = 0 := by
      simp [Formalism.FourierDecayAlt.ThreeDimData.be, Formalism.FourierDecayAlt.ThreeDimData.beInt]
    unfold PI.BesselPeriodGGP.l2SG
    simp [e0]
  · obtain ⟨hint, heq, -⟩ := normId_gen_bd hds' hHaar hq' hGr hSg hPi hPs hM hS hx0 hb (hB.1 x hx) hB.2
      hGg hSS ξ
    rw [hfd x hx0, re_inner_swap] at heq
    unfold PI.BesselPeriodGGP.l2SG
    show ∫⁻ y, (‖PI.WBL.be z c π μW μN σ (σ (Matrix.of y) x) v ξ‖₊ : ℝ≥0∞) ^ 2 ∂νq =
      ENNReal.ofReal (‖x‖ ^ 2 * (⟪ξ, PI.WBL.be z c π μW μN σ v v ξ⟫_ℂ).re / d)
    rw [← heq, ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => by positivity)]
    apply lintegral_congr
    intro y
    simp only [ENNReal.ofReal_pow, norm_nonneg, ofReal_norm, enorm_eq_nnnorm]

end PI.WBL.NIS
end
end
end
