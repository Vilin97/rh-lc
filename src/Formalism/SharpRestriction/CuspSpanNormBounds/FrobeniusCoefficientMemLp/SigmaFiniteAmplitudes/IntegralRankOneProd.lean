module

public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.MeasurableMulInvInv
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.OpNormLeOneOfIso
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.BesselUnipotentEquivHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.ConvGrp
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.ConvSig
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrablePhiF
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Tactic.TypeStar

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegralAdjoint

section

@[expose] public section

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace Formalism.FourierDecayAlt.P.S3dx6

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def aInt {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (σ : Mx k r → (H →L[ℂ] H))
    (w0 a : H) (t : Mx k r) (p : Mt k r × Mt k r) : Wp →L[ℂ] Wp :=
  (psi k r z c (Matrix.of p.2) * ⟪a, σ ((Matrix.of p.1)⁻¹ * (Matrix.of p.2)⁻¹ * t) w0⟫_ℂ) • π (Matrix.of p.1)

theorem aInt_eq {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    {σ : Mx k r → (H →L[ℂ] H)} (hU : PI.WBL.Cv.SigU σ) (w0 a : H) {t : Mx k r} (ht : t ∈ UH (Hpk k r))
    {p : Mt k r × Mt k r} (hp1 : Matrix.of p.1 ∈ UWset k r z) (hp2 : Matrix.of p.2 ∈ Nset k r) :
    beInt z c π σ (σ t w0) a (Prod.map B7.invM B7.invM p) = aInt z c π σ w0 a t p := by
  obtain ⟨p1, p2⟩ := p
  simp only at hp1 hp2
  have hh : Matrix.of p1 ∈ UH (Hpk k r) := hp1.1
  have hn : Matrix.of p2 ∈ UH (Hpk k r) := hp2.1
  have hinv : ((Matrix.of p1)⁻¹)⁻¹ = Matrix.of p1 :=
    Matrix.inv_eq_left_inv (PI.WBL.Cv.uh_inv hh).1
  have hmul : σ ((Matrix.of p1)⁻¹ * (Matrix.of p2)⁻¹ * t) =
      (σ ((Matrix.of p1)⁻¹ * (Matrix.of p2)⁻¹)).comp (σ t) :=
    hU.2.1 _ (PI.WBL.Cv.uh_mul (PI.WBL.Cv.uh_inv hh).2.2 (PI.WBL.Cv.uh_inv hn).2.2) t ht
  have hpsi := Formalism.QuantumDeterminants.BesselUnipotentEquiv.star_psi_inv z c hz (Matrix.of p2) hp2
  show (⟪a, σ ((Matrix.of p1)⁻¹ * (Matrix.of p2)⁻¹) (σ t w0)⟫_ℂ *
      star (psi k r z c (Matrix.of p2)⁻¹)) • π ((Matrix.of p1)⁻¹)⁻¹ =
    (psi k r z c (Matrix.of p2) * ⟪a, σ ((Matrix.of p1)⁻¹ * (Matrix.of p2)⁻¹ * t) w0⟫_ℂ) •
      π (Matrix.of p1)
  rw [hinv, hpsi, hmul, ContinuousLinearMap.comp_apply, mul_comm]

end Formalism.FourierDecayAlt.P.S3dx6
end
end
end

-- Source module: Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.NormPiLeOne

section

set_option backward.isDefEq.respectTransparency false

@[expose] public section

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.MainNotions.S.Pv.AmpDDPf

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

attribute [local instance] Formalism.FourierDecayAlt.P.B7.properFD

section OneSide

variable {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

theorem op_eq_sum (T : Wp →L[ℂ] Wp) :
    T = ∑ i, (innerSL ℂ ((stdOrthonormalBasis ℂ Wp) i)).smulRight (T ((stdOrthonormalBasis ℂ Wp) i)) := by
  ext x
  rw [_root_.sum_apply]
  simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  conv_lhs => rw [← (stdOrthonormalBasis ℂ Wp).sum_repr' x]

  rw [map_sum]
  simp only [map_smul]

def piOp (z : Fin (2 * r + k + 1) → ℂ)
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (h : Mt k r) : Wp →L[ℂ] Wp :=
  ∑ i, (innerSL ℂ ((stdOrthonormalBasis ℂ Wp) i)).smulRight (piV z π ((stdOrthonormalBasis ℂ Wp) i) h)

theorem sm_piOp {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ}
    {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)}
    (hT : 0 < Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π) : StronglyMeasurable (piOp (k := k) (r := r) z π) := by
  have hs := Finset.stronglyMeasurable_sum (Finset.univ : Finset (Fin (Module.finrank ℂ Wp)))
    (f := fun i (h : Mt k r) => (innerSL ℂ ((stdOrthonormalBasis ℂ Wp) i)).smulRight
      (piV z π ((stdOrthonormalBasis ℂ Wp) i) h))
    (fun i _ => (StrongDual.smulRightL ℂ Wp Wp
      (innerSL ℂ ((stdOrthonormalBasis ℂ Wp) i))).continuous.comp_stronglyMeasurable (sm_piV hT hπ _))
  convert hs using 1
  funext h
  unfold piOp
  rw [Finset.sum_apply]

theorem piOp_eq (z : Fin (2 * r + k + 1) → ℂ)
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) {h : Mt k r}
    (hh : Matrix.of h ∈ UWset k r z) : piOp z π h = π (Matrix.of h) := by
  rw [op_eq_sum (π (Matrix.of h))]
  unfold piOp
  congr 1
  funext i
  rw [show piV z π ((stdOrthonormalBasis ℂ Wp) i) h = π (Matrix.of h) ((stdOrthonormalBasis ℂ Wp) i) from
    Set.indicator_of_mem (s := {h : Mt k r | Matrix.of h ∈ UWset k r z}) hh _]

end OneSide

section Be

variable {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

theorem aVec_eq (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ)
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp))
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (w0 v : H) (ξ : Wp)
    (t : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (p1 : Mt k r × Mt k r) :
    aVec z c π σ w0 v ξ t p1 = Formalism.FourierDecayAlt.P.S3dx6.aInt z c π σ w0 v t p1 ξ := rfl

theorem norm_pi_le_one {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ}
    {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)}
    (hT : 0 < Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π) {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) : ‖π h‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_unitary hT hπ h hh, one_mul]

theorem aesm_beInt {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ}
    {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)}
    (hT : 0 < Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π) (c : ℂ) (w0 v : H)
    {t : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ht : t ∈ UH (Hpk k r))
    {μW μN : Measure (Mt k r)} [SFinite μW] [SFinite μN]
    (h1 : ∀ᵐ x ∂μW, Matrix.of x ∈ UWset k r z) (h2 : ∀ᵐ x ∂μN, Matrix.of x ∈ Nset k r) :
    AEStronglyMeasurable (Formalism.FourierDecayAlt.ThreeDimData.beInt z c π σ (σ t w0) v) (μW.prod μN) := by
  have hU : PI.WBL.Cv.SigU σ := PI.WBL.Cv.sigAll k r ε lam H σ hσ
  let F : Mt k r × Mt k r → (Wp →L[ℂ] Wp) := fun p =>
    (cM σ v w0 (Formalism.FourierDecayAlt.P.B7.mulM (Formalism.FourierDecayAlt.P.B7.mulM p.1 p.2) (t : Mt k r)) * star (psi k r z c (Matrix.of p.2))) •
      piOp z π (Formalism.FourierDecayAlt.P.B7.invM p.1)
  have hF : StronglyMeasurable F := by
    have hc : Measurable fun p : Mt k r × Mt k r =>
        cM σ v w0 (Formalism.FourierDecayAlt.P.B7.mulM (Formalism.FourierDecayAlt.P.B7.mulM p.1 p.2) (t : Mt k r)) :=
      (meas_cM hσ v w0).comp (Formalism.FourierDecayAlt.P.B7.meas_mulM (Formalism.FourierDecayAlt.P.B7.meas_mulM measurable_fst measurable_snd)
        measurable_const)
    have hps : Measurable fun p : Mt k r × Mt k r => star (psi k r z c (Matrix.of p.2)) :=
      (continuous_star.comp (Formalism.FourierDecayAlt.P.S3dx6.continuous_psi z c)).measurable.comp measurable_snd
    exact (hc.mul hps).stronglyMeasurable.smul
      ((sm_piOp hT hπ).comp_measurable (Formalism.FourierDecayAlt.P.B7.measurable_invM.comp measurable_fst))
  refine hF.aestronglyMeasurable.congr ?_
  have h1' : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z := Measure.quasiMeasurePreserving_fst.ae h1
  have h2' : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.2 ∈ Nset k r := Measure.quasiMeasurePreserving_snd.ae h2
  filter_upwards [h1', h2'] with p hp1 hp2
  have hhn : Matrix.of p.1 * Matrix.of p.2 ∈ UH (Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hp1.1 hp2.1
  have hm : Matrix.of p.1 * Matrix.of p.2 * t ∈ UH (Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hhn ht
  have e1 : cM σ v w0 (Formalism.FourierDecayAlt.P.B7.mulM (Formalism.FourierDecayAlt.P.B7.mulM p.1 p.2) (t : Mt k r)) =
      ⟪v, σ (Matrix.of p.1 * Matrix.of p.2) (σ t w0)⟫_ℂ := by
    rw [show cM σ v w0 (Formalism.FourierDecayAlt.P.B7.mulM (Formalism.FourierDecayAlt.P.B7.mulM p.1 p.2) (t : Mt k r)) =
      ⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * t) w0⟫_ℂ from
      Set.indicator_of_mem (s := {g : Mt k r | Matrix.of g ∈ UH (Hpk k r)}) hm _]
    rw [hU.2.1 _ hhn _ ht]
    rfl
  have e2 : piOp z π (Formalism.FourierDecayAlt.P.B7.invM p.1) = π (Matrix.of p.1)⁻¹ :=
    piOp_eq z π (h := Formalism.FourierDecayAlt.P.B7.invM p.1) (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uw_inv hp1).1
  show F p = _
  simp only [F, e1, e2]
  rfl

variable [CompleteSpace Wp]

theorem int_beInt_of {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ}
    {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)}
    (hz : inWb k r z) (hT : 0 < Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π) (c : ℂ) (w0 v : H) (ξ : Wp)
    (hξ : ξ ≠ 0) {t : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ht : t ∈ UH (Hpk k r))
    {μW μN : Measure (Mt k r)} [SFinite μW] [SFinite μN]
    (hιW : MeasurePreserving (Formalism.FourierDecayAlt.P.B7.invM (k := k) (r := r)) μW μW)
    (hιN : MeasurePreserving (Formalism.FourierDecayAlt.P.B7.invM (k := k) (r := r)) μN μN)
    (h1 : ∀ᵐ x ∂μW, Matrix.of x ∈ UWset k r z) (h2 : ∀ᵐ x ∂μN, Matrix.of x ∈ Nset k r)
    (ha : Integrable (aVec z c π σ w0 v ξ t) (μW.prod μN)) :
    Integrable (Formalism.FourierDecayAlt.ThreeDimData.beInt z c π σ (σ t w0) v) (μW.prod μN) := by
  have hU : PI.WBL.Cv.SigU σ := PI.WBL.Cv.sigAll k r ε lam H σ hσ
  have hι : MeasurePreserving (Prod.map (Formalism.FourierDecayAlt.P.B7.invM (k := k) (r := r)) Formalism.FourierDecayAlt.P.B7.invM)
      (μW.prod μN) (μW.prod μN) := hιW.prod hιN
  have hae := aesm_beInt hσ hT hπ c w0 v ht h1 h2
  have h1' : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z := Measure.quasiMeasurePreserving_fst.ae h1
  have h2' : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.2 ∈ Nset k r := Measure.quasiMeasurePreserving_snd.ae h2
  have hξn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  have hcomp : Integrable (Formalism.FourierDecayAlt.ThreeDimData.beInt z c π σ (σ t w0) v ∘ Prod.map Formalism.FourierDecayAlt.P.B7.invM Formalism.FourierDecayAlt.P.B7.invM)
      (μW.prod μN) := by
    refine (ha.norm.div_const ‖ξ‖).mono' (hae.comp_measurePreserving hι) ?_
    filter_upwards [h1', h2'] with p hp1 hp2
    rw [Function.comp_apply, Formalism.FourierDecayAlt.P.S3dx6.aInt_eq hz c π hU w0 v ht hp1 hp2, aVec_eq]
    unfold Formalism.FourierDecayAlt.P.S3dx6.aInt
    rw [norm_smul, _root_.smul_apply, norm_smul,
      Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_unitary hT hπ _ hp1, le_div_iff₀ hξn]
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (norm_nonneg _) (norm_pi_le_one hT hπ hp1))
      (norm_nonneg ξ)
  exact (hι.integrable_comp hae).mp hcomp

theorem int_a_eq {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ}
    {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)}
    (hz : inWb k r z) (hT : 0 < Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π) (c : ℂ) (w0 v : H) (ξ : Wp)
    {t : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ht : t ∈ UH (Hpk k r))
    {μW μN : Measure (Mt k r)} [SFinite μW] [SFinite μN]
    (hιW : MeasurePreserving (Formalism.FourierDecayAlt.P.B7.invM (k := k) (r := r)) μW μW)
    (hιN : MeasurePreserving (Formalism.FourierDecayAlt.P.B7.invM (k := k) (r := r)) μN μN)
    (h1 : ∀ᵐ x ∂μW, Matrix.of x ∈ UWset k r z) (h2 : ∀ᵐ x ∂μN, Matrix.of x ∈ Nset k r)
    (l : H → Wp)
    (hbe : Formalism.FourierDecayAlt.ThreeDimData.be z c π σ μW μN (σ t w0) v = (innerSL ℂ (l v)).smulRight (l (σ t w0)))
    (hA : Integrable (aVec z c π σ w0 v ξ t) (μW.prod μN) ∨ ∀ᵐ p ∂(μW.prod μN), aVec z c π σ w0 v ξ t p = 0) :
    ∫ p, aVec z c π σ w0 v ξ t p ∂(μW.prod μN) = ⟪l v, ξ⟫_ℂ • l (σ t w0) := by
  have hU : PI.WBL.Cv.SigU σ := PI.WBL.Cv.sigAll k r ε lam H σ hσ
  have hι : MeasurePreserving (Prod.map (Formalism.FourierDecayAlt.P.B7.invM (k := k) (r := r)) Formalism.FourierDecayAlt.P.B7.invM)
      (μW.prod μN) (μW.prod μN) := hιW.prod hιN
  have h1' : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z := Measure.quasiMeasurePreserving_fst.ae h1
  have h2' : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.2 ∈ Nset k r := Measure.quasiMeasurePreserving_snd.ae h2
  have hval : (Formalism.FourierDecayAlt.ThreeDimData.be z c π σ μW μN (σ t w0) v) ξ = ⟪l v, ξ⟫_ℂ • l (σ t w0) := by
    rw [hbe, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  by_cases hI : Integrable (Formalism.FourierDecayAlt.ThreeDimData.beInt z c π σ (σ t w0) v) (μW.prod μN)
  · have e1 : (Formalism.FourierDecayAlt.ThreeDimData.be z c π σ μW μN (σ t w0) v) ξ =
        ∫ p, Formalism.FourierDecayAlt.ThreeDimData.beInt z c π σ (σ t w0) v p ξ ∂(μW.prod μN) :=
      ContinuousLinearMap.integral_apply hI ξ
    have hg : AEStronglyMeasurable (fun p => Formalism.FourierDecayAlt.ThreeDimData.beInt z c π σ (σ t w0) v p ξ)
        (Measure.map (Prod.map Formalism.FourierDecayAlt.P.B7.invM Formalism.FourierDecayAlt.P.B7.invM) (μW.prod μN)) := by
      rw [hι.map_eq]; exact hI.aestronglyMeasurable.apply_continuousLinearMap ξ
    have e2 : ∫ p, Formalism.FourierDecayAlt.ThreeDimData.beInt z c π σ (σ t w0) v p ξ ∂(μW.prod μN) =
        ∫ p, Formalism.FourierDecayAlt.ThreeDimData.beInt z c π σ (σ t w0) v (Prod.map Formalism.FourierDecayAlt.P.B7.invM Formalism.FourierDecayAlt.P.B7.invM p) ξ
          ∂(μW.prod μN) := by
      rw [← integral_map hι.measurable.aemeasurable hg, hι.map_eq]
    have e3 : ∫ p, Formalism.FourierDecayAlt.ThreeDimData.beInt z c π σ (σ t w0) v (Prod.map Formalism.FourierDecayAlt.P.B7.invM Formalism.FourierDecayAlt.P.B7.invM p) ξ
          ∂(μW.prod μN) = ∫ p, aVec z c π σ w0 v ξ t p ∂(μW.prod μN) := by
      refine integral_congr_ae ?_
      filter_upwards [h1', h2'] with p hp1 hp2
      rw [Formalism.FourierDecayAlt.P.S3dx6.aInt_eq hz c π hU w0 v ht hp1 hp2, aVec_eq]
    rw [← e3, ← e2, ← e1, hval]
  · have hbe0 : Formalism.FourierDecayAlt.ThreeDimData.be z c π σ μW μN (σ t w0) v = 0 := integral_undef hI
    rw [hbe0, _root_.zero_apply] at hval
    rw [← hval]
    rcases hA with hA | hA
    · by_cases hξ : ξ = 0
      · subst hξ
        simp [aVec]
      · exact absurd (int_beInt_of hσ hz hT hπ c w0 v ξ hξ ht hιW hιN h1 h2 hA) hI
    · exact integral_eq_zero_of_ae hA

end Be

end Formalism.MainNotions.S.Pv.AmpDDPf
end
end
end

-- Source module: Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.IntegralRankOneProd

section

@[expose] public section

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.MainNotions.S.Pv.AmpDDPf

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

attribute [local instance] Formalism.FourierDecayAlt.P.B7.properFD

section Gen

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
  {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem enorm_rankOne (w : E) (u : F) : ‖(innerSL ℂ w).smulRight u‖ₑ = ‖w‖ₑ * ‖u‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _),
    ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]

theorem rankOne_smul (w : E) (u : F) (c d : ℂ) :
    (innerSL ℂ (d • w)).smulRight (c • u) = (c * star d) • (innerSL ℂ w).smulRight u := by
  ext η
  simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    _root_.smul_apply, inner_smul_left, smul_smul, starRingEnd_apply]
  congr 1
  ring

theorem integral_inner_left {f : α → E} (hf : Integrable f μ) (η : E) :
    ∫ x, ⟪f x, η⟫_ℂ ∂μ = ⟪∫ x, f x ∂μ, η⟫_ℂ := by
  have h1 : (fun x => ⟪f x, η⟫_ℂ) = fun x => (starRingEnd ℂ) ⟪η, f x⟫_ℂ := by
    funext x; rw [inner_conj_symm]
  rw [h1, integral_conj, integral_inner hf, inner_conj_symm]

theorem integral_rankOne_prod [SFinite μ] [SFinite ν] {a : α → F} {b : β → E} (ha : Integrable a μ)
    (hb : Integrable b ν) (hI : Integrable (fun q : α × β => (innerSL ℂ (b q.2)).smulRight (a q.1)) (μ.prod ν)) :
    ∫ q, (innerSL ℂ (b q.2)).smulRight (a q.1) ∂(μ.prod ν) = (innerSL ℂ (∫ y, b y ∂ν)).smulRight (∫ x, a x ∂μ) := by
  ext η
  rw [ContinuousLinearMap.integral_apply hI η]
  simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  have hI' : Integrable (fun q : α × β => ⟪b q.2, η⟫_ℂ • a q.1) (μ.prod ν) := by
    simpa only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply] using hI.apply_continuousLinearMap η
  rw [integral_prod (fun q : α × β => ⟪b q.2, η⟫_ℂ • a q.1) hI']
  simp only
  simp_rw [integral_smul_const]
  rw [integral_inner_left hb, integral_smul]

end Gen

section Pt

variable {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp]

theorem aM_eq (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ)
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp))
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (w0 v : H) (ξ : Wp)
    {t : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ht : t ∈ UH (Hpk k r)) {p1 : Mt k r × Mt k r}
    (hp1 : Matrix.of p1.1 ∈ UWset k r z) (hp2 : Matrix.of p1.2 ∈ Nset k r) :
    aM z c π σ w0 v ξ (t : Mt k r) p1 = aVec z c π σ w0 v ξ t p1 := by
  have g : (Matrix.of p1.1)⁻¹ * (Matrix.of p1.2)⁻¹ * t ∈ UH (Hpk k r) :=
    Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hp1.1)
      (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hp2.1)) ht
  have e1 : cM σ v w0 (Formalism.FourierDecayAlt.P.B7.mulM (Formalism.FourierDecayAlt.P.B7.mulM (Formalism.FourierDecayAlt.P.B7.invM p1.1)
      (Formalism.FourierDecayAlt.P.B7.invM p1.2)) (t : Mt k r)) = ⟪v, σ ((Matrix.of p1.1)⁻¹ * (Matrix.of p1.2)⁻¹ * t) w0⟫_ℂ :=
    Set.indicator_of_mem (s := {g : Mt k r | Matrix.of g ∈ UH (Hpk k r)}) g _
  have e2 : piV z π ξ p1.1 = π (Matrix.of p1.1) ξ :=
    Set.indicator_of_mem (s := {h : Mt k r | Matrix.of h ∈ UWset k r z}) hp1 _
  simp only [aM, aVec]
  rw [e1, e2]

theorem aesm_aVec [FiniteDimensional ℂ Wp] {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ}
    {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)}
    (hT : 0 < Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π) (c : ℂ) (w0 v : H) (ξ : Wp)
    {t : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ht : t ∈ UH (Hpk k r))
    {μW μN : Measure (Mt k r)} [SFinite μW] [SFinite μN]
    (h1 : ∀ᵐ x ∂μW, Matrix.of x ∈ UWset k r z) (h2 : ∀ᵐ x ∂μN, Matrix.of x ∈ Nset k r) :
    AEStronglyMeasurable (aVec z c π σ w0 v ξ t) (μW.prod μN) := by
  have hs := sm_aM hσ hT hπ c w0 v ξ (t := fun _ : Mt k r × Mt k r => (t : Mt k r)) (p1 := id)
    measurable_const measurable_id
  refine hs.aestronglyMeasurable.congr ?_
  have h1' : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z := Measure.quasiMeasurePreserving_fst.ae h1
  have h2' : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.2 ∈ Nset k r := Measure.quasiMeasurePreserving_snd.ae h2
  filter_upwards [h1', h2'] with p hp1 hp2
  exact aM_eq z c π σ w0 v ξ ht hp1 hp2

end Pt

theorem rankOne_zero_right {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] (w : E) : (innerSL ℂ w).smulRight (0 : F) = 0 := by
  ext η; simp

theorem rankOne_zero_left {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] (u : F) : (innerSL ℂ (0 : E)).smulRight u = 0 := by
  ext η; simp

theorem pair_split (L : LocBessel k r) [SFinite L.μW] [SFinite L.μW'] [SFinite L.μN]
    (hιW : MeasurePreserving (Formalism.FourierDecayAlt.P.B7.invM (k := k) (r := r)) L.μW L.μW)
    (hιW' : MeasurePreserving (Formalism.FourierDecayAlt.P.B7.invM (k := k) (r := r)) L.μW' L.μW')
    (hιN : MeasurePreserving (Formalism.FourierDecayAlt.P.B7.invM (k := k) (r := r)) L.μN L.μN)
    (hW1 : ∀ᵐ x ∂L.μW, Matrix.of x ∈ UWset k r L.z) (hW1' : ∀ᵐ x ∂L.μW', Matrix.of x ∈ UWset k r L.z')
    (hN1 : ∀ᵐ x ∂L.μN, Matrix.of x ∈ Nset k r)
    (w0 v v' : L.Hs) (ξ : L.Wp) (ξ' : L.Wq) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq)
    {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} {x : Mt k r}
    (hx : Matrix.of x ∈ UH (Hpk k r)) (hγx : γ * Matrix.of x ∈ UH (Hpk k r))
    (hbe : Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π L.σ L.μW L.μN (L.σ (γ * Matrix.of x) w0) v =
      (innerSL ℂ (l v)).smulRight (l (L.σ (γ * Matrix.of x) w0)))
    (hbe' : Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' L.σ L.μW' L.μN (L.σ (Matrix.of x) w0) v' =
      (innerSL ℂ (l' v')).smulRight (l' (L.σ (Matrix.of x) w0)))
    (hI : Integrable (fun p => Psi L w0 v v' ξ ξ' γ p x) (pairMeas L)) :
    ∫ p, Psi L w0 v v' ξ ξ' γ p x ∂(pairMeas L) =
      (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ) • (innerSL ℂ (l' (L.σ (Matrix.of x) w0))).smulRight (l (L.σ (γ * Matrix.of x) w0)) := by
  have hσ : PI.UpqRep.IsDSHpk k r L.ε L.lam L.σ := L.hσ
  set a := aVec L.z L.c L.π L.σ w0 v ξ (γ * Matrix.of x) with ha_def
  set b := aVec L.z' L.c L.π' L.σ w0 v' ξ' (Matrix.of x) with hb_def
  have hPsi : (fun p => Psi L w0 v v' ξ ξ' γ p x) = fun q : PairSp k r => (innerSL ℂ (b q.2)).smulRight (a q.1) := rfl
  have hpm : pairMeas L = (L.μW.prod L.μN).prod (L.μW'.prod L.μN) := rfl
  have haS : AEStronglyMeasurable a (L.μW.prod L.μN) := aesm_aVec hσ L.hz.2 L.hπ L.c w0 v ξ hγx hW1 hN1
  have hbS : AEStronglyMeasurable b (L.μW'.prod L.μN) := aesm_aVec hσ L.hz'.2 L.hπ' L.c w0 v' ξ' hx hW1' hN1
  have ha_eq := fun hA => int_a_eq hσ L.hz.1 L.hz.2 L.hπ L.c w0 v ξ hγx hιW hιN hW1 hN1 l hbe hA
  have hb_eq := fun hB => int_a_eq hσ L.hz'.1 L.hz'.2 L.hπ' L.c w0 v' ξ' hx hιW' hιN hW1' hN1 l' hbe' hB
  have hRHS : (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ) •
      (innerSL ℂ (l' (L.σ (Matrix.of x) w0))).smulRight (l (L.σ (γ * Matrix.of x) w0)) =
      (innerSL ℂ (⟪l' v', ξ'⟫_ℂ • l' (L.σ (Matrix.of x) w0))).smulRight (⟪l v, ξ⟫_ℂ • l (L.σ (γ * Matrix.of x) w0)) := by
    rw [rankOne_smul]
    congr 2
    rw [← starRingEnd_apply, inner_conj_symm]
  rw [hRHS, hPsi, hpm]
  rw [hpm, hPsi] at hI
  have hprod : ∫⁻ q : PairSp k r, ‖(innerSL ℂ (b q.2)).smulRight (a q.1)‖ₑ ∂((L.μW.prod L.μN).prod (L.μW'.prod L.μN)) =
      (∫⁻ p, ‖a p‖ₑ ∂(L.μW.prod L.μN)) * ∫⁻ p, ‖b p‖ₑ ∂(L.μW'.prod L.μN) := by
    simp_rw [enorm_rankOne, mul_comm (‖b _‖ₑ)]
    exact lintegral_prod_mul haS.enorm hbS.enorm
  have hfin : (∫⁻ p, ‖a p‖ₑ ∂(L.μW.prod L.μN)) * ∫⁻ p, ‖b p‖ₑ ∂(L.μW'.prod L.μN) < ⊤ := by
    rw [← hprod]; exact hI.2
  by_cases hA0 : ∫⁻ p, ‖a p‖ₑ ∂(L.μW.prod L.μN) = 0
  · have hz : ∀ᵐ p ∂(L.μW.prod L.μN), a p = 0 :=
      ((lintegral_eq_zero_iff' haS.enorm).mp hA0).mono fun p hp => enorm_eq_zero.mp hp
    have e := ha_eq (Or.inr hz)
    rw [integral_eq_zero_of_ae hz] at e
    rw [← e, rankOne_zero_right]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hz] with q hq
    rw [hq, rankOne_zero_right]; rfl
  by_cases hB0 : ∫⁻ p, ‖b p‖ₑ ∂(L.μW'.prod L.μN) = 0
  · have hz : ∀ᵐ p ∂(L.μW'.prod L.μN), b p = 0 :=
      ((lintegral_eq_zero_iff' hbS.enorm).mp hB0).mono fun p hp => enorm_eq_zero.mp hp
    have e := hb_eq (Or.inr hz)
    rw [integral_eq_zero_of_ae hz] at e
    rw [← e, rankOne_zero_left]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae hz] with q hq
    rw [hq, rankOne_zero_left]; rfl
  have hAB := ENNReal.mul_lt_top_iff.mp hfin
  have hlt : (∫⁻ p, ‖a p‖ₑ ∂(L.μW.prod L.μN)) < ⊤ ∧ (∫⁻ p, ‖b p‖ₑ ∂(L.μW'.prod L.μN)) < ⊤ := by
    rcases hAB with h | h | h
    · exact h
    · exact absurd h hA0
    · exact absurd h hB0
  have haI : Integrable a (L.μW.prod L.μN) := ⟨haS, hlt.1⟩
  have hbI : Integrable b (L.μW'.prod L.μN) := ⟨hbS, hlt.2⟩
  rw [integral_rankOne_prod haI hbI hI, ha_eq (Or.inl haI), hb_eq (Or.inl hbI)]

end Formalism.MainNotions.S.Pv.AmpDDPf
end
end
end
