module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.AmpOrbOfAmpDD
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.SfiniteMuN
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PsiMajNonneg
public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.AeInPairPair
public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.IntegralRankOneProd
public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.NormPsiOne
public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.MeasurableMulInvInv
public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.SigmaFiniteOfWeight
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.InPairOfStab
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.ProductFirstZerothParts
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.SigmaFiniteOfUnfold

-- Source module: Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.ProductFirstParts

section

@[expose] public section

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.MainNotions.S.Pv.AmpDDPf

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

attribute [local instance] Formalism.FourierDecayAlt.P.B7.properFD

theorem qG_invM (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (x a : Mt k r) :
    qG γ (x, Formalism.FourierDecayAlt.P.B7.invM a) = Matrix.of.symm (γ⁻¹ * (Matrix.of a)⁻¹ * γ * Matrix.of x) := rfl

theorem qG_inv_mem {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hγ : γ ∈ UH (Hpk k r))
    {x a : Mt k r} (hx : Matrix.of x ∈ UH (Hpk k r)) (ha : Matrix.of a ∈ UH (Hpk k r)) :
    Matrix.of (qG γ (x, Formalism.FourierDecayAlt.P.B7.invM a)) ∈ UH (Hpk k r) := by
  rw [qG_invM, Equiv.apply_symm_apply]
  exact Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul
    (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hγ) (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv ha)) hγ) hx

section Cell

variable (L : LocBessel k r) (w0 v v' : L.Hs) (ξ : L.Wp) (ξ' : L.Wq)
  {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} {μG μR νR : Measure (Mt k r)}

theorem PsiM_stab (hγ : γ ∈ UH (Hpk k r)) (hrel : IsRelStab L γ) {p : PairSp k r} (hp : InPair L p)
    {a : Mt k r} (ha : Matrix.of a ∈ RStab k r γ) {x : Mt k r} (hx : Matrix.of x ∈ UH (Hpk k r)) :
    PsiM L w0 v v' ξ ξ' γ (mStab γ (p, a), x) = PsiM L w0 v v' ξ ξ' γ (p, qG γ (x, Formalism.FourierDecayAlt.P.B7.invM a)) := by
  have hq := qG_inv_mem hγ hx ha.1.1
  rw [PsiM_eq L w0 v v' ξ ξ' hγ hp hq, qG_invM]
  show PsiM L w0 v v' ξ ξ' γ (stabAct γ (Matrix.of a) p, x) = _
  rw [PsiM_eq L w0 v v' ξ ξ' hγ (inPair_stab L hp ha) hx, Psi_stab L w0 v v' ξ ξ' hγ hrel hp ha x]

theorem lint_cell (hγ : γ ∈ UH (Hpk k r)) (hrel : IsRelStab L γ) (hμG : IsHaarOn (UH (Hpk k r)) μG)
    (hμR : IsHaarOn (RStab k r γ) μR) (hinv : MeasurePreserving (Formalism.FourierDecayAlt.P.B7.invM (k := k) (r := r)) μR μR)
    (hQ : PI.BesselPeriodGGP.IsQuotMeas μG (μR.map (fun x => fun i j => (γ⁻¹ * Matrix.of x * γ) i j)) νR)
    {p : PairSp k r} (hp : InPair L p) :
    ∫⁻ a, ∫⁻ x, ‖PsiM L w0 v v' ξ ξ' γ (mStab γ (p, a), x)‖ₑ ∂νR ∂μR =
      ∫⁻ y, ‖Psi L w0 v v' ξ ξ' γ p y‖ₑ ∂μG := by
  haveI : SigmaFinite μR := hμR.1
  haveI : SigmaFinite νR := sigmaFinite_nuR hμG hμR hQ
  have hmeasP : Measurable (fun y : Mt k r => ‖PsiM L w0 v v' ξ ξ' γ (p, y)‖ₑ) :=
    ((sm_PsiM L w0 v v' ξ ξ' γ).measurable.comp measurable_prodMk_left).enorm
  have hmeasQ : Measurable (fun q : Mt k r × Mt k r => ‖PsiM L w0 v v' ξ ξ' γ (p, qG γ q)‖ₑ) :=
    hmeasP.comp (continuous_qG γ).measurable
  have hR : ∀ᵐ a ∂μR, Matrix.of a ∈ RStab k r γ := ae_iff.mpr hμR.2.2.1
  have hU := ae_uh_nuR hγ hμG hμR hQ
  calc ∫⁻ a, ∫⁻ x, ‖PsiM L w0 v v' ξ ξ' γ (mStab γ (p, a), x)‖ₑ ∂νR ∂μR
      = ∫⁻ a, ∫⁻ x, ‖PsiM L w0 v v' ξ ξ' γ (p, qG γ (x, Formalism.FourierDecayAlt.P.B7.invM a))‖ₑ ∂νR ∂μR := by
        refine lintegral_congr_ae (hR.mono (fun a ha => ?_))
        refine lintegral_congr_ae (hU.mono (fun x hx => ?_))
        dsimp only
        rw [PsiM_stab L w0 v v' ξ ξ' hγ hrel hp ha hx]
    _ = ∫⁻ a, ∫⁻ x, ‖PsiM L w0 v v' ξ ξ' γ (p, qG γ (x, a))‖ₑ ∂νR ∂μR :=
        hinv.lintegral_comp hmeasQ.lintegral_prod_left'
    _ = ∫⁻ x, ∫⁻ a, ‖PsiM L w0 v v' ξ ξ' γ (p, qG γ (x, a))‖ₑ ∂μR ∂νR :=
        lintegral_lintegral_swap (hmeasQ.comp measurable_swap).aemeasurable
    _ = ∫⁻ q, ‖PsiM L w0 v v' ξ ξ' γ (p, qG γ q)‖ₑ ∂(νR.prod μR) :=
        (lintegral_prod _ hmeasQ.aemeasurable).symm
    _ = ∫⁻ y, ‖PsiM L w0 v v' ξ ξ' γ (p, y)‖ₑ ∂μG := by
        rw [muG_eq_map hμR hQ, lintegral_map hmeasP (continuous_qG γ).measurable]
    _ = ∫⁻ y, ‖Psi L w0 v v' ξ ξ' γ p y‖ₑ ∂μG := by
        have hG : ∀ᵐ y ∂μG, Matrix.of y ∈ UH (Hpk k r) := ae_iff.mpr hμG.2.2.1
        refine lintegral_congr_ae (hG.mono (fun y hy => ?_))
        dsimp only
        rw [PsiM_eq L w0 v v' ξ ξ' hγ hp hy]

theorem int_cell (hγ : γ ∈ UH (Hpk k r)) (hrel : IsRelStab L γ) (hμG : IsHaarOn (UH (Hpk k r)) μG)
    (hμR : IsHaarOn (RStab k r γ) μR) (hinv : MeasurePreserving (Formalism.FourierDecayAlt.P.B7.invM (k := k) (r := r)) μR μR)
    (hQ : PI.BesselPeriodGGP.IsQuotMeas μG (μR.map (fun x => fun i j => (γ⁻¹ * Matrix.of x * γ) i j)) νR)
    {p : PairSp k r} (hp : InPair L p) (hint : Integrable (fun y => Psi L w0 v v' ξ ξ' γ p y) μG) :
    ∫ a, ∫ x, PsiM L w0 v v' ξ ξ' γ (mStab γ (p, a), x) ∂νR ∂μR = ∫ y, Psi L w0 v v' ξ ξ' γ p y ∂μG := by
  haveI : SigmaFinite μR := hμR.1
  haveI : SigmaFinite νR := sigmaFinite_nuR hμG hμR hQ
  have hsmP : StronglyMeasurable (fun y : Mt k r => PsiM L w0 v v' ξ ξ' γ (p, y)) :=
    (sm_PsiM L w0 v v' ξ ξ' γ).comp_measurable measurable_prodMk_left
  have hsmQ : StronglyMeasurable (fun q : Mt k r × Mt k r => PsiM L w0 v v' ξ ξ' γ (p, qG γ q)) :=
    hsmP.comp_measurable (continuous_qG γ).measurable
  have hR : ∀ᵐ a ∂μR, Matrix.of a ∈ RStab k r γ := ae_iff.mpr hμR.2.2.1
  have hU := ae_uh_nuR hγ hμG hμR hQ
  have hG : ∀ᵐ y ∂μG, Matrix.of y ∈ UH (Hpk k r) := ae_iff.mpr hμG.2.2.1
  have hGeq : (fun y => PsiM L w0 v v' ξ ξ' γ (p, y)) =ᵐ[μG] fun y => Psi L w0 v v' ξ ξ' γ p y :=
    hG.mono (fun y hy => PsiM_eq L w0 v v' ξ ξ' hγ hp hy)
  have hintP : Integrable (fun y => PsiM L w0 v v' ξ ξ' γ (p, y)) μG := hint.congr hGeq.symm
  have hμ := muG_eq_map hμR hQ
  have hintQ : Integrable (fun q : Mt k r × Mt k r => PsiM L w0 v v' ξ ξ' γ (p, qG γ q)) (νR.prod μR) := by
    rw [hμ] at hintP
    exact (integrable_map_measure hsmP.aestronglyMeasurable (continuous_qG γ).measurable.aemeasurable).mp hintP
  have hsmA : StronglyMeasurable (fun a => ∫ x, PsiM L w0 v v' ξ ξ' γ (p, qG γ (x, a)) ∂νR) :=
    hsmQ.integral_prod_left
  calc ∫ a, ∫ x, PsiM L w0 v v' ξ ξ' γ (mStab γ (p, a), x) ∂νR ∂μR
      = ∫ a, ∫ x, PsiM L w0 v v' ξ ξ' γ (p, qG γ (x, Formalism.FourierDecayAlt.P.B7.invM a)) ∂νR ∂μR := by
        refine integral_congr_ae (hR.mono (fun a ha => ?_))
        refine integral_congr_ae (hU.mono (fun x hx => ?_))
        dsimp only
        rw [PsiM_stab L w0 v v' ξ ξ' hγ hrel hp ha hx]
    _ = ∫ a, ∫ x, PsiM L w0 v v' ξ ξ' γ (p, qG γ (x, a)) ∂νR ∂μR := by
        have h := integral_map (μ := μR) hinv.measurable.aemeasurable
          (f := fun a => ∫ x, PsiM L w0 v v' ξ ξ' γ (p, qG γ (x, a)) ∂νR)
          (by rw [hinv.map_eq]; exact hsmA.aestronglyMeasurable)
        rw [hinv.map_eq] at h
        exact h.symm
    _ = ∫ x, ∫ a, PsiM L w0 v v' ξ ξ' γ (p, qG γ (x, a)) ∂μR ∂νR :=
        integral_integral_swap hintQ.swap
    _ = ∫ q, PsiM L w0 v v' ξ ξ' γ (p, qG γ q) ∂(νR.prod μR) := (integral_prod _ hintQ).symm
    _ = ∫ y, PsiM L w0 v v' ξ ξ' γ (p, y) ∂μG := by
        rw [hμ, integral_map (continuous_qG γ).measurable.aemeasurable hsmP.aestronglyMeasurable]
    _ = ∫ y, Psi L w0 v v' ξ ξ' γ p y ∂μG := integral_congr_ae hGeq

end Cell

end Formalism.MainNotions.S.Pv.AmpDDPf
end
end
end

-- Source module: Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.FlipOneTwo

section

@[expose] public section

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.MainNotions.S.Pv.AmpDDPf

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

attribute [local instance] Formalism.FourierDecayAlt.P.B7.properFD

theorem pairMaj_nonneg (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (b : ℝ) (p : PairSp k r) :
    0 ≤ Formalism.MainNotions.S.Pv.AmpDD.pairMaj γ b p :=
  Real.rpow_nonneg (Formalism.FourierDecayAlt.P.S3dx6.gN_nonneg _) _

theorem amp_core' (L : LocBessel k r) {μG : Measure (Mt k r)} (hμG : IsHaarOn (UH (Hpk k r)) μG) {d : ℝ}
    (hd : 0 < d)
    (hSch : ∀ v w v' w' : L.Hs,
      Integrable (fun x : Mt k r => ⟪w, L.σ (Matrix.of x) v⟫_ℂ * star ⟪w', L.σ (Matrix.of x) v'⟫_ℂ) μG ∧
      ∫ x, ⟪w, L.σ (Matrix.of x) v⟫_ℂ * star ⟪w', L.σ (Matrix.of x) v'⟫_ℂ ∂μG = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ))
    (hNI : Formalism.FourierDecayAlt.ThreeDimData.NormInv) {w0 : L.Hs} (hw1 : ⟪w0, w0⟫_ℂ = 1) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq)
    {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hγ : γ ∈ UH (Hpk k r)) (hrel : IsRelStab L γ)
    {μR νR : Measure (Mt k r)} {ν : Measure (PairSp k r)} (hμR : IsHaarOn (RStab k r γ) μR)
    (hOQ : IsOrbQuot L γ μR ν)
    (hQ : PI.BesselPeriodGGP.IsQuotMeas μG (μR.map (fun x => fun i j => (γ⁻¹ * Matrix.of x * γ) i j)) νR)
    (hinv : MeasurePreserving (Formalism.FourierDecayAlt.P.B7.invM (k := k) (r := r)) μR μR)
    {a b C1 C2 : ℝ} (hb : 0 ≤ b) (hab : b ≤ a)
    (hIG : Integrable (fun x : Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (b - a)) μG)
    (hpm : Integrable (Formalism.MainNotions.S.Pv.AmpDD.pairMaj γ b) ν)
    {v v' : L.Hs}
    (hbe1 : ∀ t ∈ UH (Hpk k r), Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π L.σ L.μW L.μN (L.σ t w0) v =
      (innerSL ℂ (l v)).smulRight (l (L.σ t w0)))
    (hbe2 : ∀ t ∈ UH (Hpk k r), Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' L.σ L.μW' L.μN (L.σ t w0) v' =
      (innerSL ℂ (l' v')).smulRight (l' (L.σ t w0)))
    (hC1 : ∀ g ∈ UH (Hpk k r), ‖⟪v, L.σ g w0⟫_ℂ‖ ≤ C1 * Formalism.FourierDecayAlt.B.gN g ^ (-a))
    (hC2 : ∀ g ∈ UH (Hpk k r), ‖⟪v', L.σ g w0⟫_ℂ‖ ≤ C2 * Formalism.FourierDecayAlt.B.gN g ^ (-a))
    (ξ : L.Wp) (ξ' : L.Wq) :
    (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ) • ampJ νR 1 (fun g => l (L.σ g w0)) (fun g => l' (L.σ g w0)) γ =
      ((d : ℂ)⁻¹) • OrbInt L (Formalism.MainNotions.S.Pv.AmpDD.coefF L v v' ξ ξ') γ ν := by
  have hσR : SigmaFinite μR := hμR.1
  have hσνR : SigmaFinite νR := sigmaFinite_nuR hμG hμR hQ
  have hσν : SigmaFinite ν := sigmaFinite_nu L hγ hμR hOQ hNI hpm
  have hσW : SigmaFinite L.μW := L.hμW.1.1
  have hσW' : SigmaFinite L.μW' := L.hμW'.1.1
  have hWi := mp_inv_W_sk L.hz.1 L.hz.2 L.hμW.1
  have hWi' := mp_inv_W_sk L.hz'.1 L.hz'.2 L.hμW'.1
  have hNi : MeasurePreserving Formalism.FourierDecayAlt.P.B7.invM L.μN L.μN :=
    ⟨hinv.measurable, map_inv_haarLieN L.κN⟩
  have hWae : ∀ᵐ x ∂L.μW, Matrix.of x ∈ UWset k r L.z := ae_mem_sk L.hμW.1
  have hWae' : ∀ᵐ x ∂L.μW', Matrix.of x ∈ UWset k r L.z' := ae_mem_sk L.hμW'.1
  have hNae : ∀ᵐ x ∂L.μN, Matrix.of x ∈ Nset k r := ae_mem_haarLieN L.κN
  have hsm : StronglyMeasurable (fun q : (PairSp k r × Mt k r) × Mt k r =>
      PsiM L w0 v v' ξ ξ' γ (mStab γ q.1, q.2)) :=
    (sm_PsiM L w0 v v' ξ ξ' γ).comp_measurable
      (((measurable_mStab γ).comp measurable_fst).prodMk measurable_snd)
  have hF : Integrable (fun q : (PairSp k r × Mt k r) × Mt k r =>
      PsiM L w0 v v' ξ ξ' γ (mStab γ q.1, q.2)) ((ν.prod μR).prod νR) := by
    refine ⟨hsm.aestronglyMeasurable, ?_⟩
    have hmeas : Measurable (fun q : (PairSp k r × Mt k r) × Mt k r =>
        ‖PsiM L w0 v v' ξ ξ' γ (mStab γ q.1, q.2)‖ₑ) := hsm.measurable.enorm
    have hmeas2 : Measurable (fun pa : PairSp k r × Mt k r =>
        ∫⁻ x, ‖PsiM L w0 v v' ξ ξ' γ (mStab γ pa, x)‖ₑ ∂νR) :=
      hmeas.lintegral_prod_right'
    show ∫⁻ q, ‖PsiM L w0 v v' ξ ξ' γ (mStab γ q.1, q.2)‖ₑ ∂((ν.prod μR).prod νR) < ⊤
    calc ∫⁻ q, ‖PsiM L w0 v v' ξ ξ' γ (mStab γ q.1, q.2)‖ₑ ∂((ν.prod μR).prod νR)
        = ∫⁻ pa, ∫⁻ x, ‖PsiM L w0 v v' ξ ξ' γ (mStab γ pa, x)‖ₑ ∂νR ∂(ν.prod μR) :=
          lintegral_prod _ hmeas.aemeasurable
      _ = ∫⁻ p, ∫⁻ a, ∫⁻ x, ‖PsiM L w0 v v' ξ ξ' γ (mStab γ (p, a), x)‖ₑ ∂νR ∂μR ∂ν :=
          lintegral_prod _ hmeas2.aemeasurable
      _ = ∫⁻ p, ∫⁻ y, ‖Psi L w0 v v' ξ ξ' γ p y‖ₑ ∂μG ∂ν := by
          refine lintegral_congr_ae ((ae_inPair_nu L hμR hOQ).mono fun p hp => ?_)
          exact lint_cell L w0 v v' ξ ξ' hγ hrel hμG hμR hinv hQ hp
      _ ≤ ∫⁻ p, ENNReal.ofReal ((‖ξ‖ * ‖ξ'‖ * (|C1| * |C2|) *
            ∫ x, Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (b - a) ∂μG) *
              Formalism.MainNotions.S.Pv.AmpDD.pairMaj γ b p) ∂ν := by
          refine lintegral_mono_ae ((ae_inPair_nu L hμR hOQ).mono fun p hp => ?_)
          exact lint_G_bound L hμG hNI hb hab hIG w0 v v' ξ ξ' hC1 hC2 hγ hp
      _ < ⊤ := (hpm.const_mul _).lintegral_lt_top
  have hmap := pairMeas_eq_map L hμR hOQ
  have hL : ∀ᵐ x ∂νR, (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ) •
      (innerSL ℂ (l' (L.σ (Matrix.of x) w0))).smulRight (l (L.σ (γ * Matrix.of x) w0)) =
      ∫ pa, PsiM L w0 v v' ξ ξ' γ (mStab γ pa, x) ∂(ν.prod μR) := by
    filter_upwards [ae_uh_nuR hγ hμG hμR hQ, hF.prod_left_ae] with x hx hix
    have hgx : γ * Matrix.of x ∈ UH (Hpk k r) := WeylGroupFacts.uh_mul hγ hx
    have hsmx : StronglyMeasurable (fun q : PairSp k r => PsiM L w0 v v' ξ ξ' γ (q, x)) :=
      (sm_PsiM L w0 v v' ξ ξ' γ).comp_measurable (measurable_id.prodMk measurable_const)
    have hPM : (fun q => Psi L w0 v v' ξ ξ' γ q x) =ᵐ[pairMeas L]
        (fun q => PsiM L w0 v v' ξ ξ' γ (q, x)) :=
      (ae_inPair_pair L).mono fun q hq => (PsiM_eq L w0 v v' ξ ξ' hγ hq hx).symm
    have hintM : Integrable (fun q : PairSp k r => PsiM L w0 v v' ξ ξ' γ (q, x)) (pairMeas L) := by
      rw [hmap]
      exact (integrable_map_measure hsmx.aestronglyMeasurable (measurable_mStab γ).aemeasurable).2 hix
    rw [← pair_split L hWi hWi' hNi hWae hWae' hNae w0 v v' ξ ξ' l l' hx hgx (hbe1 _ hgx)
      (hbe2 _ hx) (hintM.congr hPM.symm), integral_congr_ae hPM, hmap,
      integral_map (measurable_mStab γ).aemeasurable hsmx.aestronglyMeasurable]
  have hsch : ∀ᵐ p ∂ν, ∫ a, ∫ x, PsiM L w0 v v' ξ ξ' γ (mStab γ (p, a), x) ∂νR ∂μR =
      ((d : ℂ)⁻¹) • besselIntg L (Formalism.MainNotions.S.Pv.AmpDD.coefF L v v' ξ ξ') γ p := by
    filter_upwards [ae_inPair_nu L hμR hOQ] with p hp
    have hs := schur_step L hμG hd hSch hw1 v v' ξ ξ' hγ hp
    rw [int_cell L w0 v v' ξ ξ' hγ hrel hμG hμR hinv hQ hp hs.1, hs.2]
  calc (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ) •
        ampJ νR 1 (fun g => l (L.σ g w0)) (fun g => l' (L.σ g w0)) γ
      = ∫ x, (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ) •
          (innerSL ℂ (l' (L.σ (Matrix.of x) w0))).smulRight (l (L.σ (γ * Matrix.of x) w0)) ∂νR := by
        rw [integral_smul]
        simp [ampJ]
    _ = ∫ x, ∫ pa, PsiM L w0 v v' ξ ξ' γ (mStab γ pa, x) ∂(ν.prod μR) ∂νR := integral_congr_ae hL
    _ = ∫ pa, ∫ x, PsiM L w0 v v' ξ ξ' γ (mStab γ pa, x) ∂νR ∂(ν.prod μR) :=
        (integral_integral_swap (f := fun pa x => PsiM L w0 v v' ξ ξ' γ (mStab γ pa, x)) hF).symm
    _ = ∫ p, ∫ a, ∫ x, PsiM L w0 v v' ξ ξ' γ (mStab γ (p, a), x) ∂νR ∂μR ∂ν :=
        integral_prod _ hF.integral_prod_left
    _ = ∫ p, ((d : ℂ)⁻¹) • besselIntg L (Formalism.MainNotions.S.Pv.AmpDD.coefF L v v' ξ ξ') γ p ∂ν :=
        integral_congr_ae hsch
    _ = ((d : ℂ)⁻¹) • OrbInt L (Formalism.MainNotions.S.Pv.AmpDD.coefF L v v' ξ ξ') γ ν := by
        rw [integral_smul]
        rfl

theorem amp_core (L : LocBessel k r) {μG : Measure (Mt k r)} (hμG : IsHaarOn (UH (Hpk k r)) μG) {d : ℝ}
    (hd : 0 < d)
    (hSch : ∀ v w v' w' : L.Hs,
      Integrable (fun x : Mt k r => ⟪w, L.σ (Matrix.of x) v⟫_ℂ * star ⟪w', L.σ (Matrix.of x) v'⟫_ℂ) μG ∧
      ∫ x, ⟪w, L.σ (Matrix.of x) v⟫_ℂ * star ⟪w', L.σ (Matrix.of x) v'⟫_ℂ ∂μG = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ))
    (hNI : Formalism.FourierDecayAlt.ThreeDimData.NormInv) {w0 : L.Hs} (hw1 : ⟪w0, w0⟫_ℂ = 1) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq)
    (hl : ∀ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp L.σ w0, ∀ v ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp L.σ w0,
      Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π L.σ L.μW L.μN x v = (innerSL ℂ (l v)).smulRight (l x))
    (hl' : ∀ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp L.σ w0, ∀ v ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp L.σ w0,
      Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' L.σ L.μW' L.μN x v = (innerSL ℂ (l' v)).smulRight (l' x))
    {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hγ : γ ∈ UH (Hpk k r)) (hrel : IsRelStab L γ)
    {μR νR : Measure (Mt k r)} {ν : Measure (PairSp k r)} (hμR : IsHaarOn (RStab k r γ) μR)
    (hOQ : IsOrbQuot L γ μR ν)
    (hQ : PI.BesselPeriodGGP.IsQuotMeas μG (μR.map (fun x => fun i j => (γ⁻¹ * Matrix.of x * γ) i j)) νR)
    (hinv : MeasurePreserving (Formalism.FourierDecayAlt.P.B7.invM (k := k) (r := r)) μR μR)
    {a b C1 C2 : ℝ} (hb : 0 ≤ b) (hab : b ≤ a)
    (hIG : Integrable (fun x : Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (b - a)) μG)
    (hpm : Integrable (Formalism.MainNotions.S.Pv.AmpDD.pairMaj γ b) ν)
    {v v' : L.Hs} (hv : v ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp L.σ w0) (hv' : v' ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp L.σ w0)
    (hC1 : ∀ g ∈ UH (Hpk k r), ‖⟪v, L.σ g w0⟫_ℂ‖ ≤ C1 * Formalism.FourierDecayAlt.B.gN g ^ (-a))
    (hC2 : ∀ g ∈ UH (Hpk k r), ‖⟪v', L.σ g w0⟫_ℂ‖ ≤ C2 * Formalism.FourierDecayAlt.B.gN g ^ (-a))
    (ξ : L.Wp) (ξ' : L.Wq) :
    (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ) • ampJ νR 1 (fun g => l (L.σ g w0)) (fun g => l' (L.σ g w0)) γ =
      ((d : ℂ)⁻¹) • OrbInt L (Formalism.MainNotions.S.Pv.AmpDD.coefF L v v' ξ ξ') γ ν := by
  exact amp_core' L hμG hd hSch hNI hw1 l l' hγ hrel hμR hOQ hQ hinv hb hab hIG hpm
    (fun t ht => hl _ (Submodule.subset_span ⟨t, ht, rfl⟩) v hv)
    (fun t ht => hl' _ (Submodule.subset_span ⟨t, ht, rfl⟩) v' hv') hC1 hC2 ξ ξ'

end Formalism.MainNotions.S.Pv.AmpDDPf
end
end
end
