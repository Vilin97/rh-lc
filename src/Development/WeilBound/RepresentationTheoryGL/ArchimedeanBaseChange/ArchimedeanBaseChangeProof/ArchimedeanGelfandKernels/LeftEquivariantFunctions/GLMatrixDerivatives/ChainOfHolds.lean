module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ChainOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneralLinearGroupUnimodularStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthFunctionFactsHoldStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightDerivativeCalculusHoldsStatement
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfCactB
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthFunctionFactsHold
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfCdcB
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfCdc
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfCdcA
import Mathlib.RingTheory.PiTensorProduct
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfCwave
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfDone

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfCactC

section

@[expose] public section

noncomputable section

open MeasureTheory Matrix Finset Filter Topology Metric Set
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Cact

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open GlobalTheory.CompanionTheory.LengthGL (isOpen_GLs mem_GLs_val isCompact_G contDiffOn_lg)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem fderiv_eq_zero_of_lg {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {g : Mat n → V} {R : ℝ}
    (hg : ∀ y ∈ GLs n, R < lg y → g y = 0) {y : Mat n} (hy : y ∈ GLs n) (hR : R < lg y) : fderiv ℝ g y = 0 := by
  have hN : IsOpen (GLs n ∩ lg ⁻¹' Ioi R) := contDiffOn_lg.continuousOn.isOpen_inter_preimage isOpen_GLs isOpen_Ioi
  have h0 : g =ᶠ[𝓝 y] fun _ => (0 : V) :=
    eventually_of_mem (hN.mem_nhds ⟨hy, hR⟩) fun w hw => hg w hw.1 hw.2
  rw [h0.fderiv_eq]
  exact fderiv_const_apply 0

theorem continuousOn_Rd {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {g : Mat n → V}
    (hg : ContDiffOn ℝ ∞ g (GLs n)) (X : Mat n) : ContinuousOn (Rd X g) (GLs n) := by
  have h1 : ContinuousOn (fderiv ℝ g) (GLs n) := hg.continuousOn_fderiv_of_isOpen isOpen_GLs (by simp)
  have h2 : ContinuousOn (fun y : Mat n => y * X) (GLs n) := (cdo_mul contDiffOn_id contDiffOn_const).continuousOn
  exact h1.clm_apply h2

theorem ibpAct : IBPAct := by
  intro _hU hRc n _ _ μ _ E k f hk hkc hf X x hx
  have hmap : MapsTo (fun y : Mat n => x * y) (GLs n) (GLs n) := fun y hy => mul_mem hx hy
  have hxy : ContDiffOn ℝ ∞ (fun y : Mat n => x * y) (GLs n) := cdo_mul contDiffOn_const contDiffOn_id
  have hkr : ContDiffOn ℝ ∞ (fun y => (k y).restrictScalars ℝ) (GLs n) :=
    (ContinuousLinearMap.restrictScalarsL ℂ E.V E.V ℝ ℝ).contDiff.comp_contDiffOn hk
  have hF : ContDiffOn ℝ ∞ (fun y : Mat n => k y (f (x * y))) (GLs n) := hkr.clm_apply (hf.comp hxy hmap)
  obtain ⟨R, hR⟩ := hkc
  have hFc : Cpt (fun y : Mat n => k y (f (x * y))) := ⟨R, fun y hy h => by simp [hR y hy h]⟩
  have h0 := (hRc n).2.2 μ E.V (fun y : Mat n => k y (f (x * y))) hF hFc X
  have hdF : ∀ y ∈ GLs n, Rd X (fun y : Mat n => k y (f (x * y))) y =
      Rd X k y (f (x * y)) + k y (Rd X f (x * y)) := by
    intro y hy
    have hk' : HasFDerivAt k (fderiv ℝ k y) y :=
      ((hk.differentiableOn (by simp)).differentiableAt (isOpen_GLs.mem_nhds hy)).hasFDerivAt
    have hk2 : HasFDerivAt (fun y => (k y).restrictScalars ℝ)
        ((ContinuousLinearMap.restrictScalarsL ℂ E.V E.V ℝ ℝ).comp (fderiv ℝ k y)) y :=
      (ContinuousLinearMap.restrictScalarsL ℂ E.V E.V ℝ ℝ).hasFDerivAt.comp y hk'
    have hf' : HasFDerivAt f (fderiv ℝ f (x * y)) (x * y) :=
      ((hf.differentiableOn (by simp)).differentiableAt (isOpen_GLs.mem_nhds (hmap hy))).hasFDerivAt
    have hg : HasFDerivAt (fun y : Mat n => f (x * y)) ((fderiv ℝ f (x * y)).comp (mulL x)) y :=
      hf'.comp y (mulL x).hasFDerivAt
    have hFD := hk2.clm_apply hg
    have e1 : Rd X (fun y : Mat n => k y (f (x * y))) y =
        k y (fderiv ℝ f (x * y) (x * (y * X))) + (fderiv ℝ k y (y * X)) (f (x * y)) := by
      exact (congrArg (fun L => L (y * X)) hFD.fderiv).trans rfl
    rw [e1, ← Matrix.mul_assoc]
    show _ = fderiv ℝ k y (y * X) (f (x * y)) + k y (fderiv ℝ f (x * y) (x * y * X))
    exact add_comm _ _
  have hK := isCompact_G (n := n) R
  have hA : Integrable (fun y : G n => Rd X k y.val (f (x * y.val))) μ := by
    refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.intro hK fun y hy => ?_)
    · have hc : ContinuousOn (fun y : Mat n => Rd X k y (f (x * y))) (GLs n) :=
        (continuousOn_Rd hk X).clm_apply (hf.continuousOn.comp hxy.continuousOn hmap)
      exact hc.comp_continuous Units.continuous_val mem_GLs_val
    · have : fderiv ℝ k y.val = 0 := fderiv_eq_zero_of_lg hR (mem_GLs_val y) (lt_of_not_ge hy)
      simp [Rd, this]
  have hB : Integrable (fun y : G n => k y.val (Rd X f (x * y.val))) μ := by
    refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.intro hK fun y hy => ?_)
    · have hc : ContinuousOn (fun y : Mat n => k y (Rd X f (x * y))) (GLs n) :=
        hk.continuousOn.clm_apply ((continuousOn_Rd hf X).comp hxy.continuousOn hmap)
      exact hc.comp_continuous Units.continuous_val mem_GLs_val
    · simp [hR y.val (mem_GLs_val y) (lt_of_not_ge hy)]
  have hsum : ∫ y : G n, Rd X (fun y : Mat n => k y (f (x * y))) y.val ∂μ =
      ∫ y : G n, Rd X k y.val (f (x * y.val)) ∂μ + ∫ y : G n, k y.val (Rd X f (x * y.val)) ∂μ := by
    rw [← integral_add hA hB]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => hdF y.val (mem_GLs_val y))
  rw [hsum] at h0
  rw [eq_neg_iff_add_eq_zero, add_comm]
  exact h0

end PositivityTheory.RgBcC.LfSt.ChainPf.Cact
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfCdcC

section

@[expose] public section

noncomputable section

open Matrix Finset
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Cdc

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def mulLL (a : Mat n) : Mat n →L[ℝ] Mat n := LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ a)

theorem hb_conj_back' (k : Matrix.unitaryGroup (Fin n) ℂ) (X : Mat n) :
    (k.1)ᴴ * (k.1 * X * (k.1)ᴴ) * k.1 = X := by
  rw [show (k.1)ᴴ * (k.1 * X * (k.1)ᴴ) * k.1 = (k.1)ᴴ * (((k.1 * X * (k.1)ᴴ)) * k.1) by simp only [Matrix.mul_assoc],
    hb_conj_back]

theorem kapEquiv : KapEquiv := by
  intro n lam E Fr ε ι S Γ T h k hk hkK
  have hopen := isOpen_GLs (n := n)
  have hkd : ∀ y ∈ GLs n, DifferentiableAt ℝ k y := fun y hy =>
    (hk.differentiableOn (by simp)).differentiableAt (hopen.mem_nhds hy)
  have hcont := hk.continuousOn_fderiv_of_isOpen hopen (by simp)
  refine ⟨?_, ?_, ?_⟩
  · unfold kapL
    apply continuousOn_finsetSum
    intro p _
    apply continuousOn_const.mul
    apply ContinuousOn.add
    · unfold Ld
      exact (hcont.clm_apply (mulLL (hb p)).continuous.continuousOn).neg
    · exact continuousOn_const.mul hk.continuousOn
  · unfold kapR
    apply continuousOn_finsetSum
    intro p _
    apply ContinuousOn.add
    · unfold Rd
      exact (hcont.clm_apply (mulRL (hb p)).continuous.continuousOn).neg.mul continuousOn_const
    · exact (hk.continuousOn.mul continuousOn_const).mul continuousOn_const
  · intro y hy k₂
    set Φ : (E.V →L[ℂ] E.V) →L[ℝ] (E.V →L[ℂ] E.V) :=
      ((ContinuousLinearMap.mul ℂ (E.V →L[ℂ] E.V)).flip (E.ρ k₂)).restrictScalars ℝ with hΦ
    have hyk : y * k₂.1 ∈ GLs n := mem_GLs_mul hy (unit_mem k₂)
    have hEq : (fun z => k (z * k₂.1)) =ᶠ[nhds y] fun z => Φ (k z) := by
      filter_upwards [hopen.mem_nhds hy] with z hz
      rw [hkK z hz k₂]
      rfl
    have hD : ∀ Z, fderiv ℝ k (y * k₂.1) (Z * k₂.1) = fderiv ℝ k y Z * E.ρ k₂ := fun Z =>
      fderiv_right k k₂.1 y Φ (hkd _ hyk) (hkd y hy) hEq Z
    constructor
    · have hLd : ∀ X, Ld X k (y * k₂.1) = Ld X k y * E.ρ k₂ := by
        intro X
        unfold Ld
        rw [show X * (y * k₂.1) = (X * y) * k₂.1 by rw [Matrix.mul_assoc], hD, neg_mul]
      unfold kapL
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [hLd, hkK y hy k₂]
      simp only [mul_assoc, add_mul]
    · set Y : Fin n × Fin n → Mat n := fun p => k₂.1 * hb p * (k₂.1)ᴴ with hYdef
      have hRd : ∀ p, Rd (hb p) k (y * k₂.1) = Rd (Y p) k y * E.ρ k₂ := by
        intro p
        unfold Rd
        rw [show y * k₂.1 * hb p = (y * Y p) * k₂.1 by
          simp only [hYdef, Matrix.mul_assoc, unit_star_mul, Matrix.mul_one], hD]
      have hε : ∀ p, E.ρ k₂ * ε (hb p) = ε (Y p) * E.ρ k₂ := by
        intro p
        rw [eps_rho h k₂ (Y p) (conj_herm _ _ (hb_herm p)), hYdef]
        dsimp only
        rw [hb_conj_back']
      have hF : ∀ p, E.ρ k₂ * fderiv ℝ Fr 1 (hb p) = fderiv ℝ Fr 1 (Y p) * E.ρ k₂ := by
        intro p
        have := dFr_conj h k₂ (Y p)
        rw [hYdef, hb_conj_back] at this
        rw [this, ← mul_assoc, ← mul_assoc, rho_mul_inv, one_mul]
      let B : Mat n →ₗ[ℝ] Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V) := LinearMap.mk₂ ℝ
        (fun H H' => -(fderiv ℝ k y (y * H')) * ε H + k y * ε H * fderiv ℝ Fr 1 H')
        (fun H₁ H₂ H' => by simp only [map_add (f := _), mul_add, add_mul]; abel)
        (fun c H H' => by simp only [map_smul, mul_smul_comm, smul_mul_assoc, smul_add])
        (fun H H₁ H₂ => by simp only [Matrix.mul_add, map_add (f := _), neg_add, add_mul, mul_add]; abel)
        (fun c H H' => by
          simp only [Matrix.mul_smul, map_smul, neg_smul, smul_mul_assoc, mul_smul_comm, smul_add, ← smul_neg])
      have hkapR : kapR ε Fr k y = ∑ p, B (hb p) (hb p) := rfl
      have hterm : ∀ p, -(Rd (hb p) k (y * k₂.1)) * ε (hb p) + k (y * k₂.1) * ε (hb p) * fderiv ℝ Fr 1 (hb p) =
          B (Y p) (Y p) * E.ρ k₂ := by
        intro p
        rw [hRd, hkK y hy k₂]
        show -(Rd (Y p) k y * E.ρ k₂) * ε (hb p) + k y * E.ρ k₂ * ε (hb p) * fderiv ℝ Fr 1 (hb p) =
          (-(fderiv ℝ k y (y * Y p)) * ε (Y p) + k y * ε (Y p) * fderiv ℝ Fr 1 (Y p)) * E.ρ k₂
        rw [neg_mul, mul_assoc (Rd (Y p) k y), hε, mul_assoc (k y), hε, mul_assoc (k y), mul_assoc (ε (Y p)), hF]
        simp only [Rd, add_mul, neg_mul, mul_assoc]
      unfold kapR
      rw [Finset.sum_congr rfl (fun p _ => hterm p), ← Finset.sum_mul]
      congr 1
      rw [basis_inv B k₂]
      rfl

end PositivityTheory.RgBcC.LfSt.ChainPf.Cdc
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfFinal

section

@[expose] public section

namespace PositivityTheory.RgBcC.LfSt.ChainPf

open PositivityTheory.RgBcC

theorem chain_identity_multiplier_kernels (hU : Unimod) (hR : RCalc) (hL : LgFacts) : ChainOf' :=
  Done.chainOf'_of Cdc.dCinCE Cwave.paramInt Cact.actDer Cact.ibpAct Cdc.kapEquiv hU hR hL

end PositivityTheory.RgBcC.LfSt.ChainPf
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfHolds

section

@[expose] public section

namespace PositivityTheory.RgBcC.LfSt

theorem chainOf'_holds : PositivityTheory.RgBcC.ChainOf' := ChainPf.chain_identity_multiplier_kernels GlobalTheory.T.general_linear_group_unimodular GlobalTheory.T.right_derivative_calculus_holds GlobalTheory.T.length_function_facts_hold

end PositivityTheory.RgBcC.LfSt
end
end
