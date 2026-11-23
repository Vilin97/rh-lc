module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToFourierJacobiHandedFamilyContinuousAutomStatement
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiKernelEqWeilRepresentationApply
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiActionsMatchThroughLinkMap
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiKernelEqWeilRepresentationApplyStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.fourierJacobiKernel_eq_weilRepresentation_apply : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (W W₀ V₀ A L : HSp D) (ρ : ℕ) (dW : HypDec W W₀ ρ) (o : OrthDec V₀ A L) (ζ : Fin L.rank → D.host.E) (χ χ' : ((AE D)ˣ →* Circle)) (om : Om V₀ W₀), IsWeilDatumO ψ V₀ W₀ χ χ' om → ∀ Ξ, IsThetaFunO ψ V₀ W₀ Ξ → ∀ h₀ n h, fjKer ψ dW o ζ om Ξ h₀ n h = ψ (cenT dW L (yZero L ρ ζ) n) * om (o.emb (h₀, 1), h) Ξ ((o.resS W₀).symm (0, ptT dW L (yZero L ρ ζ) n)) := by
  first | exact @GlobalTheory.Unf.fjKer_eq_om_apply | exact GlobalTheory.Unf.fjKer_eq_om_apply | (intros; apply GlobalTheory.Unf.fjKer_eq_om_apply <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiActionsMatchThroughLinkMapStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.jacobiActions_match_through_linkMap : ∀ (D : D7) (ρ σ : ℕ) (B : BesLev D σ) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E), IsLineVec L' ζ' → ∀ (l : Link B L' ζ') (W W₀ : HSp D) (d : HypDec W W₀ ρ), ∀ n ∈ flagN d, l.κ W₀ (ptS d L' (zEll L' ρ ζ') n) = ptT d B.L (yZero B.L ρ B.ζ) n ∧ cenT d B.L (yZero B.L ρ B.ζ) n = -cenS d L' (zEll L' ρ ζ') n := by
  first | exact @GlobalTheory.Unf.LinkPoint.link_point | exact GlobalTheory.Unf.LinkPoint.link_point | (intros; apply GlobalTheory.Unf.LinkPoint.link_point <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLevelStepFourierJacobiPeriodLink

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.UnfLink

theorem star_psi {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) :
    star (ψ a) = ψ (-a) := by
  have h1 : ‖ψ a‖ = 1 := hψ.1.2.1 a
  have h2 : ψ a * star (ψ a) = 1 := by
    rw [Complex.star_def, Complex.mul_conj', h1]; simp
  have h3 : ψ a * ψ (-a) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have h0 : ψ a ≠ 0 := by intro h; rw [h, zero_mul] at h3; exact zero_ne_one h3
  exact mul_left_cancel₀ h0 (h2.trans h3.symm)

theorem heisO_at_zero' {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (w : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T w f 0 = f w := by
  have h : hO S T 0 w = 0 := by simp [hO]
  simp [heisO, symplOH, symplO, h]

theorem link : ∀ D : D7, LinkLaw D := by
  intro D ψ ρ B J s L' ζ' hz l φ Ξ hφ hΞ
  refine ⟨GlobalTheory.T.besselToFourierJacobi_handedFamily_continuous_automorphic D ψ ρ B J s L' ζ' hz l φ Ξ hφ hΞ, fun G' => ?_⟩
  unfold JacLev.perAll JacLev.per fjAll fjSrcKer
  congr 1; funext h; congr 1; funext n
  have hk := GlobalTheory.T.fourierJacobiKernel_eq_weilRepresentation_apply D ψ J.W J.W₀ B.V₀ B.A B.L ρ J.d B.o B.ζ _ _ s.om₀ s.weil₀ Ξ hΞ
  obtain ⟨hp, hc⟩ := GlobalTheory.T.jacobiActions_match_through_linkMap D ρ ρ B L' ζ' hz l J.W J.W₀ J.d n.1 n.2
  simp only [fjAllFun, fjSrcKerFun, JacLev.ker, jacS, handBF, hk, Pi.smul_apply, smul_eq_mul, heisO_at_zero', hp, hc]
  rw [star_mul', star_star, star_psi s.weil₀.std]
  simp_rw [mul_left_comm (φ _) (ψ _)]
  rw [integral_const_mul]
  ring

end GlobalTheory.UnfLink
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLevelStepFourierJacobiPeriodLinkStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.bessel_level_step_fourierJacobi_period_link : ∀ D : D7, LinkLaw D := by
  first | exact @GlobalTheory.UnfLink.link | exact GlobalTheory.UnfLink.link | (intros; apply GlobalTheory.UnfLink.link <;> assumption)
end
end
