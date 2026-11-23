module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.ThetaLine
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.ThetaZeroLogDerivative
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GaussianOddJacobiThetaEqDerivMulSgStarStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DifferentiableOddTheta
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HalfPeriodDiffThetaFourthOfSigmaStarAddition
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Mathlib.NumberTheory.ModularForms.DedekindEta
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HasDerivAtOddJacobiThetaZeroEtaCube
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JacobiTripleProductTwoVariableTheta
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.NormNum.Parity
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ThetaConstEqEtaWeberSqOfTripleProduct
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeberFunctionsRootsOfCubicOfHalfPeriodDiffStatement
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EllipticOnePole
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.QuasiPeriodConstUnique

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HalfPeriodDiffThetaFourthOfSigmaStarAdditionStatement

section

@[expose] public section

open Complex

theorem _root_.GlobalTheory.T.halfPeriodDiffThetaFourth_of_sigmaStar_addition : Formalism.L2.Th1.F.SgStarAdd → (∀ (τ : UpperHalfPlane) (z : ℂ), Complex.exp ((Real.pi : ℂ) * z ^ 2 / (2 * ((τ.im : ℝ) : ℂ))) * GlobalTheory.ThetaWeberRoad.oddTheta τ z = deriv (GlobalTheory.ThetaWeberRoad.oddTheta τ) 0 * Formalism.L2.Th1.F.sgStar (GlobalTheory.periodPairOfTau τ) z) → (∀ τ : UpperHalfPlane, HasDerivAt (GlobalTheory.ThetaWeberRoad.oddTheta τ) (-2 * (Real.pi : ℂ) * ModularForm.eta (τ : ℂ) ^ 3) 0) → (∀ τ : UpperHalfPlane, GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.JacobiProduct τ) → ∀ τ : UpperHalfPlane, GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.HalfPeriodDiff τ := by
  first | exact @GlobalTheory.ThetaWeberRoad.halfPeriodDiff_of | exact GlobalTheory.ThetaWeberRoad.halfPeriodDiff_of | (intros; apply GlobalTheory.ThetaWeberRoad.halfPeriodDiff_of <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HasDerivAtOddJacobiThetaZeroEtaCubeStatement

section

@[expose] public section

open Complex

theorem _root_.GlobalTheory.T.hasDerivAt_oddJacobiTheta_zero_eta_cube : GlobalTheory.ThetaWeberRoad.TripleProduct → ∀ τ : UpperHalfPlane, HasDerivAt (GlobalTheory.ThetaWeberRoad.oddTheta τ) (-2 * (Real.pi : ℂ) * ModularForm.eta (τ : ℂ) ^ 3) 0 := by
  first | exact @GlobalTheory.ThetaWeberRoad.OddDeriv.hasDerivAt_oddTheta_zero | exact GlobalTheory.ThetaWeberRoad.OddDeriv.hasDerivAt_oddTheta_zero | (intros; apply GlobalTheory.ThetaWeberRoad.OddDeriv.hasDerivAt_oddTheta_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JacobiTripleProductTwoVariableThetaStatement

section

@[expose] public section

open Complex

theorem _root_.GlobalTheory.T.jacobiTripleProduct_twoVariableTheta : GlobalTheory.ThetaWeberRoad.TripleProduct := by
  first | exact @GlobalTheory.JacobiTriple.tripleProduct | exact GlobalTheory.JacobiTriple.tripleProduct | (intros; apply GlobalTheory.JacobiTriple.tripleProduct <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ThetaConstEqEtaWeberSqOfTripleProductStatement

section

@[expose] public section

open Complex

theorem _root_.GlobalTheory.T.thetaConstEqEtaWeberSq_of_tripleProduct : GlobalTheory.ThetaWeberRoad.TripleProduct → ∀ τ : UpperHalfPlane, GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.ThetaWeber τ := by
  first | exact @GlobalTheory.ThetaWeberProof.thetaWeber_of_tripleProduct | exact GlobalTheory.ThetaWeberProof.thetaWeber_of_tripleProduct | (intros; apply GlobalTheory.ThetaWeberProof.thetaWeber_of_tripleProduct <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeberFunctionProductEqSqrtTwo

section

@[expose] public section

open Complex
open UpperHalfPlane hiding I
open scoped Real

noncomputable section

namespace GlobalTheory.WeberProduct

def eulerProd (x : ℂ) : ℂ := ∏' n : ℕ, (1 - x ^ (n + 1))

def oddProd (x : ℂ) : ℂ := ∏' k : ℕ, (1 - x ^ (2 * k + 1))

theorem multipliable_odd {x : ℂ} (hx : ‖x‖ < 1) :
    Multipliable fun k : ℕ ↦ 1 - x ^ (2 * k + 1) := by
  have h2 : ‖x‖ ^ 2 < 1 := by nlinarith [norm_nonneg x]
  have hs : Summable fun k : ℕ ↦ ‖x‖ * (‖x‖ ^ 2) ^ k :=
    (summable_geometric_of_lt_one (by positivity) h2).mul_left _
  have := multipliable_one_add_of_summable (f := fun k : ℕ ↦ -x ^ (2 * k + 1))
    (hs.congr fun k ↦ by simp [norm_pow, pow_succ, pow_mul]; ring)
  simpa [sub_eq_add_neg] using this

theorem multipliable_euler {x : ℂ} (hx : ‖x‖ < 1) :
    Multipliable fun n : ℕ ↦ 1 - x ^ (n + 1) :=
  ModularForm.multipliable_one_sub_pow hx

theorem eulerProd_split {y : ℂ} (hy : ‖y‖ < 1) : eulerProd y = oddProd y * eulerProd (y ^ 2) := by
  have hy2 : ‖y ^ 2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg y]
  have e1 : (fun k : ℕ ↦ (fun n : ℕ ↦ 1 - y ^ (n + 1)) (2 * k)) = fun k ↦ 1 - y ^ (2 * k + 1) := rfl
  have e2 : (fun k : ℕ ↦ (fun n : ℕ ↦ 1 - y ^ (n + 1)) (2 * k + 1)) =
      fun k ↦ 1 - (y ^ 2) ^ (k + 1) := by
    funext k; rw [← pow_mul]; ring_nf
  have h := tprod_even_mul_odd (f := fun n : ℕ ↦ 1 - y ^ (n + 1))
    (by rw [e1]; exact multipliable_odd hy) (by rw [e2]; exact multipliable_euler hy2)
  rw [e1, e2] at h
  rw [eulerProd, eulerProd, oddProd, h]

theorem oddProd_neg_mul {t : ℂ} (ht : ‖t‖ < 1) : oddProd (-t) * oddProd t = oddProd (t ^ 2) := by
  have hn : ‖-t‖ < 1 := by rwa [norm_neg]
  rw [oddProd, oddProd, oddProd, ← (multipliable_odd hn).tprod_mul (multipliable_odd ht)]
  congr 1
  funext k
  rw [Odd.neg_pow ⟨k, rfl⟩, ← pow_mul]
  ring_nf

theorem eulerProd_identity {t : ℂ} (ht : ‖t‖ < 1) :
    eulerProd (-t) * eulerProd t * eulerProd (t ^ 4) = eulerProd (t ^ 2) ^ 3 := by
  have hn : ‖-t‖ < 1 := by rwa [norm_neg]
  have h2 : ‖t ^ 2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg t]
  have a := eulerProd_split hn
  have b := eulerProd_split ht
  have c := eulerProd_split h2
  rw [neg_sq] at a
  rw [← pow_mul] at c
  norm_num at c
  have d := oddProd_neg_mul ht
  norm_num at c
  linear_combination (eulerProd t * eulerProd (t ^ 4)) * a + (oddProd (-t) * eulerProd (t ^ 2) * eulerProd (t ^ 4)) * b +
    (eulerProd (t ^ 2) ^ 2 * eulerProd (t ^ 4)) * d - eulerProd (t ^ 2) ^ 2 * c

theorem eta_eq (z : ℂ) : ModularForm.eta z = Function.Periodic.qParam 24 z * eulerProd (Function.Periodic.qParam 1 z) :=
  rfl

theorem eta_relation (τ : ℍ) :
    cexp (-(π * I / 24)) * ModularForm.eta (((τ : ℂ) + 1) / 2) * ModularForm.eta ((τ : ℂ) / 2) *
      ModularForm.eta (2 * (τ : ℂ)) = ModularForm.eta τ ^ 3 := by
  set t := cexp (π * I * (τ : ℂ)) with ht_def
  have ht : ‖t‖ < 1 := by
    rw [ht_def, Complex.norm_exp, Real.exp_lt_one_iff]
    have := τ.im_pos
    simp only [mul_re, ofReal_re, Complex.I_re, ofReal_im, Complex.I_im, mul_im, coe_re, coe_im]
    nlinarith [Real.pi_pos]
  have q1 : Function.Periodic.qParam 1 (((τ : ℂ) + 1) / 2) = -t := by
    rw [Function.Periodic.qParam, ht_def, ← mul_neg_one, ← Complex.exp_pi_mul_I, ← Complex.exp_add]
    congr 1; push_cast; ring
  have q2 : Function.Periodic.qParam 1 ((τ : ℂ) / 2) = t := by
    rw [Function.Periodic.qParam, ht_def]; congr 1; push_cast; ring
  have q3 : Function.Periodic.qParam 1 (2 * (τ : ℂ)) = t ^ 4 := by
    rw [Function.Periodic.qParam, ht_def, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have q4 : Function.Periodic.qParam 1 (τ : ℂ) = t ^ 2 := by
    rw [Function.Periodic.qParam, ht_def, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hq : cexp (-(π * I / 24)) * Function.Periodic.qParam 24 (((τ : ℂ) + 1) / 2) *
      Function.Periodic.qParam 24 ((τ : ℂ) / 2) * Function.Periodic.qParam 24 (2 * (τ : ℂ)) =
      Function.Periodic.qParam 24 (τ : ℂ) ^ 3 := by
    simp only [Function.Periodic.qParam, ← Complex.exp_add, ← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  rw [eta_eq, eta_eq, eta_eq, eta_eq, q1, q2, q3, q4]
  have key := eulerProd_identity ht
  linear_combination (eulerProd (-t) * eulerProd t * eulerProd (t ^ 4)) * hq +
    Function.Periodic.qParam 24 (τ : ℂ) ^ 3 * key

theorem weber_prod (τ : ℍ) :
    GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.weberF τ * GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.weberF₁ τ * GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.weberF₂ τ =
      ((Real.sqrt 2 : ℝ) : ℂ) := by
  have h0 : ModularForm.eta τ ≠ 0 := ModularForm.eta_ne_zero τ.2
  have key := eta_relation τ
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.weberF, GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.weberF₁, GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.weberF₂]
  rw [div_mul_div_comm, div_mul_div_comm, div_eq_iff (by simp [h0])]
  linear_combination ((Real.sqrt 2 : ℝ) : ℂ) * key

end GlobalTheory.WeberProduct
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeberFunctionProductEqSqrtTwoStatement

section

@[expose] public section

open Complex

theorem _root_.GlobalTheory.T.weberFunction_product_eq_sqrt_two : ∀ τ : UpperHalfPlane, GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.weberF τ * GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.weberF₁ τ * GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.weberF₂ τ = ((Real.sqrt 2 : ℝ) : ℂ) := by
  first | exact @GlobalTheory.WeberProduct.weber_prod | exact GlobalTheory.WeberProduct.weber_prod | (intros; apply GlobalTheory.WeberProduct.weber_prod <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JacobiProductOfThetaWeber

section

@[expose] public section

open GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber

namespace GlobalTheory.ThetaWeberRoad

theorem jacobiProduct_of_thetaWeber {τ : UpperHalfPlane} (hTW : ThetaWeber τ)
    (hw : weberF τ * weberF₁ τ * weberF₂ τ = ((Real.sqrt 2 : ℝ) : ℂ)) : JacobiProduct τ := by
  obtain ⟨h1, h2, h3⟩ := hTW
  unfold JacobiProduct
  rw [h1, h2, h3]
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  linear_combination (ModularForm.eta (τ : ℂ)) ^ 3 *
    (weberF τ * weberF₁ τ * weberF₂ τ + ((Real.sqrt 2 : ℝ) : ℂ)) * hw +
    ModularForm.eta (τ : ℂ) ^ 3 * hs

theorem thetaWeberStatement_of (hTL : Formalism.L2.Th1.F.ThetaLine) (hSB : Formalism.L2.Th1.F.SgStarBasic)
    (hSA : Formalism.L2.Th1.F.SgStarAdd) : ThetaWeberStatement := by
  have hTW := GlobalTheory.T.thetaConstEqEtaWeberSq_of_tripleProduct GlobalTheory.T.jacobiTripleProduct_twoVariableTheta
  have hJ : ∀ τ : UpperHalfPlane, JacobiProduct τ := fun τ ↦
    jacobiProduct_of_thetaWeber (hTW τ) (GlobalTheory.T.weberFunction_product_eq_sqrt_two τ)
  have hH := GlobalTheory.T.halfPeriodDiffThetaFourth_of_sigmaStar_addition hSA (GlobalTheory.T.gaussianOddJacobiTheta_eq_deriv_mul_sgStar hTL hSB) (GlobalTheory.T.hasDerivAt_oddJacobiTheta_zero_eta_cube GlobalTheory.T.jacobiTripleProduct_twoVariableTheta) hJ
  intro τ
  exact ⟨hH τ, hJ τ, hTW τ, GlobalTheory.T.weberFunctionsRootsOfCubic_of_halfPeriodDiff τ (hH τ) (hJ τ) (hTW τ)⟩

end GlobalTheory.ThetaWeberRoad
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ThetaWeberStatement

section

@[expose] public section

namespace GlobalTheory.ThetaWeberObj

theorem thetaWeberStatement : GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.ThetaWeberStatement :=
  GlobalTheory.ThetaWeberRoad.thetaWeberStatement_of Formalism.L2.Th1.F.thetaLine Formalism.L2.Th1.F.sgStarBasic
    Formalism.L2.Th1.F.sgStarAdd

end GlobalTheory.ThetaWeberObj
end
end
