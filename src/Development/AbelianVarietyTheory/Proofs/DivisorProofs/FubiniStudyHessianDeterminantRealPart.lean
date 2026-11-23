module

public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.L2DbarEstimates.LeviForms.EventuallyDifferentiableAtOfContDiffAt
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexHessianLogOneAddNormSq

section

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FubiniStudyHessian

open ReciprocityTheory.L2DbarEstimates
open scoped ComplexConjugate

variable {n : ℕ}

theorem differentiableAt_coord (i : Fin n) (x : V n) : DifferentiableAt ℂ (fun w : V n => w i) x :=
  (EuclideanSpace.proj (𝕜 := ℂ) i).differentiableAt

theorem wd_coord (j i : Fin n) (x : V n) : wd n j (fun w : V n => w i) x = if j = i then 1 else 0 := by
  rw [wd_of_differentiableAt (differentiableAt_coord i x)]
  have h : fderiv ℂ (fun w : V n => w i) x = EuclideanSpace.proj (𝕜 := ℂ) i :=
    (EuclideanSpace.proj (𝕜 := ℂ) i).fderiv
  rw [h]
  by_cases hji : j = i
  · subst hji; simp [bas]
  · simp [bas, hji, Ne.symm hji]

theorem normSq_eq_sum : (fun w : V n => ((‖w‖ ^ 2 : ℝ) : ℂ)) = fun w => ∑ i, w i * conj (w i) := by
  funext w
  rw [EuclideanSpace.norm_sq_eq]
  simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem differentiableAt_normSq (x : V n) : DifferentiableAt ℝ (fun w : V n => ‖w‖ ^ 2) x :=
  ((contDiff_norm_sq ℂ (n := 1)).differentiable one_ne_zero) x

theorem wd_normSq (j : Fin n) (x : V n) :
    wd n j (fun w : V n => ((‖w‖ ^ 2 : ℝ) : ℂ)) x = conj (x j) := by
  have hd : ∀ i, DifferentiableAt ℝ (fun w : V n => w i) x := fun i =>
    (differentiableAt_coord i x).restrictScalars ℝ
  rw [normSq_eq_sum, wd_sum Finset.univ (f := fun i (w : V n) => w i * conj (w i))
    (fun i _ => (hd i).mul (differentiableAt_conj (hd i)))]
  have h : ∀ i, wd n j (fun w : V n => w i * conj (w i)) x = if j = i then conj (x i) else 0 := fun i => by
    rw [wd_mul (hd i) (differentiableAt_conj (hd i)), wd_conj (hd i),
      wdb_of_differentiableAt (differentiableAt_coord i x), wd_coord]
    simp
  simp [h]

theorem wdb_normSq (j : Fin n) (x : V n) :
    wdb n j (fun w : V n => ((‖w‖ ^ 2 : ℝ) : ℂ)) x = x j := by
  rw [wdb_ofReal (differentiableAt_normSq x), wd_normSq, Complex.conj_conj]

theorem wdb_log (l : Fin n) :
    wdb n l (fun w : V n => (Real.log (1 + ‖w‖ ^ 2) : ℂ)) =
      fun w => (((1 + ‖w‖ ^ 2)⁻¹ : ℝ) : ℂ) * w l := by
  funext x
  have hpos : (1 + ‖x‖ ^ 2 : ℝ) ≠ 0 := by positivity
  have hk : HasDerivAt (fun t : ℝ => Real.log (1 + t)) (1 / (1 + ‖x‖ ^ 2)) (‖x‖ ^ 2) :=
    ((hasDerivAt_id' (‖x‖ ^ 2)).const_add 1).log hpos
  rw [wdb_ofReal_comp (k := fun t : ℝ => Real.log (1 + t)) (v := fun w : V n => ‖w‖ ^ 2)
    hk.differentiableAt (differentiableAt_normSq x), hk.deriv, wdb_normSq, one_div]

theorem cHess_log_one_add_normSq : ∀ (n : ℕ) (v : ReciprocityTheory.L2DbarEstimates.V n), ReciprocityTheory.L2DbarEstimates.cHess n (fun w => (Real.log (1 + ‖w‖ ^ 2) : ℂ)) v = Matrix.of (fun j l => (if j = l then 1 else 0) / (1 + (‖v‖ : ℂ) ^ 2) - (starRingEnd ℂ (v j) * v l) / (1 + (‖v‖ : ℂ) ^ 2) ^ 2) := by
  intro n v
  ext j l
  have hpos : (1 + ‖v‖ ^ 2 : ℝ) ≠ 0 := by positivity
  have hk : HasDerivAt (fun t : ℝ => (1 + t)⁻¹) (-1 / (1 + ‖v‖ ^ 2) ^ 2) (‖v‖ ^ 2) :=
    ((hasDerivAt_id' (‖v‖ ^ 2)).const_add 1).inv hpos
  have hd : DifferentiableAt ℝ (fun w : V n => (1 + ‖w‖ ^ 2)⁻¹) v :=
    ((differentiableAt_normSq v).const_add 1).inv hpos
  simp only [cHess, Matrix.of_apply]
  rw [wdb_log, wd_mul (differentiableAt_ofReal hd) ((differentiableAt_coord l v).restrictScalars ℝ),
    wd_ofReal_comp (k := fun t : ℝ => (1 + t)⁻¹) (v := fun w : V n => ‖w‖ ^ 2)
      hk.differentiableAt (differentiableAt_normSq v), hk.deriv, wd_normSq, wd_coord]
  push_cast
  ring

end GlobalTheory.FubiniStudyHessian
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexHessianLogOneAddNormSqStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

theorem _root_.GlobalTheory.T.complexHessian_log_one_add_normSq : ∀ (n : ℕ) (v : ReciprocityTheory.L2DbarEstimates.V n), ReciprocityTheory.L2DbarEstimates.cHess n (fun w => (Real.log (1 + ‖w‖ ^ 2) : ℂ)) v = Matrix.of (fun j l => (if j = l then 1 else 0) / (1 + (‖v‖ : ℂ) ^ 2) - (starRingEnd ℂ (v j) * v l) / (1 + (‖v‖ : ℂ) ^ 2) ^ 2) := by
  first | exact @GlobalTheory.FubiniStudyHessian.cHess_log_one_add_normSq | exact GlobalTheory.FubiniStudyHessian.cHess_log_one_add_normSq | (intros; apply GlobalTheory.FubiniStudyHessian.cHess_log_one_add_normSq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyHessianDeterminantRealPart

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.FSDet

theorem sum_conj_mul_self {n : ℕ} (v : ReciprocityTheory.L2DbarEstimates.V n) :
    (∑ j, starRingEnd ℂ (v j) * v j) = (‖v‖ : ℂ) ^ 2 := by
  have h := EuclideanSpace.norm_sq_eq v
  have h2 : ((‖v‖ : ℂ)) ^ 2 = ((‖v‖ ^ 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [h2, h]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.conj_mul']

theorem det_one_add_vecMulVec' {m : Type} [Fintype m] [DecidableEq m] (a b : m → ℂ) :
    (1 + Matrix.vecMulVec a b).det = 1 + a ⬝ᵥ b := by
  have := Matrix.det_one_add_replicateCol_mul_replicateRow (ι := Unit) a b
  rw [Matrix.vecMulVec_eq (ι := Unit), this, dotProduct_comm]

end GlobalTheory.FSDet

namespace GlobalTheory.FSDet

theorem det_fubiniStudy_hess :
    ∀ (n : ℕ) (v : ReciprocityTheory.L2DbarEstimates.V n), (ReciprocityTheory.L2DbarEstimates.cHess n (fun w => (Real.log (1 + ‖w‖ ^ 2) : ℂ)) v).det.re = ((1 + ‖v‖ ^ 2) ^ (n + 1))⁻¹ := by
  intro n v
  rw [GlobalTheory.T.complexHessian_log_one_add_normSq n v]
  set t : ℂ := 1 + (‖v‖ : ℂ) ^ 2 with ht
  have htr : t = ((1 + ‖v‖ ^ 2 : ℝ) : ℂ) := by rw [ht]; push_cast; rfl
  have ht0 : t ≠ 0 := by
    rw [htr]; exact_mod_cast (by positivity : (1 + ‖v‖ ^ 2 : ℝ) ≠ 0)
  have hM : (Matrix.of (fun j l => (if j = l then (1:ℂ) else 0) / t - (starRingEnd ℂ (v j) * v l) / t ^ 2) : Matrix (Fin n) (Fin n) ℂ)
      = t⁻¹ • (1 + Matrix.vecMulVec (fun j => -(starRingEnd ℂ (v j)) / t) (fun l => v l)) := by
    ext j l
    simp only [Matrix.of_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply, smul_eq_mul]
    field_simp
    ring
  rw [hM, Matrix.det_smul, det_one_add_vecMulVec', Fintype.card_fin]
  have hdot : (fun j => -(starRingEnd ℂ (v j)) / t) ⬝ᵥ (fun l => v l) = -((‖v‖ : ℂ) ^ 2) / t := by
    rw [← sum_conj_mul_self v, dotProduct, neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hval : t⁻¹ ^ n * (1 + -((‖v‖ : ℂ) ^ 2) / t) = (((1 + ‖v‖ ^ 2 : ℝ) ^ (n + 1))⁻¹ : ℝ) := by
    have h1 : (1 + -((‖v‖ : ℂ) ^ 2) / t) = t⁻¹ := by
      field_simp
      rw [ht]; ring
    rw [h1, ← pow_succ, inv_pow, htr]
    push_cast
    rfl
  rw [hdot, hval, Complex.ofReal_re]

end GlobalTheory.FSDet
end
end
