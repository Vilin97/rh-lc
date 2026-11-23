module

public import Development.AbelianVarietyTheory.Definitions.Jets.Imports
public import Development.AbelianVarietyTheory.Definitions.Jets.WigMap
public import Formalism.HermitianCurvature.FrameExists2
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LieListProducts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HypAndAdj
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsTypeOfIrreducibleStable
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameExpansionUwGroup
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameCompletion
import Mathlib.Algebra.Order.Star.Real
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PieriLoweringStepGlTensorDualStandardStatement
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameCompletion
import Mathlib.Tactic.Basify
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameExtension
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.HermExpHasDeriv

section

@[expose] public section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)
open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.QrD

noncomputable section

namespace GlobalTheory.TensorDualDifferential

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def hermLin {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (v w : Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ where
  toFun M := herm H (M *ᵥ v) w
  map_add' M N := by simp [herm, Matrix.add_mulVec, Matrix.mulVec_add]
  map_smul' c M := by simp [herm, Matrix.smul_mulVec, Matrix.mulVec_smul]

theorem herm_exp_hasDeriv {n : ℕ} (H X : Matrix (Fin n) (Fin n) ℂ) (v w : Fin n → ℂ) :
    HasDerivAt (fun t : ℝ => herm H (NormedSpace.exp ((t : ℂ) • X) *ᵥ v) w) (herm H (X *ᵥ v) w) 0 := by
  have h : HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) X 0 :=
    hasDerivAt_iff_tendsto_slope.2 (Formalism.REAL.tendsto_slope_exp_smul X)
  exact (((LinearMap.toContinuousLinearMap (hermLin H v w)).restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt
    (0 : ℝ) h

theorem herm_skew {n : ℕ} {H X : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ * H + H * X = 0) (v w : Fin n → ℂ) :
    herm H v (X *ᵥ w) = -herm H (X *ᵥ v) w := by
  have h : Xᴴ * H = -(H * X) := eq_neg_of_add_eq_zero_left hX
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h,
    Matrix.neg_mulVec, dotProduct_neg]

theorem dOp_tensor {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] {k r : ℕ}
    {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (V →L[ℂ] V)} {B : Fin k → (Fin (2 * r + k + 1) → ℂ)}
    {πt : Mx k r → ((PiLp 2 (fun _ : Fin k => V)) →L[ℂ] (PiLp 2 (fun _ : Fin k => V)))}
    (hπ : IsRepW k r z π) (hπt : IsRepW k r z πt) (hB : IsFrameOf k r [z] B)
    (h : ∀ h ∈ UWset k r z, ∀ y c, πt h y c = ∑ d, star (herm (Hpk k r) (h *ᵥ B d) (B c)) • π h (y d))
    {X : Mx k r} (hX : InLieW k r z X) (y : PiLp 2 (fun _ : Fin k => V)) (c : Fin k) :
    dOp πt X y c = dOp π X (y c) - ∑ d, hermLin (Hpk k r) (B c) (B d) X • y d := by
  have h1 := dOp_hasDeriv hπt.1 hπt.2 hX
  have h2 := dOp_hasDeriv hπ.1 hπ.2 hX
  have h3 : HasDerivAt (fun t : ℝ => πt (NormedSpace.exp ((t : ℂ) • X)) y c) (dOp πt X y c) 0 :=
    (((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin k => V) c).comp
      (ContinuousLinearMap.apply ℂ _ y)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  have h4 : ∀ d, HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)) (y d)) (dOp π X (y d)) 0 :=
    fun d => ((ContinuousLinearMap.apply ℂ V (y d)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
  have h5 := HasDerivAt.fun_sum (u := Finset.univ) fun d _ =>
    (herm_exp_hasDeriv (Hpk k r) X (B d) (B c)).star.fun_smul (h4 d)
  have h6 : (fun t : ℝ => πt (NormedSpace.exp ((t : ℂ) • X)) y c) = fun t : ℝ =>
      ∑ d, star (herm (Hpk k r) (NormedSpace.exp ((t : ℂ) • X) *ᵥ B d) (B c)) •
        π (NormedSpace.exp ((t : ℂ) • X)) (y d) := funext fun t => h _ (exp_uw hX t) y c
  rw [h6] at h3
  rw [h3.unique h5, Finset.sum_add_distrib]
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.one_mulVec, hπ.1.1, hB.2.1,
    Qx2.herm_star, herm_skew hX.1.1]
  simp [hermLin, sub_eq_add_neg]

theorem EB_tensor : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mx k r → (V →L[ℂ] V)) (B : Fin k → (Fin (2 * r + k + 1) → ℂ)) (πt : Mx k r → ((PiLp 2 (fun _ : Fin k => V)) →L[ℂ] (PiLp 2 (fun _ : Fin k => V)))), inWb k r z → 0 < Tz k r z → IsRepW k r z π → IsRepW k r z πt → IsFrameOf k r [z] B → (∀ h ∈ UWset k r z, ∀ y c, πt h y c = ∑ d, star (herm (Hpk k r) (h *ᵥ B d) (B c)) • π h (y d)) → ∀ a b y c, EB πt B a b y c = EB π B a b (y c) - if c = b then y a else 0 := by
  intro V _ _ _ k r z π B πt _ _ hπ hπt hB h a b y c
  have hl := frame_lie hB a b
  have e1 := dOp_tensor hπ hπt hB h hl.1 y c
  have e2 := dOp_tensor hπ hπt hB h hl.2 y c
  have e3 : ∑ d, hermLin (Hpk k r) (B c) (B d) (hpart1 (Hpk k r) (unitB (Hpk k r) B a b)) • y d +
      Complex.I • ∑ d, hermLin (Hpk k r) (B c) (B d) (hpart2 (Hpk k r) (unitB (Hpk k r) B a b)) • y d =
      if c = b then y a else 0 := by
    rw [Finset.smul_sum, ← Finset.sum_add_distrib]
    have e4 : ∀ d, hermLin (Hpk k r) (B c) (B d) (hpart1 (Hpk k r) (unitB (Hpk k r) B a b)) • y d +
        Complex.I • hermLin (Hpk k r) (B c) (B d) (hpart2 (Hpk k r) (unitB (Hpk k r) B a b)) • y d =
        if a = d then (if c = b then y d else 0) else 0 := by
      intro d
      rw [smul_smul, ← add_smul, ← smul_eq_mul Complex.I, ← map_smul, ← map_add (f := _), LieListProducts.hsum]
      have e5 : hermLin (Hpk k r) (B c) (B d) (unitB (Hpk k r) B a b) =
          herm (Hpk k r) (B c) (B b) * herm (Hpk k r) (B a) (B d) := by
        show herm (Hpk k r) (unitB (Hpk k r) B a b *ᵥ B c) (B d) = _
        rw [Qx8.unitB_mulVec]
        simp [herm, Matrix.mulVec_smul]
      rw [e5, hB.2.1, hB.2.1]
      split_ifs <;> simp
    simp [e4]
  have e6 : EB πt B a b y c = dOp πt (hpart1 (Hpk k r) (unitB (Hpk k r) B a b)) y c +
      Complex.I • dOp πt (hpart2 (Hpk k r) (unitB (Hpk k r) B a b)) y c := rfl
  have e7 : EB π B a b (y c) = dOp π (hpart1 (Hpk k r) (unitB (Hpk k r) B a b)) (y c) +
      Complex.I • dOp π (hpart2 (Hpk k r) (unitB (Hpk k r) B a b)) (y c) := rfl
  rw [e6, e7, e1, e2, ← e3, smul_sub]
  abel

end GlobalTheory.TensorDualDifferential
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormSqContractLe

section

@[expose] public section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.ContractLinear

open Formalism.FourierDecayAlt.P

theorem norm_sq_contract_le {V V₂ : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] {k : ℕ} (a : Fin k → (V₂ →L[ℂ] V))
    (ha : ∀ y, ∑ c, ‖a c y‖ ^ 2 = ‖y‖ ^ 2) (l : Fin k → ℂ) :
    ‖∑ c, l c • a c‖ ^ 2 ≤ ∑ c, ‖l c‖ ^ 2 := by
  have h0 : 0 ≤ ∑ c, ‖l c‖ ^ 2 := Finset.sum_nonneg fun c _ => by positivity
  have h1 : ‖∑ c, l c • a c‖ ≤ Real.sqrt (∑ c, ‖l c‖ ^ 2) := by
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun y => ?_
    have h2 : ‖(∑ c, l c • a c) y‖ ≤ ∑ c, ‖l c‖ * ‖a c y‖ := by
      rw [ContinuousLinearMap.sum_apply]
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [ContinuousLinearMap.smul_apply, norm_smul]
    have h3 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun c => ‖l c‖) (fun c => ‖a c y‖)
    rw [ha y] at h3
    refine h2.trans (le_of_sq_le_sq ?_ (by positivity))
    rw [mul_pow, Real.sq_sqrt h0]
    exact h3
  calc ‖∑ c, l c • a c‖ ^ 2 ≤ (Real.sqrt (∑ c, ‖l c‖ ^ 2)) ^ 2 := by gcongr
    _ = _ := Real.sq_sqrt h0

theorem wigMap_contract : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mx k r → (V →L[ℂ] V)) (B : Fin k → (Fin (2 * r + k + 1) → ℂ)) (V₂ : Type) [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] [FiniteDimensional ℂ V₂] (π₂ : Mx k r → (V₂ →L[ℂ] V₂)) (a : Fin k → (V₂ →L[ℂ] V)), inWb k r z → 0 < Tz k r z → IsFrameOf k r [z] B → (∀ y, ∑ c, ‖a c y‖ ^ 2 = ‖y‖ ^ 2) → (∀ h ∈ UWset k r z, ∀ y c, a c (π₂ h y) = ∑ d, star (herm (Hpk k r) (h *ᵥ B d) (B c)) • π h (a d y)) → GlobalTheory.WigSh.WigMap k r z π₂ π 1 (fun ω => ∑ c, herm (Hpk k r) ω (B c) • a c) ∧ ∀ c₀, (∑ c, herm (Hpk k r) (B c₀) (B c) • a c) = a c₀ := by
  intro V _ _ _ k r z π B V₂ _ _ _ π₂ a hz hT hB ha heq
  obtain ⟨hexp, hU⟩ := GlobalTheory.FrameExpansion.frame_expansion_uw_group k r z B hz hT hB
  refine ⟨⟨⟨k, fun c => ∑ j, MvPolynomial.C ((star (B c) ᵥ* Hpk k r) j) * MvPolynomial.X (Sum.inl j), a,
    fun c => ?_, fun ω => ?_⟩, fun h hh ω => ?_, fun t ω => ?_, fun ω hω hωz => ?_⟩, fun c₀ => ?_⟩
  · refine MvPolynomial.totalDegree_finsetSum_le fun j _ => ?_
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
  · refine Finset.sum_congr rfl fun c _ => ?_
    congr 1

    simp only [map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, Sum.elim_inl]
    rw [herm, Matrix.dotProduct_mulVec]
    rfl
  · obtain ⟨hW, hpres, -⟩ := hU h hh
    ext y
    have key : ∀ d, herm (Hpk k r) ω (B d) =
        ∑ c, star (herm (Hpk k r) (h *ᵥ B d) (B c)) * herm (Hpk k r) (h *ᵥ ω) (B c) := by
      intro d
      obtain ⟨h1, h2⟩ := hW (B d) (hB.1 d) (hB.2.2 d z (by simp))
      rw [← HermitianFormSums.herm_rsum, ← hexp _ h1 h2, hpres]

    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    heq h hh, map_sum, map_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [key d, Finset.sum_smul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [mul_comm]
  · simp only [Qx8.herm_smul_left', pow_one, Finset.smul_sum, smul_smul]
  · refine (norm_sq_contract_le a ha _).trans (le_of_eq ?_)
    have h1 := HermitianFormSums.herm_comb hB (fun c => herm (Hpk k r) ω (B c)) (fun c => herm (Hpk k r) ω (B c))
    rw [← hexp ω hω hωz] at h1
    rw [pow_one, h1, Complex.re_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  · simp [hB.2.1]

end GlobalTheory.ContractLinear
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorOpContinuousOn

section

@[expose] public section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P
open Formalism.REAL (qdet GlRel IsHW)

noncomputable section

namespace GlobalTheory.TensorDualStd

section General

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] {k : ℕ}

def tensorOp (C : Matrix (Fin k) (Fin k) ℂ) (A : V →L[ℂ] V) :
    PiLp 2 (fun _ : Fin k => V) →L[ℂ] PiLp 2 (fun _ : Fin k => V) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => WithLp.toLp 2 fun c => ∑ d, C c d • A (y d)
      map_add' := fun x y => by
        ext c
        simp [Finset.sum_add_distrib]
      map_smul' := fun a x => by
        ext c
        simp [Finset.smul_sum, smul_smul, mul_comm] }

theorem tensorOp_apply (C : Matrix (Fin k) (Fin k) ℂ) (A : V →L[ℂ] V) (y : PiLp 2 (fun _ : Fin k => V)) (c : Fin k) :
    tensorOp C A y c = ∑ d, C c d • A (y d) := rfl

theorem tensorOp_one : tensorOp (1 : Matrix (Fin k) (Fin k) ℂ) (1 : V →L[ℂ] V) = 1 := by
  ext y c
  simp [tensorOp_apply, Matrix.one_apply]

theorem tensorOp_mul (C D : Matrix (Fin k) (Fin k) ℂ) (A B : V →L[ℂ] V) :
    tensorOp (C * D) (A.comp B) = (tensorOp C A).comp (tensorOp D B) := by
  ext y c

  simp only [tensorOp_apply, ContinuousLinearMap.comp_apply, Matrix.mul_apply, Finset.sum_smul, map_sum,
  map_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

theorem tensorOp_norm {C : Matrix (Fin k) (Fin k) ℂ} (hC : ∀ d e, ∑ c, star (C c d) * C c e = if d = e then 1 else 0)
    {A : V →L[ℂ] V} (hA : ∀ v, ‖A v‖ = ‖v‖) (y : PiLp 2 (fun _ : Fin k => V)) : ‖tensorOp C A y‖ = ‖y‖ := by
  have h1 : inner ℂ (tensorOp C A y) (tensorOp C A y) = inner ℂ y y := by
    rw [PiLp.inner_apply, PiLp.inner_apply]
    calc ∑ c, inner ℂ (tensorOp C A y c) (tensorOp C A y c)
        = ∑ c, ∑ d, ∑ e, (star (C c d) * C c e) * inner ℂ (A (y d)) (A (y e)) := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [tensorOp_apply, sum_inner]
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [inner_sum]
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [inner_smul_left, inner_smul_right, mul_assoc]
          rfl
      _ = ∑ d, ∑ e, (∑ c, star (C c d) * C c e) * inner ℂ (A (y d)) (A (y e)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [Finset.sum_mul]
      _ = ∑ d, inner ℂ (y d) (y d) := by
          refine Finset.sum_congr rfl fun d _ => ?_
          simp only [hC, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
          rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, hA]
  rw [@norm_eq_sqrt_re_inner ℂ, h1, ← @norm_eq_sqrt_re_inner ℂ]

theorem tensorOp_continuousOn {X : Type} [TopologicalSpace X] {s : Set X} {C : X → Matrix (Fin k) (Fin k) ℂ}
    {A : X → (V →L[ℂ] V)} (hC : ∀ c d, Continuous fun x => C x c d) (hA : ContinuousOn A s) :
    ContinuousOn (fun x => tensorOp (C x) (A x)) s := by
  rw [continuousOn_clm_apply]
  intro y
  have h : ContinuousOn (fun x => fun c => ∑ d, C x c d • A x (y d)) s := by
    refine continuousOn_pi.2 fun c => continuousOn_finsetSum _ fun d _ => ?_
    exact (hC c d).continuousOn.smul (hA.clm_apply continuousOn_const)
  exact (PiLp.continuous_toLp 2 (fun _ : Fin k => V)).comp_continuousOn h

end General

variable {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}

theorem herm_inv {h : Mx k r} (hh : h ∈ UWset k r z) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (h *ᵥ v) (h *ᵥ w) = herm (Hpk k r) v w := by
  have e : hᴴ * Hpk k r * h = Hpk k r := hh.1
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e]

theorem inWb_mulVec {h : Mx k r} (hh : h ∈ UWset k r z) {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) :
    inWb k r (h *ᵥ v) := by
  rw [Qx8.inWb_iff] at hv ⊢
  intro c
  have hc := hh.2.1 c
  constructor
  · rw [← Qx8.coord_e (h *ᵥ v) c, ← hc.2, herm_inv hh, Qx8.coord_e]
    exact (hv c).1
  · rw [← Qx8.coord_es (h *ᵥ v) c, ← hc.1, herm_inv hh, Qx8.coord_es]
    exact (hv c).2

theorem expand {B : Fin k → Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z)
    (hB : IsFrameOf k r [z] B) {h : Mx k r} (hh : h ∈ UWset k r z) (d : Fin k) :
    h *ᵥ B d = ∑ c, herm (Hpk k r) (h *ᵥ B d) (B c) • B c := by
  refine HermitianFormSums.complete0 hz (HermitianFormSums.hzz hT) hB (inWb_mulVec hh (hB.1 d)) ?_
  have h1 := herm_inv hh (B d) z
  rw [hh.2.2] at h1
  rw [h1]
  exact hB.2.2 d z (by simp)

def dualMat (k r : ℕ) (B : Fin k → Fin (2 * r + k + 1) → ℂ) (h : Mx k r) : Matrix (Fin k) (Fin k) ℂ :=
  fun c d => star (herm (Hpk k r) (h *ᵥ B d) (B c))

end GlobalTheory.TensorDualStd


open GlobalTheory.TensorDualStd in
theorem GlobalTheory.tensor_dual_standard : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mx k r → (V →L[ℂ] V)) (B : Fin k → (Fin (2 * r + k + 1) → ℂ)), inWb k r z → 0 < Tz k r z → IsRepW k r z π → (∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖) → IsFrameOf k r [z] B → ∃ πt : Mx k r → ((PiLp 2 (fun _ : Fin k => V)) →L[ℂ] (PiLp 2 (fun _ : Fin k => V))), IsRepW k r z πt ∧ (∀ h ∈ UWset k r z, ∀ v, ‖πt h v‖ = ‖v‖) ∧ (∀ h ∈ UWset k r z, ∀ y c, πt h y c = ∑ d, star (herm (Hpk k r) (h *ᵥ B d) (B c)) • π h (y d)) := by
  intro V _ _ _ k r z π B hz hT hπ hn hB
  refine ⟨fun h => tensorOp (dualMat k r B h) (π h), ⟨⟨?_, ?_⟩, ?_⟩, ?_, fun h _ y c => rfl⟩
  · have h1 : dualMat k r B 1 = 1 := by
      ext c d
      simp only [dualMat, Matrix.one_mulVec, hB.2.1, Matrix.one_apply]
      by_cases h : c = d
      · simp [h]
      · simp [h, Ne.symm h]
    simp only [h1, hπ.1.1]
    exact tensorOp_one
  · intro a ha b hb
    have h1 : dualMat k r B (a * b) = dualMat k r B a * dualMat k r B b := by
      ext c d
      simp only [dualMat, Matrix.mul_apply]
      rw [← Matrix.mulVec_mulVec]
      conv_lhs => rw [expand hz hT hB hb d, Matrix.mulVec_sum]
      simp only [Matrix.mulVec_smul]
      rw [HermitianFormSums.herm_lsum, star_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [star_mul]
    simp only [h1, hπ.1.2 a ha b hb]
    exact tensorOp_mul _ _ _ _
  · refine tensorOp_continuousOn (fun c d => ?_) hπ.2
    unfold dualMat herm
    fun_prop
  · intro h hh v
    refine tensorOp_norm (fun d e => ?_) (hn h hh) v
    simp only [dualMat, star_star]
    rw [← HermitianFormSums.herm_comb hB, ← expand hz hT hB hh, ← expand hz hT hB hh, herm_inv hh, hB.2.1]

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.WignerStepLoweringUnitaryComplement

section

@[expose] public section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.WignerStepLower

open Formalism.FourierDecayAlt.P

theorem comp_adjoint_apply {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    {k : ℕ} (S : Submodule ℂ (PiLp 2 (fun _ : Fin k => V))) (c : Fin k) (a : S →L[ℂ] V)
    (ha : ∀ y : S, a y = (y : PiLp 2 (fun _ : Fin k => V)) c) (v : V) :
    a (ContinuousLinearMap.adjoint a v) = S.starProjection (PiLp.single 2 c v) c := by
  have h : ContinuousLinearMap.adjoint a v = S.orthogonalProjection (PiLp.single 2 c v) := by
    refine ext_inner_left ℂ fun y => ?_
    rw [ContinuousLinearMap.adjoint_inner_right, Submodule.inner_orthogonalProjection_eq_of_mem_left, ha,
      PiLp.inner_apply, Finset.sum_eq_single c]
    · simp
    · intro b _ hb
      simp [PiLp.single_apply, Pi.single_apply, hb]
    · simp
  rw [h, ha]
  rfl

theorem wigner_step_lowering : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n r : ℕ) (z : (Fin (2 * r + (n + 1) + 1) → ℂ)) (π : Mx (n + 1) r → (V →L[ℂ] V)) (u : ℕ → ℝ) (β : ℂ) (L : Fin (n + 1) → ℤ) (B : Fin (n + 1) → (Fin (2 * r + (n + 1) + 1) → ℂ)) (l : Fin (n + 1)), inWb (n + 1) r z → 0 < Tz (n + 1) r z → IsType (n + 1) r z π u → StrictAnti L → (∀ j : Fin (n + 1), (u ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L j : ℂ)) → IsFrameOf (n + 1) r [z] B → (∀ j, L j ≠ L l - 1) → ∃ (V₂ : Type) (_ : NormedAddCommGroup V₂) (_ : InnerProductSpace ℂ V₂) (_ : FiniteDimensional ℂ V₂) (π₂ : Mx (n + 1) r → (V₂ →L[ℂ] V₂)) (A : (Fin (2 * r + (n + 1) + 1) → ℂ) → (V₂ →L[ℂ] V)), IsType (n + 1) r z π₂ (Function.update u ((l : ℕ) + 1) (u ((l : ℕ) + 1) - 1)) ∧ GlobalTheory.WigSh.WigMap (n + 1) r z π₂ π 1 A ∧ ∀ (M : Fin n → ℤ) (v : V), v ∈ CapSp (subA (EB π B)) (shf β M) → A (B (Fin.last n)) (ContinuousLinearMap.adjoint (A (B (Fin.last n))) v) = ((GlobalTheory.WigSh.wM L M l : ℝ) : ℂ) • v := by
  intro V _ _ _ n r z π u β L B l hz hT hty hL hu hB hl
  obtain ⟨hH, hadj⟩ := GlobalTheory.TypeGlModule.hyp_and_adj V n r z π u β L B hz hT hty hL hu hB
  have hR : IsRepW (n + 1) r z π := ⟨hty.2.1, hty.2.2.1⟩
  obtain ⟨πt, hRt, hnt, hft⟩ := GlobalTheory.tensor_dual_standard V (n + 1) r z π B hz hT hR hty.2.2.2.1 hB
  have hE := GlobalTheory.TensorDualDifferential.EB_tensor V (n + 1) r z π B πt hz hT hR hRt hB hft
  obtain ⟨S, hS, hS0, hirr, hcap, hw⟩ := GlobalTheory.T.pieri_lowering_step_gl_tensor_dual_standard V n (EB π B) (EB πt B) β L l hH hadj hE hl
  obtain ⟨π₂, hty₂, hπ₂⟩ := GlobalTheory.isType_of_irreducible_stable _ (n + 1) r z πt B S
    (Function.update u ((l : ℕ) + 1) (u ((l : ℕ) + 1) - 1)) hz hT hRt hnt hB hS hS0 hirr (by
      intro w y hy
      rw [mem_CapSp.1 (hcap hy) w, FrameExtension.prod_Icc_fin]
      congr 1
      unfold cpol shf
      refine Finset.prod_congr rfl (fun j _ => ?_)
      have h1 := hu j
      by_cases hj : j = l
      · subst hj
        rw [Function.update_self, Function.update_self]
        push_cast at h1 ⊢
        linear_combination -h1
      · have hj' : (j : ℕ) + 1 ≠ (l : ℕ) + 1 := fun h => hj (Fin.ext (by omega))
        rw [Function.update_of_ne hj, Function.update_of_ne hj']
        linear_combination -h1)
  let a : Fin (n + 1) → (S →L[ℂ] V) := fun c =>
    (PiLp.proj 2 (fun _ : Fin (n + 1) => V) c).comp S.subtypeL
  have ha : ∀ c (y : S), a c y = (y : PiLp 2 (fun _ : Fin (n + 1) => V)) c := fun _ _ => rfl
  obtain ⟨hW, hA⟩ := GlobalTheory.ContractLinear.wigMap_contract V (n + 1) r z π B S π₂ a hz hT hB
    (fun y => by
      simp only [ha]
      rw [← PiLp.norm_sq_eq_of_L2]
      rfl)
    (fun h hh y c => by
      simp only [ha]
      rw [hπ₂ h hh y, hft h hh])
  refine ⟨S, inferInstance, inferInstance, inferInstance, π₂, _, hty₂, hW, fun M v hv => ?_⟩
  simp only [hA]
  rw [comp_adjoint_apply S (Fin.last n) (a (Fin.last n)) (ha _) v]
  exact hw M v hv

end GlobalTheory.WignerStepLower
end
end
