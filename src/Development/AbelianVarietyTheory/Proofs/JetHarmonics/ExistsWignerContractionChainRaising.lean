module

public import Development.AbelianVarietyTheory.Definitions.Jets.Imports
public import Development.AbelianVarietyTheory.Definitions.Jets.WigMap
public import Formalism.HermitianCurvature.FrameExists2
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AdjointMemCapSpSubA
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WigMapComp
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WigMapZeroOfContraction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsTensorStandardRep
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HypAndAdj
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsTypeOfIrreducibleStable
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameExpansionUwGroup
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
import Mathlib.Algebra.Order.Star.Real
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PieriRaisingSubmoduleGlSuccStatement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameExtension
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.CoefHasDerivAt

section

@[expose] public section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.QrD

namespace GlobalTheory.TensorStd

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable def coefL {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (v w : Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun g => herm H (g *ᵥ v) w
      map_add' := fun g h => by simp [herm, Matrix.add_mulVec, Matrix.mulVec_add, dotProduct_add]
      map_smul' := fun c g => by simp [herm, Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul] }

theorem coefL_apply {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (v w : Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) :
    coefL H v w g = herm H (g *ᵥ v) w := rfl

theorem coef_hasDerivAt {k r : ℕ} (X : Mx k r) (v w : Fin (2 * r + k + 1) → ℂ) :
    HasDerivAt (fun t : ℝ => herm (Hpk k r) (NormedSpace.exp ((t : ℂ) • X) *ᵥ v) w)
      (herm (Hpk k r) (X *ᵥ v) w) 0 := by
  have h1 := B5.curve_hasDerivAt (1 : Mx k r) X 0
  simp only [Matrix.one_mul, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero] at h1
  exact ((coefL (Hpk k r) v w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1

theorem hpart_sum {n : ℕ} (H Z : Matrix (Fin n) (Fin n) ℂ) :
    hpart1 H Z + Complex.I • hpart2 H Z = Z := by
  unfold hpart1 hpart2
  rw [smul_smul]
  have : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by field_simp
  rw [this, ← smul_add]
  have : Z - H⁻¹ * Zᴴ * H + (Z + H⁻¹ * Zᴴ * H) = (2 : ℂ) • Z := by rw [two_smul]; abel
  rw [this, smul_smul]; norm_num

theorem dOp_tensor {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] {k r : ℕ}
    {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (V →L[ℂ] V)} {B : Fin k → (Fin (2 * r + k + 1) → ℂ)}
    {πt : Mx k r → ((PiLp 2 (fun _ : Fin k => V)) →L[ℂ] (PiLp 2 (fun _ : Fin k => V)))}
    (hπ : IsRepW k r z π) (hπt : IsRepW k r z πt) (hB : IsFrameOf k r [z] B)
    (hf : ∀ h ∈ UWset k r z, ∀ y c, πt h y c = ∑ d, herm (Hpk k r) (h *ᵥ B d) (B c) • π h (y d))
    {X : Mx k r} (hX : InLieW k r z X) (y : PiLp 2 (fun _ : Fin k => V)) (c : Fin k) :
    dOp πt X y c = dOp π X (y c) + ∑ d, herm (Hpk k r) (X *ᵥ B d) (B c) • y d := by
  have h1 := dOp_hasDeriv hπt.1 hπt.2 hX
  have h2 := dOp_hasDeriv hπ.1 hπ.2 hX
  have h3 : HasDerivAt (fun t : ℝ => πt (NormedSpace.exp ((t : ℂ) • X)) y c) (dOp πt X y c) 0 :=
    (((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin k => V) c).comp
      (ContinuousLinearMap.apply ℂ _ y)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  have h4 : ∀ d, HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)) (y d)) (dOp π X (y d)) 0 := fun d =>
    ((ContinuousLinearMap.apply ℂ V (y d)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
  have h5 := HasDerivAt.fun_sum (u := Finset.univ) fun d _ => (coef_hasDerivAt X (B d) (B c)).fun_smul (h4 d)
  have h6 : (fun t : ℝ => πt (NormedSpace.exp ((t : ℂ) • X)) y c) = fun t : ℝ => ∑ d,
      herm (Hpk k r) (NormedSpace.exp ((t : ℂ) • X) *ᵥ B d) (B c) • π (NormedSpace.exp ((t : ℂ) • X)) (y d) :=
    funext fun t => hf _ (exp_uw hX t) y c
  rw [h6] at h3
  rw [h3.unique h5]
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.one_mulVec, hπ.1.1, hB.2.1,
    Finset.sum_add_distrib, one_apply_eq_self]
  simp

theorem EB_tensor_std : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mx k r → (V →L[ℂ] V)) (B : Fin k → (Fin (2 * r + k + 1) → ℂ)) (πt : Mx k r → ((PiLp 2 (fun _ : Fin k => V)) →L[ℂ] (PiLp 2 (fun _ : Fin k => V)))), inWb k r z → 0 < Tz k r z → IsRepW k r z π → IsRepW k r z πt → IsFrameOf k r [z] B → (∀ h ∈ UWset k r z, ∀ y c, πt h y c = ∑ d, herm (Hpk k r) (h *ᵥ B d) (B c) • π h (y d)) → ∀ a b y c, EB πt B a b y c = EB π B a b (y c) + if c = a then y b else 0 := by
  intro V _ _ _ k r z π B πt _ _ hπ hπt hB hf a b y c
  obtain ⟨l1, l2⟩ := frame_lie hB a b
  have e1 := dOp_tensor hπ hπt hB hf l1 y c
  have e2 := dOp_tensor hπ hπt hB hf l2 y c
  have e3 : ∀ d, herm (Hpk k r) (hpart1 (Hpk k r) (unitB (Hpk k r) B a b) *ᵥ B d) (B c) +
      Complex.I * herm (Hpk k r) (hpart2 (Hpk k r) (unitB (Hpk k r) B a b) *ᵥ B d) (B c) =
      if d = b then (if c = a then 1 else 0) else 0 := by
    intro d
    rw [← coefL_apply, ← coefL_apply, ← smul_eq_mul Complex.I, ← map_smul, ← map_add (f := _), hpart_sum, coefL_apply,
      Qx8.unitB_mulVec, hB.2.1]
    have := hB.2.1 a c
    by_cases hd : d = b
    · subst hd
      have e : herm (Hpk k r) ((1 : ℂ) • B a) (B c) = herm (Hpk k r) (B a) (B c) := by rw [one_smul]
      rw [if_pos rfl, if_pos rfl, e, this]
      simp only [eq_comm]
    · simp [hd, herm]
  show dOp πt _ y c + Complex.I • dOp πt _ y c = (dOp π _ (y c) + Complex.I • dOp π _ (y c)) + _
  rw [e1, e2, smul_add, Finset.smul_sum, add_add_add_comm, ← Finset.sum_add_distrib]
  congr 1
  simp only [smul_smul, ← add_smul, e3]
  by_cases hc : c = a <;> simp [hc]

end GlobalTheory.TensorStd
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.OpNormSumSmulSqLe

section

@[expose] public section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.WigSh.ContrPlus

theorem herm_sum_smul_left {ι κ : Type} [Fintype ι] [Fintype κ] (H : Matrix ι ι ℂ) (l : κ → ℂ) (B : κ → ι → ℂ)
    (w : ι → ℂ) : herm H (∑ c, l c • B c) w = ∑ c, l c * herm H (B c) w := by
  unfold herm
  rw [Matrix.mulVec_sum, dotProduct_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem herm_conj {ι : Type} [Fintype ι] (H : Matrix ι ι ℂ) (hH : Hᴴ = H) (v w : ι → ℂ) :
    herm H w v = star (herm H v w) := by
  unfold herm
  rw [← star_dotProduct_star, star_star, Matrix.star_mulVec, hH, Matrix.dotProduct_mulVec]

theorem herm_real_smul_right {ι : Type} [Fintype ι] (H : Matrix ι ι ℂ) (t : ℝ) (v w : ι → ℂ) :
    herm H v ((t : ℂ) • w) = (t : ℂ) * herm H v w := by
  unfold herm
  rw [star_smul, smul_dotProduct, smul_eq_mul]
  simp

theorem opNorm_sum_smul_sq_le {V V₂ κ : Type} [Fintype κ] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] (a : κ → (V₂ →L[ℂ] V)) (l : κ → ℂ)
    (ha : ∀ y, ∑ c, ‖a c y‖ ^ 2 = ‖y‖ ^ 2) : ‖∑ c, l c • a c‖ ^ 2 ≤ ∑ c, ‖l c‖ ^ 2 := by
  have hS : 0 ≤ ∑ c, ‖l c‖ ^ 2 := Finset.sum_nonneg fun c _ => sq_nonneg _
  have h1 : ‖∑ c, l c • a c‖ ≤ Real.sqrt (∑ c, ‖l c‖ ^ 2) := by
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun y => ?_
    have h2 : ‖(∑ c, l c • a c) y‖ ≤ ∑ c, ‖l c‖ * ‖a c y‖ := by
      rw [ContinuousLinearMap.sum_apply]
      refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun c _ => ?_))
      rw [ContinuousLinearMap.smul_apply, norm_smul]
    have h3 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun c => ‖l c‖) (fun c => ‖a c y‖)
    rw [ha y] at h3
    refine h2.trans ?_
    have h4 := Real.le_sqrt_of_sq_le h3
    rwa [Real.sqrt_mul hS, Real.sqrt_sq (norm_nonneg y)] at h4
  calc _ ≤ Real.sqrt (∑ c, ‖l c‖ ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = _ := Real.sq_sqrt hS

theorem contraction_wigMap :
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mx k r → (V →L[ℂ] V)) (B : Fin k → (Fin (2 * r + k + 1) → ℂ)) (V₂ : Type) [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] [FiniteDimensional ℂ V₂] (π₂ : Mx k r → (V₂ →L[ℂ] V₂)) (a : Fin k → (V₂ →L[ℂ] V)), inWb k r z → 0 < Tz k r z → IsFrameOf k r [z] B → (∀ y, ∑ c, ‖a c y‖ ^ 2 = ‖y‖ ^ 2) → (∀ h ∈ UWset k r z, ∀ y c, a c (π₂ h y) = ∑ d, herm (Hpk k r) (h *ᵥ B d) (B c) • π h (a d y)) → GlobalTheory.WigSh.WigMap k r z π₂ π 1 (fun ω => ∑ c, herm (Hpk k r) (B c) ω • a c) ∧ ∀ c₀, (∑ c, herm (Hpk k r) (B c) (B c₀) • a c) = a c₀ := by
  intro V _ _ _ k r z π B V₂ _ _ _ π₂ a hz hT hB ha hequi
  obtain ⟨hcomp, hU⟩ := GlobalTheory.FrameExpansion.frame_expansion_uw_group k r z B hz hT hB
  have hH : (Hpk k r)ᴴ = Hpk k r := (hermitian_pos_facts_hold k r).1
  refine ⟨⟨⟨k, fun c => ∑ j, MvPolynomial.C ((Hpk k r *ᵥ B c) j) * MvPolynomial.X (Sum.inr j), a, ?_, ?_⟩,
    ?_, ?_, ?_⟩, ?_⟩
  · intro c
    refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
  · intro ω
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    simp [herm, dotProduct, mul_comm]
  · intro h hh ω
    obtain ⟨hW, hiso, -⟩ := hU h hh
    ext y
    have key : ∀ d, ∑ c, herm (Hpk k r) (h *ᵥ B d) (B c) * herm (Hpk k r) (B c) (h *ᵥ ω)
        = herm (Hpk k r) (B d) ω := by
      intro d
      obtain ⟨h1, h2⟩ := hW (B d) (hB.1 d) (hB.2.2 d z (by simp))
      rw [← herm_sum_smul_left, ← hcomp _ h1 h2, hiso]

    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    map_sum, map_smul, hequi h hh, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Finset.sum_smul, ← key d]
    simp only [mul_comm]
  · intro t ω
    simp only [herm_real_smul_right, pow_one, Finset.smul_sum, smul_smul]
  · intro ω h1 h2
    rw [pow_one]
    refine (opNorm_sum_smul_sq_le a _ ha).trans (le_of_eq ?_)
    have h3 : herm (Hpk k r) ω ω = ∑ c, herm (Hpk k r) ω (B c) * herm (Hpk k r) (B c) ω := by
      rw [← herm_sum_smul_left, ← hcomp _ h1 h2]
    rw [h3, Complex.re_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [herm_conj _ hH (B c) ω, Complex.star_def, Complex.conj_mul']
    norm_cast
  · intro c₀
    simp [hB.2.1]

end GlobalTheory.WigSh.ContrPlus
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.WignerStepRaisingUnitaryComplement

section

@[expose] public section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.WigSh

theorem adjoint_eval_subspace {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    {k : ℕ} (S : Submodule ℂ (PiLp 2 (fun _ : Fin k => V))) (c : Fin k) (v : V) :
    ContinuousLinearMap.adjoint
        ((PiLp.proj 2 (𝕜 := ℂ) (fun _ : Fin k => V) c).comp S.subtypeL) v
      = S.orthogonalProjectionOnto (PiLp.single 2 c v) := by
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right, Submodule.inner_orthogonalProjection_eq_of_mem_left,
    PiLp.inner_apply, Finset.sum_eq_single c]
  · simp
  · intro b _ hb
    simp [PiLp.single_eq_of_ne, hb]
  · simp

theorem wigner_step_raise : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n r : ℕ) (z : (Fin (2 * r + (n + 1) + 1) → ℂ)) (π : Mx (n + 1) r → (V →L[ℂ] V)) (u : ℕ → ℝ) (β : ℂ) (L : Fin (n + 1) → ℤ) (B : Fin (n + 1) → (Fin (2 * r + (n + 1) + 1) → ℂ)) (l : Fin (n + 1)), inWb (n + 1) r z → 0 < Tz (n + 1) r z → IsType (n + 1) r z π u → StrictAnti L → (∀ j : Fin (n + 1), (u ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L j : ℂ)) → IsFrameOf (n + 1) r [z] B → (∀ j, L j ≠ L l + 1) → ∃ (V₂ : Type) (_ : NormedAddCommGroup V₂) (_ : InnerProductSpace ℂ V₂) (_ : FiniteDimensional ℂ V₂) (π₂ : Mx (n + 1) r → (V₂ →L[ℂ] V₂)) (A : (Fin (2 * r + (n + 1) + 1) → ℂ) → (V₂ →L[ℂ] V)), IsType (n + 1) r z π₂ (Function.update u ((l : ℕ) + 1) (u ((l : ℕ) + 1) + 1)) ∧ GlobalTheory.WigSh.WigMap (n + 1) r z π₂ π 1 A ∧ ∀ (M : Fin n → ℤ) (v : V), v ∈ CapSp (subA (EB π B)) (shf β M) → A (B (Fin.last n)) (ContinuousLinearMap.adjoint (A (B (Fin.last n))) v) = ((GlobalTheory.WigSh.wP L M l : ℝ) : ℂ) • v := by
  intro V _ _ _ n r z π u β L B l hz hT hπ hL hu hB hl
  obtain ⟨hH, hadj⟩ := GlobalTheory.TypeGlModule.hyp_and_adj V n r z π u β L B hz hT hπ hL hu hB
  have hrep : IsRepW (n + 1) r z π := ⟨hπ.2.1, hπ.2.2.1⟩
  obtain ⟨πt, ht1, ht2, ht3⟩ :=
    GlobalTheory.exists_tensor_standard_rep V (n + 1) r z π B hz hT hrep hπ.2.2.2.1 hB
  have hE := GlobalTheory.TensorStd.EB_tensor_std V (n + 1) r z π B πt hz hT hrep ht1 hB ht3
  obtain ⟨S, hS1, hS2, hS3, hS4, hS5⟩ := GlobalTheory.T.pieri_raising_submodule_glSucc V n (EB π B) (EB πt B) β L l hH hadj hE hl
  have hq : ∀ (w : ℂ), ∀ y ∈ S, qdet (EB πt B) w y = (∏ i ∈ Finset.Icc 1 (n + 1),
      (w - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 +
        ((Function.update u ((l : ℕ) + 1) (u ((l : ℕ) + 1) + 1) i : ℝ) : ℂ))) • y := by
    intro w y hy
    have h1 := hS4 hy
    unfold CapSp at h1
    rw [Submodule.mem_iInf] at h1
    have h2 := h1 w
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, LinearMap.smul_apply, Module.End.one_apply] at h2
    rw [h2, Formalism.FourierDecayAlt.P.FrameExtension.prod_Icc_fin]
    congr 1
    unfold cpol shf
    refine Finset.prod_congr rfl fun j _ => ?_
    have hj := hu j
    by_cases hjl : j = l
    · subst hjl
      simp only [Function.update_self]
      push_cast at hj ⊢
      linear_combination -hj
    · have hne : (j : ℕ) + 1 ≠ (l : ℕ) + 1 := fun h => hjl (Fin.ext (by omega))
      rw [Function.update_of_ne hjl, Function.update_of_ne hne]
      linear_combination -hj
  obtain ⟨πS, hπS, hπS2⟩ := GlobalTheory.isType_of_irreducible_stable _ (n + 1) r z πt B S _ hz hT ht1 ht2 hB
    hS1 hS2 hS3 hq
  let a : Fin (n + 1) → (S →L[ℂ] V) := fun c =>
    (PiLp.proj 2 (𝕜 := ℂ) (fun _ : Fin (n + 1) => V) c).comp S.subtypeL
  have ha : ∀ c (y : S), a c y = (y : PiLp 2 (fun _ : Fin (n + 1) => V)) c := fun c y => rfl
  obtain ⟨hW, hA⟩ := GlobalTheory.WigSh.ContrPlus.contraction_wigMap V (n + 1) r z π B S πS a hz hT hB
    (by
      intro y
      simp only [ha]
      rw [← PiLp.norm_sq_eq_of_L2]
      rfl)
    (by
      intro h hh y c
      simp only [ha]
      rw [hπS2 h hh y, ht3 h hh])
  refine ⟨S, inferInstance, inferInstance, inferInstance, πS, _, hπS, hW, ?_⟩
  intro M v hv
  simp only [hA]
  rw [ha, ← hS5 M v hv]
  simp only [a]
  rw [adjoint_eval_subspace]
  rfl

end GlobalTheory.WigSh
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.WignerStepRaisingUnitaryComplementStatement

section

@[expose] public section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

theorem _root_.GlobalTheory.T.wigner_step_raising_unitary_complement : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n r : ℕ) (z : (Fin (2 * r + (n + 1) + 1) → ℂ)) (π : Mx (n + 1) r → (V →L[ℂ] V)) (u : ℕ → ℝ) (β : ℂ) (L : Fin (n + 1) → ℤ) (B : Fin (n + 1) → (Fin (2 * r + (n + 1) + 1) → ℂ)) (l : Fin (n + 1)), inWb (n + 1) r z → 0 < Tz (n + 1) r z → IsType (n + 1) r z π u → StrictAnti L → (∀ j : Fin (n + 1), (u ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L j : ℂ)) → IsFrameOf (n + 1) r [z] B → (∀ j, L j ≠ L l + 1) → ∃ (V₂ : Type) (_ : NormedAddCommGroup V₂) (_ : InnerProductSpace ℂ V₂) (_ : FiniteDimensional ℂ V₂) (π₂ : Mx (n + 1) r → (V₂ →L[ℂ] V₂)) (A : (Fin (2 * r + (n + 1) + 1) → ℂ) → (V₂ →L[ℂ] V)), IsType (n + 1) r z π₂ (Function.update u ((l : ℕ) + 1) (u ((l : ℕ) + 1) + 1)) ∧ GlobalTheory.WigSh.WigMap (n + 1) r z π₂ π 1 A ∧ ∀ (M : Fin n → ℤ) (v : V), v ∈ CapSp (subA (EB π B)) (shf β M) → A (B (Fin.last n)) (ContinuousLinearMap.adjoint (A (B (Fin.last n))) v) = ((GlobalTheory.WigSh.wP L M l : ℝ) : ℂ) • v := by
  first | exact @GlobalTheory.WigSh.wigner_step_raise | exact GlobalTheory.WigSh.wigner_step_raise | (intros; apply GlobalTheory.WigSh.wigner_step_raise <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsWignerContractionChainRaising

section

@[expose] public section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.WigSh

theorem chain_raise : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n r : ℕ) (z : (Fin (2 * r + (n + 1) + 1) → ℂ)) (π : Mx (n + 1) r → (V →L[ℂ] V)) (u : ℕ → ℝ) (β : ℂ) (L : Fin (n + 1) → ℤ) (B : Fin (n + 1) → (Fin (2 * r + (n + 1) + 1) → ℂ)) (l : Fin (n + 1)) (n₀ : ℕ), inWb (n + 1) r z → 0 < Tz (n + 1) r z → IsType (n + 1) r z π u → StrictAnti L → (∀ j : Fin (n + 1), (u ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L j : ℂ)) → IsFrameOf (n + 1) r [z] B → (∀ j, j < l → L l + (n₀ : ℤ) < L j) → ∃ (V₂ : Type) (_ : NormedAddCommGroup V₂) (_ : InnerProductSpace ℂ V₂) (_ : FiniteDimensional ℂ V₂) (π₂ : Mx (n + 1) r → (V₂ →L[ℂ] V₂)) (A : (Fin (2 * r + (n + 1) + 1) → ℂ) → (V₂ →L[ℂ] V)), IsType (n + 1) r z π₂ (Function.update u ((l : ℕ) + 1) (u ((l : ℕ) + 1) + (n₀ : ℝ))) ∧ GlobalTheory.WigSh.WigMap (n + 1) r z π₂ π n₀ A ∧ ∀ (M : Fin n → ℤ) (v : V), v ∈ CapSp (subA (EB π B)) (shf β M) → A (B (Fin.last n)) (ContinuousLinearMap.adjoint (A (B (Fin.last n))) v) = ((∏ j ∈ Finset.range n₀, GlobalTheory.WigSh.wP (Function.update L l (L l + (j : ℤ))) M l : ℝ) : ℂ) • v := by
  intro V _ _ _ n r z π u β L B l n₀ hz hT hπ hL hu hB
  induction n₀ with
  | zero =>
    intro _
    refine ⟨V, inferInstance, inferInstance, inferInstance, π, fun _ => ContinuousLinearMap.id ℂ V, ?_, ?_, ?_⟩
    · simpa using hπ
    · exact wigMap_zero_of_contraction V V (n + 1) r z π π _ (fun v => le_rfl) (fun h _ v => rfl)
    · intro M v _
      simp [ContinuousLinearMap.adjoint_id]
  | succ m ih =>
    intro hreg
    obtain ⟨V₂, i1, i2, i3, π₂, A, hπ₂, hA, hAA⟩ := ih (fun j hj => by
      have := hreg j hj
      push_cast at this
      omega)
    have hm0 : (0 : ℤ) ≤ (m : ℤ) := Int.natCast_nonneg m
    have hL' : StrictAnti (Function.update L l (L l + (m : ℤ))) := by
      intro a b hab
      have h1 := hL hab
      by_cases ha : a = l
      · have hb : b ≠ l := fun hb => hab.ne (ha.trans hb.symm)
        subst ha
        rw [Function.update_self, Function.update_of_ne hb]
        omega
      · by_cases hb : b = l
        · subst hb
          rw [Function.update_self, Function.update_of_ne ha]
          have := hreg a hab
          push_cast at this
          omega
        · rw [Function.update_of_ne ha, Function.update_of_ne hb]
          exact h1
    have hu' : ∀ j : Fin (n + 1),
        ((Function.update u ((l : ℕ) + 1) (u ((l : ℕ) + 1) + (m : ℝ)) ((j : ℕ) + 1) : ℝ) : ℂ) -
          ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + ((Function.update L l (L l + (m : ℤ)) j : ℤ) : ℂ) := by
      intro j
      by_cases hj : j = l
      · subst hj
        rw [Function.update_self, Function.update_self]
        have := hu j
        push_cast at this ⊢
        linear_combination this
      · have hj' : (j : ℕ) + 1 ≠ (l : ℕ) + 1 := fun h => hj (Fin.ext (by omega))
        rw [Function.update_of_ne hj, Function.update_of_ne hj']
        exact hu j
    have hreg' : ∀ j, Function.update L l (L l + (m : ℤ)) j ≠ Function.update L l (L l + (m : ℤ)) l + 1 := by
      intro j
      rw [Function.update_self]
      rcases lt_trichotomy j l with hj | hj | hj
      · rw [Function.update_of_ne hj.ne]
        have := hreg j hj
        push_cast at this
        omega
      · subst hj
        rw [Function.update_self]
        omega
      · rw [Function.update_of_ne hj.ne']
        have := hL hj
        omega
    obtain ⟨V₃, j1, j2, j3, π₃, a, hπ₃, ha, haa⟩ :=
      GlobalTheory.T.wigner_step_raising_unitary_complement V₂ n r z π₂ _ β _ B l hz hT hπ₂ hL' hu' hB hreg'
    refine ⟨V₃, j1, j2, j3, π₃, fun ω => (A ω).comp (a ω), ?_,
      wigMap_comp V V₂ V₃ (n + 1) r z π π₂ π₃ m 1 A a hA ha, ?_⟩
    · rw [Function.update_self, Function.update_idem] at hπ₃
      have e : u ((l : ℕ) + 1) + ((m + 1 : ℕ) : ℝ) = u ((l : ℕ) + 1) + (m : ℝ) + 1 := by
        push_cast
        ring
      rw [e]
      exact hπ₃
    · intro M v hv
      have hc := GlobalTheory.adjoint_mem_CapSp_subA V V₂ n r z π π₂ B (A (B (Fin.last n))) (shf β M)
        ⟨hπ.2.1, hπ.2.2.1⟩ ⟨hπ₂.2.1, hπ₂.2.2.1⟩ hπ.2.2.2.1 hπ₂.2.2.2.1 hB
        (fun h hh he => by
          have := hA.2.1 h hh (B (Fin.last n))
          rwa [he] at this) v hv
      have h2 := haa M _ hc
      show A (B (Fin.last n)) (a (B (Fin.last n))
        (ContinuousLinearMap.adjoint ((A (B (Fin.last n))).comp (a (B (Fin.last n)))) v)) = _
      rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply, h2, map_smul, hAA M v hv,
        smul_smul, Finset.prod_range_succ]
      push_cast
      rw [mul_comm]

end GlobalTheory.WigSh
end
end
