module

public import Development.AbelianVarietyTheory.Definitions.Jets.WigMap
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Formalism.HermitianCurvature.StatementQ
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
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
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Formalism.HermitianCurvature.CapelliDeterminantAndBranching
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLinearEquivOfIrreducibleIsHW
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CommonEigenvectors
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HighestWeightPolynomials
import Mathlib.Tactic.Linter.HaveILetI
public import Formalism.HermitianCurvature.FrameExists2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DifferentialOperatorBracket
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsFrameTwo
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GroupGeneratedByExp
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormRankFour
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
import Mathlib.Tactic.Linter.Style
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DifferentialOperatorBracket
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameExtension
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsShiftedTypesLowerBound
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WigMapComp
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WigMapZeroOfContraction

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsometryOfIntertwinerOfIrreducible

section

@[expose] public section

namespace GlobalTheory

open scoped InnerProductSpace

theorem exists_isometry_of_intertwiner_of_irreducible
    (V₁ : Type) [NormedAddCommGroup V₁] [InnerProductSpace ℂ V₁] [FiniteDimensional ℂ V₁]
    (V₂ : Type) [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] [FiniteDimensional ℂ V₂]
    (ι : Type) (π₁ : ι → (V₁ →L[ℂ] V₁)) (π₂ : ι → (V₂ →L[ℂ] V₂)) (T : V₁ ≃ₗ[ℂ] V₂)
    (h₁ : ∀ i v, ‖π₁ i v‖ = ‖v‖) (h₂ : ∀ i v, ‖π₂ i v‖ = ‖v‖)
    (hirr : ∀ S : Submodule ℂ V₁, (∀ i, ∀ v ∈ S, π₁ i v ∈ S) → S = ⊥ ∨ S = ⊤)
    (hT : ∀ i v, T (π₁ i v) = π₂ i (T v)) :
    ∃ φ : V₁ ≃ₗᵢ[ℂ] V₂, ∀ i v, φ (π₁ i v) = π₂ i (φ v) := by
  rcases subsingleton_or_nontrivial V₁ with hV | hV
  · refine ⟨⟨T, fun v => ?_⟩, hT⟩
    rw [Subsingleton.elim v 0]
    simp
  let p₁ : ι → (V₁ →ₗᵢ[ℂ] V₁) := fun i => ⟨(π₁ i : V₁ →ₗ[ℂ] V₁), h₁ i⟩
  let p₂ : ι → (V₂ →ₗᵢ[ℂ] V₂) := fun i => ⟨(π₂ i : V₂ →ₗ[ℂ] V₂), h₂ i⟩
  have i₁ : ∀ i a b, ⟪π₁ i a, π₁ i b⟫_ℂ = ⟪a, b⟫_ℂ := fun i a b => (p₁ i).inner_map_map a b
  have i₂ : ∀ i a b, ⟪π₂ i a, π₂ i b⟫_ℂ = ⟪a, b⟫_ℂ := fun i a b => (p₂ i).inner_map_map a b
  have s₁ : ∀ i, Function.Surjective (π₁ i) := fun i =>
    (LinearMap.injective_iff_surjective (f := (π₁ i : V₁ →ₗ[ℂ] V₁))).1 (p₁ i).injective
  let X : Module.End ℂ V₁ :=
    (LinearMap.adjoint (T : V₁ →ₗ[ℂ] V₂)).comp (T : V₁ →ₗ[ℂ] V₂)
  have hX : ∀ a b, ⟪X a, b⟫_ℂ = ⟪T a, T b⟫_ℂ := fun a b =>
    LinearMap.adjoint_inner_left (T : V₁ →ₗ[ℂ] V₂) b (T a)
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue X
  have htop : X.eigenspace c = ⊤ := by
    refine (hirr _ ?_).resolve_left hc
    intro i v hv
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    refine ext_inner_right ℂ fun u => ?_
    obtain ⟨w, rfl⟩ := s₁ i u
    rw [hX, hT, hT, i₂, ← hX, hv, ← map_smul, i₁]
  have hall : ∀ v, ‖T v‖ = Real.sqrt ‖c‖ * ‖v‖ := by
    intro v
    have hv : X v = c • v := Module.End.mem_eigenspace_iff.1 (htop ▸ Submodule.mem_top)
    have h := hX v v
    rw [hv, inner_smul_left] at h
    have h' := congrArg norm h
    rw [norm_mul, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h'
    simp only [RCLike.norm_conj, norm_pow, RCLike.norm_ofReal, abs_norm, norm_norm, Complex.coe_algebraMap, Complex.norm_real] at h'
    have e : ‖T v‖ ^ 2 = (Real.sqrt ‖c‖ * ‖v‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (norm_nonneg c), h']
    exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 e
  have hr : Real.sqrt ‖c‖ ≠ 0 := by
    intro h0
    obtain ⟨v, hv⟩ := exists_ne (0 : V₁)
    have := hall v
    rw [h0, zero_mul, norm_eq_zero] at this
    exact hv (T.map_eq_zero_iff.1 this)
  have hr' : (((Real.sqrt ‖c‖)⁻¹ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast inv_ne_zero hr
  refine ⟨⟨T.trans (LinearEquiv.smulOfNeZero ℂ V₂ _ hr'), fun v => ?_⟩, fun i v => ?_⟩
  · change ‖(((Real.sqrt ‖c‖)⁻¹ : ℝ) : ℂ) • T v‖ = ‖v‖
    rw [norm_smul, hall, Complex.norm_real, Real.norm_of_nonneg (by positivity), ← mul_assoc,
      inv_mul_cancel₀ hr, one_mul]
  · change (((Real.sqrt ‖c‖)⁻¹ : ℝ) : ℂ) • T (π₁ i v)
      = π₂ i ((((Real.sqrt ‖c‖)⁻¹ : ℝ) : ℂ) • T v)
    rw [hT, map_smul]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLinearEquivOfIrreducibleCapelli

section

@[expose] public section

open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

namespace GlobalTheory

theorem exists_linearEquiv_of_irreducible_capelli :
    ∀ (V₁ : Type) [AddCommGroup V₁] [Module ℂ V₁] [FiniteDimensional ℂ V₁] (V₂ : Type) [AddCommGroup V₂]
      [Module ℂ V₂] [FiniteDimensional ℂ V₂] (n : ℕ) (E₁ : Fin n → Fin n → Module.End ℂ V₁)
      (E₂ : Fin n → Fin n → Module.End ℂ V₂) (m : Fin n → ℂ), GlRel E₁ → GlRel E₂ → Irr E₁ → Irr E₂ →
      (∀ w v, qdet E₁ w v = cpol m w • v) → (∀ w v, qdet E₂ w v = cpol m w • v) →
      ∃ T : V₁ ≃ₗ[ℂ] V₂, ∀ a b x, T (E₁ a b x) = E₂ a b (T x) := by
  intro V₁ _ _ _ V₂ _ _ _ n E₁ E₂ m g₁ g₂ i₁ i₂ c₁ c₂
  haveI := i₁.1
  haveI := i₂.1
  obtain ⟨ν₁, v₁, -, hv₁, hw₁, -⟩ := Formalism.FourierDecayAlt.P.exists_singular_maximal_vector V₁ n E₁ g₁ ⊤
    (fun _ _ _ _ => Submodule.mem_top) top_ne_bot
  obtain ⟨ν₂, v₂, -, hv₂, hw₂, -⟩ := Formalism.FourierDecayAlt.P.exists_singular_maximal_vector V₂ n E₂ g₂ ⊤
    (fun _ _ _ _ => Submodule.mem_top) top_ne_bot
  have p₁ := Formalism.FourierDecayAlt.P.HighestWeightPolynomials.hw_cpol (m := m) g₁ (mem_CapSp.2 fun w => c₁ w v₁) hv₁ hw₁
  have p₂ := Formalism.FourierDecayAlt.P.HighestWeightPolynomials.hw_cpol (m := m) g₂ (mem_CapSp.2 fun w => c₂ w v₂) hv₂ hw₂
  have s₁ := Formalism.FourierDecayAlt.P.HighestWeightPolynomials.sdec_shift (Formalism.FourierDecayAlt.P.singular_dominant V₁ n E₁ ν₁ v₁ g₁ hw₁ hv₁)
  have s₂ := Formalism.FourierDecayAlt.P.HighestWeightPolynomials.sdec_shift (Formalism.FourierDecayAlt.P.singular_dominant V₂ n E₂ ν₂ v₂ g₂ hw₂ hv₂)
  have h := (Formalism.FourierDecayAlt.P.separating_polynomials n _ _ (fun w => (p₁ w).symm.trans (p₂ w)) s₂).2 s₁
  have hν : ν₁ = ν₂ := by
    funext j
    exact sub_left_injective (congrFun h j)
  subst hν
  exact exists_linearEquiv_of_irreducible_isHW V₁ V₂ n E₁ E₂ ν₁ v₁ v₂ g₁ g₂ i₁.2 i₂.2 hw₁ hw₂ hv₁ hv₂

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntertwinerExpOfIntertwiner

section

@[expose] public section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)
open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.QrD

noncomputable section

namespace GlobalTheory

theorem intertwiner_exp_of_intertwiner {V₁ : Type} [NormedAddCommGroup V₁] [NormedSpace ℂ V₁] [FiniteDimensional ℂ V₁]
    {V₂ : Type} [NormedAddCommGroup V₂] [NormedSpace ℂ V₂] [FiniteDimensional ℂ V₂]
    (T : V₁ →ₗ[ℂ] V₂) {A₁ : V₁ →L[ℂ] V₁} {A₂ : V₂ →L[ℂ] V₂} (h : ∀ v, T (A₁ v) = A₂ (T v)) (v : V₁) :
    T (NormedSpace.exp A₁ v) = NormedSpace.exp A₂ (T v) := by
  have : CompleteSpace V₁ := FiniteDimensional.complete ℂ V₁
  have : CompleteSpace V₂ := FiniteDimensional.complete ℂ V₂
  have hp : ∀ n : ℕ, ∀ v, T ((A₁ ^ n) v) = (A₂ ^ n) (T v) := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [pow_succ, pow_succ, mul_apply_eq_comp, mul_apply_eq_comp, ih, h]
  have h1 := ((LinearMap.toContinuousLinearMap T).comp (ContinuousLinearMap.apply ℂ V₁ v)).hasSum
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A₁)
  have h2 := (ContinuousLinearMap.apply ℂ V₂ (T v)).hasSum (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A₂)
  refine h1.unique (h2.congr_fun ?_)
  intro n
  show T (((n.factorial : ℂ)⁻¹) • (A₁ ^ n) v) = ((n.factorial : ℂ)⁻¹) • (A₂ ^ n) (T v)
  rw [map_smul, hp]

theorem intertwiner_dOp_of_EB {V₁ : Type} [NormedAddCommGroup V₁] [NormedSpace ℂ V₁] [FiniteDimensional ℂ V₁]
    {V₂ : Type} [NormedAddCommGroup V₂] [NormedSpace ℂ V₂] [FiniteDimensional ℂ V₂] {k r : ℕ}
    {z : Fin (2 * r + k + 1) → ℂ} {π₁ : Mx k r → (V₁ →L[ℂ] V₁)} {π₂ : Mx k r → (V₂ →L[ℂ] V₂)} (T : V₁ →ₗ[ℂ] V₂)
    {B : Fin k → Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hzz : herm (Hpk k r) z z ≠ 0)
    (h₁ : IsRepW k r z π₁) (h₂ : IsRepW k r z π₂) (hB : IsFrameOf k r [z] B)
    (hT : ∀ a b v, T (EB π₁ B a b v) = EB π₂ B a b (T v)) {X : Mx k r} (hX : InLieW k r z X) :
    ∀ v, T (dOp π₁ X v) = dOp π₂ X (T v) := by
  have hE := elementary_lie_elements
  let Gd : Mx k r → Prop := fun Z => InGlW k r z Z ∧ ∀ v, T (ecOp π₁ Z v) = ecOp π₂ Z (T v)
  have gadd : ∀ Z Z', Gd Z → Gd Z' → Gd (Z + Z') := by
    intro Z Z' h h'
    have e₁ := (hE V₁ k r z π₁ h₁ Z Z' h.1 h'.1).1
    have e₂ := (hE V₂ k r z π₂ h₂ Z Z' h.1 h'.1).1
    refine ⟨e₁.1, fun v => ?_⟩
    rw [e₁.2, e₂.2, _root_.add_apply, _root_.add_apply, map_add (f := _), h.2, h'.2]
  have gsmul : ∀ (c : ℂ) Z, Gd Z → Gd (c • Z) := by
    intro c Z h
    have e₁ := (hE V₁ k r z π₁ h₁ Z Z h.1 h.1).2.1 c
    have e₂ := (hE V₂ k r z π₂ h₂ Z Z h.1 h.1).2.1 c
    refine ⟨e₁.1, fun v => ?_⟩
    rw [e₁.2, e₂.2, _root_.smul_apply, _root_.smul_apply, map_smul, h.2]
  have g0 : Gd 0 := by
    refine ⟨SkewHermitianParts.inGl_zero z, fun v => ?_⟩
    have e₁ := ((hE V₁ k r z π₁ h₁ 0 0 (SkewHermitianParts.inGl_zero z) (SkewHermitianParts.inGl_zero z)).2.1 0).2
    have e₂ := ((hE V₂ k r z π₂ h₂ 0 0 (SkewHermitianParts.inGl_zero z) (SkewHermitianParts.inGl_zero z)).2.1 0).2
    rw [zero_smul, zero_smul] at e₁ e₂
    rw [e₁, e₂]
    simp
  have gu : ∀ a b, Gd (unitB (Hpk k r) B a b) := fun a b => ⟨frame_lie hB a b, fun v => hT a b v⟩
  have hsum : Gd (∑ a, ∑ b, herm (Hpk k r) (X *ᵥ B b) (B a) • unitB (Hpk k r) B a b) :=
    Finset.sum_induction _ Gd gadd g0 fun a _ =>
      Finset.sum_induction _ Gd gadd g0 fun b _ => gsmul _ _ (gu a b)
  rw [← SkewHermitianParts.lie_expand hz hzz hB hX] at hsum
  have e₁ : ecOp π₁ X = dOp π₁ X := by
    unfold ecOp
    rw [SkewHermitianParts.hpart1_skew hX.1.1, SkewHermitianParts.hpart2_skew hX.1.1, SkewHermitianParts.dOp_zero, smul_zero, add_zero]
  have e₂ : ecOp π₂ X = dOp π₂ X := by
    unfold ecOp
    rw [SkewHermitianParts.hpart1_skew hX.1.1, SkewHermitianParts.hpart2_skew hX.1.1, SkewHermitianParts.dOp_zero, smul_zero, add_zero]
  rw [← e₁, ← e₂]
  exact hsum.2

theorem intertwiner_group_of_EB : ∀ (V₁ : Type) [NormedAddCommGroup V₁] [NormedSpace ℂ V₁] [FiniteDimensional ℂ V₁] (V₂ : Type) [NormedAddCommGroup V₂] [NormedSpace ℂ V₂] [FiniteDimensional ℂ V₂] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π₁ : Mx k r → (V₁ →L[ℂ] V₁)) (π₂ : Mx k r → (V₂ →L[ℂ] V₂)) (T : V₁ →ₗ[ℂ] V₂) (B : Fin k → (Fin (2 * r + k + 1) → ℂ)), inWb k r z → 0 < Tz k r z → IsRepW k r z π₁ → IsRepW k r z π₂ → IsFrameOf k r [z] B → (∀ a b v, T (EB π₁ B a b v) = EB π₂ B a b (T v)) → ∀ h ∈ UWset k r z, ∀ v, T (π₁ h v) = π₂ h (T v) := by
  intro V₁ _ _ _ V₂ _ _ _ k r z π₁ π₂ T B hz hTz h₁ h₂ hB hT h hh
  have hzz : herm (Hpk k r) z z ≠ 0 := by
    rw [Qx8.herm_self']
    intro h0
    rw [neg_eq_zero, Complex.ofReal_eq_zero] at h0
    exact hTz.ne' h0
  refine (exp_generates k r z hz hTz (fun h => h ∈ UWset k r z ∧ ∀ v, T (π₁ h v) = π₂ h (T v))
    ⟨Qx8.uw_one z, fun v => ?_⟩ ?_ h hh).2
  · rw [h₁.1.1, h₂.1.1]
    rfl
  · intro X g hX hg
    have e0 : NormedSpace.exp X ∈ UWset k r z := by
      have := exp_uw hX 1
      simpa using this
    have e₁ : π₁ (NormedSpace.exp X) = NormedSpace.exp (dOp π₁ X) := by
      have := representation_exp V₁ k r z π₁ h₁ X hX 1
      simpa using this
    have e₂ : π₂ (NormedSpace.exp X) = NormedSpace.exp (dOp π₂ X) := by
      have := representation_exp V₂ k r z π₂ h₂ X hX 1
      simpa using this
    refine ⟨SkewHermitianParts.uw_mul e0 hg.1, fun v => ?_⟩
    rw [h₁.1.2 _ e0 _ hg.1, h₂.1.2 _ e0 _ hg.1, e₁, e₂]
    show T (NormedSpace.exp (dOp π₁ X) (π₁ g v)) = NormedSpace.exp (dOp π₂ X) (π₂ g (T v))
    rw [intertwiner_exp_of_intertwiner T (intertwiner_dOp_of_EB T hz hzz h₁ h₂ hB hT hX), hg.2]

end GlobalTheory
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsometryOfIsTypeOfParamEq

section

@[expose] public section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory

open Formalism.FourierDecayAlt.P

theorem exists_isometry_of_isType_of_param_eq :
    ∀ (V₁ : Type) [NormedAddCommGroup V₁] [InnerProductSpace ℂ V₁] [FiniteDimensional ℂ V₁] (V₂ : Type) [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] [FiniteDimensional ℂ V₂] (n r : ℕ) (z : (Fin (2 * r + (n + 1) + 1) → ℂ)) (π₁ : Mx (n + 1) r → (V₁ →L[ℂ] V₁)) (π₂ : Mx (n + 1) r → (V₂ →L[ℂ] V₂)) (u₁ u₂ : ℕ → ℝ), inWb (n + 1) r z → 0 < Tz (n + 1) r z → IsType (n + 1) r z π₁ u₁ → IsType (n + 1) r z π₂ u₂ → (∀ i ∈ Finset.Icc 1 (n + 1), u₁ i = u₂ i) → ∃ φ : V₁ ≃ₗᵢ[ℂ] V₂, ∀ h ∈ UWset (n + 1) r z, ∀ v, φ (π₁ h v) = π₂ h (φ v) := by
  intro V₁ _ _ _ V₂ _ _ _ n r z π₁ π₂ u₁ u₂ hz hT ht₁ ht₂ hu
  obtain ⟨hnt₁, hrep₁, hcont₁, hn₁, hirr₁, hcap₁⟩ := ht₁
  obtain ⟨hnt₂, hrep₂, hcont₂, hn₂, hirr₂, hcap₂⟩ := ht₂
  have hR₁ : IsRepW (n + 1) r z π₁ := ⟨hrep₁, hcont₁⟩
  have hR₂ : IsRepW (n + 1) r z π₂ := ⟨hrep₂, hcont₂⟩
  obtain ⟨B, hB⟩ : ∃ B : Fin (n + 1) → (Fin (2 * r + (n + 1) + 1) → ℂ), IsFrameOf (n + 1) r [z] B :=
    Qx8.frame_exists hz hT
  obtain ⟨g₁, q₁⟩ := frame_general_linear V₁ (n + 1) r (n + 1) z π₁ B hR₁ hB
  obtain ⟨g₂, q₂⟩ := frame_general_linear V₂ (n + 1) r (n + 1) z π₂ B hR₂ hB
  have i₁ : Irr (EB π₁ B) :=
    ⟨hnt₁, fun S hS => hirr₁ S (lie_stabilizer V₁ (n + 1) r z π₁ B hz hT hR₁ hB S hS)⟩
  have i₂ : Irr (EB π₂ B) :=
    ⟨hnt₂, fun S hS => hirr₂ S (lie_stabilizer V₂ (n + 1) r z π₂ B hz hT hR₂ hB S hS)⟩
  let m : Fin (n + 1) → ℂ := fun j => (u₁ ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2
  have hc : ∀ w : ℂ, (∏ i ∈ Finset.Icc 1 (n + 1), (w - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 + (u₁ i : ℂ))) =
      cpol m w := by
    intro w
    rw [FrameExtension.prod_Icc_fin]
    unfold cpol
    refine Finset.prod_congr rfl (fun j _ => ?_)
    simp only [m]
    ring
  have c₁ : ∀ w v, qdet (EB π₁ B) w v = cpol m w • v := by
    intro w v
    rw [← q₁ w v, hcap₁ B hB w v, hc]
  have c₂ : ∀ w v, qdet (EB π₂ B) w v = cpol m w • v := by
    intro w v
    rw [← q₂ w v, hcap₂ B hB w v, ← hc]
    congr 1
    exact Finset.prod_congr rfl (fun i hi => by rw [hu i hi])
  obtain ⟨T, hTE⟩ := exists_linearEquiv_of_irreducible_capelli V₁ V₂ (n + 1) _ _ m g₁ g₂ i₁ i₂ c₁ c₂
  have hG := intertwiner_group_of_EB V₁ V₂ (n + 1) r z π₁ π₂ (T : V₁ →ₗ[ℂ] V₂) B hz hT hR₁ hR₂ hB hTE
  obtain ⟨φ, hφ⟩ := exists_isometry_of_intertwiner_of_irreducible V₁ V₂ (UWset (n + 1) r z)
    (fun h => π₁ h.1) (fun h => π₂ h.1) T (fun h v => hn₁ h.1 h.2 v) (fun h v => hn₂ h.1 h.2 v)
    (fun S hS => hirr₁ S (fun h hh v hv => hS ⟨h, hh⟩ v hv)) (fun h v => hG h.1 h.2 v)
  exact ⟨φ, fun h hh v => hφ ⟨h, hh⟩ v⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsShiftedTypesLowerBoundStatement

section

@[expose] public section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

theorem _root_.GlobalTheory.T.exists_shifted_types_lower_bound_alt : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mx k r → (V →L[ℂ] V)) (u : ℕ → ℝ) (l n₀ : ℕ) (b : ℝ), inWb k r z → 0 < Tz k r z → IsType k r z π u → (∀ i ∈ Finset.Icc 1 (k - 1), ∃ N : ℕ, u i - u (i + 1) = (N : ℝ) + 1) → 1 ≤ l → l < k → 2 * (n₀ : ℝ) + 1 ≤ u l - u (l + 1) → (∀ i ∈ Finset.Icc 1 k, |u i| ≤ b) → (n₀ : ℝ) ≤ b → 1 ≤ b → ∃ (Vp : Type) (_ : NormedAddCommGroup Vp) (_ : InnerProductSpace ℂ Vp) (_ : FiniteDimensional ℂ Vp) (Vm : Type) (_ : NormedAddCommGroup Vm) (_ : InnerProductSpace ℂ Vm) (_ : FiniteDimensional ℂ Vm) (πp : Mx k r → (Vp →L[ℂ] Vp)) (πm : Mx k r → (Vm →L[ℂ] Vm)) (Ap : (Fin (2 * r + k + 1) → ℂ) → (Vp →L[ℂ] V)) (Am : (Fin (2 * r + k + 1) → ℂ) → (Vm →L[ℂ] V)), IsType k r z πp (Function.update u (l + 1) (u (l + 1) + (n₀ : ℝ))) ∧ IsType k r z πm (Function.update u l (u l - (n₀ : ℝ))) ∧ GlobalTheory.WigSh.WigMap k r z πp π n₀ Ap ∧ GlobalTheory.WigSh.WigMap k r z πm π n₀ Am ∧ ∀ ω, inWb k r ω → herm (Hpk k r) ω z = 0 → ∀ v : V, (herm (Hpk k r) ω ω).re ^ n₀ * ‖v‖ ^ 2 ≤ (3 * b) ^ (2 * n₀) * (‖ContinuousLinearMap.adjoint (Ap ω) v‖ ^ 2 + ‖ContinuousLinearMap.adjoint (Am ω) v‖ ^ 2) := by
  first | exact @GlobalTheory.WigSh.exists_shifted_types_lower_bound | exact GlobalTheory.WigSh.exists_shifted_types_lower_bound | (intros; apply GlobalTheory.WigSh.exists_shifted_types_lower_bound <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormAdjointCompIsometryEquiv

section

@[expose] public section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.WigSh

theorem norm_adjoint_comp_isometryEquiv {V₁ V₂ V₃ : Type} [NormedAddCommGroup V₁] [InnerProductSpace ℂ V₁]
    [CompleteSpace V₁] [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] [CompleteSpace V₂]
    [NormedAddCommGroup V₃] [InnerProductSpace ℂ V₃] [CompleteSpace V₃]
    (A : V₂ →L[ℂ] V₁) (φ : V₃ ≃ₗᵢ[ℂ] V₂) (v : V₁) :
    ‖ContinuousLinearMap.adjoint (A.comp (φ : V₃ →L[ℂ] V₂)) v‖ = ‖ContinuousLinearMap.adjoint A v‖ := by
  rw [ContinuousLinearMap.adjoint_comp, LinearIsometryEquiv.adjoint_eq_symm]
  simp

theorem exists_wigMap_pair_of_isType : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp] (Vm : Type) [NormedAddCommGroup Vm] [InnerProductSpace ℂ Vm] [FiniteDimensional ℂ Vm] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mx k r → (V →L[ℂ] V)) (πp : Mx k r → (Vp →L[ℂ] Vp)) (πm : Mx k r → (Vm →L[ℂ] Vm)) (u up um : ℕ → ℝ) (l n₀ : ℕ) (b : ℝ), inWb k r z → 0 < Tz k r z → IsType k r z π u → (∀ i ∈ Finset.Icc 1 (k - 1), ∃ N : ℕ, u i - u (i + 1) = (N : ℝ) + 1) → 1 ≤ l → l < k → 2 * (n₀ : ℝ) + 1 ≤ u l - u (l + 1) → (∀ i ∈ Finset.Icc 1 k, |u i| ≤ b) → (n₀ : ℝ) ≤ b → 1 ≤ b → IsType k r z πp up → IsType k r z πm um → (∀ i ∈ Finset.Icc 1 k, up i = if i = l + 1 then u i + (n₀ : ℝ) else u i) → (∀ i ∈ Finset.Icc 1 k, um i = if i = l then u i - (n₀ : ℝ) else u i) → ∃ (Ap : (Fin (2 * r + k + 1) → ℂ) → (Vp →L[ℂ] V)) (Am : (Fin (2 * r + k + 1) → ℂ) → (Vm →L[ℂ] V)), GlobalTheory.WigSh.WigMap k r z πp π n₀ Ap ∧ GlobalTheory.WigSh.WigMap k r z πm π n₀ Am ∧ ∀ ω, inWb k r ω → herm (Hpk k r) ω z = 0 → ∀ v : V, (herm (Hpk k r) ω ω).re ^ n₀ * ‖v‖ ^ 2 ≤ (3 * b) ^ (2 * n₀) * (‖ContinuousLinearMap.adjoint (Ap ω) v‖ ^ 2 + ‖ContinuousLinearMap.adjoint (Am ω) v‖ ^ 2) := by
  intro V _ _ _ Vp _ _ _ Vm _ _ _ k r z π πp πm u up um l n₀ b hz hT hπ hgap hl hlk hn hb hnb h1b hp hm hup hum
  obtain ⟨Vp', _, _, _, Vm', _, _, _, πp', πm', Ap', Am', hp', hm', hAp, hAm, hlb⟩ :=
    GlobalTheory.T.exists_shifted_types_lower_bound_alt V k r z π u l n₀ b hz hT hπ hgap hl hlk hn hb hnb h1b
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  obtain ⟨φp, hφp⟩ := GlobalTheory.exists_isometry_of_isType_of_param_eq Vp Vp' n r z πp πp' _ _ hz hT hp hp' (by
    intro i hi
    rw [hup i hi, Function.update_apply]
    split_ifs with h
    · rw [h]
    · rfl)
  obtain ⟨φm, hφm⟩ := GlobalTheory.exists_isometry_of_isType_of_param_eq Vm Vm' n r z πm πm' _ _ hz hT hm hm' (by
    intro i hi
    rw [hum i hi, Function.update_apply]
    split_ifs with h
    · rw [h]
    · rfl)
  refine ⟨fun ω => (Ap' ω).comp (φp : Vp →L[ℂ] Vp'), fun ω => (Am' ω).comp (φm : Vm →L[ℂ] Vm'), ?_, ?_, ?_⟩
  · exact wigMap_comp V Vp' Vp (n + 1) r z π πp' πp n₀ 0 Ap' (fun _ => (φp : Vp →L[ℂ] Vp')) hAp
      (wigMap_zero_of_contraction Vp' Vp (n + 1) r z πp' πp _ (fun v => by simp)
        (fun h hh v => by simpa using hφp h hh v))
  · exact wigMap_comp V Vm' Vm (n + 1) r z π πm' πm n₀ 0 Am' (fun _ => (φm : Vm →L[ℂ] Vm')) hAm
      (wigMap_zero_of_contraction Vm' Vm (n + 1) r z πm' πm _ (fun v => by simp)
        (fun h hh v => by simpa using hφm h hh v))
  · intro ω hω hωz v
    rw [norm_adjoint_comp_isometryEquiv, norm_adjoint_comp_isometryEquiv]
    exact hlb ω hω hωz v

end GlobalTheory.WigSh
end
end
