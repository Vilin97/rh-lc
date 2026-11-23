module

public import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.Statement
public import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.SplitA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.DerivExistsAllPosStatement
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.HasDerivAtRealOfComplex
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.OneParam
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Exists
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Weight
public import Mathlib.LinearAlgebra.Trace
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactCasimirHighestWeight
import Mathlib.RingTheory.SimpleRing.Principal
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.URepCompRed
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Unique

-- Source module: ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.SplitB

section

@[expose] public section

noncomputable section

open Matrix Finset TensorProduct

namespace ReciprocityTheory.ChartRestriction.TR.Weyl

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.HW

section Tens

variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

theorem sp_mapL_one : mapL (1 : E →L[ℂ] E) (1 : F →L[ℂ] F) = 1 := mapL_id_id

theorem sp_star_mapL (A : E →L[ℂ] E) (B : F →L[ℂ] F) : star (mapL A B) = mapL (star A) (star B) := by
  have := FiniteDimensional.complete ℂ E
  have := FiniteDimensional.complete ℂ F
  have := FiniteDimensional.complete ℂ (E ⊗[ℂ] F)
  simp only [ContinuousLinearMap.star_eq_adjoint, adjoint_mapL]

theorem sp_mapL_unitary (A : unitary (E →L[ℂ] E)) (B : unitary (F →L[ℂ] F)) :
    mapL (A : E →L[ℂ] E) (B : F →L[ℂ] F) ∈ unitary (E ⊗[ℂ] F →L[ℂ] E ⊗[ℂ] F) := by
  rw [Unitary.mem_iff, sp_star_mapL, ← mapL_mul, ← mapL_mul, Unitary.star_mul_self_of_mem A.2,
    Unitary.star_mul_self_of_mem B.2, Unitary.mul_star_self_of_mem A.2, Unitary.mul_star_self_of_mem B.2]
  exact ⟨sp_mapL_one, sp_mapL_one⟩

def sp_tensU {G : Type*} [Monoid G] (ρ1 : G →* unitary (E →L[ℂ] E)) (ρ2 : G →* unitary (F →L[ℂ] F)) :
    G →* unitary (E ⊗[ℂ] F →L[ℂ] E ⊗[ℂ] F) where
  toFun g := ⟨mapL (ρ1 g : E →L[ℂ] E) (ρ2 g : F →L[ℂ] F), sp_mapL_unitary _ _⟩
  map_one' := Subtype.ext (by
    show mapL _ _ = 1
    rw [map_one, map_one]
    exact sp_mapL_one)
  map_mul' g h := Subtype.ext (by
    show mapL _ _ = mapL _ _ * mapL _ _
    rw [map_mul, map_mul]
    exact mapL_mul _ _ _ _)

def tensorLeftOperator : (E →L[ℂ] E) →L[ℂ] (E ⊗[ℂ] F →L[ℂ] E ⊗[ℂ] F) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => mapL A (1 : F →L[ℂ] F)
      map_add' := fun _ _ => mapL_add_left _ _ _
      map_smul' := fun _ _ => mapL_smul_left _ _ _ }

def tensorRightOperator : (F →L[ℂ] F) →L[ℂ] (E ⊗[ℂ] F →L[ℂ] E ⊗[ℂ] F) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun B => mapL (1 : E →L[ℂ] E) B
      map_add' := fun _ _ => mapL_add_right _ _ _
      map_smul' := fun _ _ => mapL_smul_right _ _ _ }

theorem tensorLeftOperator_apply (A : E →L[ℂ] E) : (tensorLeftOperator : _ →L[ℂ] (E ⊗[ℂ] F →L[ℂ] E ⊗[ℂ] F)) A =
    mapL A (1 : F →L[ℂ] F) := rfl

theorem tensorRightOperator_apply (B : F →L[ℂ] F) : (tensorRightOperator : _ →L[ℂ] (E ⊗[ℂ] F →L[ℂ] E ⊗[ℂ] F)) B =
    mapL (1 : E →L[ℂ] E) B := rfl

theorem sp_mapL_split (A : E →L[ℂ] E) (B : F →L[ℂ] F) :
    mapL A B = mapL A (1 : F →L[ℂ] F) * mapL (1 : E →L[ℂ] E) B := by
  rw [← mapL_mul, mul_one, one_mul]

theorem sp_tensU_cont {G : Type*} [Monoid G] [TopologicalSpace G] (ρ1 : G →* unitary (E →L[ℂ] E))
    (ρ2 : G →* unitary (F →L[ℂ] F)) (h1 : Continuous ρ1) (h2 : Continuous ρ2) :
    Continuous (sp_tensU ρ1 ρ2) := by
  have c1 : Continuous fun g => (ρ1 g : E →L[ℂ] E) := continuous_subtype_val.comp h1
  have c2 : Continuous fun g => (ρ2 g : F →L[ℂ] F) := continuous_subtype_val.comp h2
  have h : Continuous fun g => mapL (ρ1 g : E →L[ℂ] E) (ρ2 g : F →L[ℂ] F) := by
    have e : (fun g => mapL (ρ1 g : E →L[ℂ] E) (ρ2 g : F →L[ℂ] F)) =
        fun g => mapL (ρ1 g : E →L[ℂ] E) (1 : F →L[ℂ] F) * mapL (1 : E →L[ℂ] E) (ρ2 g : F →L[ℂ] F) :=
      funext fun g => sp_mapL_split _ _
    rw [e]
    exact ((tensorLeftOperator (F := F)).continuous.comp c1).mul ((tensorRightOperator (E := E)).continuous.comp c2)
  exact Continuous.subtype_mk h _

theorem sp_mapL_hasDeriv {a : ℝ → E →L[ℂ] E} {b : ℝ → F →L[ℂ] F} {a' : E →L[ℂ] E} {b' : F →L[ℂ] F}
    (ha : HasDerivAt a a' 0) (hb : HasDerivAt b b' 0) (ha0 : a 0 = 1) (hb0 : b 0 = 1) :
    HasDerivAt (fun t => mapL (a t) (b t)) (mapL a' (1 : F →L[ℂ] F) + mapL (1 : E →L[ℂ] E) b') 0 := by
  have h1 := ((tensorLeftOperator (F := F)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) ha
  have h2 := ((tensorRightOperator (E := E)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hb
  have h := h1.mul h2
  simp only [Function.comp_def, ContinuousLinearMap.coe_restrictScalars', tensorLeftOperator_apply, tensorRightOperator_apply,
    ha0, hb0, sp_mapL_one, mul_one, one_mul] at h
  have e : (fun t => mapL (a t) (b t)) = fun t => mapL (a t) (1 : F →L[ℂ] F) * mapL (1 : E →L[ℂ] E) (b t) :=
    funext fun t => sp_mapL_split _ _
  rw [e]
  exact h

end Tens

variable {n : ℕ} {ε : Fin n → Bool} {Λ1 : Fin (cnt ε true) → ℝ} {Λ2 : Fin (cnt ε false) → ℝ}

theorem sp_sub_add (ε : Fin n → Bool) (c : Bool) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    sp_sub ε c (X + Y) = sp_sub ε c X + sp_sub ε c Y := by
  ext; simp [sp_sub]

def sp_dτ (T1 : KType (fun _ : Fin (cnt ε true) => true) Λ1)
    (T2 : KType (fun _ : Fin (cnt ε false) => true) Λ2) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (T1.V ⊗[ℂ] T2.V →L[ℂ] T1.V ⊗[ℂ] T2.V) where
  toFun X := mapL (T1.dτ (sp_sub ε true X)) 1 + mapL 1 (T2.dτ (sp_sub ε false X))
  map_add' X Y := by
    simp only [sp_sub_add, map_add (f := _), mapL_add_left, mapL_add_right]
    abel
  map_smul' c X := by
    simp only [sp_sub_smul, map_smul, mapL_smul_left, mapL_smul_right, smul_add, RingHom.id_apply]

theorem sp_dτ_apply (T1 : KType (fun _ : Fin (cnt ε true) => true) Λ1)
    (T2 : KType (fun _ : Fin (cnt ε false) => true) Λ2) (X : Matrix (Fin n) (Fin n) ℂ) :
    sp_dτ T1 T2 X = mapL (T1.dτ (sp_sub ε true X)) 1 + mapL 1 (T2.dτ (sp_sub ε false X)) := rfl

theorem sp_curve_zero {X : Matrix (Fin n) (Fin n) ℂ} {γ : ℝ → KG ε}
    (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) : γ 0 = 1 :=
  onep_KG_ext (by rw [hγ 0]; simp; rfl)

def sp_rep (T1 : KType (fun _ : Fin (cnt ε true) => true) Λ1)
    (T2 : KType (fun _ : Fin (cnt ε false) => true) Λ2) : KRep ε where
  V := T1.V ⊗[ℂ] T2.V
  instCS := FiniteDimensional.complete ℂ _
  τ := sp_tensU (T1.τ.comp (sp_proj ε true)) (T2.τ.comp (sp_proj ε false))
  cont := sp_tensU_cont _ _ (T1.cont.comp (sp_proj_cont ε true)) (T2.cont.comp (sp_proj_cont ε false))
  dτ := sp_dτ T1 T2
  hasDeriv := by
    intro X hX γ hγ
    have h1 := T1.hasDeriv _ (sp_sub_inK true hX) (fun t => sp_proj ε true (γ t))
      (sp_proj_curve true hX hγ)
    have h2 := T2.hasDeriv _ (sp_sub_inK false hX) (fun t => sp_proj ε false (γ t))
      (sp_proj_curve false hX hγ)
    have e0 := sp_curve_zero hγ
    refine sp_mapL_hasDeriv h1 h2 ?_ ?_
    · simp only [e0, map_one]; rfl
    · simp only [e0, map_one]; rfl

theorem sp_rep_op (T1 : KType (fun _ : Fin (cnt ε true) => true) Λ1)
    (T2 : KType (fun _ : Fin (cnt ε false) => true) Λ2) (k : KG ε) :
    (sp_rep T1 T2).op k = mapL (T1.op (sp_proj ε true k)) (T2.op (sp_proj ε false k)) := rfl

theorem sp_units_true (T1 : KType (fun _ : Fin (cnt ε true) => true) Λ1)
    (T2 : KType (fun _ : Fin (cnt ε false) => true) Λ2) (r s : Fin (cnt ε true))
    (x : T1.V ⊗[ℂ] T2.V) :
    (sp_rep T1 T2).units (blk ε true r) (blk ε true s) x = TensorProduct.map (kunits T1 r s) LinearMap.id x := by
  show (sp_dτ T1 T2 (single (blk ε true r) (blk ε true s) 1)) x = _
  simp [sp_dτ_apply, sp_sub_single_same, sp_sub_single_other, kunits, mapL_apply]
  rfl

theorem sp_units_false (T1 : KType (fun _ : Fin (cnt ε true) => true) Λ1)
    (T2 : KType (fun _ : Fin (cnt ε false) => true) Λ2) (r s : Fin (cnt ε false))
    (x : T1.V ⊗[ℂ] T2.V) :
    (sp_rep T1 T2).units (blk ε false r) (blk ε false s) x = TensorProduct.map LinearMap.id (kunits T2 r s) x := by
  show (sp_dτ T1 T2 (single (blk ε false r) (blk ε false s) 1)) x = _
  simp [sp_dτ_apply, sp_sub_single_same, sp_sub_single_other, kunits, mapL_apply]
  rfl

end ReciprocityTheory.ChartRestriction.TR.Weyl
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.SplitC

section

@[expose] public section

noncomputable section

open Matrix Finset TensorProduct

namespace ReciprocityTheory.ChartRestriction.TR.Weyl

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.HW

theorem sp_coef_map {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    (f : M →ₗ[ℂ] M) (ψ : N →ₗ[ℂ] ℂ) (x : M ⊗[ℂ] N) :
    TensorProduct.rid ℂ M (ψ.lTensor M (TensorProduct.map f LinearMap.id x)) =
      f (TensorProduct.rid ℂ M (ψ.lTensor M x)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m y => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem sp_expand {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    [Module.Finite ℂ N] (x : M ⊗[ℂ] N) :
    x = ∑ i, TensorProduct.rid ℂ M (((Module.finBasis ℂ N).coord i).lTensor M x) ⊗ₜ
      (Module.finBasis ℂ N) i := by
  conv_lhs => rw [← (TensorProduct.equivFinsuppOfBasisRight (Module.finBasis ℂ N)).symm_apply_apply x]
  rw [TensorProduct.equivFinsuppOfBasisRight_symm_apply,
    Finsupp.sum_fintype _ _ (fun i => by simp)]
  simp_rw [TensorProduct.equivFinsuppOfBasisRight_apply]

theorem sp_tmul_cancel {E N : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [AddCommGroup N]
    [Module ℂ N] {w : E} (hw : ‖w‖ = 1) {y z : N} (h : w ⊗ₜ[ℂ] y = w ⊗ₜ[ℂ] z) : y = z := by
  have e := congrArg (fun u => TensorProduct.lid ℂ N
    (((innerSL ℂ w : E →L[ℂ] ℂ) : E →ₗ[ℂ] ℂ).rTensor N u)) h
  simpa [hw] using e

variable {p q : ℕ} {Λ1 : Fin p → ℝ} {Λ2 : Fin q → ℝ}

theorem sp_left (T1 : KType (fun _ : Fin p => true) Λ1) {N : Type*} [AddCommGroup N] [Module ℂ N]
    [Module.Finite ℂ N] (x : T1.V ⊗[ℂ] N) (ν : Fin p → ℝ)
    (hw : ∀ r, TensorProduct.map (kunits T1 r r) LinearMap.id x = ((ν r : ℝ) : ℂ) • x)
    (hr : ∀ r s, r < s → TensorProduct.map (kunits T1 r s) LinearMap.id x = 0) :
    ∃ y : N, x = T1.w ⊗ₜ y := by
  have hcoef : ∀ i, ∃ c : ℂ,
      TensorProduct.rid ℂ _ (((Module.finBasis ℂ N).coord i).lTensor _ x) = c • T1.w := by
    intro i
    by_cases hm : TensorProduct.rid ℂ _ (((Module.finBasis ℂ N).coord i).lTensor _ x) = 0
    · exact ⟨0, by rw [hm, zero_smul]⟩
    · have h : IsKHWVec (fun _ : Fin p => true) (kunits T1) ν
          (TensorProduct.rid ℂ _ (((Module.finBasis ℂ N).coord i).lTensor _ x)) := by
        refine ⟨fun r => ?_, fun r s hrs _ => ?_⟩
        · rw [← sp_coef_map, hw r, map_smul, map_smul]
        · rw [← sp_coef_map, hr r s hrs, map_zero, map_zero]
      obtain ⟨-, c, hc⟩ := KType.hw_unique T1 hm h
      exact ⟨c, hc⟩
  choose c hc using hcoef
  refine ⟨∑ i, c i • (Module.finBasis ℂ N) i, ?_⟩
  conv_lhs => rw [sp_expand x]
  simp_rw [hc, TensorProduct.smul_tmul, TensorProduct.tmul_sum]

theorem sp_ker (T1 : KType (fun _ : Fin p => true) Λ1) (T2 : KType (fun _ : Fin q => true) Λ2)
    (x : T1.V ⊗[ℂ] T2.V) (hx0 : x ≠ 0) (ν1 : Fin p → ℝ) (ν2 : Fin q → ℝ)
    (hw1 : ∀ r, TensorProduct.map (kunits T1 r r) LinearMap.id x = ((ν1 r : ℝ) : ℂ) • x)
    (hr1 : ∀ r s, r < s → TensorProduct.map (kunits T1 r s) LinearMap.id x = 0)
    (hw2 : ∀ r, TensorProduct.map LinearMap.id (kunits T2 r r) x = ((ν2 r : ℝ) : ℂ) • x)
    (hr2 : ∀ r s, r < s → TensorProduct.map LinearMap.id (kunits T2 r s) x = 0) :
    ∃ c : ℂ, x = c • (T1.w ⊗ₜ T2.w) := by
  obtain ⟨y, rfl⟩ := sp_left T1 x ν1 hw1 hr1
  have hy0 : y ≠ 0 := by rintro rfl; exact hx0 (TensorProduct.tmul_zero _ _)
  have h : IsKHWVec (fun _ : Fin q => true) (kunits T2) ν2 y := by
    refine ⟨fun r => ?_, fun r s hrs _ => ?_⟩
    · have e := hw2 r
      rw [TensorProduct.map_tmul, LinearMap.id_apply, ← TensorProduct.tmul_smul] at e
      exact sp_tmul_cancel T1.w_norm e
    · have e := hr2 r s hrs
      rw [TensorProduct.map_tmul, LinearMap.id_apply, ← TensorProduct.tmul_zero T2.V T1.w] at e
      exact sp_tmul_cancel T1.w_norm e
  obtain ⟨-, c, hc⟩ := KType.hw_unique T2 hy0 h
  exact ⟨c, by rw [hc, TensorProduct.tmul_smul]⟩

end ReciprocityTheory.ChartRestriction.TR.Weyl
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.SplitD

section

@[expose] public section

noncomputable section

open Matrix Finset TensorProduct

namespace ReciprocityTheory.ChartRestriction.TR.Weyl

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.HW

variable {n : ℕ} {ε : Fin n → Bool}

theorem sp_trace_piece {Λ' μ : Fin n → ℝ} (T : KType ε Λ') (T' : KType ε μ) (hμ : μ = Λ') (R : KRep ε)
    (S : Submodule ℂ R.V) (hS : S = ⊤) (φ : T'.V ≃ₗᵢ[ℂ] S)
    (hφ : ∀ (k : KG ε) (v : T'.V), (φ (T'.op k v) : R.V) = R.op k (φ v)) (k : KG ε) :
    LinearMap.trace ℂ T.V (T.op k : T.V →ₗ[ℂ] T.V) = LinearMap.trace ℂ R.V (R.op k : R.V →ₗ[ℂ] R.V) := by
  subst hμ hS
  obtain ⟨ψ, hψ, -, -⟩ := kType_unique T T'
  let Θ : T.V ≃ₗ[ℂ] R.V := ψ.toLinearEquiv ≪≫ₗ φ.toLinearEquiv ≪≫ₗ LinearEquiv.ofTop ⊤ rfl
  have hΘ : ∀ v, Θ (T.op k v) = R.op k (Θ v) := by
    intro v
    show ((φ (ψ (T.op k v)) : R.V)) = R.op k (φ (ψ v))
    rw [hψ, hφ]
  have e : (R.op k : R.V →ₗ[ℂ] R.V) = Θ.conj (T.op k : T.V →ₗ[ℂ] T.V) := by
    ext v
    rw [LinearEquiv.conj_apply_apply]
    show R.op k v = Θ (T.op k (Θ.symm v))
    rw [hΘ, LinearEquiv.apply_symm_apply]
  rw [e, LinearMap.trace_conj']

theorem sp_trace_of_rep {Λ' : Fin n → ℝ} (T : KType ε Λ') (R : KRep ε) (x : R.V) (hx : x ≠ 0)
    (hxw : Formalism.REAL.KHighest ε R.units Λ' x)
    (huniq : ∀ (μ : Fin n → ℝ) (y : R.V), y ≠ 0 → Formalism.REAL.KHighest ε R.units μ y → ∃ c : ℂ, y = c • x)
    (k : KG ε) :
    LinearMap.trace ℂ T.V (T.op k : T.V →ₗ[ℂ] T.V) = LinearMap.trace ℂ R.V (R.op k : R.V →ₗ[ℂ] R.V) := by
  obtain ⟨m, xs, μ, h1, h2, h3, -, -, h6⟩ := compRed n ε R
  choose c hc using fun i => huniq (μ i) (xs i) (h1 i).1 (h1 i).2
  have hc0 : ∀ i, c i ≠ 0 := by
    intro i h; apply (h1 i).1; rw [hc i, h, zero_smul]
  have hm0 : m ≠ 0 := by
    rintro rfl
    have : x ∈ (⨆ i : Fin 0, Formalism.REAL.kSpan ε R.units (xs i)) := by rw [h3]; trivial
    rw [iSup_of_empty, Submodule.mem_bot] at this
    exact hx this
  have hm1 : m ≤ 1 := by
    by_contra hm
    have hne : (⟨0, by omega⟩ : Fin m) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
    have h := h2 _ _ hne (xs ⟨0, by omega⟩) (Formalism.REAL.mem_compact_span_self (ε := ε) (F := R.units) _)
      (xs ⟨1, by omega⟩) (Formalism.REAL.mem_compact_span_self (ε := ε) (F := R.units) _)
    rw [hc, hc, inner_smul_left, inner_smul_right] at h
    refine (mul_ne_zero ((map_ne_zero _).mpr (hc0 _)) (mul_ne_zero (hc0 _) (inner_self_ne_zero.mpr hx))) h
  obtain rfl : m = 1 := by omega
  have htop : Formalism.REAL.kSpan ε R.units (xs 0) = ⊤ := by rw [← h3, iSup_unique]; rfl
  have hμ : μ 0 = Λ' := by
    funext a
    have e1 := (h1 0).2.1 a
    have e2 := hxw.1 a
    have hne : xs 0 ≠ 0 := (h1 0).1
    rw [hc 0, map_smul, e2, smul_comm] at e1
    have e3 : ((μ 0 a : ℝ) : ℂ) • xs 0 = ((Λ' a : ℝ) : ℂ) • xs 0 := by rw [hc 0]; exact e1.symm
    exact_mod_cast smul_left_injective ℂ hne e3
  obtain ⟨T', φ, -, hφ, -, -⟩ := h6 0
  exact sp_trace_piece T T' hμ R _ htop φ hφ k

end ReciprocityTheory.ChartRestriction.TR.Weyl
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.SpBlkSurj

section

@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.TR.Weyl

open ReciprocityTheory.ChartRestriction.DS.S7

open Matrix TensorProduct ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW

variable {n : ℕ} {ε : Fin n → Bool}

theorem sp_blk_surj' (ε : Fin n → Bool) (c : Bool) (a : Fin n) (h : ε a = c) : ∃ r, blk ε c r = a := by
  subst h
  exact sp_blk_surj ε a

theorem sp_tens_ne (Λ' : Fin n → ℝ) (T1 : KType (fun _ : Fin (cnt ε true) => true) (fun r => Λ' (blk ε true r)))
    (T2 : KType (fun _ : Fin (cnt ε false) => true) (fun r => Λ' (blk ε false r))) :
    (T1.w ⊗ₜ[ℂ] T2.w) ≠ 0 := by
  intro h
  have e := norm_tmul T1.w T2.w (𝕜 := ℂ)
  rw [h, norm_zero, T1.w_norm, T2.w_norm] at e
  norm_num at e

theorem sp_tens_hw (Λ' : Fin n → ℝ) (T1 : KType (fun _ : Fin (cnt ε true) => true) (fun r => Λ' (blk ε true r)))
    (T2 : KType (fun _ : Fin (cnt ε false) => true) (fun r => Λ' (blk ε false r))) :
    Formalism.REAL.KHighest ε (sp_rep T1 T2).units Λ' (T1.w ⊗ₜ[ℂ] T2.w) := by
  refine ⟨fun a => ?_, fun a b hab he => ?_⟩
  · cases hc : ε a
    · obtain ⟨r, rfl⟩ := sp_blk_surj' ε false a hc
      rw [sp_units_false, TensorProduct.map_tmul, LinearMap.id_apply]
      show T1.w ⊗ₜ (T2.dτ (single r r 1) T2.w) = _
      rw [T2.w_wt r, TensorProduct.tmul_smul]; rfl
    · obtain ⟨r, rfl⟩ := sp_blk_surj' ε true a hc
      rw [sp_units_true, TensorProduct.map_tmul, LinearMap.id_apply]
      show (T1.dτ (single r r 1) T1.w) ⊗ₜ T2.w = _
      rw [T1.w_wt r, ← TensorProduct.smul_tmul']; rfl
  · cases hc : ε a
    · obtain ⟨r, rfl⟩ := sp_blk_surj' ε false a hc
      obtain ⟨s, rfl⟩ := sp_blk_surj' ε false b (he ▸ hc)
      have hrs : r < s := (blk_strictMono ε false).lt_iff_lt.mp hab
      rw [sp_units_false, TensorProduct.map_tmul, LinearMap.id_apply]
      show T1.w ⊗ₜ (T2.dτ (single r s 1) T2.w) = 0
      rw [T2.w_hw r s hrs rfl, TensorProduct.tmul_zero]
    · obtain ⟨r, rfl⟩ := sp_blk_surj' ε true a hc
      obtain ⟨s, rfl⟩ := sp_blk_surj' ε true b (he ▸ hc)
      have hrs : r < s := (blk_strictMono ε true).lt_iff_lt.mp hab
      rw [sp_units_true, TensorProduct.map_tmul, LinearMap.id_apply]
      show (T1.dτ (single r s 1) T1.w) ⊗ₜ T2.w = 0
      rw [T1.w_hw r s hrs rfl, TensorProduct.zero_tmul]

theorem sp_tens_uniq {Λ1 : Fin (cnt ε true) → ℝ} {Λ2 : Fin (cnt ε false) → ℝ}
    (T1 : KType (fun _ : Fin (cnt ε true) => true) Λ1) (T2 : KType (fun _ : Fin (cnt ε false) => true) Λ2)
    (μ : Fin n → ℝ) (y : (sp_rep T1 T2).V) (hy : y ≠ 0)
    (h : Formalism.REAL.KHighest ε (sp_rep T1 T2).units μ y) : ∃ c : ℂ, y = c • (T1.w ⊗ₜ[ℂ] T2.w) := by
  obtain ⟨hwt, hr⟩ := h
  refine sp_ker T1 T2 y hy (fun r => μ (blk ε true r)) (fun r => μ (blk ε false r)) ?_ ?_ ?_ ?_
  · intro r; have e := hwt (blk ε true r); exact (sp_units_true T1 T2 r r y).symm.trans e
  · intro r s hrs
    have e := hr _ _ (blk_strictMono ε true hrs) (by rw [blk_mem ε true r, blk_mem ε true s])
    exact (sp_units_true T1 T2 r s y).symm.trans e
  · intro r; have e := hwt (blk ε false r); exact (sp_units_false T1 T2 r r y).symm.trans e
  · intro r s hrs
    have e := hr _ _ (blk_strictMono ε false hrs) (by rw [blk_mem ε false r, blk_mem ε false s])
    exact (sp_units_false T1 T2 r s y).symm.trans e

theorem sp_kChar (Λ' : Fin n → ℝ) (T : KType ε Λ')
    (T1 : KType (fun _ : Fin (cnt ε true) => true) (fun r => Λ' (blk ε true r)))
    (T2 : KType (fun _ : Fin (cnt ε false) => true) (fun r => Λ' (blk ε false r))) (k : KG ε) :
    kChar T k = kChar T1 (sp_proj ε true k) * kChar T2 (sp_proj ε false k) := by
  unfold kChar
  rw [sp_trace_of_rep T (sp_rep T1 T2) _ (sp_tens_ne Λ' T1 T2) (sp_tens_hw Λ' T1 T2)
    (fun μ y hy h => sp_tens_uniq T1 T2 μ y hy h) k, sp_rep_op]
  rw [show ((mapL (T1.op (sp_proj ε true k)) (T2.op (sp_proj ε false k)) : _ →L[ℂ] _) : _ →ₗ[ℂ] _) =
      TensorProduct.map (T1.op (sp_proj ε true k) : T1.V →ₗ[ℂ] T1.V)
        (T2.op (sp_proj ε false k) : T2.V →ₗ[ℂ] T2.V) from toLinearMap_mapL _ _]
  exact LinearMap.trace_tensorProduct' _ _

theorem kCharGT_of (hU : UCharStatement) : KCharGTStatement := by
  intro n ε Λ hdom T k t hk
  have hd : ∀ c, ∀ a b : Fin (cnt ε c), a < b → (fun _ => true) a = (fun _ => true) b →
      (((Λ ∘ blk ε c) b : ℤ) : ℝ) ≤ (((Λ ∘ blk ε c) a : ℤ) : ℝ) :=
    fun c a b hab _ => by exact_mod_cast antitone_blk hdom c hab.le
  obtain ⟨T1⟩ := kType_exists_of_dom (fun _ : Fin (cnt ε true) => true)
    (fun r => (((Λ ∘ blk ε true) r : ℤ) : ℝ)) (fun a => ⟨_, rfl⟩) (hd true)
  obtain ⟨T2⟩ := kType_exists_of_dom (fun _ : Fin (cnt ε false) => true)
    (fun r => (((Λ ∘ blk ε false) r : ℤ) : ℝ)) (fun a => ⟨_, rfl⟩) (hd false)
  rw [sp_kChar (fun a => (Λ a : ℝ)) T T1 T2 k,
    hU _ _ (antitone_blk hdom true) T1 (sp_proj ε true k) (t ∘ blk ε true)
      (by rw [sp_toMK_proj, hk, sp_sub_diag]),
    hU _ _ (antitone_blk hdom false) T2 (sp_proj ε false k) (t ∘ blk ε false)
      (by rw [sp_toMK_proj, hk, sp_sub_diag])]

end ReciprocityTheory.ChartRestriction.TR.Weyl
end
end
end
