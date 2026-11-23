module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TopCompS
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.StarExpNegI
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TCMatB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.CategoryTheory.Category.Basic
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.StarExpNegI
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TCBlock
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TCCalc
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TCMatA
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TCMatB
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Topology.Algebra.Module.Multilinear.Basic
public import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.TypeStar
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.RingTheory.PiTensorProduct

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TopCompC

section

@[expose] public section

noncomputable section

open Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.TC

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def matrixBlockRestriction (s t : Finset (Fin n)) (x : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun a b => if a ∈ s ∧ b ∈ t then x a b else 0

def matrixBlockRestrictionLinear (s t : Finset (Fin n)) : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := matrixBlockRestriction s t
      map_add' := fun x y => by ext a b; simp only [matrixBlockRestriction, Matrix.add_apply]; split_ifs <;> simp
      map_smul' := fun c x => by
        ext a b; simp only [matrixBlockRestriction, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> simp }

@[simp] theorem block_part_linear_apply (s t : Finset (Fin n)) (x : Matrix (Fin n) (Fin n) ℂ) : matrixBlockRestrictionLinear s t x = matrixBlockRestriction s t x := rfl

def conjL (g : M2 n) (P Q R S : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →L[ℂ] M2 n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => g * (Cm n * fromBlocks (P x) (Q x) (R x) (S x) * CmI n)
      map_add' := fun x y => by
        simp only [map_add (f := _), ← fromBlocks_add, Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c x => by
        simp only [map_smul, RingHom.id_apply, ← fromBlocks_smul, Matrix.mul_smul, Matrix.smul_mul] }

@[simp] theorem conjL_apply (g : M2 n) (P Q R S : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ)
    (x : Matrix (Fin n) (Fin n) ℂ) : conjL g P Q R S x = g * (Cm n * fromBlocks (P x) (Q x) (R x) (S x) * CmI n) := rfl

def rotL (g : M2 n) (j : ℕ) (θ : ℝ) : Matrix (Fin n) (Fin n) ℂ →L[ℂ] M2 n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun H => g * (rot j θ * fromBlocks 0 H 0 0 * (rot j θ)⁻¹)
      map_add' := fun x y => by
        rw [show fromBlocks (0 : Matrix (Fin n) (Fin n) ℂ) (x + y) 0 0 = fromBlocks 0 x 0 0 + fromBlocks 0 y 0 0 by
          rw [fromBlocks_add]; simp]
        simp only [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c x => by
        rw [show fromBlocks (0 : Matrix (Fin n) (Fin n) ℂ) (c • x) 0 0 = c • fromBlocks 0 x 0 0 by
          rw [fromBlocks_smul]; simp]
        simp only [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul] }

@[simp] theorem rotL_apply (g : M2 n) (j : ℕ) (θ : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) :
    rotL g j θ H = g * (rot j θ * fromBlocks 0 H 0 0 * (rot j θ)⁻¹) := rfl

theorem nU_eq (H : Matrix (Fin n) (Fin n) ℂ) : nU H = 1 + fromBlocks 0 H 0 0 := by
  rw [nU, ← fromBlocks_one, fromBlocks_add]; simp

theorem rot_mul_inv (j : ℕ) (θ : ℝ) : rot (n := n) j θ * (rot j θ)⁻¹ = 1 := inG_mul_inv (rot_inG j θ)

theorem rot_nU (g : M2 n) (j : ℕ) (θ : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) :
    g * rot j θ * nU H * (rot j θ)⁻¹ = g + rotL g j θ H := by
  simp only [nU_eq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_assoc, rot_mul_inv, rotL_apply]

theorem rotL_single (g : M2 n) (j : ℕ) (θ : ℝ) (r s : Fin n) :
    Complex.exp (2 * θ * Complex.I) • rotL g j θ (single r s 1) =
      g * (Cm n * zLow j r s * CmI n) + Complex.exp (2 * θ * Complex.I) • (g * (Cm n * zMid j r s * CmI n)) +
        Complex.exp (2 * θ * Complex.I) ^ 2 • (g * (Cm n * zTop j r s * CmI n)) := by
  have hX : rot (n := n) j θ * fromBlocks 0 (single r s 1) 0 0 * (rot j θ)⁻¹ =
      rot j θ * nU (single r s 1) * (rot j θ)⁻¹ - 1 := by
    have h := rot_nU (1 : M2 n) j θ (single r s 1)
    simp only [Matrix.one_mul, rotL_apply] at h
    rw [h]
    abel
  rw [rotL_apply, hX, ← Matrix.mul_smul, rot_conj]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]

theorem block_part_single (s t : Finset (Fin n)) (r u : Fin n) :
    matrixBlockRestriction s t (single r u (1 : ℂ)) = if r ∈ s ∧ u ∈ t then single r u 1 else 0 := by
  ext a b
  by_cases h : r ∈ s ∧ u ∈ t
  · rw [if_pos h]
    simp only [matrixBlockRestriction, Matrix.single_apply]
    by_cases hab : r = a ∧ u = b
    · obtain ⟨rfl, rfl⟩ := hab
      simp [h]
    · simp [hab]
  · rw [if_neg h]
    simp only [matrixBlockRestriction, Matrix.single_apply, Matrix.zero_apply]
    by_cases hab : r = a ∧ u = b
    · obtain ⟨rfl, rfl⟩ := hab
      simp [h]
    · simp [hab]

theorem memB {j : ℕ} {a : Fin n} : a ∈ blkB j ↔ a ∉ blkA j := by simp [blkB]

def topL (g : M2 n) (j : ℕ) : Matrix (Fin n) (Fin n) ℂ →L[ℂ] M2 n :=
  conjL g (((2 * Complex.I)⁻¹ : ℂ) • matrixBlockRestrictionLinear (blkA j) (blkB j)) (((2 * Complex.I)⁻¹ : ℂ) • matrixBlockRestrictionLinear (blkA j) (blkA j))
    ((-(2 * Complex.I)⁻¹ : ℂ) • matrixBlockRestrictionLinear (blkB j) (blkB j)) ((-(2 * Complex.I)⁻¹ : ℂ) • matrixBlockRestrictionLinear (blkB j) (blkA j))

theorem topL_single (g : M2 n) (j : ℕ) (r s : Fin n) : topL g j (single r s 1) = g * (Cm n * zTop j r s * CmI n) := by
  simp only [topL, conjL_apply, ContinuousLinearMap.smul_apply, block_part_linear_apply, block_part_single, zTop]
  congr 2
  by_cases hr : r ∈ blkA j <;> by_cases hs : s ∈ blkA j <;>
    simp [hr, hs, memB, fromBlocks_smul, fromBlocks_neg]

end PositivityTheory.Rg.Sw.LVs.TC
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TopCompB

section

@[expose] public section

noncomputable section

open Polynomial

namespace PositivityTheory.Rg.Sw.LVs.TC

theorem ml_expand {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {k : ℕ}
    (A : ContinuousMultilinearMap ℂ (fun _ : Fin k => V) ℂ) (Y : Fin k → Fin 3 → V) (z : ℂ) :
    A (fun i => Y i 0 + z • Y i 1 + z ^ 2 • Y i 2) =
      ∑ f : Fin k → Fin 3, z ^ (∑ i, (f i : ℕ)) * A (fun i => Y i (f i)) := by
  have h : (fun i => Y i 0 + z • Y i 1 + z ^ 2 • Y i 2) = fun i => ∑ w : Fin 3, z ^ (w : ℕ) • Y i w := by
    funext i; simp [Fin.sum_univ_three]

  rw [h, ContinuousMultilinearMap.map_sum]
  refine Finset.sum_congr (by simp) fun f _ => ?_
  rw [ContinuousMultilinearMap.map_smul_univ, Finset.prod_pow_eq_pow_sum, smul_eq_mul]

theorem sum_eq_top {k : ℕ} (f : Fin k → Fin 3) (h : ∑ i, (f i : ℕ) = 2 * k) : ∀ i, f i = 2 := by
  by_contra hne
  push Not at hne
  obtain ⟨i, hi⟩ := hne
  have hle : ∀ x, (f x : ℕ) ≤ 2 := fun x => by omega
  have hlt : (f i : ℕ) < 2 := by
    rcases Nat.lt_or_ge (f i : ℕ) 2 with h' | h'
    · exact h'
    · exact absurd (Fin.ext (by simp; omega)) hi
  have : ∑ x, (f x : ℕ) < ∑ _x : Fin k, 2 :=
    Finset.sum_lt_sum (fun x _ => hle x) ⟨i, Finset.mem_univ _, hlt⟩
  simp at this
  omega

theorem infinite_circle : Set.Infinite (Set.range fun θ : ℝ => Complex.exp (2 * θ * Complex.I)) := by
  have hinj : Function.Injective fun m : ℕ => Complex.exp (2 * ((1 : ℝ) / (m + 2) : ℝ) * Complex.I) := by
    intro a b hab
    have hre := congrArg Complex.re hab
    simp only at hre
    have e1 : ∀ x : ℝ, (Complex.exp (2 * (x : ℂ) * Complex.I)).re = Real.cos (2 * x) := by
      intro x
      rw [show 2 * (x : ℂ) * Complex.I = ((2 * x : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.exp_ofReal_mul_I_re]
    rw [e1, e1] at hre
    have ha : 2 * ((1 : ℝ) / (a + 2)) ∈ Set.Icc 0 Real.pi := by
      constructor
      · positivity
      · have : (2 : ℝ) * (1 / (a + 2)) ≤ 1 := by
          rw [mul_one_div, div_le_one (by positivity)]; linarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a)]
        linarith [Real.pi_gt_three]
    have hb : 2 * ((1 : ℝ) / (b + 2)) ∈ Set.Icc 0 Real.pi := by
      constructor
      · positivity
      · have : (2 : ℝ) * (1 / (b + 2)) ≤ 1 := by
          rw [mul_one_div, div_le_one (by positivity)]; linarith [(Nat.cast_nonneg b : (0 : ℝ) ≤ b)]
        linarith [Real.pi_gt_three]
    have := Real.injOn_cos ha hb hre
    have h2 : (1 : ℝ) / (a + 2) = 1 / (b + 2) := by linarith
    rw [div_eq_div_iff (by positivity) (by positivity)] at h2
    exact_mod_cast (by linarith : (a : ℝ) = b)
  refine Set.infinite_of_injective_forall_mem hinj fun m => ⟨_, rfl⟩

theorem top_vanish {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {k : ℕ} {ι : Type*} [Fintype ι]
    (A : ContinuousMultilinearMap ℂ (fun _ : Fin k => V) ℂ) (sg : ι → ℂ) (Y : ι → Fin k → Fin 3 → V)
    (h : ∀ θ : ℝ, ∑ σ, sg σ * A (fun i => Y σ i 0 + Complex.exp (2 * θ * Complex.I) • Y σ i 1 +
      Complex.exp (2 * θ * Complex.I) ^ 2 • Y σ i 2) = 0) :
    ∑ σ, sg σ * A (fun i => Y σ i 2) = 0 := by
  set Q : ℂ[X] := ∑ σ, C (sg σ) * ∑ f : Fin k → Fin 3, C (A (fun i => Y σ i (f i))) * X ^ (∑ i, (f i : ℕ)) with hQ
  have heval : ∀ z : ℂ, Q.eval z = ∑ σ, sg σ * A (fun i => Y σ i 0 + z • Y σ i 1 + z ^ 2 • Y σ i 2) := by
    intro z
    simp only [hQ, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [ml_expand]
    congr 1
    refine Finset.sum_congr rfl fun f _ => ?_
    ring
  have hQ0 : Q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono ?_ infinite_circle
    rintro _ ⟨θ, rfl⟩
    simp only [Set.mem_ofPred_eq, IsRoot.def, heval, h θ]
  have hc := congrArg (fun p : ℂ[X] => p.coeff (2 * k)) hQ0
  simp only [hQ, finsetSum_coeff, coeff_C_mul, coeff_X_pow, coeff_zero] at hc
  rw [← hc]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  rw [Finset.sum_eq_single (fun _ => 2)]
  · simp only [Fin.isValue, Fin.val_two, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    rw [if_pos (by ring), mul_one]
  · intro f _ hf
    rw [if_neg, mul_zero]
    intro h2
    exact hf (funext (sum_eq_top f h2.symm))
  · simp

end PositivityTheory.Rg.Sw.LVs.TC
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TopComp

section

@[expose] public section

noncomputable section

open Matrix
open scoped ContDiff Topology

namespace PositivityTheory.Rg.Sw.LVs.TC

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem detD_affine (hA : IterAffine) {F : M2 n → ℂ} {Ω : Set (M2 n)} (hΩ : IsOpen Ω) (hF : ContDiffOn ℂ ∞ F Ω)
    {g : M2 n} (hg : g ∈ Ω) (L : Matrix (Fin n) (Fin n) ℂ →L[ℂ] M2 n) :
    detD (fun t => F (g + L t)) = ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) *
      iteratedFDeriv ℂ (Fintype.card (Fin n)) F g (fun i => L (single ((Fintype.equivFin (Fin n)).symm i)
        (σ ((Fintype.equivFin (Fin n)).symm i)) 1)) := by
  unfold detD
  refine Finset.sum_congr rfl fun σ _ => ?_
  erw [hA (M2 n) (Matrix (Fin n) (Fin n) ℂ) F Ω hΩ hF g hg L]
  rfl

theorem top_zero (hA : IterAffine) {j : ℕ} {F : M2 n → ℂ} {Ω : Set (M2 n)} (hΩ : IsOpen Ω) (hG : GSet n ⊆ Ω)
    (hF : ContDiffOn ℂ ∞ F Ω) (hhyp : ∀ a b, InG a → InG b → detD (fun H => F (a * nU H * b)) = 0)
    {g : M2 n} (hg : InG g) : detD (fun t => F (g + topL g j t)) = 0 := by
  have hgΩ : g ∈ Ω := hG hg
  have key : ∀ θ : ℝ, ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) *
      iteratedFDeriv ℂ (Fintype.card (Fin n)) F g (fun i => rotL g j θ
        (single ((Fintype.equivFin (Fin n)).symm i) (σ ((Fintype.equivFin (Fin n)).symm i)) 1)) = 0 := by
    intro θ
    have h0 := hhyp (g * rot j θ) (rot j θ)⁻¹ (TC.inG_mul hg (rot_inG j θ)) (inG_inv (rot_inG j θ))
    simp only [rot_nU] at h0
    rwa [detD_affine hA hΩ hF hgΩ] at h0
  rw [detD_affine hA hΩ hF hgΩ]
  simp only [topL_single]
  have hv := top_vanish (iteratedFDeriv ℂ (Fintype.card (Fin n)) F g)
    (fun σ : Equiv.Perm (Fin n) => (Equiv.Perm.sign σ : ℂ))
    (fun σ i m => g * (Cm n * (![zLow j, zMid j, zTop j] m) ((Fintype.equivFin (Fin n)).symm i)
      (σ ((Fintype.equivFin (Fin n)).symm i)) * CmI n)) ?_
  · simpa using hv
  intro θ
  have h1 : ∀ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) *
      iteratedFDeriv ℂ (Fintype.card (Fin n)) F g (fun i =>
        g * (Cm n * zLow j ((Fintype.equivFin (Fin n)).symm i) (σ ((Fintype.equivFin (Fin n)).symm i)) * CmI n)
        + Complex.exp (2 * ↑θ * Complex.I) • (g * (Cm n * zMid j ((Fintype.equivFin (Fin n)).symm i)
          (σ ((Fintype.equivFin (Fin n)).symm i)) * CmI n))
        + Complex.exp (2 * ↑θ * Complex.I) ^ 2 • (g * (Cm n * zTop j ((Fintype.equivFin (Fin n)).symm i)
          (σ ((Fintype.equivFin (Fin n)).symm i)) * CmI n)))
      = Complex.exp (2 * ↑θ * Complex.I) ^ Fintype.card (Fin n) * ((Equiv.Perm.sign σ : ℂ) *
        iteratedFDeriv ℂ (Fintype.card (Fin n)) F g (fun i => rotL g j θ
          (single ((Fintype.equivFin (Fin n)).symm i) (σ ((Fintype.equivFin (Fin n)).symm i)) 1))) := by
    intro σ
    simp_rw [← rotL_single]
    rw [ContinuousMultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]
    ring
  refine (Finset.sum_congr rfl fun σ _ => h1 σ).trans ?_
  rw [← Finset.mul_sum, key θ, mul_zero]

theorem block_part_embedding_first (j : ℕ) (T : Matrix (blkA (n := n) j) (blkA j) ℂ) (S : Matrix (blkB (n := n) j) (blkB j) ℂ) :
    matrixBlockRestriction (blkA j) (blkA j) (embOn (blkA j) T + embOn (blkB j) S) = embOn (blkA j) T := by
  ext a b
  by_cases ha : a ∈ blkA j <;> by_cases hb : b ∈ blkA j <;>
    simp [matrixBlockRestriction, embOn, blkB, ha, hb]

theorem block_part_embedding_second (j : ℕ) (T : Matrix (blkA (n := n) j) (blkA j) ℂ) (S : Matrix (blkB (n := n) j) (blkB j) ℂ) :
    matrixBlockRestriction (blkB j) (blkB j) (embOn (blkA j) T + embOn (blkB j) S) = embOn (blkB j) S := by
  ext a b
  by_cases ha : a ∈ blkA j <;> by_cases hb : b ∈ blkA j <;>
    simp [matrixBlockRestriction, embOn, blkB, ha, hb]

theorem block_part_diagonal_first (j : ℕ) (c c' : ℂ) (t : Matrix (Fin n) (Fin n) ℂ) :
    matrixBlockRestriction (blkA j) (blkA j) (bdiag j c c' t) = c • matrixBlockRestriction (blkA j) (blkA j) t := by
  ext a b
  by_cases ha : a ∈ blkA j <;> by_cases hb : b ∈ blkA j <;>
    simp [matrixBlockRestriction, bdiag, blkB, ha, hb]

theorem block_part_diagonal_second (j : ℕ) (c c' : ℂ) (t : Matrix (Fin n) (Fin n) ℂ) :
    matrixBlockRestriction (blkB j) (blkB j) (bdiag j c c' t) = c' • matrixBlockRestriction (blkB j) (blkB j) t := by
  ext a b
  by_cases ha : a ∈ blkA j <;> by_cases hb : b ∈ blkA j <;>
    simp [matrixBlockRestriction, bdiag, blkB, ha, hb]

theorem g_mX (g : M2 n) (P Q R S : Matrix (Fin n) (Fin n) ℂ) :
    g * mX (1 + P) Q R (1 + S) = g + g * (Cm n * fromBlocks P Q R S * CmI n) := by
  have h : fromBlocks (1 + P) Q R (1 + S) = (1 : M2 n) + fromBlocks P Q R S := by
    rw [← fromBlocks_one, fromBlocks_add]
    simp
  simp only [mX, cm_inv, h, mul_add, add_mul, mul_one, cm_mul_cmI]

theorem supp_smul {s t : Finset (Fin n)} (c : ℂ) (x : Matrix (Fin n) (Fin n) ℂ) :
    ∀ a b, (c • matrixBlockRestriction s t x) a b ≠ 0 → a ∈ s ∧ b ∈ t := by
  intro a b h
  by_contra hn
  apply h
  simp only [Matrix.smul_apply, matrixBlockRestriction, if_neg hn, smul_zero]

private theorem eq_mul_mX_mul_mX_blockEntries (g : M2 n) (j : ℕ) (t : Matrix (Fin n) (Fin n) ℂ) :
    g + topL g j t = g * mX 1 ((2 * Complex.I)⁻¹ • matrixBlockRestriction (blkA j) (blkA j) t)
      ((-(2 * Complex.I)⁻¹) • matrixBlockRestriction (blkB j) (blkB j) t) 1 *
      mX (1 + (2 * Complex.I)⁻¹ • matrixBlockRestriction (blkA j) (blkB j) t) 0 0
        (1 + (-(2 * Complex.I)⁻¹) • matrixBlockRestriction (blkB j) (blkA j) t) := by
  rw [mul_assoc, ← mX_factor j _ _ _ _ (supp_smul _ _) (supp_smul _ _) (supp_smul _ _) (supp_smul _ _), g_mX]
  simp only [topL, conjL_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply, block_part_linear_apply,
    neg_smul]

private theorem conjL_bdiag_eq_mul_mX_blockEntries (g : M2 n) (j : ℕ) (t : Matrix (Fin n) (Fin n) ℂ) :
    g + conjL g 0 (matrixBlockRestrictionLinear (blkA j) (blkA j)) (matrixBlockRestrictionLinear (blkB j) (blkB j)) 0
      (bdiag j (2 * Complex.I)⁻¹ (-(2 * Complex.I)⁻¹) t) =
    g * mX 1 ((2 * Complex.I)⁻¹ • matrixBlockRestriction (blkA j) (blkA j) t)
      ((-(2 * Complex.I)⁻¹) • matrixBlockRestriction (blkB j) (blkB j) t) 1 := by
  have h := g_mX g 0 ((2 * Complex.I)⁻¹ • matrixBlockRestriction (blkA j) (blkA j) t)
    ((-(2 * Complex.I)⁻¹) • matrixBlockRestriction (blkB j) (blkB j) t) 0
  simp only [add_zero] at h
  rw [h, conjL_apply]
  simp only [ContinuousLinearMap.zero_apply, block_part_linear_apply, block_part_diagonal_first, block_part_diagonal_second]

private theorem comp_blockEntries_eq (g : M2 n) (j : ℕ) (T : Matrix (blkA (n := n) j) (blkA j) ℂ)
    (S : Matrix (blkB (n := n) j) (blkB j) ℂ) :
    g * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1 =
      g + conjL g 0 (matrixBlockRestrictionLinear (blkA j) (blkA j)) (matrixBlockRestrictionLinear (blkB j) (blkB j)) 0
        (embOn (blkA j) T + embOn (blkB j) S) := by
  have h := g_mX g 0 (embOn (blkA j) T) (embOn (blkB j) S) 0
  simp only [add_zero] at h
  rw [h, conjL_apply]
  simp only [ContinuousLinearMap.zero_apply, block_part_linear_apply, block_part_embedding_first, block_part_embedding_second]


theorem topComp_of (hA : IterAffine) (hB : DetDBlock) : TopComp := by
  intro n j F Ω hΩ hG hF hinv hhyp g hg
  have hgΩ : g ∈ Ω := hG hg
  have hc : (2 * Complex.I)⁻¹ ≠ 0 := by simp [Complex.I_ne_zero]
  have hLc : Continuous fun t : Matrix (Fin n) (Fin n) ℂ =>
      g + conjL g 0 (matrixBlockRestrictionLinear (blkA j) (blkA j)) (matrixBlockRestrictionLinear (blkB j) (blkB j)) 0 t :=
    continuous_const.add (ContinuousLinearMap.continuous _)
  have hΩ' : IsOpen ((fun t : Matrix (Fin n) (Fin n) ℂ =>
      g + conjL g 0 (matrixBlockRestrictionLinear (blkA j) (blkA j)) (matrixBlockRestrictionLinear (blkB j) (blkB j)) 0 t) ⁻¹' Ω) := hΩ.preimage hLc
  have h0 : (0 : Matrix (Fin n) (Fin n) ℂ) ∈ (fun t : Matrix (Fin n) (Fin n) ℂ =>
      g + conjL g 0 (matrixBlockRestrictionLinear (blkA j) (blkA j)) (matrixBlockRestrictionLinear (blkB j) (blkB j)) 0 t) ⁻¹' Ω := by
    simp only [Set.mem_preimage, map_zero, add_zero]
    exact hgΩ
  have hψ : ContDiffOn ℂ ∞ (fun t : Matrix (Fin n) (Fin n) ℂ =>
      F (g + conjL g 0 (matrixBlockRestrictionLinear (blkA j) (blkA j)) (matrixBlockRestrictionLinear (blkB j) (blkB j)) 0 t))
      ((fun t : Matrix (Fin n) (Fin n) ℂ =>
        g + conjL g 0 (matrixBlockRestrictionLinear (blkA j) (blkA j)) (matrixBlockRestrictionLinear (blkB j) (blkB j)) 0 t) ⁻¹' Ω) :=
    hF.comp (contDiff_const.add (ContinuousLinearMap.contDiff _)).contDiffOn (fun t ht => ht)
  have hmain := hB n j (2 * Complex.I)⁻¹ (-(2 * Complex.I)⁻¹) _ _ hΩ' h0 hψ
  have hzero : (detD fun t : Matrix (Fin n) (Fin n) ℂ =>
      F (g + conjL g 0 (matrixBlockRestrictionLinear (blkA j) (blkA j)) (matrixBlockRestrictionLinear (blkB j) (blkB j)) 0
        (bdiag j (2 * Complex.I)⁻¹ (-(2 * Complex.I)⁻¹) t))) = 0 := by
    refine Eq.trans ?_ (top_zero (j := j) hA hΩ hG hF hhyp hg)
    have hev : (fun t : Matrix (Fin n) (Fin n) ℂ =>
        F (g + conjL g 0 (matrixBlockRestrictionLinear (blkA j) (blkA j)) (matrixBlockRestrictionLinear (blkB j) (blkB j)) 0
          (bdiag j (2 * Complex.I)⁻¹ (-(2 * Complex.I)⁻¹) t))) =ᶠ[𝓝 0]
        fun t => F (g + topL g j t) := by
      have e1 : ∀ᶠ t in 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ), g + topL g j t ∈ Ω :=
        (continuous_const.add (topL g j).continuous).continuousAt.preimage_mem_nhds
          (by simpa using hΩ.mem_nhds hgΩ)
      have hc2 : Continuous fun t : Matrix (Fin n) (Fin n) ℂ => g + conjL g 0 (matrixBlockRestrictionLinear (blkA j) (blkA j))
          (matrixBlockRestrictionLinear (blkB j) (blkB j)) 0 (bdL j (2 * Complex.I)⁻¹ (-(2 * Complex.I)⁻¹) t) :=
        continuous_const.add ((ContinuousLinearMap.continuous _).comp (ContinuousLinearMap.continuous _))
      have e2 : ∀ᶠ t in 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ), g + conjL g 0 (matrixBlockRestrictionLinear (blkA j) (blkA j))
          (matrixBlockRestrictionLinear (blkB j) (blkB j)) 0 (bdL j (2 * Complex.I)⁻¹ (-(2 * Complex.I)⁻¹) t) ∈ Ω := by
        have hm : Ω ∈ 𝓝 (g + conjL g 0 (matrixBlockRestrictionLinear (blkA j) (blkA j))
            (matrixBlockRestrictionLinear (blkB j) (blkB j)) 0 (bdL j (2 * Complex.I)⁻¹ (-(2 * Complex.I)⁻¹) 0)) := by
          rw [map_zero, map_zero, add_zero]
          exact hΩ.mem_nhds hgΩ
        exact hc2.continuousAt.preimage_mem_nhds hm
      filter_upwards [e1, e2] with t ht1 ht2
      rw [bdL_apply, conjL_bdiag_eq_mul_mX_blockEntries] at ht2
      rw [eq_mul_mX_mul_mX_blockEntries] at ht1
      rw [conjL_bdiag_eq_mul_mX_blockEntries, eq_mul_mX_mul_mX_blockEntries]
      exact (hinv _ _ _ ht1 ht2 (supp_smul _ _) (supp_smul _ _)).symm
    have hI := (hev.iteratedFDeriv ℂ (Fintype.card (Fin n))).eq_of_nhds
    unfold detD
    rw [hI]
  rw [hzero] at hmain
  have hX := (mul_eq_zero.mp hmain.symm).resolve_left
    (mul_ne_zero (pow_ne_zero _ hc) (pow_ne_zero _ (neg_ne_zero.mpr hc)))
  simpa only [comp_blockEntries_eq] using hX

theorem topComp : TopComp := topComp_of iterAffine (detDBlock_of iterAffine iterSymm iterNested)

end PositivityTheory.Rg.Sw.LVs.TC

namespace PositivityTheory.Rg.Sw.LVs

theorem topComp : TopComp := TC.topComp

end PositivityTheory.Rg.Sw.LVs
end
end
end
