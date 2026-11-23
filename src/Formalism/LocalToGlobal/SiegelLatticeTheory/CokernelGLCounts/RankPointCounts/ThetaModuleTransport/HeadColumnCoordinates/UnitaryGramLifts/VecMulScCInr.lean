module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.ThetaC
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
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.ScaleB
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.ThetaGC
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.LiftMemHead
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.ENatToNat

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.FGInvariant

section

@[expose] public section

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

section ScaleA3

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}

def phiEq (A A' : Matrix (Ix r) (Ix r) O) (h1 : A * A' = 1) (h2 : A' * A = 1) : (Ix r → O) ≃ₗ[O] (Ix r → O) :=
  LinearEquiv.ofLinear (Matrix.vecMulLinear A) (Matrix.vecMulLinear A')
    (LinearMap.ext fun x => by
      simp only [LinearMap.comp_apply, Matrix.vecMulLinear_apply, Matrix.vecMul_vecMul, h2, Matrix.vecMul_one,
        LinearMap.id_apply])
    (LinearMap.ext fun x => by
      simp only [LinearMap.comp_apply, Matrix.vecMulLinear_apply, Matrix.vecMul_vecMul, h1, Matrix.vecMul_one,
        LinearMap.id_apply])

theorem coe_vecMul (Y : Ix r → O) (A : Matrix (Ix r) (Ix r) O) (j : Ix r) :
    ((Matrix.vecMul Y A j : O) : E) = Matrix.vecMul (fun i => (Y i : E)) (A.map O.subtype) j := by
  simp [Matrix.vecMul, dotProduct]

theorem relC_fwd (G G' C C' : Matrix (Ix r) (Ix r) E) (hC : C * C' = 1) (hG : G' = C.transpose * G * C.map cj)
    (A : Matrix (Ix r) (Ix r) O) (hA : A.map O.subtype = C.map cj) (hC'O : ∀ i j, C' j i ∈ O)
    (Y : Ix r → O) (hY : ∃ c : Ix r → O, ∀ j, (Y j : E) = ∑ i, (c i : E) * G i j) :
    ∃ c : Ix r → O, ∀ j, ((Matrix.vecMul Y A j : O) : E) = ∑ i, (c i : E) * G' i j := by
  obtain ⟨c, hc⟩ := hY
  let c' : Ix r → O := fun i => ⟨∑ k, (c k : E) * C' i k, Subring.sum_mem _ fun k _ => O.mul_mem (c k).2 (hC'O k i)⟩
  refine ⟨c', fun j => ?_⟩
  have hcE : (fun i => (c' i : E)) = Matrix.vecMul (fun k => (c k : E)) C'.transpose := by
    funext i; simp [c', Matrix.vecMul, dotProduct]
  have hYE : (fun i => (Y i : E)) = Matrix.vecMul (fun k => (c k : E)) G := by
    funext j; rw [hc j]; simp [Matrix.vecMul, dotProduct]
  rw [coe_vecMul, hA, hYE]
  show _ = Matrix.vecMul (fun i => (c' i : E)) G' j
  rw [hcE, hG, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    ← Matrix.transpose_mul, hC, Matrix.transpose_one, Matrix.one_mul]

def fG (G : Matrix (Ix r) (Ix r) E) (Y W : Ix r → E) : E := ∑ i, ∑ j, Y i * G⁻¹ i j * cj (W j)

theorem fG_eq (G : Matrix (Ix r) (Ix r) E) (Y W : Ix r → E) :
    fG cj G Y W = Matrix.vecMul Y G⁻¹ ⬝ᵥ (fun j => cj (W j)) := by
  unfold fG
  simp only [dotProduct, Matrix.vecMul, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem fG_invariant (hcj : ∀ x, cj (cj x) = x) (G G' C : Matrix (Ix r) (Ix r) E)
    (hG : G' = C.transpose * G * C.map cj) (hCu : IsUnit C.det) (hCcu : IsUnit (C.map cj).det) (Y W : Ix r → E) :
    fG cj G' (Matrix.vecMul Y (C.map cj)) (Matrix.vecMul W (C.map cj)) = fG cj G Y W := by
  have hcw : (fun j => cj (Matrix.vecMul W (C.map cj) j)) = C.transpose.mulVec fun j => cj (W j) := by
    funext j; simp [Matrix.vecMul, Matrix.mulVec, dotProduct, map_sum, map_mul, hcj, mul_comm]
  have hCt : IsUnit C.transpose.det := by rw [Matrix.det_transpose]; exact hCu
  rw [fG_eq, fG_eq, hcw, hG, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.vecMul_vecMul, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hCcu, Matrix.one_mul, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hCt, Matrix.mul_one]

end ScaleA3

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.ScCApplyInlInl

section

@[expose] public section

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

section ScaleA

variable {E : Type} [CommRing E] (cj : E →+* E) (qi : E) {r : ℕ}

def scC (r : ℕ) (α β : E) : Matrix (Ix r) (Ix r) E :=
  Matrix.fromBlocks 1 (β • liftE r) 0 (dlast r α)

theorem scC_apply_inl_inl (α β : E) (a b : Fin (r + 1)) : scC r α β (Sum.inl a) (Sum.inl b) = if a = b then 1 else 0 := by
  simp [scC, Matrix.one_apply]
theorem scC_apply_inl_inr (α β : E) (a b : Fin (r + 1)) :
    scC r α β (Sum.inl a) (Sum.inr b) = if a = Fin.last r ∧ b = Fin.last r then β else 0 := by
  simp [scC, liftE, smul_ite]
theorem scC_apply_inr_inl (α β : E) (a b : Fin (r + 1)) : scC r α β (Sum.inr a) (Sum.inl b) = 0 := by
  simp [scC]
theorem scC_apply_inr_inr (α β : E) (a b : Fin (r + 1)) :
    scC r α β (Sum.inr a) (Sum.inr b) = if a = b then (if a = Fin.last r then α else 1) else 0 := by
  simp [scC, dlast, Matrix.diagonal_apply]

theorem scC_left_inl (α β : E) (G : Matrix (Ix r) (Ix r) E) (a : Fin (r + 1)) (j : Ix r) :
    ((scC r α β).transpose * G) (Sum.inl a) j = G (Sum.inl a) j := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type, scC_apply_inl_inl, scC_apply_inr_inl,
    zero_mul, Finset.sum_const_zero, add_zero, ite_mul, one_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem scC_left_inr (α β : E) (G : Matrix (Ix r) (Ix r) E) (a : Fin (r + 1)) (j : Ix r) :
    ((scC r α β).transpose * G) (Sum.inr a) j =
      (if a = Fin.last r then α else 1) * G (Sum.inr a) j +
        (if a = Fin.last r then β * G (Sum.inl (Fin.last r)) j else 0) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type, scC_apply_inl_inr, scC_apply_inr_inr]
  by_cases ha : a = Fin.last r
  · subst ha
    simp [ite_mul, Finset.sum_ite_eq', add_comm]
  · simp [ha, ite_mul, Finset.sum_ite_eq]

theorem scC_right_inl (α β : E) (X : Matrix (Ix r) (Ix r) E) (i : Ix r) (b : Fin (r + 1)) :
    (X * (scC r α β).map cj) i (Sum.inl b) = X i (Sum.inl b) := by
  simp only [Matrix.mul_apply, Matrix.map_apply, Fintype.sum_sum_type, scC_apply_inl_inl, scC_apply_inr_inl, map_zero,
    mul_zero, Finset.sum_const_zero, add_zero, apply_ite cj, map_one, mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]

theorem scC_right_inr (α β : E) (X : Matrix (Ix r) (Ix r) E) (i : Ix r) (b : Fin (r + 1)) :
    (X * (scC r α β).map cj) i (Sum.inr b) =
      X i (Sum.inr b) * cj (if b = Fin.last r then α else 1) +
        (if b = Fin.last r then X i (Sum.inl (Fin.last r)) * cj β else 0) := by
  simp only [Matrix.mul_apply, Matrix.map_apply, Fintype.sum_sum_type, scC_apply_inl_inr, scC_apply_inr_inr]
  by_cases hb : b = Fin.last r
  · subst hb
    simp [apply_ite cj, mul_ite, Finset.sum_ite_eq', add_comm]
  · simp [hb, apply_ite cj, mul_ite, Finset.sum_ite_eq']

theorem gramG_scale (hcj : ∀ x, cj (cj x) = x) (α T T' : E) (hα : α * cj α = 1)
    (hqi : cj qi = qi) (hT : cj T = T) (hT' : cj T' = T') (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    gramG cj qi (Zh * dlast r α) T T' =
      (scC r α ((α - 1) * qi)).transpose * gramG cj qi Zh T T' * (scC r α ((α - 1) * qi)).map cj := by
  ext i j
  rcases i with a | a <;> rcases j with b | b
  · rw [scC_right_inl, scC_left_inl]
    simp [gramG]
  · rw [scC_right_inr, scC_left_inl, scC_left_inl]
    by_cases ha : a = Fin.last r <;> by_cases hb : b = Fin.last r <;>
      simp [gramG, cor, dlast, Matrix.mul_diagonal, ha, hb, map_mul, map_sub, map_add (f := _), hqi, hT] <;> ring
  · rw [scC_right_inl, scC_left_inr]
    by_cases ha : a = Fin.last r <;> by_cases hb : b = Fin.last r <;>
      simp [gramG, cor, dlast, Matrix.mul_diagonal, ha, hb] <;> ring
  · rw [scC_right_inr, scC_left_inr, scC_left_inr]
    by_cases ha : a = Fin.last r <;> by_cases hb : b = Fin.last r <;>
      simp [gramG, cor, dlast, Matrix.mul_diagonal, ha, hb, map_mul, map_sub, map_add (f := _), map_neg, hqi, hT, hT',
        hcj] <;> first | ring1 | linear_combination (qi ^ 2 * T') * hα | linear_combination (qi * qi * T') * hα | linear_combination (-(qi ^ 2 * T')) * hα

end ScaleA

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.ScCMulInv

section

@[expose] public section

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

section ScaleA2

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}

def toOm {ι : Type} (X : Matrix ι ι E) (h : ∀ i j, X i j ∈ O) : Matrix ι ι O := Matrix.of fun i j => ⟨X i j, h i j⟩

theorem scC_mem (α β : E) (hα : α ∈ O) (hβ : β ∈ O) (i j : Ix r) : scC r α β i j ∈ O := by
  rcases i with i | i <;> rcases j with j | j <;>
    simp [scC, liftE, dlast, Matrix.fromBlocks, Matrix.one_apply, Matrix.diagonal_apply] <;>
    split_ifs <;> simp_all [O.one_mem, O.zero_mem]

theorem scC_mul_inv (α β α' β' : E) (h1 : α * α' = 1) (h2 : β' = -(β * α')) :
    scC r α β * scC r α' β' = 1 := by
  unfold scC
  rw [Matrix.fromBlocks_multiply]
  have hL : liftE (R := E) r * dlast r α' = α' • liftE r := by
    ext a b
    simp only [liftE, dlast, Matrix.mul_diagonal, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    split_ifs with h1 h2 <;> simp_all
  have hD : dlast r α * dlast r α' = 1 := by
    rw [dlast, dlast, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    split_ifs <;> simp [h1]
  simp only [Matrix.smul_mul, hL, hD, h2, smul_smul, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul,
    Matrix.mul_one, add_zero, zero_add, smul_zero]
  rw [← Matrix.fromBlocks_one, ← add_smul]
  congr 1
  simp [mul_comm]

theorem scC_det (α β : E) : (scC r α β).det = α := by
  rw [scC, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, dlast, Matrix.det_diagonal]
  rw [Finset.prod_eq_single (Fin.last r)]
  · simp
  · intro b _ hb; simp [hb]
  · simp

end ScaleA2

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.VecMulScCInr

section

@[expose] public section

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

section ScaleA4

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) (qi : E) {r : ℕ}

structure ScHyp (O : Subring E) (cj : E →+* E) (qi T T' α : E) : Prop where
  cjcj : ∀ x, cj (cj x) = x
  cjO : ∀ x ∈ O, cj x ∈ O
  qic : cj qi = qi
  Tc : cj T = T
  T'c : cj T' = T'
  αO : α ∈ O
  αn : α * cj α = 1
  βO : (α - 1) * qi ∈ O

variable {O cj qi} {T T' α : E}

theorem ScHyp.cα_mem (h : ScHyp O cj qi T T' α) : cj α ∈ O := h.cjO α h.αO
theorem ScHyp.β'_mem (h : ScHyp O cj qi T T' α) : -((α - 1) * qi * cj α) ∈ O :=
  O.neg_mem (O.mul_mem h.βO h.cα_mem)

theorem ScHyp.C_mul (h : ScHyp O cj qi T T' α) :
    scC r α ((α - 1) * qi) * scC r (cj α) (-((α - 1) * qi * cj α)) = 1 :=
  scC_mul_inv α _ (cj α) _ h.αn rfl

theorem ScHyp.C'_mul (h : ScHyp O cj qi T T' α) :
    scC r (cj α) (-((α - 1) * qi * cj α)) * scC r α ((α - 1) * qi) = 1 := by
  have hc : cj α * α = 1 := by rw [mul_comm]; exact h.αn
  exact scC_mul_inv (cj α) _ α _ hc (by linear_combination (-((α - 1) * qi)) * hc)

def scA (h : ScHyp O cj qi T T' α) : Matrix (Ix r) (Ix r) O :=
  toOm O ((scC r α ((α - 1) * qi)).map cj) fun i j => h.cjO _ (scC_mem O α _ h.αO h.βO i j)

def scA' (h : ScHyp O cj qi T T' α) : Matrix (Ix r) (Ix r) O :=
  toOm O ((scC r (cj α) (-((α - 1) * qi * cj α))).map cj) fun i j =>
    h.cjO _ (scC_mem O _ _ h.cα_mem h.β'_mem i j)

theorem scA_mul (h : ScHyp O cj qi T T' α) : scA (r := r) h * scA' h = 1 := by
  refine Matrix.map_injective (f := O.subtype) Subtype.val_injective ?_
  show (scA h * scA' h).map O.subtype = (1 : Matrix (Ix r) (Ix r) O).map O.subtype
  rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have e1 : (scA (r := r) h).map O.subtype = (scC r α ((α - 1) * qi)).map cj := by
    ext i j
    rfl
  have e2 : (scA' (r := r) h).map O.subtype = (scC r (cj α) (-((α - 1) * qi * cj α))).map cj := by
    ext i j
    rfl
  rw [e1, e2, ← Matrix.map_mul, h.C_mul, Matrix.map_one _ (map_zero cj) (map_one cj)]

theorem scA'_mul (h : ScHyp O cj qi T T' α) : scA' (r := r) h * scA h = 1 := by
  refine Matrix.map_injective (f := O.subtype) Subtype.val_injective ?_
  show (scA' h * scA h).map O.subtype = (1 : Matrix (Ix r) (Ix r) O).map O.subtype
  rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have e1 : (scA (r := r) h).map O.subtype = (scC r α ((α - 1) * qi)).map cj := by
    ext i j
    rfl
  have e2 : (scA' (r := r) h).map O.subtype = (scC r (cj α) (-((α - 1) * qi * cj α))).map cj := by
    ext i j
    rfl
  rw [e1, e2, ← Matrix.map_mul, h.C'_mul, Matrix.map_one _ (map_zero cj) (map_one cj)]

def scPhi (h : ScHyp O cj qi T T' α) : (Ix r → O) ≃ₗ[O] (Ix r → O) :=
  phiEq O (scA h) (scA' h) (scA_mul h) (scA'_mul h)

theorem scPhi_coe (h : ScHyp O cj qi T T' α) (Y : Ix r → O) (j : Ix r) :
    ((scPhi (r := r) h Y j : O) : E) = Matrix.vecMul (fun i => (Y i : E)) ((scC r α ((α - 1) * qi)).map cj) j := by
  show ((Matrix.vecMul Y (scA h) j : O) : E) = _
  simp [Matrix.vecMul, dotProduct, scA, toOm]

theorem vecMul_scC_inl (α β : E) (Y : Ix r → E) (b : Fin (r + 1)) :
    Matrix.vecMul Y ((scC r α β).map cj) (Sum.inl b) = Y (Sum.inl b) := by
  simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, Fintype.sum_sum_type, scC_apply_inl_inl,
    scC_apply_inr_inl, map_zero, mul_zero, Finset.sum_const_zero, add_zero]
  simp [apply_ite cj, mul_ite, Finset.sum_ite_eq']

theorem vecMul_scC_inr (α β : E) (Y : Ix r → E) (b : Fin (r + 1)) :
    Matrix.vecMul Y ((scC r α β).map cj) (Sum.inr b) =
      Y (Sum.inr b) * cj (if b = Fin.last r then α else 1) +
        (if b = Fin.last r then Y (Sum.inl (Fin.last r)) * cj β else 0) := by
  simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, Fintype.sum_sum_type, scC_apply_inl_inr,
    scC_apply_inr_inr]
  by_cases hb : b = Fin.last r
  · subst hb
    simp [apply_ite cj, mul_ite, Finset.sum_ite_eq', Finset.sum_ite_eq]
    ring
  · simp [hb, apply_ite cj, mul_ite, Finset.sum_ite_eq', Finset.sum_ite_eq]

end ScaleA4

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
end
end
end
