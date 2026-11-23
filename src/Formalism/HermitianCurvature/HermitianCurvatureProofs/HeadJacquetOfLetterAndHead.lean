module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelZeroKernel
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActOneVariableSmul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LocOfSmoothOnH
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ParamCommF
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DirectionsInParabolic
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DirectionsInParabolic
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExpFromBlocks
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ZOnlyOfLeviCurve
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WordInduction.WordInductionOfPartsHolds

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadJOf

section

@[expose] public section

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.LevelPointCoordinates

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

theorem kapJ_eq (P : M.Par) (j : ℕ) : kapJ P j = levelZeroKernel P.k P.r j := rfl

theorem headJ_of (hW : WordInd) (hB : HeadBridge) : HeadJ := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h hh γ hF hw hγ hγ' φ hφ t ht e
  obtain ⟨X, _, μ, ℓ, Zx, Fx, Dm, φx, hDm, hDmsub, hR, hZ, hφx, hL, hRt⟩ :=
    hB Wp Wq P p F j hj w h hh γ hF hw hγ hγ' φ hφ t ht e
  have ht0 : t ≠ 0 := (ht.1 (1, t) (by simp)).2
  rw [hL, hRt]
  congr 1
  funext x
  rw [hW P.k P.r j hj _ _ (Wq →L[ℂ] Wp) Dm (Fx x) p.T.base.z_mem p.T.base.z'_mem hDm hDmsub (hR x) (Zx x) γ
    (hZ x).1 hγ (hZ x).2 w (φx x) (hφx x) t ht0 e, kapJ_eq]

end Formalism.FourierDecayAlt.P.LevelPointCoordinates
end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockTwoApply

section

@[expose] public section

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates

theorem fsym (m n : ℕ) (i : Fin (m + n)) : finSumFinEquiv.symm i =
    if h : i.val < m then Sum.inl ⟨i, h⟩ else Sum.inr ⟨i - m, by omega⟩ := by
  split_ifs with h
  · rw [Equiv.symm_apply_eq]; ext; simp
  · rw [Equiv.symm_apply_eq]; ext; simp; omega

theorem block_two_apply {p s : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (B' : Matrix (Fin p) (Fin s) ℂ)
    (C : Matrix (Fin s) (Fin p) ℂ) (D' : Matrix (Fin s) (Fin s) ℂ) (a b : Fin (p + s)) :
    U.blk2 A B' C D' a b =
      if ha : a.val < p then (if hb : b.val < p then A ⟨a, ha⟩ ⟨b, hb⟩ else B' ⟨a, ha⟩ ⟨b - p, by omega⟩)
      else (if hb : b.val < p then C ⟨a - p, by omega⟩ ⟨b, hb⟩ else D' ⟨a - p, by omega⟩ ⟨b - p, by omega⟩) := by
  simp only [U.blk2, Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [fsym, fsym]
  split_ifs <;> rfl

theorem w_mul_apply {d : ℕ} {ι : Type*} (M : Matrix (Fin d) ι ℂ) (a : Fin d) (b : ι) :
    (G.wMat d * M) a b = M a.rev b := by
  simp [G.wMat, Matrix.mul_apply]

theorem mul_w_apply {d : ℕ} {ι : Type*} [Fintype ι] (M : Matrix ι (Fin d) ℂ) (a : ι) (b : Fin d) :
    (M * G.wMat d) a b = M a b.rev := by
  simp only [G.wMat, Matrix.mul_apply, Matrix.of_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single b.rev]
  · simp
  · intro c _ hc; rw [if_neg]; intro h; apply hc; rw [h, Fin.rev_rev]
  · simp

theorem xcongr {j : ℕ} (x : MJ j) {a a' b b' : Fin j} (ha : a.val = a'.val) (hb : b.val = b'.val) :
    x a b = x a' b' := by
  rw [Fin.ext ha, Fin.ext hb]

theorem levi_eq {k r j : ℕ} (hj : j + 1 ≤ r) (x : MJ j) :
    levi k r j x = D.castM (by omega : j + 1 + (r - (j + 1)) = r)
      (U.blk3 (k := k) (j := j + 1) (ρ := r - (j + 1)) (U.blk2 x 0 0 0) 0 0 0 0 0 0 0
        (G.wMat (j + 1) * U.blk2 (-xᴴ) 0 0 0 * G.wMat (j + 1))) := by
  ext p q
  obtain ⟨X, hX⟩ := (U.eB k (j + 1) (r - (j + 1))).surjective (Fin.cast (by omega) p)
  obtain ⟨Y, hY⟩ := (U.eB k (j + 1) (r - (j + 1))).surjective (Fin.cast (by omega) q)
  have hp : p.val = (U.eB k (j + 1) (r - (j + 1)) X).val := by rw [hX]; rfl
  have hq : q.val = (U.eB k (j + 1) (r - (j + 1)) Y).val := by rw [hY]; rfl
  have e : ∀ M : B.Mat k (j + 1 + (r - (j + 1))),
      D.castM (by omega : j + 1 + (r - (j + 1)) = r) M p q =
        M (U.eB k (j + 1) (r - (j + 1)) X) (U.eB k (j + 1) (r - (j + 1)) Y) := by
    intro M
    rw [hX, hY]; rfl
  rw [e, Ux4.block3_apply]
  rcases X with ((a | v) | a) <;> rcases Y with ((b | w) | b) <;>
    simp only [Ux4.block_index_first_val_eq, Ux4.block_index_middle_val_eq, Ux4.block_index_last_val_eq] at hp hq <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl,
      Matrix.fromCols_apply_inr, Matrix.zero_apply, levi, Matrix.of_apply, block_two_apply, w_mul_apply, mul_w_apply,
      Matrix.mul_assoc, Fin.val_rev, Matrix.neg_apply, Matrix.conjTranspose_apply] <;>
    split_ifs <;> first | rfl | (exfalso; omega) | skip
  all_goals first
    | exact xcongr x (by simp; omega) (by simp; omega)
    | (simp only [Complex.star_def]; congr 2; exact xcongr x (by simp; omega) (by simp; omega))

end Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential
end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.SandwichApply

section

@[expose] public section

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates

theorem hpk_inv' (k r : ℕ) : (Hpk k r)⁻¹ = Hpk k r :=
  Matrix.inv_eq_left_inv (Formalism.QuantumDeterminants.WeylGroupFacts.hpk_sq (k := k) (r := r))

theorem sandwich_apply {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (u v p q : Fin N) :
    (H * Matrix.single u v (1 : ℂ) * H) p q = H p u * H v q := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, ite_mul]

theorem hpk_col_eI (k r : ℕ) (b : Fin r) (p : Fin (2 * r + k + 1)) :
    Hpk k r p (eI k r b) = if p.val + b.val = 2 * r + k then 1 else 0 := by
  have := b.isLt
  unfold Hpk eI
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem hpk_row_eI (k r : ℕ) (a : Fin r) (q : Fin (2 * r + k + 1)) :
    Hpk k r (eI k r a) q = if a.val + q.val = 2 * r + k then 1 else 0 := by
  have := a.isLt
  unfold Hpk eI
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem hpk_col_esI (k r : ℕ) (b : Fin r) (p : Fin (2 * r + k + 1)) :
    Hpk k r p (esI k r b) = if p.val = b.val then 1 else 0 := by
  have := b.isLt
  unfold Hpk esI
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem hpk_row_esI (k r : ℕ) (a : Fin r) (q : Fin (2 * r + k + 1)) :
    Hpk k r (esI k r a) q = if q.val = a.val then 1 else 0 := by
  have := a.isLt
  unfold Hpk esI
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem hpartLevi : HpartLevi := by
  intro k r j hj a b
  have ha := a.isLt
  have hb := b.isLt
  have hcI : (starRingEnd ℂ) (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
    rw [map_div₀, map_one, map_mul, Complex.conj_I, map_ofNat, mul_neg, div_neg]
  have hc2 : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
    rw [map_div₀, map_one, map_ofNat]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext p q <;>
    simp only [hpart1, hpart2, hpk_inv', Matrix.conjTranspose_single, star_one, Matrix.smul_apply,
      Matrix.sub_apply, Matrix.add_apply, sandwich_apply, hpk_col_eI, hpk_row_eI, hpk_col_esI, hpk_row_esI] <;>
    simp only [levi, Matrix.of_apply, Matrix.single_apply, eI, esI, Fin.ext_iff, Fin.val_castLE, smul_eq_mul,
      Matrix.smul_apply] <;>
    split_ifs <;> first | (exfalso; omega) | skip
  all_goals first
    | (exfalso; omega)
    | (simp; done)
    | (simp [Complex.conj_I]; done)
    | (simp [Complex.conj_I]; ring; done)
    | (simp only [mul_one, mul_zero, sub_zero, zero_sub, add_zero, zero_add, map_neg, hcI, hc2, neg_neg,
        neg_mul] <;> ring)

end Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential
end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianPartLevi

section

@[expose] public section

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates

theorem castM_mul' {k a b : ℕ} (h : a = b) (g g' : B.Mat k a) :
    D.castM h (g * g') = D.castM h g * D.castM h g' := by
  simp only [D.castM, Matrix.reindex_apply, Matrix.submatrix_mul_equiv]

theorem exp_castM {k a b : ℕ} (h : a = b) (M : B.Mat k a) :
    NormedSpace.exp (D.castM h M) = D.castM h (NormedSpace.exp M) := by
  unfold D.castM; exact exp_reindex _ M

theorem exp_block_three_diagonal {k j ρ : ℕ} (A : Matrix (Fin j) (Fin j) ℂ) (Bm : B.Mat k ρ) (C : Matrix (Fin j) (Fin j) ℂ) :
    NormedSpace.exp (U.blk3 A 0 0 0 Bm 0 0 0 C) =
      U.blk3 (NormedSpace.exp A) 0 0 0 (NormedSpace.exp Bm) 0 0 0 (NormedSpace.exp C) := by
  unfold U.blk3
  rw [exp_reindex]
  have h1 : Matrix.fromRows (0 : Matrix (Fin j) (Fin j) ℂ) (0 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) = 0 := by
    ext i l; rcases i with i | i <;> rfl
  have h2 : Matrix.fromCols (0 : Matrix (Fin j) (Fin j) ℂ) (0 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) = 0 := by
    ext i l; rcases l with l | l <;> rfl
  rw [h1, h2, exp_fromBlocks, exp_fromBlocks]

theorem exp_block_two_diagonal {p s : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (Dd : Matrix (Fin s) (Fin s) ℂ) :
    NormedSpace.exp (U.blk2 A 0 0 Dd) = U.blk2 (NormedSpace.exp A) 0 0 (NormedSpace.exp Dd) := by
  unfold U.blk2
  rw [exp_reindex, exp_fromBlocks]

theorem symmetricScalarBlockMatrix_one_zero {p s : ℕ} : U.blk2 (1 : Matrix (Fin p) (Fin p) ℂ) 0 0 (1 : Matrix (Fin s) (Fin s) ℂ) = 1 := by
  simp [U.blk2]

theorem block_two_identity_conjTranspose {p s : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) :
    (U.blk2 A 0 0 (1 : Matrix (Fin s) (Fin s) ℂ))ᴴ = U.blk2 Aᴴ 0 0 1 := by
  ext a b
  simp only [Matrix.conjTranspose_apply, block_two_apply]
  split_ifs <;> simp [Matrix.one_apply, Fin.ext_iff, eq_comm]

theorem w_inv (d : ℕ) : (G.wMat d)⁻¹ = G.wMat d :=
  Matrix.inv_eq_left_inv (Ux4.wMat_mul_self d)

theorem exp_w_conj (d : ℕ) (M : Matrix (Fin d) (Fin d) ℂ) :
    NormedSpace.exp (G.wMat d * M * G.wMat d) = G.wMat d * NormedSpace.exp M * G.wMat d := by
  have hu : IsUnit (G.wMat d) := ⟨⟨G.wMat d, G.wMat d, Ux4.wMat_mul_self d, Ux4.wMat_mul_self d⟩, rfl⟩
  have e := Matrix.exp_conj (G.wMat d) M hu
  rw [w_inv] at e
  exact e

theorem block_two_exp_conjTranspose_inv {j : ℕ} (y : MJ j) :
    (U.blk2 (NormedSpace.exp y) 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ))ᴴ⁻¹ = U.blk2 (NormedSpace.exp (-yᴴ)) 0 0 1 := by
  rw [block_two_identity_conjTranspose]
  apply Matrix.inv_eq_left_inv
  rw [Ux4.symmetricScalarBlockMatrix_mul]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one]
  have hu : IsUnit (NormedSpace.exp yᴴ).det := (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp _)
  rw [Matrix.exp_neg, ← Matrix.exp_conjTranspose, Matrix.nonsing_inv_mul _ hu, symmetricScalarBlockMatrix_one_zero]

theorem exp_levi {k r j : ℕ} (hj : j + 1 ≤ r) (x : MJ j) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • levi k r j x) = D.castM (by omega : j + 1 + (r - (j + 1)) = r)
      (U.muP k (j + 1) (r - (j + 1)) (U.blk2 (NormedSpace.exp ((t : ℂ) • x)) 0 0 1)) := by
  have hs : (t : ℂ) • levi k r j x = levi k r j ((t : ℂ) • x) := by
    ext p q
    simp only [levi, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> simp [Complex.conj_ofReal]
  rw [hs, levi_eq hj, exp_castM, exp_block_three_diagonal, exp_w_conj, exp_block_two_diagonal, exp_block_two_diagonal]
  simp only [NormedSpace.exp_zero]
  unfold U.muP
  rw [block_two_exp_conjTranspose_inv]

theorem zfull_mul {j : ℕ} (Z E : MJ j) (τ : ℂ) :
    zfull Z τ * U.blk2 E 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ) = zfull (Z * E) τ := by
  unfold zfull
  rw [Ux4.symmetricScalarBlockMatrix_mul]
  simp

theorem curveLevi : CurveLevi := by
  intro k r j hj Z τ γ x t
  rw [exp_levi hj]
  unfold x0
  rw [← castM_mul', Ux4.mMap_mul_muP, zfull_mul]

end Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential

theorem Formalism.FourierDecayAlt.P.levi_curve : Formalism.FourierDecayAlt.P.WirtingerOperators.CurveLevi := Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential.curveLevi

theorem Formalism.FourierDecayAlt.P.hermitian_part_levi : Formalism.FourierDecayAlt.P.WirtingerOperators.HpartLevi := Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential.hpartLevi
end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.ZOnly

section

@[expose] public section

namespace Formalism.FourierDecayAlt.P

theorem z_only : LevelPointCoordinates.ZOnly :=
  z_only_of_levi_curve levi_curve hermitian_part_levi

end Formalism.FourierDecayAlt.P
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WordInd

section

@[expose] public section

namespace Formalism.FourierDecayAlt.P

theorem word_induction_of_parts : LevelPointCoordinates.WordIndOfParts := LevelPointCoordinates.WordIndPf.word_induction_of_parts_holds

end Formalism.FourierDecayAlt.P
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadJacquetOfLetterAndHead

section

@[expose] public section

noncomputable section

namespace Formalism.FourierDecayAlt.P

theorem head_jacquet_of_letter_and_head (hHL : LevelPointCoordinates.HeadLetter) (hB : LevelPointCoordinates.HeadBridge) : LevelPointCoordinates.HeadJ :=
  LevelPointCoordinates.headJ_of (word_induction_of_parts hHL z_only rules_closed) hB

theorem radial_head_of_letter_and_head (hHL : LevelPointCoordinates.HeadLetter) (hB : LevelPointCoordinates.HeadBridge) : KB.RadHead :=
  pb_radHead_of_headJ (head_jacquet_of_letter_and_head hHL hB)

end Formalism.FourierDecayAlt.P
end
end
end
