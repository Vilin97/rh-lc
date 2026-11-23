module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.LetterSize
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DirectionsInParabolic
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.DerivA
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Block3MulBlocks
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
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
import Mathlib.Tactic.Lemma
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
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.DerivA

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.DerivB

section

@[expose] public section

open Matrix Filter Topology
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL

noncomputable section

namespace PI.UnitaryGroupMassFormula.UsCost.DB

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open PI.UnitaryGroupMassFormula.UsCost PI.UnitaryGroupMassFormula.UsCost.DA

lemma leviDifferential_add (k j ρ : ℕ) (Q Q' : Matrix (Fin j) (Fin j) ℂ) :
    dmuP k j ρ (Q + Q') = dmuP k j ρ Q + dmuP k j ρ Q' := by
  unfold dmuP
  rw [P.Ux4.block3_add]
  simp only [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul, add_zero, neg_add]

lemma leviDifferential_smul (k j ρ : ℕ) (c : ℝ) (Q : Matrix (Fin j) (Fin j) ℂ) :
    dmuP k j ρ (c • Q) = c • dmuP k j ρ Q := by
  unfold dmuP
  apply P.Ux4.ext_eB
  rintro (((a | a) | a)) (((b | b) | b)) <;>
    simp [P.Ux4.block3_apply, Matrix.conjTranspose_smul]

lemma block_matrix_two_zero_add {p s : ℕ} (e e' : Matrix (Fin s) (Fin s) ℂ) :
    blk2 (0 : Matrix (Fin p) (Fin p) ℂ) 0 0 (e + e') = blk2 (0 : Matrix (Fin p) (Fin p) ℂ) 0 0 e + blk2 0 0 0 e' := by
  ext i j
  simp only [blk2, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.add_apply]
  generalize finSumFinEquiv.symm i = u
  generalize finSumFinEquiv.symm j = v
  rcases u with a | a <;> rcases v with b | b <;> simp

lemma block_matrix_two_zero_smul {p s : ℕ} (c : ℝ) (e : Matrix (Fin s) (Fin s) ℂ) :
    blk2 (0 : Matrix (Fin p) (Fin p) ℂ) 0 0 (c • e) = c • blk2 (0 : Matrix (Fin p) (Fin p) ℂ) 0 0 e := by
  ext i j
  simp only [blk2, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply]
  generalize finSumFinEquiv.symm i = u
  generalize finSumFinEquiv.symm j = v
  rcases u with a | a <;> rcases v with b | b <;> simp

lemma symmetricScalarBlockMatrix_one_zero {p s : ℕ} : blk2 (1 : Matrix (Fin p) (Fin p) ℂ) 0 0 (1 : Matrix (Fin s) (Fin s) ℂ) = 1 := by
  simp [blk2, Matrix.fromBlocks_one]

lemma block_matrix_two_line {p s : ℕ} (t : ℝ) (A : Matrix (Fin s) (Fin s) ℂ) :
    blk2 (1 : Matrix (Fin p) (Fin p) ℂ) 0 0 (1 + t • A) = 1 + t • blk2 (0 : Matrix (Fin p) (Fin p) ℂ) 0 0 A := by
  rw [← symmetricScalarBlockMatrix_one_zero]
  ext i j
  simp only [blk2, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply]
  generalize finSumFinEquiv.symm i = u
  generalize finSumFinEquiv.symm j = v
  rcases u with a | a <;> rcases v with b | b <;> simp

def lamZ (k : ℕ) {p s : ℕ} (ρ : ℕ) {σ : Equiv.Perm (Fin p)} (ξ : Xi k p s ρ σ) (e : Matrix (Fin s) (Fin s) ℂ) :
    B.Mat k (p + s + ρ) :=
  (Rn k (p + s) ρ ξ.1.2)⁻¹ *
    dmuP k (p + s) ρ ((blk2 1 (Matrix.of ξ.2.1.2) 0 1)⁻¹ *
      blk2 (0 : Matrix (Fin p) (Fin p) ℂ) 0 0 e * blk2 1 (Matrix.of ξ.2.1.2) 0 1) *
    Rn k (p + s) ρ ξ.1.2

def lamL (k : ℕ) {p s : ℕ} (ρ : ℕ) {σ : Equiv.Perm (Fin p)} (ξ : Xi k p s ρ σ) :
    Matrix (Fin s) (Fin s) ℂ →ₗ[ℝ] B.Mat k (p + s + ρ) where
  toFun := lamZ k ρ ξ
  map_add' e e' := by
    simp only [lamZ, block_matrix_two_zero_add, Matrix.mul_add, Matrix.add_mul, leviDifferential_add]
  map_smul' c e := by
    simp only [lamZ, block_matrix_two_zero_smul, Matrix.mul_smul, Matrix.smul_mul, leviDifferential_smul, RingHom.id_apply]

lemma coef_sum {s : ℕ} (Z W : G.Mat s) :
    ∑ i : Fin s × Fin s × Bool, coefZ Z W i • eMat i.1 i.2.1 i.2.2 = (Matrix.of Z)⁻¹ * Matrix.of W := by
  ext x y
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, eMat, Matrix.of_apply]
  simp [Fintype.sum_prod_type, smul_ite, ite_and, Finset.sum_ite_eq, coefZ,
    Complex.real_smul, Complex.re_add_im]

lemma sum_dirZ {k p s ρ : ℕ} {σ : Equiv.Perm (Fin p)} (ξ : Xi k p s ρ σ) (Z W : G.Mat s) :
    ∑ i : Fin s × Fin s × Bool, coefZ Z W i • dirZ k ρ ξ i = lamZ k ρ ξ ((Matrix.of Z)⁻¹ * Matrix.of W) := by
  rw [← coef_sum Z W]
  change _ = lamL k ρ ξ _

  rw [map_sum]
  simp only [map_smul]
  rfl

lemma rn_mem (hRad : RadicalParam) (k j ρ : ℕ) (x : RC k j ρ) : Rn k j ρ x ∈ B.GV k (j + ρ) := by
  have h : Rn k j ρ x ∈ Rset k j ρ := (hRad k j ρ).2.1 ▸ Set.mem_range_self x
  exact h.1

lemma ga_mem (hMem : SliceMem) (hRad : RadicalParam) {k p s ρ : ℕ} {σ : Equiv.Perm (Fin p)} {d : Fin p → ℂ}
    (hd : ∀ i, d i ≠ 0) (ξ : Xi k p s ρ σ) {Z : G.Mat s} {γ : B.Mat k ρ} (hZ : G.detM Z ≠ 0)
    (hγ : γ ∈ B.GV k ρ) : gaXi k ρ σ d ξ Z γ ∈ B.GV k (p + s + ρ) := by
  have hdet : (ZjH σ d ξ.2 Z).det ≠ 0 := by
    rw [P.level_determinant_z]
    refine mul_ne_zero ?_ hZ
    rw [hMat, Matrix.det_mul, Matrix.det_diagonal]
    exact mul_ne_zero (P.Ux5.det_permutationMatrix_ne_zero σ) (Finset.prod_ne_zero_iff.mpr fun i _ => hd i)
  exact P.BetaSesquilinearity.gv_mul (P.BetaSesquilinearity.gv_mul (P.BetaSesquilinearity.gv_inv (rn_mem hRad _ _ _ _)) ((hMem k (p + s) ρ).1 _ γ hdet hγ))
    (rn_mem hRad _ _ _ _)

variable {k p s ρ : ℕ} {σ : Equiv.Perm (Fin p)} {d : Fin p → ℂ}

lemma phi_rep (hSZ : SliceZ) (ξ : Xi k p s ρ σ) {Z : G.Mat s} (hZ : G.detM Z ≠ 0) (γ : B.Mat k ρ) (Z' : G.Mat s) :
    gaXi k ρ σ d ξ Z' γ = gaXi k ρ σ d ξ Z γ * ((Rn k (p + s) ρ ξ.1.2)⁻¹ *
      muP k (p + s) ρ ((blk2 1 (Matrix.of ξ.2.1.2) 0 1)⁻¹ *
        blk2 1 0 0 ((Matrix.of Z)⁻¹ * Matrix.of Z') * blk2 1 (Matrix.of ξ.2.1.2) 0 1) *
      Rn k (p + s) ρ ξ.1.2) := by
  have hZu : IsUnit (Matrix.of Z).det := isUnit_iff_ne_zero.mpr hZ
  have := hSZ k p s ρ σ d ξ Z ((Matrix.of Z)⁻¹ * Matrix.of Z') γ
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hZu, Matrix.one_mul] at this
  exact this

lemma U_inv_mul {p s : ℕ} (b : Fin p → Fin s → ℂ) :
    (blk2 (1 : Matrix (Fin p) (Fin p) ℂ) (Matrix.of b) 0 (1 : Matrix (Fin s) (Fin s) ℂ))⁻¹ *
      blk2 1 (Matrix.of b) 0 1 = 1 := by
  apply Matrix.nonsing_inv_mul
  rw [P.Ux4.block2_det_upper_triangular]
  simp

lemma line_rep (hSZ : SliceZ) (ξ : Xi k p s ρ σ) {Z : G.Mat s} (hZ : G.detM Z ≠ 0) (γ : B.Mat k ρ) (W : G.Mat s)
    (t : ℝ) :
    gaXi k ρ σ d ξ (Z + t • W) γ = gaXi k ρ σ d ξ Z γ * ((Rn k (p + s) ρ ξ.1.2)⁻¹ *
      muP k (p + s) ρ (1 + t • ((blk2 1 (Matrix.of ξ.2.1.2) 0 1)⁻¹ *
        blk2 (0 : Matrix (Fin p) (Fin p) ℂ) 0 0 ((Matrix.of Z)⁻¹ * Matrix.of W) * blk2 1 (Matrix.of ξ.2.1.2) 0 1)) *
      Rn k (p + s) ρ ξ.1.2) := by
  rw [phi_rep hSZ ξ hZ γ (Z + t • W)]
  have hZu : IsUnit (Matrix.of Z).det := isUnit_iff_ne_zero.mpr hZ
  have e1 : (Matrix.of Z)⁻¹ * Matrix.of (Z + t • W) = 1 + t • ((Matrix.of Z)⁻¹ * Matrix.of W) := by
    have : Matrix.of (Z + t • W) = Matrix.of Z + t • Matrix.of W := rfl
    rw [this, Matrix.mul_add, Matrix.nonsing_inv_mul _ hZu, Matrix.mul_smul]
  rw [e1, block_matrix_two_line, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, U_inv_mul, Matrix.mul_smul, Matrix.smul_mul]

end PI.UnitaryGroupMassFormula.UsCost.DB
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.ZDeriv

section

@[expose] public section

open Matrix Filter Topology
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL

noncomputable section

namespace PI.UnitaryGroupMassFormula.UsCost

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open PI.UnitaryGroupMassFormula.UsCost.DA PI.UnitaryGroupMassFormula.UsCost.DB

theorem zDeriv : ZDeriv := by
  intro hMem hRad hSZ k p s ρ σ d hd E _ _ H hH ξ Z γ hZ hγ W
  have hZu : IsUnit (Matrix.of Z).det := isUnit_iff_ne_zero.mpr hZ
  have hg := ga_mem hMem hRad hd ξ hZ hγ

  have hΦ : ContDiffAt ℝ 1 (fun Z' : G.Mat s => gaXi k ρ σ d ξ Z' γ) Z := by
    rw [show (fun Z' : G.Mat s => gaXi k ρ σ d ξ Z' γ) = _ from funext (phi_rep hSZ ξ hZ γ)]
    have hA : ContDiffAt ℝ 1 (fun Z' : G.Mat s => (Matrix.of Z)⁻¹ * Matrix.of Z') Z :=
      cm_mul contDiffAt_const contDiffAt_id
    have hP := cm_mul (cm_mul (contDiffAt_const (c := (blk2 (1 : Matrix (Fin p) (Fin p) ℂ) (Matrix.of ξ.2.1.2) 0
      (1 : Matrix (Fin s) (Fin s) ℂ))⁻¹))
      (contDiffAt_block_matrix_two (contDiffAt_const (c := (1 : Matrix (Fin p) (Fin p) ℂ))) (contDiffAt_const (c := (0 : Matrix (Fin p) (Fin s) ℂ)))
        (contDiffAt_const (c := (0 : Matrix (Fin s) (Fin p) ℂ))) hA))
      (contDiffAt_const (c := blk2 (1 : Matrix (Fin p) (Fin p) ℂ) (Matrix.of ξ.2.1.2) 0 (1 : Matrix (Fin s) (Fin s) ℂ)))
    have hP1 : (blk2 (1 : Matrix (Fin p) (Fin p) ℂ) (Matrix.of ξ.2.1.2) 0 (1 : Matrix (Fin s) (Fin s) ℂ))⁻¹ *
        blk2 1 0 0 ((Matrix.of Z)⁻¹ * Matrix.of Z) * blk2 1 (Matrix.of ξ.2.1.2) 0 1 = 1 := by
      rw [Matrix.nonsing_inv_mul _ hZu, symmetricScalarBlockMatrix_one_zero, Matrix.mul_one, U_inv_mul]
    have hdet : ((((blk2 (1 : Matrix (Fin p) (Fin p) ℂ) (Matrix.of ξ.2.1.2) 0 (1 : Matrix (Fin s) (Fin s) ℂ))⁻¹ *
        blk2 1 0 0 ((Matrix.of Z)⁻¹ * Matrix.of Z) * blk2 1 (Matrix.of ξ.2.1.2) 0 1))ᴴ).det ≠ 0 := by
      rw [hP1]; simp
    have hmu := contDiffAt_block_matrix_three (k := k) (ρ := ρ) hP (contDiffAt_const (c := 0)) (contDiffAt_const (c := 0))
      (contDiffAt_const (c := 0))
      (contDiffAt_const (c := (1 : B.Mat k ρ))) (contDiffAt_const (c := 0)) (contDiffAt_const (c := 0))
      (contDiffAt_const (c := 0))
      (cm_mul (cm_mul (contDiffAt_const (c := G.wMat (p + s))) (cm_inv (cm_conjT hP) hdet))
        (contDiffAt_const (c := G.wMat (p + s))))
    exact cm_mul contDiffAt_const (cm_mul (cm_mul contDiffAt_const hmu) contDiffAt_const)
  have hΦd : DifferentiableAt ℝ (fun Z' : G.Mat s => gaXi k ρ σ d ξ Z' γ) Z := hΦ.differentiableAt one_ne_zero

  have hline : HasDerivAt (fun t : ℝ => gaXi k ρ σ d ξ (Z + t • W) γ)
      (gaXi k ρ σ d ξ Z γ * lamZ k ρ ξ ((Matrix.of Z)⁻¹ * Matrix.of W)) 0 := by
    rw [show (fun t : ℝ => gaXi k ρ σ d ξ (Z + t • W) γ) = _ from funext (line_rep hSZ ξ hZ γ W)]
    set Bm := (blk2 (1 : Matrix (Fin p) (Fin p) ℂ) (Matrix.of ξ.2.1.2) 0 (1 : Matrix (Fin s) (Fin s) ℂ))⁻¹ *
        blk2 (0 : Matrix (Fin p) (Fin p) ℂ) 0 0 ((Matrix.of Z)⁻¹ * Matrix.of W) * blk2 1 (Matrix.of ξ.2.1.2) 0 1
      with hBm
    have h11 : HasDerivAt (fun t : ℝ => (1 : Matrix (Fin (p + s)) (Fin (p + s)) ℂ) + t • Bm) Bm 0 :=
      (((hasDerivAt_id' (0 : ℝ)).smul_const Bm).const_add _).congr_deriv (one_smul _ _)
    have h33 : HasDerivAt (fun t : ℝ => G.wMat (p + s) * ((1 + t • Bm)ᴴ)⁻¹ * G.wMat (p + s))
        (-(G.wMat (p + s) * Bmᴴ * G.wMat (p + s))) 0 :=
      (hd_mul (hd_mul (hasDerivAt_const (0 : ℝ) (G.wMat (p + s))) (hd_invT Bm))
        (hasDerivAt_const (0 : ℝ) (G.wMat (p + s)))).congr_deriv (by simp)
    have hmu : HasDerivAt (fun t : ℝ => muP k (p + s) ρ (1 + t • Bm)) (dmuP k (p + s) ρ Bm) 0 :=
      hasDerivAt_block_matrix_three (k := k) (ρ := ρ) h11 (hasDerivAt_const _ _) (hasDerivAt_const _ _) (hasDerivAt_const _ _)
        (hasDerivAt_const _ (1 : B.Mat k ρ)) (hasDerivAt_const _ _) (hasDerivAt_const _ _) (hasDerivAt_const _ _) h33
    exact (hd_mul (hasDerivAt_const (0 : ℝ) (gaXi k ρ σ d ξ Z γ))
      (hd_mul (hd_mul (hasDerivAt_const (0 : ℝ) (Rn k (p + s) ρ ξ.1.2)⁻¹) hmu)
        (hasDerivAt_const (0 : ℝ) (Rn k (p + s) ρ ξ.1.2)))).congr_deriv (by simp [lamZ, Bm, Matrix.mul_assoc])
  have hfd : fderiv ℝ (fun Z' : G.Mat s => gaXi k ρ σ d ξ Z' γ) Z W =
      gaXi k ρ σ d ξ Z γ * lamZ k ρ ξ ((Matrix.of Z)⁻¹ * Matrix.of W) := by
    have hlin : HasDerivAt (fun t : ℝ => Z + t • W) W 0 :=
      (((hasDerivAt_id' (0 : ℝ)).smul_const W).const_add Z).congr_deriv (one_smul _ _)
    exact (hΦd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hlin (by simp)).unique hline

  obtain ⟨U0, H', hU0, hgU0, hcd, hagree⟩ := hH _ hg
  have hH'd : DifferentiableAt ℝ H' (gaXi k ρ σ d ξ Z γ) :=
    (hcd.differentiableOn (by simp)).differentiableAt (hU0.mem_nhds hgU0)
  have hdc : Continuous fun Z' : G.Mat s => G.detM Z' :=
    Continuous.matrix_det (A := fun Z' : G.Mat s => (Matrix.of Z' : Matrix (Fin s) (Fin s) ℂ)) continuous_id
  have hev : (fun Z' : G.Mat s => H (gaXi k ρ σ d ξ Z' γ)) =ᶠ[𝓝 Z] fun Z' => H' (gaXi k ρ σ d ξ Z' γ) := by
    have h1 : ∀ᶠ Z' in 𝓝 Z, gaXi k ρ σ d ξ Z' γ ∈ U0 := hΦd.continuousAt.preimage_mem_nhds (hU0.mem_nhds hgU0)
    have h2 : ∀ᶠ Z' in 𝓝 Z, G.detM Z' ≠ 0 := hdc.continuousAt.eventually_ne hZ
    filter_upwards [h1, h2] with Z' h1 h2
    exact hagree _ h1 (ga_mem hMem hRad hd ξ h2 hγ)
  have hcomp : fderiv ℝ (fun Z' : G.Mat s => H' (gaXi k ρ σ d ξ Z' γ)) Z =
      (fderiv ℝ H' (gaXi k ρ σ d ξ Z γ)).comp (fderiv ℝ (fun Z' : G.Mat s => gaXi k ρ σ d ξ Z' γ) Z) :=
    (hH'd.hasFDerivAt.comp Z hΦd.hasFDerivAt).fderiv
  have hR : ∀ i, RdV (dirZ k ρ ξ i) H (gaXi k ρ σ d ξ Z γ) =
      fderiv ℝ H' (gaXi k ρ σ d ξ Z γ) (gaXi k ρ σ d ξ Z γ * dirZ k ρ ξ i) := by
    intro i
    have hX : B.inLie k (p + s + ρ) (dirZ k ρ ξ i) := ((P.directions_in_parabolic k (p + s) ρ ξ.1.2).2 _).1
    exact (P.BetaSesquilinearity.Dx_hasDerivAt (x := (false, dirZ k ρ ξ i)) hX hU0 hgU0 hg hH'd hagree).deriv

  rw [hev.fderiv_eq, hcomp, ContinuousLinearMap.comp_apply, hfd, ← sum_dirZ, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hR i, Matrix.mul_smul, map_smul]

end PI.UnitaryGroupMassFormula.UsCost
end
end
end
