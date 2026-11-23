module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviElementIsotropicOrthogonalComplexStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFlagComplementPosDefFactorizationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFlagUnipotentMatrixExistsSparseStatement
public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Algebra.Star.UnitaryStarAlgAut
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RadicalEltMovingDualToMajorantStatement
import Mathlib.Analysis.CStarAlgebra.Classes

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjTransposeMulMulSelfOfUnitaryConj

section

@[expose] public section

open scoped ComplexOrder
open Matrix

namespace GlobalTheory


open scoped ComplexOrder in
open Matrix in
theorem _root_.GlobalTheory.conjTranspose_mul_mul_self_of_unitary_conj :
    ∀ (n d : ℕ) (J P : Matrix (Fin n) (Fin n) ℂ) (Xb Yb : Matrix (Fin n) (Fin d) ℂ) (y₀ : GL (Fin d) ℂ),
    J.conjTranspose = J → P.conjTranspose = P → Xb.conjTranspose * J * Xb = 0 → Yb.conjTranspose * J * Yb = 0 →
    Xb.conjTranspose * J * Yb = 1 →
    P * Xb = J * Yb * ((y₀⁻¹).1.conjTranspose * (y₀⁻¹).1) → P * Yb = J * Xb * (y₀.1 * (y₀.1).conjTranspose) →
    ∀ k : GL (Fin d) ℂ, (k.1).conjTranspose * k.1 = 1 →
      let m : GL (Fin d) ℂ := y₀ * k * y₀⁻¹
      let G : Matrix (Fin n) (Fin n) ℂ := 1 + Xb * (m.1 - 1) * (Yb.conjTranspose * J) + Yb * ((m⁻¹).1.conjTranspose - 1) * (Xb.conjTranspose * J)
      G.conjTranspose * P * G = P := by
  intro n d J P X Y y₀ hJ hP hXX hYY hXY hPX hPY k hk m G
  have hki : (k⁻¹).1 = k.1ᴴ := by
    calc (k⁻¹).1 = (k.1ᴴ * k.1) * (k⁻¹).1 := by rw [hk, Matrix.one_mul]
      _ = k.1ᴴ := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  have hm : m.1 = y₀.1 * k.1 * (y₀⁻¹).1 := by simp [m]
  have hmi : (m⁻¹).1 = y₀.1 * k.1ᴴ * (y₀⁻¹).1 := by
    simp only [m, _root_.mul_inv_rev, inv_inv, Units.val_mul, hki, Matrix.mul_assoc]
  have hab : y₀.1ᴴ * (y₀⁻¹).1ᴴ = 1 := by
    rw [← conjTranspose_mul, Units.inv_mul, conjTranspose_one]
  have hAm : m.1ᴴ * ((y₀⁻¹).1ᴴ * (y₀⁻¹).1) * m.1 = (y₀⁻¹).1ᴴ * (y₀⁻¹).1 := by
    rw [hm]
    simp only [conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc y₀.1ᴴ, hab, Matrix.one_mul, ← Matrix.mul_assoc (y₀⁻¹).1 y₀.1, Units.inv_mul,
      Matrix.one_mul, ← Matrix.mul_assoc k.1ᴴ k.1, hk, Matrix.one_mul]
  have hBm : (m⁻¹).1 * (y₀.1 * y₀.1ᴴ) * (m⁻¹).1ᴴ = y₀.1 * y₀.1ᴴ := by
    rw [hmi]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (y₀⁻¹).1 y₀.1, Units.inv_mul, Matrix.one_mul, ← Matrix.mul_assoc y₀.1ᴴ, hab,
      Matrix.one_mul, ← Matrix.mul_assoc k.1ᴴ k.1, hk, Matrix.one_mul]
  have hAh : ((y₀⁻¹).1ᴴ * (y₀⁻¹).1)ᴴ = (y₀⁻¹).1ᴴ * (y₀⁻¹).1 := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
  have hBh : (y₀.1 * y₀.1ᴴ)ᴴ = y₀.1 * y₀.1ᴴ := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
  simp only [G]
  generalize (y₀⁻¹).1ᴴ * (y₀⁻¹).1 = A at hPX hAm hAh
  generalize y₀.1 * y₀.1ᴴ = B at hPY hBm hBh
  generalize m.1 = m₁ at hAm
  generalize (m⁻¹).1 = m₂ at hBm
  have hYX : Yᴴ * J * X = 1 := by
    have h := congrArg conjTranspose hXY
    simpa [conjTranspose_mul, hJ, Matrix.mul_assoc] using h
  have hXP : Xᴴ * P = A * (Yᴴ * J) := by
    have h := congrArg conjTranspose hPX
    simpa [conjTranspose_mul, hJ, hP, hAh, Matrix.mul_assoc] using h
  have hYP : Yᴴ * P = B * (Xᴴ * J) := by
    have h := congrArg conjTranspose hPY
    simpa [conjTranspose_mul, hJ, hP, hBh, Matrix.mul_assoc] using h
  have r1 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin d) c ℂ), Xᴴ * (J * (X * Z)) = 0 := fun Z => by
    simp only [← Matrix.mul_assoc, hXX, Matrix.zero_mul]
  have r2 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin d) c ℂ), Yᴴ * (J * (Y * Z)) = 0 := fun Z => by
    simp only [← Matrix.mul_assoc, hYY, Matrix.zero_mul]
  have r3 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin d) c ℂ), Xᴴ * (J * (Y * Z)) = Z := fun Z => by
    simp only [← Matrix.mul_assoc, hXY, Matrix.one_mul]
  have r4 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin d) c ℂ), Yᴴ * (J * (X * Z)) = Z := fun Z => by
    simp only [← Matrix.mul_assoc, hYX, Matrix.one_mul]
  have r5 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin d) c ℂ), P * (X * Z) = J * (Y * (A * Z)) := fun Z => by
    simp only [← Matrix.mul_assoc, hPX]
  have r6 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin d) c ℂ), P * (Y * Z) = J * (X * (B * Z)) := fun Z => by
    simp only [← Matrix.mul_assoc, hPY]
  have r7 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin n) c ℂ), Xᴴ * (P * Z) = A * (Yᴴ * (J * Z)) := fun Z => by
    simp only [← Matrix.mul_assoc, hXP]
  have r8 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin n) c ℂ), Yᴴ * (P * Z) = B * (Xᴴ * (J * Z)) := fun Z => by
    simp only [← Matrix.mul_assoc, hYP]
  have r9 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin d) c ℂ), m₁ᴴ * (A * (m₁ * Z)) = A * Z := fun Z => by
    simp only [← Matrix.mul_assoc, hAm]
  have r10 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin d) c ℂ), m₂ * (B * (m₂ᴴ * Z)) = B * Z := fun Z => by
    simp only [← Matrix.mul_assoc, hBm]
  simp only [conjTranspose_add, conjTranspose_mul, conjTranspose_sub, conjTranspose_one,
    conjTranspose_conjTranspose, hJ, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, hXP, hYP,
    Matrix.mul_zero, Matrix.zero_mul, sub_zero, add_zero, zero_add]
  abel

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjTransposeMulMulSelfOfUnitaryConjStatement

section

@[expose] public section

open scoped ComplexOrder

theorem _root_.GlobalTheory.T.conjTranspose_mul_self_of_witt_frame_unitary : ∀ (n d : ℕ) (J P : Matrix (Fin n) (Fin n) ℂ) (Xb Yb : Matrix (Fin n) (Fin d) ℂ) (y₀ : GL (Fin d) ℂ),
    J.conjTranspose = J → P.conjTranspose = P → Xb.conjTranspose * J * Xb = 0 → Yb.conjTranspose * J * Yb = 0 →
    Xb.conjTranspose * J * Yb = 1 →
    P * Xb = J * Yb * ((y₀⁻¹).1.conjTranspose * (y₀⁻¹).1) → P * Yb = J * Xb * (y₀.1 * (y₀.1).conjTranspose) →
    ∀ k : GL (Fin d) ℂ, (k.1).conjTranspose * k.1 = 1 →
      let m : GL (Fin d) ℂ := y₀ * k * y₀⁻¹
      let G : Matrix (Fin n) (Fin n) ℂ := 1 + Xb * (m.1 - 1) * (Yb.conjTranspose * J) + Yb * ((m⁻¹).1.conjTranspose - 1) * (Xb.conjTranspose * J)
      G.conjTranspose * P * G = P := by
  first | exact @GlobalTheory.conjTranspose_mul_mul_self_of_unitary_conj | exact GlobalTheory.conjTranspose_mul_mul_self_of_unitary_conj | (intros; apply GlobalTheory.conjTranspose_mul_mul_self_of_unitary_conj <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosDefExistsConjTransposeMulMulEqOne

section

@[expose] public section

open scoped ComplexOrder

noncomputable section

namespace GlobalTheory

open Matrix

theorem posDef_exists_conjTranspose_mul_mul_eq_one :
    ∀ (d : ℕ) (H : Matrix (Fin d) (Fin d) ℂ), H.PosDef →
      ∃ y₀ : GL (Fin d) ℂ, (y₀.1).conjTranspose * H * y₀.1 = 1 := by
  intro d H hP
  have hH : H.IsHermitian := hP.isHermitian
  set U : Matrix (Fin d) (Fin d) ℂ := (hH.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hUdef
  have hU1 : Uᴴ * U = 1 := hH.eigenvectorUnitary.2.1
  have hU2 : U * Uᴴ = 1 := hH.eigenvectorUnitary.2.2
  have hspec : H = U * diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) * Uᴴ := by
    have h := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    simpa [Matrix.star_eq_conjTranspose, Function.comp_def] using h
  have hpos : ∀ i, 0 < hH.eigenvalues i := fun i => hP.eigenvalues_pos i
  let r : Fin d → ℝ := fun i => Real.sqrt (hH.eigenvalues i)
  have hr : ∀ i, 0 < r i := fun i => Real.sqrt_pos.2 (hpos i)
  have hrr : ∀ i, r i * r i = hH.eigenvalues i := fun i => Real.mul_self_sqrt (hpos i).le
  let s : Fin d → ℂ := fun i => (((r i)⁻¹ : ℝ) : ℂ)
  let t : Fin d → ℂ := fun i => ((r i : ℝ) : ℂ)
  have hst : diagonal s * diagonal t = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i
    simp only [s, t, ← Complex.ofReal_mul, inv_mul_cancel₀ (hr i).ne', Complex.ofReal_one]
  have hts : diagonal t * diagonal s = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i
    simp only [s, t, ← Complex.ofReal_mul, mul_inv_cancel₀ (hr i).ne', Complex.ofReal_one]
  let Y : Matrix (Fin d) (Fin d) ℂ := U * diagonal s
  let Z : Matrix (Fin d) (Fin d) ℂ := diagonal t * Uᴴ
  have hYZ : Y * Z = 1 := by
    simp only [Y, Z]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal s), hst, Matrix.one_mul, hU2]
  have hZY : Z * Y = 1 := by
    simp only [Y, Z]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, hU1, Matrix.one_mul, hts]
  refine ⟨⟨Y, Z, hYZ, hZY⟩, ?_⟩
  show Yᴴ * H * Y = 1
  have hsH : (diagonal s)ᴴ = diagonal s := by
    rw [diagonal_conjTranspose]
    congr 1; funext i
    simp [s]
  have hdiag : diagonal s * diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) * diagonal s = 1 := by
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i
    simp only [s, ← hrr i, ← Complex.ofReal_mul]
    rw [show (r i)⁻¹ * (r i * r i) * (r i)⁻¹ = ((r i)⁻¹ * r i) * (r i * (r i)⁻¹) by ring,
      inv_mul_cancel₀ (hr i).ne', mul_inv_cancel₀ (hr i).ne']
    simp
  simp only [Y]
  rw [conjTranspose_mul, hsH, hspec]
  calc diagonal s * Uᴴ * (U * diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) * Uᴴ) * (U * diagonal s)
      = diagonal s * (Uᴴ * U) * diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) * (Uᴴ * U) * diagonal s := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hU1, Matrix.mul_one, Matrix.mul_one, hdiag]

end GlobalTheory
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosDefExistsConjTransposeMulMulEqOneStatement

section

@[expose] public section

open scoped ComplexOrder

theorem _root_.GlobalTheory.T.posDef_exists_conjTranspose_mul_mul_eq_one' : ∀ (d : ℕ) (H : Matrix (Fin d) (Fin d) ℂ), H.PosDef → ∃ y₀ : GL (Fin d) ℂ, (y₀.1).conjTranspose * H * y₀.1 = 1 := by
  first | exact @GlobalTheory.posDef_exists_conjTranspose_mul_mul_eq_one | exact GlobalTheory.posDef_exists_conjTranspose_mul_mul_eq_one | (intros; apply GlobalTheory.posDef_exists_conjTranspose_mul_mul_eq_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexWittBasisNormalForm

section

@[expose] public section

open scoped ComplexOrder

namespace GlobalTheory.MajPosCpx

theorem gram_sub_eq {n r a b : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (X Y : Matrix (Fin n) (Fin r) ℂ)
    (f : Fin a → Fin r) (g : Fin b → Fin r) (R : Matrix (Fin a) (Fin b) ℂ)
    (hR : ∀ i j, (X.conjTranspose * J * Y) (f i) (g j) = R i j) :
    (X.submatrix id f).conjTranspose * J * (Y.submatrix id g) = R := by
  ext i j; rw [← hR]; simp [Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem mul_submatrix_id {n r a : ℕ} (u : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (Fin n) (Fin r) ℂ)
    (f : Fin a → Fin r) : u * X.submatrix id f = (u * X).submatrix id f := by
  ext i j; simp [Matrix.mul_apply]

theorem exists_unip_conj_unitary : ∀ (n r : ℕ) (J : Matrix (Fin n) (Fin n) ℂ), J.conjTranspose = J →
    ∀ (X Y : Matrix (Fin n) (Fin r) ℂ), X.conjTranspose * J * X = 0 → Y.conjTranspose * J * Y = 0 → X.conjTranspose * J * Y = 1 →
    ∀ (c : GL (Fin n) ℂ) (ε : Fin n → Bool), (c.1).conjTranspose * J * c.1 = Matrix.diagonal (fun i => if ε i then 1 else -1) →
    ∀ (l d : ℕ) (h : l + d ≤ r),
      ∃ (u : GL (Fin n) ℂ) (N : Matrix (Fin r) (Fin r) ℂ),
        (u.1).conjTranspose * J * u.1 = J ∧ u.1 * X = X + X * N ∧
        (∀ i j, N i j ≠ 0 → (i.val < l ∧ l ≤ j.val) ∨ (i.val < l + d ∧ l + d ≤ j.val)) ∧
        (∀ v : Fin n → ℂ, (∀ i : Fin r, i.val < l + d → Matrix.mulVec (X.conjTranspose * J) v i = 0) →
          ∃ w : Fin r → ℂ, (∀ i, w i ≠ 0 → i.val < l + d) ∧ Matrix.mulVec u.1 v - v = Matrix.mulVec X w) ∧
        ∃ y₀ : GL (Fin d) ℂ, ∀ k : GL (Fin d) ℂ, (k.1).conjTranspose * k.1 = 1 →
          let Xb : Matrix (Fin n) (Fin d) ℂ := X.submatrix id fun j => ⟨l + j.val, by omega⟩
          let Yb : Matrix (Fin n) (Fin d) ℂ := Y.submatrix id fun j => ⟨l + j.val, by omega⟩
          let m : GL (Fin d) ℂ := y₀ * k * y₀⁻¹
          let G : Matrix (Fin n) (Fin n) ℂ := 1 + Xb * (m.1 - 1) * (Yb.conjTranspose * J) + Yb * ((m⁻¹).1.conjTranspose - 1) * (Xb.conjTranspose * J)
          let M : Matrix (Fin n) (Fin n) ℂ := (c⁻¹).1 * u.1 * G * (u⁻¹).1 * c.1
          M.conjTranspose * M = 1 := by
  intro n r J hJ X Y hXX hYY hXY c ε hc l d h
  set Dg : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal (fun i => if ε i then 1 else -1) with hDg
  have hDD : Dg * Dg = 1 := by
    rw [hDg, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; split_ifs <;> norm_num
  have hcc : c.1 * (c⁻¹).1 = 1 := Units.mul_inv c
  have hcc' : (c⁻¹).1 * c.1 = 1 := Units.inv_mul c
  have hcH : (c⁻¹).1.conjTranspose * (c.1).conjTranspose = 1 := by
    rw [← Matrix.conjTranspose_mul, hcc, Matrix.conjTranspose_one]
  have hJc : J = (c⁻¹).1.conjTranspose * Dg * (c⁻¹).1 := by
    have e : (c⁻¹).1.conjTranspose * Dg * (c⁻¹).1 =
        ((c⁻¹).1.conjTranspose * (c.1).conjTranspose) * J * (c.1 * (c⁻¹).1) := by
      rw [← hc]; simp only [Matrix.mul_assoc]
    rw [e, hcH, hcc, Matrix.one_mul, Matrix.mul_one]
  set θ : Matrix (Fin n) (Fin n) ℂ := c.1 * Dg * (c⁻¹).1 with hθ
  have hθθ : θ * θ = 1 := by
    simp only [hθ, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (c⁻¹).1 c.1, hcc', Matrix.one_mul, ← Matrix.mul_assoc Dg Dg, hDD, Matrix.one_mul, hcc]
  have hQ : J * θ = (c⁻¹).1.conjTranspose * (c⁻¹).1 := by
    rw [hJc]; simp only [hθ, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (c⁻¹).1 c.1, hcc', Matrix.one_mul, ← Matrix.mul_assoc Dg Dg, hDD, Matrix.one_mul]
  have hQpd : (J * θ).PosDef := by
    rw [hQ]; exact Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_iff_isUnit.2 (c⁻¹).isUnit)
  set X₁ : Matrix (Fin n) (Fin l) ℂ := X.submatrix id fun j => ⟨j.val, by omega⟩ with hX₁
  set Y₁ : Matrix (Fin n) (Fin l) ℂ := Y.submatrix id fun j => ⟨j.val, by omega⟩ with hY₁
  set Xb : Matrix (Fin n) (Fin d) ℂ := X.submatrix id fun j => ⟨l + j.val, by omega⟩ with hXb
  set Yb : Matrix (Fin n) (Fin d) ℂ := Y.submatrix id fun j => ⟨l + j.val, by omega⟩ with hYb
  set X₂ : Matrix (Fin n) (Fin (l + d)) ℂ := X.submatrix id fun j => ⟨j.val, by omega⟩ with hX₂
  set Y₂ : Matrix (Fin n) (Fin (l + d)) ℂ := Y.submatrix id fun j => ⟨j.val, by omega⟩ with hY₂
  have w11 : X₁.conjTranspose * J * X₁ = 0 := gram_sub_eq J X X _ _ 0 (fun i j => by rw [hXX]; rfl)
  have w1b : X₁.conjTranspose * J * Xb = 0 := gram_sub_eq J X X _ _ 0 (fun i j => by rw [hXX]; rfl)
  have wbb : Xb.conjTranspose * J * Xb = 0 := gram_sub_eq J X X _ _ 0 (fun i j => by rw [hXX]; rfl)
  have v11 : X₁.conjTranspose * J * Y₁ = 1 :=
    gram_sub_eq J X Y _ _ 1 (fun i j => by rw [hXY]; simp [Matrix.one_apply, Fin.ext_iff])
  have v1b : X₁.conjTranspose * J * Yb = 0 :=
    gram_sub_eq J X Y _ _ 0 (fun i j => by
      rw [hXY, Matrix.one_apply, if_neg]
      · rfl
      · simp only [Fin.ext_iff]; omega)
  have ybb : Yb.conjTranspose * J * Yb = 0 := gram_sub_eq J Y Y _ _ 0 (fun i j => by rw [hYY]; rfl)
  have vbb : Xb.conjTranspose * J * Yb = 1 :=
    gram_sub_eq J X Y _ _ 1 (fun i j => by rw [hXY]; simp [Matrix.one_apply, Fin.ext_iff])
  have w22 : X₂.conjTranspose * J * X₂ = 0 := gram_sub_eq J X X _ _ 0 (fun i j => by rw [hXX]; rfl)
  have y22 : Y₂.conjTranspose * J * Y₂ = 0 := gram_sub_eq J Y Y _ _ 0 (fun i j => by rw [hYY]; rfl)
  have v22 : X₂.conjTranspose * J * Y₂ = 1 :=
    gram_sub_eq J X Y _ _ 1 (fun i j => by rw [hXY]; simp [Matrix.one_apply, Fin.ext_iff])
  have w21 : X₂.conjTranspose * J * X₁ = 0 := gram_sub_eq J X X _ _ 0 (fun i j => by rw [hXX]; rfl)
  obtain ⟨u₂, A, hu₂J, hu₂X₁, hu₂Xb, hu₂Yb, hu₂v, hA⟩ :=
    GlobalTheory.T.exists_unipotent_unitary_shift_making_complement_orthogonal n l d J (J * θ) hJ hQpd X₁ Y₁ Xb Yb w11 w1b wbb v11 v1b ybb vbb
  obtain ⟨u₁, hu₁J, hu₁X₂, hu₁v, hθX₂⟩ := GlobalTheory.T.exists_unitary_fixing_mulVec_conj_eq_of_majorant n (l + d) J θ hJ hθθ hQpd X₂ Y₂ w22 y22 v22
  have hu₁X₁ : u₁.1 * X₁ = X₁ := by
    have e : X₁ = X₂.submatrix id (fun j : Fin l => ⟨j.val, by omega⟩) := rfl
    rw [e, mul_submatrix_id, hu₁X₂]
  have hu₁Xb : u₁.1 * Xb = Xb := by
    have e : Xb = X₂.submatrix id (fun j : Fin d => ⟨l + j.val, by omega⟩) := rfl
    rw [e, mul_submatrix_id, hu₁X₂]
  set u : GL (Fin n) ℂ := u₁ * u₂ with hu
  have huv : u.1 = u₁.1 * u₂.1 := Units.val_mul u₁ u₂
  have huJ : (u.1).conjTranspose * J * u.1 = J := by
    have e : (u₂.1).conjTranspose * (u₁.1).conjTranspose * J * (u₁.1 * u₂.1) =
        (u₂.1).conjTranspose * ((u₁.1).conjTranspose * J * u₁.1) * u₂.1 := by simp only [Matrix.mul_assoc]
    rw [huv, Matrix.conjTranspose_mul, e, hu₁J, hu₂J]
  have huX₁ : u.1 * X₁ = X₁ := by rw [huv, Matrix.mul_assoc, hu₂X₁, hu₁X₁]
  have huXb : u.1 * Xb = Xb + X₁ * A := by
    rw [huv, Matrix.mul_assoc, hu₂Xb, Matrix.mul_add, hu₁Xb, ← Matrix.mul_assoc, hu₁X₁]
  have huYb : u.1 * Yb = u₁.1 * Yb := by rw [huv, Matrix.mul_assoc, hu₂Yb]
  have huP : ∀ v : Fin n → ℂ, Matrix.mulVec (X₂.conjTranspose * J) v = 0 →
      ∃ (w : Fin (l + d) → ℂ) (a : Fin l → ℂ), Matrix.mulVec u.1 v - v = Matrix.mulVec X₂ w + Matrix.mulVec X₁ a := by
    intro v hv
    have h1 : Matrix.mulVec (X₁.conjTranspose * J) v = 0 := by
      funext i; exact congrFun hv ⟨i.val, by omega⟩
    set a := Matrix.mulVec A (Matrix.mulVec (Yb.conjTranspose * J) v) with ha
    have h2 : Matrix.mulVec (X₂.conjTranspose * J) (v + Matrix.mulVec X₁ a) = 0 := by
      rw [Matrix.mulVec_add, hv, Matrix.mulVec_mulVec, w21, Matrix.zero_mulVec, add_zero]
    obtain ⟨w, hw⟩ := hu₁v _ h2
    refine ⟨w, a, ?_⟩
    rw [huv, ← Matrix.mulVec_mulVec, hu₂v v h1, ← hw]
    abel
  obtain ⟨N, hN, hNs, hNp⟩ := GlobalTheory.T.hermitian_flag_unipotent_matrix_exists_sparse n r J X hXX l d h u.1 A huX₁ huXb huP
  obtain ⟨hθX', hHpd⟩ := GlobalTheory.T.hermitian_flag_complement_posDef_factorization n r J θ hJ hQpd X Y hXY l d h u₁.1 A hθX₂ hA
  set H : Matrix (Fin d) (Fin d) ℂ := Xb.conjTranspose * (J * θ) * (Xb + X₁ * A) with hHdef
  obtain ⟨y₀, hy₀⟩ := GlobalTheory.T.posDef_exists_conjTranspose_mul_mul_eq_one' d H hHpd
  have hθu : θ * u.1 * Xb = u.1 * Yb * H := by
    rw [Matrix.mul_assoc, huXb, hθX', huYb]
  have hy1 : (y₀⁻¹).1.conjTranspose * (y₀.1).conjTranspose = 1 := by
    rw [← Matrix.conjTranspose_mul, Units.mul_inv, Matrix.conjTranspose_one]
  have hHy : H = (y₀⁻¹).1.conjTranspose * (y₀⁻¹).1 := by
    calc H = ((y₀⁻¹).1.conjTranspose * (y₀.1).conjTranspose) * H * (y₀.1 * (y₀⁻¹).1) := by
          rw [hy1, Units.mul_inv, Matrix.one_mul, Matrix.mul_one]
      _ = (y₀⁻¹).1.conjTranspose * ((y₀.1).conjTranspose * H * y₀.1) * (y₀⁻¹).1 := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hy₀, Matrix.mul_one]
  have hHinv : H * (y₀.1 * (y₀.1).conjTranspose) = 1 := by
    calc H * (y₀.1 * (y₀.1).conjTranspose) = (y₀⁻¹).1.conjTranspose * ((y₀⁻¹).1 * y₀.1) * (y₀.1).conjTranspose := by
          rw [hHy]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Units.inv_mul, Matrix.mul_one, hy1]
  have huJ' : (u.1).conjTranspose * J = J * (u⁻¹).1 := by
    calc (u.1).conjTranspose * J = (u.1).conjTranspose * J * (u.1 * (u⁻¹).1) := by rw [Units.mul_inv, Matrix.mul_one]
      _ = ((u.1).conjTranspose * J * u.1) * (u⁻¹).1 := by simp only [Matrix.mul_assoc]
      _ = J * (u⁻¹).1 := by rw [huJ]
  have hθuY : θ * u.1 * Yb = u.1 * Xb * (y₀.1 * (y₀.1).conjTranspose) := by
    calc θ * u.1 * Yb = θ * u.1 * Yb * (H * (y₀.1 * (y₀.1).conjTranspose)) := by rw [hHinv, Matrix.mul_one]
      _ = θ * (θ * u.1 * Xb) * (y₀.1 * (y₀.1).conjTranspose) := by rw [hθu]; simp only [Matrix.mul_assoc]
      _ = (θ * θ) * u.1 * Xb * (y₀.1 * (y₀.1).conjTranspose) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hθθ, Matrix.one_mul]
  have hPX : (u.1).conjTranspose * (J * θ) * u.1 * Xb = J * Yb * ((y₀⁻¹).1.conjTranspose * (y₀⁻¹).1) := by
    calc (u.1).conjTranspose * (J * θ) * u.1 * Xb = ((u.1).conjTranspose * J) * (θ * u.1 * Xb) := by
          simp only [Matrix.mul_assoc]
      _ = J * ((u⁻¹).1 * u.1) * Yb * H := by rw [huJ', hθu]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [Units.inv_mul, Matrix.mul_one, hHy]
  have hPY : (u.1).conjTranspose * (J * θ) * u.1 * Yb = J * Xb * (y₀.1 * (y₀.1).conjTranspose) := by
    calc (u.1).conjTranspose * (J * θ) * u.1 * Yb = ((u.1).conjTranspose * J) * (θ * u.1 * Yb) := by
          simp only [Matrix.mul_assoc]
      _ = J * ((u⁻¹).1 * u.1) * Xb * (y₀.1 * (y₀.1).conjTranspose) := by rw [huJ', hθuY]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [Units.inv_mul, Matrix.mul_one]
  have hPH : ((u.1).conjTranspose * (J * θ) * u.1).conjTranspose = (u.1).conjTranspose * (J * θ) * u.1 := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hQpd.1.eq]
    simp only [Matrix.mul_assoc]
  refine ⟨u, N, huJ, hN, hNs, fun v hv => hNp v hv, y₀, fun k hk => ?_⟩
  intro Xb' Yb' m G M
  have hG : G.conjTranspose * ((u.1).conjTranspose * (J * θ) * u.1) * G = (u.1).conjTranspose * (J * θ) * u.1 :=
    GlobalTheory.T.conjTranspose_mul_self_of_witt_frame_unitary n d J ((u.1).conjTranspose * (J * θ) * u.1) Xb Yb y₀ hJ hPH wbb ybb vbb hPX hPY k hk
  show ((c⁻¹).1 * u.1 * G * (u⁻¹).1 * c.1).conjTranspose * ((c⁻¹).1 * u.1 * G * (u⁻¹).1 * c.1) = 1
  have e1 : ((c⁻¹).1 * u.1 * G * (u⁻¹).1 * c.1).conjTranspose * ((c⁻¹).1 * u.1 * G * (u⁻¹).1 * c.1) =
      (c.1).conjTranspose * ((u⁻¹).1.conjTranspose *
        (G.conjTranspose * ((u.1).conjTranspose * ((c⁻¹).1.conjTranspose * (c⁻¹).1) * u.1) * G) * (u⁻¹).1) * c.1 := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [e1, ← hQ, hG]
  have e2 : (c.1).conjTranspose * ((u⁻¹).1.conjTranspose * ((u.1).conjTranspose * (J * θ) * u.1) * (u⁻¹).1) * c.1 =
      (c.1).conjTranspose * ((u.1 * (u⁻¹).1).conjTranspose * (J * θ) * (u.1 * (u⁻¹).1)) * c.1 := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [e2, Units.mul_inv, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, hQ]
  have e3 : (c.1).conjTranspose * ((c⁻¹).1.conjTranspose * (c⁻¹).1) * c.1 =
      ((c⁻¹).1 * c.1).conjTranspose * ((c⁻¹).1 * c.1) := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [e3, hcc', Matrix.conjTranspose_one, Matrix.one_mul]

end GlobalTheory.MajPosCpx
end
end
