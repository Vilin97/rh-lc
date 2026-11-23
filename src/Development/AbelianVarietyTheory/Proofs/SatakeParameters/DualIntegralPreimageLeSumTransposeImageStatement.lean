module

public import Formalism.SatakeDualWeyl.StatementF
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.DualLattices.BlockOneMulMulBlockOne
import ReciprocityTheory.DualLattices.UpSmith
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Basic.PEquiv
public import Mathlib.Data.Matrix.PEquiv
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmithNormalFormDiscreteValuationField

section

@[expose] public section

open Matrix

namespace GlobalTheory.SmithValued

variable (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))]

noncomputable def vNN : Valuation L NNReal :=
  (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).map
    { toMonoidWithZeroHom := WithZeroMulInt.toNNReal (e := 2) (by norm_num)
      monotone' := (WithZeroMulInt.toNNReal_strictMono (e := 2) (by norm_num)).monotone }

theorem vNN_le_one_iff (x : L) : vNN L x ≤ 1 ↔ x ∈ Formalism.UG.intL L := by
  have h := (WithZeroMulInt.toNNReal_strictMono (e := 2) (by norm_num)).le_iff_le
    (a := (Valued.v x : WithZero (Multiplicative ℤ))) (b := 1)
  rw [map_one] at h
  exact h

theorem vNN_integers : (vNN L).Integers ↥(Formalism.UG.intL L) := by
  refine ⟨Subtype.val_injective, ?_, ?_⟩
  · intro x
    exact (vNN_le_one_iff L _).2 x.2
  · intro r hr
    exact ⟨⟨r, (vNN_le_one_iff L _).1 hr⟩, rfl⟩

theorem exists_clear {ι : Type} (s : Finset ι) (f : ι → L) :
    ∃ c : L, c ≠ 0 ∧ c ∈ Formalism.UG.intL L ∧ ∀ i ∈ s, c * f i ∈ Formalism.UG.intL L := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, one_mem _, by simp⟩
  | insert a s _ ih =>
    obtain ⟨c, hc0, hc, hs⟩ := ih
    by_cases ha : f a ∈ Formalism.UG.intL L
    · refine ⟨c, hc0, hc, fun i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact mul_mem hc ha
      · exact hs i hi
    · have h0 : f a ≠ 0 := by
        intro h; exact ha (h ▸ zero_mem _)
      have hinv : (f a)⁻¹ ∈ Formalism.UG.intL L := by
        rw [← vNN_le_one_iff] at ha ⊢
        rw [map_inv₀]
        exact inv_le_one_of_one_le₀ (not_le.1 ha).le
      refine ⟨(f a)⁻¹ * c, mul_ne_zero (inv_ne_zero h0) hc0, mul_mem hinv hc, fun i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · have : (f i)⁻¹ * c * f i = c := by field_simp
        rw [this]; exact hc
      · rw [mul_assoc]; exact mul_mem hinv (hs i hi)

theorem smith_valued : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (m n : ℕ) (M : Matrix (Fin m) (Fin n) L),
    ∃ (P P' : Matrix (Fin m) (Fin m) L) (Q Q' : Matrix (Fin n) (Fin n) L) (d : Fin m → L),
      (∀ i j, P i j ∈ Formalism.UG.intL L) ∧ (∀ i j, P' i j ∈ Formalism.UG.intL L) ∧
      (∀ i j, Q i j ∈ Formalism.UG.intL L) ∧ (∀ i j, Q' i j ∈ Formalism.UG.intL L) ∧ P * P' = 1 ∧ Q * Q' = 1 ∧
      M = P * Matrix.of (fun (j : Fin m) (k : Fin n) => if (k : ℕ) = (j : ℕ) then d j else 0) * Q := by
  intro L _ _ m n M
  classical
  obtain ⟨c, hc0, -, hc⟩ := exists_clear L (Finset.univ : Finset (Fin m × Fin n))
    (fun p => M p.1 p.2)
  let A : Matrix (Fin m) (Fin n) ↥(Formalism.UG.intL L) :=
    Matrix.of fun i j => ⟨c * M i j, hc (i, j) (Finset.mem_univ _)⟩
  have diagonalize : ∀ (d n : ℕ) (X : Matrix (Fin d) (Fin n) ↥(Formalism.UG.intL L)),
      ∃ (P : Matrix (Fin d) (Fin d) ↥(Formalism.UG.intL L))
        (Q : Matrix (Fin n) (Fin n) ↥(Formalism.UG.intL L)) (a : Fin d → ↥(Formalism.UG.intL L)),
        IsUnit P.det ∧ IsUnit Q.det ∧
          ∀ j k, (P * X * Q) j k = if (k : ℕ) = (j : ℕ) then a j else 0 := by
    open ReciprocityTheory.PGsh.Up.Smith in
    intro d
    induction d with
    | zero =>
      intro n X
      exact ⟨1, 1, Fin.elim0, by simp, by simp, fun j => j.elim0⟩
    | succ d ih =>
      intro n X
      cases n with
      | zero => exact ⟨1, 1, 0, by simp, by simp, fun j k => k.elim0⟩
      | succ n =>
        let g : Fin (n + 1) → Fin (d + 1) → ↥(Formalism.UG.intL L) := fun j i => X i j
        obtain ⟨i₀, a, u, s, hu, -, hs, hz, hnz⟩ := exists_pivot (vNN_integers L) g
        by_cases ha : a = 0
        · have hX : X = 0 := by
            apply Matrix.ext
            intro i j
            exact congrFun (hz ha j) i
          exact ⟨1, 1, 0, by simp, by simp, fun j k => by simp [hX]⟩
        obtain ⟨j₀, hj₀, hs₀⟩ := hnz ha
        have hcol : ∀ i, X i j₀ = a * u i := fun i => congrFun hj₀ i
        have hrow : ∀ j, X i₀ j = a * s j := hs
        let B := (Vm i₀ u)ᵀ * X * Vm j₀ s
        have hB (i j) : B i j = if i = i₀ then (if j = j₀ then a else 0) else
            if j = j₀ then 0 else X i j - s j * (a * u i) := by
          dsimp only [B]
          rw [Matrix.mul_assoc, VmT_mul, mul_Vm, mul_Vm]
          by_cases hi : i = i₀ <;> by_cases hj : j = j₀
          · subst i
            subst j
            simp [hcol, hu]
          · subst i
            simp [hj, hrow, hs₀]
            ring
          · subst j
            simp [hi, hcol, hu]
            ring
          · simp only [hi, hj, ite_false, hcol, hrow, hu]
            ring
        let C := B.submatrix (piv i₀) (piv j₀)
        let Y := Matrix.of fun (i : Fin d) (j : Fin n) => C i.succ j.succ
        obtain ⟨P, Q, b, hP, hQ, hY⟩ := ih n Y
        let U : Matrix (Fin (d + 1)) (Fin (d + 1)) ↥(Formalism.UG.intL L) :=
          (piv i₀).toPEquiv.toMatrix
        let V : Matrix (Fin (n + 1)) (Fin (n + 1)) ↥(Formalism.UG.intL L) :=
          (piv j₀).symm.toPEquiv.toMatrix
        have hC : U * B * V = C := by
          dsimp only [U, V, C]
          rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Equiv.symm_symm]
          rfl
        have hrow₀ (j : Fin n) : C 0 j.succ = 0 := by
          simp [C, piv_zero, piv_succ, hB, Fin.succAbove_ne]
        have hcol₀ (i : Fin d) : C i.succ 0 = 0 := by
          simp [C, piv_zero, piv_succ, hB, Fin.succAbove_ne]
        obtain ⟨h00, h0j, hi0, hij⟩ := blockOne_mul_mul_blockOne P C Q hrow₀ hcol₀
        refine ⟨bd1 P * U * (Vm i₀ u)ᵀ, Vm j₀ s * V * bd1 Q, Fin.cons a b, ?_, ?_, ?_⟩
        · rw [Matrix.det_mul, Matrix.det_mul, det_blockOne_alt, Matrix.det_transpose, det_Vm, mul_one]
          exact hP.mul (isUnit_det_perm _)
        · rw [Matrix.det_mul, Matrix.det_mul, det_blockOne_alt, det_Vm, one_mul]
          exact (isUnit_det_perm _).mul hQ
        · have hfull : bd1 P * U * (Vm i₀ u)ᵀ * X * (Vm j₀ s * V * bd1 Q) =
              bd1 P * C * bd1 Q := by
            rw [← hC]
            simp only [B, Matrix.mul_assoc]
          intro i j
          rw [hfull]
          refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
          · rw [h00]
            simp [C, piv_zero, hB]
          · rw [h0j]
            simp
          · rw [hi0]
            simp
          · rw [hij, hY]
            simp [Fin.val_succ]
  obtain ⟨P, Q, a, hP, hQ, hD⟩ := diagonalize m n A
  let φ : ↥(Formalism.UG.intL L) →+* L := (Formalism.UG.intL L).subtype
  have hP1 : P⁻¹.map φ * P.map φ = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hP, Matrix.map_one _ (map_zero φ) (map_one φ)]
  have hQ1 : Q⁻¹.map φ * Q.map φ = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hQ, Matrix.map_one _ (map_zero φ) (map_one φ)]
  have hQ2 : Q.map φ * Q⁻¹.map φ = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hQ, Matrix.map_one _ (map_zero φ) (map_one φ)]
  refine ⟨P⁻¹.map φ, P.map φ, Q⁻¹.map φ, Q.map φ, fun j => c⁻¹ * (a j : L),
    fun i j => (P⁻¹ i j).2, fun i j => (P i j).2, fun i j => (Q⁻¹ i j).2, fun i j => (Q i j).2,
    hP1, hQ1, ?_⟩
  have hA : A.map φ = c • M := by
    ext i j; simp [A, φ]
  have hD' : Matrix.of (fun (j : Fin m) (k : Fin n) =>
      if (k : ℕ) = (j : ℕ) then c⁻¹ * (a j : L) else 0) = P.map φ * M * Q.map φ := by
    have h1 : (P * A * Q).map φ = c • (P.map φ * M * Q.map φ) := by
      rw [Matrix.map_mul, Matrix.map_mul, hA, Matrix.mul_smul, Matrix.smul_mul]
    have h2 : P.map φ * M * Q.map φ = c⁻¹ • (P * A * Q).map φ := by
      rw [h1, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [h2]
    ext j k
    rw [Matrix.of_apply, Matrix.smul_apply, Matrix.map_apply, hD, smul_eq_mul]
    split_ifs
    · rfl
    · simp
  rw [hD', ← Matrix.mul_assoc, ← Matrix.mul_assoc, hP1, Matrix.one_mul, Matrix.mul_assoc, hQ2,
    Matrix.mul_one]

end GlobalTheory.SmithValued
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmithNormalFormDiscreteValuationFieldStatement

section

@[expose] public section

open Matrix

theorem _root_.GlobalTheory.T.smithNormalForm_discreteValuationField : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (m n : ℕ) (M : Matrix (Fin m) (Fin n) L),
    ∃ (P P' : Matrix (Fin m) (Fin m) L) (Q Q' : Matrix (Fin n) (Fin n) L) (d : Fin m → L),
      (∀ i j, P i j ∈ Formalism.UG.intL L) ∧ (∀ i j, P' i j ∈ Formalism.UG.intL L) ∧
      (∀ i j, Q i j ∈ Formalism.UG.intL L) ∧ (∀ i j, Q' i j ∈ Formalism.UG.intL L) ∧ P * P' = 1 ∧ Q * Q' = 1 ∧
      M = P * Matrix.of (fun (j : Fin m) (k : Fin n) => if (k : ℕ) = (j : ℕ) then d j else 0) * Q := by
  first | exact @GlobalTheory.SmithValued.smith_valued | exact GlobalTheory.SmithValued.smith_valued | (intros; apply GlobalTheory.SmithValued.smith_valued <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualIntegralPreimageLeSumTransposeImage

section

@[expose] public section

open Matrix

namespace GlobalTheory.LatticeDuality

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem mem_int_iff (a : L) : a ∈ Formalism.UG.intL L ↔ Valued.v a ≤ 1 := Iff.rfl

theorem mulVec_int {m n : ℕ} (A : Matrix (Fin m) (Fin n) L) (u : Fin n → L)
    (hA : ∀ i j, A i j ∈ Formalism.UG.intL L) (hu : ∀ i, u i ∈ Formalism.UG.intL L) :
    ∀ i, (A *ᵥ u) i ∈ Formalism.UG.intL L := fun i => by
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hA i j) (hu j)

theorem one_dim (e z : L)
    (h : ∀ c : L, c ∈ Formalism.UG.intL L → e * c ∈ Formalism.UG.intL L → c * z ∈ Formalism.UG.intL L) :
    ∃ a b : L, a ∈ Formalism.UG.intL L ∧ b ∈ Formalism.UG.intL L ∧ z = a + e * b := by
  by_cases he : e ∈ Formalism.UG.intL L
  · refine ⟨z, 0, ?_, Subring.zero_mem _, by simp⟩
    simpa using h 1 (Subring.one_mem _) (by simpa using he)
  · have he0 : e ≠ 0 := by
      rintro rfl
      exact he (Subring.zero_mem _)
    have hlt : 1 < Valued.v e := not_le.mp ((mem_int_iff e).not.mp he)
    have hinv : e⁻¹ ∈ Formalism.UG.intL L := by
      rw [mem_int_iff, map_inv₀]
      exact inv_le_one_of_one_le₀ hlt.le
    refine ⟨0, e⁻¹ * z, Subring.zero_mem _, h _ hinv ?_, ?_⟩
    · rw [mul_inv_cancel₀ he0]; exact Subring.one_mem _
    · field_simp
      simp

theorem diag_case {m n : ℕ} (d : Fin m → L) (z : Fin n → L)
    (h : ∀ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) →
      (∀ i, ((Matrix.of (fun (j : Fin m) (k : Fin n) => if (k : ℕ) = (j : ℕ) then d j else 0)) *ᵥ u) i
        ∈ Formalism.UG.intL L) → (∑ i, u i * z i) ∈ Formalism.UG.intL L) :
    ∃ l : Fin n → L, ∃ w : Fin m → L, (∀ i, l i ∈ Formalism.UG.intL L) ∧ (∀ i, w i ∈ Formalism.UG.intL L) ∧
      z = l + (Matrix.of (fun (j : Fin m) (k : Fin n) => if (k : ℕ) = (j : ℕ) then d j else 0))ᵀ *ᵥ w := by
  have key : ∀ k : Fin n, ∃ a b : L, a ∈ Formalism.UG.intL L ∧ b ∈ Formalism.UG.intL L ∧
      z k = a + (if hk : (k : ℕ) < m then d ⟨k, hk⟩ else 0) * b := by
    intro k
    apply one_dim
    intro c hc hec
    have := h (Pi.single k c) ?_ ?_
    · simpa [Pi.single_apply] using this
    · intro i
      by_cases hi : i = k
      · subst hi; simpa using hc
      · simp [hi]
    · intro j
      rw [Matrix.mulVec_single]
      by_cases hj : (k : ℕ) = (j : ℕ)
      · have hk : (k : ℕ) < m := hj ▸ j.2
        have : (⟨k, hk⟩ : Fin m) = j := Fin.ext hj
        rw [dite_eq_left hk, this] at hec
        simpa [hj] using hec
      · simp [hj]
  choose a b ha hb hz using key
  refine ⟨a, fun j => if hj : (j : ℕ) < n then b ⟨j, hj⟩ else 0, ha, ?_, ?_⟩
  · intro j
    dsimp only
    split_ifs
    · exact hb _
    · exact Subring.zero_mem _
  · funext k
    rw [hz k, Pi.add_apply]
    congr 1
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply]
    by_cases hk : (k : ℕ) < m
    · rw [dite_eq_left hk, Finset.sum_eq_single (⟨k, hk⟩ : Fin m)]
      · simp
      · intro j _ hj
        have : (k : ℕ) ≠ (j : ℕ) := fun e => hj (Fin.ext e.symm)
        simp [this]
      · simp
    · rw [dite_eq_right hk, zero_mul]
      symm
      refine Finset.sum_eq_zero fun j _ => ?_
      have : (k : ℕ) ≠ (j : ℕ) := fun e => hk (e ▸ j.2)
      simp [this]

theorem dual_subset : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (m n : ℕ) (x : Matrix (Fin m) (Fin n) L)
    (z : Fin n → L),
    (∀ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) → (∑ i, u i * z i) ∈ Formalism.UG.intL L) →
    ∃ l : Fin n → L, ∃ w : Fin m → L, (∀ i, l i ∈ Formalism.UG.intL L) ∧ (∀ i, w i ∈ Formalism.UG.intL L) ∧ z = l + xᵀ *ᵥ w := by
  intro L _ _ m n x z h
  obtain ⟨P, P', Q, Q', d, hP, hP', hQ, hQ', hPP, hQQ, hx⟩ := GlobalTheory.T.smithNormalForm_discreteValuationField L m n x
  set D : Matrix (Fin m) (Fin n) L :=
    Matrix.of (fun (j : Fin m) (k : Fin n) => if (k : ℕ) = (j : ℕ) then d j else 0) with hD
  have hPP' : P' * P = 1 := mul_eq_one_comm.mp hPP
  have hQQ' : Q' * Q = 1 := mul_eq_one_comm.mp hQQ
  obtain ⟨l, w, hl, hw, hz⟩ := diag_case d (Q'ᵀ *ᵥ z) (by
    intro s hs hDs
    have h1 := h (Q' *ᵥ s) (mulVec_int _ _ hQ' hs) (by
      have : x *ᵥ (Q' *ᵥ s) = P *ᵥ (D *ᵥ s) := by
        rw [hx, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc (P * D), hQQ, Matrix.mul_one]
      rw [this]
      exact mulVec_int _ _ hP hDs)
    have h2 : ∑ i, s i * (Q'ᵀ *ᵥ z) i = ∑ i, (Q' *ᵥ s) i * z i := by
      change s ⬝ᵥ (Q'ᵀ *ᵥ z) = (Q' *ᵥ s) ⬝ᵥ z
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    rw [h2]
    exact h1)
  refine ⟨Qᵀ *ᵥ l, P'ᵀ *ᵥ w, mulVec_int _ _ (fun i j => hQ j i) hl,
    mulVec_int _ _ (fun i j => hP' j i) hw, ?_⟩
  have h3 : z = Qᵀ *ᵥ (Q'ᵀ *ᵥ z) := by
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hQQ', Matrix.transpose_one, Matrix.one_mulVec]
  have h4 : xᵀ *ᵥ (P'ᵀ *ᵥ w) = Qᵀ *ᵥ (Dᵀ *ᵥ w) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, ← Matrix.transpose_mul, hx,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP', Matrix.one_mul]
  rw [h4, ← Matrix.mulVec_add, ← hz]
  exact h3

end GlobalTheory.LatticeDuality
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualIntegralPreimageLeSumTransposeImageStatement

section

@[expose] public section

open Matrix

theorem _root_.GlobalTheory.T.dual_integral_preimage_le_sum_transpose_image : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (m n : ℕ) (x : Matrix (Fin m) (Fin n) L)
    (z : Fin n → L),
    (∀ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) → (∑ i, u i * z i) ∈ Formalism.UG.intL L) →
    ∃ l : Fin n → L, ∃ w : Fin m → L, (∀ i, l i ∈ Formalism.UG.intL L) ∧ (∀ i, w i ∈ Formalism.UG.intL L) ∧ z = l + xᵀ *ᵥ w := by
  first | exact @GlobalTheory.LatticeDuality.dual_subset | exact GlobalTheory.LatticeDuality.dual_subset | (intros; apply GlobalTheory.LatticeDuality.dual_subset <;> assumption)
end
end
