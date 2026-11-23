module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.HermitianCurvature.StatementB
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsUnitaryOfGramEq

section

@[expose] public section

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open scoped ENNReal ComplexOrder

namespace GlobalTheory.UnitaryExtension

theorem exists_isometry_comp {W V : Type} [AddCommGroup W] [Module ℂ W] [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (a b : W →ₗ[ℂ] V)
    (h : ∀ x, ‖b x‖ = ‖a x‖) : ∃ u : V →ₗᵢ[ℂ] V, ∀ x, u (a x) = b x := by
  have hk : LinearMap.ker a ≤ LinearMap.ker b := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← norm_eq_zero, h, hx, norm_zero]
  let l : LinearMap.range a →ₗ[ℂ] V :=
    ((LinearMap.ker a).liftQ b hk) ∘ₗ (a.quotKerEquivRange.symm : LinearMap.range a →ₗ[ℂ] _)
  have hl : ∀ x, l ⟨a x, LinearMap.mem_range_self a x⟩ = b x := by
    intro x
    simp only [l, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    simp
  let L : LinearMap.range a →ₗᵢ[ℂ] V :=
    { toLinearMap := l
      norm_map' := by
        rintro ⟨y, x, rfl⟩
        rw [hl, h]; rfl }
  refine ⟨L.extend, fun x => ?_⟩
  have := L.extend_apply ⟨a x, LinearMap.mem_range_self a x⟩
  rw [← hl]
  exact this

theorem exists_unitary_mul_eq {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B : Matrix (Fin n) ι ℂ) (h : Aᴴ * A = Bᴴ * B) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 ∧ U * A = B := by
  have key : ∀ (C : Matrix (Fin n) ι ℂ) (x : EuclideanSpace ℂ ι),
      inner ℂ (Matrix.toEuclideanLin C x) (Matrix.toEuclideanLin C x)
        = inner ℂ x (Matrix.toEuclideanLin (Cᴴ * C) x) := by
    intro C x
    rw [← LinearMap.adjoint_inner_right, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    congr 1
    simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
  obtain ⟨u, hu⟩ := exists_isometry_comp (Matrix.toEuclideanLin A) (Matrix.toEuclideanLin B) (by
    intro x
    rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ _ _ _ _ (Matrix.toEuclideanLin A x), key, key, h])
  refine ⟨Matrix.toEuclideanLin.symm u.toLinearMap, ?_, ?_⟩
  · apply (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Fin n) (n := Fin n)).injective
    ext1 x
    apply ext_inner_left ℂ
    intro y
    have e : Matrix.toEuclideanLin ((Matrix.toEuclideanLin.symm u.toLinearMap)ᴴ * Matrix.toEuclideanLin.symm u.toLinearMap) x
        = Matrix.toEuclideanLin (Matrix.toEuclideanLin.symm u.toLinearMap)ᴴ (Matrix.toEuclideanLin (Matrix.toEuclideanLin.symm u.toLinearMap) x) := by
      generalize Matrix.toEuclideanLin.symm u.toLinearMap = U
      simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
    rw [e, Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_right]
    simp [Matrix.toLpLin_apply]
  · apply (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Fin n) (n := ι)).injective
    ext1 x
    have e : Matrix.toEuclideanLin (Matrix.toEuclideanLin.symm u.toLinearMap * A) x
        = Matrix.toEuclideanLin (Matrix.toEuclideanLin.symm u.toLinearMap) (Matrix.toEuclideanLin A x) := by
      generalize Matrix.toEuclideanLin.symm u.toLinearMap = U
      simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
    rw [e, LinearEquiv.apply_symm_apply]
    exact hu x

end GlobalTheory.UnitaryExtension
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsUnitaryCommMulEqOfGram

section

@[expose] public section

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open scoped ENNReal ComplexOrder

namespace GlobalTheory.HCXi

open Matrix MeasureTheory in
open scoped ENNReal ComplexOrder in
private lemma exists_unitary_fix_proj_of_gram_eq_of_mul_eq_zero {n m : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ) (hQ : Qᴴ = Q)
    (X Y : Matrix (Fin n) (Fin m) ℂ) (h : Xᴴ * X = Yᴴ * Y) (hX : Q * X = 0) (hY : Q * Y = 0) :
    ∃ W : Matrix (Fin n) (Fin n) ℂ, Wᴴ * W = 1 ∧ W * Q = Q ∧ W * X = Y := by
  have hXQ : Xᴴ * Q = 0 := by rw [← hQ, ← conjTranspose_mul, hX, conjTranspose_zero]
  have hYQ : Yᴴ * Q = 0 := by rw [← hQ, ← conjTranspose_mul, hY, conjTranspose_zero]
  have e2 : Xᴴ * Q = Yᴴ * Q := by rw [hXQ, hYQ]
  have e3 : Qᴴ * X = Qᴴ * Y := by rw [hQ, hX, hY]
  have hG : (fromCols X Q)ᴴ * fromCols X Q = (fromCols Y Q)ᴴ * fromCols Y Q := by
    ext (i | i) (j | j)
    · simpa [Matrix.mul_apply] using congrFun (congrFun h i) j
    · simpa [Matrix.mul_apply] using congrFun (congrFun e2 i) j
    · simpa [Matrix.mul_apply] using congrFun (congrFun e3 i) j
    · simp [Matrix.mul_apply]
  obtain ⟨W, hWu, hW⟩ := _root_.GlobalTheory.UnitaryExtension.exists_unitary_mul_eq _ _ hG
  rw [mul_fromCols, fromCols_inj.eq_iff] at hW
  exact ⟨W, hWu, hW.2, hW.1⟩


open Matrix MeasureTheory in
open scoped ENNReal ComplexOrder in
theorem _root_.GlobalTheory.HCXi.exists_unitary_comm_mul_eq_of_gram {n m : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : Hᴴ = H) (hHH : H * H = 1)
    (A B : Matrix (Fin n) (Fin m) ℂ) (h1 : Aᴴ * A = Bᴴ * B) (h2 : Aᴴ * H * A = Bᴴ * H * B) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 ∧ U * H = H * U ∧ U * A = B := by
  obtain ⟨Pp, hPp⟩ : ∃ P : Matrix (Fin n) (Fin n) ℂ, P = (1 / 2 : ℂ) • (1 + H) := ⟨_, rfl⟩
  obtain ⟨Pm, hPm⟩ : ∃ P : Matrix (Fin n) (Fin n) ℂ, P = (1 / 2 : ℂ) • (1 - H) := ⟨_, rfl⟩
  have hPpH : Ppᴴ = Pp := by simp [hPp, hH, conjTranspose_smul]
  have hPmH : Pmᴴ = Pm := by simp [hPm, hH, conjTranspose_smul]
  have hPpPp : Pp * Pp = Pp := by
    simp only [hPp, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.one_mul, Matrix.mul_one, hHH]
    module
  have hPmPm : Pm * Pm = Pm := by
    simp only [hPm, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, hHH]
    module
  have hPpPm : Pp * Pm = 0 := by
    simp only [hPp, hPm, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.add_mul,
      Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hHH]
    module
  have hPmPp : Pm * Pp = 0 := by
    simp only [hPp, hPm, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.sub_mul,
      Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hHH]
    module
  have hsum : Pp + Pm = 1 := by rw [hPp, hPm]; module
  have hHdec : H = Pp - Pm := by rw [hPp, hPm]; module
  have h2' : Aᴴ * (H * A) = Bᴴ * (H * B) := by simpa only [Matrix.mul_assoc] using h2
  have gramP : ∀ Z : Matrix (Fin n) (Fin m) ℂ,
      (Pp * Z)ᴴ * (Pp * Z) = (1 / 2 : ℂ) • (Zᴴ * Z + Zᴴ * (H * Z)) := by
    intro Z
    rw [conjTranspose_mul, hPpH, Matrix.mul_assoc, ← Matrix.mul_assoc Pp, hPpPp, hPp]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul]
  have gramM : ∀ Z : Matrix (Fin n) (Fin m) ℂ,
      (Pm * Z)ᴴ * (Pm * Z) = (1 / 2 : ℂ) • (Zᴴ * Z - Zᴴ * (H * Z)) := by
    intro Z
    rw [conjTranspose_mul, hPmH, Matrix.mul_assoc, ← Matrix.mul_assoc Pm, hPmPm, hPm]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul]
  obtain ⟨Wp, hWpu, hWpP, hWpA⟩ := exists_unitary_fix_proj_of_gram_eq_of_mul_eq_zero Pm hPmH (Pp * A) (Pp * B)
    (by rw [gramP, gramP, h1, h2']) (by rw [← Matrix.mul_assoc, hPmPp, Matrix.zero_mul])
    (by rw [← Matrix.mul_assoc, hPmPp, Matrix.zero_mul])
  obtain ⟨Wm, hWmu, hWmP, hWmA⟩ := exists_unitary_fix_proj_of_gram_eq_of_mul_eq_zero Pp hPpH (Pm * A) (Pm * B)
    (by rw [gramM, gramM, h1, h2']) (by rw [← Matrix.mul_assoc, hPpPm, Matrix.zero_mul])
    (by rw [← Matrix.mul_assoc, hPpPm, Matrix.zero_mul])
  have hWpHPm : Wpᴴ * Pm = Pm := by rw [← hWpP, ← Matrix.mul_assoc, hWpu, Matrix.one_mul, hWpP]
  have hWmHPp : Wmᴴ * Pp = Pp := by rw [← hWmP, ← Matrix.mul_assoc, hWmu, Matrix.one_mul, hWmP]
  have hPmWp : Pm * Wp = Pm := by
    have := congrArg conjTranspose hWpHPm
    rwa [conjTranspose_mul, conjTranspose_conjTranspose, hPmH] at this
  have hPpWm : Pp * Wm = Pp := by
    have := congrArg conjTranspose hWmHPp
    rwa [conjTranspose_mul, conjTranspose_conjTranspose, hPpH] at this
  have hA : Pp * Wp * Pp = Wp * Pp := calc
    Pp * Wp * Pp = (Pp + Pm) * Wp * Pp - Pm * Wp * Pp := by
      rw [Matrix.add_mul, Matrix.add_mul]; abel
    _ = Wp * Pp := by rw [hsum, Matrix.one_mul, hPmWp, hPmPp, sub_zero]
  have hB : Pm * Wm * Pm = Wm * Pm := calc
    Pm * Wm * Pm = (Pp + Pm) * Wm * Pm - Pp * Wm * Pm := by
      rw [Matrix.add_mul, Matrix.add_mul]; abel
    _ = Wm * Pm := by rw [hsum, Matrix.one_mul, hPpWm, hPpPm, sub_zero]
  have hX1 : Pp * Wpᴴ * Wp = Pp := by rw [Matrix.mul_assoc, hWpu, Matrix.mul_one]
  have hX2 : Pm * Wmᴴ * Wm = Pm := by rw [Matrix.mul_assoc, hWmu, Matrix.mul_one]
  have hX3 : Pp * Wpᴴ * Wm * Pm = 0 := calc
    Pp * Wpᴴ * Wm * Pm = Pp * Wpᴴ * (Pm * Wm * Pm) := by rw [hB, Matrix.mul_assoc (Pp * Wpᴴ)]
    _ = Pp * (Wpᴴ * Pm) * Wm * Pm := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hWpHPm, hPpPm, Matrix.zero_mul, Matrix.zero_mul]
  have hX4 : Pm * Wmᴴ * Wp * Pp = 0 := calc
    Pm * Wmᴴ * Wp * Pp = Pm * Wmᴴ * (Pp * Wp * Pp) := by rw [hA, Matrix.mul_assoc (Pm * Wmᴴ)]
    _ = Pm * (Wmᴴ * Pp) * Wp * Pp := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hWmHPp, hPmPp, Matrix.zero_mul, Matrix.zero_mul]
  refine ⟨Wp * Pp + Wm * Pm, ?_, ?_, ?_⟩
  · simp only [conjTranspose_add, conjTranspose_mul, hPpH, hPmH, Matrix.add_mul, Matrix.mul_add,
      ← Matrix.mul_assoc, hX1, hX2, hX3, hX4, hPpPp, hPmPm]
    rw [add_zero, zero_add, hsum]
  · have hUH : (Wp * Pp + Wm * Pm) * H = Wp * Pp - Wm * Pm := by
      rw [hHdec]
      simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_assoc, hPpPp, hPpPm, hPmPp, hPmPm,
        Matrix.mul_zero]
      abel
    have hHU : H * (Wp * Pp + Wm * Pm) = Wp * Pp - Wm * Pm := by
      rw [hHdec]
      simp only [Matrix.sub_mul, Matrix.mul_add, ← Matrix.mul_assoc, hPpWm, hPmWp, hPpPm, hPmPp,
        hA, hB]
      abel
    rw [hUH, hHU]
  · rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, hWpA, hWmA, ← Matrix.add_mul, hsum,
      Matrix.one_mul]

end GlobalTheory.HCXi
end
end
