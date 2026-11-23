module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.ENatToNat
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowerTransvectionMulVecMemSpanWeightVectorsDominStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowerTriangularGLComplexInductionStatement
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.Topology.Algebra.MvPolynomial
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLUDecompositionOfLeadingMinorsNeZero

section

@[expose] public section

open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory.LUDecomp

lemma exists_row {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (i : Fin n)
    (hdet : (B.submatrix (Fin.castLE i.is_lt.le) (Fin.castLE i.is_lt.le)).det ≠ 0) :
    ∃ x : Fin n → ℂ, (∀ j, i ≤ j → x j = 0) ∧ ∀ k, k < i → B i k + ∑ j, x j * B j k = 0 := by
  have h : (i : ℕ) ≤ n := i.is_lt.le
  set A := B.submatrix (Fin.castLE h) (Fin.castLE h) with hAdef
  have hA : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
  let c : Fin i → ℂ := fun k => B i (Fin.castLE h k)
  let y : Fin i → ℂ := -(c ᵥ* A⁻¹)
  have hy : y ᵥ* A = -c := by
    simp only [y, Matrix.neg_vecMul, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hA, Matrix.vecMul_one]
  refine ⟨fun j => if hj : (j : ℕ) < i then y ⟨j, hj⟩ else 0, ?_, ?_⟩
  · intro j hj
    have : ¬ ((j : ℕ) < i) := not_lt.mpr hj
    simp [this]
  · intro k hk
    have hsum : ∑ j : Fin n, (if hj : (j : ℕ) < i then y ⟨j, hj⟩ else 0) * B j k
        = ∑ j' : Fin i, y j' * B (Fin.castLE h j') k := by
      symm
      apply Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h)
      · intro j hj
        have : ¬ ((j : ℕ) < i) := by
          intro hlt; exact hj ⟨⟨j, hlt⟩, Fin.ext rfl⟩
        simp [this]
      · intro j'
        simp [j'.is_lt]
    have hk' := congrFun hy ⟨k, hk⟩
    have hkk : Fin.castLE h ⟨k, hk⟩ = k := Fin.ext rfl
    simp only [Matrix.vecMul, dotProduct, hAdef, Matrix.submatrix_apply, Pi.neg_apply, hkk, c] at hk'
    rw [hsum, hk']
    ring

theorem lu : ∀ {n : ℕ} (B : GL (Fin n) ℂ), (∀ (k : ℕ) (hk : k ≤ n), (B.val.submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0) → ∃ L U : GL (Fin n) ℂ, L.val.BlockTriangular OrderDual.toDual ∧ U.val.BlockTriangular id ∧ B = L * U := by
  intro n B hB
  have hx : ∀ i : Fin n, ∃ x : Fin n → ℂ, (∀ j, i ≤ j → x j = 0) ∧
      ∀ k, k < i → B.val i k + ∑ j, x j * B.val j k = 0 :=
    fun i => exists_row B.val i (hB i i.is_lt.le)
  choose x hx0 hx1 using hx
  let M : Matrix (Fin n) (Fin n) ℂ := fun i j => x i j + if i = j then 1 else 0
  have hMlow : M.BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hij' : i < j := hij
    simp [M, hx0 i j hij'.le, hij'.ne]
  have hMdet : M.det = 1 := by
    rw [Matrix.det_of_lowerTriangular M hMlow]
    exact Finset.prod_eq_one (fun i _ => by simp [M, hx0 i i le_rfl])
  have hMunit : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).mpr (by rw [hMdet]; exact isUnit_one)
  let Mg : GL (Fin n) ℂ := hMunit.unit
  have hMg : (Mg : Matrix (Fin n) (Fin n) ℂ) = M := rfl
  refine ⟨Mg⁻¹, Mg * B, ?_, ?_, by simp⟩
  · rw [Matrix.coe_units_inv, hMg]
    have : Invertible M := M.invertibleOfIsUnitDet ((Matrix.isUnit_iff_isUnit_det M).mp hMunit)
    exact Matrix.blockTriangular_inv_of_blockTriangular hMlow
  · intro i k hik
    have hik' : k < i := hik
    show (M * B.val) i k = 0
    rw [Matrix.mul_apply]
    have := hx1 i k hik'
    simp only [M, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [add_comm]
    exact this

end GlobalTheory.LUDecomp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLUDecompositionOfLeadingMinorsNeZeroStatement

section

@[expose] public section

open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

theorem _root_.GlobalTheory.T.exists_LU_decomposition_of_leading_minors_ne_zero : ∀ {n : ℕ} (B : GL (Fin n) ℂ), (∀ (k : ℕ) (hk : k ≤ n), (B.val.submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0) → ∃ L U : GL (Fin n) ℂ, L.val.BlockTriangular OrderDual.toDual ∧ U.val.BlockTriangular id ∧ B = L * U := by
  first | exact @GlobalTheory.LUDecomp.lu | exact GlobalTheory.LUDecomp.lu | (intros; apply GlobalTheory.LUDecomp.lu <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteShiftsVanishingLeadingMinor

section

@[expose] public section

open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory

theorem shift_minors_vanish_finite {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) :
    Set.Finite {s : ℂ | ¬ ∀ (k : ℕ) (hk : k ≤ n),
      ((B + s • (1 : Matrix (Fin n) (Fin n) ℂ)).submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0} := by
  classical
  let p : ℕ → Polynomial ℂ := fun k =>
    if hk : k ≤ n then (-(B.submatrix (Fin.castLE hk) (Fin.castLE hk))).charpoly else 1
  have key : ∀ (k : ℕ) (hk : k ≤ n) (s : ℂ),
      ((B + s • (1 : Matrix (Fin n) (Fin n) ℂ)).submatrix (Fin.castLE hk) (Fin.castLE hk)).det
        = (p k).eval s := by
    intro k hk s
    simp only [p, dif_pos hk, Matrix.eval_charpoly]
    congr 1
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
      Matrix.neg_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply,
      Fin.castLE_inj, smul_eq_mul, sub_neg_eq_add]
    split_ifs <;> ring
  have hp : ∀ k, p k ≠ 0 := by
    intro k
    by_cases hk : k ≤ n
    · simp only [p, dif_pos hk]; exact (Matrix.charpoly_monic _).ne_zero
    · simp [p, dif_neg hk]
  refine Set.Finite.subset
    ((Finset.range (n + 1)).finite_toSet.biUnion fun k _ =>
      Polynomial.finite_setOf_isRoot (hp k)) ?_
  intro s hs
  simp only [Set.mem_setOf_eq, not_forall, not_not] at hs
  obtain ⟨k, hk, h0⟩ := hs
  simp only [Set.mem_iUnion, Finset.coe_range, Set.mem_Iio, Set.mem_setOf_eq]
  exact ⟨k, Nat.lt_succ_of_le hk, by rw [Polynomial.IsRoot, ← key k hk s, h0]⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteShiftsVanishingLeadingMinorStatement

section

@[expose] public section

open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

theorem _root_.GlobalTheory.T.finite_shifts_vanishing_leading_minor : ∀ {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ), Set.Finite {s : ℂ | ¬ ∀ (k : ℕ) (hk : k ≤ n), ((B + s • (1 : Matrix (Fin n) (Fin n) ℂ)).submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0} := by
  first | exact @GlobalTheory.shift_minors_vanish_finite | exact GlobalTheory.shift_minors_vanish_finite | (intros; apply GlobalTheory.shift_minors_vanish_finite <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolyRepMulVecMemOfCofiniteScalarShift

section

@[expose] public section

open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory.AlgWtHW

theorem mulVec_mem_of_cofinite_shift : ∀ {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ → ∀ (S : Submodule ℂ (ι → ℂ)) (v : ι → ℂ)
    (B : GL (Fin n) ℂ) (F : Set ℂ), F.Finite →
    (∀ s ∉ F, ∀ C : GL (Fin n) ℂ, C.val = B.val + s • (1 : Matrix (Fin n) (Fin n) ℂ) → Φ C *ᵥ v ∈ S) →
    Φ B *ᵥ v ∈ S := by
  intro n ι _ _ Φ hΦ S v B F hF hS
  choose Q hQ using hΦ.poly
  let M : ℂ → Matrix (Fin n) (Fin n) ℂ := fun s => B.val + s • (1 : Matrix (Fin n) (Fin n) ℂ)
  let x : ℂ → ((Fin n × Fin n) ⊕ (Fin n × Fin n)) → ℂ :=
    fun s => Sum.elim (fun p => M s p.1 p.2) (fun p => (M s)⁻¹ p.1 p.2)
  let g : ℂ → ι → ℂ := fun s i => ∑ j, MvPolynomial.eval (x s) (Q i j) * v j
  have hMc : Continuous M := by
    fun_prop
  have hdetB : IsUnit (B.val).det := (Matrix.isUnit_iff_isUnit_det _).1 B.isUnit
  have hM0 : M 0 = B.val := by simp [M]
  have hinvc : ContinuousAt (fun s => (M s)⁻¹) 0 := by
    have h1 : ContinuousAt Inv.inv (M 0) := by
      apply continuousAt_matrix_inv
      rw [hM0]
      exact NormedRing.inverse_continuousAt hdetB.unit
    exact h1.comp hMc.continuousAt
  have hxc : ContinuousAt x 0 := by
    rw [continuousAt_pi]
    rintro (p | p)
    · exact ((continuous_apply p.2).comp ((continuous_apply p.1).comp hMc)).continuousAt
    · exact ((continuous_apply p.2).comp (continuous_apply p.1)).continuousAt.comp hinvc
  have hgc : ContinuousAt g 0 := by
    rw [continuousAt_pi]
    intro i
    apply tendsto_finsetSum
    intro j _
    exact (((MvPolynomial.continuous_eval (Q i j)).continuousAt).comp hxc).mul continuousAt_const

  have hgC : ∀ s, ∀ C : GL (Fin n) ℂ, C.val = M s → g s = Φ C *ᵥ v := by
    intro s C hC
    funext i
    simp only [g, Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hQ i j C]
    have hx : x s = Sum.elim (fun p => C.val p.1 p.2) (fun p => (C⁻¹).val p.1 p.2) := by
      funext q
      rcases q with p | p
      · simp [x, hC]
      · simp [x, Matrix.coe_units_inv, hC]
    rw [hx]
  have hg0 : g 0 = Φ B *ᵥ v := hgC 0 B hM0.symm
  have hdetev : ∀ᶠ s in nhds (0:ℂ), IsUnit (M s).det := by
    have hc : ContinuousAt (fun s => (M s).det) 0 := hMc.matrix_det.continuousAt
    have : IsOpen {z : ℂ | z ≠ 0} := isOpen_ne
    have hne : (M 0).det ≠ 0 := by rw [hM0]; exact hdetB.ne_zero
    filter_upwards [hc.eventually (this.mem_nhds hne)] with s hs
    exact isUnit_iff_ne_zero.2 hs
  have hFev : ∀ᶠ s in nhdsWithin (0:ℂ) {0}ᶜ, s ∉ F := by
    have hcl : IsClosed (F \ {0}) := (hF.diff).isClosed
    have hmem : (F \ {0})ᶜ ∈ nhds (0:ℂ) := hcl.isOpen_compl.mem_nhds (by simp)
    filter_upwards [nhdsWithin_le_nhds hmem, self_mem_nhdsWithin] with s hs1 hs2
    intro hsF
    exact hs1 ⟨hsF, hs2⟩
  have hev : ∀ᶠ s in nhdsWithin (0:ℂ) {0}ᶜ, g s ∈ S := by
    filter_upwards [hFev, nhdsWithin_le_nhds hdetev] with s hs hdet
    rw [hgC s (Matrix.nonsingInvUnit (M s) hdet) rfl]
    exact hS s hs _ rfl
  have ht : Filter.Tendsto g (nhdsWithin (0:ℂ) {0}ᶜ) (nhds (Φ B *ᵥ v)) := by
    rw [← hg0]
    exact hgc.tendsto.mono_left nhdsWithin_le_nhds
  exact (Submodule.closed_of_finiteDimensional S).mem_of_tendsto ht hev

end GlobalTheory.AlgWtHW
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolyRepMulVecMemOfCofiniteScalarShiftStatement

section

@[expose] public section

open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

theorem _root_.GlobalTheory.T.polyRep_mulVec_mem_of_cofinite_scalar_shift : ∀ {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ → ∀ (S : Submodule ℂ (ι → ℂ)) (v : ι → ℂ) (B : GL (Fin n) ℂ) (F : Set ℂ), F.Finite → (∀ s ∉ F, ∀ C : GL (Fin n) ℂ, C.val = B.val + s • (1 : Matrix (Fin n) (Fin n) ℂ) → Φ C *ᵥ v ∈ S) → Φ B *ᵥ v ∈ S := by
  first | exact @GlobalTheory.AlgWtHW.mulVec_mem_of_cofinite_shift | exact GlobalTheory.AlgWtHW.mulVec_mem_of_cofinite_shift | (intros; apply GlobalTheory.AlgWtHW.mulVec_mem_of_cofinite_shift <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulVecMemSpanLowerWeightsOfBorelEigenvector

section

@[expose] public section

open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory.AlgWtHW

theorem mulVec_mem_sle_of_isBEig : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ → ∀ (v : ι → ℂ) (lam : Fin n → ℤ), IsBEig Φ v lam → ∀ B : GL (Fin n) ℂ, Φ B *ᵥ v ∈ Sle Φ lam := by
  intro n ι _ _ Φ hΦ v lam hv B
  have hdom : DomLE lam lam := ⟨rfl, fun _ => le_rfl⟩
  have hvS : v ∈ Sle Φ lam := by
    refine Submodule.subset_span ⟨lam, hdom, fun D hD => hv.2 D ?_⟩
    intro a b hab
    exact hD (ne_of_gt hab)

  have hstab : ∀ L : GL (Fin n) ℂ, L.val.BlockTriangular OrderDual.toDual →
      ∀ w ∈ Sle Φ lam, Φ L *ᵥ w ∈ Sle Φ lam := by
    refine GlobalTheory.T.lowerTriangular_GL_complex_induction _ ?_ ?_ ?_ ?_
    · intro w hw; rw [hΦ.one, one_mulVec]; exact hw
    · intro A C hA hC w hw
      rw [hΦ.mul, ← mulVec_mulVec]
      exact hA _ (hC w hw)
    · intro D hD w hw
      refine Submodule.span_induction (p := fun w _ => Φ D *ᵥ w ∈ Sle Φ lam) ?_ ?_ ?_ ?_ hw
      · rintro u ⟨ν, hν, hu⟩
        rw [hu D hD]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨ν, hν, hu⟩)
      · simp
      · intro x y _ _ hx hy; rw [mulVec_add]; exact Submodule.add_mem _ hx hy
      · intro c x _ hx; rw [mulVec_smul]; exact Submodule.smul_mem _ _ hx
    · intro i j s T hji hT w hw
      refine Submodule.span_induction (p := fun w _ => Φ T *ᵥ w ∈ Sle Φ lam) ?_ ?_ ?_ ?_ hw
      · rintro u ⟨ν, hν, hu⟩
        exact GlobalTheory.T.lowerTransvection_mulVec_mem_spanWeightVectorsDominatedBy Φ hΦ lam ν hν u hu i j hji s T hT
      · simp
      · intro x y _ _ hx hy; rw [mulVec_add]; exact Submodule.add_mem _ hx hy
      · intro c x _ hx; rw [mulVec_smul]; exact Submodule.smul_mem _ _ hx

  have hbig : ∀ C : GL (Fin n) ℂ,
      (∀ (k : ℕ) (hk : k ≤ n), (C.val.submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0) →
      Φ C *ᵥ v ∈ Sle Φ lam := by
    intro C hC
    obtain ⟨L, U, hL, hU, rfl⟩ := GlobalTheory.T.exists_LU_decomposition_of_leading_minors_ne_zero C hC
    rw [hΦ.mul, ← mulVec_mulVec, hv.2 U hU, mulVec_smul]
    exact Submodule.smul_mem _ _ (hstab L hL v hvS)

  refine GlobalTheory.T.polyRep_mulVec_mem_of_cofinite_scalar_shift Φ hΦ _ v B _ (GlobalTheory.T.finite_shifts_vanishing_leading_minor B.val) ?_
  intro s hs C hC
  apply hbig
  rw [hC]
  simpa using hs

end GlobalTheory.AlgWtHW
end
end
