module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Spectrum
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
public import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TraceLogLeLogDet

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.LogCompress

theorem jensen_exp {ι : Type} [Fintype ι] (w d : ι → ℝ) (hw : ∀ j, 0 ≤ w j) (h1 : ∑ j, w j = 1) :
    0 < ∑ j, w j * Real.exp (d j) ∧ ∑ j, w j * d j ≤ Real.log (∑ j, w j * Real.exp (d j)) ∧
      (∑ j, w j * d j = Real.log (∑ j, w j * Real.exp (d j)) →
        ∀ j, w j ≠ 0 → Real.exp (d j) = ∑ j, w j * Real.exp (d j)) := by
  set m := ∑ j, w j * Real.exp (d j) with hm
  have hpos : 0 < m := by
    obtain ⟨j, -, hj⟩ : ∃ j ∈ (Finset.univ : Finset ι), w j ≠ 0 :=
      Finset.exists_ne_zero_of_sum_ne_zero (by rw [h1]; exact one_ne_zero)
    exact Finset.sum_pos' (fun i _ => mul_nonneg (hw i) (Real.exp_pos _).le)
      ⟨j, Finset.mem_univ _, mul_pos (lt_of_le_of_ne (hw j) hj.symm) (Real.exp_pos _)⟩
  have hexp : ∀ j, Real.exp (d j - Real.log m) = Real.exp (d j) / m := by
    intro j
    rw [Real.exp_sub, Real.exp_log hpos]
  have hnn : ∀ j ∈ (Finset.univ : Finset ι),
      0 ≤ w j * (Real.exp (d j - Real.log m) - (d j - Real.log m + 1)) :=
    fun j _ => mul_nonneg (hw j) (sub_nonneg.2 (Real.add_one_le_exp _))
  have hsum : ∑ j, w j * (Real.exp (d j - Real.log m) - (d j - Real.log m + 1))
      = Real.log m - ∑ j, w j * d j := by
    have : ∀ j, w j * (Real.exp (d j - Real.log m) - (d j - Real.log m + 1))
        = w j * Real.exp (d j) / m - w j * d j + w j * (Real.log m - 1) := by
      intro j
      rw [hexp]; ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div,
      ← Finset.sum_mul, h1, ← hm, div_self hpos.ne']
    ring
  refine ⟨hpos, ?_, ?_⟩
  · have := Finset.sum_nonneg hnn
    linarith
  · intro h j hj
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 (by rw [hsum, h, sub_self]) j
      (Finset.mem_univ _)
    have h2 := (mul_eq_zero.1 h0).resolve_left hj
    have h3 : d j - Real.log m = 0 := by
      by_contra hne
      have := Real.add_one_lt_exp hne
      linarith
    have h4 : d j = Real.log m := by linarith
    rw [h4, Real.exp_log hpos]

theorem compress_diag {ι κ : Type} [Fintype ι] [DecidableEq ι] (C : Matrix ι κ ℂ) (f : ι → ℝ) (k : κ) :
    (Cᴴ * diagonal (fun i => (f i : ℂ)) * C) k k = ((∑ j, Complex.normSq (C j k) * f j : ℝ) : ℂ) := by
  rw [Matrix.mul_apply]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Complex.normSq_eq_conj_mul_self]
  simp only [Complex.star_def]
  ring

theorem exists_diag {κ : Type} [Fintype κ] [DecidableEq κ] (B : Matrix κ κ ℂ) (hB : B.IsHermitian) :
    ∃ (V : Matrix κ κ ℂ) (m : κ → ℂ), V * Vᴴ = 1 ∧ Vᴴ * V = 1 ∧ Vᴴ * B * V = diagonal m := by
  refine ⟨hB.eigenvectorUnitary, RCLike.ofReal ∘ hB.eigenvalues, ?_, ?_, ?_⟩
  · exact (Matrix.mem_unitaryGroup_iff.1 hB.eigenvectorUnitary.2)
  · exact (Matrix.mem_unitaryGroup_iff'.1 hB.eigenvectorUnitary.2)
  · have := hB.conjStarAlgAut_star_eigenvectorUnitary
    simpa [Matrix.star_eq_conjTranspose] using this

theorem trace_log_le_log_det : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (κ : Type) [Fintype κ] [DecidableEq κ] (H A : Matrix ι ι ℂ) (Q : Matrix ι κ ℂ), IsLog H A → Qᴴ * Q = 1 → (Matrix.trace (Qᴴ * H * Q)).re ≤ Real.log (Qᴴ * A * Q).det.re ∧ ((Matrix.trace (Qᴴ * H * Q)).re = Real.log (Qᴴ * A * Q).det.re → ∃ N : Matrix κ κ ℂ, A * Q = Q * N) := by
  intro ι _ _ κ _ _ H A Q ⟨U, d, hU, hH, hA⟩ hQ
  have hAh : A.IsHermitian := by
    rw [hA]
    refine Matrix.isHermitian_mul_mul_conjTranspose _ ?_
    rw [Matrix.isHermitian_diagonal_iff]
    intro i
    exact Complex.conj_ofReal _
  obtain ⟨V, m, hV, hV', hm⟩ := exists_diag _ (Matrix.isHermitian_conjTranspose_mul_mul Q hAh)
  set C : Matrix ι κ ℂ := Uᴴ * Q * V with hC
  have hCH : Cᴴ = Vᴴ * Qᴴ * U := by
    simp [hC, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have key : ∀ D : Matrix ι ι ℂ, Cᴴ * D * C = Vᴴ * (Qᴴ * (U * D * Uᴴ) * Q) * V := by
    intro D
    rw [hCH, hC]
    simp only [Matrix.mul_assoc]
  have hw : ∀ k, ∑ j, Complex.normSq (C j k) = 1 := by
    intro k
    have h := compress_diag C (fun _ => 1) k
    have h1 : diagonal (fun _ : ι => ((1 : ℝ) : ℂ)) = 1 := by simp
    rw [key, h1, Matrix.mul_one, hU, Matrix.mul_one, hQ, Matrix.mul_one, hV'] at h
    simp only [Matrix.one_apply_eq, mul_one] at h
    exact_mod_cast h.symm
  have hmk : ∀ k, m k = ((∑ j, Complex.normSq (C j k) * Real.exp (d j) : ℝ) : ℂ) := by
    intro k
    rw [← compress_diag C (fun j => Real.exp (d j)) k, key, ← hA, hm, Matrix.diagonal_apply_eq]
  have hJ := fun k => jensen_exp (fun j => Complex.normSq (C j k)) d
    (fun j => Complex.normSq_nonneg _) (hw k)
  have hdet : (Qᴴ * A * Q).det.re = ∏ k, ∑ j, Complex.normSq (C j k) * Real.exp (d j) := by
    have h := congrArg Matrix.det hm
    rw [Matrix.det_mul_comm, ← Matrix.mul_assoc, hV, Matrix.one_mul, Matrix.det_diagonal] at h
    rw [h]
    simp only [hmk]
    rw [← Complex.ofReal_prod, Complex.ofReal_re]
  have htr : (Matrix.trace (Qᴴ * H * Q)).re = ∑ k, ∑ j, Complex.normSq (C j k) * d j := by
    have h : Matrix.trace (Cᴴ * diagonal (fun i => (d i : ℂ)) * C) = Matrix.trace (Qᴴ * H * Q) := by
      rw [key, ← hH, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hV, Matrix.one_mul]
    rw [← h, Matrix.trace]
    simp only [Matrix.diag_apply, compress_diag]
    rw [← Complex.ofReal_sum, Complex.ofReal_re]
  rw [hdet, htr, Real.log_prod (fun k _ => (hJ k).1.ne')]
  refine ⟨Finset.sum_le_sum fun k _ => (hJ k).2.1, fun h => ?_⟩
  have heq := (Finset.sum_eq_sum_iff_of_le fun k _ => (hJ k).2.1).1 h
  have hDC : diagonal (fun i => (Real.exp (d i) : ℂ)) * C = C * diagonal m := by
    ext j k
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases h0 : C j k = 0
    · simp [h0]
    · have := (hJ k).2.2 (heq k (Finset.mem_univ _)) j (by simpa using h0)
      rw [hmk, ← this, mul_comm]
  refine ⟨V * diagonal m * Vᴴ, ?_⟩
  have h1 : A * Q = U * (diagonal (fun i => (Real.exp (d i) : ℂ)) * C) * Vᴴ := by
    rw [hA, hC]
    simp only [Matrix.mul_assoc, hV, Matrix.mul_one]
  rw [h1, hDC, hC]
  simp only [← Matrix.mul_assoc, hU, Matrix.one_mul]

end GlobalTheory.LogCompress
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsometryMatrixRange

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_isometry_matrix_range {ι : Type} [Fintype ι] [DecidableEq ι] (W : Submodule ℂ (ι → ℂ)) :
    ∃ (n : ℕ) (Q : Matrix ι (Fin n) ℂ), Qᴴ * Q = 1 ∧ ∀ v, v ∈ W ↔ ∃ x, v = Q *ᵥ x := by
  let W' : Submodule ℂ (EuclideanSpace ℂ ι) := W.comap (WithLp.linearEquiv 2 ℂ (ι → ℂ)).toLinearMap
  let b := stdOrthonormalBasis ℂ W'
  refine ⟨_, Matrix.of fun i j => (b j : EuclideanSpace ℂ ι) i, ?_, ?_⟩
  · ext j k
    have h := orthonormal_iff_ite.mp b.orthonormal j k
    rw [Submodule.coe_inner, PiLp.inner_apply] at h
    rw [Matrix.mul_apply, Matrix.one_apply, ← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_comm]
  · intro v
    constructor
    · intro hv
      let w : W' := ⟨WithLp.toLp 2 v, hv⟩
      refine ⟨fun j => b.repr w j, ?_⟩
      ext i
      have h := congrArg (fun z : W' => (z : EuclideanSpace ℂ ι) i) (b.sum_repr w)
      simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at h
      have h2 : v i = (w : EuclideanSpace ℂ ι) i := rfl
      rw [h2, ← h]
      simp [Matrix.mulVec, dotProduct, mul_comm]
    · rintro ⟨x, rfl⟩
      have h : (Matrix.of fun i j => (b j : EuclideanSpace ℂ ι) i) *ᵥ x
          = ∑ j, x j • (b j : EuclideanSpace ℂ ι).ofLp := by
        ext i
        simp [Matrix.mulVec, dotProduct, mul_comm]
      rw [h]
      exact W.sum_mem fun j _ => W.smul_mem _ (b j).2

theorem ss_of_harm : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Type) [Fintype σ] (τ : σ ≃ σ)
    (g : σ → Matrix ι ι ℂ), (∀ s, g (τ s) * g s = 1) → Harm g → SS (Set.range g) := by
  intro ι _ _ σ _ τ g hτ hH W hW
  obtain ⟨H, hlog, hsum⟩ := hH
  obtain ⟨n, Q, hQ, hmem⟩ := exists_isometry_matrix_range W
  have hN : ∀ s, ∃ N : Matrix (Fin n) (Fin n) ℂ, g s * Q = Q * N := by
    intro s
    have : ∀ j : Fin n, ∃ x, g s *ᵥ (Q *ᵥ Pi.single j 1) = Q *ᵥ x := fun j =>
      (hmem _).1 (hW _ ⟨s, rfl⟩ _ ((hmem _).2 ⟨_, rfl⟩))
    choose x hx using this
    refine ⟨Matrix.of fun i j => x j i, ?_⟩
    ext i j
    have h := congrFun (hx j) i
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at h
    exact h
  choose N hN using hN
  have hNinv : ∀ s, N (τ s) * N s = 1 := by
    intro s
    have h : Q * (N (τ s) * N s) = Q := by
      rw [← Matrix.mul_assoc, ← hN, Matrix.mul_assoc, ← hN, ← Matrix.mul_assoc, hτ, Matrix.one_mul]
    have h2 := congrArg (fun X => Qᴴ * X) h
    simpa only [← Matrix.mul_assoc, hQ, Matrix.one_mul] using h2
  have hdet : ∀ s, (Qᴴ * ((g s)ᴴ * g s) * Q).det.re = Complex.normSq (N s).det := by
    intro s
    have h : Qᴴ * ((g s)ᴴ * g s) * Q = (N s)ᴴ * N s := by
      calc Qᴴ * ((g s)ᴴ * g s) * Q = (g s * Q)ᴴ * (g s * Q) := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = (N s)ᴴ * (Qᴴ * Q) * N s := by
            rw [hN]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [hQ, Matrix.mul_one]
    rw [h, Matrix.det_mul, Matrix.det_conjTranspose, Complex.star_def,
      ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  set a : σ → ℝ := fun s => Real.log (Complex.normSq (N s).det) with ha
  have hpair : ∀ s, a (τ s) + a s = 0 := by
    intro s
    have h : Complex.normSq (N (τ s)).det * Complex.normSq (N s).det = 1 := by
      rw [← map_mul, ← Matrix.det_mul, hNinv, Matrix.det_one, map_one]
    simp only [ha]
    rw [← Real.log_mul (left_ne_zero_of_mul_eq_one h) (right_ne_zero_of_mul_eq_one h), h, Real.log_one]
  have hasum : ∑ s, a s = 0 := by
    have h : ∑ s, (a (τ s) + a s) = 0 := Finset.sum_eq_zero fun s _ => hpair s
    rw [Finset.sum_add_distrib, Equiv.sum_comp τ a] at h
    linarith
  have htsum : ∑ s, (Matrix.trace (Qᴴ * H s * Q)).re = 0 := by
    rw [← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.sum_mul, ← Matrix.mul_sum, hsum]
    simp
  have hJ := fun s => GlobalTheory.LogCompress.trace_log_le_log_det ι (Fin n) (H s) ((g s)ᴴ * g s) Q (hlog s) hQ
  have heq : ∀ s, (Matrix.trace (Qᴴ * H s * Q)).re = a s := by
    have h := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
      (f := fun s => (Matrix.trace (Qᴴ * H s * Q)).re) (g := a)
      (fun s _ => by have := (hJ s).1; rwa [hdet] at this)).1 (by rw [htsum, hasum])
    exact fun s => h s (Finset.mem_univ s)
  have hadj : ∀ s, ∃ M : Matrix (Fin n) (Fin n) ℂ, Qᴴ * g s = M * Qᴴ := by
    intro s
    obtain ⟨M, hM⟩ := (hJ s).2 (by rw [hdet]; exact heq s)
    have h1 : N s * N (τ s) = 1 := mul_eq_one_comm.1 (hNinv s)
    have h2 : (g s)ᴴ * Q = Q * (M * N (τ s)) := by
      rw [← Matrix.mul_assoc, ← hM, Matrix.mul_assoc (g s)ᴴ, hN, Matrix.mul_assoc, Matrix.mul_assoc, h1,
        Matrix.mul_one]
    refine ⟨(M * N (τ s))ᴴ, ?_⟩
    have h3 := congrArg Matrix.conjTranspose h2
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_mul Q] at h3
  refine ⟨LinearMap.ker (Matrix.mulVecLin Qᴴ), ?_, ?_, ?_⟩
  · rintro _ ⟨s, rfl⟩ v hv
    obtain ⟨M, hM⟩ := hadj s
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
    rw [Matrix.mulVec_mulVec, hM, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  · rw [Submodule.disjoint_def]
    intro v hv hv'
    obtain ⟨x, rfl⟩ := (hmem v).1 hv
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hQ, Matrix.one_mulVec] at hv'
    rw [hv', Matrix.mulVec_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    refine Submodule.mem_sup.2 ⟨Q *ᵥ (Qᴴ *ᵥ v), (hmem _).2 ⟨_, rfl⟩, v - Q *ᵥ (Qᴴ *ᵥ v), ?_, by abel⟩
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_sub, Matrix.mulVec_mulVec (Qᴴ *ᵥ v), hQ,
      Matrix.one_mulVec, sub_self]

end GlobalTheory.ClassFin
end
end
