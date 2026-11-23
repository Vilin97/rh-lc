module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.DetFirstCayleyBlockNeGroup
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.LocTauAlt
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.SecondCoordMulInner
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Imports
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GaussS
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
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
public import Mathlib.LinearAlgebra.Matrix.Rank
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
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GaussS
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ContinuousGramX
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GaussM
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.HermTranspose
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.NormMono
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.SecondCoordMulInner
import Mathlib.RingTheory.SimpleRing.Principal
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.TraceTransposeMul

section

@[expose] public section

noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.HSt.L3

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR.G

variable {m n : ℕ}

theorem det_gram_eq_zero (hmn : m < n) (x : Fin m → Fin n → ℂ) : (gramX (fun _ : Fin m => true) x).det = 0 := by
  have hg : gramX (fun _ : Fin m => true) x = (Matrix.of x)ᴴ * Matrix.of x := by
    ext i j
    simp [gramX, evX, Qp, Qb, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [hg]
  by_contra hne
  have hu : IsUnit ((Matrix.of x)ᴴ * Matrix.of x) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hne)
  have h1 := Matrix.rank_of_isUnit _ hu
  have h2 := Matrix.rank_mul_le_right (Matrix.of x)ᴴ (Matrix.of x)
  have h3 := Matrix.rank_le_height (Matrix.of x)
  simp only [Fintype.card_fin] at h1 h3
  omega

theorem trace_transpose_mul' (X Y : Matrix (Fin n) (Fin n) ℂ) : (Xᵀ * Y).trace = (Yᵀ * X).trace := by
  rw [← Matrix.trace_transpose, Matrix.transpose_mul, Matrix.transpose_transpose]

end PositivityTheory.Rg.Sw.HSt.L3
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.InnerGen

section

@[expose] public section

noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.HSt.L3

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR.G

variable {m n : ℕ}

theorem inner_gen (ψ : (Fin n → Fin n → ℝ) → ℂ) (hψ : IsSingTest ψ) (Q : Matrix (Fin n) (Fin n) ℂ)
    (hQ : Q.IsHermitian) (hd : Q.det = 0) :
    ∫ s, ψ s * Complex.exp (Complex.I * ((herm s)ᵀ * Q).trace) = 0 := by
  obtain ⟨_, _, h⟩ := hψ
  have hπ : (2 * (Real.pi : ℂ)) ≠ 0 := by
    have h0 : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    exact_mod_cast h0
  have hβH : (((2 * (Real.pi : ℂ)))⁻¹ • Qᵀ).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, hQ.transpose.eq]
    congr 1
    simp [Complex.conj_ofReal]
  have hβd : (((2 * (Real.pi : ℂ)))⁻¹ • Qᵀ).det = 0 := by
    rw [Matrix.det_smul, Matrix.det_transpose, hd, mul_zero]
  have key := h _ hβH hβd
  rw [← key]
  congr 1
  ext s
  simp only [eTr]
  congr 2
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, trace_transpose_mul' (herm s) Q]
  field_simp

open PositivityTheory.Rg.Sw.WR.G.GM in
theorem core2 (hmn : m < n) (R : Matrix (Fin n) (Fin n) ℂ) (hR : IsUnit R.det) (H0 : Matrix (Fin n) (Fin n) ℂ)
    (hH : H0.IsHermitian) (ψ : (Fin n → Fin n → ℝ) → ℂ) (hψ : IsSingTest ψ) :
    ∫ s, ψ s * ((R * Rᴴ - Complex.I • (H0 + herm s)).det)⁻¹ ^ m = 0 := by
  have hψ0 := hψ
  obtain ⟨hψc, hψs, -⟩ := hψ0
  have hRR : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R hR
  have hRRh : (R⁻¹)ᴴ * Rᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hRR, Matrix.conjTranspose_one]
  have hBH : ∀ s : Fin n → Fin n → ℝ, (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ).IsHermitian := by
    intro s
    have h := Matrix.isHermitian_conjTranspose_mul_mul (R⁻¹)ᴴ (hH.add (GM.herm_isHermitian s))
    rwa [Matrix.conjTranspose_conjTranspose] at h
  have hD : ∀ s : Fin n → Fin n → ℝ, (1 - Complex.I • (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ)).det ≠ 0 := by
    intro s
    have h := GM.det_ne_zero (hBH s) 1
    simpa using h
  have hfac : ∀ s : Fin n → Fin n → ℝ, R * Rᴴ - Complex.I • (H0 + herm s) =
      R * (1 - Complex.I • (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ)) * Rᴴ := by
    intro s
    have hM : R * (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ) * Rᴴ = H0 + herm s := by
      simp only [← Matrix.mul_assoc, hRR, Matrix.one_mul]
      rw [Matrix.mul_assoc, hRRh, Matrix.mul_one]
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, hM]
  have hbase : ∀ s : Fin n → Fin n → ℝ, secN (fun _ : Fin m => true) 1 1 1 (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ) =
      ((Real.pi : ℂ) ^ n / (1 - Complex.I • (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ)).det) ^ m := by
    intro s
    have hA : ∀ a : Fin m, Amat (fun _ : Fin m => true) 1 1 (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ) a =
        (1 - Complex.I • (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ))ᵀ := by
      intro a
      simp [Amat, sgn, Matrix.transpose_sub, Matrix.transpose_smul]
    rw [base m n _ 1 1 one_pos _ (hBH s)]
    simp only [hA, Matrix.det_transpose, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hdR : R.det ≠ 0 := hR.ne_zero
  have hdRh : Rᴴ.det ≠ 0 := by
    rw [Matrix.det_conjTranspose]
    exact star_ne_zero.2 hdR
  have hπ : (Real.pi : ℂ) ^ n ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)
  have halg : ∀ (P D A B Y : ℂ), P ≠ 0 → D ≠ 0 → A ≠ 0 → B ≠ 0 →
      Y * (A * D * B)⁻¹ ^ m = (A * B * P)⁻¹ ^ m * (Y * (P / D) ^ m) := by
    intro P D A B Y hP hD' hA' hB'
    have k : (A * D * B)⁻¹ = (A * B * P)⁻¹ * (P / D) := by
      field_simp
    rw [k, mul_pow]
    ring
  have hpt : ∀ s : Fin n → Fin n → ℝ, ψ s * ((R * Rᴴ - Complex.I • (H0 + herm s)).det)⁻¹ ^ m =
      ((R.det * Rᴴ.det) * (Real.pi : ℂ) ^ n)⁻¹ ^ m *
        (ψ s * secN (fun _ : Fin m => true) 1 1 1 (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ)) := by
    intro s
    rw [hfac s, Matrix.det_mul, Matrix.det_mul, hbase s]
    exact halg _ _ _ _ _ hπ (hD s) hdR hdRh
  have hgi : Integrable (fun x : Fin m → Fin n → ℂ => evX (1 : PX m n) x * gs 1 x) volume :=
    integP m n 1 one_pos 1
  have hψi : Integrable ψ volume := hψc.integrable_of_hasCompactSupport hψs
  have hherm : Continuous (herm : (Fin n → Fin n → ℝ) → Matrix (Fin n) (Fin n) ℂ) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [herm]
    fun_prop
  have hint : Integrable (Function.uncurry fun (s : Fin n → Fin n → ℝ) (x : Fin m → Fin n → ℂ) =>
      ψ s * (evX (1 : PX m n) x * gs 1 x *
        Complex.exp (Complex.I * ((1 : ℝ) : ℂ) *
          (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x).trace)))
      (volume.prod volume) := by
    refine Integrable.mono' (hψi.norm.mul_prod hgi.norm) ?_ ?_
    · apply Continuous.aestronglyMeasurable
      have h1 : Continuous fun p : (Fin n → Fin n → ℝ) × (Fin m → Fin n → ℂ) =>
          R⁻¹ * (H0 + herm p.1) * (R⁻¹)ᴴ * gramX (fun _ : Fin m => true) p.2 :=
        ((continuous_const.matrix_mul (continuous_const.add (hherm.comp continuous_fst))).matrix_mul
          continuous_const).matrix_mul ((continuous_gramX _).comp continuous_snd)
      exact (hψc.comp continuous_fst).mul ((((GM.continuous_evX 1).comp continuous_snd).mul
        ((GI.continuous_gs 1).comp continuous_snd)).mul
        (Complex.continuous_exp.comp (continuous_const.mul h1.matrix_trace)))
    · refine Filter.Eventually.of_forall fun p => le_of_eq ?_
      obtain ⟨s, x⟩ := p
      simp only [Function.uncurry_apply_pair, norm_mul]
      rw [GM.norm_phase (hBH s) x, mul_one]
  have hin : ∀ x : Fin m → Fin n → ℂ, ∫ s, ψ s * (evX (1 : PX m n) x * gs 1 x *
        Complex.exp (Complex.I * ((1 : ℝ) : ℂ) *
          (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x).trace)) = 0 := by
    intro x
    have hGH : ((R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x * R⁻¹)ᵀ.IsHermitian :=
      (Matrix.isHermitian_conjTranspose_mul_mul R⁻¹ (GM.gramX_isHermitian _ x)).transpose
    have hGd : ((R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x * R⁻¹)ᵀ.det = 0 := by
      rw [Matrix.det_transpose, Matrix.det_mul, Matrix.det_mul, det_gram_eq_zero hmn x, mul_zero, zero_mul]
    have htr : ∀ s : Fin n → Fin n → ℝ,
        (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x).trace =
          (H0 * ((R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x * R⁻¹)).trace +
          ((herm s)ᵀ * ((R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x * R⁻¹)ᵀ).trace := by
      intro s
      have h1 : (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x).trace =
          ((H0 + herm s) * ((R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x * R⁻¹)).trace := by
        simp only [Matrix.mul_assoc]
        rw [Matrix.trace_mul_comm R⁻¹]
        simp only [Matrix.mul_assoc]
      rw [h1, Matrix.add_mul, Matrix.trace_add]
      congr 1
      rw [← Matrix.trace_transpose (herm s * _), Matrix.transpose_mul, Matrix.trace_mul_comm]
    have hrw : ∀ s : Fin n → Fin n → ℝ, ψ s * (evX (1 : PX m n) x * gs 1 x *
        Complex.exp (Complex.I * ((1 : ℝ) : ℂ) *
          (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x).trace)) =
        (evX (1 : PX m n) x * gs 1 x *
          Complex.exp (Complex.I * (H0 * ((R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x * R⁻¹)).trace)) *
        (ψ s * Complex.exp (Complex.I *
          ((herm s)ᵀ * ((R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x * R⁻¹)ᵀ).trace)) := by
      intro s
      rw [htr s, Complex.ofReal_one, mul_one, mul_add, Complex.exp_add]
      ring
    simp only [hrw]
    rw [integral_const_mul, inner_gen ψ hψ _ hGH hGd, mul_zero]
  have hmain : ∫ s, ψ s * secN (fun _ : Fin m => true) 1 1 1 (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ) = 0 := by
    simp only [secN]
    simp only [← integral_const_mul]
    rw [integral_integral_swap hint]
    simp only [hin, integral_zero]
  simp only [hpt]
  rw [integral_const_mul, hmain, mul_zero]

end PositivityTheory.Rg.Sw.HSt.L3
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.VanishInv

section

@[expose] public section

noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.HSt.L3

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {m n : ℕ}

theorem vanish_inv (hmn : m < n) (e : ℤ) (y b : M2 n) (hy : InG y) (hb : InG b) (hc : IsUnit y.toBlocks₂₁.det)
    (ψ : (Fin n → Fin n → ℝ) → ℂ) (hψ : IsSingTest ψ) :
    ∫ s, fz m e 0 (y * nU (herm s) * b) * ψ s = 0 := by
  obtain ⟨R, H0, κ, hR, hH0, hκ, hf⟩ := factor y b hy hb hc
  have key : ∀ s, fz m e 0 (y * nU (herm s) * b) * ψ s =
      ((y.det * b.det) ^ e * κ ^ (-(m : ℤ))) *
        (ψ s * (R * Rᴴ - Complex.I • (H0 + herm s)).det⁻¹ ^ m) := by
    intro s
    rw [fz_zero, hf, Matrix.det_mul, Matrix.det_mul, det_nU, mul_one]
    simp only [mul_zpow, _root_.zpow_neg, zpow_natCast, inv_pow]
    ring
  simp_rw [key]
  rw [MeasureTheory.integral_const_mul, core2 hmn R hR H0 hH0 ψ hψ, mul_zero]

end PositivityTheory.Rg.Sw.HSt.L3
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.EventuallyUnit

section

@[expose] public section

noncomputable section

open MeasureTheory Matrix Filter Topology Polynomial

namespace PositivityTheory.Rg.Sw.HSt.L3

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {m n : ℕ}

theorem eventually_unit (y : M2 n) (hy : InG y) :
    ∀ᶠ t in 𝓝[≠] (0 : ℝ), IsUnit (y * nbar t).toBlocks₂₁.det := by
  set C := y.toBlocks₂₁ with hC
  set D := y.toBlocks₂₂ with hD
  let M : Matrix (Fin n) (Fin n) ℂ[X] := C.map Polynomial.C + (Polynomial.X : ℂ[X]) • D.map Polynomial.C
  have hev : ∀ z : ℂ, (M.det).eval z = (C + z • D).det := by
    intro z
    rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp [M]
    ring
  have hp : M.det ≠ 0 := by
    intro h0
    have h1 := hev (-Complex.I)
    rw [h0, Polynomial.eval_zero] at h1
    have hu : u1 y = Complex.I • C + D := rfl
    have hmat : C + (-Complex.I) • D = (-Complex.I) • u1 y := by
      rw [hu, smul_add, smul_smul]
      simp
    rw [hmat, Matrix.det_smul] at h1
    exact (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 Complex.I_ne_zero)) (det_first_cayley_block_ne_group y hy)) h1.symm
  have hfin : {t : ℝ | (M.det).eval (t : ℂ) = 0}.Finite := by
    refine ((M.det.roots.toFinset.finite_toSet).preimage Complex.ofReal_injective.injOn).subset ?_
    intro t ht
    simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hp]
    exact ht
  have hS : IsClosed ({t : ℝ | (M.det).eval (t : ℂ) = 0} \ {0}) :=
    (hfin.subset Set.diff_subset).isClosed
  have hnhds : ({t : ℝ | (M.det).eval (t : ℂ) = 0} \ {0})ᶜ ∈ 𝓝 (0 : ℝ) :=
    hS.isOpen_compl.mem_nhds (by simp)
  filter_upwards [nhdsWithin_le_nhds hnhds, self_mem_nhdsWithin] with t ht ht0
  rw [nbar_block, ← hev]
  exact isUnit_iff_ne_zero.2 (fun h => ht ⟨h, ht0⟩)

private theorem inG_mul' {x y : M2 n} (hx : InG x) (hy : InG y) : InG (x * y) := by
  unfold InG at *
  rw [Matrix.conjTranspose_mul]
  calc yᴴ * xᴴ * JJ n * (x * y) = yᴴ * (xᴴ * JJ n * x) * y := by simp only [Matrix.mul_assoc]
    _ = JJ n := by rw [hx, hy]

private theorem inG_nU_herm' (s : Fin n → Fin n → ℝ) : InG (nU (herm s)) := by
  have hh : (herm s)ᴴ = herm s := by
    ext i j
    simp only [herm, Matrix.conjTranspose_apply, Complex.star_def, map_add (f := _), map_div₀, map_mul,
      Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    push_cast
    ring
  simp [InG, nU, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hh]

theorem vanish_all (hmn : m < n) (e : ℤ) (y b : M2 n) (hy : InG y) (hb : InG b)
    (ψ : (Fin n → Fin n → ℝ) → ℂ) (hψ : IsSingTest ψ) :
    ∫ s, fz m e 0 (y * nU (herm s) * b) * ψ s = 0 := by
  let G : ℝ → (Fin n → Fin n → ℝ) → ℂ := fun t s => fz m e 0 (y * nbar t * nU (herm s) * b) * ψ s
  let X : ℝ × (Fin n → Fin n → ℝ) → M2 n := fun p => y * nbar p.1 * nU (herm p.2) * b
  have hIn : ∀ p, InG (X p) := fun p =>
    inG_mul' (inG_mul' (inG_mul' hy (inG_nbar p.1)) (inG_nU_herm' p.2)) hb
  have h1 : Continuous fun p : ℝ × (Fin n → Fin n → ℝ) => nbar (n := n) p.1 := by
    unfold nbar
    exact Continuous.matrix_fromBlocks continuous_const continuous_const
      ((Complex.continuous_ofReal.comp continuous_fst).smul continuous_const) continuous_const
  have h2 : Continuous fun p : ℝ × (Fin n → Fin n → ℝ) => nU (herm p.2) := by
    unfold nU
    refine Continuous.matrix_fromBlocks continuous_const ?_ continuous_const continuous_const
    unfold herm
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fun_prop
  have hX : Continuous X :=
    ((continuous_const.matrix_mul h1).matrix_mul h2).matrix_mul continuous_const
  have hU : Continuous fun p => u1 (X p) := by
    unfold u1
    refine (Continuous.const_smul ?_ Complex.I).add ?_ <;>
      exact continuous_pi fun i => continuous_pi fun j => hX.matrix_elem _ _
  have hcont : Continuous (Function.uncurry G) := by
    have hG : Function.uncurry G = fun p => (X p).det ^ e * (u1 (X p)).det ^ (-(m : ℤ)) * ψ p.2 := by
      funext ⟨t, s⟩
      simp only [Function.uncurry_apply_pair, G, X, fz_zero]
    rw [hG]
    exact ((hX.matrix_det.zpow₀ e fun p => Or.inl (det_ne_of_inG _ (hIn p))).mul
      (hU.matrix_det.zpow₀ _ fun p => Or.inl (det_first_cayley_block_ne_group _ (hIn p)))).mul (hψ.1.comp continuous_snd)
  have hK : IsCompact (tsupport ψ) := hψ.2.1
  have hInt : ∀ t, ∫ s, G t s = ∫ s in tsupport ψ, G t s := fun t =>
    (setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun s hs => by simp [G, image_eq_zero_of_notMem_tsupport hs])).symm
  have hc : Continuous fun t => ∫ s in tsupport ψ, G t s :=
    continuous_parametric_integral_of_continuous hcont hK
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∫ s in tsupport ψ, G t s = 0 := by
    filter_upwards [eventually_unit y hy] with t ht
    rw [← hInt]
    exact vanish_inv hmn e (y * nbar t) b (inG_mul' hy (inG_nbar t)) hb ht ψ hψ
  have hlim : Tendsto (fun t => ∫ s in tsupport ψ, G t s) (𝓝[≠] 0) (𝓝 (∫ s in tsupport ψ, G 0 s)) :=
    (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have h0 : ∫ s in tsupport ψ, G 0 s = 0 :=
    tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hev.mono fun t ht => ht.symm))
  have hn0 : nbar (n := n) 0 = 1 := by simp [nbar]
  have := (hInt 0).trans h0
  simpa [G, hn0] using this

end PositivityTheory.Rg.Sw.HSt.L3
end
end
end
