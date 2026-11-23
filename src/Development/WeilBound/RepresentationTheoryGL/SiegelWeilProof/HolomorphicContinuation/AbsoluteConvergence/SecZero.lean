module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.DerivativeVacuumDilationsAlt
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SecZeroA
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SecZeroB

section

@[expose] public section

noncomputable section

open Matrix Filter Topology Set Polynomial

namespace PositivityTheory.Rg.Sw.AbsSt.SZ

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

def lowM (n : ℕ) (s : ℝ) : M2 n := fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) 0 ((s : ℂ) • 1) 1

lemma lowM_mul (s s' : ℝ) : lowM n s * lowM n s' = lowM n (s + s') := by
  simp only [lowM, fromBlocks_multiply]
  simp [add_smul]

lemma lowM_zero : lowM n 0 = 1 := by
  unfold lowM; simp [fromBlocks_one]

def lowU (n : ℕ) (s : ℝ) : GL (Fin n ⊕ Fin n) ℂ :=
  ⟨lowM n s, lowM n (-s), by rw [lowM_mul, add_neg_cancel, lowM_zero], by rw [lowM_mul, neg_add_cancel, lowM_zero]⟩

def lowG (n : ℕ) (s : ℝ) : GR n := ⟨lowU n s, InG_lower s⟩

lemma lowG_cont : Continuous (lowG n) := by
  unfold lowG
  apply Continuous.subtype_mk
  rw [Units.continuous_iff]
  have hc : Continuous (fun s : ℝ => lowM n s) := by
    unfold lowM
    exact Continuous.matrix_fromBlocks continuous_const continuous_const
      (Complex.continuous_ofReal.smul continuous_const) continuous_const
  exact ⟨hc, hc.comp continuous_neg⟩

lemma lowG_zero : lowG n 0 = 1 := by
  apply Subtype.ext
  apply Units.ext
  exact lowM_zero

lemma mR_mul (a b : GR n) : mR (a * b) = mR a * mR b := rfl

lemma lower_left_block_lowering_mul (y : GR n) (s : ℝ) :
    (mR (y * lowG n s)).toBlocks₂₁ = (mR y).toBlocks₂₁ + (s : ℂ) • (mR y).toBlocks₂₂ := by
  rw [mR_mul]
  show (mR y * lowM n s).toBlocks₂₁ = _
  conv_lhs => rw [← fromBlocks_toBlocks (mR y)]
  unfold lowM
  rw [fromBlocks_multiply]
  simp

lemma dense_cell (y : GR n) : y ∈ closure {z : GR n | ((mR z).toBlocks₂₁).det ≠ 0} := by
  classical
  obtain ⟨C, hC⟩ : ∃ C, C = (mR y).toBlocks₂₁ := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = (mR y).toBlocks₂₂ := ⟨_, rfl⟩
  have hG : (mR y)ᴴ * JJ n * mR y = JJ n := y.2
  have hgg : mR y * mR y⁻¹ = 1 := by
    rw [← mR_mul, mul_inv_cancel]
    rfl
  have hJJ : JJ n * JJ n = -1 := by
    rw [JJ, fromBlocks_multiply]
    simp [← fromBlocks_one, fromBlocks_neg]
  have key : mR y * JJ n * (mR y)ᴴ = JJ n := by
    have h1 : (mR y)ᴴ * JJ n = JJ n * mR y⁻¹ := by
      calc (mR y)ᴴ * JJ n = (mR y)ᴴ * JJ n * (mR y * mR y⁻¹) := by rw [hgg, Matrix.mul_one]
        _ = ((mR y)ᴴ * JJ n * mR y) * mR y⁻¹ := by simp only [Matrix.mul_assoc]
        _ = JJ n * mR y⁻¹ := by rw [hG]
    calc mR y * JJ n * (mR y)ᴴ = mR y * JJ n * (mR y)ᴴ * (JJ n * JJ n) * (-1) := by
          rw [hJJ]; simp
      _ = mR y * JJ n * ((mR y)ᴴ * JJ n) * JJ n * (-1) := by simp only [Matrix.mul_assoc]
      _ = mR y * (JJ n * JJ n) * mR y⁻¹ * JJ n * (-1) := by rw [h1]; simp only [Matrix.mul_assoc]
      _ = JJ n := by
          rw [hJJ]
          simp [hgg]
  have hherm : C * Dᴴ = D * Cᴴ := by
    have hb := congrArg Matrix.toBlocks₂₂ key
    rw [← fromBlocks_toBlocks (mR y), JJ, fromBlocks_conjTranspose, fromBlocks_multiply,
      fromBlocks_multiply] at hb
    simp at hb
    rw [← hC, ← hD] at hb
    exact (neg_add_eq_zero.mp hb).symm
  have hpos : ((C * Cᴴ + D * Dᴴ).det) ≠ 0 := by
    have hu : IsUnit (mR y) := ⟨(y : GL (Fin n ⊕ Fin n) ℂ), rfl⟩
    open ComplexOrder in
    have hpd : ((mR y * (mR y)ᴴ).submatrix Sum.inr Sum.inr).PosDef :=
      (Matrix.PosDef.mul_conjTranspose_self _
        (Matrix.vecMul_injective_iff_isUnit.mpr hu)).submatrix Sum.inr_injective
    have he : (mR y * (mR y)ᴴ).submatrix Sum.inr Sum.inr = C * Cᴴ + D * Dᴴ := by
      change Matrix.toBlocks₂₂ (mR y * (mR y)ᴴ) = _
      rw [hC, hD]
      conv_lhs => rw [← fromBlocks_toBlocks (mR y), fromBlocks_conjTranspose, fromBlocks_multiply]
      simp
    rw [← he]
    exact (Matrix.isUnit_iff_isUnit_det _).mp hpd.isUnit |>.ne_zero
  have hprod : (C + Complex.I • D) * (C + Complex.I • D)ᴴ = C * Cᴴ + D * Dᴴ := by
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.star_def, Complex.conj_I]
    rw [← hherm, smul_add, smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul, neg_smul]
    abel
  have hI : (C + Complex.I • D).det ≠ 0 := by
    intro h
    apply hpos
    rw [← hprod, Matrix.det_mul, h, zero_mul]
  let P : Polynomial ℂ :=
    Matrix.det (C.map Polynomial.C + (Polynomial.X : Polynomial ℂ) • D.map Polynomial.C)
  have hev : ∀ r : ℂ, P.eval r = (C + r • D).det := by
    intro r
    show Polynomial.evalRingHom r (Matrix.det _) = _
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp
    ring
  have hP : P ≠ 0 := fun h => hI (by rw [← hev, h, Polynomial.eval_zero])
  have hfin : {s : ℝ | P.eval (s : ℂ) = 0}.Finite := by
    apply Set.Finite.subset ((P.roots.toFinset.finite_toSet).preimage
      Complex.ofReal_injective.injOn)
    intro s hs
    simp only [Set.mem_setOf_eq] at hs
    simp [Polynomial.mem_roots hP, hs]
  have hT : Tendsto (fun s : ℝ => y * lowG n s) (𝓝[≠] (0 : ℝ)) (𝓝 y) := by
    have h0 : Tendsto (fun s : ℝ => y * lowG n s) (𝓝 0) (𝓝 (y * lowG n 0)) :=
      (continuous_const.mul lowG_cont).tendsto 0
    rw [lowG_zero, mul_one] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  apply mem_closure_of_tendsto hT
  have hopen : ({s : ℝ | P.eval (s : ℂ) = 0} \ {0})ᶜ ∈ 𝓝 (0 : ℝ) :=
    (hfin.subset Set.diff_subset).isClosed.isOpen_compl.mem_nhds (by simp)
  filter_upwards [nhdsWithin_le_nhds hopen, self_mem_nhdsWithin] with s hs hs0
  show ((mR (y * lowG n s)).toBlocks₂₁).det ≠ 0
  rw [lower_left_block_lowering_mul, ← hC, ← hD, ← hev]
  intro h
  exact hs ⟨h, hs0⟩

end PositivityTheory.Rg.Sw.AbsSt.SZ
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SecZero

section

@[expose] public section

noncomputable section

open Matrix Filter Topology Set

namespace PositivityTheory.Rg.Sw.AbsSt.SZ

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

lemma cell_decomp (y : GR n) (hy : ((mR y).toBlocks₂₁).det ≠ 0) :
    ∃ (p g : GR n) (b : Matrix (Fin n) (Fin n) ℂ), b.IsHermitian ∧ mR g = JJ n * nU b ∧
      (mR p).toBlocks₂₁ = 0 ∧ y = p * g := by
  set C := (mR y).toBlocks₂₁ with hC
  set D := (mR y).toBlocks₂₂ with hD
  have hyG : InG (mR y) := y.2
  have hrel : C * Dᴴ = D * Cᴴ := lowerDiagonalBlockAsGL hyG
  have hCu : IsUnit C.det := isUnit_iff_ne_zero.mpr hy
  have hCHu : IsUnit (Cᴴ).det := by
    rw [det_conjTranspose]
    exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hy)
  set b := C⁻¹ * D with hb
  have hbH : b.IsHermitian := by
    show bᴴ = b
    calc bᴴ = Dᴴ * (Cᴴ)⁻¹ := by
            rw [hb, conjTranspose_mul, conjTranspose_nonsing_inv]
      _ = C⁻¹ * (C * Dᴴ) * (Cᴴ)⁻¹ := by
            rw [← Matrix.mul_assoc C⁻¹, nonsing_inv_mul _ hCu, Matrix.one_mul]
      _ = C⁻¹ * (D * Cᴴ) * (Cᴴ)⁻¹ := by rw [hrel]
      _ = b := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hCHu, Matrix.mul_one, hb]
  obtain ⟨g, hg⟩ := exists_of_InG (InG_JJ_nU hbH)
  set N : M2 n := fromBlocks (-b) (-1) 1 0 with hN
  have h1 : mR g⁻¹ * mR g = 1 := by
    rw [← SZ.mR_mul, inv_mul_cancel]
    rfl
  have h2 : mR g * N = 1 := by
    rw [hg, hN]
    simp only [JJ, nU, fromBlocks_multiply]
    rw [← fromBlocks_one]
    congr 1 <;> simp
  have hM : mR g⁻¹ = N := by
    calc mR g⁻¹ = mR g⁻¹ * (mR g * N) := by rw [h2, Matrix.mul_one]
      _ = N := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  refine ⟨y * g⁻¹, g, b, hbH, hg, ?_, (inv_mul_cancel_right y g).symm⟩
  rw [SZ.mR_mul, hM, ← fromBlocks_toBlocks (mR y), hN, fromBlocks_multiply, toBlocks_fromBlocks₂₁]
  rw [← hC, ← hD, Matrix.mul_neg, Matrix.mul_one, ← Matrix.mul_assoc, mul_nonsing_inv _ hCu,
    Matrix.one_mul, neg_add_cancel]

end PositivityTheory.Rg.Sw.AbsSt.SZ

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt.SZ

theorem secZero : NullIff → SecZero := by
  intro hN m n ε c t p q e sL ρ hL P
  have ht : t ≠ 0 := by
    rcases hL.sign with ⟨h, -, -⟩ | ⟨h, -, -⟩
    · rw [h]; exact hL.cpos.ne'
    · rw [h]; exact neg_ne_zero.2 hL.cpos.ne'
  obtain ⟨C, hC, hcell⟩ := hL.cell
  rw [hN m n ε c t hL.cpos ht P]
  constructor
  · intro h y
    have hS : {z : GR n | ((mR z).toBlocks₂₁).det ≠ 0} ⊆ {z | sL P z = 0} := by
      intro z hz
      obtain ⟨p', g, b, hb, hg, hp, rfl⟩ := cell_decomp z hz
      show sL P (p' * g) = 0
      rw [hL.law P p' g hp, hcell P g b hb hg, h b hb, mul_zero, mul_zero]
    have hcl : IsClosed {z : GR n | sL P z = 0} := isClosed_eq (hL.cont P) continuous_const
    exact hcl.closure_subset_iff.2 hS (dense_cell y)
  · intro h b hb
    obtain ⟨g, hg⟩ := exists_of_InG (InG_JJ_nU hb)
    have hh := hcell P g b hb hg
    rw [h g] at hh
    exact (mul_eq_zero.1 hh.symm).resolve_left hC

end PositivityTheory.Rg.Sw.AbsSt
end
end
end
