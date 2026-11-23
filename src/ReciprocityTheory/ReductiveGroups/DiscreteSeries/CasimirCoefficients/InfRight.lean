module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.DTauFacts
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ContinuousConjProjection
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ContinuousOnFderivPhiP
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.DerivGA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.KFacts
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.LowMinusUpExpand

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.InfRightA

section

@[expose] public section

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ}

lemma infR_hasFDerivAt (T : KType ε Λ) (μ : Fin n → ℤ) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) :
    HasFDerivAt (psM T μ) (fderiv ℂ (psM T μ) x) x := by
  haveI : CompactSpace (KG ε) := compactSpace_KG ε
  have hU : x ∈ Ps1.Uset ε := by
    intro k
    have hk : toMK k⁻¹ = (toMK k)ᴴ := Ps1.toMK_inv_eq k
    have hinv : toMK k⁻¹ * toMK k = 1 := by
      unfold toMK toM
      simp
    have hinj : Function.Injective (toMK k).mulVec := by
      intro v w hvw
      have := congrArg (toMK k⁻¹).mulVec hvw
      simpa [Matrix.mulVec_mulVec, hinv] using this
    have hpd : (toMK k⁻¹ * x * toMK k).PosDef := by
      rw [hk]
      exact hx.conjTranspose_mul_mul_same hinj
    intro i
    unfold lead
    rw [dite_eq_left (by omega)]
    exact ((hpd.submatrix (Fin.castLE_injective _)).det_pos).ne'
  exact (Ps1.hasFDerivAt_psM T μ hU).differentiableAt.hasFDerivAt

lemma infR_conj (T : KType ε Λ) (μ : Fin n → ℤ) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef)
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : inK ε A) :
    fderiv ℂ (psM T μ) x (x * A - A * x) = psM T μ x * T.dτ A - T.dτ A * psM T μ x := by
  obtain ⟨γ, -, hγ, hγm⟩ := exists_oneParam ε hA
  have h0 : γ 0 = 1 := by simpa using hγm 0 0
  have hinv : ∀ t, (γ (-t))⁻¹ = γ t := fun t =>
    inv_eq_of_mul_eq_one_right (by rw [← hγm, neg_add_cancel, h0])

  have heq : ∀ t : ℝ, psM T μ (NormedSpace.exp (-((t : ℂ) • A)) * x * NormedSpace.exp ((t : ℂ) • A))
      = T.op (γ (-t)) * psM T μ x * T.op (γ t) := by
    intro t
    have h1 := psM_conj T μ (γ (-t)) x
    rw [hinv, hγ, hγ] at h1
    simpa [Complex.ofReal_neg, neg_smul] using h1

  have hL : HasDerivAt (fun t : ℝ => psM T μ (NormedSpace.exp (-((t : ℂ) • A)) * x *
      NormedSpace.exp ((t : ℂ) • A))) (fderiv ℂ (psM T μ) x (x * A - A * x)) 0 := by
    have hc := dga_path A x
    have hψ := infR_hasFDerivAt T μ hx
    exact (hψ.restrictScalars ℝ).comp_hasDerivAt_of_eq (0 : ℝ) hc (by simp)

  have hR1 := T.hasDeriv A hA γ hγ
  have hR1' : HasDerivAt (fun t => ((T.τ (γ t) : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V))
      (T.dτ A) (-(0 : ℝ)) := by
    rw [neg_zero]
    exact hR1
  have hR2 := hR1'.scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
  have hR := (hR2.mul (hasDerivAt_const (0 : ℝ) (psM T μ x))).mul hR1
  have hL' : HasDerivAt (fun t : ℝ => ((T.τ (γ (-t)) : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) *
      psM T μ x * ((T.τ (γ t) : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V))
      (fderiv ℂ (psM T μ) x (x * A - A * x)) 0 := by
    have hfun : (fun t : ℝ => psM T μ (NormedSpace.exp (-((t : ℂ) • A)) * x *
        NormedSpace.exp ((t : ℂ) • A))) = fun t : ℝ => ((T.τ (γ (-t)) : unitary (T.V →L[ℂ] T.V)) :
          T.V →L[ℂ] T.V) * psM T μ x * ((T.τ (γ t) : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) := by
      funext t
      exact heq t
    rw [hfun] at hL
    exact hL
  rw [hL'.unique hR]
  simp [h0]
  abel

end ReciprocityTheory.ChartRestriction.DS.S7
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.InfRight

section

@[expose] public section

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

variable {ε : Fin n → Bool} {lam : Fin n → ℝ}

private lemma smul_cancel_lemma {E : Type*} [AddCommGroup E] [Module ℂ E] {c : ℂ} (hc : c ≠ 0)
    {u v : E} (h : c • u = c • v) : u = v := by
  have h' := congrArg (fun w => c⁻¹ • w) h
  simpa [smul_smul, inv_mul_cancel₀ hc] using h'

lemma infR_skew (T : KType ε (lowK ε lam)) (μ : Fin n → ℤ) (hμ : IsMu lam μ)
    {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) {A : Matrix (Fin n) (Fin n) ℂ} (hA : inK ε A) :
    fderiv ℂ (psM T μ) x (x * A) = -(T.dτ A * psM T μ x) ∧
      fderiv ℂ (psM T μ) x (A * x) = -(psM T μ x * T.dτ A) := by
  obtain ⟨hAs, hAb⟩ := (inK_iff ε A).1 hA
  have hH : IsBlock ε (Complex.I • A) := by
    intro i j hij
    rw [Matrix.smul_apply, hAb i j hij, smul_zero]
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  have hHh : (Complex.I • A)ᴴ = Complex.I • A := by
    rw [Matrix.conjTranspose_smul, hAs, hI, neg_smul_neg]
  have h1 := psM_inf_herm T μ hμ hx hH hHh
  have e1 : Complex.I • A * x + x * (Complex.I • A) = Complex.I • (A * x + x * A) := by
    rw [smul_mul_assoc, mul_smul_comm, smul_add]
  rw [e1] at h1

  have hs : fderiv ℂ (psM T μ) x (A * x) + fderiv ℂ (psM T μ) x (x * A) =
      -(T.dτ A * psM T μ x + psM T μ x * T.dτ A) := by
    apply smul_cancel_lemma Complex.I_ne_zero
    simpa only [map_smul, map_add (f := _), smul_mul_assoc, mul_smul_comm, smul_add, smul_neg] using h1

  have hd : fderiv ℂ (psM T μ) x (x * A) - fderiv ℂ (psM T μ) x (A * x) =
      psM T μ x * T.dτ A - T.dτ A * psM T μ x := by
    rw [← map_sub]
    exact infR_conj T μ hx hA
  constructor
  · apply smul_cancel_lemma (two_ne_zero : (2 : ℂ) ≠ 0)
    rw [two_smul, two_smul]
    calc fderiv ℂ (psM T μ) x (x * A) + fderiv ℂ (psM T μ) x (x * A)
        = (fderiv ℂ (psM T μ) x (A * x) + fderiv ℂ (psM T μ) x (x * A)) +
          (fderiv ℂ (psM T μ) x (x * A) - fderiv ℂ (psM T μ) x (A * x)) := by abel
      _ = -(T.dτ A * psM T μ x + psM T μ x * T.dτ A) +
          (psM T μ x * T.dτ A - T.dτ A * psM T μ x) := by rw [hs, hd]
      _ = -(T.dτ A * psM T μ x) + -(T.dτ A * psM T μ x) := by abel
  · apply smul_cancel_lemma (two_ne_zero : (2 : ℂ) ≠ 0)
    rw [two_smul, two_smul]
    calc fderiv ℂ (psM T μ) x (A * x) + fderiv ℂ (psM T μ) x (A * x)
        = (fderiv ℂ (psM T μ) x (A * x) + fderiv ℂ (psM T μ) x (x * A)) -
          (fderiv ℂ (psM T μ) x (x * A) - fderiv ℂ (psM T μ) x (A * x)) := by abel
      _ = -(T.dτ A * psM T μ x + psM T μ x * T.dτ A) -
          (psM T μ x * T.dτ A - T.dτ A * psM T μ x) := by rw [hs, hd]
      _ = -(psM T μ x * T.dτ A) + -(psM T μ x * T.dτ A) := by abel

theorem psM_inf_right (T : KType ε (lowK ε lam)) (μ : Fin n → ℤ) (hμ : IsMu lam μ) {x : Matrix (Fin n) (Fin n) ℂ}
    (hx : x.PosDef) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : IsBlock ε Y) :
    fderiv ℂ (psM T μ) x (x * Y) = -(T.dτ Y * psM T μ x) ∧
      fderiv ℂ (psM T μ) x (Y * x) = -(psM T μ x * T.dτ Y) := by

  obtain ⟨A, B, hA, hB, rfl, -⟩ := block_decomp hY
  have hA' := infR_skew T μ hμ hx hA
  have hB' := infR_skew T μ hμ hx hB
  constructor
  · simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, map_add (f := _), map_smul, hA'.1, hB'.1,
      neg_add, smul_neg]
  · simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, map_add (f := _), map_smul, hA'.2, hB'.2,
      neg_add, smul_neg]

end ReciprocityTheory.ChartRestriction.DS.S7
end
end
end
