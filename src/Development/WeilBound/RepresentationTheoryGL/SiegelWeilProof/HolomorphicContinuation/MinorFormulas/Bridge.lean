module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.BridgeSt
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.BridgeB
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.BridgeA
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.BridgeH
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
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
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RingTheory.PiTensorProduct
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.BridgeH
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ClsGainA
public import Mathlib.Analysis.Analytic.IteratedFDeriv

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.DetSqSplit

section

@[expose] public section

noncomputable section

open Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.SP

open PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z

variable {n : ℕ}

theorem det_line (M0 A : Matrix (Fin n) (Fin n) ℂ) (h : M0.det ≠ 0) :
    HasDerivAt (fun t : ℂ => (M0 + t • A).det) (M0.det * (M0⁻¹ * A).trace) 0 := by
  have hM : M0 * M0⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr h)
  set N := M0⁻¹ * A with hN
  set P : Polynomial ℂ := (det (1 + (Polynomial.X : Polynomial ℂ) • N.map Polynomial.C)).divX.divX with hP
  have e : (fun t : ℂ => (M0 + t • A).det) = fun t : ℂ => M0.det * (1 + N.trace * t + P.eval t * t ^ 2) := by
    funext t
    have : M0 + t • A = M0 * (1 + t • N) := by
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, hN, ← Matrix.mul_assoc, hM, Matrix.one_mul]
    rw [this, Matrix.det_mul, Matrix.det_one_add_smul]
  rw [e]
  have h1 : HasDerivAt (fun t : ℂ => 1 + N.trace * t + P.eval t * t ^ 2) N.trace 0 := by
    have ha : HasDerivAt (fun t : ℂ => N.trace * t) N.trace 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_mul N.trace
    have hb : HasDerivAt (fun t : ℂ => P.eval t * t ^ 2) 0 0 := by
      have := (P.hasDerivAt (0 : ℂ)).fun_mul (hasDerivAt_pow 2 (0 : ℂ))
      simpa using this
    simpa using (ha.const_add 1).fun_add hb
  exact h1.const_mul M0.det

theorem c_sq (s : ℂ) (hs : s = 1 ∨ s = -1) : (Complex.I * s) * (Complex.I * s) = -1 := by
  rcases hs with rfl | rfl <;> simp [Complex.I_mul_I]

theorem det_sq_split (s : ℂ) (hs : s = 1 ∨ s = -1) (B : MC n) :
    (1 + Matrix.of B * Matrix.of B).det =
      (1 - (Complex.I * s) • Matrix.of B).det * (1 + (Complex.I * s) • Matrix.of B).det := by
  rw [← Matrix.det_mul]
  congr 1
  have hc := c_sq s hs
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hc]
  simp only [neg_smul, one_smul]
  abel

theorem hCls : HCls := by
  intro n s hs z m x v hx
  obtain ⟨h1, h2, h3⟩ := hx
  set c : ℂ := Complex.I * s with hc
  set M0 : Matrix (Fin n) (Fin n) ℂ := 1 - c • Matrix.of x
  set M0' : Matrix (Fin n) (Fin n) ℂ := 1 + c • Matrix.of x
  set V : Matrix (Fin n) (Fin n) ℂ := Matrix.of v
  have hdM := det_line M0 (-c • V) h1
  have hdM' := det_line M0' (c • V) h2

  have e : (fun t : ℂ => clsC s z m 0 1 (x + t • v)) = fun t : ℂ =>
      Complex.exp (-z * Complex.log ((M0 + t • (-c • V)).det * (M0' + t • (c • V)).det)) * (((M0 + t • (-c • V)).det)⁻¹) ^ m := by
    funext t
    simp only [clsC, pow_zero, mul_one, map_one]
    rw [det_sq_split s hs, mX, mY, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  rw [e]
  have hW0 : (M0 + (0 : ℂ) • (-c • V)).det * (M0' + (0 : ℂ) • (c • V)).det ∈ Complex.slitPlane := by
    have e0 : (M0 + (0 : ℂ) • (-c • V)).det * (M0' + (0 : ℂ) • (c • V)).det = (1 + Matrix.of x * Matrix.of x).det := by
      simp only [zero_smul, add_zero]
      exact (det_sq_split s hs x).symm
    rw [e0]
    exact h3
  have hW := hdM.fun_mul hdM'
  have hL := hW.clog (by simpa using hW0)
  have hE := (hL.const_mul (-z)).cexp
  have hD := (hdM.inv (by simpa using h1)).pow m
  have hT := hE.fun_mul hD
  refine hT.congr_deriv ?_
  simp only [zero_smul, add_zero]
  have hM0 : M0.det ≠ 0 := h1
  have hM0' : M0'.det ≠ 0 := h2
  have tr1 : (M0⁻¹ * (-c • V)).trace = -c * (Ym s x * V).trace := by
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    rfl
  have tr2 : (M0'⁻¹ * (c • V)).trace = c * (Yp s x * V).trace := by
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    rfl
  have ecls : clsC s z m 0 1 x = Complex.exp (-z * Complex.log (M0.det * M0'.det)) * (M0.det⁻¹) ^ m := by
    simp only [clsC, pow_zero, mul_one, map_one]
    rw [det_sq_split s hs, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  rw [ecls, tr1, tr2]
  simp only [Pi.inv_apply, Pi.pow_apply, zero_smul, add_zero]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
    field_simp
    ring
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    field_simp
    have hinv : M0.det * M0.det⁻¹ = 1 := mul_inv_cancel₀ hM0
    linear_combination (-(c * (Ym s x * V).trace * M0.det⁻¹ ^ k) * (1 + (k : ℂ))) * hinv

end PositivityTheory.Rg.Sw.SP
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.BridgeC

section

@[expose] public section

noncomputable section

open Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.SP

open PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z

variable {n : ℕ}

def gD (s : ℂ) (x : MC n) (k l : Fin n) (kk : Bool × Fin n × Fin n) : ℂ :=
  if kk.1 then (-(Complex.I * s) • (Yp s x * Matrix.of (eU k l) * Yp s x)) kk.2.1 kk.2.2
  else ((Complex.I * s) • (Ym s x * Matrix.of (eU k l) * Ym s x)) kk.2.1 kk.2.2

theorem hasDerivAt_vals (s : ℂ) (x : MC n) (hx : x ∈ OmS s) (k l : Fin n) (kk : Bool × Fin n × Fin n) :
    HasDerivAt (fun t : ℂ => vals s (x + t • eU k l) kk) (gD s x k l kk) 0 := by
  obtain ⟨b, a, d⟩ := kk
  cases b
  · simpa [vals, gD] using hYm n s x (eU k l) hx.1 a d
  · simpa [vals, gD] using hYp n s x (eU k l) hx.2.1 a d

theorem hasDerivAt_evQ (s z : ℂ) (x : MC n) (hx : x ∈ OmS s) (k l : Fin n) (Q : Fm n) :
    HasDerivAt (fun t : ℂ => evQ s z Q (x + t • eU k l))
      (∑ kk, evQ s z (MvPolynomial.pderiv kk Q) x * gD s x k l kk) 0 := by
  have h := hasDerivAt_eval (fun t : ℂ => vals s (x + t • eU k l)) (gD s x k l) (hasDerivAt_vals s x hx k l)
    (MvPolynomial.map (Polynomial.evalRingHom z) Q)
  simp only [zero_smul, add_zero] at h
  refine h.congr_deriv ?_
  refine Finset.sum_congr rfl fun kk _ => ?_
  rw [MvPolynomial.pderiv_map]
  rfl

theorem sum_bool_fin (F : Bool × Fin n × Fin n → ℂ) :
    ∑ kk, F kk = ∑ a : Fin n, ∑ d : Fin n, F (false, a, d) + ∑ a : Fin n, ∑ d : Fin n, F (true, a, d) := by
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [Fintype.sum_prod_type]
  ring

theorem line_fQ (s : ℂ) (hs : s = 1 ∨ s = -1) (z : ℂ) (m : ℕ) (Q : Fm n) (x : MC n) (hx : x ∈ OmS s) (k l : Fin n) :
    HasDerivAt (fun t : ℂ => fQ s z m Q (x + t • eU k l)) (fQ s z m (opD s m k l Q) x) 0 := by
  have h1 := hCls n s hs z m x (eU k l) hx
  have h2 := hasDerivAt_evQ s z x hx k l Q
  have h3 := h1.mul h2
  refine h3.congr_deriv ?_
  simp only [fQ, opD, LinearMap.add_apply, opH_eq, evQ_add, evQ_multPart, evQ_derPart, trace_eU, sum_bool_fin, gD,
    Bool.false_eq_true, if_false, if_true, Matrix.smul_apply, sandwich_eU, smul_eq_mul, cB, alB, vals,
    Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X, zero_smul, add_zero]
  simp only [Finset.mul_sum, Finset.sum_add_distrib, mul_add]
  ring_nf
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => ?_
    ring
  · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => ?_
    ring

end PositivityTheory.Rg.Sw.SP
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.Bridge

section

@[expose] public section

noncomputable section

open Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.SP

open PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z

variable {n : ℕ}

theorem an_fQ (s z : ℂ) (m : ℕ) (Q : Fm n) (B₀ : MC n) (hB : B₀ ∈ OmS s) : AnalyticAt ℂ (fQ s z m Q) B₀ := by
  obtain ⟨h1, h2, h3⟩ := hB
  have hu := entAn_inv (entAn_X (Complex.I * s) B₀) h1
  have hv := entAn_inv (entAn_Y (Complex.I * s) B₀) h2
  have hf : ∀ k : Bool × Fin n × Fin n, AnalyticAt ℂ (fun B => vals s B k) B₀ := by
    rintro ⟨_ | _, a, b⟩
    · exact hu a b
    · exact hv a b
  exact (an_clsC s z m 0 1 B₀ ⟨h1, h2, h3⟩).mul (an_eval (fun k B => vals s B k) B₀ hf _)

theorem anN_fQ (s z : ℂ) (m : ℕ) (Q : Fm n) : AnalyticOnNhd ℂ (fQ s z m Q) (OmS s) := fun x hx => an_fQ s z m Q x hx

theorem fderiv_fQ (s : ℂ) (hs : s = 1 ∨ s = -1) (z : ℂ) (m : ℕ) (Q : Fm n) (x : MC n) (hx : x ∈ OmS s) (k l : Fin n) :
    fderiv ℂ (fQ s z m Q) x (eU k l) = fQ s z m (opD s m k l Q) x := by
  have hd := (an_fQ s z m Q x hx).differentiableAt.hasFDerivAt
  have hl : HasDerivAt (fun t : ℂ => x + t • eU k l) (eU k l) 0 := hasDerivAt_line x (eU k l)
  have h1 : HasDerivAt (fun t : ℂ => fQ s z m Q (x + t • eU k l)) (fderiv ℂ (fQ s z m Q) x (eU k l)) 0 :=
    hd.comp_hasDerivAt_of_eq (0 : ℂ) hl (by simp)
  exact h1.unique (line_fQ s hs z m Q x hx k l)

def opsSeq (s : ℂ) (m : ℕ) : (k : ℕ) → (Fin k → Fin n × Fin n) → Fm n → Fm n
  | 0, _, Q => Q
  | k + 1, dirs, Q => opD s m (dirs 0).1 (dirs 0).2 (opsSeq s m k (Fin.tail dirs) Q)

theorem iter_fQ (s : ℂ) (hs : s = 1 ∨ s = -1) (z : ℂ) (m : ℕ) :
    ∀ (k : ℕ) (dirs : Fin k → Fin n × Fin n) (Q : Fm n) (x : MC n), x ∈ OmS s →
      iteratedFDeriv ℂ k (fQ s z m Q) x (fun i => eU (dirs i).1 (dirs i).2) = fQ s z m (opsSeq s m k dirs Q) x
  | 0, dirs, Q, x, hx => by simp [opsSeq]
  | k + 1, dirs, Q, x, hx => by
    have hdiff : DifferentiableAt ℂ (iteratedFDeriv ℂ k (fQ s z m Q)) x :=
      ((anN_fQ s z m Q).iteratedFDeriv k x hx).differentiableAt
    rw [hdiff.iteratedFDeriv_succ_apply_left']
    have heq : (fun y => iteratedFDeriv ℂ k (fQ s z m Q) y (Fin.tail fun i => eU (dirs i).1 (dirs i).2)) =ᶠ[𝓝 x]
        fQ s z m (opsSeq s m k (Fin.tail dirs) Q) := by
      filter_upwards [(isOpen_OmS s).mem_nhds hx] with y hy
      exact iter_fQ s hs z m k (Fin.tail dirs) Q y hy
    rw [heq.fderiv_eq]
    exact fderiv_fQ s hs z m _ x hx (dirs 0).1 (dirs 0).2

theorem opsSeq_eq (s : ℂ) (m : ℕ) : ∀ (k : ℕ) (dirs : Fin k → Fin n × Fin n) (Q : Fm n),
    opsSeq s m k dirs Q = (List.finRange k).foldr (fun i g => opD s m (dirs i).1 (dirs i).2 ∘ₗ g) LinearMap.id Q
  | 0, dirs, Q => by simp [opsSeq]
  | k + 1, dirs, Q => by
    rw [opsSeq, opsSeq_eq s m k (Fin.tail dirs) Q, List.finRange_succ, List.foldr_cons, List.foldr_map]
    rfl

theorem evQ_smul (s z a : ℂ) (P : Fm n) (B : MC n) : evQ s z (a • P) B = a * evQ s z P B := by
  rw [smulC, evQ_mul, evQ_CC]

theorem fQ_linear (s z : ℂ) (m : ℕ) {ι : Type} (t : Finset ι) (a : ι → ℂ) (P : ι → Fm n) (B : MC n) :
    fQ s z m (∑ i ∈ t, a i • P i) B = ∑ i ∈ t, a i * fQ s z m (P i) B := by
  simp only [fQ, evQ_sum, evQ_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem cay_fQ (s : ℂ) (hs : s = 1 ∨ s = -1) (z : ℂ) (m : ℕ) (Q : Fm n) (x : MC n) (hx : x ∈ OmS s) :
    cay (fQ s z m Q) x = fQ s z m (cayF s m Q) x := by
  have hc : ContDiffAt ℂ ω (fQ s z m Q) x := (an_fQ s z m Q x hx).contDiffAt
  have hperm : ∀ σ : Equiv.Perm (Fin n), iteratedFDeriv ℂ n (fQ s z m Q) x (fun k => eU (σ k) k) =
      iteratedFDeriv ℂ n (fQ s z m Q) x (fun k => eU k (σ⁻¹ k)) := by
    intro σ
    have := hc.iteratedFDeriv_comp_perm (fun k => eU k (σ⁻¹ k)) σ
    rw [← this]
    congr 1
    funext k
    change eU (σ k) k = eU (σ k) (σ.symm (σ k))
    rw [Equiv.symm_apply_apply]
  simp only [cay, hperm]
  rw [← Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin n)))]
  simp only [Equiv.inv_apply, inv_inv, Equiv.Perm.sign_inv]
  have hI : ∀ σ : Equiv.Perm (Fin n), iteratedFDeriv ℂ n (fQ s z m Q) x (fun k => eU k (σ k)) =
      fQ s z m (opsSeq s m n (fun k => (k, σ k)) Q) x := fun σ => iter_fQ s hs z m n (fun k => (k, σ k)) Q x hx
  simp only [hI, opsSeq_eq]
  rw [cayF, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply]
  rw [fQ_linear]

theorem fQ_one (s z : ℂ) (m : ℕ) (B : MC n) : fQ s z m 1 B = clsC s z m 0 1 B := by
  simp [fQ, evQ]

theorem bridge : Bridge := by
  intro n s hs m N z B hB
  have key : ∀ N : ℕ, ∀ B : MC n, B ∈ OmS s → (cay^[N] (clsC s z m 0 1)) B = fQ s z m ((cayF s m)^[N] 1) B := by
    intro N
    induction N with
    | zero =>
      intro B _
      simp [fQ_one]
    | succ N ih =>
      intro B hB
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      have heq : (cay^[N] (clsC s z m 0 1)) =ᶠ[𝓝 B] fQ s z m ((cayF s m)^[N] 1) := by
        filter_upwards [(isOpen_OmS s).mem_nhds hB] with y hy
        exact ih y hy
      have e : cay (cay^[N] (clsC s z m 0 1)) B = cay (fQ s z m ((cayF s m)^[N] 1)) B := by
        simp only [cay]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [(heq.iteratedFDeriv ℂ n).eq_of_nhds]
      rw [e, cay_fQ s hs z m _ B hB]
  rw [key N B hB]
  rfl

end PositivityTheory.Rg.Sw.SP
end
end
end
