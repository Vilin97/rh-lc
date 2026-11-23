module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ClsGainBSt
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Lagr
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GBFinal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.RatBound

section

@[expose] public section

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.WR.K.GB

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem ratBound (hC : CauchyW) (hI : Invar) (hB : PBound) (hL : Link) (s : ℂ) (hs : s = 1 ∨ s = -1)
    (p q N : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) :
    ∃ C : ℝ, ∀ y : E n, ‖(Delta^[N] (cls s 0 p q R)) y‖ ≤ C * (dP y) ^ (-((p + q + N : ℕ) : ℝ) / 2) := by
  obtain ⟨hUo, hFc, c₀, C₀, hc₀, hb⟩ := hB n s hs p q R
  set K : ℝ := ((N * n : ℕ) : ℝ) with hK
  set C₁ : ℝ := max C₀ 0 with hC₁
  refine ⟨(Fintype.card (Fin N → Equiv.Perm (Fin n)) : ℝ) * ((K / c₀) ^ n) ^ N * C₁, fun y => ?_⟩
  obtain ⟨k, hk, lam, hy⟩ := herm_spectral y
  set w : Fin n → ℝ := fun i => 1 + |lam i| with hw
  have hwpos : ∀ i, 0 < w i := fun i => by simp only [hw]; positivity
  set W : ℝ := ∏ i, w i with hW
  have hWpos : 0 < W := Finset.prod_pos fun i _ => hwpos i
  set d : Mc n := Matrix.diagonal (fun i => (lam i : ℂ)) with hd
  set ρ : Fin n → Fin n → ℝ := fun i j => c₀ * Real.sqrt ((1 + |lam i|) * (1 + |lam j|)) with hρ
  have hρpos : ∀ i j, 0 < ρ i j := fun i j => mul_pos hc₀ (Real.sqrt_pos.2 (mul_pos (hwpos i) (hwpos j)))
  have hlink := (hL n (Fr s p q R) (Ugood s) hUo hFc (herm_mem_Ugood s hs)).1 N y
  rw [cls_zero, hlink, hy]
  set F' : Mc n → ℂ := fun c => Fr s p q R (k * c * kᴴ) with hF'
  set U' : Set (Mc n) := {c | k * c * kᴴ ∈ Ugood s} with hU'
  have hU'o : IsOpen U' := hUo.preimage (contDiff_conj k).continuous
  have hF'c : ContDiffOn ℂ (⊤ : ℕ∞) F' U' := hFc.comp (contDiff_conj k).contDiffOn (fun c hc => hc)
  have hdisc : pdisc d ρ ⊆ U' := fun b hb' => (hb k hk lam b hb').1
  have hdmem : d ∈ U' := hdisc (fun i j => by simp [hρpos i j |>.le])
  have hherm' : ∀ y', herm y' ∈ U' := fun y' => conj_mem_Ugood s k hk _ (herm_mem_Ugood s hs y')
  rw [← hI n (Fr s p q R) (Ugood s) hUo hFc k hk N d hdmem, (hL n F' U' hU'o hF'c hherm').2 N d hdmem]
  have hM : ∀ b ∈ pdisc d ρ, ‖F' b‖ ≤ C₁ * W ^ (-((p + q : ℕ) : ℝ)) := fun b hb' =>
    ((hb k hk lam b hb').2).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hWpos.le _))
  have hword : ∀ τ : Fin N → Equiv.Perm (Fin n),
      ‖word ((List.finRange N).flatMap fun j => (List.finRange n).map fun k => (τ j k, k)) F' d‖ ≤
        ((K / c₀) ^ n / W) ^ N * (C₁ * W ^ (-((p + q : ℕ) : ℝ))) := by
    intro τ
    have h := hC n F' U' hU'o hF'c d ρ hρpos hdisc _ hM ((List.finRange N).flatMap fun j => (List.finRange n).map fun k => (τ j k, k))
    refine h.trans (le_of_eq ?_)
    congr 1
    rw [List.map_flatMap]
    simp only [List.map_map, Function.comp_def]
    rw [prod_blocks N (fun j k => (((List.finRange N).flatMap fun j => (List.finRange n).map fun k => (τ j k, k)).length : ℝ) /
      ρ (τ j k) k)]
    rw [length_blocks]
    show ∏ j, ∏ k, K / ρ ((τ j) k) k = ((K / c₀) ^ n / W) ^ N
    have hblock : ∀ j, ∏ k, K / ρ ((τ j) k) k = (K / c₀) ^ n / W := by
      intro j
      have hs := prod_sqrt_perm (τ j) w hwpos
      simp only [hw] at hs
      simp only [hρ]
      rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.prod_mul_distrib,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin, hs, div_pow]
      simp only [hW, hw]
      field_simp
    rw [Finset.prod_congr rfl fun j _ => hblock j, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hsgn : ∀ τ : Fin N → Equiv.Perm (Fin n), ‖(((∏ j, (Equiv.Perm.sign (τ j) : ℤ) : ℤ) : ℂ))‖ = 1 := by
    intro τ
    have h : ∀ j, |((Equiv.Perm.sign (τ j) : ℤ))| = 1 := fun j => by
      rcases Int.units_eq_one_or (Equiv.Perm.sign (τ j)) with h | h <;> simp [h]
    have h2 : |∏ j, ((Equiv.Perm.sign (τ j) : ℤ))| = 1 := by
      rw [Finset.abs_prod, Finset.prod_eq_one fun j _ => h j]
    rw [Complex.norm_intCast]
    exact_mod_cast h2
  have hdP : dP y ≤ W ^ (2 : ℝ) := by
    rw [dP_of_spectral y k hk lam hy, Real.rpow_two, hW, ← Finset.prod_pow]
    refine Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => ?_
    simp only [hw]
    have : lam i ^ 2 = |lam i| ^ 2 := (sq_abs _).symm
    nlinarith [abs_nonneg (lam i)]
  have hWe : ∀ e : ℝ, 0 ≤ e → W ^ (-e) ≤ (dP y) ^ (-e / 2) := by
    intro e he
    have h1 : W ^ (-e) = (W ^ (2 : ℝ)) ^ (-e / 2) := by
      rw [← Real.rpow_mul hWpos.le]; ring_nf
    rw [h1]
    exact Real.rpow_le_rpow_of_nonpos (dP_pos y) hdP (by linarith)
  calc ‖∑ τ : Fin N → Equiv.Perm (Fin n), (((∏ j, (Equiv.Perm.sign (τ j) : ℤ) : ℤ) : ℂ)) *
          word ((List.finRange N).flatMap fun j => (List.finRange n).map fun k => (τ j k, k)) F' d‖
      ≤ ∑ τ : Fin N → Equiv.Perm (Fin n), ((K / c₀) ^ n / W) ^ N * (C₁ * W ^ (-((p + q : ℕ) : ℝ))) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun τ _ => ?_)
        rw [norm_mul, hsgn τ, one_mul]; exact hword τ
    _ = (Fintype.card (Fin N → Equiv.Perm (Fin n)) : ℝ) * ((K / c₀) ^ n) ^ N * C₁ *
          (W ^ (-((p + q + N : ℕ) : ℝ))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        have : W ^ (-((p + q + N : ℕ) : ℝ)) = W ^ (-((p + q : ℕ) : ℝ)) * (W ^ N)⁻¹ := by
          rw [show (-((p + q + N : ℕ) : ℝ)) = (-((p + q : ℕ) : ℝ)) + (-(N : ℝ)) by push_cast; ring,
            Real.rpow_add hWpos, Real.rpow_neg hWpos.le, Real.rpow_natCast, Real.rpow_neg hWpos.le, Real.rpow_natCast]
        rw [this, div_pow]; ring
    _ ≤ (Fintype.card (Fin N → Equiv.Perm (Fin n)) : ℝ) * ((K / c₀) ^ n) ^ N * C₁ *
          (dP y) ^ (-((p + q + N : ℕ) : ℝ) / 2) := by
        refine mul_le_mul_of_nonneg_left (hWe _ (by positivity)) ?_
        refine mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (pow_nonneg (div_nonneg (by positivity) hc₀.le) _) _))
          (le_max_right _ _)

end PositivityTheory.Rg.Sw.WR.K.GB
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ContDiffHerm

section

@[expose] public section

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.WR.K.GB

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem contDiff_herm (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (herm (n := n)) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  have hc : ∀ a b : Fin n, ContDiff ℝ (⊤ : ℕ∞) (fun x : E n => ((x a b : ℝ) : ℂ)) := fun a b =>
    Complex.ofRealCLM.contDiff.comp ((contDiff_apply ℝ (fun _ => ℝ) b).comp (contDiff_apply ℝ (fun _ => (Fin n → ℝ)) a))
  simp only [herm]
  push_cast
  exact (((hc i j).add (hc j i)).div_const 2).add ((contDiff_const.mul ((hc i j).sub (hc j i))).div_const 2)

theorem clsGainB_of (hC : CauchyW) (hI : Invar) (hB : PBound) (hL : Link) (hT : Twist) (hLg : Lagr) : ClsGain := by
  intro n s hs p q N R
  obtain ⟨hUo, hFc, -⟩ := hB n s hs p q R
  have hH : ContDiff ℝ (⊤ : ℕ∞) (cls s 0 p q R) := by
    rw [cls_zero]
    rw [contDiff_iff_contDiffAt]
    intro y
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (Fr s p q R) (herm y) :=
      ((hFc.restrict_scalars ℝ).contDiffAt (hUo.mem_nhds (herm_mem_Ugood s hs y)))
    exact h1.comp y (contDiff_herm n).contDiffAt
  obtain ⟨G, hGc, hG⟩ := hT n (cls s 0 p q R) hH N
  have hcls : ∀ z : ℂ, cls s z p q R = fun y => ((dP y : ℝ) : ℂ) ^ (-z) * cls s 0 p q R y := by
    intro z; funext y; simp only [cls, neg_zero, Complex.cpow_zero, one_mul]; ring
  set D := n * N with hD
  have hrat : ∀ i : ℕ, ∃ C : ℝ, ∀ y : E n,
      ‖(Delta^[N] (cls s 0 (p + i) (q + i) R)) y‖ ≤ C * (dP y) ^ (-((p + i + (q + i) + N : ℕ) : ℝ) / 2) :=
    fun i => ratBound hC hI hB hL s hs (p + i) (q + i) N R
  choose Ci hCi using hrat
  obtain ⟨CL, hCL⟩ := hLg D
  set Cm : ℝ := ∑ i ∈ Finset.range (D + 1), |Ci i| with hCm
  refine ⟨D + 1, fun j => Polynomial.X ^ (j : ℕ), fun j => G j, fun j => (hGc j).continuous, ⟨CL * Cm, ?_⟩, ?_⟩
  · intro j y
    have hdp := dP_pos y
    have hval : ∀ i ≤ D, ‖∑ j ∈ Finset.range (D + 1), ((i : ℕ) : ℂ) ^ j * G j y‖ ≤ Cm * (dP y) ^ (-((p + q + N : ℕ) : ℝ) / 2) := by
      intro i hi
      have e1 := hG (i : ℂ) y
      rw [← hcls, cls_nat s hs i p q R] at e1
      have hne : (((dP y : ℝ) : ℂ)) ^ (-(i : ℂ)) ≠ 0 := by
        rw [Complex.cpow_neg, Complex.cpow_natCast]; exact inv_ne_zero (pow_ne_zero _ (by exact_mod_cast hdp.ne'))
      have e2 : ∑ j ∈ Finset.range (D + 1), ((i : ℕ) : ℂ) ^ j * G j y =
          (((dP y : ℝ) : ℂ)) ^ i * (Delta^[N] (cls s 0 (p + i) (q + i) R)) y := by
        rw [e1, Complex.cpow_neg, Complex.cpow_natCast, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (by exact_mod_cast hdp.ne')), one_mul]
      rw [e2, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hdp.le]
      have hb := hCi i y
      have hCi_le : |Ci i| ≤ Cm := by
        rw [hCm]
        exact Finset.single_le_sum (f := fun i => |Ci i|) (fun i _ => abs_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
      calc dP y ^ i * ‖(Delta^[N] (cls s 0 (p + i) (q + i) R)) y‖
          ≤ dP y ^ i * (Ci i * (dP y) ^ (-((p + i + (q + i) + N : ℕ) : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_left hb (pow_nonneg hdp.le _)
        _ = Ci i * (dP y) ^ (-((p + q + N : ℕ) : ℝ) / 2) := by
            rw [← Real.rpow_natCast, mul_left_comm, ← Real.rpow_add hdp]
            congr 2; push_cast; ring
        _ ≤ Cm * (dP y) ^ (-((p + q + N : ℕ) : ℝ) / 2) :=
            mul_le_mul_of_nonneg_right ((le_abs_self _).trans hCi_le) (Real.rpow_nonneg hdp.le _)
    have := hCL (fun j => G j y) _ hval j (Nat.lt_succ_iff.1 j.2)
    simpa [mul_assoc] using this
  · intro z y
    rw [hcls z, hG z y]
    congr 1
    rw [Finset.sum_range (fun j => z ^ j * G j y)]
    simp [Polynomial.eval_pow, Polynomial.eval_X]

end PositivityTheory.Rg.Sw.WR.K.GB
end
end
end
