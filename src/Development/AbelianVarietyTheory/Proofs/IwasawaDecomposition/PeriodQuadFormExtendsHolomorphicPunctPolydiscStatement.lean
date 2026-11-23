module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
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
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtensionAcrossCoordinateHyperplanesStatement
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicDescentPunctPolydiscLogCover

section

@[expose] public section

open GlobalTheory.ShFam.Hor

set_option autoImplicit false

namespace GlobalTheory.LogDescent

open Complex Topology

theorem continuous_logExp (n a : ℕ) : Continuous (logExp a : (Fin n → ℂ) → Fin n → ℂ) := by
  refine continuous_pi fun k => ?_
  simp only [logExp]
  split_ifs
  · exact Complex.continuous_exp.comp (continuous_apply k)
  · exact continuous_apply k

theorem mem_logDom_of_mem_ball {n a : ℕ} {ρ : ℝ} (hρ1 : ρ ≤ 1) (s : Fin n → ℂ)
    (hs : logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ) : s ∈ logDom n a := by
  intro k
  have hz := mem_ball_zero_iff.1 hs
  have hk' := (norm_le_pi_norm (logExp a s) k).trans_lt hz
  split_ifs with hk
  · simp only [logExp, hk, if_true, Complex.norm_exp] at hk'
    exact Real.exp_lt_one_iff.mp (lt_of_lt_of_le hk' hρ1)
  · simp only [logExp, hk, if_false] at hk'
    exact lt_of_lt_of_le hk' hρ1

theorem logExp_shift {n a : ℕ} (s : Fin n → ℂ) (k : Fin n) (hk : (k : ℕ) < a) (m : ℤ) :
    logExp a (s + Pi.single k ((m : ℂ) * (2 * Real.pi * Complex.I))) = logExp a s := by
  funext j
  by_cases hj : j = k
  · subst hj
    simp only [logExp, hk, if_true, Pi.add_apply, Pi.single_eq_same]
    rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  · simp [logExp, Pi.single_eq_of_ne hj]

variable {n a : ℕ} {ρ : ℝ} {h : (Fin n → ℂ) → ℂ}

theorem inv_int (hρ1 : ρ ≤ 1)
    (hinv : ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ → ∀ k : Fin n, (k : ℕ) < a →
      h (s + Pi.single k (2 * Real.pi * Complex.I)) = h s)
    (s : Fin n → ℂ) (hs : logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ) (k : Fin n) (hk : (k : ℕ) < a) (m : ℤ) :
    h (s + Pi.single k ((m : ℂ) * (2 * Real.pi * Complex.I))) = h s := by
  induction m using Int.induction_on with
  | zero => simp
  | succ m ih =>
    have ht : logExp a (s + Pi.single k (((m : ℤ) : ℂ) * (2 * Real.pi * Complex.I))) ∈ Metric.ball (0 : Fin n → ℂ) ρ := by
      rw [logExp_shift s k hk]; exact hs
    have := hinv _ (mem_logDom_of_mem_ball hρ1 _ ht) ht k hk
    have e : s + Pi.single k ((((m : ℤ) + 1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I)) =
        s + Pi.single k (((m : ℤ) : ℂ) * (2 * Real.pi * Complex.I)) + Pi.single k (2 * Real.pi * Complex.I) := by
      rw [add_assoc, ← Pi.single_add]; congr 2; push_cast; ring
    rw [e, this, ih]
  | pred m ih =>
    set t := s + Pi.single k ((((-(m : ℤ) - 1 : ℤ)) : ℂ) * (2 * Real.pi * Complex.I)) with htdef
    have ht : logExp a t ∈ Metric.ball (0 : Fin n → ℂ) ρ := by
      rw [htdef, logExp_shift s k hk]; exact hs
    have := hinv _ (mem_logDom_of_mem_ball hρ1 _ ht) ht k hk
    have e : t + Pi.single k (2 * Real.pi * Complex.I) =
        s + Pi.single k ((((-(m : ℤ)) : ℤ) : ℂ) * (2 * Real.pi * Complex.I)) := by
      rw [htdef, add_assoc, ← Pi.single_add]; congr 2; push_cast; ring
    rw [← this, e, ih]

theorem key (hρ1 : ρ ≤ 1)
    (hinv : ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ → ∀ k : Fin n, (k : ℕ) < a →
      h (s + Pi.single k (2 * Real.pi * Complex.I)) = h s)
    (s s' : Fin n → ℂ) (hs : logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ) (he : logExp a s = logExp a s') :
    h s = h s' := by
  suffices H : ∀ S : Finset (Fin n), ∀ s s' : Fin n → ℂ, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ →
      logExp a s = logExp a s' → (∀ k ∉ S, s k = s' k) → h s = h s' from
    H Finset.univ s s' hs he (fun k hk => absurd (Finset.mem_univ k) hk)
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro s s' _ _ hk
    congr 1; funext k; exact hk k (Finset.notMem_empty k)
  | insert j S hjS ih =>
    intro s s' hs he hk
    have hej := congrFun he j
    set s'' := Function.update s' j (s j) with hs''
    have he'' : logExp a s = logExp a s'' := by
      funext k
      by_cases hkj : k = j
      · subst hkj; simp [hs'', logExp]
      · have := congrFun he k
        simpa [hs'', logExp, Function.update_of_ne hkj] using this
    have h1 : h s = h s'' := ih s s'' hs he'' (fun k hk' => by
      by_cases hkj : k = j
      · subst hkj; simp [hs'']
      · rw [hs'', Function.update_of_ne hkj]
        exact hk k (by simp [hkj, hk']))
    rw [h1]
    have hs2 : logExp a s'' ∈ Metric.ball (0 : Fin n → ℂ) ρ := he'' ▸ hs
    by_cases hja : (j : ℕ) < a
    · simp only [logExp, hja, if_true] at hej
      obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.1 hej.symm
      have e : s' = s'' + Pi.single j ((m : ℂ) * (2 * Real.pi * Complex.I)) := by
        funext k
        by_cases hkj : k = j
        · subst hkj; simp [hs'', hm]
        · simp [hs'', Function.update_of_ne hkj, Pi.single_eq_of_ne hkj]
      rw [e, inv_int hρ1 hinv s'' hs2 j hja m]
    · simp only [logExp, hja, if_false] at hej
      congr 1
      rw [hs'', hej, Function.update_eq_self]

theorem dom_mem_nhds {ρ : ℝ} (hρ1 : ρ ≤ 1) (s₀ : Fin n → ℂ)
    (hs₀ : logExp a s₀ ∈ Metric.ball (0 : Fin n → ℂ) ρ) :
    {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ} ∈ 𝓝 s₀ := by
  have ho : IsOpen (logExp a ⁻¹' Metric.ball (0 : Fin n → ℂ) ρ) :=
    Metric.isOpen_ball.preimage (continuous_logExp n a)
  refine Filter.mem_of_superset (ho.mem_nhds hs₀) ?_
  intro s hs
  rw [Set.mem_preimage] at hs
  exact ⟨mem_logDom_of_mem_ball hρ1 s hs, hs⟩

noncomputable def logSec (a : ℕ) {n : ℕ} (z : Fin n → ℂ) : Fin n → ℂ := fun k => if (k : ℕ) < a then Complex.log (z k) else z k

noncomputable def logSecAt (a : ℕ) {n : ℕ} (z₀ z : Fin n → ℂ) : Fin n → ℂ :=
  fun k => if (k : ℕ) < a then Complex.log (z₀ k) + Complex.log (z k / z₀ k) else z k

theorem logExp_logSec (z : Fin n → ℂ) (hz : ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) : logExp a (logSec a z) = z := by
  funext k
  by_cases hk : (k : ℕ) < a
  · simp [logExp, logSec, hk, Complex.exp_log (hz k hk)]
  · simp [logExp, logSec, hk]

theorem logExp_logSecAt (z₀ z : Fin n → ℂ) (hz₀ : ∀ k : Fin n, (k : ℕ) < a → z₀ k ≠ 0)
    (hz : ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) : logExp a (logSecAt a z₀ z) = z := by
  funext k
  by_cases hk : (k : ℕ) < a
  · simp only [logExp, logSecAt, hk, if_true]
    rw [Complex.exp_add, Complex.exp_log (hz₀ k hk), Complex.exp_log (div_ne_zero (hz k hk) (hz₀ k hk))]
    field_simp [hz₀ k hk]
  · simp [logExp, logSecAt, hk]

theorem differentiableAt_logSecAt (z₀ : Fin n → ℂ) (hz₀ : ∀ k : Fin n, (k : ℕ) < a → z₀ k ≠ 0) :
    DifferentiableAt ℂ (logSecAt a z₀) z₀ := by
  rw [differentiableAt_pi]
  intro k
  have hpk : DifferentiableAt ℂ (fun z : Fin n → ℂ => z k) z₀ := differentiableAt_apply k z₀
  by_cases hk : (k : ℕ) < a
  · simp only [logSecAt, hk, if_true]
    refine (differentiableAt_const _).add ?_
    have hq : DifferentiableAt ℂ (fun z : Fin n → ℂ => z k / z₀ k) z₀ := by
      simpa [div_eq_mul_inv] using hpk.mul_const (z₀ k)⁻¹
    refine hq.clog ?_
    simp [div_self (hz₀ k hk), Complex.one_mem_slitPlane]
  · simpa [logSecAt, hk] using hpk

theorem descent : ∀ (n a : ℕ) (ρ : ℝ) (h : (Fin n → ℂ) → ℂ), 0 < ρ → ρ ≤ 1 →
    DifferentiableOn ℂ h {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ} →
    (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ → ∀ k : Fin n, (k : ℕ) < a →
      h (s + Pi.single k (2 * Real.pi * Complex.I)) = h s) →
    ∃ H : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ H
      {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} ∧
      ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ → h s = H (logExp a s) := by
  intro n a ρ h _ hρ1 hd hinv
  refine ⟨fun z => h (logSec a z), ?_, ?_⟩
  · intro z₀ hz₀
    obtain ⟨hb₀, hn₀⟩ := hz₀

    have hU : ∀ᶠ z in 𝓝 z₀, z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0 := by
      have h1 : ∀ᶠ z in 𝓝 z₀, z ∈ Metric.ball (0 : Fin n → ℂ) ρ := Metric.isOpen_ball.mem_nhds hb₀
      refine h1.and ?_
      rw [Filter.eventually_all]
      intro k
      by_cases hk : (k : ℕ) < a
      · exact ((continuous_apply k).continuousAt.eventually_ne (hn₀ k hk)).mono fun z hz _ => hz
      · exact Filter.Eventually.of_forall fun z hk' => absurd hk' hk
    have hEq : (fun z => h (logSec a z)) =ᶠ[𝓝 z₀] fun z => h (logSecAt a z₀ z) := by
      refine hU.mono fun z ⟨hb, hn⟩ => ?_
      refine key hρ1 hinv _ _ ?_ ?_
      · rw [logExp_logSec z hn]; exact hb
      · rw [logExp_logSec z hn, logExp_logSecAt z₀ z hn₀ hn]
    have hD : {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ} ∈ 𝓝 (logSecAt a z₀ z₀) := by
      refine dom_mem_nhds hρ1 _ ?_
      rw [logExp_logSecAt z₀ z₀ hn₀ hn₀]; exact hb₀
    have hh : DifferentiableAt ℂ h (logSecAt a z₀ z₀) := hd.differentiableAt hD
    have hcomp : DifferentiableAt ℂ (h ∘ logSecAt a z₀) z₀ :=
      DifferentiableAt.comp (𝕜 := ℂ) z₀ hh (differentiableAt_logSecAt z₀ hn₀)
    exact (hcomp.congr_of_eventuallyEq hEq).differentiableWithinAt
  · intro s _ hs
    have hn : ∀ k : Fin n, (k : ℕ) < a → logExp a s k ≠ 0 := fun k hk => by
      simp only [logExp, hk, if_true]; exact Complex.exp_ne_zero _
    refine key hρ1 hinv _ _ hs ?_
    rw [logExp_logSec _ hn]

end GlobalTheory.LogDescent
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicDescentPunctPolydiscLogCoverStatement

section

@[expose] public section

open GlobalTheory.ShFam.Hor


theorem _root_.GlobalTheory.T.exists_holomorphic_descent_punctPolydisc_logCover : ∀ (n a : ℕ) (ρ : ℝ) (h : (Fin n → ℂ) → ℂ), 0 < ρ → ρ ≤ 1 → DifferentiableOn ℂ h {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ} → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ → ∀ k : Fin n, (k : ℕ) < a → h (s + Pi.single k (2 * Real.pi * Complex.I)) = h s) → ∃ H : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ H {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} ∧ ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ → h s = H (logExp a s) := by
  first | exact @GlobalTheory.LogDescent.descent | exact GlobalTheory.LogDescent.descent | (intros; apply GlobalTheory.LogDescent.descent <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodQuadFormExtendsHolomorphicPunctPolydisc

section

@[expose] public section

open GlobalTheory.ShFam.Hor

namespace GlobalTheory

theorem periodVec_im_dot {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (v : Fin g → ℤ) :
    (dotProduct (fun i => (v i : ℂ)) (M.mulVec (fun i => (v i : ℂ)))).im
      = dotProduct (fun i => (v i : ℝ)) ((M.map Complex.im).mulVec (fun i => (v i : ℝ))) := by
  simp [dotProduct, Matrix.mulVec, Complex.im_sum, Finset.mul_sum, Complex.mul_im]

theorem periodVec_norm_exp_le {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (hM : (M.map Complex.im).PosDef)
    (v : Fin g → ℤ) :
    ‖Complex.exp (2 * Real.pi * Complex.I *
      dotProduct (fun i => (v i : ℂ)) (M.mulVec (fun i => (v i : ℂ))))‖ ≤ 1 := by
  have h1 : 0 ≤ dotProduct (fun i => (v i : ℝ)) ((M.map Complex.im).mulVec (fun i => (v i : ℝ))) := by
    have := hM.posSemidef.dotProduct_mulVec_nonneg (fun i => (v i : ℝ))
    simpa using this
  rw [Complex.norm_exp, Real.exp_le_one_iff]
  have : (2 * Real.pi * Complex.I *
      dotProduct (fun i => (v i : ℂ)) (M.mulVec (fun i => (v i : ℂ)))).re
      = -(2 * Real.pi) * (dotProduct (fun i => (v i : ℂ)) (M.mulVec (fun i => (v i : ℂ)))).im := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [this, periodVec_im_dot]
  have := Real.pi_pos
  nlinarith

end GlobalTheory

namespace GlobalTheory

theorem periodVec_extends : ∀ (n a g : ℕ) (ha : a ≤ n) (ρ₁ : ℝ) (τ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (v : Fin g → ℤ), 0 < ρ₁ → ρ₁ ≤ 1 → (∀ i j, DifferentiableOn ℂ (fun s => τ s i j) {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁}) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → (τ s).IsSymm ∧ ((τ s).map Complex.im).PosDef) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → ∀ k : Fin a, τ (s + Pi.single (Fin.castLE ha k) (2 * Real.pi * Complex.I)) = τ s + (B k).map (Int.cast : ℤ → ℂ)) → (∀ k, 0 ≤ dotProduct v ((B k).mulVec v)) → ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F (Metric.ball 0 ρ₁) ∧ ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → dotProduct (fun i => (v i : ℂ)) ((τ s).mulVec (fun i => (v i : ℂ))) - ∑ k, s (Fin.castLE ha k) * ((dotProduct v ((B k).mulVec v) : ℤ) : ℂ) / (2 * Real.pi * Complex.I) = F (logExp a s) := by
  intro n a g ha ρ₁ τ B v hρ0 hρ1 hdiff hpos hmono hm
  let vC : Fin g → ℂ := fun i => (v i : ℂ)
  let m : Fin a → ℤ := fun k => dotProduct v ((B k).mulVec v)
  have hc : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hcd : ∀ x : ℂ, 2 * Real.pi * Complex.I * (x / (2 * Real.pi * Complex.I)) = x := fun x => by
    field_simp
  let h : (Fin n → ℂ) → ℂ := fun s => dotProduct vC ((τ s).mulVec vC) -
    ∑ k, s (Fin.castLE ha k) * ((m k : ℤ) : ℂ) / (2 * Real.pi * Complex.I)
  have hdh : DifferentiableOn ℂ h
      {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁} := by
    apply DifferentiableOn.sub
    · simp only [dotProduct, Matrix.mulVec]
      apply DifferentiableOn.fun_sum; intro i _
      apply DifferentiableOn.mul (differentiableOn_const _)
      apply DifferentiableOn.fun_sum; intro j _
      exact (hdiff i j).mul (differentiableOn_const _)
    · apply DifferentiableOn.fun_sum; intro k _
      simp only [div_eq_mul_inv]
      apply DifferentiableOn.mul_const
      apply DifferentiableOn.mul_const
      exact differentiableOn_pi.mp differentiableOn_id (Fin.castLE ha k)
  have hQ : ∀ k : Fin a, dotProduct vC (((B k).map (Int.cast : ℤ → ℂ)).mulVec vC) = ((m k : ℤ) : ℂ) := by
    intro k
    simp [vC, m, dotProduct, Matrix.mulVec, Int.cast_sum, Int.cast_mul]
  have hinv : ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ →
      ∀ k : Fin n, (k : ℕ) < a → h (s + Pi.single k (2 * Real.pi * Complex.I)) = h s := by
    intro s hs hb k hk
    obtain ⟨k', rfl⟩ : ∃ k' : Fin a, Fin.castLE ha k' = k := ⟨⟨k, hk⟩, Fin.ext rfl⟩
    have hτ := hmono s hs hb k'
    simp only [h]
    rw [hτ, Matrix.add_mulVec, dotProduct_add, hQ k']
    have hsum : ∑ j, (s + Pi.single (Fin.castLE ha k') (2 * Real.pi * Complex.I) : Fin n → ℂ) (Fin.castLE ha j)
        * ((m j : ℤ) : ℂ) / (2 * Real.pi * Complex.I)
        = ∑ j, s (Fin.castLE ha j) * ((m j : ℤ) : ℂ) / (2 * Real.pi * Complex.I) + ((m k' : ℤ) : ℂ) := by
      simp only [Pi.add_apply, add_mul, add_div, Finset.sum_add_distrib]
      congr 1
      simp only [Pi.single_apply, (Fin.castLE_injective ha).eq_iff, ite_mul, zero_mul, ite_div, zero_div,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      field_simp
    rw [hsum]; ring
  obtain ⟨H, hHd, hHe⟩ := GlobalTheory.T.exists_holomorphic_descent_punctPolydisc_logCover n a ρ₁ h hρ0 hρ1 hdh hinv
  let m' : Fin n → ℕ := fun j => if hj : (j : ℕ) < a then (m ⟨j, hj⟩).toNat else 0
  have hm0 : ∀ k, (((m k).toNat : ℕ) : ℂ) = ((m k : ℤ) : ℂ) := fun k => by
    have := Int.toNat_of_nonneg (hm k)
    exact_mod_cast this
  have hbound : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ₁, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) →
      ‖Complex.exp (2 * Real.pi * Complex.I * H z)‖ * ∏ k, ‖z k‖ ^ m' k ≤ 1 := by
    intro z hz hz0
    let s : Fin n → ℂ := fun j => if (j : ℕ) < a then Complex.log (z j) else z j
    have hzj : ∀ j, ‖z j‖ < ρ₁ := fun j =>
      lt_of_le_of_lt (norm_le_pi_norm z j) (by simpa using hz)
    have hls : logExp a s = z := by
      funext j; simp only [logExp, s]; split_ifs with hj
      · exact Complex.exp_log (hz0 j hj)
      · rfl
    have hsD : s ∈ logDom n a := by
      simp only [logDom, Set.mem_setOf_eq]
      intro j; simp only [s]; split_ifs with hj
      · rw [Complex.log_re]
        exact Real.log_neg (norm_pos_iff.2 (hz0 j hj)) (lt_of_lt_of_le (hzj j) hρ1)
      · exact lt_of_lt_of_le (hzj j) hρ1
    have hb' : logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ := by rw [hls]; exact hz
    have hHz : h s = H z := by rw [hHe s hsD hb', hls]
    have hprod : ∏ j, (z j) ^ m' j = ∏ k : Fin a, (z (Fin.castLE ha k)) ^ (m k).toNat := by
      symm
      apply Finset.prod_of_injOn (Fin.castLE ha)
      · intro x _ y _ hxy; exact Fin.castLE_injective ha hxy
      · intro x _; simp
      · intro j _ hj
        have : ¬ (j : ℕ) < a := by
          intro hlt; apply hj; exact ⟨⟨j, hlt⟩, by simp, Fin.ext rfl⟩
        simp [m', this]
      · intro k _; simp [m', Fin.coe_castLE, k.isLt]
    have hexp : ∀ k : Fin a, (z (Fin.castLE ha k)) ^ (m k).toNat
        = Complex.exp (s (Fin.castLE ha k) * ((m k : ℤ) : ℂ)) := by
      intro k
      have hk : ((Fin.castLE ha k : Fin n) : ℕ) < a := by simp
      rw [mul_comm, ← hm0 k, Complex.exp_nat_mul]
      congr 1
      simp only [s, if_pos hk]; exact (Complex.exp_log (hz0 _ hk)).symm
    calc ‖Complex.exp (2 * Real.pi * Complex.I * H z)‖ * ∏ k, ‖z k‖ ^ m' k
        = ‖Complex.exp (2 * Real.pi * Complex.I * h s) * ∏ k, z k ^ m' k‖ := by
          rw [norm_mul, norm_prod, hHz]; simp only [norm_pow]
      _ = ‖Complex.exp (2 * Real.pi * Complex.I * dotProduct vC ((τ s).mulVec vC))‖ := by
          rw [hprod, Finset.prod_congr rfl (fun k _ => hexp k), ← Complex.exp_sum, ← Complex.exp_add]
          congr 2
          simp only [h]
          rw [mul_sub, Finset.mul_sum, Finset.sum_congr rfl (fun k _ => hcd _)]
          ring
      _ ≤ 1 := periodVec_norm_exp_le _ (hpos s hsD hb').2 v
  obtain ⟨F, hFd, hFe⟩ := GlobalTheory.T.exists_holomorphic_extension_across_coordinate_hyperplanes n a ρ₁ H m' hρ0 hHd hbound
  refine ⟨F, hFd, fun s hs hb => ?_⟩
  rw [hFe _ hb (fun k hk => by simp [logExp, hk, Complex.exp_ne_zero])]
  exact hHe s hs hb

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodQuadFormExtendsHolomorphicPunctPolydiscStatement

section

@[expose] public section

open GlobalTheory.ShFam.Hor


theorem _root_.GlobalTheory.T.periodQuadForm_extends_holomorphic_punctPolydisc : ∀ (n a g : ℕ) (ha : a ≤ n) (ρ₁ : ℝ) (τ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (v : Fin g → ℤ), 0 < ρ₁ → ρ₁ ≤ 1 → (∀ i j, DifferentiableOn ℂ (fun s => τ s i j) {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁}) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → (τ s).IsSymm ∧ ((τ s).map Complex.im).PosDef) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → ∀ k : Fin a, τ (s + Pi.single (Fin.castLE ha k) (2 * Real.pi * Complex.I)) = τ s + (B k).map (Int.cast : ℤ → ℂ)) → (∀ k, 0 ≤ dotProduct v ((B k).mulVec v)) → ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F (Metric.ball 0 ρ₁) ∧ ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → dotProduct (fun i => (v i : ℂ)) ((τ s).mulVec (fun i => (v i : ℂ))) - ∑ k, s (Fin.castLE ha k) * ((dotProduct v ((B k).mulVec v) : ℤ) : ℂ) / (2 * Real.pi * Complex.I) = F (logExp a s) := by
  first | exact @GlobalTheory.periodVec_extends | exact GlobalTheory.periodVec_extends | (intros; apply GlobalTheory.periodVec_extends <;> assumption)
end
end
