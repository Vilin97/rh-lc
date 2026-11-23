module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeYDerivativeTermIntegralPolynomialDecayStatement
public import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedDerivHeckePhiFourierTransformBoundStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnHeckeEisensteinFourierTerm
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIteratedFDerivHeckeFourierFactorLeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIteratedFDerivProdCoordLeLeibnizStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactPiUpperHalfPlaneImBounds

section

@[expose] public section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory

theorem isCompact_pi_upperHalfPlane_im_bounds :
    ∀ (ι : Type) [Fintype ι] (L : Set (ι → ℂ)), IsCompact L → (∀ z ∈ L, ∀ i, 0 < (z i).im) →
    ∃ c c' : ℝ, 0 < c ∧ ∀ z ∈ L, ∀ i, c ≤ (z i).im ∧ (z i).im ≤ c' := by
  intro ι _ L hL hpos
  obtain ⟨C, hC⟩ := hL.isBounded.exists_norm_le
  have hup : ∀ z ∈ L, ∀ i, (z i).im ≤ C := fun z hz i =>
    (Complex.im_le_norm (z i)).trans ((norm_le_pi_norm z i).trans (hC z hz))
  rcases L.eq_empty_or_nonempty with hE | hne
  · exact ⟨1, 0, one_pos, by simp [hE]⟩
  have hm : ∀ i, ∃ m : ℝ, 0 < m ∧ ∀ z ∈ L, m ≤ (z i).im := by
    intro i
    have hc : Continuous fun z : ι → ℂ => (z i).im :=
      Complex.continuous_im.comp (continuous_apply i)
    obtain ⟨x, hx, hmin⟩ := hL.exists_isMinOn hne hc.continuousOn
    exact ⟨(x i).im, hpos x hx i, fun z hz => hmin hz⟩
  choose m hm0 hmle using hm
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, C, one_pos, fun z _ i => isEmptyElim i⟩
  refine ⟨Finset.univ.inf' Finset.univ_nonempty m, C, ?_, fun z hz i => ⟨?_, hup z hz i⟩⟩
  · exact (Finset.lt_inf'_iff _).2 fun i _ => hm0 i
  · exact (Finset.inf'_le _ (Finset.mem_univ i)).trans (hmle i z hz)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactPiUpperHalfPlaneImBoundsStatement

section

@[expose] public section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

theorem _root_.GlobalTheory.T.exists_im_bounds_of_isCompact_upperHalfPlane : ∀ (ι : Type) [Fintype ι] (L : Set (ι → ℂ)), IsCompact L → (∀ z ∈ L, ∀ i, 0 < (z i).im) →
    ∃ c c' : ℝ, 0 < c ∧ ∀ z ∈ L, ∀ i, c ≤ (z i).im ∧ (z i).im ≤ c' := by
  first | exact @GlobalTheory.isCompact_pi_upperHalfPlane_im_bounds | exact GlobalTheory.isCompact_pi_upperHalfPlane_im_bounds | (intros; apply GlobalTheory.isCompact_pi_upperHalfPlane_im_bounds <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedDerivHeckePhiFourierTransformRepr

section

@[expose] public section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section
namespace GlobalTheory.HeckeTwo.TermSmooth

theorem sum_pushforward_eval (σ : ℂ) (F : ℕ × ℕ × ℕ → ℂ) (g : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ)
    (c : ℕ × ℕ × ℕ → Polynomial ℂ) (U S' : Finset (ℕ × ℕ × ℕ)) (hU : ∀ p ∈ U, g p ∈ S') :
    ∑ q ∈ S', (∑ p ∈ U, if g p = q then c p else 0).eval σ * F q = ∑ p ∈ U, (c p).eval σ * F (g p) := by
  simp_rw [Polynomial.eval_finsetSum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p hp => ?_
  simp_rw [apply_ite (Polynomial.eval σ), Polynomial.eval_zero, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq, if_pos (hU p hp)]

theorem iteratedDeriv_hTrans_repr : ∀ j : ℕ, ∃ (S : Finset (ℕ × ℕ × ℕ)) (P : ℕ × ℕ × ℕ → Polynomial ℂ),
    (∀ p ∈ S, 2 ≤ p.1 + 2 * p.2.1 ∧ p.1 + 2 * p.2.1 = p.2.2 + 2 + j) ∧
    ∀ σ ∈ halfPlane, ∀ ν y : ℝ, y ≠ 0 →
      iteratedDeriv j (hTrans σ ν) y = ∑ p ∈ S, (P p).eval σ * GlobalTheory.HeckeTwo.TermSmooth.intT σ ν p.1 p.2.1 p.2.2 y := by
  intro j
  induction j with
  | zero =>
    refine ⟨{(2, 0, 0)}, fun _ => 1, ?_, ?_⟩
    · intro p hp; rw [Finset.mem_singleton] at hp; subst hp; norm_num
    · intro σ hσ ν y hy
      simp [iteratedDeriv_zero, hTrans_eq σ ν hy]
  | succ j ih =>
    obtain ⟨S, P, hS, hP⟩ := ih
    let f1 : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ := fun p => (p.1 + 1, p.2.1, p.2.2)
    let f2 : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ := fun p => (p.1, p.2.1 + 1, p.2.2 + 1)
    let f3 : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ := fun p => (p.1, p.2.1, p.2.2 - 1)
    let T := S.filter (fun p => 1 ≤ p.2.2)
    let c1 : ℕ × ℕ × ℕ → Polynomial ℂ := fun p => Polynomial.C (-(p.1 : ℂ) * I) * P p
    let c2 : ℕ × ℕ × ℕ → Polynomial ℂ := fun p =>
      Polynomial.C 2 * (-Polynomial.X - Polynomial.C (p.2.1 : ℂ)) * P p
    let c3 : ℕ × ℕ × ℕ → Polynomial ℂ := fun p => Polynomial.C (p.2.2 : ℂ) * P p
    let S' := S.image f1 ∪ S.image f2 ∪ T.image f3
    refine ⟨S', fun q => (∑ p ∈ S, if f1 p = q then c1 p else 0) + (∑ p ∈ S, if f2 p = q then c2 p else 0)
        + ∑ p ∈ T, if f3 p = q then c3 p else 0, ?_, ?_⟩
    · intro q hq
      simp only [S', Finset.mem_union, Finset.mem_image, T, Finset.mem_filter] at hq
      rcases hq with (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩) | ⟨p, ⟨hp, hm⟩, rfl⟩ <;>
        have := hS p hp <;> simp only [f1, f2, f3] <;> omega
    · intro σ hσ ν y hy
      have hev : iteratedDeriv j (hTrans σ ν) =ᶠ[nhds y]
          fun y => ∑ p ∈ S, (P p).eval σ * intT σ ν p.1 p.2.1 p.2.2 y :=
        Filter.eventually_of_mem (isOpen_ne.mem_nhds hy) fun z hz => hP σ hσ ν z hz
      have hd : HasDerivAt (fun y => ∑ p ∈ S, (P p).eval σ * intT σ ν p.1 p.2.1 p.2.2 y)
          (∑ p ∈ S, (P p).eval σ * (-(p.1 : ℂ) * I * intT σ ν (p.1 + 1) p.2.1 p.2.2 y
            + 2 * (-σ - (p.2.1 : ℂ)) * intT σ ν p.1 (p.2.1 + 1) (p.2.2 + 1) y
            + (p.2.2 : ℂ) * intT σ ν p.1 p.2.1 (p.2.2 - 1) y)) y :=
        HasDerivAt.fun_sum fun p hp => (hasDerivAt_intT σ hσ ν p.2.2 (hS p hp).1 hy).const_mul _
      rw [iteratedDeriv_succ, hev.deriv_eq, hd.deriv]
      set F : ℕ × ℕ × ℕ → ℂ := fun q => intT σ ν q.1 q.2.1 q.2.2 y with hF
      have e1 := sum_pushforward_eval σ F f1 c1 S S' fun p hp => by
        simp only [S', Finset.mem_union, Finset.mem_image]; exact Or.inl (Or.inl ⟨p, hp, rfl⟩)
      have e2 := sum_pushforward_eval σ F f2 c2 S S' fun p hp => by
        simp only [S', Finset.mem_union, Finset.mem_image]; exact Or.inl (Or.inr ⟨p, hp, rfl⟩)
      have e3 := sum_pushforward_eval σ F f3 c3 T S' fun p hp => by
        simp only [S', Finset.mem_union, Finset.mem_image]; exact Or.inr ⟨p, hp, rfl⟩
      have e3' : ∑ p ∈ T, (c3 p).eval σ * F (f3 p) = ∑ p ∈ S, (c3 p).eval σ * F (f3 p) := by
        refine Finset.sum_filter_of_ne fun p _ hne => ?_
        by_contra h
        have h0 : p.2.2 = 0 := by omega
        apply hne
        simp [c3, h0]
      have split : ∀ q, ((∑ p ∈ S, if f1 p = q then c1 p else 0) + (∑ p ∈ S, if f2 p = q then c2 p else 0)
          + ∑ p ∈ T, if f3 p = q then c3 p else 0).eval σ * F q =
          (∑ p ∈ S, if f1 p = q then c1 p else 0).eval σ * F q +
          (∑ p ∈ S, if f2 p = q then c2 p else 0).eval σ * F q +
          (∑ p ∈ T, if f3 p = q then c3 p else 0).eval σ * F q := by
        intro q; rw [Polynomial.eval_add, Polynomial.eval_add]; ring
      show _ = ∑ q ∈ S', _ * F q
      rw [Finset.sum_congr rfl fun q _ => split q, Finset.sum_add_distrib, Finset.sum_add_distrib, e1, e2, e3, e3',
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      simp only [c1, c2, c3, F, f1, f2, f3, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
        Polynomial.eval_neg, Polynomial.eval_X]
      ring

end GlobalTheory.HeckeTwo.TermSmooth
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedDerivHeckePhiFourierTransformReprStatement

section

@[expose] public section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

theorem _root_.GlobalTheory.T.iteratedDeriv_heckePhiFourierTransform_repr : ∀ j : ℕ, ∃ (S : Finset (ℕ × ℕ × ℕ)) (P : ℕ × ℕ × ℕ → Polynomial ℂ),
    (∀ p ∈ S, 2 ≤ p.1 + 2 * p.2.1 ∧ p.1 + 2 * p.2.1 = p.2.2 + 2 + j) ∧
    ∀ σ ∈ halfPlane, ∀ ν y : ℝ, y ≠ 0 →
      iteratedDeriv j (hTrans σ ν) y = ∑ p ∈ S, (P p).eval σ * GlobalTheory.HeckeTwo.TermSmooth.intT σ ν p.1 p.2.1 p.2.2 y := by
  first | exact @GlobalTheory.HeckeTwo.TermSmooth.iteratedDeriv_hTrans_repr | exact GlobalTheory.HeckeTwo.TermSmooth.iteratedDeriv_hTrans_repr | (intros; apply GlobalTheory.HeckeTwo.TermSmooth.iteratedDeriv_hTrans_repr <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FTermIteratedFDerivBound

section

@[expose] public section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.HeckeTwo.TermBound

theorem factorSmooth (σ : ℂ) (hσ : σ ∈ halfPlane) (ν β : ℝ) (hβ : β ≠ 0) :
    ContDiffOn ℝ ∞ (fun w : ℂ => Complex.exp (2 * (Real.pi : ℂ) * I * ((ν * β * w.re : ℝ) : ℂ)) *
      hTrans σ ν (β * w.im)) {w : ℂ | 0 < w.im} := by
  have hre : ContDiff ℝ ∞ (fun w : ℂ => ((ν * β * w.re : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_const.mul Complex.reCLM.contDiff)
  have h1 : ContDiff ℝ ∞ (fun w : ℂ => Complex.exp (2 * (Real.pi : ℂ) * I * ((ν * β * w.re : ℝ) : ℂ))) :=
    Complex.contDiff_exp.comp (contDiff_const.mul hre)
  have h2 : ContDiffOn ℝ ∞ (fun w : ℂ => hTrans σ ν (β * w.im)) {w : ℂ | 0 < w.im} := by
    refine (GlobalTheory.HeckeTwo.TermSmooth.contDiffOn_hTrans σ hσ ν).comp
      (contDiff_const.mul Complex.imCLM.contDiff : ContDiff ℝ ∞ fun w : ℂ => β * w.im).contDiffOn ?_
    intro w hw; exact mul_ne_zero hβ (ne_of_gt hw)
  exact h1.contDiffOn.mul h2

theorem fTerm_iteratedFDeriv_bound : ∀ (F : Type) [Field F] [NumberField F] (K : Set ℂ), IsCompact K → K ⊆ halfPlane →
    ∀ L : Set (Emb F → ℂ), IsCompact L → L ⊆ upperHalf F → ∀ n : ℕ, ∃ m : ℕ, ∀ N : ℕ, ∃ C : ℝ,
      ∀ σ ∈ K, ∀ z ∈ L, ∀ b ν : F, b ≠ 0 → ν ≠ 0 →
        ‖iteratedFDeriv ℝ n (fun z : Emb F → ℂ => fTerm σ z b ν) z‖ ≤
          C * ∏ τ : Emb F, (|τ b| + |τ b|⁻¹) ^ m / (1 + |τ ν * τ b|) ^ N := by
  intro F _ _ K hK hKH L hL hLH n
  obtain ⟨c, c', hc, hcc⟩ := GlobalTheory.T.exists_im_bounds_of_isCompact_upperHalfPlane (Emb F) L hL (fun z hz τ => hLH hz τ)
  have hfb := GlobalTheory.T.norm_iteratedFDeriv_heckeFourierFactor_le (GlobalTheory.T.iteratedDeriv_heckePhiFourierTransform_bound GlobalTheory.T.iteratedDeriv_heckePhiFourierTransform_repr GlobalTheory.T.heckeYDerivativeTermIntegral_polynomial_decay) K hK hKH c c' hc
  choose mk hmk using hfb
  refine ⟨(Finset.range (n + 1)).sup mk, fun N => ?_⟩
  choose Ck hCk using fun k => hmk k N
  refine ⟨n.factorial * (∑ k ∈ Finset.range (n + 1), max (Ck k) 0) ^ Fintype.card (Emb F), ?_⟩
  intro σ hσ z hz b ν hb hν
  have hσH : σ ∈ halfPlane := hKH hσ
  set m := (Finset.range (n + 1)).sup mk with hm
  set C0 := ∑ k ∈ Finset.range (n + 1), max (Ck k) 0 with hC0
  set g : Emb F → ℂ → ℂ := fun τ w => Complex.exp (2 * (Real.pi : ℂ) * I * ((τ ν * τ b * w.re : ℝ) : ℂ)) *
    hTrans σ (τ ν) (τ b * w.im) with hg
  have hfun : (fun z : Emb F → ℂ => fTerm σ z b ν) = fun z => ∏ τ, g τ (z τ) := rfl
  have hτb : ∀ τ : Emb F, τ b ≠ 0 := fun τ => (map_ne_zero τ).2 hb
  have hτν : ∀ τ : Emb F, τ ν ≠ 0 := fun τ => (map_ne_zero τ).2 hν
  have hsm : ∀ τ, ContDiffOn ℝ ∞ (g τ) {w : ℂ | 0 < w.im} := fun τ => factorSmooth σ hσH (τ ν) (τ b) (hτb τ)
  have hopen : ∀ τ : Emb F, IsOpen {w : ℂ | 0 < w.im} := fun _ => isOpen_lt continuous_const Complex.continuous_im
  rw [hfun]
  refine (GlobalTheory.T.norm_iteratedFDeriv_prod_coord_le_leibniz (Emb F) g (fun _ => {w : ℂ | 0 < w.im}) hopen hsm z (fun τ => hLH hz τ) n).trans ?_
  have hfac : ∀ τ, ∑ k ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ k (g τ) (z τ)‖ ≤
      C0 * ((|τ b| + |τ b|⁻¹) ^ m / (1 + |τ ν * τ b|) ^ N) := by
    intro τ
    rw [hC0, Finset.sum_mul]
    refine Finset.sum_le_sum fun k hk => ?_
    have h1 := hCk k σ hσ (τ ν) (τ b) (hτν τ) (hτb τ) (z τ) (hcc z hz τ).1 (hcc z hz τ).2
    have hB1 : (1 : ℝ) ≤ |τ b| + |τ b|⁻¹ := by
      have hp : 0 < |τ b| := abs_pos.2 (hτb τ)
      rcases le_total 1 |τ b| with h | h
      · linarith [inv_pos.2 hp]
      · have : 1 ≤ |τ b|⁻¹ := (one_le_inv₀ hp).2 h
        linarith
    have hmk' : mk k ≤ m := Finset.le_sup hk
    have hpow : (|τ b| + |τ b|⁻¹) ^ mk k ≤ (|τ b| + |τ b|⁻¹) ^ m := pow_le_pow_right₀ hB1 hmk'
    have hden : 0 < (1 + |τ ν * τ b|) ^ N := by positivity
    calc ‖iteratedFDeriv ℝ k (g τ) (z τ)‖ ≤ Ck k * (|τ b| + |τ b|⁻¹) ^ mk k / (1 + |τ ν * τ b|) ^ N := h1
      _ ≤ max (Ck k) 0 * ((|τ b| + |τ b|⁻¹) ^ m / (1 + |τ ν * τ b|) ^ N) := by
        rw [mul_div_assoc]
        exact mul_le_mul (le_max_left _ _) (div_le_div_of_nonneg_right hpow hden.le) (by positivity)
          (le_max_right _ _)
  calc (n.factorial : ℝ) * ∏ τ, ∑ k ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ k (g τ) (z τ)‖
      ≤ n.factorial * ∏ τ : Emb F, (C0 * ((|τ b| + |τ b|⁻¹) ^ m / (1 + |τ ν * τ b|) ^ N)) := by
        exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun τ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
          (fun τ _ => hfac τ)) (by positivity)
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]; ring

end GlobalTheory.HeckeTwo.TermBound
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FTermIteratedFDerivBoundStatement

section

@[expose] public section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

theorem _root_.GlobalTheory.T.norm_iteratedFDeriv_fTerm_le_of_isCompact : ∀ (F : Type) [Field F] [NumberField F] (K : Set ℂ), IsCompact K → K ⊆ halfPlane →
    ∀ L : Set (Emb F → ℂ), IsCompact L → L ⊆ upperHalf F → ∀ n : ℕ, ∃ m : ℕ, ∀ N : ℕ, ∃ C : ℝ,
      ∀ σ ∈ K, ∀ z ∈ L, ∀ b ν : F, b ≠ 0 → ν ≠ 0 →
        ‖iteratedFDeriv ℝ n (fun z : Emb F → ℂ => fTerm σ z b ν) z‖ ≤
          C * ∏ τ : Emb F, (|τ b| + |τ b|⁻¹) ^ m / (1 + |τ ν * τ b|) ^ N := by
  first | exact @GlobalTheory.HeckeTwo.TermBound.fTerm_iteratedFDeriv_bound | exact GlobalTheory.HeckeTwo.TermBound.fTerm_iteratedFDeriv_bound | (intros; apply GlobalTheory.HeckeTwo.TermBound.fTerm_iteratedFDeriv_bound <;> assumption)
end
end
