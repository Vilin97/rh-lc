module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticDoublingMapLocalInverseStatement
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.Schwarz
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
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.DoublingLimitLocalLogarithmStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IterDifferentiableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Topology.Sheaves.Presheaf

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticGroupLawBoundedCommutator

section

@[expose] public section

open Set Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Metric

theorem norm_le_mul_norm_div_of_bounded_on_ball {V W : Type} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] {ψ : V → W} {R M : ℝ}
    (hd : DifferentiableOn ℂ ψ (ball (0 : V) R)) (h0 : ψ 0 = 0)
    (hM : ∀ x ∈ ball (0 : V) R, ‖ψ x‖ ≤ M) {x : V} (hx : x ∈ ball (0 : V) R) :
    ‖ψ x‖ ≤ M * ‖x‖ / R := by
  have h := Complex.dist_le_div_mul_dist_of_mapsTo_ball (R₂ := M) hd (by
    intro y hy
    rw [mem_closedBall, h0, dist_zero_right]
    exact hM y hy) hx
  rw [h0, dist_zero_right, dist_zero_right] at h
  calc ‖ψ x‖ ≤ M / R * ‖x‖ := h
    _ = M * ‖x‖ / R := by ring

theorem norm_le_of_vanishing_on_axes {B V W : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    (b₀ : B) (G : B × V × V → W) (R : ℝ) (hR : 0 < R)
    (hG : DifferentiableOn ℂ G (ball b₀ R ×ˢ ball (0 : V) R ×ˢ ball (0 : V) R))
    (hb : ∀ p ∈ ball b₀ R ×ˢ ball (0 : V) R ×ˢ ball (0 : V) R, ‖G p‖ ≤ 1)
    (hz : ∀ b ∈ ball b₀ R, ∀ s ∈ ball (0 : V) R, G (b, s, 0) = 0 ∧ G (b, 0, s) = 0) :
    ∀ b ∈ ball b₀ R, ∀ s ∈ ball (0 : V) R, ∀ t ∈ ball (0 : V) R,
      ‖G (b, s, t)‖ ≤ ‖s‖ * ‖t‖ / R ^ 2 := by
  intro b hbm s hs t ht

  have h1 : ∀ s ∈ ball (0 : V) R, ∀ t ∈ ball (0 : V) R, ‖G (b, s, t)‖ ≤ ‖s‖ / R := by
    intro s hs t ht
    have hd : DifferentiableOn ℂ (fun s' => G (b, s', t)) (ball (0 : V) R) :=
      hG.comp ((differentiableOn_const b).prodMk (differentiableOn_id.prodMk (differentiableOn_const t)))
        (by intro s' hs'; exact ⟨hbm, hs', ht⟩)
    have h := norm_le_mul_norm_div_of_bounded_on_ball hd (hz b hbm t ht).2
      (fun s' hs' => hb _ ⟨hbm, hs', ht⟩) hs
    rwa [one_mul] at h

  have hd : DifferentiableOn ℂ (fun t' => G (b, s, t')) (ball (0 : V) R) :=
    hG.comp ((differentiableOn_const b).prodMk ((differentiableOn_const s).prodMk differentiableOn_id))
      (by intro t' ht'; exact ⟨hbm, hs, ht'⟩)
  have h := norm_le_mul_norm_div_of_bounded_on_ball hd (hz b hbm s hs).1
    (fun t' ht' => h1 s hs t' ht') ht
  calc ‖G (b, s, t)‖ ≤ ‖s‖ / R * ‖t‖ / R := h
    _ = ‖s‖ * ‖t‖ / R ^ 2 := by ring

end GlobalTheory.CompanionTheory.Metric
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticGroupLawBoundedCommutatorStatement

section

@[expose] public section

open Set Filter Topology Metric

theorem _root_.GlobalTheory.T.analytic_group_law_bounded_commutator : ∀ {B V W : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] (b₀ : B) (G : B × V × V → W) (R : ℝ), 0 < R → DifferentiableOn ℂ G (ball b₀ R ×ˢ ball (0 : V) R ×ˢ ball (0 : V) R) → (∀ p ∈ ball b₀ R ×ˢ ball (0 : V) R ×ˢ ball (0 : V) R, ‖G p‖ ≤ 1) → (∀ b ∈ ball b₀ R, ∀ s ∈ ball (0 : V) R, G (b, s, 0) = 0 ∧ G (b, 0, s) = 0) → ∀ b ∈ ball b₀ R, ∀ s ∈ ball (0 : V) R, ∀ t ∈ ball (0 : V) R, ‖G (b, s, t)‖ ≤ ‖s‖ * ‖t‖ / R ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.Metric.norm_le_of_vanishing_on_axes | exact GlobalTheory.CompanionTheory.Metric.norm_le_of_vanishing_on_axes | (intros; apply GlobalTheory.CompanionTheory.Metric.norm_le_of_vanishing_on_axes <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalLogarithmHomomorphism

section

@[expose] public section

open Set Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat.LocalLog

theorem koenigs_limit_additive_for_law : ∀ {B V : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [NormedAddCommGroup V] [NormedSpace ℂ V] (b₀ : B) (h : B × V → V) (μ : B × V × V → V) (L : B × V → V) (ρ C : ℝ), 0 < ρ → 0 ≤ C → (∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ‖h (b, s)‖ ≤ 3 / 5 * ‖s‖) → (∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ∀ t ∈ ball (0 : V) ρ, ‖μ (b, s, t) - s - t‖ ≤ C * ‖s‖ * ‖t‖) → (∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ∀ t ∈ ball (0 : V) ρ, h (b, μ (b, s, t)) = μ (b, h (b, s), h (b, t))) → (∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, Tendsto (fun k : ℕ => (2 : ℂ) ^ k • GlobalTheory.CompanionTheory.Ar.Flat.LocalLog.iter h k (b, s)) atTop (𝓝 (L (b, s)))) → ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ∀ t ∈ ball (0 : V) ρ, μ (b, s, t) ∈ ball (0 : V) ρ → L (b, μ (b, s, t)) = L (b, s) + L (b, t) := by
  intro B V _ _ _ _ b₀ h μ L ρ C _hρ hC hcontr happrox hhom hlim b hb s hs t ht hm
  have hsk := fun k => iter_mem_ball b₀ h ρ hcontr hb hs k
  have htk := fun k => iter_mem_ball b₀ h ρ hcontr hb ht k
  have hiter : ∀ k : ℕ, iter h k (b, μ (b, s, t)) = μ (b, iter h k (b, s), iter h k (b, t)) := by
    intro k
    induction k with
    | zero => rw [iter_zero, iter_zero, iter_zero]
    | succ k ih =>
      rw [iter_succ, iter_succ, iter_succ, ih]
      exact hhom b hb _ (hsk k) _ (htk k)
  have hn2 : ‖(2 : ℂ)‖ = 2 := by simp
  have herr : Tendsto (fun k : ℕ => (2 : ℂ) ^ k •
      (μ (b, iter h k (b, s), iter h k (b, t)) - iter h k (b, s) - iter h k (b, t))) atTop (𝓝 0) := by
    have hg : Tendsto (fun k : ℕ => C * ‖s‖ * ‖t‖ * (18 / 25 : ℝ) ^ k) atTop (𝓝 0) := by
      have := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 18 / 25)
        (by norm_num : (18 / 25 : ℝ) < 1)
      simpa using this.const_mul (C * ‖s‖ * ‖t‖)
    refine squeeze_zero_norm (fun k => ?_) hg
    rw [norm_smul, norm_pow, hn2]
    have h1 := happrox b hb _ (hsk k) _ (htk k)
    have h2 := norm_iter_le b₀ h ρ hcontr hb hs k
    have h3 := norm_iter_le b₀ h ρ hcontr hb ht k
    calc (2 : ℝ) ^ k * ‖μ (b, iter h k (b, s), iter h k (b, t)) - iter h k (b, s) - iter h k (b, t)‖
        ≤ 2 ^ k * (C * ‖iter h k (b, s)‖ * ‖iter h k (b, t)‖) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ 2 ^ k * (C * ((3 / 5) ^ k * ‖s‖) * ((3 / 5) ^ k * ‖t‖)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul (mul_le_mul_of_nonneg_left h2 hC) h3 (norm_nonneg _)
            (mul_nonneg hC (by positivity))
      _ = C * ‖s‖ * ‖t‖ * (18 / 25) ^ k := by
          rw [show (18 / 25 : ℝ) = 2 * (3 / 5) * (3 / 5) by norm_num, mul_pow, mul_pow]
          ring
  have hsum : Tendsto (fun k : ℕ => (2 : ℂ) ^ k • iter h k (b, μ (b, s, t))) atTop
      (𝓝 (L (b, s) + L (b, t) + 0)) := by
    refine (((hlim b hb s hs).add (hlim b hb t ht)).add herr).congr (fun k => ?_)
    rw [hiter k, smul_sub, smul_sub]
    abel
  rw [add_zero] at hsum
  exact tendsto_nhds_unique (hlim b hb _ hm) hsum

end GlobalTheory.CompanionTheory.Ar.Flat.LocalLog
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalLogarithmHomomorphismStatement

section

@[expose] public section

open Set Filter Topology Metric

theorem _root_.GlobalTheory.T.local_logarithm_homomorphism : ∀ {B V : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [NormedAddCommGroup V] [NormedSpace ℂ V] (b₀ : B) (h : B × V → V) (μ : B × V × V → V) (L : B × V → V) (ρ C : ℝ), 0 < ρ → 0 ≤ C → (∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ‖h (b, s)‖ ≤ 3 / 5 * ‖s‖) → (∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ∀ t ∈ ball (0 : V) ρ, ‖μ (b, s, t) - s - t‖ ≤ C * ‖s‖ * ‖t‖) → (∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ∀ t ∈ ball (0 : V) ρ, h (b, μ (b, s, t)) = μ (b, h (b, s), h (b, t))) → (∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, Tendsto (fun k : ℕ => (2 : ℂ) ^ k • GlobalTheory.CompanionTheory.Ar.Flat.LocalLog.iter h k (b, s)) atTop (𝓝 (L (b, s)))) → ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ∀ t ∈ ball (0 : V) ρ, μ (b, s, t) ∈ ball (0 : V) ρ → L (b, μ (b, s, t)) = L (b, s) + L (b, t) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.LocalLog.koenigs_limit_additive_for_law | exact GlobalTheory.CompanionTheory.Ar.Flat.LocalLog.koenigs_limit_additive_for_law | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.LocalLog.koenigs_limit_additive_for_law <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannFormPeriodDeterminant

section

@[expose] public section

open Set Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_local_log_of_commutative_law : ∀ (n g : ℕ) (b₀ : Fin n → ℂ) (μ : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) → (Fin g → ℂ)), AnalyticAt ℂ μ (b₀, 0, 0) → (∀ᶠ p : (Fin n → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0), μ (p.1, p.2, 0) = p.2 ∧ μ (p.1, 0, p.2) = p.2) → (∀ᶠ p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0, 0), μ (p.1, p.2.1, p.2.2) = μ (p.1, p.2.2, p.2.1)) → (∀ᶠ p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0, 0, 0), μ (p.1, μ (p.1, p.2.1, p.2.2.1), p.2.2.2) = μ (p.1, p.2.1, μ (p.1, p.2.2.1, p.2.2.2))) → ∃ L : (Fin n → ℂ) × (Fin g → ℂ) → (Fin g → ℂ), AnalyticAt ℂ L (b₀, 0) ∧ (∀ᶠ b in 𝓝 b₀, L (b, 0) = 0 ∧ HasFDerivAt (fun s => L (b, s)) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0) ∧ ∀ᶠ p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0, 0), L (p.1, μ p) = L (p.1, p.2.1) + L (p.1, p.2.2) := by
  intro n g b₀ μ hμ hunit hcomm hassoc
  have hμ0 : μ (b₀, 0, 0) = 0 := hunit.self_of_nhds.1

  set G : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) → (Fin g → ℂ) := fun p => μ p - p.2.1 - p.2.2 with hG
  have hGan : AnalyticAt ℂ G (b₀, 0, 0) :=
    (hμ.sub (analyticAt_fst.comp_of_eq analyticAt_snd rfl)).sub (analyticAt_snd.comp_of_eq analyticAt_snd rfl)
  have hG0 : G (b₀, 0, 0) = 0 := by simp [hG, hμ0]
  have hGsmall : ∀ᶠ p in 𝓝 ((b₀, 0, 0) : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ)), ‖G p‖ < 1 := by
    filter_upwards [hGan.continuousAt (ball_mem_nhds (G (b₀, 0, 0)) one_pos)] with p hp
    simpa [hG0] using hp
  obtain ⟨R₁, hR₁, hball₁⟩ := Metric.eventually_nhds_iff_ball.1 (hGsmall.and hGan.eventually_analyticAt)
  obtain ⟨R₂, hR₂, hball₂⟩ := Metric.eventually_nhds_iff_ball.1 hunit
  set R := min R₁ R₂ with hRdef
  have hR : 0 < R := lt_min hR₁ hR₂
  have hRG : ∀ b ∈ ball b₀ R, ∀ s ∈ ball (0 : Fin g → ℂ) R, ∀ t ∈ ball (0 : Fin g → ℂ) R, ‖G (b, s, t)‖ < 1 ∧ AnalyticAt ℂ G (b, s, t) := by
    intro b hb s hs t ht
    refine hball₁ (b, s, t) ?_
    rw [← ball_prod_same, ← ball_prod_same]
    exact ⟨ball_subset_ball (min_le_left _ _) hb, ball_subset_ball (min_le_left _ _) hs, ball_subset_ball (min_le_left _ _) ht⟩
  have hRu : ∀ b ∈ ball b₀ R, ∀ s ∈ ball (0 : Fin g → ℂ) R, μ (b, s, 0) = s ∧ μ (b, 0, s) = s := by
    intro b hb s hs
    refine hball₂ (b, s) ?_
    rw [← ball_prod_same]
    exact ⟨ball_subset_ball (min_le_right _ _) hb, ball_subset_ball (min_le_right _ _) hs⟩
  have hGbound : ∀ b ∈ ball b₀ R, ∀ s ∈ ball (0 : Fin g → ℂ) R, ∀ t ∈ ball (0 : Fin g → ℂ) R, ‖μ (b, s, t) - s - t‖ ≤ ‖s‖ * ‖t‖ / R ^ 2 := by
    refine GlobalTheory.T.analytic_group_law_bounded_commutator b₀ G R hR ?_ ?_ ?_
    · rintro ⟨b, s, t⟩ ⟨hb, hs, ht⟩
      exact (hRG b hb s hs t ht).2.differentiableAt.differentiableWithinAt
    · rintro ⟨b, s, t⟩ ⟨hb, hs, ht⟩
      exact (hRG b hb s hs t ht).1.le
    · intro b hb s hs
      have := hRu b hb s hs
      simp [hG, this.1, this.2]
  set C : ℝ := 1 / R ^ 2 with hCdef
  have hCpos : 0 < C := by positivity
  have hbound : ∀ b ∈ ball b₀ R, ∀ s ∈ ball (0 : Fin g → ℂ) R, ∀ t ∈ ball (0 : Fin g → ℂ) R, ‖μ (b, s, t) - s - t‖ ≤ C * ‖s‖ * ‖t‖ := by
    intro b hb s hs t ht
    refine (hGbound b hb s hs t ht).trans (le_of_eq ?_)
    rw [hCdef]; ring
  set d : (Fin n → ℂ) × (Fin g → ℂ) → (Fin g → ℂ) := fun p => μ (p.1, p.2, p.2) with hd
  have hdan : AnalyticAt ℂ d (b₀, 0) := by
    have h1 : AnalyticAt ℂ (fun p : (Fin n → ℂ) × (Fin g → ℂ) => (p.1, p.2, p.2)) (b₀, 0) :=
      analyticAt_fst.prod (analyticAt_snd.prod analyticAt_snd)
    exact AnalyticAt.comp_of_eq hμ h1 rfl
  have hd0 : d (b₀, 0) = 0 := hμ0
  have hdderiv : HasFDerivAt d ((2 : ℂ) • ContinuousLinearMap.snd ℂ (Fin n → ℂ) (Fin g → ℂ)) (b₀, 0) := by
    refine HasFDerivAt.of_isLittleO ?_
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    have hmem : ball ((b₀, 0) : (Fin n → ℂ) × (Fin g → ℂ)) (min R (c / C)) ∈ 𝓝 ((b₀, 0) : (Fin n → ℂ) × (Fin g → ℂ)) :=
      ball_mem_nhds _ (lt_min hR (by positivity))
    filter_upwards [hmem] with p hp
    obtain ⟨b, s⟩ := p
    rw [← ball_prod_same] at hp
    obtain ⟨hb, hs⟩ := hp
    have hb' : b ∈ ball b₀ R := ball_subset_ball (min_le_left _ _) hb
    have hs' : s ∈ ball (0 : Fin g → ℂ) R := ball_subset_ball (min_le_left _ _) hs
    have h1 := hbound b hb' s hs' s hs'
    have hsn : ‖s‖ < c / C := by simpa using (ball_subset_ball (min_le_right _ _) hs)
    have heq : d (b, s) - d (b₀, 0) - ((2 : ℂ) • ContinuousLinearMap.snd ℂ (Fin n → ℂ) (Fin g → ℂ)) ((b, s) - (b₀, 0)) = μ (b, s, s) - s - s := by
      rw [hd0]
      simp [hd, two_smul]
      abel
    rw [heq]
    have hle : ‖s‖ ≤ ‖((b, s) : (Fin n → ℂ) × (Fin g → ℂ)) - (b₀, 0)‖ := by
      simp [Prod.norm_def]
    have hCs : C * ‖s‖ ≤ c := ((lt_div_iff₀' hCpos).1 hsn).le
    calc ‖μ (b, s, s) - s - s‖ ≤ C * ‖s‖ * ‖s‖ := h1
      _ ≤ c * ‖s‖ := by gcongr
      _ ≤ c * ‖((b, s) : (Fin n → ℂ) × (Fin g → ℂ)) - (b₀, 0)‖ := by gcongr
  obtain ⟨h, hhan, hh0, H1, H2⟩ := GlobalTheory.T.analytic_doubling_map_local_inverse b₀ d hdan hd0 hdderiv
  have hmed := LocalLog.medial_eventually b₀ μ hμ.continuousAt hμ0 hcomm hassoc
  have hhc : ContinuousAt h (b₀, 0) := hhan.continuousAt
  have t0 : Tendsto (fun p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => p.1) (𝓝 (b₀, 0, 0)) (𝓝 b₀) :=
    continuous_fst.tendsto _
  have t1 : Tendsto (fun p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => (p.1, p.2.1)) (𝓝 (b₀, 0, 0)) (𝓝 (b₀, 0)) :=
    t0.prodMk_nhds ((continuous_fst.comp continuous_snd).tendsto _)
  have t2 : Tendsto (fun p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => (p.1, p.2.2)) (𝓝 (b₀, 0, 0)) (𝓝 (b₀, 0)) :=
    t0.prodMk_nhds ((continuous_snd.comp continuous_snd).tendsto _)
  have ts : Tendsto (fun p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => h (p.1, p.2.1)) (𝓝 (b₀, 0, 0)) (𝓝 0) := by
    simpa [Function.comp_def, hh0] using hhc.tendsto.comp t1
  have tt : Tendsto (fun p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => h (p.1, p.2.2)) (𝓝 (b₀, 0, 0)) (𝓝 0) := by
    simpa [Function.comp_def, hh0] using hhc.tendsto.comp t2
  have t3 : Tendsto (fun p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => (p.1, h (p.1, p.2.1), h (p.1, p.2.2))) (𝓝 (b₀, 0, 0)) (𝓝 (b₀, 0, 0)) :=
    t0.prodMk_nhds (ts.prodMk_nhds tt)
  have t4 : Tendsto (fun p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => (p.1, μ (p.1, h (p.1, p.2.1), h (p.1, p.2.2)))) (𝓝 (b₀, 0, 0)) (𝓝 (b₀, 0)) :=
    t0.prodMk_nhds (by simpa [Function.comp_def, hμ0] using hμ.continuousAt.tendsto.comp t3)
  have hhom : ∀ᶠ p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0, 0), h (p.1, μ p) = μ (p.1, h (p.1, p.2.1), h (p.1, p.2.2)) := by
    filter_upwards [t1.eventually H1, t2.eventually H1, t3.eventually hmed, t4.eventually H2] with p e1 e2 e3 e4
    obtain ⟨b, s, t⟩ := p
    have e1' : μ (b, h (b, s), h (b, s)) = s := e1
    have e2' : μ (b, h (b, t), h (b, t)) = t := e2
    have e3' : μ (b, μ (b, h (b, s), h (b, s)), μ (b, h (b, t), h (b, t))) = μ (b, μ (b, h (b, s), h (b, t)), μ (b, h (b, s), h (b, t))) := e3
    have e4' : h (b, μ (b, μ (b, h (b, s), h (b, t)), μ (b, h (b, s), h (b, t)))) = μ (b, h (b, s), h (b, t)) := e4
    rw [e1', e2'] at e3'
    show h (b, μ (b, s, t)) = μ (b, h (b, s), h (b, t))
    rw [e3', e4']
  have hsmall : ∀ᶠ q in 𝓝 ((b₀, 0) : (Fin n → ℂ) × (Fin g → ℂ)), ‖h q‖ < min R (1 / (3 * C)) := by
    have hpos : 0 < min R (1 / (3 * C)) := lt_min hR (by positivity)
    filter_upwards [hhc (ball_mem_nhds (h (b₀, 0)) hpos)] with p hp
    simpa [hh0] using hp
  obtain ⟨ρ₁, hρ₁, hb₁⟩ := Metric.eventually_nhds_iff_ball.1 (H1.and (hhan.eventually_analyticAt.and hsmall))
  obtain ⟨ρ₂, hρ₂, hb₂⟩ := Metric.eventually_nhds_iff_ball.1 hhom
  set ρ := min R (min ρ₁ ρ₂) with hρdef
  have hρ : 0 < ρ := lt_min hR (lt_min hρ₁ hρ₂)
  have hρR : ρ ≤ R := min_le_left _ _
  have hρ1 : ρ ≤ ρ₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hρ2 : ρ ≤ ρ₂ := (min_le_right _ _).trans (min_le_right _ _)
  have hq : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : Fin g → ℂ) ρ, μ (b, h (b, s), h (b, s)) = s ∧ AnalyticAt ℂ h (b, s) ∧ ‖h (b, s)‖ < min R (1 / (3 * C)) := by
    intro b hb s hs
    refine hb₁ (b, s) ?_
    rw [← ball_prod_same]
    exact ⟨ball_subset_ball hρ1 hb, ball_subset_ball hρ1 hs⟩
  have hhomρ : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : Fin g → ℂ) ρ, ∀ t ∈ ball (0 : Fin g → ℂ) ρ, h (b, μ (b, s, t)) = μ (b, h (b, s), h (b, t)) := by
    intro b hb s hs t ht
    refine hb₂ (b, s, t) ?_
    rw [← ball_prod_same, ← ball_prod_same]
    exact ⟨ball_subset_ball hρ2 hb, ball_subset_ball hρ2 hs, ball_subset_ball hρ2 ht⟩
  have hboundρ : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : Fin g → ℂ) ρ, ∀ t ∈ ball (0 : Fin g → ℂ) ρ, ‖μ (b, s, t) - s - t‖ ≤ C * ‖s‖ * ‖t‖ :=
    fun b hb s hs t ht => hbound b (ball_subset_ball hρR hb) s (ball_subset_ball hρR hs) t (ball_subset_ball hρR ht)
  have key : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : Fin g → ℂ) ρ, ‖(2 : ℂ) • h (b, s) - s‖ ≤ C * ‖h (b, s)‖ ^ 2 := by
    intro b hb s hs
    obtain ⟨e1, -, e3⟩ := hq b hb s hs
    have hs' : h (b, s) ∈ ball (0 : Fin g → ℂ) R := by
      rw [mem_ball_zero_iff]; exact e3.trans_le (min_le_left _ _)
    have h1 := hbound b (ball_subset_ball hρR hb) _ hs' _ hs'
    rw [e1] at h1
    have h2 : (2 : ℂ) • h (b, s) - s = -(s - h (b, s) - h (b, s)) := by
      rw [two_smul]; abel
    rw [h2, norm_neg]
    calc _ ≤ _ := h1
      _ = _ := by ring
  have hcontr : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : Fin g → ℂ) ρ, ‖h (b, s)‖ ≤ 3 / 5 * ‖s‖ := by
    intro b hb s hs
    have h1 := key b hb s hs
    obtain ⟨-, -, e3⟩ := hq b hb s hs
    have h3 : ‖h (b, s)‖ < 1 / (3 * C) := e3.trans_le (min_le_right _ _)
    have h4 : C * ‖h (b, s)‖ ≤ 1 / 3 := by
      rw [lt_div_iff₀ (by positivity)] at h3
      nlinarith
    have h5 : ‖(2 : ℂ) • h (b, s)‖ = 2 * ‖h (b, s)‖ := by simp [norm_smul]
    have h6 : ‖(2 : ℂ) • h (b, s)‖ ≤ ‖(2 : ℂ) • h (b, s) - s‖ + ‖s‖ := norm_le_norm_sub_add _ _
    have h7 := norm_nonneg (h (b, s))
    nlinarith
  have hquad : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : Fin g → ℂ) ρ, ‖(2 : ℂ) • h (b, s) - s‖ ≤ C * ‖s‖ ^ 2 := by
    intro b hb s hs
    refine (key b hb s hs).trans ?_
    have h1 := hcontr b hb s hs
    have h2 : ‖h (b, s)‖ ≤ ‖s‖ := by linarith [norm_nonneg s]
    gcongr
  obtain ⟨L, hLu, hLb⟩ := GlobalTheory.T.doubling_limit_local_logarithm b₀ h ρ C hρ hCpos.le hcontr hquad
  have hdiffh : DifferentiableOn ℂ h (ball b₀ ρ ×ˢ ball (0 : Fin g → ℂ) ρ) := by
    rintro ⟨b, s⟩ ⟨hb, hs⟩
    exact (hq b hb s hs).2.1.differentiableAt.differentiableWithinAt
  have hit := fun k => LocalLog.iter_differentiableOn b₀ h ρ hdiffh hcontr k
  have hDopen : IsOpen (ball b₀ ρ ×ˢ ball (0 : Fin g → ℂ) ρ) := isOpen_ball.prod isOpen_ball
  have hLd : DifferentiableOn ℂ L (ball b₀ ρ ×ˢ ball (0 : Fin g → ℂ) ρ) :=
    GlobalTheory.SCV.differentiableOn_of_tendstoLocallyUniformlyOn hDopen hLu.tendstoLocallyUniformlyOn
      (Eventually.of_forall fun k => by
        show DifferentiableOn ℂ ((2 : ℂ) ^ k • GlobalTheory.CompanionTheory.Ar.Flat.LocalLog.iter h k) _
        exact (hit k).const_smul _)
  have hLan : AnalyticAt ℂ L (b₀, 0) :=
    GlobalTheory.SCV.analyticOnNhd_of_differentiableOn hDopen hLd (b₀, 0)
      (Set.mk_mem_prod (mem_ball_self hρ) (mem_ball_self (x := (0 : Fin g → ℂ)) hρ))
  refine ⟨L, hLan, ?_, ?_⟩
  · filter_upwards [ball_mem_nhds b₀ hρ] with b hb
    have hL0 : L (b, 0) = 0 := by
      have := hLb b hb 0 (mem_ball_self hρ)
      simpa using this
    refine ⟨hL0, ?_⟩
    refine HasFDerivAt.of_isLittleO ?_
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    have hc' : 0 < c / (4 * C) := by positivity
    filter_upwards [ball_mem_nhds (0 : Fin g → ℂ) (lt_min hρ hc')] with s hs
    have hs1 : s ∈ ball (0 : Fin g → ℂ) ρ := ball_subset_ball (min_le_left _ _) hs
    have hs2 : ‖s‖ < c / (4 * C) := by simpa using (ball_subset_ball (min_le_right _ _) hs)
    have h1 := hLb b hb s hs1
    have h2 : 4 * C * ‖s‖ ≤ c := ((lt_div_iff₀' (by positivity)).1 hs2).le
    simp only [hL0, sub_zero, ContinuousLinearMap.id_apply]
    calc ‖L (b, s) - s‖ ≤ 4 * C * ‖s‖ ^ 2 := h1
      _ = 4 * C * ‖s‖ * ‖s‖ := by ring
      _ ≤ c * ‖s‖ := by gcongr
  · have hpt : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : Fin g → ℂ) ρ, Tendsto (fun k : ℕ => (2 : ℂ) ^ k • GlobalTheory.CompanionTheory.Ar.Flat.LocalLog.iter h k (b, s)) atTop (𝓝 (L (b, s))) :=
      fun b hb s hs => hLu.tendsto_at ⟨hb, hs⟩
    have hadd := GlobalTheory.T.local_logarithm_homomorphism b₀ h μ L ρ C hρ hCpos.le hcontr hboundρ hhomρ hpt
    have hμs : ∀ᶠ p in 𝓝 ((b₀, 0, 0) : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ)), μ p ∈ ball (0 : Fin g → ℂ) ρ := by
      filter_upwards [hμ.continuousAt (ball_mem_nhds (μ (b₀, 0, 0)) hρ)] with p hp
      simpa [hμ0] using hp
    filter_upwards [ball_mem_nhds ((b₀, 0, 0) : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ)) hρ, hμs] with p hp hq'
    obtain ⟨b, s, t⟩ := p
    rw [← ball_prod_same, ← ball_prod_same] at hp
    exact hadd b hp.1 s hp.2.1 t hp.2.2 hq'

end GlobalTheory.CompanionTheory.Ar.Flat
end
end
