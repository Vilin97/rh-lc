module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtensionAcrossZeroOfExpTwoPiIBoundStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.Complex.AbsMax
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Calculus.DiffContOnCl
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannExtensionCoordinateHyperplaneStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocallyBoundedOffCoordinateHyperplanes

section

@[expose] public section

open Metric Filter Topology Set

namespace GlobalTheory.HyperplaneLocBound

lemma isOpen_offHyperplanes (n a : ℕ) (ρ : ℝ) :
    IsOpen {z : Fin n → ℂ | z ∈ ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} := by
  have : {z : Fin n → ℂ | z ∈ ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} =
      ball 0 ρ ∩ ⋂ k ∈ (Finset.univ.filter fun k : Fin n => (k : ℕ) < a),
        (fun z : Fin n → ℂ => z k) ⁻¹' {0}ᶜ := by
    ext z; simp
  rw [this]
  exact isOpen_ball.inter (isOpen_biInter_finset fun k _ =>
    (continuous_apply k).isOpen_preimage _ isOpen_compl_singleton)

lemma prod_update_eq {n : ℕ} (z : Fin n → ℂ) (m : Fin n → ℕ) (k : Fin n) (t : ℂ) :
    ∏ j, ‖Function.update z k t j‖ ^ m j =
      ‖t‖ ^ m k * ∏ j ∈ Finset.univ.erase k, ‖z j‖ ^ m j := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

lemma norm_le_of_circle {n a : ℕ} {ρ r : ℝ} {Φ : (Fin n → ℂ) → ℂ} {m : Fin n → ℕ}
    (hext : ∀ (H : ℂ → ℂ) (r C : ℝ) (N : ℕ), 0 < r → DifferentiableOn ℂ H (Metric.ball (0 : ℂ) r \ {0}) → (∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → ‖Complex.exp (2 * Real.pi * Complex.I * H t)‖ * ‖t‖ ^ N ≤ C) → ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (Metric.ball (0 : ℂ) r) ∧ ∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → G t = H t)
    (hΦ : DifferentiableOn ℂ Φ {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0})
    (hgr : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) →
      ‖Complex.exp (2 * Real.pi * Complex.I * Φ z)‖ * ∏ k, ‖z k‖ ^ m k ≤ 1)
    {z₀ z : Fin n → ℂ} (hr : 0 < r) (hsub : ball z₀ (2 * r) ⊆ ball 0 ρ)
    (hz : z ∈ closedBall z₀ r) (hgen : ∀ j, z j ≠ 0) {k : Fin n} (hk0 : z₀ k = 0)
    {B : ℝ} (hB : ∀ t : ℂ, ‖t‖ = r → ‖Φ (Function.update z k t)‖ ≤ B) : ‖Φ z‖ ≤ B := by
  set H : ℂ → ℂ := fun t => Φ (Function.update z k t) with hH
  have hmem : ∀ t ∈ ball (0 : ℂ) (2 * r), Function.update z k t ∈ ball z₀ (2 * r) := by
    intro t ht
    rw [mem_ball, dist_pi_lt_iff (by linarith)]
    intro j
    by_cases hj : j = k
    · subst hj; simpa [hk0] using ht
    · rw [Function.update_of_ne hj]
      exact lt_of_le_of_lt ((dist_le_pi_dist z z₀ j).trans (mem_closedBall.1 hz)) (by linarith)
  have hU : ∀ t ∈ ball (0 : ℂ) (2 * r), t ≠ 0 → Function.update z k t ∈
      {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} := by
    intro t ht ht0
    refine ⟨hsub (hmem t ht), fun j _ => ?_⟩
    by_cases hj : j = k
    · subst hj; simpa using ht0
    · rw [Function.update_of_ne hj]; exact hgen j
  have hHd : DifferentiableOn ℂ H (ball (0 : ℂ) (2 * r) \ {0}) := by
    intro t ht
    have hd := (hΦ _ (hU t ht.1 ht.2)).differentiableAt
      ((isOpen_offHyperplanes n a ρ).mem_nhds (hU t ht.1 ht.2))
    exact (hd.comp t (hasFDerivAt_update z t).differentiableAt).differentiableWithinAt
  set P := ∏ j ∈ Finset.univ.erase k, ‖z j‖ ^ m j with hPdef
  have hP : 0 < P := Finset.prod_pos fun j _ => pow_pos (norm_pos_iff.2 (hgen j)) _
  have hHg : ∀ t ∈ ball (0 : ℂ) (2 * r), t ≠ 0 →
      ‖Complex.exp (2 * Real.pi * Complex.I * H t)‖ * ‖t‖ ^ m k ≤ 1 / P := by
    intro t ht ht0
    have h1 := hgr _ (hU t ht ht0).1 (hU t ht ht0).2
    rw [prod_update_eq, ← mul_assoc] at h1
    exact (le_div_iff₀ hP).2 h1
  obtain ⟨G, hGd, hGH⟩ := hext H (2 * r) (1 / P) (m k) (by linarith) hHd hHg
  have hcl : closedBall (0 : ℂ) r ⊆ ball 0 (2 * r) := closedBall_subset_ball (by linarith)
  have hzk : z k ∈ closedBall (0 : ℂ) r := by
    rw [mem_closedBall]
    have := dist_le_pi_dist z z₀ k
    rw [hk0] at this
    exact this.trans (mem_closedBall.1 hz)
  have key := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
    (hGd.diffContOnCl_ball hcl) (C := B) ?_ (by rw [closure_ball 0 hr.ne']; exact hzk)
  · rw [hGH _ (hcl hzk) (hgen k)] at key
    simpa [H] using key
  · intro t ht
    rw [frontier_ball 0 hr.ne', mem_sphere, dist_zero_right] at ht
    have ht0 : t ≠ 0 := by rintro rfl; simp at ht; linarith
    have htb : t ∈ ball (0 : ℂ) (2 * r) := by rw [mem_ball, dist_zero_right]; linarith
    rw [hGH t htb ht0]
    exact hB t ht

theorem locally_bounded : (∀ (H : ℂ → ℂ) (r C : ℝ) (N : ℕ), 0 < r → DifferentiableOn ℂ H (Metric.ball (0 : ℂ) r \ {0}) → (∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → ‖Complex.exp (2 * Real.pi * Complex.I * H t)‖ * ‖t‖ ^ N ≤ C) → ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (Metric.ball (0 : ℂ) r) ∧ ∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → G t = H t) → ∀ (n a : ℕ) (ρ : ℝ) (Φ : (Fin n → ℂ) → ℂ) (m : Fin n → ℕ), 0 < ρ → DifferentiableOn ℂ Φ {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ‖Complex.exp (2 * Real.pi * Complex.I * Φ z)‖ * ∏ k, ‖z k‖ ^ m k ≤ 1) → ∀ z₀ ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∃ V ∈ nhds z₀, ∃ M : ℝ, ∀ z ∈ V, z ∈ Metric.ball (0 : Fin n → ℂ) ρ → (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ‖Φ z‖ ≤ M := by
  intro hext n a ρ Φ m hρ hΦ hgr z₀ hz₀
  have hUo := isOpen_offHyperplanes n a ρ
  have hδ : 0 < ρ - ‖z₀‖ := by rw [mem_ball, dist_zero_right] at hz₀; linarith
  obtain ⟨r, hr0, hrδ, hrk⟩ : ∃ r : ℝ, 0 < r ∧ 2 * r < ρ - ‖z₀‖ ∧ ∀ k, z₀ k ≠ 0 → r < ‖z₀ k‖ := by
    have h1 : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r := self_mem_nhdsWithin
    have h2 : ∀ᶠ r in 𝓝[>] (0 : ℝ), 2 * r < ρ - ‖z₀‖ := by
      apply nhdsWithin_le_nhds
      have : Tendsto (fun r : ℝ => 2 * r) (𝓝 0) (𝓝 0) := by
        simpa using (continuous_const_mul (2 : ℝ)).tendsto 0
      exact this.eventually (gt_mem_nhds hδ)
    have h3 : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ k, z₀ k ≠ 0 → r < ‖z₀ k‖ := by
      rw [eventually_all]; intro k
      by_cases hk : z₀ k = 0
      · exact Eventually.of_forall fun _ h => absurd hk h
      · exact (show ∀ᶠ r in 𝓝[>] (0 : ℝ), r < ‖z₀ k‖ from
          nhdsWithin_le_nhds (gt_mem_nhds (norm_pos_iff.2 hk))).mono fun r hr _ => hr
    exact (h1.and (h2.and h3)).exists
  have hsub : ball z₀ (2 * r) ⊆ ball 0 ρ := ball_subset_ball' (by rw [dist_zero_right]; linarith)
  set K := closedBall z₀ r ∩ {ζ : Fin n → ℂ | ∀ k : Fin n, (k : ℕ) < a → z₀ k = 0 → ‖ζ k‖ = r}
    with hK
  have hKc : IsCompact K := (isCompact_closedBall z₀ r).inter_right (by
    simp only [setOf_forall]
    exact isClosed_iInter fun k => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_eq (continuous_norm.comp (continuous_apply k)) continuous_const)
  have hKU : K ⊆ {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} := by
    rintro ζ ⟨hζ, hζc⟩
    refine ⟨hsub (closedBall_subset_ball (by linarith) hζ), fun k hk => ?_⟩
    by_cases h0 : z₀ k = 0
    · intro h; have := hζc k hk h0; rw [h, norm_zero] at this; linarith
    · intro h
      have h1 := dist_le_pi_dist ζ z₀ k
      rw [h, dist_comm, dist_zero_right] at h1
      have := hrk k h0
      linarith [mem_closedBall.1 hζ]
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn (hΦ.continuousOn.mono hKU)
  have hind : ∀ S : Finset (Fin n), ∀ z : Fin n → ℂ, (∀ j, z j ≠ 0) → z ∈ closedBall z₀ r →
      (∀ k : Fin n, (k : ℕ) < a → z₀ k = 0 → k ∉ S → ‖z k‖ = r) → ‖Φ z‖ ≤ M := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · intro z _ hz hc
      exact hM z ⟨hz, fun k hk h0 => hc k hk h0 (by simp)⟩
    · intro k S hkS ih z hgen hz hc
      by_cases hk : (k : ℕ) < a ∧ z₀ k = 0
      · refine norm_le_of_circle hext hΦ hgr hr0 hsub hz hgen hk.2 fun t ht => ?_
        apply ih
        · intro j
          by_cases hj : j = k
          · subst hj; simp only [Function.update_self]; rintro rfl; simp at ht; linarith
          · rw [Function.update_of_ne hj]; exact hgen j
        · rw [mem_closedBall, dist_pi_le_iff hr0.le]
          intro j
          by_cases hj : j = k
          · subst hj; simp [hk.2, ht]
          · rw [Function.update_of_ne hj]
            exact (dist_le_pi_dist z z₀ j).trans (mem_closedBall.1 hz)
        · intro j hj h0 hjS
          by_cases hjk : j = k
          · subst hjk; simpa using ht
          · rw [Function.update_of_ne hjk]; exact hc j hj h0 (by simp [hjk, hjS])
      · apply ih z hgen hz
        intro j hj h0 hjS
        by_cases hjk : j = k
        · subst hjk; exact absurd ⟨hj, h0⟩ hk
        · exact hc j hj h0 (by simp [hjk, hjS])
  refine ⟨ball z₀ r, ball_mem_nhds z₀ hr0, M, fun z hzV hzρ hza => ?_⟩
  have hzU : z ∈ {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} :=
    ⟨hzρ, hza⟩
  let w : ℂ → Fin n → ℂ := fun s j => if z j = 0 then s else z j
  have hwc : Continuous w := continuous_pi fun j => by
    by_cases h : z j = 0
    · simp only [w, h, if_true]; exact continuous_id
    · simp only [w, h, if_false]; exact continuous_const
  have hw0 : w 0 = z := funext fun j => by by_cases h : z j = 0 <;> simp [w, h]
  have hΦz : ContinuousAt Φ z := (hΦ.differentiableAt (hUo.mem_nhds hzU)).continuousAt
  have hT : Tendsto (fun s => Φ (w s)) (𝓝[≠] (0 : ℂ)) (𝓝 (Φ z)) := by
    have hc : ContinuousAt (Φ ∘ w) 0 :=
      ContinuousAt.comp (x := 0) (by rw [hw0]; exact hΦz) hwc.continuousAt
    have h := hc.tendsto
    rw [Function.comp_apply, hw0] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ s in 𝓝[≠] (0 : ℂ), ‖Φ (w s)‖ ≤ M := by
    have h1 : ∀ᶠ s in 𝓝 (0 : ℂ), w s ∈ ball z₀ r :=
      hwc.continuousAt.preimage_mem_nhds (by rw [hw0]; exact isOpen_ball.mem_nhds hzV)
    filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with s hs hs0
    apply hind Finset.univ (w s)
    · intro j
      simp only [w]
      split_ifs with h
      · exact hs0
      · exact h
    · exact ball_subset_closedBall hs
    · intro k _ _ hk; exact absurd (Finset.mem_univ k) hk
  exact le_of_tendsto hT.norm hev

end GlobalTheory.HyperplaneLocBound
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocallyBoundedOffCoordinateHyperplanesStatement

section

@[expose] public section

open Metric Filter Topology Set

theorem _root_.GlobalTheory.T.locally_bounded_off_coordinate_hyperplanes : (∀ (H : ℂ → ℂ) (r C : ℝ) (N : ℕ), 0 < r → DifferentiableOn ℂ H (Metric.ball (0 : ℂ) r \ {0}) → (∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → ‖Complex.exp (2 * Real.pi * Complex.I * H t)‖ * ‖t‖ ^ N ≤ C) → ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (Metric.ball (0 : ℂ) r) ∧ ∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → G t = H t) → ∀ (n a : ℕ) (ρ : ℝ) (Φ : (Fin n → ℂ) → ℂ) (m : Fin n → ℕ), 0 < ρ → DifferentiableOn ℂ Φ {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ‖Complex.exp (2 * Real.pi * Complex.I * Φ z)‖ * ∏ k, ‖z k‖ ^ m k ≤ 1) → ∀ z₀ ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∃ V ∈ nhds z₀, ∃ M : ℝ, ∀ z ∈ V, z ∈ Metric.ball (0 : Fin n → ℂ) ρ → (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ‖Φ z‖ ≤ M := by
  first | exact @GlobalTheory.HyperplaneLocBound.locally_bounded | exact GlobalTheory.HyperplaneLocBound.locally_bounded | (intros; apply GlobalTheory.HyperplaneLocBound.locally_bounded <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtensionAcrossCoordinateHyperplanes

section

@[expose] public section

open Metric Filter Topology Set

namespace GlobalTheory.HyperplaneExt

theorem norm_le_of_off_hyperplane {n : ℕ} {U V : Set (Fin n → ℂ)} {k : Fin n} {F : (Fin n → ℂ) → ℂ} {M : ℝ}
    (hU : IsOpen U) (hV : IsOpen V) (hF : ContinuousOn F U)
    (hb : ∀ z ∈ V, z ∈ U → z k ≠ 0 → ‖F z‖ ≤ M) : ∀ z ∈ V, z ∈ U → ‖F z‖ ≤ M := by
  intro z hzV hzU
  by_cases hz : z k = 0
  · have hc : ContinuousAt F z := hF.continuousAt (hU.mem_nhds hzU)
    have hupd : Continuous (fun ε : ℂ => Function.update z k ε) := continuous_const.update k continuous_id
    have h0 : Function.update z k 0 = z := by rw [← hz]; exact Function.update_eq_self k z
    have ht : Tendsto (fun ε : ℂ => Function.update z k ε) (𝓝[≠] (0 : ℂ)) (𝓝 z) := by
      have := hupd.tendsto 0
      rw [h0] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hT : Tendsto (fun ε : ℂ => F (Function.update z k ε)) (𝓝[≠] (0 : ℂ)) (𝓝 (F z)) :=
      hc.tendsto.comp ht
    refine le_of_tendsto hT.norm ?_
    have hm : ∀ᶠ ε in 𝓝[≠] (0 : ℂ), Function.update z k ε ∈ V ∩ U :=
      ht (inter_mem (hV.mem_nhds hzV) (hU.mem_nhds hzU))
    filter_upwards [hm, self_mem_nhdsWithin] with ε hε hne
    exact hb _ hε.1 hε.2 (by simpa using hne)
  · exact hb z hzV hzU hz

theorem extend_finset (hR : ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (k : Fin n) (f : (Fin n → ℂ) → ℂ), IsOpen U → DifferentiableOn ℂ f {z | z ∈ U ∧ z k ≠ 0} → (∀ z₀ ∈ U, ∃ V ∈ nhds z₀, ∃ M : ℝ, ∀ z ∈ V, z ∈ U → z k ≠ 0 → ‖f z‖ ≤ M) → ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F U ∧ ∀ z ∈ U, z k ≠ 0 → F z = f z) :
    ∀ (n : ℕ) (s : Finset (Fin n)) (W : Set (Fin n → ℂ)) (Φ : (Fin n → ℂ) → ℂ), IsOpen W →
      DifferentiableOn ℂ Φ {z | z ∈ W ∧ ∀ k ∈ s, z k ≠ 0} →
      (∀ z₀ ∈ W, ∃ V ∈ nhds z₀, ∃ M : ℝ, ∀ z ∈ V, z ∈ W → (∀ k ∈ s, z k ≠ 0) → ‖Φ z‖ ≤ M) →
      ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F W ∧ ∀ z ∈ W, (∀ k ∈ s, z k ≠ 0) → F z = Φ z := by
  intro n s
  induction s using Finset.induction_on with
  | empty =>
    intro W Φ _ hd _
    refine ⟨Φ, ?_, fun _ _ _ => rfl⟩
    simpa using hd
  | insert j t _ ih =>
    intro W Φ hW hd hb
    have hUeq : {z : Fin n → ℂ | z ∈ W ∧ ∀ k ∈ t, z k ≠ 0} = W ∩ ⋂ k ∈ t, {z | z k ≠ 0} := by
      ext z; simp
    have hU : IsOpen {z : Fin n → ℂ | z ∈ W ∧ ∀ k ∈ t, z k ≠ 0} := by
      rw [hUeq]
      exact hW.inter (isOpen_biInter_finset fun k _ => isOpen_ne_fun (continuous_apply k) continuous_const)
    have hd1 : DifferentiableOn ℂ Φ {z | z ∈ {z : Fin n → ℂ | z ∈ W ∧ ∀ k ∈ t, z k ≠ 0} ∧ z j ≠ 0} := by
      refine hd.mono fun z hz => ⟨hz.1.1, ?_⟩
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact hz.2
      · exact hz.1.2 k hk
    obtain ⟨F1, hF1d, hF1e⟩ := hR n _ j Φ hU hd1 (by
      intro z₀ hz₀
      obtain ⟨V, hV, M, hM⟩ := hb z₀ hz₀.1
      refine ⟨V, hV, M, fun z hzV hzU hzj => hM z hzV hzU.1 ?_⟩
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact hzj
      · exact hzU.2 k hk)
    have hall : ∀ z : Fin n → ℂ, (∀ k ∈ insert j t, z k ≠ 0) ↔ z j ≠ 0 ∧ ∀ k ∈ t, z k ≠ 0 := by
      intro z; simp
    obtain ⟨F, hFd, hFe⟩ := ih W F1 hW hF1d (by
      intro z₀ hz₀
      obtain ⟨V, hV, M, hM⟩ := hb z₀ hz₀
      refine ⟨interior V, interior_mem_nhds.mpr hV, M, ?_⟩
      intro z hzV hzW ht
      refine norm_le_of_off_hyperplane (k := j) hU isOpen_interior hF1d.continuousOn
        (fun w hwV hwU hwj => ?_) z hzV ⟨hzW, ht⟩
      rw [hF1e w hwU hwj]
      exact hM w (interior_subset hwV) hwU.1 ((hall w).2 ⟨hwj, hwU.2⟩))
    refine ⟨F, hFd, fun z hz hk => ?_⟩
    have hk' := (hall z).1 hk
    rw [hFe z hz hk'.2, hF1e z ⟨hz, hk'.2⟩ hk'.1]

theorem extension_of_parts
    (h1 : ∀ (H : ℂ → ℂ) (r C : ℝ) (N : ℕ), 0 < r → DifferentiableOn ℂ H (Metric.ball (0 : ℂ) r \ {0}) → (∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → ‖Complex.exp (2 * Real.pi * Complex.I * H t)‖ * ‖t‖ ^ N ≤ C) → ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (Metric.ball (0 : ℂ) r) ∧ ∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → G t = H t) (h2 : (∀ (H : ℂ → ℂ) (r C : ℝ) (N : ℕ), 0 < r → DifferentiableOn ℂ H (Metric.ball (0 : ℂ) r \ {0}) → (∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → ‖Complex.exp (2 * Real.pi * Complex.I * H t)‖ * ‖t‖ ^ N ≤ C) → ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (Metric.ball (0 : ℂ) r) ∧ ∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → G t = H t) → ∀ (n a : ℕ) (ρ : ℝ) (Φ : (Fin n → ℂ) → ℂ) (m : Fin n → ℕ), 0 < ρ → DifferentiableOn ℂ Φ {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ‖Complex.exp (2 * Real.pi * Complex.I * Φ z)‖ * ∏ k, ‖z k‖ ^ m k ≤ 1) → ∀ z₀ ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∃ V ∈ nhds z₀, ∃ M : ℝ, ∀ z ∈ V, z ∈ Metric.ball (0 : Fin n → ℂ) ρ → (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ‖Φ z‖ ≤ M) (h3 : ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (k : Fin n) (f : (Fin n → ℂ) → ℂ), IsOpen U → DifferentiableOn ℂ f {z | z ∈ U ∧ z k ≠ 0} → (∀ z₀ ∈ U, ∃ V ∈ nhds z₀, ∃ M : ℝ, ∀ z ∈ V, z ∈ U → z k ≠ 0 → ‖f z‖ ≤ M) → ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F U ∧ ∀ z ∈ U, z k ≠ 0 → F z = f z) :
    ∀ (n a : ℕ) (ρ : ℝ) (Φ : (Fin n → ℂ) → ℂ) (m : Fin n → ℕ), 0 < ρ → DifferentiableOn ℂ Φ {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ‖Complex.exp (2 * Real.pi * Complex.I * Φ z)‖ * ∏ k, ‖z k‖ ^ m k ≤ 1) → ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F (Metric.ball 0 ρ) ∧ ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → F z = Φ z := by
  intro n a ρ Φ m hρ hd hb
  have hset : {z : Fin n → ℂ | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} =
      {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k ∈ Finset.univ.filter (fun k : Fin n => (k : ℕ) < a), z k ≠ 0} := by
    ext z; simp
  have hmem : ∀ z : Fin n → ℂ, (∀ k ∈ Finset.univ.filter (fun k : Fin n => (k : ℕ) < a), z k ≠ 0) ↔
      ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0 := by
    intro z; simp
  obtain ⟨F, hFd, hFe⟩ := extend_finset h3 n (Finset.univ.filter (fun k : Fin n => (k : ℕ) < a))
    (Metric.ball 0 ρ) Φ isOpen_ball (hset ▸ hd) (by
      intro z₀ hz₀
      obtain ⟨V, hV, M, hM⟩ := h2 h1 n a ρ Φ m hρ hd hb z₀ hz₀
      exact ⟨V, hV, M, fun z hzV hz hk => hM z hzV hz ((hmem z).1 hk)⟩)
  exact ⟨F, hFd, fun z hz hk => hFe z hz ((hmem z).2 hk)⟩

theorem extension_across_coordinate_hyperplanes : ∀ (n a : ℕ) (ρ : ℝ) (Φ : (Fin n → ℂ) → ℂ) (m : Fin n → ℕ), 0 < ρ → DifferentiableOn ℂ Φ {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ‖Complex.exp (2 * Real.pi * Complex.I * Φ z)‖ * ∏ k, ‖z k‖ ^ m k ≤ 1) → ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F (Metric.ball 0 ρ) ∧ ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → F z = Φ z :=
  extension_of_parts GlobalTheory.T.extension_across_zero_of_exp_two_pi_I_bound GlobalTheory.T.locally_bounded_off_coordinate_hyperplanes GlobalTheory.T.exists_differentiableOn_ext_of_bounded_off_hyperplane

end GlobalTheory.HyperplaneExt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtensionAcrossCoordinateHyperplanesStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.exists_holomorphic_extension_across_coordinate_hyperplanes : ∀ (n a : ℕ) (ρ : ℝ) (Φ : (Fin n → ℂ) → ℂ) (m : Fin n → ℕ), 0 < ρ → DifferentiableOn ℂ Φ {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ‖Complex.exp (2 * Real.pi * Complex.I * Φ z)‖ * ∏ k, ‖z k‖ ^ m k ≤ 1) → ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F (Metric.ball 0 ρ) ∧ ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → F z = Φ z := by
  first | exact @GlobalTheory.HyperplaneExt.extension_across_coordinate_hyperplanes | exact GlobalTheory.HyperplaneExt.extension_across_coordinate_hyperplanes | (intros; apply GlobalTheory.HyperplaneExt.extension_across_coordinate_hyperplanes <;> assumption)
end
end
