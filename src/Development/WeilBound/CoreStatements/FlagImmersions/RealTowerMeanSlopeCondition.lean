module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.RefLinked
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import Development.WeilBound.CoreStatements.FlagImmersions.DifferentiableAtAffCoord
public import Development.WeilBound.CoreStatements.FlagImmersions.IsPotentialSumPot
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
public import Development.WeilBound.CoreStatements.FlagImmersions.RealTowerPlurisubharmonicPotential
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

-- Source module: Development.WeilBound.CoreStatements.FlagImmersions.PshSumPotentialsSmallParameter

section

@[expose] public section

noncomputable section

namespace RootFieldNumerics.A1

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology GlobalTheory.CompanionTheory.Ar.PB

theorem scale_le {s : ℝ} (hs : 0 < s) (h1 : s ≤ 1) : Real.exp (-(s ^ 2)⁻¹) ≤ s := by
  have h := Real.one_sub_inv_le_log_of_pos hs
  have hu : 0 < s⁻¹ := inv_pos.2 hs
  have e : (s ^ 2)⁻¹ = s⁻¹ ^ 2 := by rw [inv_pow]
  have hl : -(s ^ 2)⁻¹ ≤ Real.log s := by
    rw [e]
    nlinarith [sq_nonneg (s⁻¹ - 1 / 2)]
  calc Real.exp (-(s ^ 2)⁻¹) ≤ Real.exp (Real.log s) := Real.exp_le_exp.2 hl
    _ = s := Real.exp_log hs

theorem epsT_scale (C : ℝ) {s : ℝ} (hs : 0 < s) :
    epsT C (Real.exp (-(s ^ 2)⁻¹)) = -(2 * C) * (s * Real.log s) * s := by
  have h1 : Real.log (1 / Real.exp (-(s ^ 2)⁻¹)) = (s ^ 2)⁻¹ := by
    rw [one_div, ← Real.exp_neg, neg_neg, Real.log_exp]
  have h2 : Real.log ((s ^ 2)⁻¹) = -(2 * Real.log s) := by
    rw [Real.log_inv, Real.log_pow]
    push_cast
    ring
  unfold epsT
  rw [h1, h2]
  have hs2 : s ^ 2 ≠ 0 := by positivity
  field_simp

theorem epsT_small (C ε : ℝ) (hε : 0 < ε) :
    ∃ s₀ > (0 : ℝ), ∀ s, 0 < s → s ≤ s₀ → |epsT C (Real.exp (-(s ^ 2)⁻¹))| ≤ ε * s := by
  have hc : ContinuousAt (fun x : ℝ => -(2 * C) * (x * Real.log x)) 0 :=
    (continuous_const.mul Real.continuous_mul_log).continuousAt
  obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.1 hc ε hε
  refine ⟨δ / 2, by positivity, fun s hs hsδ => ?_⟩
  have := h (x := s) (by rw [Real.dist_eq, sub_zero, abs_of_pos hs]; linarith)
  simp only [Real.dist_eq, zero_mul, mul_zero, sub_zero] at this
  rw [epsT_scale C hs, abs_mul, abs_of_pos hs]
  exact mul_le_mul_of_nonneg_right this.le hs.le

theorem potT_potential {e : ℕ} {σ : Type} (S : AnSys e σ) (a : σ) {t : ℝ} (h0 : 0 < t) (h1 : t ≤ S.t₀) :
    IsPotential S.A (S.potT a t) :=
  isPotentialAdd _ _ _ (S.sing a).1 (isPotential_ofFun _ _ ((S.reg a).2.2 t h0 h1).1)

theorem psh_sum_potentials_small_parameter : ∀ (e : ℕ) (σ : Type) [Fintype σ] (S : AnSys e σ) (Fl : Set σ) (a' : σ) (c₀ abelian₂ : ℝ), 0 < c₀ → (∀ a ∈ Fl, ∀ t, IsPsh S.A ((S.potT a t).rsmul (-1)) ∧ IsPsh S.A (S.potT a t)) → (∀ t, IsPsh S.A (S.potT a' t + S.Θ.rsmul (-c₀))) → a' ∉ Fl → ∃ s₀ > (0 : ℝ), ∀ s, 0 < s → s ≤ s₀ → Real.exp (-(s ^ 2)⁻¹) ≤ S.t₀ ∧ ∀ c : σ → ℝ, c a' = s → ∑ a, |c a| ≤ abelian₂ → (∀ a ∉ Fl, 0 ≤ c a) → IsPsh S.A (sumPot c (fun a => S.potT a (Real.exp (-(s ^ 2)⁻¹))) + S.Θ.rsmul (-(s * c₀ / 2))) := by
  classical
  intro e σ _ S Fl a' c₀ abelian₂ hc₀ hFl ha' hna'
  have ht0 : 0 < S.t₀ := (S.reg a').1
  have hεp : 0 < c₀ / (2 * (|abelian₂| + 1)) := by positivity
  obtain ⟨s₁, hs₁, heps⟩ := epsT_small S.C (c₀ / (2 * (|abelian₂| + 1))) hεp
  refine ⟨min s₁ (min 1 S.t₀), lt_min hs₁ (lt_min one_pos ht0), fun s hs hss => ?_⟩
  have hs1 : s ≤ 1 := le_trans hss (le_trans (min_le_right _ _) (min_le_left _ _))
  have hst : s ≤ S.t₀ := le_trans hss (le_trans (min_le_right _ _) (min_le_right _ _))
  have hss₁ : s ≤ s₁ := le_trans hss (min_le_left _ _)
  have htt : Real.exp (-(s ^ 2)⁻¹) ≤ S.t₀ := (scale_le hs hs1).trans hst
  refine ⟨htt, fun c hca' hsum hpos => ?_⟩
  set t := Real.exp (-(s ^ 2)⁻¹) with ht
  have htp : 0 < t := Real.exp_pos _
  have hpot : ∀ a, IsPotential S.A (S.potT a t) := fun a => potT_potential S a htp htt
  have hE : |epsT S.C t| ≤ c₀ / (2 * (|abelian₂| + 1)) * s := heps s hs hss₁
  rw [isPsh_iff (isPotentialAdd S.A _ _ (isPotential_sumPot c hpot)
    (isPotentialRsmul S.A _ S.Θ S.potΘ))]
  intro j y hy w
  rw [dl_add_rsmul (isPotential_sumPot c hpot) S.potΘ _ j hy w, dl_sumPot c hpot j hy w]
  have hθ : 0 ≤ dl S.A S.Θ j y w := dl_nonneg_of_pos S.posΘ j hy w
  set θ := dl S.A S.Θ j y w with hθdef
  set E := |epsT S.C t| with hEdef
  have hE0 : 0 ≤ E := abs_nonneg _
  have hterm : ∀ a, -(|c a| * E * θ) ≤ c a * dl S.A (S.potT a t) j y w := by
    intro a
    by_cases hF : a ∈ Fl
    · have hp := hFl a hF t
      have n1 := dl_nonneg hp.1 j hy w
      rw [dl_rsmul (hpot a) (-1) j hy w] at n1
      have n2 := dl_nonneg hp.2 j hy w
      have hz : dl S.A (S.potT a t) j y w = 0 := by linarith
      rw [hz, mul_zero]
      have := mul_nonneg (mul_nonneg (abs_nonneg (c a)) hE0) hθ
      linarith
    · have hca : 0 ≤ c a := hpos a hF
      have hr : IsPsh S.A (S.potT a t + LocPot.rsmul (epsT S.C t) S.Θ) :=
        ((S.reg a).2.2 t htp htt).2.2.2.2.1
      have n1 := dl_nonneg hr j hy w
      rw [dl_add_rsmul (hpot a) S.potΘ _ j hy w] at n1
      have n3 : epsT S.C t * θ ≤ E * θ := mul_le_mul_of_nonneg_right (le_abs_self _) hθ
      have n4 : -(E * θ) ≤ dl S.A (S.potT a t) j y w := by linarith
      rw [abs_of_nonneg hca]
      have := mul_le_mul_of_nonneg_left n4 hca
      linarith
  have ha'l : c₀ * θ ≤ dl S.A (S.potT a' t) j y w := by
    have n1 := dl_nonneg (ha' t) j hy w
    rw [dl_add_rsmul (hpot a') S.potΘ _ j hy w] at n1
    linarith
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a')]
  have hrest : -(∑ a, |c a|) * E * θ ≤
      ∑ a ∈ Finset.univ.erase a', c a * dl S.A (S.potT a t) j y w := by
    calc -(∑ a, |c a|) * E * θ = -(∑ a, |c a| * E * θ) := by
          rw [neg_mul, neg_mul, Finset.sum_mul, Finset.sum_mul]
      _ ≤ -(∑ a ∈ Finset.univ.erase a', |c a| * E * θ) := by
          refine neg_le_neg (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) ?_)
          intro a _ _
          exact mul_nonneg (mul_nonneg (abs_nonneg _) hE0) hθ
      _ = ∑ a ∈ Finset.univ.erase a', -(|c a| * E * θ) := by rw [Finset.sum_neg_distrib]
      _ ≤ _ := Finset.sum_le_sum fun a _ => hterm a
  have hA : c a' * dl S.A (S.potT a' t) j y w ≥ s * (c₀ * θ) := by
    rw [hca']
    exact mul_le_mul_of_nonneg_left ha'l hs.le
  have hLE : (∑ a, |c a|) * E ≤ s * c₀ / 2 := by
    have hL0 : 0 ≤ ∑ a, |c a| := Finset.sum_nonneg fun a _ => abs_nonneg _
    have h1 : (∑ a, |c a|) * E ≤ |abelian₂| * (c₀ / (2 * (|abelian₂| + 1)) * s) :=
      mul_le_mul (hsum.trans (le_abs_self _)) hE hE0 (abs_nonneg _)
    have h2 : |abelian₂| * (c₀ / (2 * (|abelian₂| + 1)) * s) ≤ s * c₀ / 2 := by
      have hL1 : 0 < |abelian₂| + 1 := by positivity
      rw [show |abelian₂| * (c₀ / (2 * (|abelian₂| + 1)) * s) = (s * c₀ / 2) * (|abelian₂| / (|abelian₂| + 1)) by
        field_simp]
      have hq : |abelian₂| / (|abelian₂| + 1) ≤ 1 := by
        rw [div_le_one hL1]; linarith
      have : 0 ≤ s * c₀ / 2 := by positivity
      nlinarith
    linarith
  have hfin : 0 ≤ ((s * c₀ / 2) - (∑ a, |c a|) * E) * θ := mul_nonneg (by linarith) hθ
  nlinarith

end RootFieldNumerics.A1
end
end
end

-- Source module: Development.WeilBound.CoreStatements.FlagImmersions.RealTowerMeanSlopeCondition

section

@[expose] public section

noncomputable section

namespace RootFieldNumerics.A1

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

theorem gap_eq (lam : Ψ × Fin N → ℝ) (p : Ψ × Fin N) :
    PB.gap lam p = lam p - if h : (p.2 : ℕ) + 1 < N then lam (p.1, ⟨(p.2 : ℕ) + 1, h⟩) else 0 := by
  unfold PB.gap PB.gapX
  split_ifs <;> simp

theorem abs_le_l1_norm (lam : Wt Ψ N) (τ : Ψ) (i : Fin N) : |lam τ i| ≤ l1 lam := by
  unfold l1
  calc |lam τ i| ≤ ∑ j : Fin N, |lam τ j| :=
        Finset.single_le_sum (f := fun j => |lam τ j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    _ ≤ ∑ σ : Ψ, ∑ j : Fin N, |lam σ j| :=
        Finset.single_le_sum (f := fun σ => ∑ j : Fin N, |lam σ j|)
          (fun σ _ => Finset.sum_nonneg fun j _ => abs_nonneg _) (Finset.mem_univ τ)

theorem abs_gap_le (mu : Wt Ψ N) (b : ℝ) (hb : ∀ τ i, |mu τ i| ≤ b) (p : Ψ × Fin N) :
    |PB.gap (fun x => mu x.1 x.2) p| ≤ 2 * b := by
  rw [gap_eq]
  have h0 : 0 ≤ b := le_trans (abs_nonneg _) (hb p.1 p.2)
  refine le_trans (abs_sub _ _) ?_
  have h1 : |mu p.1 p.2| ≤ b := hb p.1 p.2
  split_ifs with h
  · have h2 := hb p.1 ⟨(p.2 : ℕ) + 1, h⟩
    simp only at h1 h2 ⊢
    linarith
  · simp only [abs_zero] at h1 ⊢
    linarith

theorem comp_psh {D : ℕ} (S : PB.AnSys D (Option (Ψ × Fin N))) (k : ℕ) (hk : 0 < k) (b : ℝ)
    (h0 : ∀ t x, S.phT none t x = 0)
    (hfl : ∀ τ (i : Fin N), (i : ℕ) + 1 = N → ∀ t, IsPsh S.A ((S.potT (some (τ, i)) t).rsmul (-1)) ∧
      IsPsh S.A (S.potT (some (τ, i)) t))
    (hpos : IsPosPot S.A (S.th none)) :
    ∃ s₀ > (0 : ℝ), ∀ s, 0 < s → s ≤ s₀ → scale s ≤ S.t₀ ∧ ∀ mu : Wt Ψ N, (∀ τ i, |mu τ i| ≤ b) → Dominant mu →
      IsPsh S.A (PB.sumPot (PB.gapS (fun x => mu x.1 x.2) (s / k)) fun a => S.potT a (scale s)) := by
  have hth : IsPotential S.A (S.th none) := (S.sing none).1
  obtain ⟨c₀, hc₀, hcmp⟩ := compare_global hth hpos S.potΘ
  have hpotb : IsPotential S.A (S.th none + LocPot.rsmul (-c₀) S.Θ) :=
    isPotentialAdd S.A _ _ hth (isPotentialRsmul S.A (-c₀) S.Θ S.potΘ)
  have hbase : IsPsh S.A (S.th none + LocPot.rsmul (-c₀) S.Θ) := by
    rw [isPsh_iff hpotb]
    intro j y hy w
    rw [dl_add_rsmul hth S.potΘ (-c₀) j hy w]
    have := hcmp j y hy w
    linarith
  have ha' : ∀ t, IsPsh S.A (S.potT none t + LocPot.rsmul (-c₀) S.Θ) := by
    intro t x j y hy w
    have hy' : y ∈ (S.A.chart j).target ∩ ↑(S.A.chart j).symm ⁻¹'
        (S.th none + LocPot.rsmul (-c₀) S.Θ).U x := by
      refine ⟨hy.1, ?_⟩
      have h2 := hy.2
      simp only [Set.mem_preimage] at h2 ⊢
      exact ⟨h2.1.1, h2.2⟩
    have h3 := hbase x j y hy' w
    convert h3 using 2
    funext z
    show (S.th none).φ x _ + S.phT none t _ + -c₀ * S.Θ.φ x _ =
      (S.th none).φ x _ + -c₀ * S.Θ.φ x _
    rw [h0]
    ring
  let Fl : Set (Option (Ψ × Fin N)) := {a | ∃ p : Ψ × Fin N, a = some p ∧ (p.2 : ℕ) + 1 = N}
  have hFl : ∀ a ∈ Fl, ∀ t, IsPsh S.A (LocPot.rsmul (-1) (S.potT a t)) ∧ IsPsh S.A (S.potT a t) := by
    rintro a ⟨p, rfl, hp⟩ t
    exact hfl p.1 p.2 hp t
  have hnone : (none : Option (Ψ × Fin N)) ∉ Fl := by
    rintro ⟨p, hp, -⟩
    cases hp
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  set abelian₂ : ℝ := 1 + ∑ _p : Ψ × Fin N, (k : ℝ) * (2 * b) with hLam
  obtain ⟨s₁, hs₁, hall⟩ := psh_sum_potentials_small_parameter D _ S Fl none c₀ abelian₂ hc₀ hFl ha' hnone
  refine ⟨min s₁ 1, lt_min hs₁ one_pos, fun s hs hss => ?_⟩
  obtain ⟨hsc, hmain⟩ := hall s hs (le_trans hss (min_le_left _ _))
  have hs1 : s ≤ 1 := le_trans hss (min_le_right _ _)
  refine ⟨hsc, fun mu hmu hdom => ?_⟩
  have hpot : ∀ a, IsPotential S.A (S.potT a (scale s)) :=
    fun a => potT_potential S a (Real.exp_pos _) hsc
  set c : Option (Ψ × Fin N) → ℝ := PB.gapS (fun x => mu x.1 x.2) (s / k) with hc
  have hcn : c none = s / k := rfl
  have hcs : ∀ p, c (some p) = PB.gap (fun x => mu x.1 x.2) p := fun p => rfl
  let c' : Option (Ψ × Fin N) → ℝ := fun a => (k : ℝ) * c a
  have h1 : c' none = s := by
    show (k : ℝ) * c none = s
    rw [hcn]
    field_simp
  have h2 : ∑ a, |c' a| ≤ abelian₂ := by
    rw [Fintype.sum_option, hLam]
    have e1 : |c' none| ≤ 1 := by rw [h1, abs_of_pos hs]; exact hs1
    have e2 : ∑ p : Ψ × Fin N, |c' (some p)| ≤ ∑ _p : Ψ × Fin N, (k : ℝ) * (2 * b) := by
      refine Finset.sum_le_sum fun p _ => ?_
      show |(k : ℝ) * c (some p)| ≤ _
      rw [abs_mul, abs_of_pos hkR, hcs]
      exact mul_le_mul_of_nonneg_left (abs_gap_le mu b hmu p) hkR.le
    linarith
  have h3 : ∀ a ∉ Fl, 0 ≤ c' a := by
    intro a ha
    cases a with
    | none => rw [h1]; exact hs.le
    | some p =>
      show 0 ≤ (k : ℝ) * c (some p)
      refine mul_nonneg hkR.le ?_
      rw [hcs, gap_eq]
      have hlt : (p.2 : ℕ) + 1 < N := by
        have hne : (p.2 : ℕ) + 1 ≠ N := fun h => ha ⟨p, rfl, h⟩
        have := p.2.isLt
        omega
      rw [dite_eq_left hlt]
      have := hdom p.1 p.2 ⟨(p.2 : ℕ) + 1, hlt⟩ (by
        show (p.2 : ℕ) ≤ (p.2 : ℕ) + 1
        omega)
      simp only
      linarith
  have hP : IsPsh S.A (PB.sumPot c' (fun a => S.potT a (scale s)) +
      LocPot.rsmul (-(s * c₀ / 2)) S.Θ) := hmain c' h1 h2 h3
  rw [isPsh_iff (isPotential_sumPot c hpot)]
  intro j y hy w
  have hq := dl_nonneg hP j hy w
  rw [dl_add_rsmul (isPotential_sumPot c' hpot) S.potΘ _ j hy w, dl_sumPot c' hpot j hy w] at hq
  rw [dl_sumPot c hpot j hy w]
  have hΘ := dl_nonneg_of_pos S.posΘ j hy w
  have hsum : ∑ a, c' a * dl S.A (S.potT a (scale s)) j y w =
      (k : ℝ) * ∑ a, c a * dl S.A (S.potT a (scale s)) j y w := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    show (k : ℝ) * c a * _ = _
    ring
  rw [hsum] at hq
  have hsc0 : 0 ≤ s * c₀ / 2 * dl S.A S.Θ j y w := mul_nonneg (by positivity) hΘ
  have hk2 : 0 ≤ (k : ℝ) * ∑ a, c a * dl S.A (S.potT a (scale s)) j y w := by linarith
  exact (mul_nonneg_iff_of_pos_left hkR).mp hk2

end RootFieldNumerics.A1

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

theorem RootFieldNumerics.real_tower_mean_slope_condition : PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (R : RealTower T), R.Smooth → R.Flat → R.Pos → T.A1 := by
  intro _hin II _hII Ψ _ _ N T R hSm hFl hPos
  haveI := T.finC
  haveI := T.neC
  intro abelian₂
  set b : ℝ := abelian₂ + l1 T.nu with hb
  have hex : ∀ c : T.Comp, ∃ s₀ > (0 : ℝ), ∀ s, 0 < s → s ≤ s₀ → scale s ≤ (R.Sys c).t₀ ∧
      ∀ mu : Wt Ψ N, (∀ τ i, |mu τ i| ≤ b) → Dominant mu →
        ReciprocityTheory.AnForm.M.IsPsh (R.Sys c).A (PB.sumPot (PB.gapS (fun x => mu x.1 x.2)
          (s / ((T.M 2 c).kA : ℕ))) fun a => (R.Sys c).potT a (scale s)) := by
    intro c
    exact RootFieldNumerics.A1.comp_psh (R.Sys c) (T.M 2 c).kA (T.M 2 c).kA_pos b ((R.tie 2 c).phT_none)
      (hFl c) (hPos c)
  choose f hfpos hf using hex
  refine ⟨min 1 (Finset.univ.inf' Finset.univ_nonempty f),
    lt_min one_pos ((Finset.lt_inf'_iff _).2 fun c _ => hfpos c), ?_⟩
  intro B _hB c lam s hlam hs hss hdom
  have hs1 : s ≤ 1 := le_trans hss (min_le_left _ _)
  have hsf : s ≤ f c :=
    le_trans hss (le_trans (min_le_right _ _) (Finset.inf'_le f (Finset.mem_univ c)))
  obtain ⟨hsc, hmain⟩ := hf c s hs hsf
  set mu := T.lamS lam s with hmu
  have hbd : ∀ τ i, |mu τ i| ≤ b := by
    intro τ i
    have e1 := RootFieldNumerics.A1.abs_le_l1_norm lam τ i
    have e2 := RootFieldNumerics.A1.abs_le_l1_norm T.nu τ i
    have e0 : mu τ i = lam τ i - s * T.nu τ i := rfl
    rw [e0]
    have e3 : |s * T.nu τ i| ≤ |T.nu τ i| := by
      rw [abs_mul, abs_of_pos hs]
      exact mul_le_of_le_one_left (abs_nonneg _) hs1
    calc |lam τ i - s * T.nu τ i| ≤ |lam τ i| + |s * T.nu τ i| := abs_sub _ _
      _ ≤ b := by rw [hb]; linarith
  have hpsh := hmain mu hbd hdom
  have hk : ((T.M B c).kA : ℝ) = ((T.M 2 c).kA : ℕ) := by rw [R.kA_eq B 2 c]
  obtain ⟨hJ, alg, hsmooth⟩ := hSm B c
  letI := alg
  have ht0 : 0 < scale s := Real.exp_pos _
  intro z hz w hw
  refine RootFieldNumerics.Levi.levi_nonneg (T.M B c).Ω (T.M B c).y (dimFl Ψ N) (T.M B c).arith hsmooth hJ
    (R.tie B c).Re.R ((T.M B c).weight (scale s) mu s)
    (fun k => ∑ j, (T.M B c).coef mu s j * (((T.M B c).line (scale s) j).a k : ℝ)) ?_ ?_ ?_ z hz w hw
  · intro cc zz hcc hzz
    simp only [RootModel.weight, RootFieldNumerics.Levi.log_h_torus _ cc zz hcc hzz]
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
  · intro zz hzz
    have hsm : ∀ j, IsSmoothHerm ((T.M B c).line (scale s) j) := by
      intro j
      cases j with
      | none => exact (T.M B c).A_smooth
      | some r => exact (T.M B c).x_smooth (scale s) r
    show ContDiffAt ℝ 2
      (fun z => ∑ j, (T.M B c).coef mu s j * Real.log (((T.M B c).line (scale s) j).h z)) zz
    exact ContDiffAt.sum fun j _ =>
      contDiffAt_const.mul (RootFieldNumerics.Levi.contDiffAt_log_h (hsm j) zz hzz)
  · intro x j hx u
    refine RootFieldNumerics.Levi.levi_chart_nonneg (R.tie B c).Re (scale s) ht0 hsc _ hpsh x
      (fun y => (T.M B c).weight (scale s) mu s ((R.tie B c).Re.R.lift x y)) ?_ j hx u
    intro y hy
    have hzm : (R.tie B c).Re.R.lift x y ∈ mcPts (T.M B c).P := (R.tie B c).Re.R.mem x y hy
    have hl : ∀ a, Real.log (((R.tie B c).Re.ref a).h ((R.tie B c).Re.R.lift x y)) +
        (R.Sys c).phT a (scale s) ((R.tie B c).Re.π y) =
        Real.log (((R.tie B c).Re.line a (scale s)).h ((R.tie B c).Re.R.lift x y)) :=
      fun a => (RootFieldNumerics.Levi.log_line_lift (R.tie B c).Re a (scale s) ht0 hsc x y hy).symm
    simp only [hl]
    have hnone : Real.log (((R.tie B c).Re.line none (scale s)).h ((R.tie B c).Re.R.lift x y)) =
        Real.log ((T.M B c).A.h ((R.tie B c).Re.R.lift x y)) := by
      rw [← hl none, (R.tie B c).phT_none, add_zero, (R.tie B c).ref_none.2 _ hzm]
    have hsome : ∀ p : Ψ × Fin N,
        Real.log (((R.tie B c).Re.line (some p) (scale s)).h ((R.tie B c).Re.R.lift x y)) =
        -∑ k ≤ p.2, Real.log (((T.M B c).x (scale s) (p.1, k)).h ((R.tie B c).Re.R.lift x y)) :=
      fun p => (R.tie B c).fund_reg p.1 p.2 (scale s) ht0 hsc _ hzm
    rw [Fintype.sum_option, hnone]
    simp only [hsome]
    have hsg := RootFieldNumerics.Levi.sum_gap_mul (fun x => mu x.1 x.2)
      (fun r => Real.log (((T.M B c).x (scale s) r).h ((R.tie B c).Re.R.lift x y)))
    simp only [RootModel.weight, Fintype.sum_option, RootModel.coef, RootModel.line, PB.gapS,
      Option.elim, mul_neg, Finset.sum_neg_distrib, neg_mul, hsg]
    rw [hk]
end
end
end
