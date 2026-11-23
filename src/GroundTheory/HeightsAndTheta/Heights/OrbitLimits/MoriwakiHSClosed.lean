module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRelSectionsLarge
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRelChartPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRelOneStep
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRelTorsionBound
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Polynomial.Basic
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRelTorsionBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSerreGraded

-- Source module: GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRelChartPoly

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace RelChartPoly

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]

theorem chartMonomial_mem (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (e : K → ℕ) :
    ∏ k, y ⟨k, c k⟩ ^ e k ∈ relSecM R y e := by
  classical
  have h := monomial_mem_relSecM R y (b := e) (fun q : Σ k, ι k => if q.2 = c q.1 then e q.1 else 0)
    (fun k => by simp)
  convert h using 1
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp [pow_ite]

theorem coord_mem (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (p : Σ k, ι k) [DecidableEq K] :
    y p ∈ relSecM R y (Pi.single p.1 1) := by
  have h := chartMonomial_mem R y (Function.update c p.1 p.2) (Pi.single p.1 1)
  convert h using 1
  rw [Finset.prod_eq_single p.1]
  · simp
  · intro k _ hk
    simp [hk]
  · simp

theorem generator_mem (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (p : Σ k, ι k) :
    y p / y ⟨p.1, c p.1⟩ * ∏ k, y ⟨k, c k⟩ ∈ relSecM R y (fun _ => 1) := by
  classical
  by_cases h0 : y ⟨p.1, c p.1⟩ = 0
  · simp [h0]
  have hW : ∏ k, y ⟨k, c k⟩ = (∏ k, y ⟨k, c k⟩ ^ (Pi.single p.1 (1 : ℕ) : K → ℕ) k) *
      ∏ k, y ⟨k, c k⟩ ^ (if k = p.1 then 0 else 1) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← pow_add]
    by_cases hk : k = p.1
    · subst hk; simp
    · simp [hk]
  have h1 : ∏ k, y ⟨k, c k⟩ ^ (Pi.single p.1 (1 : ℕ) : K → ℕ) k = y ⟨p.1, c p.1⟩ := by
    rw [Finset.prod_eq_single p.1]
    · simp
    · intro k _ hk
      simp [hk]
    · simp
  have hmem := mul_mem_relSecM R y (coord_mem R y c p)
    (chartMonomial_mem R y c (fun k => if k = p.1 then 0 else 1))
  have hb : (Pi.single p.1 1 + fun k => if k = p.1 then 0 else 1 : K → ℕ) = fun _ => 1 := by
    funext k
    by_cases hk : k = p.1
    · subst hk; simp
    · simp [hk]
  rw [hb] at hmem
  rw [hW, h1, ← mul_assoc, div_mul_cancel₀ _ h0]
  exact hmem

end RelChartPoly

theorem RelChartPoly.proof : RelChartPoly.Statement := by
  intro K _ ι _ Ω _ R y c σ hσ
  have hW : ∀ M : ℕ, (∏ k, y ⟨k, c k⟩) ^ M ∈ relSecM R y (fun _ => M) := by
    intro M
    rw [← Finset.prod_pow]
    exact RelChartPoly.chartMonomial_mem R y c (fun _ => M)
  have hmul : ∀ {a b : ℕ} {x x' : Ω}, x ∈ relSecM R y (fun _ => a) → x' ∈ relSecM R y (fun _ => b) →
      x * x' ∈ relSecM R y (fun _ => a + b) := fun hx hx' => mul_mem_relSecM R y hx hx'
  induction hσ using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    exact ⟨1, by simpa using RelChartPoly.generator_mem R y c p⟩
  | algebraMap r =>
    refine ⟨0, ?_⟩
    rw [pow_zero, mul_one, Algebra.algebraMap_eq_smul_one]
    refine Submodule.smul_mem _ r ?_
    simpa using hW 0
  | add x x' _ _ hx hx' =>
    obtain ⟨N, hN⟩ := hx
    obtain ⟨M, hM⟩ := hx'
    refine ⟨N + M, ?_⟩
    rw [add_mul]
    refine add_mem ?_ ?_
    · have := hmul hN (hW M)
      convert this using 1
      ring
    · have := hmul hM (hW N)
      rw [add_comm N M]
      convert this using 1
      ring
  | mul x x' _ _ hx hx' =>
    obtain ⟨N, hN⟩ := hx
    obtain ⟨M, hM⟩ := hx'
    refine ⟨N + M, ?_⟩
    have := hmul hN hM
    convert this using 1
    ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRelOneStep

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace RelOneStep

theorem chart_monomial_mem {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]
    (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (b : K → ℕ) (c : ∀ k, ι k) :
    ∏ k, y ⟨k, c k⟩ ^ b k ∈ relSecM R y b := by
  classical
  let μ : (Σ k, ι k) → ℕ := fun p => if p.2 = c p.1 then b p.1 else 0
  have hμ : ∀ k, ∑ i, μ ⟨k, i⟩ = b k := by
    intro k
    simp [μ]
  have h := monomial_mem_relSecM R y μ hμ
  have heq : ∏ p, y p ^ μ p = ∏ k, y ⟨k, c k⟩ ^ b k := by
    rw [← Finset.univ_sigma_univ, Finset.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [μ]
    rw [Finset.prod_congr rfl fun i _ => (show y ⟨k, i⟩ ^ (if i = c k then b k else 0) =
      if i = c k then y ⟨k, i⟩ ^ b k else 1 by split_ifs <;> simp)]
    simp
  rwa [heq] at h

end RelOneStep

theorem RelOneStep.proof (hC : RelChartPoly.Statement) (hT : RelTorsionBound.Statement) : RelOneStep.Statement := by
  intro K _ _ ι _ Ω _ R hR y c0 hc0
  choose n hn using fun k0 : K => hT K ι Ω R hR y c0 hc0 k0
  refine ⟨Finset.univ.sup n, fun b hb k0 t ht hxt => ?_⟩
  have hbk : ∀ k, n k0 ≤ b k := fun k => le_trans (Finset.le_sup (Finset.mem_univ k0)) (hb k)
  obtain ⟨g', hg', hfg⟩ := hn k0 b hbk (y ⟨k0, c0 k0⟩ * t) hxt (by
    intro c hc
    obtain ⟨N, hN⟩ := hC K ι Ω R y c _ (ht c hc)
    refine ⟨N, t * (∏ k, y ⟨k, c k⟩) ^ N, ?_, by ring⟩
    have hm := mul_mem_relSecM R y hN (RelOneStep.chart_monomial_mem R y b c)
    have hone : (∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * (b k : ℤ)))) * ∏ k, y ⟨k, c k⟩ ^ b k = 1 := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun k _ => ?_
      rw [← zpow_natCast, ← zpow_add₀ (hc k)]
      simp
    have heq : t * (∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * (b k : ℤ)))) * (∏ k, y ⟨k, c k⟩) ^ N *
        ∏ k, y ⟨k, c k⟩ ^ b k = t * (∏ k, y ⟨k, c k⟩) ^ N := by
      linear_combination (t * (∏ k, y ⟨k, c k⟩) ^ N) * hone
    rw [heq, add_comm] at hm
    exact hm)
  have hx : y ⟨k0, c0 k0⟩ ≠ 0 := hc0 k0
  rwa [mul_left_cancel₀ hx hfg]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRelSectionsLarge

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace RelSectionsLarge

theorem chartMonomial_mem_relSecM {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (c0 : ∀ k, ι k) (b : K → ℕ) :
    ∏ k, y ⟨k, c0 k⟩ ^ b k ∈ relSecM R y b := by
  classical
  have h := monomial_mem_relSecM R y (b := b) (fun p => if p.2 = c0 p.1 then b p.1 else 0)
    (fun k => by simp)
  convert h using 1
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finset.prod_eq_single (c0 k) (fun i _ hi => by simp [hi]) (by simp)]
  simp

theorem descend {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (c0 : ∀ k, ι k) (n₁ : ℕ)
    (hstep : ∀ b : K → ℕ, (∀ k, n₁ ≤ b k) → ∀ k0 : K,
      ∀ t ∈ relChartLat R y (fun k => (b k : ℤ)) 1, y ⟨k0, c0 k0⟩ * t ∈ relSecM R y (b + Pi.single k0 1) →
        t ∈ relSecM R y b) :
    ∀ (m : ℕ) (e : K → ℕ), ∑ k, e k = m → ∀ b : K → ℕ, (∀ k, n₁ ≤ b k) →
      ∀ s ∈ relChartLat R y (fun k => (b k : ℤ)) 1,
        s * ∏ k, y ⟨k, c0 k⟩ ^ e k ∈ relSecM R y (b + e) → s ∈ relSecM R y b := by
  intro m
  induction m with
  | zero =>
    intro e he b _ s _ hs
    have h0 : e = 0 := funext fun k => by
      simpa using (Finset.sum_eq_zero_iff.mp he) k (Finset.mem_univ k)
    subst h0
    simpa using hs
  | succ m ih =>
    intro e he b hb s hsL hs
    obtain ⟨k0, hk0⟩ : ∃ k0, 0 < e k0 := by
      by_contra hcon
      simp only [not_exists, not_lt] at hcon
      have : ∑ k, e k = 0 := Finset.sum_eq_zero fun k _ => Nat.le_zero.mp (hcon k)
      omega
    set e' : K → ℕ := e - Pi.single k0 1 with he'
    have hee : e = e' + Pi.single k0 1 := by
      funext k
      simp only [he', Pi.add_apply, Pi.sub_apply]
      by_cases hk : k = k0
      · subst hk; simp; omega
      · simp [hk]
    have hsum : ∑ k, e' k = m := by
      have : ∑ k, e k = ∑ k, e' k + 1 := by
        rw [hee]; simp only [Pi.add_apply]; rw [Finset.sum_add_distrib]; simp
      omega
    refine ih e' hsum b hb s hsL ?_
    have htL : s * ∏ k, y ⟨k, c0 k⟩ ^ e' k ∈ relChartLat R y (fun k => ((b + e') k : ℤ)) 1 :=
      mul_prod_mem_relChartLat R y (a := fun k => (b k : ℤ)) (a' := fun k => ((b + e') k : ℤ)) (n := 1) e' c0
        (fun k => by simp only [Pi.add_apply]; push_cast; ring) hsL
    have hb' : ∀ k, n₁ ≤ (b + e') k := fun k => le_trans (hb k) (Nat.le_add_right _ _)
    refine hstep (b + e') hb' k0 _ htL ?_
    have hprod : y ⟨k0, c0 k0⟩ * (s * ∏ k, y ⟨k, c0 k⟩ ^ e' k) = s * ∏ k, y ⟨k, c0 k⟩ ^ e k := by
      rw [hee]
      have h1 : ∏ k, y ⟨k, c0 k⟩ ^ (Pi.single k0 1 : K → ℕ) k = y ⟨k0, c0 k0⟩ := by
        rw [Fintype.prod_eq_single k0 (fun k hk => by simp [hk])]
        simp
      simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib, h1]
      ring
    rw [hprod, add_assoc, ← hee]
    exact hs

theorem proof (hC : RelChartPoly.Statement) (hO : RelOneStep.Statement) : RelSectionsLarge.Statement := by
  classical
  intro K _ ι _ Ω _ R hR y hy
  choose c0 hc0 using hy
  obtain ⟨n₁, hn₁⟩ := hO K ι Ω R hR y c0 hc0
  refine ⟨n₁, fun b hb s hs => ?_⟩
  obtain ⟨N, hN⟩ := hC K ι Ω R y c0 _ (hs c0 hc0)
  have hform := mul_mem_relSecM R y hN (chartMonomial_mem_relSecM R y c0 b)
  refine descend R y c0 n₁ hn₁ (∑ _k : K, N) (fun _ => N) rfl b hb s hs ?_
  rw [add_comm]
  convert hform using 1
  have hcancel : (∏ k, y ⟨k, c0 k⟩ ^ (-(((1 : ℕ) : ℤ) * (b k : ℤ)))) * ∏ k, y ⟨k, c0 k⟩ ^ b k = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun k _ => ?_
    rw [Nat.cast_one, one_mul, zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ (hc0 k))]
  rw [← Finset.prod_pow]
  linear_combination (-(s * ∏ k, y ⟨k, c0 k⟩ ^ N)) * hcancel

end RelSectionsLarge

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.OrbitLimits.MoriwakiHSClosed

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel

theorem RelSectionsLarge.full : RelSectionsLarge.Statement :=
  RelSectionsLarge.proof RelChartPoly.proof (RelOneStep.proof RelChartPoly.proof RelTorsionBound.proof)

end GroundTheory.Heights₂.Heights.Targets
end
end
