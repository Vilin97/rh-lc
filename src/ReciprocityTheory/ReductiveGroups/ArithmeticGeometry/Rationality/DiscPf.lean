module

public import ReciprocityTheory.SemistableReduction.ComapInclusionIsLocalHom
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import ReciprocityTheory.SemistableReduction.ExistsTorusPointOneLeNormSum
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.DiscSt

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

def DiscStatement : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (K₀ : Subfield K),
    ReciprocityTheory.MultiplicativeHeights.ResidueFieldInfiniteOn (K₀ : Set K) →
    ∀ S : Set K, (∀ t ∈ S, 0 < ‖t‖ ∧ ‖t‖ < 1) →
    (∀ r : ℝ, 0 < r → r < 1 → ∀ ε > (0 : ℝ), ∃ t ∈ S, |‖t‖ - r| < ε) →
    ∀ (c : ℤ → K) (b : ℕ), (∀ n, n < -(b : ℤ) → c n = 0) →
      (∀ t ∈ S,
        Filter.Tendsto (fun n => ‖c n * t ^ n‖) Filter.cofinite (nhds 0) ∧
        ∀ τ ∈ K₀, ‖τ‖ = 1 → ‖∑' n, c n * (t * τ) ^ n‖ ≤ 1) →
      ∀ n, ‖c n‖ ≤ 1 ∧ (n < 0 → c n = 0)

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end
end

-- Source module: ReciprocityTheory.SemistableReduction.CauchyInequalityOnTorus

section

@[expose] public section

namespace ReciprocityTheory.MultiplicativeHeights

theorem cauchy_inequality_on_torus : CauchyTorusStatement := by
  intro K _ _ _ K₀ hK₀ n c hc hτ χ
  by_contra hχ
  push_neg at hχ
  have hev : ∀ᶠ ψ in Filter.cofinite, ‖c ψ‖ < 1 / 2 := hc.eventually (gt_mem_nhds (by norm_num))
  have hFfin : {ψ | ¬ ‖c ψ‖ < 1 / 2}.Finite := Filter.eventually_cofinite.1 hev
  set F := hFfin.toFinset with hFdef
  have hχF : χ ∈ F := by
    rw [Set.Finite.mem_toFinset]
    show ¬ ‖c χ‖ < 1 / 2
    linarith
  obtain ⟨χm, hχmF, hmax⟩ := F.exists_max_image (fun ψ => ‖c ψ‖) ⟨χ, hχF⟩
  have hgt : 1 < ‖c χm‖ := lt_of_lt_of_le hχ (hmax χ hχF)
  have hglob : ∀ ψ, ‖c ψ‖ ≤ ‖c χm‖ := by
    intro ψ
    by_cases hψ : ψ ∈ F
    · exact hmax ψ hψ
    · have h2 : ‖c ψ‖ < 1 / 2 := by
        rw [Set.Finite.mem_toFinset] at hψ
        simpa using hψ
      linarith
  set lam := c χm with hlam
  have hlam0 : lam ≠ 0 := by
    intro h
    rw [h, norm_zero] at hgt
    linarith
  set a : (Fin n → ℤ) → K := fun ψ => c ψ / lam with hadef
  have ha : ∀ ψ, ‖a ψ‖ ≤ 1 := by
    intro ψ
    simp only [hadef, norm_div]
    exact (div_le_one (norm_pos_iff.2 hlam0)).2 (hglob ψ)
  have ha0 : ‖a χm‖ = 1 := by
    simp only [hadef, norm_div]
    exact div_self (norm_ne_zero_iff.2 hlam0)
  obtain ⟨τ, hτu, hτ1⟩ := exists_torus_point_one_le_norm_sum K₀ hK₀ F a ha χm hχmF ha0
  have hprodnorm : ∀ ψ : Fin n → ℤ, ‖∏ i, τ i ^ ψ i‖ = 1 := by
    intro ψ
    rw [norm_prod]
    exact Finset.prod_eq_one fun i _ => by rw [norm_zpow, (hτu i).2, one_zpow]
  have hSF : ∑ ψ ∈ F, c ψ * ∏ i, τ i ^ ψ i = lam * ∑ ψ ∈ F, a ψ * ∏ i, τ i ^ ψ i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ψ _ => ?_
    simp only [hadef]
    field_simp
  have hSFn : ‖lam‖ ≤ ‖∑ ψ ∈ F, c ψ * ∏ i, τ i ^ ψ i‖ := by
    rw [hSF, norm_mul]
    calc ‖lam‖ = ‖lam‖ * 1 := (mul_one _).symm
      _ ≤ ‖lam‖ * ‖∑ ψ ∈ F, a ψ * ∏ i, τ i ^ ψ i‖ := mul_le_mul_of_nonneg_left hτ1 (norm_nonneg _)
  have hsum : Summable (fun ψ => c ψ * ∏ i, τ i ^ ψ i) := by
    apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [norm_mul, hprodnorm] using hc
  have hsplit := hsum.sum_add_tsum_compl (s := F)
  have htail : ‖∑' ψ : ↑((F : Set (Fin n → ℤ))ᶜ), c ψ * ∏ i, τ i ^ (ψ : Fin n → ℤ) i‖ ≤ 1 / 2 := by
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by norm_num) fun ψ => ?_
    rw [norm_mul, hprodnorm, mul_one]
    have hψ : (ψ : Fin n → ℤ) ∉ F := fun h => ψ.2 (Finset.mem_coe.2 h)
    rw [Set.Finite.mem_toFinset] at hψ
    simp only [Set.mem_setOf_eq, not_not] at hψ
    exact le_of_lt hψ
  have hne : ‖∑ ψ ∈ F, c ψ * ∏ i, τ i ^ ψ i‖ ≠
      ‖∑' ψ : ↑((F : Set (Fin n → ℤ))ᶜ), c ψ * ∏ i, τ i ^ (ψ : Fin n → ℤ) i‖ := by
    intro h
    linarith
  have htot := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
  rw [hsplit] at htot
  have h1 := hτ τ hτu
  unfold torusSum at h1
  rw [htot] at h1
  have h3 := le_max_left ‖∑ ψ ∈ F, c ψ * ∏ i, τ i ^ ψ i‖
    ‖∑' ψ : ↑((F : Set (Fin n → ℤ))ᶜ), c ψ * ∏ i, τ i ^ (ψ : Fin n → ℤ) i‖
  linarith

end ReciprocityTheory.MultiplicativeHeights
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.DiscPf

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

theorem disc_bound {K : Type} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (K₀ : Subfield K) (hres : ReciprocityTheory.MultiplicativeHeights.ResidueFieldInfiniteOn (K₀ : Set K)) (c : ℤ → K)
    (S : Set K)
    (hc : ∀ t ∈ S,
        Filter.Tendsto (fun n => ‖c n * t ^ n‖) Filter.cofinite (nhds 0) ∧
        ∀ τ ∈ K₀, ‖τ‖ = 1 → ‖∑' n, c n * (t * τ) ^ n‖ ≤ 1)
    (t : K) (htS : t ∈ S) (n : ℤ) : ‖c n‖ * ‖t‖ ^ n ≤ 1 := by
  obtain ⟨hlim, hbd⟩ := hc t htS
  let e := Equiv.funUnique (Fin 1) ℤ
  have key := ReciprocityTheory.MultiplicativeHeights.cauchy_inequality_on_torus K K₀ hres 1 (fun χ => c (χ 0) * t ^ (χ 0)) ?_ ?_ (fun _ => n)
  · simpa [norm_mul, norm_zpow] using key
  · exact (hlim.comp e.injective.tendsto_cofinite :)
  · intro τ hτ
    have h := hbd (τ 0) (hτ 0).1 (hτ 0).2
    unfold ReciprocityTheory.MultiplicativeHeights.torusSum
    have h2 : (fun χ : Fin 1 → ℤ => c (χ 0) * t ^ (χ 0) * ∏ i, τ i ^ χ i) =
        fun χ => (fun m : ℤ => c m * (t * τ 0) ^ m) (e χ) := by
      funext χ
      simp [e, Fin.prod_univ_one, mul_zpow, mul_assoc]
    rw [h2]
    convert h using 2
    exact e.tsum_eq (fun m : ℤ => c m * (t * τ 0) ^ m)

theorem disc_holds : DiscStatement := by
  intro K _ _ _ K₀ hres S hS hdense c b hb hc n
  have hbd : ∀ t ∈ S, ‖c n‖ * ‖t‖ ^ n ≤ 1 := fun t ht => disc_bound K₀ hres c S hc t ht n
  constructor
  · by_contra hlt
    push_neg at hlt
    have hcont : ContinuousAt (fun x : ℝ => ‖c n‖ * x ^ n) 1 :=
      continuousAt_const.mul (continuousAt_zpow₀ (1 : ℝ) n (Or.inl one_ne_zero))
    have hev : ∀ᶠ x in nhds (1 : ℝ), 1 < ‖c n‖ * x ^ n :=
      hcont.eventually (lt_mem_nhds (by simpa using hlt))
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
    set r : ℝ := max (1 / 2) (1 - ε / 2) with hr
    have hr0 : 0 < r := lt_max_of_lt_left (by norm_num)
    have hr1 : r < 1 := max_lt (by norm_num) (by linarith)
    obtain ⟨t, htS, ht⟩ :=
      hdense r hr0 hr1 (min (ε / 2) (1 - r)) (lt_min (by linarith) (by linarith))
    have h1 := hbd t htS
    have h2 := (hS t htS).2
    have hdist : dist ‖t‖ 1 < ε := by
      rw [Real.dist_eq, abs_sub_comm, abs_of_pos (by linarith : (0 : ℝ) < 1 - ‖t‖)]
      have h4 := (abs_lt.1 ht).1
      have h5 : min (ε / 2) (1 - r) ≤ ε / 2 := min_le_left _ _
      have h3 : 1 - ε / 2 ≤ r := le_max_right _ _
      linarith
    exact absurd h1 (not_le.2 (hball hdist))
  · intro hn
    by_contra hne
    have hq : 0 < ‖c n‖ := norm_pos_iff.2 hne
    have hm : 0 < -n := by omega
    have hcont : ContinuousAt (fun x : ℝ => x ^ (-n)) 0 :=
      continuousAt_zpow₀ (0 : ℝ) (-n) (Or.inr hm.le)
    have h0 : (fun x : ℝ => x ^ (-n)) 0 = 0 := zero_zpow _ hm.ne'
    have hev : ∀ᶠ x in nhds (0 : ℝ), x ^ (-n) < ‖c n‖ :=
      hcont.eventually (gt_mem_nhds (by rw [h0]; exact hq))
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
    set r : ℝ := min (1 / 2) (ε / 2) with hr
    have hr0 : 0 < r := lt_min (by norm_num) (by linarith)
    have hr1 : r < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    obtain ⟨t, htS, ht⟩ := hdense r hr0 hr1 r hr0
    have htpos := (hS t htS).1
    have hdist : dist ‖t‖ 0 < ε := by
      rw [Real.dist_eq, sub_zero, abs_of_pos htpos]
      have h4 := (abs_lt.1 ht).2
      have h5 : r ≤ ε / 2 := min_le_right _ _
      linarith
    have h6 := hball hdist
    have h1 := hbd t htS
    have h7 : ‖t‖ ^ n * ‖t‖ ^ (-n) = 1 := by
      rw [← zpow_add₀ htpos.ne', add_neg_cancel, zpow_zero]
    have h9 : ‖c n‖ ≤ ‖t‖ ^ (-n) := by
      have h10 := mul_le_mul_of_nonneg_right h1 (zpow_pos htpos (-n)).le
      rw [mul_assoc, h7, mul_one, one_mul] at h10
      exact h10
    linarith

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end
end
