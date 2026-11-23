module

public import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPthPowerScaleThinShellStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CosetRepresentativeTraceFixedProperties
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
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.RingTheory.Valuation.Integers
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.CosetRepresentativeTraceFixedPropertiesStatement

section

@[expose] public section

open GlobalTheory.AlmostEt
open scoped NNReal

theorem _root_.GlobalTheory.T.cosetRepresentativeTrace_fixed_properties : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G] [MulSemiringAction G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ (N : Subgroup G) [Fintype (G ⧸ N)], ∀ z ∈ Fix L N, (∀ g : G, g • cosetTrace N z = cosetTrace N z) ∧ (v z ≤ 1 → v (cosetTrace N z) ≤ 1) ∧ ∀ e : L, (∀ g : G, g • e = e) → cosetTrace N (e * z) = e * cosetTrace N z := by
  first | exact @GlobalTheory.AlmostEt.cosetTrace_fixed_props | exact GlobalTheory.AlmostEt.cosetTrace_fixed_props | (intros; apply GlobalTheory.AlmostEt.cosetTrace_fixed_props <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationFrobeniusSumSubLeNatCastPrime

section

@[expose] public section

open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem frob_sum_sub_le (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ) (hp : p.Prime)
    (ι : Type) (s : Finset ι) (x : ι → L) (hx : ∀ i ∈ s, v (x i) ≤ 1) :
    v ((∑ i ∈ s, x i) ^ p - ∑ i ∈ s, x i ^ p) ≤ v (p : L) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [zero_pow hp.ne_zero]
  | insert a s ha ih =>
    have hxa : v (x a) ≤ 1 := hx a (Finset.mem_insert_self a s)
    have hxs : ∀ i ∈ s, v (x i) ≤ 1 := fun i hi => hx i (Finset.mem_insert_of_mem hi)
    have hS : v (∑ i ∈ s, x i) ≤ 1 := by
      have : (∑ i ∈ s, x i) ∈ v.integer :=
        Subring.sum_mem _ (fun i hi => (Valuation.mem_integer_iff v _).2 (hxs i hi))
      exact (Valuation.mem_integer_iff v _).1 this
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp
      (⟨x a, (Valuation.mem_integer_iff v _).2 hxa⟩ : v.integer)
      ⟨∑ i ∈ s, x i, (Valuation.mem_integer_iff v _).2 hS⟩
    have hr' : (x a + ∑ i ∈ s, x i) ^ p = x a ^ p + (∑ i ∈ s, x i) ^ p + (p : L) * (x a * (∑ i ∈ s, x i) * (r : L)) := by
      have := congrArg (fun z : v.integer => (z : L)) hr
      push_cast at this
      rw [this]; ring
    have hrle : v (x a * (∑ i ∈ s, x i) * (r : L)) ≤ 1 := by
      rw [Valuation.map_mul, Valuation.map_mul]
      have hr1 : v (r : L) ≤ 1 := (Valuation.mem_integer_iff v _).1 r.2
      calc v (x a) * v (∑ i ∈ s, x i) * v (r : L) ≤ 1 * 1 * 1 := by gcongr
        _ = 1 := by simp
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hr']
    have heq : x a ^ p + (∑ i ∈ s, x i) ^ p + (p : L) * (x a * (∑ i ∈ s, x i) * (r : L)) - (x a ^ p + ∑ i ∈ s, x i ^ p)
        = (p : L) * (x a * (∑ i ∈ s, x i) * (r : L)) + ((∑ i ∈ s, x i) ^ p - ∑ i ∈ s, x i ^ p) := by ring
    rw [heq]
    refine (Valuation.map_add v _ _).trans (max_le ?_ (ih hxs))
    rw [Valuation.map_mul]
    calc v (p : L) * v (x a * (∑ i ∈ s, x i) * (r : L)) ≤ v (p : L) * 1 := by gcongr
      _ = v (p : L) := mul_one _

theorem frob_sum_sub_le' : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime →
    ∀ (ι : Type) (s : Finset ι) (x : ι → L), (∀ i ∈ s, v (x i) ≤ 1) →
      v ((∑ i ∈ s, x i) ^ p - ∑ i ∈ s, x i ^ p) ≤ v (p : L) :=
  fun L _ v p hp ι s x hx => frob_sum_sub_le L v p hp ι s x hx

end GlobalTheory.AlmostEt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationFrobeniusSumSubLeNatCastPrimeStatement

section

@[expose] public section

open GlobalTheory.AlmostEt
open scoped NNReal

theorem _root_.GlobalTheory.T.valuation_frobenius_sum_sub_le_natCast_prime : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → ∀ (ι : Type) (s : Finset ι) (x : ι → L), (∀ i ∈ s, v (x i) ≤ 1) → v ((∑ i ∈ s, x i) ^ p - ∑ i ∈ s, x i ^ p) ≤ v (p : L) := by
  first | exact @GlobalTheory.AlmostEt.frob_sum_sub_le' | exact GlobalTheory.AlmostEt.frob_sum_sub_le' | (intros; apply GlobalTheory.AlmostEt.frob_sum_sub_le' <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowMulApproxPowOfAlmostEtaleSeparatingFamily

section

@[expose] public section

open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem cpow_mul_approx_pow_of_isSep :
    ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → ∀ (G : Type) [Group G] [MulSemiringAction G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ (N : Subgroup G) [Fintype (G ⧸ N)] (θ : ℝ≥0), θ ≤ 1 → (∀ u ∈ Fix L (⊤ : Subgroup G), ∃ w ∈ Fix L (⊤ : Subgroup G), v (u - w ^ p) ≤ θ * v u) → ∀ (n : ℕ) (a b : Fin n → L) (c : L), IsSep v N a b c → ∀ x ∈ Fix L N, v x ≤ 1 → ∃ w ∈ Fix L N, v (c ^ p * x - w ^ p) ≤ max θ (v (p : L)) := by
  intro L _ v p hp G _ _ hv N _ θ hθ hroot n a b c hs x hx hx1
  have frob := GlobalTheory.T.valuation_frobenius_sum_sub_le_natCast_prime L v p hp
  have trfix := GlobalTheory.T.cosetRepresentativeTrace_fixed_properties L v G hv N
  have memN : ∀ y : L, y ∈ Fix L N ↔ ∀ g ∈ N, g • y = y := by
    intro y
    constructor
    · intro h g hg; exact h ⟨g, hg⟩
    · intro h g; exact h g g.2
  have memTop : ∀ y : L, y ∈ Fix L (⊤ : Subgroup G) ↔ ∀ g : G, g • y = y := by
    intro y
    constructor
    · intro h g; exact h ⟨g, Subgroup.mem_top g⟩
    · intro h g; exact h g
  set q₀ : G ⧸ N := ((1 : G) : G ⧸ N) with hq₀
  have hout : ∀ q : G ⧸ N, q.out ∈ N ↔ q = q₀ := fun q => by
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rw [hq₀, QuotientGroup.eq, mul_one, inv_mem_iff]
  set T : Fin n → L := fun i => cosetTrace N (b i ^ p * x) with hTdef
  have hbx : ∀ i, b i ^ p * x ∈ Fix L N := fun i =>
    Subfield.mul_mem _ (Subfield.pow_mem _ (hs.b_mem i) p) hx
  have hT : ∀ i, (∀ g : G, g • T i = T i) ∧ v (T i) ≤ 1 := fun i => by
    obtain ⟨h1, h2, -⟩ := trfix _ (hbx i)
    refine ⟨h1, h2 ?_⟩
    rw [map_mul, map_pow]
    exact mul_le_one' (pow_le_one' (hs.b_le i) p) hx1
  choose w hwmem hwle using fun i => hroot (T i) ((memTop _).2 (hT i).1)
  have hwθ : ∀ i, v (T i - w i ^ p) ≤ θ := fun i =>
    le_trans (hwle i) (mul_le_of_le_one_right zero_le' (hT i).2)
  have hw1 : ∀ i, v (w i) ≤ 1 := fun i => by
    have : v (w i ^ p) ≤ 1 := by
      have e : w i ^ p = T i - (T i - w i ^ p) := by ring
      rw [e]
      exact Valuation.map_sub_le v (hT i).2 (le_trans (hwθ i) hθ)
    rw [map_pow] at this
    exact (pow_le_one_iff_of_nonneg zero_le' hp.ne_zero).1 this
  set W : L := ∑ i, a i * w i with hWdef
  have hWmem : W ∈ Fix L N := by
    refine Subfield.sum_mem _ fun i _ => Subfield.mul_mem _ (hs.a_mem i) ?_
    exact (memN _).2 fun g _ => (memTop _).1 (hwmem i) g
  refine ⟨W, hWmem, ?_⟩

  have key1 : ∑ i, a i ^ p * T i = ∑ q : G ⧸ N, (∑ i, (a i * q.out • b i) ^ p) * q.out • x := by
    simp only [hTdef, cosetTrace, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul', smul_pow', mul_pow]
    ring
  have key2 : c ^ p * x = ∑ q : G ⧸ N, (∑ i, a i * q.out • b i) ^ p * q.out • x := by
    rw [Finset.sum_eq_single q₀]
    · rw [hs.sum_in _ ((hout q₀).2 rfl), (memN x).1 hx _ ((hout q₀).2 rfl)]
    · intro q _ hq
      rw [hs.sum_out _ (fun h => hq ((hout q).1 h)), zero_pow hp.ne_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have bound1 : v (c ^ p * x - ∑ i, a i ^ p * T i) ≤ v (p : L) := by
    rw [key1, key2, ← Finset.sum_sub_distrib]
    apply Valuation.map_sum_le
    intro q _
    rw [← sub_mul, map_mul]
    have h1 : v (q.out • x) ≤ 1 := by rw [hv]; exact hx1
    have h2 := frob (Fin n) Finset.univ (fun i => a i * q.out • b i)
      (fun i _ => by rw [map_mul, hv]; exact mul_le_one' (hs.a_le i) (hs.b_le i))
    calc _ ≤ v (p : L) * 1 := mul_le_mul' h2 h1
      _ = _ := mul_one _
  have bound2 : v (∑ i, a i ^ p * T i - ∑ i, a i ^ p * w i ^ p) ≤ θ := by
    rw [← Finset.sum_sub_distrib]
    apply Valuation.map_sum_le
    intro i _
    rw [← mul_sub, map_mul]
    calc _ ≤ 1 * θ := mul_le_mul' (by rw [map_pow]; exact pow_le_one' (hs.a_le i) p) (hwθ i)
      _ = θ := one_mul θ
  have bound3 : v (∑ i, a i ^ p * w i ^ p - W ^ p) ≤ v (p : L) := by
    have h := frob (Fin n) Finset.univ (fun i => a i * w i)
      (fun i _ => by rw [map_mul]; exact mul_le_one' (hs.a_le i) (hw1 i))
    simp only [mul_pow] at h
    rw [Valuation.map_sub_swap]
    exact h
  have e : c ^ p * x - W ^ p = (c ^ p * x - ∑ i, a i ^ p * T i)
      + (∑ i, a i ^ p * T i - ∑ i, a i ^ p * w i ^ p) + (∑ i, a i ^ p * w i ^ p - W ^ p) := by ring
  rw [e]
  refine Valuation.map_add_le v (Valuation.map_add_le v ?_ ?_) ?_
  · exact le_trans bound1 (le_max_right _ _)
  · exact le_trans bound2 (le_max_left _ _)
  · exact le_trans bound3 (le_max_right _ _)

end GlobalTheory.AlmostEt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowMulApproxPowOfAlmostEtaleSeparatingFamilyStatement

section

@[expose] public section

open GlobalTheory.AlmostEt
open scoped NNReal

theorem _root_.GlobalTheory.T.pow_mul_approx_pow_of_almostEtaleSeparatingFamily : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → ∀ (G : Type) [Group G] [MulSemiringAction G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ (N : Subgroup G) [Fintype (G ⧸ N)] (θ : ℝ≥0), θ ≤ 1 → (∀ u ∈ Fix L (⊤ : Subgroup G), ∃ w ∈ Fix L (⊤ : Subgroup G), v (u - w ^ p) ≤ θ * v u) → ∀ (n : ℕ) (a b : Fin n → L) (c : L), IsSep v N a b c → ∀ x ∈ Fix L N, v x ≤ 1 → ∃ w ∈ Fix L N, v (c ^ p * x - w ^ p) ≤ max θ (v (p : L)) := by
  first | exact @GlobalTheory.AlmostEt.cpow_mul_approx_pow_of_isSep | exact GlobalTheory.AlmostEt.cpow_mul_approx_pow_of_isSep | (intros; apply GlobalTheory.AlmostEt.cpow_mul_approx_pow_of_isSep <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ApproxPthRootFixedSubfieldOfAlmostEtale

section

@[expose] public section

open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem approxRoot_fix_of_almostSep : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ),
    p.Prime → 0 < v (p : L) → v (p : L) < 1 → ∀ (G : Type) [Group G] [MulSemiringAction G L],
    (∀ (g : G) (x : L), v (g • x) = v x) → ∀ N : Subgroup G, N.FiniteIndex → AlmostSep v N →
    ApproxRoot p v (Fix L (⊤ : Subgroup G)) → ApproxRoot p v (Fix L N) := by
  intro L _ v p hp hp0 hp1 G _ _ hinv N hN hsep hroot
  haveI : Finite (G ⧸ N) := Subgroup.finite_quotient_of_finiteIndex
  haveI : Fintype (G ⧸ N) := Fintype.ofFinite _
  obtain ⟨θ, hθ1, hθ⟩ := hroot
  set θ₀ : ℝ≥0 := max θ (v (p : L)) with hθ₀
  have hθ₀1 : θ₀ < 1 := max_lt hθ1 hp1
  obtain ⟨s, hs0, hs1⟩ := exists_between hθ₀1
  set r : ℝ≥0 := s ^ (((p + 1 : ℕ) : ℝ)⁻¹) with hr
  have hrpow : r ^ (p + 1) = s := NNReal.rpow_inv_natCast_pow s (by omega)
  have hr1 : r < 1 := NNReal.rpow_lt_one hs1 (by positivity)
  have hrs : θ₀ < r ^ (p + 1) := hrpow ▸ hs0
  have hrpos : 0 < r ^ (p + 1) := lt_of_le_of_lt bot_le hrs
  obtain ⟨n, a, b, c, hc, hrc⟩ := hsep r hr1
  refine ⟨θ₀ / r ^ (p + 1), (div_lt_one hrpos).2 hrs, ?_⟩
  intro x hx
  by_cases hx0 : x = 0
  · refine ⟨0, zero_mem _, ?_⟩
    simp [hx0, hp.ne_zero]
  obtain ⟨d, hdF, hd0, hdr, hd1⟩ :=
    GlobalTheory.T.exists_pth_power_scale_thin_shell L v p hp _ ⟨θ, hθ1, hθ⟩ hp0 hp1 r hr1 x hx0
  have hdN : d ∈ Fix L N := fun σ => hdF ⟨σ.1, Subgroup.mem_top _⟩
  have hx'N : x * d ^ p ∈ Fix L N := mul_mem hx (pow_mem hdN p)
  obtain ⟨w, hwN, hw⟩ :=
    GlobalTheory.T.pow_mul_approx_pow_of_almostEtaleSeparatingFamily L v p hp G hinv N θ hθ1.le hθ n a b c hc (x * d ^ p) hx'N hd1
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, map_zero] at hrc
    exact (not_lt.2 (bot_le : (⊥ : ℝ≥0) ≤ r)) hrc
  refine ⟨w / (c * d), div_mem hwN (mul_mem hc.c_mem hdN), ?_⟩
  have key : x - (w / (c * d)) ^ p = (c ^ p * (x * d ^ p) - w ^ p) / (c ^ p * d ^ p) := by
    have hD0 : c ^ p * d ^ p ≠ 0 := mul_ne_zero (pow_ne_zero _ hc0) (pow_ne_zero _ hd0)
    rw [eq_div_iff hD0, div_pow, mul_pow, sub_mul, div_mul_cancel₀ _ (mul_ne_zero (pow_ne_zero _ hc0) (pow_ne_zero _ hd0))]
    ring
  have hD : 0 < v (c ^ p * d ^ p) := by
    rw [Valuation.pos_iff]
    exact mul_ne_zero (pow_ne_zero _ hc0) (pow_ne_zero _ hd0)
  rw [key, map_div₀, div_le_iff₀ hD]
  have hvx : v (x * d ^ p) = v x * v d ^ p := by rw [map_mul, map_pow]
  have hbig : r ^ (p + 1) ≤ v c ^ p * (v x * v d ^ p) := by
    rw [pow_succ, ← hvx]
    exact mul_le_mul' (pow_le_pow_left₀ bot_le hrc.le p) hdr.le
  calc v (c ^ p * (x * d ^ p) - w ^ p) ≤ θ₀ := hw
    _ = θ₀ / r ^ (p + 1) * r ^ (p + 1) := (div_mul_cancel₀ _ hrpos.ne').symm
    _ ≤ θ₀ / r ^ (p + 1) * (v c ^ p * (v x * v d ^ p)) := by gcongr
    _ = θ₀ / r ^ (p + 1) * v x * v (c ^ p * d ^ p) := by
      rw [map_mul, map_pow, map_pow]; ring

end GlobalTheory.AlmostEt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ApproxPthRootFixedSubfieldOfAlmostEtaleStatement

section

@[expose] public section

open GlobalTheory.AlmostEt
open scoped NNReal

theorem _root_.GlobalTheory.T.approxPthRoot_fixedSubfield_of_almostEtale : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → 0 < v (p : L) → v (p : L) < 1 → ∀ (G : Type) [Group G] [MulSemiringAction G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ N : Subgroup G, N.FiniteIndex → AlmostSep v N → ApproxRoot p v (Fix L (⊤ : Subgroup G)) → ApproxRoot p v (Fix L N) := by
  first | exact @GlobalTheory.AlmostEt.approxRoot_fix_of_almostSep | exact GlobalTheory.AlmostEt.approxRoot_fix_of_almostSep | (intros; apply GlobalTheory.AlmostEt.approxRoot_fix_of_almostSep <;> assumption)
end
end
