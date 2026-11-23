module

public import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ApproxPthRootFixedSubfieldOfAlmostEtaleStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLagrangeResolventOfPGroupFaithfulStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNormalSubgroupNotMovesUniformBoundStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FixedFieldAlmostEtaleOfMovesIntegersStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPthPowerScaleThinShellStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerGeneratorApproxCriticalRadiusStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationSubOnePowEqPrimeStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.RingTheory.Valuation.Integers
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MovesIntegersAlmostUnitOfCoprimeOrderStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerAutomorphismMovesIntegersAlmostUnit

section

@[expose] public section

open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem kummer_moves : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime →
    ∀ F : Subfield L, ApproxRoot p v F → 0 < v (p : L) → v (p : L) < 1 →
    ∀ (G : Type) [Group G] [MulSemiringAction G L] (σ : G), (∀ x ∈ F, σ • x = x) →
    ∀ ζ α : L, IsPrimitiveRoot ζ p → α ≠ 0 → α ^ p ∈ F → σ • α = ζ * α → Moves v ⊤ σ := by
  intro L _ v p hp F hF hp0 hp1 G _ _ σ hσ ζ α hζ hα hαp hσα r hr
  obtain ⟨t, hrt, ht1⟩ := exists_between hr
  have ht0 : 0 < t := lt_of_le_of_lt (zero_le') hrt
  set s : ℝ≥0 := t⁻¹ with hs_def
  have hs1 : 1 < s := by rw [hs_def]; exact one_lt_inv₀ ht0 |>.mpr ht1
  have hs0 : 0 < s := lt_trans zero_lt_one hs1
  have hrs : r * s < 1 := by
    rw [hs_def, ← div_eq_mul_inv]; exact (div_lt_one ht0).mpr hrt
  obtain ⟨y, hyF, hy⟩ := GlobalTheory.T.kummer_generator_approx_critical_radius L v p hp F hF hp1 α hαp hp0 s hs1
  have hz := GlobalTheory.T.valuation_primitiveRoot_sub_one_pow_pred_eq L v p hp ζ hζ
  have hp2 : 2 ≤ p := hp.two_le
  have hpn : p - 1 ≠ 0 := by omega
  set β := α - y with hβ_def
  have hσβ : σ • β - β = (ζ - 1) * α := by
    rw [hβ_def, smul_sub, hσα, hσ y hyF]; ring
  have hζ1 : ζ ≠ 1 := hζ.ne_one hp.one_lt
  have hne : σ • β - β ≠ 0 := by
    rw [hσβ]; exact mul_ne_zero (sub_ne_zero.mpr hζ1) hα
  have hβ0 : β ≠ 0 := by
    intro h; apply hne; rw [h, smul_zero, sub_zero]

  have hvβ : v β ≤ s * v (σ • β - β) := by
    have h1 : v β ^ (p - 1) ≤ (s * v (σ • β - β)) ^ (p - 1) := by
      rw [hσβ, map_mul, mul_pow, mul_pow, hz]
      calc v β ^ (p - 1) ≤ s * v (p : L) * v α ^ (p - 1) := hy
        _ ≤ s ^ (p - 1) * v (p : L) * v α ^ (p - 1) := by
          gcongr
          exact le_self_pow₀ hs1.le hpn
        _ = s ^ (p - 1) * (v (p : L) * v α ^ (p - 1)) := by ring
    exact le_of_pow_le_pow_left₀ hpn (zero_le') h1
  obtain ⟨d, hdF, hd0, hdlo, hdhi⟩ := GlobalTheory.T.exists_pth_power_scale_thin_shell L v p hp F hF hp0 hp1 (r * s) hrs β hβ0
  refine ⟨β * d ^ p, Subfield.mem_top _, hdhi, ?_⟩
  have hσx : σ • (β * d ^ p) - β * d ^ p = d ^ p * (σ • β - β) := by
    rw [smul_mul', smul_pow', hσ d hdF]; ring
  rw [hσx]
  have hvx : v (β * d ^ p) ≤ s * v (d ^ p * (σ • β - β)) := by
    rw [map_mul, map_mul]
    calc v β * v (d ^ p) ≤ s * v (σ • β - β) * v (d ^ p) := by gcongr
      _ = s * (v (d ^ p) * v (σ • β - β)) := by ring
  have : r * s < s * v (d ^ p * (σ • β - β)) := lt_of_lt_of_le hdlo hvx
  rw [mul_comm] at this
  exact lt_of_mul_lt_mul_left this (zero_le')

end GlobalTheory.AlmostEt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerAutomorphismMovesIntegersAlmostUnitStatement

section

@[expose] public section

open GlobalTheory.AlmostEt
open scoped NNReal

theorem _root_.GlobalTheory.T.kummer_automorphism_moves_integers_almost_unit : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → ∀ F : Subfield L, ApproxRoot p v F → 0 < v (p : L) → v (p : L) < 1 → ∀ (G : Type) [Group G] [MulSemiringAction G L] (σ : G), (∀ x ∈ F, σ • x = x) → ∀ ζ α : L, IsPrimitiveRoot ζ p → α ≠ 0 → α ^ p ∈ F → σ • α = ζ * α → Moves v ⊤ σ := by
  first | exact @GlobalTheory.AlmostEt.kummer_moves | exact GlobalTheory.AlmostEt.kummer_moves | (intros; apply GlobalTheory.AlmostEt.kummer_moves <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.MovesIntegersAlmostUnitDistanceFixedSubfield

section

@[expose] public section

open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

open Polynomial

theorem moves_fix_of_moves : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G]
    [MulSemiringAction G L] [Finite G], (∀ (g : G) (x : L), v (g • x) = v x) →
    ∀ (N : Subgroup G) (i : ℝ≥0), i < 1 → (∀ τ ∈ N, ∀ x : L, v x ≤ 1 → v (τ • x - x) ≤ i) →
    ∀ σ : G, Moves v ⊤ σ → Moves v (Fix L N) σ := by
  intro L _ v G _ _ _ hinv N i hi hN σ hσ r hr
  classical
  by_contra hcon
  push_neg at hcon
  haveI := Fintype.ofFinite G
  set n := Fintype.card N with hn_def
  have hn : n ≠ 0 := Fintype.card_ne_zero
  set t : ℝ≥0 := max i (r ^ ((n : ℝ)⁻¹)) with ht_def
  have ht1 : t < 1 := max_lt hi (NNReal.rpow_lt_one hr (by positivity))
  have hrt : r ≤ t ^ n := by
    calc r = (r ^ ((n : ℝ)⁻¹)) ^ n := (NNReal.rpow_inv_natCast_pow r hn).symm
      _ ≤ t ^ n := pow_le_pow_left₀ zero_le (le_max_right _ _) n
  obtain ⟨x, -, hx1, hxt⟩ := hσ t ht1

  have hfac : ∀ τ : N, v (x - σ • ((τ : G) • x)) = v (σ • x - x) := by
    intro τ
    have h1 : v (σ • x - σ • ((τ : G) • x)) < v (x - σ • x) := by
      rw [← smul_sub, hinv, Valuation.map_sub_swap, Valuation.map_sub_swap v x]
      exact lt_of_le_of_lt (le_trans (hN τ τ.2 x hx1) (le_max_left _ _)) hxt
    have h2 : x - σ • ((τ : G) • x) = (x - σ • x) + (σ • x - σ • ((τ : G) • x)) := by ring
    rw [h2, Valuation.map_add_eq_of_lt_left v h1, Valuation.map_sub_swap]

  set P : L[X] := ∏ τ : N, (X - C ((τ : G) • x)) with hP_def
  have hint : ∀ τ : N, (τ : G) • x ∈ v.integer := fun τ => by
    rw [Valuation.mem_integer_iff, hinv]; exact hx1
  set Q : (v.integer)[X] := ∏ τ : N, (X - C (⟨(τ : G) • x, hint τ⟩ : v.integer)) with hQ_def
  have hPQ : P = Q.map (v.integer.subtype) := by
    simp [hP_def, hQ_def, Polynomial.map_prod]
  have hcint : ∀ k, v (P.coeff k) ≤ 1 := by
    intro k
    rw [hPQ, coeff_map]
    exact (Q.coeff k).2
  have hcfix : ∀ k, P.coeff k ∈ Fix L N := by
    intro k m
    have hmap : P.map (MulSemiringAction.toRingHom G L (m : G)) = P := by
      rw [hP_def, Polynomial.map_prod]
      simp only [Polynomial.map_sub, map_X, map_C, MulSemiringAction.toRingHom_apply, smul_smul]
      exact Fintype.prod_equiv (Equiv.mulLeft m) _ _ (fun τ => by simp)
    have := congrArg (fun p => p.coeff k) hmap
    have h' : (m : G) • P.coeff k = P.coeff k := by simpa [coeff_map] using this
    exact h'
  have hPx : P.eval x = 0 := by
    rw [hP_def, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ 1) (by simp)
  have hPσx : (P.map (MulSemiringAction.toRingHom G L σ)).eval x = ∏ τ : N, (x - σ • ((τ : G) • x)) := by
    simp [hP_def, Polynomial.map_prod, eval_prod]

  have hdiff : v ((P.map (MulSemiringAction.toRingHom G L σ) - P).eval x) ≤ r := by
    rw [eval_eq_sum, Polynomial.sum_def]
    apply Valuation.map_sum_le
    intro k _
    rw [map_mul, map_pow, coeff_sub, coeff_map, MulSemiringAction.toRingHom_apply]
    calc v (σ • P.coeff k - P.coeff k) * v x ^ k ≤ r * 1 :=
          mul_le_mul' (hcon _ (hcfix k) (hcint k)) (pow_le_one₀ zero_le hx1)
      _ = r := mul_one r
  rw [eval_sub, hPx, sub_zero, hPσx, map_prod] at hdiff
  simp only [hfac, Finset.prod_const, Finset.card_univ] at hdiff
  have := pow_lt_pow_left₀ hxt zero_le hn
  exact absurd (lt_of_le_of_lt (hdiff.trans hrt) this) (lt_irrefl _)

end GlobalTheory.AlmostEt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.MovesIntegersAlmostUnitDistanceFixedSubfieldStatement

section

@[expose] public section

open GlobalTheory.AlmostEt
open scoped NNReal

theorem _root_.GlobalTheory.T.movesIntegersAlmostUnitDistance_fixedSubfield : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G] [MulSemiringAction G L] [Finite G], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ (N : Subgroup G) (i : ℝ≥0), i < 1 → (∀ τ ∈ N, ∀ x : L, v x ≤ 1 → v (τ • x - x) ≤ i) → ∀ σ : G, Moves v ⊤ σ → Moves v (Fix L N) σ := by
  first | exact @GlobalTheory.AlmostEt.moves_fix_of_moves | exact GlobalTheory.AlmostEt.moves_fix_of_moves | (intros; apply GlobalTheory.AlmostEt.moves_fix_of_moves <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlmostPurityMovesIntegersOfNeOne

section

@[expose] public section

open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem moves_of_ne_one : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → 0 < v (p : L) → v (p : L) < 1 → ∀ (G : Type) [Group G] [MulSemiringAction G L] [Finite G] [FaithfulSMul G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ ζ : L, IsPrimitiveRoot ζ p → (∀ g : G, g • ζ = ζ) → ApproxRoot p v (Fix L (⊤ : Subgroup G)) → ∀ σ : G, σ ≠ 1 → Moves v ⊤ σ := by
  intro L _ v p hp hp0 hp1 G _ _ _ _ hinv ζ hζ hζfix hroot σ hσ
  obtain ⟨N, hNn, hNmem, i, hi, hNi⟩ := GlobalTheory.T.exists_normal_subgroup_not_moves_uniform_bound L v G hinv
  by_contra hmov
  have hσN : σ ∈ N := (hNmem σ).2 hmov
  have hfixN : ∀ τ ∈ N, ∀ x ∈ Fix L N, τ • x = x := fun τ hτ x hx => hx ⟨τ, hτ⟩
  have hdesc : ∀ τ : G, τ ∉ N → Moves v (Fix L N) τ := fun τ hτ =>
    GlobalTheory.T.movesIntegersAlmostUnitDistance_fixedSubfield L v G hinv N i hi hNi τ (by_contra fun h => hτ ((hNmem τ).2 h))
  have hsep : AlmostSep v N := GlobalTheory.T.fixedFieldAlmostEtale_of_moves_integers L v G hinv N hNn inferInstance hdesc
  have hF : ApproxRoot p v (Fix L N) := GlobalTheory.T.approxPthRoot_fixedSubfield_of_almostEtale L v p hp hp0 hp1 G hinv N inferInstance hsep hroot
  have hpg : IsPGroup p N := by
    intro τ
    set n := orderOf (τ : G) with hn
    have hn0 : n ≠ 0 := (orderOf_pos (τ : G)).ne'
    set k := n.factorization p
    refine ⟨k, ?_⟩
    have hcop : Nat.Coprime (n / p ^ k) p := (Nat.coprime_ordCompl hp hn0).symm
    have hτ' : ((τ : G) ^ (p ^ k)) ∈ N := N.pow_mem τ.2 _
    by_contra hne
    have hne' : (τ : G) ^ (p ^ k) ≠ 1 := by
      intro h; apply hne; ext; simpa using h
    have hl : ((τ : G) ^ (p ^ k)) ^ (n / p ^ k) = 1 := by
      rw [← pow_mul, Nat.mul_div_cancel' (Nat.ordProj_dvd n p), hn, pow_orderOf_eq_one]
    obtain ⟨y, hy⟩ : ∃ y : L, ((τ : G) ^ (p ^ k)) • y ≠ y := by
      by_contra h
      push_neg at h
      exact hne' (eq_of_smul_eq_smul (α := L) (fun y => by rw [h y, one_smul]))
    exact (hNmem _).1 hτ' (GlobalTheory.T.movesIntegersAlmostUnit_of_coprime_order L v p hp (Fix L N) hF hp0 hp1 G hinv _ (hfixN _ hτ') _ hcop hl ⟨y, hy⟩)
  haveI : Nontrivial N := ⟨⟨⟨σ, hσN⟩, 1, fun h => hσ (congrArg Subtype.val h)⟩⟩
  haveI : FaithfulSMul N L := ⟨fun {a b} h => Subtype.ext (eq_of_smul_eq_smul (α := L) h)⟩
  obtain ⟨σ₀, α, hα0, hσα, hαp⟩ := GlobalTheory.T.exists_lagrange_resolvent_of_pGroup_faithful L p hp N hpg ζ hζ (fun g => hζfix g)
  have hαF : α ^ p ∈ Fix L N := fun g => hαp g
  exact (hNmem _).1 σ₀.2 (GlobalTheory.T.kummer_automorphism_moves_integers_almost_unit L v p hp (Fix L N) hF hp0 hp1 G (σ₀ : G) (hfixN _ σ₀.2) ζ α hζ hα0 hαF hσα)

end GlobalTheory.AlmostEt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlmostPurityMovesIntegersOfNeOneStatement

section

@[expose] public section

open GlobalTheory.AlmostEt
open scoped NNReal

theorem _root_.GlobalTheory.T.almostPurity_moves_integers_of_ne_one : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → 0 < v (p : L) → v (p : L) < 1 → ∀ (G : Type) [Group G] [MulSemiringAction G L] [Finite G] [FaithfulSMul G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ ζ : L, IsPrimitiveRoot ζ p → (∀ g : G, g • ζ = ζ) → ApproxRoot p v (Fix L (⊤ : Subgroup G)) → ∀ σ : G, σ ≠ 1 → Moves v ⊤ σ := by
  first | exact @GlobalTheory.AlmostEt.moves_of_ne_one | exact GlobalTheory.AlmostEt.moves_of_ne_one | (intros; apply GlobalTheory.AlmostEt.moves_of_ne_one <;> assumption)
end
end
