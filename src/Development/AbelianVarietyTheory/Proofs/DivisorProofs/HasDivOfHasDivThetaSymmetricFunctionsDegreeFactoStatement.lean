module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
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
public import Mathlib.RingTheory.Valuation.LocalSubring
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.LocalRing.LocalSubring
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.Valuation.LocalSubring
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEsymmPowDivMemOfIsLocalRing

section

@[expose] public section

namespace GlobalTheory

theorem exists_esymm_pow_div_mem_of_isLocalRing : ∀ (K : Type) [Field K] (O : Subring K) [IsLocalRing O] (A : Type) [Fintype A] (x : A → K) (D k : ℕ) (c : K), 1 ≤ D → 1 ≤ k → k ∣ D → c ≠ 0 → (Finset.univ.val.map x).esymm k ^ (D / k) = c → (∀ a, x a ^ D / c ∈ O) → ∃ a, x a ≠ 0 ∧ c / x a ^ D ∈ O := by
  intro K _ O _ A _ x D k c hD hk hkD hc hce hO
  obtain ⟨V, hle, hloc⟩ := (LocalSubring.mk O).exists_le_valuationSubring
  have hkD' : 0 < D / k := Nat.div_pos (Nat.le_of_dvd (by omega) hkD) (by omega)
  have hes : (Finset.univ.val.map x).esymm k = ∑ t ∈ (Finset.univ : Finset A).powersetCard k, ∏ b ∈ t, x b :=
    Finset.esymm_map_val x _ k
  rcases isEmpty_or_nonempty A with hA | hA
  · exfalso
    apply hc
    rw [← hce, hes, Finset.powersetCard_eq_empty.2 (by simp; omega), Finset.sum_empty, zero_pow hkD'.ne']
  obtain ⟨a, -, ha⟩ := Finset.exists_max_image (Finset.univ : Finset A) (fun b => V.valuation (x b))
    Finset.univ_nonempty
  have hvc : V.valuation c ≠ 0 := by simpa using hc
  have h1 : V.valuation (x a) ^ D ≤ V.valuation c := by
    have := (V.valuation_le_one_iff _).2 (hle (hO a))
    rw [map_div₀, map_pow] at this
    exact (div_le_one₀ (zero_lt_iff.2 hvc)).1 this
  have h2 : V.valuation c ≤ V.valuation (x a) ^ D := by
    rw [← hce, map_pow, hes]
    have hb : V.valuation (∑ t ∈ (Finset.univ : Finset A).powersetCard k, ∏ b ∈ t, x b) ≤ V.valuation (x a) ^ k := by
      refine Valuation.map_sum_le _ (fun t ht => ?_)
      rw [map_prod]
      have hcard := (Finset.mem_powersetCard.1 ht).2
      rw [← hcard]
      exact Finset.prod_le_pow_card _ _ _ (fun b _ => ha b (Finset.mem_univ b))
    calc _ ≤ (V.valuation (x a) ^ k) ^ (D / k) := pow_le_pow_left₀ zero_le' hb _
      _ = V.valuation (x a) ^ D := by rw [← pow_mul, Nat.mul_div_cancel' hkD]
  have heq : V.valuation (x a) ^ D = V.valuation c := le_antisymm h1 h2
  have hxa : x a ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_pow (by omega)] at heq
    exact hvc heq.symm
  refine ⟨a, hxa, ?_⟩
  let y : O := ⟨x a ^ D / c, hO a⟩
  have hyV : IsUnit (Subring.inclusion hle y) := by
    refine (V.valuation_eq_one_iff ⟨x a ^ D / c, hle (hO a)⟩).2 ?_
    show V.valuation (x a ^ D / c) = 1
    rw [map_div₀, map_pow, heq, div_self hvc]
  have hy : IsUnit y := hloc.map_nonunit _ hyV
  obtain ⟨u, hu⟩ := hy
  have : ((u⁻¹ : Oˣ) : O) = c / x a ^ D := by
    have h3 : ((u : O) : K) * (((u⁻¹ : Oˣ) : O) : K) = 1 := by
      rw [← Subring.coe_mul, Units.mul_inv, Subring.coe_one]
    rw [hu] at h3
    have h4 : (x a ^ D / c) * (((u⁻¹ : Oˣ) : O) : K) = 1 := h3
    show (((u⁻¹ : Oˣ) : O) : K) = c / x a ^ D
    rw [eq_inv_of_mul_eq_one_right h4, inv_div]
  rw [← this]
  exact ((u⁻¹ : Oˣ) : O).2

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowDivMemOfEsymmPowDivMem

section

@[expose] public section

open Polynomial

namespace GlobalTheory

theorem pow_div_mem_of_esymm_pow_div_mem (K : Type) [Field K] (V : ValuationSubring K)
    (A : Type) [Fintype A] (x : A → K) (D : ℕ) (c : K) (hc : c ≠ 0)
    (h : ∀ k : ℕ, 1 ≤ k → k ≤ Fintype.card A →
      k ∣ D ∧ (Finset.univ.val.map x).esymm k ^ (D / k) / c ∈ V) (a : A) :
    x a ^ D / c ∈ V := by
  classical
  set v := V.valuation with hv
  set s : Multiset K := Finset.univ.val.map x with hs
  have hcard : Multiset.card s = Fintype.card A := by simp [s, Finset.card_univ]
  have hn : 1 ≤ Multiset.card s := hcard ▸ Fintype.card_pos_iff.mpr ⟨a⟩
  have hvc : v c ≠ 0 := (Valuation.ne_zero_iff v).mpr hc
  have mem_iff : ∀ y : K, y / c ∈ V ↔ v y ≤ v c := by
    intro y
    rw [← V.valuation_le_one_iff, ← hv, map_div₀, div_le_one₀ (zero_lt_iff.mpr hvc)]
  rw [mem_iff]
  by_contra hlt
  push_neg at hlt
  rw [Valuation.map_pow] at hlt
  have key : ∀ k, 1 ≤ k → k ≤ Multiset.card s → v (s.esymm k) < v (x a) ^ k := by
    intro k hk1 hkn
    obtain ⟨hkD, hmem⟩ := h k hk1 (hcard ▸ hkn)
    rw [mem_iff, Valuation.map_pow] at hmem
    by_contra hge
    push_neg at hge
    have hp : (v (x a) ^ k) ^ (D / k) ≤ v (s.esymm k) ^ (D / k) := pow_le_pow_left₀ zero_le' hge _
    rw [← pow_mul, Nat.mul_div_cancel' hkD] at hp
    exact absurd (hp.trans hmem) (not_le.mpr hlt)
  have hpos : 0 < v (x a) := by
    have := key 1 le_rfl hn
    rw [pow_one] at this
    exact lt_of_le_of_lt zero_le' this
  have h0 : (s.map fun t => X - C t).prod.eval (x a) = 0 := by
    rw [Polynomial.eval_multiset_prod, Multiset.prod_eq_zero_iff]
    simp only [Multiset.map_map, Function.comp_def, eval_sub, eval_X, eval_C]
    exact Multiset.mem_map.mpr ⟨x a, by simp [s], sub_self _⟩
  rw [Multiset.prod_X_sub_X_eq_sum_esymm, Polynomial.eval_finsetSum, Finset.sum_range_succ'] at h0
  simp only [eval_mul, eval_pow, eval_neg, eval_one, eval_C, eval_X, pow_zero, one_mul,
    Nat.sub_zero] at h0
  have he0 : s.esymm 0 = 1 := by simp [Multiset.esymm, Multiset.powersetCard_zero_left]
  rw [he0, one_mul, ← eq_neg_iff_add_eq_zero] at h0
  have hlt2 : v (∑ j ∈ Finset.range (Multiset.card s),
      (-1) ^ (j + 1) * (s.esymm (j + 1) * x a ^ (Multiset.card s - (j + 1)))) < v (x a) ^ Multiset.card s := by
    apply Valuation.map_sum_lt _ (pow_ne_zero _ hpos.ne')
    intro j hj
    have hj' : j + 1 ≤ Multiset.card s := Finset.mem_range.mp hj
    rw [map_mul, map_mul, map_pow, map_pow, Valuation.map_neg, map_one, one_pow, one_mul]
    calc v (s.esymm (j + 1)) * v (x a) ^ (Multiset.card s - (j + 1))
        < v (x a) ^ (j + 1) * v (x a) ^ (Multiset.card s - (j + 1)) :=
          mul_lt_mul_of_pos_right (key (j + 1) (Nat.succ_le_succ (Nat.zero_le _)) hj') (pow_pos hpos _)
      _ = v (x a) ^ Multiset.card s := by rw [← pow_add, Nat.add_sub_cancel' hj']
  rw [h0, Valuation.map_neg, map_pow] at hlt2
  exact lt_irrefl _ hlt2

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDivOfHasDivThetaSymmetricFunctionsDegreeFacto

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem hasDiv_of_hasDiv_symTup : ∀ (k Ω : Type) [CommRing k] [Field Ω] [Algebra k Ω] (M : RatModel k Ω) (N : ℕ)
    (c : Fin N → Ω), Geo.Tor.IsNormalScheme M.Z → M.HasDiv (symTup c) → M.HasDiv c := by
  intro k Ω _ _ _ M N c hn hd z
  obtain ⟨j, he, hdiv⟩ := hd z
  haveI := RatModel.isIntegrallyClosed_O hn z
  set D := N.factorial with hD
  set e := symTup c j with he'
  have hD1 : 1 ≤ D := Nat.factorial_pos N

  haveI : IsFractionRing (M.O z).toSubring Ω := inferInstanceAs (IsFractionRing (M.O z) Ω)
  haveI : IsIntegrallyClosed (M.O z).toSubring := inferInstanceAs (IsIntegrallyClosed (M.O z))
  haveI hcl : IsIntegrallyClosedIn (M.O z).toSubring Ω :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn Ω).1 inferInstance
  have h1 : ∀ a, c a ^ D / e ∈ M.O z := by
    intro a
    have hmem : c a ^ D / e ∈ ⨅ V : {V : ValuationSubring Ω // (M.O z).toSubring ≤ V.toSubring}, V.1.toSubring := by
      refine Subring.mem_iInf.2 fun V => ?_
      refine pow_div_mem_of_esymm_pow_div_mem Ω V.1 (Fin N) c D e he (fun i hi1 hi2 => ?_) a
      simp only [Fintype.card_fin] at hi2
      refine ⟨Nat.dvd_factorial hi1 hi2, V.2 ?_⟩
      have := hdiv ⟨i - 1, by omega⟩
      simp only [symTup, Nat.sub_add_cancel hi1] at this
      exact this
    rw [← Subring.eq_iInf_of_isIntegrallyClosedIn] at hmem
    exact hmem
  haveI : IsLocalRing (M.O z).toSubring := inferInstanceAs (IsLocalRing (M.O z))
  obtain ⟨a, ha, hea⟩ := exists_esymm_pow_div_mem_of_isLocalRing Ω (M.O z).toSubring (Fin N) c D ((j : ℕ) + 1) e hD1
    (by omega) (Nat.dvd_factorial (by omega) (by omega)) he rfl h1
  refine ⟨a, ha, fun b => ?_⟩
  have hpow : (c b / c a) ^ D ∈ M.O z := by
    have : (c b / c a) ^ D = (c b ^ D / e) * (e / c a ^ D) := by
      rw [div_pow, div_mul_div_cancel₀ he]
    rw [this]
    exact mul_mem (h1 b) hea
  have hint : IsIntegral (M.O z) (c b / c a) :=
    IsIntegral.of_pow (by omega) (isIntegral_algebraMap (R := M.O z) (x := ⟨_, hpow⟩))
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  exact hy ▸ y.2

end GlobalTheory.UMin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDivOfHasDivThetaSymmetricFunctionsDegreeFactoStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.hasDiv_of_hasDiv_thetaSymmetricFunctionsDegreeFactorial : ∀ (k Ω : Type) [CommRing k] [Field Ω] [Algebra k Ω] (M : RatModel k Ω) (N : ℕ) (c : Fin N → Ω), Geo.Tor.IsNormalScheme M.Z → M.HasDiv (symTup c) → M.HasDiv c := by
  first | exact @GlobalTheory.UMin.hasDiv_of_hasDiv_symTup | exact GlobalTheory.UMin.hasDiv_of_hasDiv_symTup | (intros; apply GlobalTheory.UMin.hasDiv_of_hasDiv_symTup <;> assumption)
end
end
