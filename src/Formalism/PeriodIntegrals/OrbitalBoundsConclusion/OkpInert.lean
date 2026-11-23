module

public import Formalism.PeriodIntegrals.OkpInert
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertPrimeTeichmuller.CFrob
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertPrimeTeichmuller.NormLeOneOfIntegralInt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertPrimeTeichmuller.DvdPowQSub
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.Complex
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Linter.Style

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertPrimeTeichmuller.TeichNeZero

section

@[expose] public section

open NumberField Filter Topology

noncomputable section

namespace PI.OkpW

variable {K : Type} [Field K] [NumberField K] {p : ℕ} [hp : Fact p.Prime]

theorem norm_tau_unit (τ : K →+* ℂ_[p]) (hP : (Ideal.span {(p : 𝓞 K)}).IsPrime) {a : 𝓞 K}
    (ha : ¬ (p : 𝓞 K) ∣ a) : ‖τ (a : K)‖ = 1 := by
  obtain ⟨b, hb⟩ := exists_inv_mod hP ha
  have h1 := norm_tau_dvd τ (a := a * b - 1) (k := 1) (by rw [pow_one]; exact hb)
  rw [pow_one] at h1
  have hab : τ ((a * b - 1 : 𝓞 K) : K) = τ (a : K) * τ (b : K) - 1 := by
    rw [tau_sub]
    simp
  rw [hab] at h1
  have hlt : (p : ℝ)⁻¹ < 1 := pinv_lt_one
  refine le_antisymm (norm_tau_le τ a) ?_
  refine not_lt.1 fun hlt' => ?_
  have hprod : ‖τ (a : K) * τ (b : K)‖ < 1 := by
    rw [norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hlt' (norm_tau_le τ b)
  have hmax : ‖(1 : ℂ_[p])‖ ≤ max ‖τ (a : K) * τ (b : K)‖ ‖τ (a : K) * τ (b : K) - 1‖ := by
    have := IsUltrametricDist.norm_add_le_max (τ (a : K) * τ (b : K)) (-(τ (a : K) * τ (b : K) - 1))
    rwa [norm_neg, ← sub_eq_add_neg, sub_sub_cancel] at this
  rw [norm_one] at hmax
  exact absurd hmax (not_le.2 (max_lt hprod (h1.trans_lt hlt)))

theorem dvd_of_close (τ : K →+* ℂ_[p]) (hP : (Ideal.span {(p : 𝓞 K)}).IsPrime) {a b : 𝓞 K}
    (h : ‖τ (a : K) - τ (b : K)‖ < 1) : (p : 𝓞 K) ∣ a - b := by
  by_contra hn
  have h1 := norm_tau_unit τ hP hn
  rw [tau_sub] at h1
  linarith

variable (hq : ∀ b : 𝓞 K, (p : 𝓞 K) ∣ b ^ (p ^ 2) - b)
include hq

theorem teich_ne_zero (τ : K →+* ℂ_[p]) (hP : (Ideal.span {(p : 𝓞 K)}).IsPrime) {a : 𝓞 K}
    (ha : ¬ (p : 𝓞 K) ∣ a) : teich τ a ≠ 0 := by
  intro h0
  have hc := teich_close τ hq a
  rw [h0, zero_sub, norm_neg, norm_tau_unit τ hP ha] at hc
  linarith [pinv_lt_one (p := p)]

theorem teich_root (τ : K →+* ℂ_[p]) (hP : (Ideal.span {(p : 𝓞 K)}).IsPrime) {a : 𝓞 K}
    (ha : ¬ (p : 𝓞 K) ∣ a) : teich τ a ^ (p ^ 2 - 1) = 1 := by
  have hpow := teich_pow τ hq a
  have hne := teich_ne_zero hq τ hP ha
  have h1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.out.pos
  have he : teich τ a ^ (p ^ 2 - 1) * teich τ a = 1 * teich τ a := by
    rw [← pow_succ, Nat.sub_add_cancel h1, hpow, one_mul]
  exact mul_right_cancel₀ hne he

theorem teich_inj (τ : K →+* ℂ_[p]) (hP : (Ideal.span {(p : 𝓞 K)}).IsPrime) {a b : 𝓞 K}
    (h : teich τ a = teich τ b) : (p : 𝓞 K) ∣ a - b := by
  apply dvd_of_close τ hP
  have ha := teich_close τ hq a
  have hb := teich_close τ hq b
  have e : τ (a : K) - τ (b : K) = (teich τ b - τ (b : K)) - (teich τ a - τ (a : K)) := by
    rw [h]; ring
  rw [e]
  calc _ ≤ max ‖teich τ b - τ (b : K)‖ ‖teich τ a - τ (a : K)‖ := by
        rw [sub_eq_add_neg _ (teich τ a - τ (a : K)), ← norm_neg (teich τ a - τ (a : K))]
        exact IsUltrametricDist.norm_add_le_max _ _
    _ ≤ (p : ℝ)⁻¹ := max_le hb ha
    _ < 1 := pinv_lt_one

theorem teich_surj (hK : Module.finrank ℚ K = 2) (τ : K →+* ℂ_[p])
    (hP : (Ideal.span {(p : 𝓞 K)}).IsPrime) {ζ : ℂ_[p]} (hζ : ζ ^ (p ^ 2 - 1) = 1) :
    ∃ a : 𝓞 K, teich τ a = ζ := by
  classical
  have : (Ideal.span {(p : 𝓞 K)}).IsMaximal := isMaximal_span_p hP
  letI : Field (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}) := Ideal.Quotient.field _
  have : Finite (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}) := finite_quot hK
  letI : Fintype (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}) := Fintype.ofFinite _
  set g : 𝓞 K ⧸ Ideal.span {(p : 𝓞 K)} → 𝓞 K :=
    Function.surjInv (Ideal.Quotient.mk_surjective (I := Ideal.span {(p : 𝓞 K)})) with hgdef
  have hg : ∀ x, Ideal.Quotient.mk _ (g x) = x := Function.surjInv_eq _
  have hn : 0 < p ^ 2 - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow two_ne_zero hp.out.one_lt)
  have hnd : ∀ u : (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)})ˣ, ¬ (p : 𝓞 K) ∣ g u := fun u hd =>
    u.ne_zero (by rw [← hg u]; exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 hd))
  let f : (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)})ˣ → ℂ_[p] := fun u => teich τ (g u)
  have hf : Function.Injective f := fun u v huv => Units.ext (by
    rw [← hg u, ← hg v]
    exact Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 (teich_inj hq τ hP huv)))
  set T := (Polynomial.nthRoots (p ^ 2 - 1) (1 : ℂ_[p])).toFinset with hT
  have hsub : Finset.univ.image f ⊆ T := by
    intro x hx
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hx
    rw [hT, Multiset.mem_toFinset, Polynomial.mem_nthRoots hn]
    exact teich_root hq τ hP (hnd u)
  have hcardQ : Fintype.card (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}) = p ^ 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact natCard_quot hK
  have hcardU : Fintype.card (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)})ˣ = p ^ 2 - 1 := by
    rw [Fintype.card_units, hcardQ]
  have hcardT : T.card ≤ p ^ 2 - 1 :=
    (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _)
  have heq : Finset.univ.image f = T := Finset.eq_of_subset_of_card_le hsub (by
    rw [Finset.card_image_of_injective _ hf, Finset.card_univ, hcardU]
    exact hcardT)
  have hζT : ζ ∈ T := by
    rw [hT, Multiset.mem_toFinset, Polynomial.mem_nthRoots hn]
    exact hζ
  rw [← heq] at hζT
  obtain ⟨u, -, hu⟩ := Finset.mem_image.1 hζT
  exact ⟨g u, hu⟩

end PI.OkpW
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertPrimeTeichmuller.UltrametricPairEstimate

section

@[expose] public section

open NumberField Filter Topology

noncomputable section

namespace PI.OkpW

variable {K : Type} [Field K] [NumberField K] {p : ℕ} [hp : Fact p.Prime]

def gens (p : ℕ) [Fact p.Prime] : Set (ℂ_[p] × ℂ_[p]) :=
  {x | ∃ ζ : ℂ_[p], ζ ^ (p ^ 2 - 1) = 1 ∧ x = (ζ, ζ ^ p)}

theorem pair_mem_of_pow (t : ℂ_[p]) (ht : t ^ (p ^ 2) = t) :
    (t, t ^ p) ∈ Subring.closure (gens p) := by
  by_cases h0 : t = 0
  · subst h0
    have e : ((0 : ℂ_[p]), (0 : ℂ_[p]) ^ p) = 0 := by
      simp [zero_pow hp.out.ne_zero]
    rw [e]
    exact zero_mem _
  · apply Subring.subset_closure
    refine ⟨t, ?_, rfl⟩
    have h1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.out.pos
    have e : t ^ (p ^ 2 - 1) * t = 1 * t := by
      rw [← pow_succ, Nat.sub_add_cancel h1, ht, one_mul]
    exact mul_right_cancel₀ h0 e

theorem positionOne_invariantIntegral_exchange_step (X T Y R : ℂ_[p]) (n : ℕ) (h1 : ‖T - X‖ ≤ (p : ℝ)⁻¹ ^ (n + 1))
    (h2 : ‖Y - R‖ ≤ (p : ℝ)⁻¹ ^ n) :
    ‖(X - (p : ℂ_[p]) * Y) - (T - (p : ℂ_[p]) * R)‖ ≤ (p : ℝ)⁻¹ ^ (n + 1) := by
  have e : (X - (p : ℂ_[p]) * Y) - (T - (p : ℂ_[p]) * R) = (X - T) - (p : ℂ_[p]) * (Y - R) := by ring
  rw [e, ← dist_eq_norm]
  refine (IsUltrametricDist.dist_triangle_max _ 0 _).trans (max_le ?_ ?_)
  · rw [dist_zero_right, norm_sub_rev]
    exact h1
  · rw [dist_zero_left, norm_mul, norm_p_cp, pow_succ']
    exact mul_le_mul_of_nonneg_left h2 (by positivity)

theorem approx (τ : K →+* ℂ_[p]) (cO : 𝓞 K →+* 𝓞 K)
    (hqn : ∀ (a : 𝓞 K) (n : ℕ), (p : 𝓞 K) ∣ a ^ ((p ^ 2) ^ n) - a)
    (hfrob : ∀ a : 𝓞 K, (p : 𝓞 K) ∣ cO a - a ^ p) (n : ℕ) (a : 𝓞 K) :
    ∃ r ∈ Subring.closure (gens p), ‖τ (a : K) - r.1‖ ≤ (p : ℝ)⁻¹ ^ n ∧
      ‖τ ((cO a : 𝓞 K) : K) - r.2‖ ≤ (p : ℝ)⁻¹ ^ n := by
  have hq1 : ∀ b : 𝓞 K, (p : 𝓞 K) ∣ b ^ (p ^ 2) - b := fun b => by simpa using hqn b 1
  let φ : 𝓞 K →+* ℂ_[p] := τ.comp (algebraMap (𝓞 K) K)
  induction n generalizing a with
  | zero =>
    refine ⟨0, zero_mem _, ?_, ?_⟩
    · simpa using norm_tau_le τ a
    · simpa using norm_tau_le τ (cO a)
  | succ n ih =>
    obtain ⟨c, hc⟩ := hqn a n
    obtain ⟨r', hr', h1, h2⟩ := ih (-c)
    set T := teich τ a with hT
    have hTc : teich τ (cO a) = T ^ p := teich_c τ hq1 a (cO a) (hfrob a)

    have rel1 : φ (a ^ ((p ^ 2) ^ n)) - φ a = (p : ℂ_[p]) * φ c := by
      have h := congrArg φ hc
      simpa only [map_sub, map_mul, map_natCast] using h
    have rel2 : φ (cO a ^ ((p ^ 2) ^ n)) - φ (cO a) = (p : ℂ_[p]) * φ (cO c) := by
      have h := congrArg (φ.comp cO) hc
      simpa only [RingHom.comp_apply, map_sub, map_mul, map_natCast, map_pow] using h
    have hn1 : φ (-c) = -φ c := map_neg φ c
    have hn2 : φ (cO (-c)) = -φ (cO c) := by rw [map_neg, map_neg]
    have k1 : ‖T - φ (a ^ ((p ^ 2) ^ n))‖ ≤ (p : ℝ)⁻¹ ^ (n + 1) := (teich_spec τ hq1 a).2 n
    have k2 : ‖T ^ p - φ (cO a ^ ((p ^ 2) ^ n))‖ ≤ (p : ℝ)⁻¹ ^ (n + 1) := by
      rw [← hTc]
      exact (teich_spec τ hq1 (cO a)).2 n
    have j1 : ‖r'.1 - φ (-c)‖ ≤ (p : ℝ)⁻¹ ^ n := by
      rw [norm_sub_rev]
      exact h1
    have j2 : ‖r'.2 - φ (cO (-c))‖ ≤ (p : ℝ)⁻¹ ^ n := by
      rw [norm_sub_rev]
      exact h2
    refine ⟨(T, T ^ p) + (p : ℂ_[p] × ℂ_[p]) * r', ?_, ?_, ?_⟩
    · exact Subring.add_mem _ (pair_mem_of_pow T (teich_pow τ hq1 a))
        (Subring.mul_mem _ (natCast_mem _ p) hr')
    · have s := positionOne_invariantIntegral_exchange_step _ _ _ _ n k1 j1
      have e : τ (a : K) - ((T, T ^ p) + (p : ℂ_[p] × ℂ_[p]) * r').1 =
          (φ (a ^ ((p ^ 2) ^ n)) - (p : ℂ_[p]) * r'.1) - (T - (p : ℂ_[p]) * φ (-c)) := by
        simp only [Prod.fst_add, Prod.fst_mul, Prod.fst_natCast]
        change φ a - _ = _
        rw [hn1]
        linear_combination -rel1
      rw [e]
      exact s
    · have s := positionOne_invariantIntegral_exchange_step _ _ _ _ n k2 j2
      have e : τ ((cO a : 𝓞 K) : K) - ((T, T ^ p) + (p : ℂ_[p] × ℂ_[p]) * r').2 =
          (φ (cO a ^ ((p ^ 2) ^ n)) - (p : ℂ_[p]) * r'.2) - (T ^ p - (p : ℂ_[p]) * φ (cO (-c))) := by
        simp only [Prod.snd_add, Prod.snd_mul, Prod.snd_natCast]
        change φ (cO a) - _ = _
        rw [hn2]
        linear_combination -rel2
      rw [e]
      exact s

end PI.OkpW
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertPrimeTeichmuller.OkpInertMain

section

@[expose] public section

open NumberField Filter Topology

noncomputable section

namespace PI.OkpW

theorem okpInert_main : PI.OkpInert := by
  intro K _ _ c p _ τ hK hc hp2 hP
  show closure (Set.range fun a : 𝓞 K => (τ (a : K), τ (c (a : K)))) =
    closure (Subring.closure (gens p) : Set (ℂ_[p] × ℂ_[p]))
  have hqn : ∀ (a : 𝓞 K) (n : ℕ), (p : 𝓞 K) ∣ a ^ ((p ^ 2) ^ n) - a := fun a n =>
    pow_q_sub hK hP a n
  have hq : ∀ b : 𝓞 K, (p : 𝓞 K) ∣ b ^ (p ^ 2) - b := fun b => by simpa using hqn b 1
  set cO : 𝓞 K →+* 𝓞 K := RingOfIntegers.mapRingHom c with hcO
  have hfrob : ∀ a : 𝓞 K, (p : 𝓞 K) ∣ cO a - a ^ p := fun a => c_frob hK c hc hp2 hP a
  have hcoe : ∀ a : 𝓞 K, ((cO a : 𝓞 K) : K) = c (a : K) := fun a => rfl
  set ψ : 𝓞 K →+* ℂ_[p] × ℂ_[p] :=
    RingHom.prod (τ.comp (algebraMap (𝓞 K) K)) (τ.comp ((algebraMap (𝓞 K) K).comp cO)) with hψ
  have hR : Set.range (fun a : 𝓞 K => (τ (a : K), τ (c (a : K)))) =
      (ψ.range : Set (ℂ_[p] × ℂ_[p])) := by
    rw [RingHom.coe_range]
    rfl
  apply Set.Subset.antisymm
  · apply closure_minimal _ isClosed_closure
    rintro _ ⟨a, rfl⟩
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hp1 : (p : ℝ)⁻¹ < 1 :=
      inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hp1
    obtain ⟨r, hr, h1, h2⟩ := approx τ cO hqn hfrob n a
    refine ⟨r, hr, ?_⟩
    rw [Prod.dist_eq, dist_eq_norm, dist_eq_norm]
    rw [hcoe] at h2
    exact max_lt (lt_of_le_of_lt h1 hn) (lt_of_le_of_lt h2 hn)
  · have hsub : gens p ⊆ (ψ.range.topologicalClosure : Set (ℂ_[p] × ℂ_[p])) := by
      rintro x ⟨ζ, hζ, rfl⟩
      obtain ⟨a, ha⟩ := teich_surj hq hK τ hP hζ
      have hb : teich τ (cO a) = teich τ a ^ p := teich_c τ hq a (cO a) (hfrob a)
      show (_ : ℂ_[p] × ℂ_[p]) ∈ closure (ψ.range : Set (ℂ_[p] × ℂ_[p]))
      have hlim : Tendsto (fun k => (tseq τ a k, tseq τ (cO a) k)) atTop (𝓝 (ζ, ζ ^ p)) := by
        rw [← ha, ← hb]
        exact (teich_spec τ hq a).1.prodMk_nhds (teich_spec τ hq (cO a)).1
      apply mem_closure_of_tendsto hlim
      refine Filter.Eventually.of_forall fun k => ?_
      refine RingHom.mem_range.mpr ⟨a ^ ((p ^ 2) ^ k), ?_⟩
      simp [hψ, tseq]
    rw [hR]
    exact closure_minimal (SetLike.coe_subset_coe.mpr (Subring.closure_le.mpr hsub))
      isClosed_closure

end PI.OkpW
end
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.OkpInert

section

@[expose] public section

theorem integers_inert_prime : PI.OkpInert := PI.OkpW.okpInert_main
end
end
