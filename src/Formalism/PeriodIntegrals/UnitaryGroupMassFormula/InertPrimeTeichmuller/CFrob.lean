module

public import Mathlib.NumberTheory.NumberField.Basic
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
public import Mathlib.Algebra.Algebra.Hom.Rat
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertPrimeTeichmuller.NormLeOneOfIntegralInt
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertPrimeTeichmuller.CFixRat

section

@[expose] public section

open NumberField

noncomputable section

namespace PI.OkpW

variable {K : Type} [Field K] [NumberField K]

theorem c_invol (hK : Module.finrank ℚ K = 2) (c : K →+* K) (x : K) : c (c x) = x := by
  let f : K →ₐ[ℚ] K := c.toRatAlgHom
  let e : K ≃ₐ[ℚ] K := AlgEquiv.ofBijective f (AlgHom.bijective f)
  have hcard : Nat.card (K ≃ₐ[ℚ] K) ≤ 2 := by
    rw [← hK, Nat.card_congr (algEquivEquivAlgHom ℚ K).toEquiv]
    exact card_algHom_le_finrank ℚ K K
  have hpos : 0 < Nat.card (K ≃ₐ[ℚ] K) := Nat.card_pos
  have h1 : e ^ Nat.card (K ≃ₐ[ℚ] K) = 1 := pow_card_eq_one'
  have he : e ^ 2 = 1 := by
    rcases (by omega : Nat.card (K ≃ₐ[ℚ] K) = 1 ∨ Nat.card (K ≃ₐ[ℚ] K) = 2) with h | h
    · rw [h, pow_one] at h1; rw [h1, one_pow]
    · rwa [h] at h1
  have := DFunLike.congr_fun he x
  rw [pow_two, AlgEquiv.mul_apply, AlgEquiv.one_apply] at this
  exact this

theorem c_fix_rat (hK : Module.finrank ℚ K = 2) (c : K →+* K) (hc : ∃ x, c x ≠ x) {y : K}
    (hy : c y = y) : ∃ r : ℚ, (r : K) = y := by
  let D : K →ₗ[ℚ] K := c.toRatAlgHom.toLinearMap - LinearMap.id
  have hD : ∀ z, D z = c z - z := fun z => rfl
  have hS : LinearMap.ker D ≠ ⊤ := by
    obtain ⟨x, hx⟩ := hc
    intro h
    have hm : x ∈ LinearMap.ker D := h ▸ Submodule.mem_top
    rw [LinearMap.mem_ker, hD, sub_eq_zero] at hm
    exact hx hm
  have hlt : Module.finrank ℚ (LinearMap.ker D) < 2 :=
    hK ▸ Submodule.finrank_lt hS
  have hle : (ℚ ∙ (1 : K)) ≤ LinearMap.ker D := by
    rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker, hD, map_one, sub_self]
  have heq : (ℚ ∙ (1 : K)) = LinearMap.ker D :=
    Submodule.eq_of_le_of_finrank_le hle (by rw [finrank_span_singleton one_ne_zero]; omega)
  have hyS : y ∈ LinearMap.ker D := by rw [LinearMap.mem_ker, hD, hy, sub_self]
  rw [← heq, Submodule.mem_span_singleton] at hyS
  obtain ⟨r, hr⟩ := hyS
  exact ⟨r, by rw [← hr, Rat.smul_def, mul_one]⟩

theorem add_c_int (hK : Module.finrank ℚ K = 2) (c : K →+* K) (hc : ∃ x, c x ≠ x) (a : 𝓞 K) :
    ∃ n : ℤ, a + RingOfIntegers.mapRingHom c a = (n : 𝓞 K) := by
  have hfix : c ((a : K) + c a) = (a : K) + c a := by rw [map_add (f := _), c_invol hK c, add_comm]
  obtain ⟨r, hr⟩ := c_fix_rat hK c hc hfix
  have hint : IsIntegral ℤ (algebraMap ℚ K r) := by
    rw [eq_ratCast, hr]
    have := (a + RingOfIntegers.mapRingHom c a).isIntegral_coe
    simpa [RingOfIntegers.mapRingHom_apply] using this
  rw [isIntegral_algebraMap_iff ,
    IsIntegrallyClosed.isIntegral_iff] at hint
  obtain ⟨n, hn⟩ := hint
  refine ⟨n, RingOfIntegers.ext ?_⟩
  have h2 : ((a + RingOfIntegers.mapRingHom c a : 𝓞 K) : K) = (a : K) + c a := by
    simp [RingOfIntegers.mapRingHom_apply]
  rw [h2, ← hr, ← hn]
  simp

end PI.OkpW
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertPrimeTeichmuller.CFrob

section

@[expose] public section

open NumberField

noncomputable section

namespace PI.OkpW

variable {K : Type} [Field K] [NumberField K] {p : ℕ} [hp : Fact p.Prime]

theorem c_frob (hK : Module.finrank ℚ K = 2) (c : K →+* K) (hc : ∃ x, c x ≠ x) (hp2 : p ≠ 2)
    (hP : (Ideal.span {(p : 𝓞 K)}).IsPrime) (a : 𝓞 K) :
    (p : 𝓞 K) ∣ RingOfIntegers.mapRingHom c a - a ^ p := by
  classical
  haveI hmax := isMaximal_span_p (K := K) (p := p) hP
  have hle : Ideal.span {(p : 𝓞 K)} ≤
      (Ideal.span {(p : 𝓞 K)}).comap (RingOfIntegers.mapRingHom c) := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show RingOfIntegers.mapRingHom c (p : 𝓞 K) ∈ Ideal.span {(p : 𝓞 K)}
    rw [map_natCast]
    exact Ideal.mem_span_singleton_self _
  let σ : (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}) →+* (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}) := Ideal.quotientMap _ (RingOfIntegers.mapRingHom c) hle
  have hσ : ∀ y : 𝓞 K, σ (Ideal.Quotient.mk _ y) =
      Ideal.Quotient.mk _ (RingOfIntegers.mapRingHom c y) := fun y => Ideal.quotientMap_mk
  haveI : CharP (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}) p := CharP.quotient (𝓞 K) p
    (mem_nonunits_iff.mpr fun hu => hP.ne_top (Ideal.span_singleton_eq_top.mpr hu))
  haveI : ExpChar (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}) p := ExpChar.prime hp.out
  have h2 : (2 : (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)})) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)})) = 0 := by exact_mod_cast h
    have hd := (CharP.cast_eq_zero_iff (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}) p 2).mp h'
    have hp3 : p ≤ 2 := Nat.le_of_dvd (by norm_num) hd
    have := hp.out.two_le
    omega
  have hfixZ : ∀ z : ℤ, ((z : (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}))) ^ p = z := fun z => by rw [← frobenius_def, map_intCast]
  have h2p : (2 : (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)})) ^ p = 2 := by rw [← frobenius_def, map_ofNat]
  have hdich : ∀ x : (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}), x ^ p = x ∨ x ^ p = σ x := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨n, hn⟩ := add_c_int hK c hc a
    obtain ⟨n2, hn2⟩ := add_c_int hK c hc (a ^ 2)
    have ht : Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)}) a +
        σ (Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)}) a) = (n : (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)})) := by
      rw [hσ, ← map_add (f := _), hn, map_intCast]
    have ht2 : Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)}) a ^ 2 +
        σ (Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)}) a) ^ 2 = (n2 : (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)})) := by
      have := congrArg (Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)})) hn2
      rw [map_add (f := _), map_intCast, map_pow, map_pow] at this
      rw [hσ, ← this, map_pow (Ideal.Quotient.mk _) ((RingOfIntegers.mapRingHom c) a)]
    generalize Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)}) a = x at ht ht2 ⊢
    have hm : (2 : (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)})) * (x * σ x) = (n : (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)})) ^ 2 - n2 := by
      rw [← ht, ← ht2]; ring
    have hmp : (x * σ x) ^ p = x * σ x := by
      have h1 : ((2 : (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)})) * (x * σ x)) ^ p = 2 * (x * σ x) := by
        rw [hm, sub_pow_char, ← pow_mul, mul_comm 2 p, pow_mul, hfixZ, hfixZ]
      rw [mul_pow, h2p] at h1
      exact mul_left_cancel₀ h2 h1
    have hzero : x ^ 2 - (n : (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)})) * x + x * σ x = 0 := by
      rw [← ht]; ring
    have hfr := congrArg (frobenius (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}) p) hzero
    rw [map_zero, map_add (f := _), map_sub, map_mul, map_pow, map_intCast, frobenius_def,
      frobenius_def, hmp] at hfr
    have hq : (x ^ p - x) * (x ^ p - σ x) = 0 := by
      rw [← hfr, ← ht]; ring
    rcases mul_eq_zero.mp hq with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (sub_eq_zero.mp h)
  have hex : ∃ y : (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}), y ^ p ≠ y := by
    by_contra hcon
    push_neg at hcon
    haveI := finite_quot (K := K) (p := p) hK
    letI := Fintype.ofFinite (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)})
    letI : Field (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}) := Ideal.Quotient.field _
    have hp1 : 1 < p := hp.out.one_lt
    have hsub : (Finset.univ : Finset (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)})) ⊆ ((Polynomial.X ^ p - Polynomial.X : Polynomial (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)})).roots.toFinset) := by
      intro y _
      rw [Multiset.mem_toFinset, Polynomial.mem_roots (Polynomial.X_pow_sub_X_ne_zero hp1)]
      simp [Polynomial.IsRoot, hcon y]
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_univ] at h1
    have h2 := (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' (Polynomial.X ^ p - Polynomial.X : Polynomial (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)})))
    rw [Polynomial.natDegree_X_pow_sub_X (R := (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)})) hp1] at h2
    have h3 : Fintype.card (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}) = p ^ 2 := by
      rw [← Nat.card_eq_fintype_card]; exact natCard_quot (K := K) (p := p) hK
    have h4 : p ^ 2 ≤ p := h3 ▸ h1.trans h2
    nlinarith [hp1]
  obtain ⟨y, hy⟩ := hex
  have hyσ : y ^ p = σ y := (hdich y).resolve_left hy
  have hall : ∀ x : (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}), σ x = x ^ p := by
    intro x
    rcases hdich x with hx | hx
    · have hxy : (x + y) ^ p ≠ x + y := by
        rw [add_pow_char, hx]
        intro h
        exact hy (add_left_cancel h)
      have h1 := (hdich (x + y)).resolve_left hxy
      rw [add_pow_char, hx, hyσ, map_add (f := _)] at h1
      rw [hx]
      exact (add_right_cancel h1).symm
    · exact hx.symm
  have := hall (Ideal.Quotient.mk _ a)
  rw [hσ, ← map_pow, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton] at this
  exact this

end PI.OkpW
end
end
end
