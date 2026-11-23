module

public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.RingTheory.Ideal.Prime
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.RingTheory.Trace.Defs
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.TraceIdempotentNotDivisible
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.TypeStar
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicative

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTer

section

@[expose] public section

theorem UpperTheory.Reformulated.B.DYdc5.main.{u_1} :
    ∀ {R : Type u_1} [inst : CommRing R] (P : Ideal R) [hP : P.IsPrime] (t : ℕ),
      t ≠ (0 : ℕ) → (↑t : R) ∈ P → ∃ (p : ℕ), Nat.Prime p ∧ p ∣ t ∧ (↑p : R) ∈ P := by
  intro R _ P hP t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro ht hmem
    have h1 : t ≠ 1 := by
      rintro rfl
      exact hP.ne_top ((Ideal.eq_top_iff_one P).2 (by simpa using hmem))
    obtain ⟨p, hp, k, rfl⟩ := Nat.exists_prime_and_dvd h1
    rw [Nat.cast_mul] at hmem
    rcases hP.mem_or_mem hmem with h | h
    · exact ⟨p, hp, dvd_mul_right p k, h⟩
    · have hk : k ≠ 0 := by
        rintro rfl
        simp at ht
      have hlt : k < p * k :=
        lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hk) hp.one_lt
      obtain ⟨q, hq, hqk, hqP⟩ := ih k hlt hk h
      exact ⟨q, hq, hqk.mul_left p, hqP⟩
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.TraceIdempotentNotDivisibleStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.trace_idempotent_not_divisible : ∀ (B : Type) [CommRing B] [Module.Free ℤ B] [Module.Finite ℤ B] (x : B) (p m : ℕ), p.Prime → Module.finrank ℤ B < p ^ m → x * x - x ∈ Ideal.span {((p : B)) ^ m} → x ∉ Ideal.span {((p : B)) ^ m} → ¬ ((p : ℤ) ^ m ∣ Algebra.trace ℤ B x) := by
  first | exact @GlobalTheory.CompanionTheory.IdemTrace.not_dvd_trace | exact GlobalTheory.CompanionTheory.IdemTrace.not_dvd_trace | (intros; apply GlobalTheory.CompanionTheory.IdemTrace.not_dvd_trace <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.PrimePowerNotDvdDifferent

section

@[expose] public section

open NumberField IsDedekindDomain nonZeroDivisors

namespace GlobalTheory.CompanionTheory.Glob

theorem not_pow_dvd_different (E : Type) [Field E] [NumberField E] (P J : Ideal (𝓞 E)) [P.IsPrime]
    (p k : ℕ) (hp : p.Prime) (hpP : (p : 𝓞 E) ∈ P) (hPJ : ¬ P ∣ J)
    (hspan : Ideal.span {((p : 𝓞 E)) ^ (Module.finrank ℚ E)} = P ^ k * J) :
    ¬ P ^ k ∣ differentIdeal ℤ (𝓞 E) := by
  intro hdiv
  set d := Module.finrank ℚ E with hd
  have hdpos : 0 < d := Module.finrank_pos
  have hp0 : (p : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hPbot : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hpP
    exact hp0 hpP
  have hPmax : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hPbot
  have hpd : ((p : 𝓞 E)) ^ d ∈ P := Ideal.pow_mem_of_mem P hpP d hdpos
  have hspanP : Ideal.span {((p : 𝓞 E)) ^ d} ≤ P := by
    rw [Ideal.span_singleton_le_iff_mem]
    exact hpd
  have hJP : ¬ J ≤ P := fun h => hPJ (Ideal.dvd_iff_le.2 h)
  have hk : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, Ideal.one_eq_top, Ideal.top_mul] at hspan
    exact hJP (hspan ▸ hspanP)
  have hcop : IsCoprime P J := by
    rw [Ideal.isCoprime_iff_sup_eq]
    exact hPmax.1.2 _ (lt_of_le_of_ne le_sup_left fun h => hJP (h ▸ le_sup_right))
  obtain ⟨y, hy, x, hx, hyx⟩ := Ideal.isCoprime_iff_exists.1 (hcop.pow_left (m := k))
  have hxy : x * y ∈ Ideal.span {((p : 𝓞 E)) ^ d} := by
    rw [hspan, mul_comm x y]
    exact Ideal.mul_mem_mul hy hx
  have hidem : x * x - x ∈ Ideal.span {((p : 𝓞 E)) ^ d} := by
    have : x * x - x = -(x * y) := by
      have : x = 1 - y := by rw [← hyx]; ring
      rw [this]; ring
    rw [this]
    exact neg_mem hxy
  have hnot : x ∉ Ideal.span {((p : 𝓞 E)) ^ d} := by
    intro h
    have h1 : x ∈ P := hspanP h
    have h2 : y ∈ P := Ideal.pow_le_self hk hy
    exact hPmax.ne_top ((Ideal.eq_top_iff_one _).2 (hyx ▸ add_mem h2 h1))
  have hlt : Module.finrank ℤ (𝓞 E) < p ^ d := by
    rw [RingOfIntegers.rank]
    exact Nat.lt_pow_self hp.one_lt
  refine GlobalTheory.T.trace_idempotent_not_divisible (𝓞 E) x p d hp hlt hidem hnot ?_

  have hpdE : ((p : E)) ^ d ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hp.ne_zero)
  have hD0 : ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
    exact differentIdeal_ne_bot
  have hz : (x : E) / ((p : E)) ^ d ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    have hdual : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) =
        ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)⁻¹ := by
      rw [coeIdeal_differentIdeal ℤ ℚ E (𝓞 E), inv_inv]
    rw [hdual, FractionalIdeal.mem_inv_iff hD0]
    intro w hw
    obtain ⟨δ, hδ, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hw
    have hδP : δ ∈ P ^ k := Ideal.dvd_iff_le.1 hdiv hδ
    have hmem : δ * x ∈ Ideal.span {((p : 𝓞 E)) ^ d} := by
      rw [hspan]
      exact Ideal.mul_mem_mul hδP hx
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hmem
    rw [FractionalIdeal.mem_one_iff]
    refine ⟨a, ?_⟩
    have h2 : algebraMap (𝓞 E) E a * ((p : E)) ^ d = algebraMap (𝓞 E) E δ * (x : E) := by
      have := congrArg (algebraMap (𝓞 E) E) ha
      simpa using this
    field_simp
    rw [h2]
    ring
  have h10 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := one_ne_zero
  have htr := (FractionalIdeal.mem_dual (A := ℤ) (K := ℚ) h10).1 hz 1 (FractionalIdeal.one_mem_one _)
  obtain ⟨n, hn⟩ := htr
  rw [Algebra.traceForm_apply, mul_one] at hn
  have hzs : (x : E) / ((p : E)) ^ d = (((p : ℚ) ^ d)⁻¹) • (x : E) := by
    rw [Algebra.smul_def, map_inv₀, map_pow, map_natCast, div_eq_inv_mul]
  rw [hzs, map_smul, smul_eq_mul, ← Algebra.coe_trace_int] at hn
  have hpq : ((p : ℚ)) ^ d ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hp.ne_zero)
  refine ⟨n, ?_⟩
  have : ((Algebra.trace ℤ (𝓞 E) x : ℤ) : ℚ) = ((p : ℚ)) ^ d * (n : ℚ) := by
    have h3 : (algebraMap ℤ ℚ n) = (n : ℚ) := rfl
    rw [h3] at hn
    rw [hn]
    field_simp
  exact_mod_cast this

end GlobalTheory.CompanionTheory.Glob
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.PrimePowerNotDvdDifferentStatement

section

@[expose] public section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.prime_power_not_dvd_different : ∀ (E : Type) [Field E] [NumberField E] (P J : Ideal (𝓞 E)) [P.IsPrime] (p k : ℕ), p.Prime → (p : 𝓞 E) ∈ P → ¬ P ∣ J → Ideal.span {((p : 𝓞 E)) ^ (Module.finrank ℚ E)} = P ^ k * J → ¬ P ^ k ∣ differentIdeal ℤ (𝓞 E) := by
  first | exact @GlobalTheory.CompanionTheory.Glob.not_pow_dvd_different | exact GlobalTheory.CompanionTheory.Glob.not_pow_dvd_different | (intros; apply GlobalTheory.CompanionTheory.Glob.not_pow_dvd_different <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.DifferentDvdRamifiedPrimePower

section

@[expose] public section

open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.Glob

theorem exists_prime_mem_of_natCast_mem {R : Type*} [CommRing R] (P : Ideal R) [hP : P.IsPrime]
    (t : ℕ) (ht : t ≠ 0) (htP : (t : R) ∈ P) : ∃ p : ℕ, p.Prime ∧ p ∣ t ∧ (p : R) ∈ P :=
  _root_.UpperTheory.Reformulated.B.DYdc5.main P t ht htP

theorem prime_pow_dvd_span_of_dvd_differentIdeal (E : Type) [Field E] [NumberField E] (t : ℕ)
    (ht : t ≠ 0)
    (h : ∀ P : Ideal (𝓞 E), P.IsPrime → P ≠ ⊥ → P ∣ differentIdeal ℤ (𝓞 E) → (t : 𝓞 E) ∈ P)
    (P : Ideal (𝓞 E)) (hPp : Prime P) (i : ℕ) (hi : P ^ i ∣ differentIdeal ℤ (𝓞 E)) :
    P ^ i ∣ Ideal.span {((t : 𝓞 E)) ^ (Module.finrank ℚ E)} := by
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · simp
  have hPD : P ∣ differentIdeal ℤ (𝓞 E) := (dvd_pow_self P hipos.ne').trans hi
  have hP0 : P ≠ ⊥ := hPp.ne_zero
  haveI hPprime : P.IsPrime := Ideal.isPrime_of_prime hPp
  obtain ⟨p, hp, hpt, hpP⟩ := exists_prime_mem_of_natCast_mem P t ht (h P hPprime hP0 hPD)
  have hp0 : ((p : 𝓞 E)) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hS0 : Ideal.span {((p : 𝓞 E)) ^ (Module.finrank ℚ E)} ≠ 0 := by
    intro h0
    have := Ideal.span_singleton_eq_bot.1 h0
    exact pow_ne_zero _ hp0 this
  obtain ⟨J, hJ, hnd⟩ :=
    (FiniteMultiplicity.of_not_isUnit hPp.not_unit hS0).exists_eq_pow_mul_and_not_dvd
  have hnot := GlobalTheory.T.prime_power_not_dvd_different E P J p _ hp hpP hnd hJ
  have hlt : i < multiplicity P (Ideal.span {((p : 𝓞 E)) ^ (Module.finrank ℚ E)}) := by
    by_contra hle
    exact hnot ((pow_dvd_pow P (not_lt.1 hle)).trans hi)
  have h1 : P ^ i ∣ Ideal.span {((p : 𝓞 E)) ^ (Module.finrank ℚ E)} := by
    exact ((pow_dvd_pow P hlt.le).mul_right J).trans (dvd_of_eq hJ.symm)
  refine h1.trans ?_
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_span_singleton]
  exact pow_dvd_pow_of_dvd (Nat.cast_dvd_cast hpt) _

theorem differentIdeal_dvd_span_pow : ∀ (E : Type) [Field E] [NumberField E] (t : ℕ), t ≠ 0 →
    (∀ P : Ideal (𝓞 E), P.IsPrime → P ≠ ⊥ → P ∣ differentIdeal ℤ (𝓞 E) → (t : 𝓞 E) ∈ P) →
    differentIdeal ℤ (𝓞 E) ∣ Ideal.span {((t : 𝓞 E)) ^ (Module.finrank ℚ E)} := by
  intro E _ _ t ht h
  have hD : differentIdeal ℤ (𝓞 E) ≠ 0 := differentIdeal_ne_bot
  have key : ∀ I : Ideal (𝓞 E), I ≠ 0 → I ∣ differentIdeal ℤ (𝓞 E) →
      I ∣ Ideal.span {((t : 𝓞 E)) ^ (Module.finrank ℚ E)} := by
    intro I
    induction I using UniqueFactorizationMonoid.induction_on_coprime with
    | h0 => exact fun h0 => absurd rfl h0
    | h1 hu => exact fun _ _ => hu.dvd
    | hpr i hq =>
      exact fun _ hd => prime_pow_dvd_span_of_dvd_differentIdeal E t ht h _ hq i hd
    | hcp hxy hx hy =>
      intro h0 hd
      exact hxy.mul_dvd (hx (left_ne_zero_of_mul h0) ((dvd_mul_right _ _).trans hd))
        (hy (right_ne_zero_of_mul h0) ((dvd_mul_left _ _).trans hd))
  exact key _ hD dvd_rfl

end GlobalTheory.CompanionTheory.Glob
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.DifferentDvdRamifiedPrimePowerStatement

section

@[expose] public section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.different_dvd_ramified_prime_power : ∀ (E : Type) [Field E] [NumberField E] (t : ℕ), t ≠ 0 → (∀ P : Ideal (𝓞 E), P.IsPrime → P ≠ ⊥ → P ∣ differentIdeal ℤ (𝓞 E) → (t : 𝓞 E) ∈ P) → differentIdeal ℤ (𝓞 E) ∣ Ideal.span {((t : 𝓞 E)) ^ (Module.finrank ℚ E)} := by
  first | exact @GlobalTheory.CompanionTheory.Glob.differentIdeal_dvd_span_pow | exact GlobalTheory.CompanionTheory.Glob.differentIdeal_dvd_span_pow | (intros; apply GlobalTheory.CompanionTheory.Glob.differentIdeal_dvd_span_pow <;> assumption)
end
end
