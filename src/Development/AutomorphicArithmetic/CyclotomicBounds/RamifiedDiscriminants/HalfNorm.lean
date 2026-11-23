module

public import Development.AutomorphicArithmetic.FrobeniusLocalisation.DiffDefs
public import Formalism.LocalRingCardinality.DataHost
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.CondRd
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.RamEq
public import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.DiffEKSupp
import Development.AutomorphicArithmetic.FrobeniusLocalisation.DiscrK
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Development.AutomorphicArithmetic.PrimeDiscriminants.RamDiscr
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AutomorphicArithmetic.FrobeniusLocalisation.halfSupp

section

@[expose] public section

open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

theorem UpperTheory.HF.half_supp :
    ∀ {φ : Frame} (H : HostAx φ) (𝔟 : Ideal (𝓞 H.E)), differentIdeal (𝓞 H.K) (𝓞 H.E) = 𝔟 * (H.conj • 𝔟) → 𝔟 ⊔ H.conj • 𝔟 = ⊤ → (∀ (P : Ideal (𝓞 H.E)) [P.IsPrime], ((P ∣ 𝔟 ∨ H.conj • P ∣ 𝔟) ↔ ∃ l ∈ H.ramI, P.LiesOver (span {(l : ℤ)})) ∧ ¬ (P ∣ 𝔟 ∧ H.conj • P ∣ 𝔟) ∧ (P ∣ 𝔟 → multiplicity P 𝔟 = multiplicity P (differentIdeal (𝓞 H.K) (𝓞 H.E)))) ∧ ∃ s : 𝓞 H.E, (s : H.E) = H.sqd ∧ differentIdeal ℤ (𝓞 H.E) = 𝔟 * (H.conj • 𝔟) * span {s} := by
  intro φ H B hD hcop
  have mono : ∀ {I J : Ideal (𝓞 H.E)}, I ≤ J → H.conj • I ≤ H.conj • J := by
    intro I J h
    rw [Ideal.pointwise_smul_def, Ideal.pointwise_smul_def]
    exact Ideal.map_mono h
  have inv : ∀ I : Ideal (𝓞 H.E), H.conj • H.conj • I = I := by
    intro I
    rw [smul_smul, H.conj_mul_conj, one_smul]
  have sw : ∀ {I J : Ideal (𝓞 H.E)}, H.conj • I ≤ J ↔ I ≤ H.conj • J := by
    intro I J
    constructor
    · intro h
      simpa only [inv] using mono h
    · intro h
      simpa only [inv] using mono h
  refine ⟨fun P hP => ?_, ?_⟩
  · have hsupp := (UpperTheory.HF.diff_EK_supp H).2.1 P
    have notboth : ¬ (B ≤ P ∧ B ≤ H.conj • P) := by
      rintro ⟨h1, h2⟩
      apply hP.ne_top
      rw [eq_top_iff, ← hcop]
      exact sup_le h1 (sw.2 h2)
    have hncB : P ∣ B → ¬ P ∣ H.conj • B := by
      intro h1 h2
      rw [Ideal.dvd_iff_le] at h1 h2
      exact notboth ⟨h1, sw.1 h2⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [← hsupp, hD]
      constructor
      · rintro (h | h)
        · exact dvd_mul_of_dvd_left h _
        · rw [Ideal.dvd_iff_le] at h ⊢
          exact le_trans Ideal.mul_le_right (sw.2 h)
      · intro h
        rw [Ideal.dvd_iff_le] at h
        rcases hP.mul_le.1 h with h1 | h1
        · exact Or.inl (Ideal.dvd_iff_le.2 h1)
        · exact Or.inr (Ideal.dvd_iff_le.2 (sw.1 h1))
    · rintro ⟨h1, h2⟩
      rw [Ideal.dvd_iff_le] at h1 h2
      exact notboth ⟨h1, h2⟩
    · intro h1
      have hP0 : P ≠ ⊥ := by
        rintro rfl
        rw [Ideal.dvd_iff_le, le_bot_iff] at h1
        have hle : B ⊔ H.conj • B ≤ ⊥ := sup_le h1.le (sw.2 (by rw [h1]; exact bot_le))
        rw [hcop] at hle
        exact hP.ne_top (eq_top_iff.2 hle)
      have hpr : Prime P := Ideal.prime_of_isPrime hP0 hP
      unfold multiplicity
      rw [hD, emultiplicity_mul hpr, emultiplicity_eq_zero.2 (hncB h1), add_zero]
  · obtain ⟨-, s, hs, -, hdiff⟩ := discr_K H
    exact ⟨s, hs, hdiff.trans (by rw [hD])⟩
end
end

-- Source module: Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.HalfNorm

section

@[expose] public section

open UpperTheory.HF

open NumberField Ideal
open scoped Pointwise

namespace Formalism.BasicNotions.Host

variable {R : Ranks} (H : Host R)

theorem mem_ramI_iff {p : ℕ} (hp : p.Prime) : p ∈ H.toHostRaw.ramI ↔ p ∣ H.QS * H.q := by
  have h0 : (discr H.E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero _)
  rw [Formalism.HC.HostRaw.ramI, Finset.mem_erase, Formalism.HC.HostRaw.ram, Nat.mem_primeFactors, H.dvd_natAbs_discr_iff hp]
  constructor
  · rintro ⟨hd, -, h, -⟩
    exact ((Nat.Prime.dvd_mul hp).1 h).resolve_right fun h' =>
      hd ((Nat.prime_dvd_prime_iff_eq hp H.toHostRaw.d_prime).1 h')
  · intro h
    refine ⟨?_, hp, h.mul_right _, h0⟩
    rintro rfl
    exact H.toHostRaw.d_not_dvd_QSq h

private theorem liesOver_of_mem {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) (P : Ideal (𝓞 E)) [P.IsPrime]
    (h : (p : 𝓞 E) ∈ P) : P.LiesOver (span {(p : ℤ)}) :=
  ⟨Ideal.IsMaximal.eq_of_le
    (PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hp).irreducible)
    (Ideal.IsPrime.ne_top inferInstance) (by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]; exact h)⟩

private theorem dvd_absNorm_of {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) (P J : Ideal (𝓞 E)) [hP : P.IsPrime]
    (h : (p : 𝓞 E) ∈ P) (hJ : P ∣ J) : p ∣ absNorm J := by
  by_contra hn
  obtain ⟨u, v, huv⟩ : IsCoprime (p : 𝓞 E) ((absNorm J : ℕ) : 𝓞 E) := ((Nat.Prime.coprime_iff_not_dvd hp).2 hn).cast
  exact hP.ne_top ((Ideal.eq_top_iff_one P).2
    (huv ▸ P.add_mem (P.mul_mem_left u h) (P.mul_mem_left v (Ideal.le_of_dvd hJ (Ideal.absNorm_mem J)))))

theorem half_ne_bot : H.𝔟 ≠ ⊥ := fun h => by
  have h1 := H.𝔟_spec.1
  rw [h, Ideal.bot_mul] at h1
  exact differentIdeal_ne_bot h1

theorem prime_dvd_absNorm_half_iff {p : ℕ} (hp : p.Prime) : p ∣ absNorm H.𝔟 ↔ p ∣ H.QS * H.q := by
  have hs := (UpperTheory.HF.half_supp H.toHostAx H.𝔟 H.𝔟_spec.1 H.𝔟_spec.2).1
  constructor
  · intro h
    obtain ⟨P, hP, hu, hd⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp _ h
    haveI := hP.isPrime
    obtain ⟨l, hl, ho⟩ := (hs P).1.1 (Or.inl hd)
    have hlp : l.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hl)
    have e : span {(l : ℤ)} = span {(p : ℤ)} := ho.over.trans hu
    have : p ∣ l := by
      have := Ideal.mem_span_singleton.1 (e ▸ Ideal.mem_span_singleton_self (l : ℤ))
      exact_mod_cast this
    rw [(Nat.prime_dvd_prime_iff_eq hp hlp).1 this]
    exact (H.mem_ramI_iff hlp).1 hl
  · intro h
    have h1 : p ∣ absNorm (span {(p : 𝓞 H.E)}) := by
      rw [Ideal.absNorm_span_natCast]
      exact dvd_pow_self _ Module.finrank_pos.ne'
    obtain ⟨P, hP, -, hd⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp _ h1
    haveI := hP.isPrime
    have hm : (p : 𝓞 H.E) ∈ P := Ideal.le_of_dvd hd (Ideal.mem_span_singleton_self _)
    rcases (hs P).1.2 ⟨p, (H.mem_ramI_iff hp).2 h, liesOver_of_mem hp P hm⟩ with h2 | h2
    · exact dvd_absNorm_of hp P _ hm h2
    · have hm' : (p : 𝓞 H.E) ∈ H.toHostRaw.conj • P := by
        have := Ideal.smul_mem_pointwise_smul H.toHostRaw.conj _ _ hm
        rwa [show H.toHostRaw.conj • (p : 𝓞 H.E) = p from map_natCast (MulSemiringAction.toRingHom _ (𝓞 H.E) H.toHostRaw.conj) p] at this
      exact dvd_absNorm_of hp _ _ hm' h2

theorem four_ord_le_condN : 4 * R.toFrame.ord ≤ H.QS * H.q * H.d := by
  have h := UpperTheory.HF.cond_rd H.toHostAx
  have h2 := UpperTheory.HF.ram_eq H.toHostAx
  refine h.2.2.2.2.2.2.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero H.toHostRaw.condN_ne_zero) ?_)
  rw [h2.2.2.2.1]
  refine Nat.mul_dvd_mul_right (Nat.mul_dvd_mul h2.2.2.2.2.1 ?_) _
  split_ifs
  exacts [dvd_rfl, one_dvd _]

end Formalism.BasicNotions.Host
end
end
