module

public import Development.AutomorphicArithmetic.FrobeniusLocalisation.DiffDefs
public import Development.AutomorphicArithmetic.PrimeDiscriminants.SlopeTestRemainingChoices
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.RingTheory.DedekindDomain.Different
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.PadicValNatAbsNormEqZero
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.GrpBridge
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.VdTameWild
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.DiscrK
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.MemRam
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.KcDiff
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.KcDiffSmulMem
import Mathlib.RingTheory.WittVector.IsPoly

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDifferentExponentDenominator

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace GlobalTheory.DifferentElement

end GlobalTheory.DifferentElement

namespace GlobalTheory.DifferentElement

theorem mult_ratio (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (l : ℕ) (hl : l.Prime) (P : Ideal (𝓞 E))
    (hP : P.IsPrime) (hlP : (l : 𝓞 E) ∈ P) :
    (multiplicity P (differentIdeal ℤ (𝓞 E)) : ℚ) / (multiplicity P (Ideal.span {(l : 𝓞 E)}) : ℚ) =
      ((NumberField.discr E).natAbs.factorization l : ℚ) / (Module.finrank ℚ E : ℚ) := by
  classical
  have hl0 : (l : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    exact hl0 ((Submodule.mem_bot _).1 hlP)
  have hirr : Irreducible P := (Ideal.prime_of_isPrime hP0 hP).irreducible
  have hd : (NumberField.discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero E)
  have h := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.diffExp E l
    ((NumberField.discr E).natAbs.factorization l) (ordCompl[l] (NumberField.discr E).natAbs) hl
    (Nat.not_dvd_ordCompl hl hd) (Nat.ordProj_mul_ordCompl_eq_self _ _).symm P hP hlP
  have hpos := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.count_span_pos E l hl hP hlP
  simp only [multiplicity_eq_count_normalizedFactors hirr, normalize_eq]
  have hn : (Module.finrank ℚ E : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  rw [div_eq_div_iff (by exact_mod_cast hpos.ne') hn]
  convert congrArg (fun t : ℕ => (t : ℚ)) h using 1 <;> push_cast <;> ring

end GlobalTheory.DifferentElement

namespace GlobalTheory.DifferentElement


end GlobalTheory.DifferentElement
end
end
end

-- Source module: Development.AutomorphicArithmetic.FrobeniusLocalisation.DiffMult

section

@[expose] public section

open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

theorem UpperTheory.HF.diff_mult :
    ∀ {φ : Frame} (H : HostAx φ) {l : ℕ}, l.Prime → ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})], (multiplicity P (differentIdeal ℤ (𝓞 H.E)) : ℝ) = H.el l * H.vdH l ∧ multiplicity P (span {(l : 𝓞 H.E)}) = H.el l ∧ (¬ l ∣ H.el l → multiplicity P (differentIdeal ℤ (𝓞 H.E)) = H.el l - 1) ∧ (l ∣ H.el l → H.el l ≤ multiplicity P (differentIdeal ℤ (𝓞 H.E))) := by
  intro φ H l hl P _ _
  haveI := H.galois
  obtain ⟨-, -, hram, -⟩ := grp_bridge H hl P
  have hmap : (span {(l : ℤ)}).map (algebraMap ℤ (𝓞 H.E)) = span {(l : 𝓞 H.E)} := by
    simp [Ideal.map_span]
  have hne : (span {(l : ℤ)}).map (algebraMap ℤ (𝓞 H.E)) ≠ ⊥ :=
    map_ne_bot_of_ne_bot (by simp [hl.ne_zero])
  have hmult : multiplicity P (span {(l : 𝓞 H.E)}) = H.el l := by
    rw [← hmap, ← IsDedekindDomain.ramificationIdx_eq_multiplicity _ _ hne, hram]
  have hmem : (l : 𝓞 H.E) ∈ P := by
    have hle : span {(l : 𝓞 H.E)} ≤ P := by
      rw [← hmap]
      exact map_le_of_le_comap (Ideal.LiesOver.over (P := P) (p := span {(l : ℤ)})).le
    exact hle (Ideal.mem_span_singleton_self _)
  have hrat := GlobalTheory.DifferentElement.mult_ratio H.E l hl P inferInstance hmem
  rw [hmult, Nat.factorization_def _ hl] at hrat
  have hel0 : (0 : ℝ) < H.el l := by exact_mod_cast HostRaw.el_pos _ l
  have hvd : H.vdH l = (multiplicity P (differentIdeal ℤ (𝓞 H.E)) : ℝ) / H.el l := by
    have hr := congrArg (fun q : ℚ => (q : ℝ)) hrat
    push_cast at hr
    simp only [HostRaw.vdH, Nat.padicValNat_def]
    exact hr.symm
  have h1 : (multiplicity P (differentIdeal ℤ (𝓞 H.E)) : ℝ) = H.el l * H.vdH l := by
    rw [hvd]
    field_simp
  obtain ⟨htw1, htw2, -⟩ := vd_tame_wild H hl
  refine ⟨h1, hmult, fun hnd => ?_, fun hd => ?_⟩
  · have hv := htw1 hnd
    have hle : 1 ≤ H.el l := HostRaw.el_pos _ l
    have h2 : (multiplicity P (differentIdeal ℤ (𝓞 H.E)) : ℝ) = ((H.el l - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hle, h1, hv]
      field_simp
      push_cast
      ring
    exact_mod_cast h2
  · have hv := htw2 hd
    have h2 : (H.el l : ℝ) ≤ multiplicity P (differentIdeal ℤ (𝓞 H.E)) := by
      rw [h1]
      nlinarith
    exact_mod_cast h2
end
end

-- Source module: Development.AutomorphicArithmetic.FrobeniusLocalisation.DiffEKSupp

section

@[expose] public section

open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

private theorem natMem {M : Type} [Field M] [NumberField M] (l : ℕ) (P : Ideal (𝓞 M))
    [h : P.LiesOver (span {(l : ℤ)})] (n : ℕ) : (n : 𝓞 M) ∈ P ↔ l ∣ n := by
  have h1 : (n : 𝓞 M) = algebraMap ℤ (𝓞 M) (n : ℤ) := by simp
  rw [h1, ← Ideal.mem_comap, ← Ideal.under_def, ← h.over, Ideal.mem_span_singleton, Int.natCast_dvd_natCast]

private theorem sq_lemma' {φ : Frame} (H : HostAx φ) (s : 𝓞 H.E) (hs : (s : H.E) = H.sqd) :
    s * s = -(H.d : 𝓞 H.E) := by
  apply RingOfIntegers.coe_injective
  have h2 := H.sqd_sq
  rw [← hs] at h2
  rw [← pow_two]
  push_cast
  exact h2

theorem UpperTheory.HF.diff_EK_supp :
    ∀ {φ : Frame} (H : HostAx φ), (∀ σ : H.E ≃ₐ[ℚ] H.E, σ • differentIdeal (𝓞 H.K) (𝓞 H.E) = differentIdeal (𝓞 H.K) (𝓞 H.E)) ∧ (∀ (P : Ideal (𝓞 H.E)) [P.IsPrime], P ∣ differentIdeal (𝓞 H.K) (𝓞 H.E) ↔ ∃ l ∈ H.ramI, P.LiesOver (span {(l : ℤ)})) ∧ (∀ l : ℕ, l.Prime → l ≠ H.d → ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})], (multiplicity P (differentIdeal (𝓞 H.K) (𝓞 H.E)) : ℝ) = H.el l * H.vdH l) ∧ 2 ∈ H.ramI := by
  intro φ H
  have hd := H.der
  obtain ⟨-, s, hs, -, hdiff⟩ := discr_K H
  have key : ∀ l : ℕ, l.Prime → l ≠ H.d → ∀ (P : Ideal (𝓞 H.E)) [P.LiesOver (span {(l : ℤ)})],
      ¬ P ∣ span {s} := by
    intro l hl hld P _ hPs
    rw [Ideal.dvd_span_singleton] at hPs
    have hsq : s * s ∈ P := P.mul_mem_left s hPs
    rw [sq_lemma' H s hs, neg_mem_iff, natMem l P] at hsq
    exact hld ((Nat.prime_dvd_prime_iff_eq hl H.d_prime).1 hsq)
  have mult : ∀ l : ℕ, l.Prime → l ≠ H.d → ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime]
      [P.LiesOver (span {(l : ℤ)})],
      multiplicity P (differentIdeal (𝓞 H.K) (𝓞 H.E)) = multiplicity P (differentIdeal ℤ (𝓞 H.E)) := by
    intro l hl hld P hPp _
    have hP0 : P ≠ ⊥ := by
      intro h0
      have hl' : (l : 𝓞 H.E) ∈ P := (natMem l P l).2 dvd_rfl
      rw [h0, Ideal.mem_bot] at hl'
      exact hl.ne_zero (by exact_mod_cast hl')
    have hpr : Prime P := Ideal.prime_of_isPrime hP0 hPp
    have hz : emultiplicity P (span {s}) = 0 := emultiplicity_eq_zero.2 (key l hl hld P)
    unfold multiplicity
    rw [hdiff, emultiplicity_mul hpr, hz, add_zero]
  refine ⟨fun σ => Formalism.HC.Der.kc_diff_smul_eq H.toHostRaw σ, ?_, ?_, ?_⟩
  · intro P hPp
    constructor
    · intro hPd
      have hmem := hd.diffSupport P hPp hPd
      have hne : H.QS * H.q ≠ 0 := mul_ne_zero H.QS_ne_zero H.q_prime.ne_zero
      obtain ⟨l, hl, hlq, hover⟩ := Formalism.HC.Der.kc_exists_prime P _ hne hmem
      refine ⟨l, ?_, hover⟩
      have hld : l ≠ H.d := by
        rintro rfl
        exact H.d_not_dvd_QSq hlq
      simp only [UpperTheory.HF.Formalism.HC.HostRaw.ramI, Finset.mem_erase]
      refine ⟨hld, ?_⟩
      rw [(mem_ram H hl).1]
      intro hel
      have h0 : multiplicity P (differentIdeal ℤ (𝓞 H.E)) = 0 := by
        rw [(diff_mult H hl P).2.2.1 (by rw [hel]; exact hl.not_dvd_one), hel]
      have hdv : P ∣ differentIdeal ℤ (𝓞 H.E) := hdiff ▸ dvd_mul_of_dvd_left hPd _
      exact (multiplicity_eq_zero (Ideal.finiteMultiplicity hPp.ne_top differentIdeal_ne_bot)).1 h0 hdv
    · rintro ⟨l, hlI, hover⟩
      simp only [UpperTheory.HF.Formalism.HC.HostRaw.ramI, Finset.mem_erase] at hlI
      obtain ⟨hld, hlr⟩ := hlI
      have hl : l.Prime := by
        simp only [UpperTheory.HF.Formalism.HC.HostRaw.ram, Nat.mem_primeFactors] at hlr
        exact hlr.1
      have hv : H.vdH l ≠ 0 := ((mem_ram H hl).2.2.1).1 hlr
      have hm := (diff_mult H hl P).1
      have hne : (H.el l : ℝ) * H.vdH l ≠ 0 :=
        mul_ne_zero (by exact_mod_cast (UpperTheory.HF.Formalism.HC.HostRaw.el_pos H.toHostRaw l).ne') hv
      rw [← hm, ← mult l hl hld P] at hne
      by_contra hnd
      exact hne (by exact_mod_cast multiplicity_eq_zero_of_not_dvd hnd)
  · intro l hl hld P _ _
    rw [mult l hl hld P]
    exact (diff_mult H hl P).1
  · simp only [UpperTheory.HF.Formalism.HC.HostRaw.ramI, Finset.mem_erase, UpperTheory.HF.Formalism.HC.HostRaw.ram,
      Nat.mem_primeFactors]
    refine ⟨H.d_ne_two.symm, Nat.prime_two, ?_, ?_⟩
    · exact Int.ofNat_dvd_left.1 hd.discr_primes.2.1
    · exact Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero H.E)
end
end
